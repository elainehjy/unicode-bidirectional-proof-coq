(* unicode-bidi-proof_v1.v *)
(* Mon 1 July 2024 *)

(* Ltac destr term := let H := fresh in destruct term as [] _eqn: H. *)

Require Import Bool List.
Import ListNotations.

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s, v2s with
  | [], [] => true
  | v1 :: v1s', v2 :: v2s' => eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
  | _, _ => false
  end.

Inductive bidi_class : Type :=
(* Strong *)
| L  	(* Left_to_Right *)
| R 	(* Right_to_Left *)
| AL 	(* Right-to-Left Arabic *)

(* Weak *)
| EN 	(* European_Number *)
| ES 	(* European_Number_Separator   plus and minus signs *)
| ET 	(* European_Number_Terminator 	degree sign, currency symbols etc *)
| AN 	(* Arabic_Number *)
| CS 	(* Common_Number_Separator   colon, comma, full stop, no-break space etc *)
| NSM 	(* Nonspacing_Mark   nonspacing mark and enclosing mark *)
(* | BN 	Boundary_Neutral   default ignorables, non-characters, and control characters - removed bc of rule X9 *)

(* Neutral *)
| B 	(* Paragraph_Separator *)
| S 	(* Segment_Separator   Tab *)
| WS 	(* White_Space *)
| ON 	(* Other_Neutrals *)

(* Explicit formatting *)
(*
| LRE 	Left_To_Right_Embedding
| LRO 	Left_To_Right_Override
| RLE 	Right_To_Left_Embedding
| RLO 	Right_To_Left_Override
| PDF 	Pop_Directional_Format - removed bc of rule X9
*)
| LRI	(* Left-to-Right Isolate *)
| RLI	(* Right-to-Left Isolate *)
| FSI	(* First Strong Isolate	*)
| PDI.	(* Pop Directional Isolate *)

Definition eq_dec_bidi_class (x y : bidi_class) : {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition eqb_bidi_class (a b : bidi_class) : bool :=
  if (eq_dec_bidi_class a b) then true else false.
 
Definition sos := R. (* change to assumption *)

(* ********** *)

(* W1: Examine each nonspacing mark (NSM) in the isolating run sequence, and change the type of the NSM to Other Neutral if the previous character is an isolate initiator or PDI, and to the type of the previous character otherwise. If the NSM is at the start of the isolating run sequence, it will get the type of sos. *)

Fixpoint rule_w1 (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | NSM :: text' =>
      match prev with
      | LRI | RLI | FSI | PDI => ON :: (rule_w1 ON text')
      | other => other :: (rule_w1 other text')
      end
  | c :: text' => c :: (rule_w1 c text')
  end.

(* Assume in this example that sos is R:

AL  NSM NSM → AL  AL  AL

sos NSM     → sos R

LRI NSM     → LRI ON

PDI NSM     → PDI ON *)

(* helper function for writing the tests *)

Definition test_prev_aux (func : bidi_class -> list bidi_class -> list bidi_class) (prev : bidi_class) (text expected : list bidi_class) : bool :=
  eqb_list bidi_class eqb_bidi_class (func prev text) expected.

Definition run_test_prev (func : bidi_class -> list bidi_class -> list bidi_class) (tests : list (bidi_class * list bidi_class * list bidi_class)) : bool :=
  fold_right (fun '(prev, text, expected) acc => test_prev_aux func prev text expected && acc) true tests.

Definition test_cases_rule_w1 : list (bidi_class * list bidi_class * list bidi_class) :=
  [
    (sos, [AL; NSM; NSM], [AL; AL; AL]);
    (sos, [LRI; NSM], [LRI; ON]);
    (sos, [PDI; NSM], [PDI; ON])
  ].

Compute (run_test_prev rule_w1 test_cases_rule_w1).

(*
Definition test_rule_w1 (candidate : bidi_class -> list bidi_class -> list bidi_class) :=
  (eqb_list bidi_class eqb_bidi_class (candidate sos [AL; NSM; NSM]) [AL; AL; AL]) &&
    (* (eqb_list bidi_class eqb_bidi_class (candidate sos [NSM]) [R; R]) && *)
    (eqb_list bidi_class eqb_bidi_class (candidate sos [LRI; NSM]) [LRI; ON]) &&
    (eqb_list bidi_class eqb_bidi_class (candidate sos [PDI; NSM]) [PDI; ON]).

Compute (test_rule_w1 rule_w1). *)

(* ********** *)

(* W2: Search backward from each instance of a European number until the first strong type (R, L, AL, or sos) is found. If an AL is found, change the type of the European number to Arabic number. *)

Fixpoint rule_w2 (is_al : bool) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | AL :: text' => AL :: rule_w2 true  text'
  | L  :: text' => L  :: rule_w2 false text'
  | R  :: text' => R  :: rule_w2 false text'
  | EN :: text' => (if is_al then AN else EN) :: rule_w2 is_al text'
  | c  :: text' => c  :: rule_w2 is_al text'
  end.

(* AL EN     → AL AN

AL NI EN  → AL NI AN

sos NI EN → sos NI EN

L NI EN   → L NI EN

R NI EN   → R NI EN *)

(* generalize aux *)

Definition test_bool_aux (is_al : bool) (text expected : list bidi_class) : bool :=
  eqb_list bidi_class eqb_bidi_class (rule_w2 is_al text) expected.

Definition run_test_bool (tests : list (bool * list bidi_class * list bidi_class)) : bool :=
  fold_right (fun '(is_al, text, expected) acc => test_bool_aux is_al text expected && acc) true tests.

Definition test_cases_rule_w2 : list (bool * list bidi_class * list bidi_class) :=
  [
    (true, [AL; EN], [AL; AN]);
    (true, [AL; B; EN], [AL; B; AN]);
    (true, [R; S; EN], [R; S; EN]);
    (true, [L; ON; EN], [L; ON; EN])
  ].

Compute (run_test_bool test_cases_rule_w2).

(* ********** *)

Fixpoint rule_w12 (is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | NSM :: text' =>
      match prev with
      | AL => AL :: rule_w12 true prev text'
      | L  => L  :: rule_w12 false prev text'
      | R  => R  :: rule_w12 false prev text'
      | EN => (if is_al then AN else EN) :: rule_w12 is_al prev text'
      | LRI | RLI | FSI | PDI => ON :: (rule_w12 is_al ON text')
      | _ => prev :: rule_w12 is_al prev text'
      end
  | AL :: text' => AL :: rule_w12 true AL text'
  | L  :: text' => L  :: rule_w12 false L text'
  | R  :: text' => R  :: rule_w12 false R text'
  | EN :: text' => (if is_al then AN else EN) :: rule_w12 is_al EN text'
  | c  :: text' => c :: rule_w12 is_al c text'
  end.

Lemma w12_correct: forall (text : list bidi_class) (is_al : bool) (prev : bidi_class),
    rule_w2 is_al (rule_w1 prev text) = rule_w12 is_al prev text.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros is_al prev.
  - reflexivity.
  - destruct c, prev; simpl; rewrite -> IH; reflexivity.
Qed.

(* ********** *)

(* W3: Change all ALs to R. *)

Fixpoint rule_w3 (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | AL :: text' => R :: rule_w3 text'
  | c  :: text' => c :: rule_w3 text'
  end.

Fixpoint rule_w13 (is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | NSM :: text' =>
      match prev with
      | AL => R :: rule_w13 true prev text'
      | L  => L :: rule_w13 false prev text'
      | R  => R :: rule_w13 false prev text'
      | EN => (if is_al then AN else EN) :: rule_w13 is_al prev text'
      | LRI | RLI | FSI | PDI => ON :: (rule_w13 is_al ON text')
      | _ => prev :: rule_w13 is_al prev text'
      end
  | AL :: text' => R :: rule_w13 true AL text'
  | L  :: text' => L :: rule_w13 false L text'
  | R  :: text' => R :: rule_w13 false R text'
  | EN :: text' => (if is_al then AN else EN) :: rule_w13 is_al EN text'
  | c  :: text' => c :: rule_w13 is_al c text'
  end.

(* ********** *)

Lemma w13_correct: forall (text : list bidi_class) (is_al : bool) (prev : bidi_class),
    rule_w3 (rule_w12 is_al prev text) = rule_w13 is_al prev text.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros is_al prev.
  - reflexivity.
  - destruct c, is_al, prev; simpl; rewrite -> IH; reflexivity.
Qed.

(* ********** *)

(* W4: A single European separator between two European numbers changes to a European number. A single common separator between two numbers of the same type changes to that type. *)

Fixpoint rule_w4 (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | _, [c] => [c]
  | EN, ES :: (EN :: _) as text' => EN :: rule_w4 EN text'
  | EN, CS :: (EN :: _) as text' => EN :: rule_w4 EN text'
  | AN, CS :: (AN :: _) as text' => AN :: rule_w4 AN text'
  | _, c :: text' => c :: rule_w4 c text'
  end.

Compute (rule_w4 sos [EN; ES; EN; ES; EN]).

(* EN ES EN → EN EN EN

EN CS EN → EN EN EN

AN CS AN → AN AN AN *)

Definition test_cases_rule_w4 : list (bidi_class * list bidi_class * list bidi_class) :=
  [
    (sos, [EN; ES; EN], [EN; EN; EN]);
    (sos, [EN; CS; EN], [EN; EN; EN]);
    (sos, [AN; CS; AN], [AN; AN; AN]);
    (sos, [EN; ES; EN; ES; EN], [EN; EN; EN; EN; EN])
  ].

Compute (run_test_prev rule_w4 test_cases_rule_w4).

(* ********** *)

Fixpoint rule_w14 (is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | AL, NSM :: text' => R :: rule_w14 true prev text'
  | L,  NSM :: text' => L :: rule_w14 false prev text'
  | R,  NSM :: text' => R :: rule_w14 false prev text'
  | EN, NSM :: text' => (if is_al then AN else EN) :: rule_w14 is_al (if is_al then AN else EN) text'
  | LRI, NSM :: text' => ON :: (rule_w14 is_al ON text')
  | RLI, NSM :: text' => ON :: (rule_w14 is_al ON text')
  | FSI, NSM :: text' => ON :: (rule_w14 is_al ON text')
  | PDI, NSM :: text' => ON :: (rule_w14 is_al ON text')
  | _, NSM :: text' => prev :: rule_w14 is_al prev text'
  | _, AL :: text' => R  :: rule_w14 true AL text'
  | _, L  :: text' => L  :: rule_w14 false L text'
  | _, R  :: text' => R  :: rule_w14 false R text'
  | _, EN :: text' => (if is_al then AN else EN) :: rule_w14 is_al (if is_al then AN else EN) text'
  | EN, ES :: (EN :: _) as text' => (if is_al then ES else EN) :: rule_w14 is_al (if is_al then ES else EN) text'
  | EN, CS :: (EN :: _) as text' => (if is_al then CS else EN) :: rule_w14 is_al (if is_al then CS else EN) text'
  | AN, CS :: (EN :: _) as text' => (if is_al then AN else CS):: rule_w14 is_al (if is_al then AN else CS) text'
  | AN, CS :: (AN :: _) as text' => AN :: rule_w14 is_al AN text' (*no if bc there are no ENs *)
  | _, c  :: text' => c :: rule_w14 is_al c text'
  end.

Lemma w13_EN_AN: forall (text : list bidi_class),
    rule_w13 true EN text = rule_w13 true AN text.
Proof.
  intro text.
  induction text as [ | c text' IH].
  - auto.
  - destruct c; simpl; repeat rewrite -> IH; repeat reflexivity.
Qed.

Lemma w14_correct: forall (text : list bidi_class) (is_al : bool) (prev : bidi_class),
  rule_w4 prev (rule_w13 is_al prev text) = rule_w14 is_al prev text.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros is_al prev.
  - reflexivity.
  - destruct text' as [ | c' text''].
    + destruct c, is_al, prev; auto.
    + remember (c' :: text'') as text' eqn:H_text'.
      destruct c; simpl; repeat rewrite <- IH; rewrite -> H_text';
        case is_al; destruct c'; auto; destruct prev; auto; rewrite w13_EN_AN; auto.
Qed.
