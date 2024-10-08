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
(* | BN - removed bc of rule X9 *)

(* Neutral *)
| B 	(* Paragraph_Separator *)
| S 	(* Segment_Separator   Tab *)
| WS 	(* White_Space *)
| ON 	(* Other_Neutrals *)

(* Explicit formatting *)
(* | LRE | LRO | RLE | RLO | PDF removed bc of rule X9 *)
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

Definition test_aux {V : Type} (func : V -> list bidi_class -> list bidi_class) (param : V) (text expected : list bidi_class) : bool :=
  eqb_list bidi_class eqb_bidi_class (func param text) expected.

Definition run_test {V : Type} (func : V -> list bidi_class -> list bidi_class) (tests : list (V * list bidi_class * list bidi_class)) : bool :=
  fold_right (fun '(param, text, expected) acc => test_aux func param text expected && acc) true tests.

Definition test_cases_rule_w1 : list (bidi_class * list bidi_class * list bidi_class) :=
  [
    (sos, [AL; NSM; NSM], [AL; AL; AL]);
    (sos, [LRI; NSM], [LRI; ON]);
    (sos, [PDI; NSM], [PDI; ON])
  ].

Compute (run_test rule_w1 test_cases_rule_w1).

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

Definition test_cases_rule_w2 : list (bool * list bidi_class * list bidi_class) :=
  [
    (true, [AL; EN], [AL; AN]);
    (true, [AL; B; EN], [AL; B; AN]);
    (true, [R; S; EN], [R; S; EN]);
    (true, [L; ON; EN], [L; ON; EN])
  ].

Compute (run_test rule_w2 test_cases_rule_w2).

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

(*Fixpoint rule_w4 (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | [c] => [c]
  | ES :: text' =>
      match prev with
      | EN => match text' with
              | EN :: _ => EN :: rule_w4 EN text'
              | _ => ES :: rule_w4 ES text'
              end
      | _ => ES :: rule_w4 ES text'
      end
  | CS :: text' =>
      match prev with
      | EN => match text' with
              | EN :: _ => EN :: rule_w4 EN text'
              | _ => CS :: rule_w4 CS text'
              end
      | AN => match text' with
              | AN :: _ => AN :: rule_w4 AN text'
              | _ => CS :: rule_w4 CS text'
              end
      | _ => CS :: rule_w4 CS text'
      end
  | c :: text' => c :: rule_w4 c text'
  end.*)

Fixpoint rule_w4 (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | _, [c] => [c]
  | EN, ES :: (EN :: _) as text' => EN :: rule_w4 EN text'
  | EN, CS :: (EN :: _) as text' => EN :: rule_w4 EN text'
  | AN, CS :: (AN :: _) as text' => AN :: rule_w4 AN text'
  | _, c :: text' => c :: rule_w4 c text'
  end.

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

Compute (run_test rule_w4 test_cases_rule_w4).

(* ********** *)

(*Fixpoint rule_w14 (is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | NSM :: text' =>
      match prev with
      | AL => R :: rule_w14 true prev text'
      | L  => L :: rule_w14 false prev text'
      | R  => R :: rule_w14 false prev text'
      | EN => (if is_al then AN else EN) :: rule_w14 is_al (if is_al then AN else EN) text'
      | LRI | RLI | FSI | PDI => ON :: (rule_w14 is_al ON text')
      | _ => prev :: rule_w14 is_al prev text'
      end
  | AL :: text' => R :: rule_w14 true AL text'
  | L  :: text' => L :: rule_w14 false L text'
  | R  :: text' => R :: rule_w14 false R text'
  | EN :: text' => (if is_al then AN else EN) :: rule_w14 is_al (if is_al then AN else EN) text'
  | ES :: text' =>
      match prev with
      | EN => match text' with
              | EN :: _ => (if is_al then ES else EN) :: rule_w14 is_al (if is_al then ES else EN) text'
              | _ => ES :: rule_w14 is_al ES text'
              end
      | _ => ES :: rule_w14 is_al ES text'
      end
  | CS :: text' =>
      match prev with
      | EN => match text' with
              | EN :: _ => (if is_al then CS else EN) :: rule_w14 is_al (if is_al then CS else EN) text'
              | _ => CS :: rule_w14 is_al CS text'
              end
      | AN => match text' with
              | EN :: _ => (if is_al then AN else CS):: rule_w14 is_al (if is_al then AN else CS) text'
              | AN :: _ => AN :: rule_w14 is_al AN text'
              | _ => CS :: rule_w14 is_al CS text'
              end
      | _ => CS :: rule_w14 is_al CS text'
      end
  | c :: text' => c :: rule_w14 is_al c text'
  end.*)

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
  | _, c :: text' => c :: rule_w14 is_al c text'
  end.

Lemma w13_EN_AN: forall (text : list bidi_class),
    rule_w13 true EN text = rule_w13 true AN text.
Proof.
  intro text.
  induction text as [ | c text' IH].
  - reflexivity.
  - destruct c; simpl; try rewrite -> IH; reflexivity.
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
      destruct c, is_al, prev; simpl; repeat rewrite <- IH; rewrite -> H_text'; destruct c'; auto; rewrite -> w13_EN_AN; auto.
Qed.

(* ********** *)

(* W5: A sequence of European terminators adjacent to European numbers changes to all European numbers. *)

Fixpoint rule_w5_before_en (text : list bidi_class) : bool :=
  match text with
  | [] => false
  | EN :: _ => true
  | ET :: text' => rule_w5_before_en text'
  | _ :: _ => false
  end.

Fixpoint rule_w5 (after_en : bool) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | ET :: text' =>
      if after_en
      then EN :: rule_w5 after_en text'
      else if rule_w5_before_en text'
           then EN :: rule_w5 after_en text'
           else ET :: rule_w5 after_en text'
  | EN :: text' => EN :: rule_w5 true text'
  | c :: text' => c :: rule_w5 false text'
  end.

(* ET ET EN → EN EN EN

EN ET ET → EN EN EN

AN ET EN → AN EN EN *)

Definition test_cases_rule_w5 : list (bool * list bidi_class * list bidi_class) :=
  [
    (true, [ET; ET; EN], [EN; EN; EN]);
    (true, [EN; ET; ET], [EN; EN; EN]);
    (true, [AN; ET; EN], [AN; EN; EN]);
    (true, [AN; ET; EN; ET; EN; ET; AN; ET], [AN; EN; EN; EN; EN; EN; AN; ET])
  ].

Compute (run_test rule_w5 test_cases_rule_w5).

(* ********** *)

Fixpoint rule_w15_before_en (is_al : bool) (prev : bidi_class) (text : list bidi_class) : bool :=
  let head :=
    match text with
    | [] => L (* don't care *)
    | NSM :: text' => match prev with
                      | LRI | RLI | FSI | PDI => ON
                      | _ => prev
                      end
    | c :: text' => c
    end in
  match head, text with
  | _, [] => false
  | EN, _ :: _ => if is_al then false else true
  | ET, _ :: text' => rule_w15_before_en is_al ET text'
  | ES, _ :: EN :: _ =>
      match prev with
      | EN => if is_al then false else true
      | _ => false
      end
  | CS, _ :: EN :: _ =>
      match prev with
      | EN => if is_al then false else true
      | _ => false
      end
  | _, _ :: _ => false
  end.

Lemma rule_w15_before_en_correct: forall (text : list bidi_class) (is_al : bool) (prev : bidi_class),
    rule_w5_before_en (rule_w14 is_al prev text) = rule_w15_before_en is_al prev text.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros is_al prev.
  - destruct prev; reflexivity.
  - destruct text' as [ | c' text''].
    + destruct c, is_al, prev; auto.
    + remember (c' :: text'') as text' eqn:H_text'.
      destruct c; simpl; try rewrite <- IH; try reflexivity; rewrite -> H_text'; destruct c', is_al, prev; auto.
Qed.

Fixpoint rule_w15 (after_en is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | AL, NSM :: text' => R  :: rule_w15 false true prev text'
  | L,  NSM :: text' => L  :: rule_w15 false false prev text'
  | R,  NSM :: text' => R  :: rule_w15 false false prev text'
  | LRI, NSM :: text' => ON :: rule_w15 false is_al ON text'
  | RLI, NSM :: text' => ON :: rule_w15 false is_al ON text'
  | FSI, NSM :: text' => ON :: rule_w15 false is_al ON text'
  | PDI, NSM :: text' => ON :: rule_w15 false is_al ON text'
  | EN, NSM :: text' => (if is_al then AN else EN) :: rule_w15 (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | ET, NSM :: text' =>
      if after_en
      then EN :: rule_w15 after_en is_al ET text'
      else if rule_w15_before_en is_al ET text'
           then EN :: rule_w15 after_en is_al ET text'
           else ET :: rule_w15 after_en is_al ET text'
  | _, NSM :: text' => prev :: rule_w15 false is_al prev text'
  | _, AL :: text' => R  :: rule_w15 false true AL text'
  | _, L  :: text' => L  :: rule_w15 false false L text'
  | _, R  :: text' => R  :: rule_w15 false false R text'
  | _, EN :: text' => (if is_al then AN else EN) :: rule_w15 (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | EN, ES :: (EN :: _) as text' => (if is_al then ES else EN) :: rule_w15 (if is_al then false else true) is_al (if is_al then ES else EN) text'
  | EN, CS :: (EN :: _) as text' => (if is_al then CS else EN) :: rule_w15 (if is_al then false else true) is_al (if is_al then CS else EN) text'
  | AN, CS :: (EN :: _) as text' => (if is_al then AN else CS):: rule_w15 false is_al (if is_al then AN else CS) text'
  | AN, CS :: (AN :: _) as text' => AN :: rule_w15 false is_al AN text'
  | _, ET :: text' =>
      if after_en
      then EN :: rule_w15 after_en is_al ET text'
      else if rule_w15_before_en is_al ET text'
           then EN :: rule_w15 after_en is_al ET text'
           else ET :: rule_w15 after_en is_al ET text'
  | _, c :: text' => c :: rule_w15 false is_al c text'
  end.

Lemma w15_correct: forall (text : list bidi_class) (after_en is_al : bool) (prev : bidi_class),
    rule_w5 after_en (rule_w14 is_al prev text) = rule_w15 after_en is_al prev text.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros after_en is_al prev.
  - destruct prev; reflexivity.
  - destruct text' as [ | c' text''].
    + destruct c, after_en, is_al, prev; auto.
    + remember (c' :: text'') as text' eqn:H_text'.
      destruct c, after_en, is_al, prev; simpl; rewrite <- IH; try reflexivity; rewrite -> H_text'; destruct c'; auto;
        try rewrite -> rule_w15_before_en_correct; auto.
        rewrite -> H_text' in IH; rewrite <- IH; reflexivity.
Qed.

(* ********** *)

(* W6. All remaining separators and terminators (after the application of W4 and W5) change to Other Neutral. *)

Fixpoint rule_w6 (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | ES :: text' | ET :: text' | CS :: text' => ON :: rule_w6 text'
  | c :: text' => c :: rule_w6 text'
  end.

(* AN ET    → AN ON

L  ES EN → L  ON EN

EN CS AN → EN ON AN

ET AN    → ON AN *)

Definition test_aux' (func: list bidi_class -> list bidi_class) (text expected : list bidi_class) : bool :=
  eqb_list bidi_class eqb_bidi_class (func text) expected.

Definition run_test' (func : list bidi_class -> list bidi_class) (tests : list (list bidi_class * list bidi_class)) : bool :=
  fold_right (fun '(text, expected) acc => test_aux' func text expected && acc) true tests.

Definition test_cases_rule_w6 : list (list bidi_class * list bidi_class) :=
  [
    ([AN; ET], [AN; ON]);
    ([L; ES; EN], [L; ON; EN]);
    ([EN; CS; AN], [EN; ON; AN]);
    ([ET; AN], [ON; AN])
  ].

Compute (run_test' rule_w6 test_cases_rule_w6).

(* ********** *)

Fixpoint rule_w16 (after_en is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | AL, NSM :: text' => R :: rule_w16 false true prev text'
  | L,  NSM :: text' => L :: rule_w16 false false prev text'
  | R,  NSM :: text' => R :: rule_w16 false false prev text'
  | LRI, NSM :: text' => ON :: rule_w16 false is_al ON text'
  | RLI, NSM :: text' => ON :: rule_w16 false is_al ON text'
  | FSI, NSM :: text' => ON :: rule_w16 false is_al ON text'
  | PDI, NSM :: text' => ON :: rule_w16 false is_al ON text'
  | EN, NSM :: text' => (if is_al then AN else EN) :: rule_w16 (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | ET, NSM :: text' =>
      if after_en
      then EN :: rule_w16 after_en is_al ET text'
      else if rule_w15_before_en is_al ET text'
           then EN :: rule_w16 after_en is_al ET text'
           else ON :: rule_w16 after_en is_al ET text'
  | ES, NSM :: text' => ON :: rule_w16 false is_al ES text'
  | CS, NSM :: text' => ON :: rule_w16 false is_al CS text'
  | _,  NSM :: text' => prev :: rule_w16 false is_al prev text'
  | _, AL :: text' => R  :: rule_w16 false true AL text'
  | _, L  :: text' => L  :: rule_w16 false false L text'
  | _, R  :: text' => R  :: rule_w16 false false R text'
  | _, EN :: text' => (if is_al then AN else EN) :: rule_w16 (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | EN, ES :: (EN :: _) as text' => (if is_al then ON else EN) :: rule_w16 (if is_al then false else true) is_al (if is_al then ES else EN) text'
  | EN, CS :: (EN :: _) as text' => (if is_al then ON else EN) :: rule_w16 (if is_al then false else true) is_al (if is_al then CS else EN) text'
  | AN, CS :: (EN :: _) as text' => (if is_al then AN else ON):: rule_w16 false is_al (if is_al then AN else CS) text'
  | AN, CS :: (AN :: _) as text' => AN :: rule_w16 false is_al AN text'
  | _, ET :: text' =>
      if after_en
      then EN :: rule_w16 after_en is_al ET text'
      else if rule_w15_before_en is_al ET text'
           then EN :: rule_w16 after_en is_al ET text'
           else ON :: rule_w16 after_en is_al ET text'
  | _, ES :: text' => ON :: rule_w16 false is_al ES text'
  | _, CS :: text' => ON :: rule_w16 false is_al CS text'
  | _, c  :: text' => c :: rule_w16 false is_al c text'
  end.

Lemma w16_correct: forall (text : list bidi_class) (after_en is_al : bool) (prev : bidi_class),
    rule_w6 (rule_w15 after_en is_al prev text) = rule_w16 after_en is_al prev text.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros after_en is_al prev.
  - destruct prev; reflexivity.
  - destruct text' as [ | c' text''].
    + destruct c, after_en, is_al, prev; auto.
    + remember (c' :: text'') as text' eqn:H_text'.
      destruct c, after_en, is_al, prev; simpl; repeat rewrite <- IH; try reflexivity; rewrite -> H_text'; destruct c'; auto.
      (* simpl rule_w15_before_en;
      destruct text''; try reflexivity; destruct b; try reflexivity *)       
Admitted.

(* ********** *)

(* W7. Search backward from each instance of a European number until the first strong type (R, L, or sos) is found. If an L is found, then change the type of the European number to L. *)

Fixpoint rule_w7 (after_l : bool) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | EN :: text' => (if after_l then L else EN) :: rule_w7 after_l text'
  | L  :: text' => L :: rule_w7 true text'
  | R  :: text' => R :: rule_w7 false text'
  | c  :: text' => c :: rule_w7 after_l text'
  end.

(* L  NI EN → L  NI  L

R  NI EN → R  NI  EN *)

Definition test_cases_rule_w7 : list (bool * list bidi_class * list bidi_class) :=
  [
    (true, [L; ON; EN], [L; ON; L]);
    (true, [R; ON; EN], [R; ON; EN]);
    (true, [L; R; EN; L; ON; EN], [L; R; EN; L; ON; L])
  ].

Compute (run_test bool rule_w7 test_cases_rule_w7).

(* ********** *)

Fixpoint rule_w17 (after_l after_en is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | AL, NSM :: text' => R  :: rule_w17 false false true prev text'
  | L,  NSM :: text' => L  :: rule_w17 true false false prev text'
  | R,  NSM :: text' => R  :: rule_w17 false false false prev text'
  | LRI, NSM :: text' => ON :: rule_w17 false false is_al ON text'
  | RLI, NSM :: text' => ON :: rule_w17 false false is_al ON text'
  | FSI, NSM :: text' => ON :: rule_w17 false false is_al ON text'
  | PDI, NSM :: text' => ON :: rule_w17 false false is_al ON text'
  | EN, NSM :: text' => (if is_al then AN else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | ET, NSM :: text' =>
      if after_en
      then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
      else if rule_w15_before_en is_al ET text'
           then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
           else ON :: rule_w17 after_l after_en is_al ET text'
  | ES, NSM :: text' => ON :: rule_w17 after_l false is_al prev text'
  | CS, NSM :: text' => ON :: rule_w17 after_l false is_al prev text'
  | _,  NSM :: text' => prev :: rule_w17 after_l false is_al prev text'
  | _, AL :: text' => R  :: rule_w17 false false true AL text'
  | _, L  :: text' => L  :: rule_w17 true false false L text'
  | _, R  :: text' => R  :: rule_w17 false false false R text'
  | _, EN :: text' => (if is_al then AN else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | EN, ES :: (EN :: _) as text' => (if is_al then ON else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then ES else EN) text'
  | EN, CS :: (EN :: _) as text' => (if is_al then ON else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then CS else EN) text'
  | AN, CS :: (EN :: _) as text' => (if is_al then AN else ON) :: rule_w17 after_l false is_al (if is_al then AN else CS) text'
  | AN, CS :: (AN :: _) as text' => AN :: rule_w17 after_l false is_al AN text'
  | _, ET :: text' =>
      if after_en
      then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
      else if rule_w15_before_en is_al ET text'
           then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
           else ON :: rule_w17 after_l after_en is_al ET text'
  | _, ES :: text' => ON :: rule_w17 after_l false is_al ES text'
  | _, CS :: text' => ON :: rule_w17 after_l false is_al CS text'
  | _, c  :: text' => c :: rule_w17 after_l false is_al c text'
  end.

Lemma w17_correct: forall (text : list bidi_class) (after_l after_en is_al : bool) (prev : bidi_class),
    rule_w7 after_l (rule_w16 after_en is_al prev text) = rule_w17 after_l after_en is_al prev text.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros after_l after_en is_al prev.
  - destruct prev; auto.
  - destruct text' as [ | c' text''].
    + destruct c, after_en, is_al, prev; auto.
    + remember (c' :: text'') as text' eqn:H_text'.
      destruct c, after_l, after_en, is_al, prev; simpl; repeat rewrite <- IH; try reflexivity; rewrite -> H_text'; destruct c'; auto; simpl.
