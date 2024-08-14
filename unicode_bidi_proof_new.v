Set Default Goal Selector "!". (* Force use of bullets. *)

Require Import Bool List.
Import ListNotations.

Require generated_test_cases.

(* Load "generated_test_cases.v". *)
(* Check generated_test_cases.test_cases. *)

(* Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s, v2s with
  | [], [] => true
  | v1 :: v1s', v2 :: v2s' => eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
  | _, _ => false
  end. *)

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

Parameter sos : bidi_class.
Parameter eos : bidi_class.
(* Parameter is_brack_e : text -> boolean.
Parameter rule_n0 : ... .
Fixpoint rule_n0 : (parens : list (int, int))
  is_brack_e  *)

(* Local sos : bidi_class. *)
(* Definition sos := R. change to assumption *)

Definition next (text : list bidi_class) : option bidi_class :=
  match text with
  | [] => None
  | c :: _ => Some c
  end.

(* ********** *)

Fixpoint fixed {S : Set} (next_head : bidi_class -> S -> bidi_class) (next_state : bidi_class -> S -> S) (l : list bidi_class) (state : S) : list bidi_class :=
  (* fix f (l : list bidi_class) (state : S) : list bidi_class := *)
  match l with
  | [] => []
  | c :: cs => next_head c state :: fixed next_head next_state cs (next_state c state)
  end.



Lemma ff
  {S1 : Set}
  {S2 : Set}
  {S12 : Set}
  (eqv : S1 -> S2 -> S12 -> Prop)
  (next_head1 : bidi_class -> S1 -> bidi_class) (next_state1 : bidi_class -> S1 -> S1)
  (next_head2 : bidi_class -> S2 -> bidi_class) (next_state2 : bidi_class -> S2 -> S2)
  (next_head12 : bidi_class -> S12 -> bidi_class) (next_state12 : bidi_class -> S12 -> S12)
  (eq_head : forall (c : bidi_class) (state1 : S1) (state2 : S2) (state12 : S12),
    (eqv state1 state2 state12) -> next_head12 c state12 = next_head2 (next_head1 c state1) state2)
  (eqv_next : forall (c : bidi_class) (state1 : S1) (state2 : S2) (state12 : S12),
    eqv state1 state2 state12 ->
    eqv (next_state1 c state1) (next_state2 (next_head1 c state1) state2) (next_state12 c state12))
  :
  forall (l : list bidi_class) (state1 : S1) (state2 : S2) (state12 : S12)
  (e : eqv state1 state2 state12)
  ,
  fixed next_head12 next_state12 l state12 =
  fixed next_head2 next_state2
    (fixed next_head1 next_state1 l state1) state2.
Proof.
  induction l as [ | c text' IH]; intros; simpl; f_equal; auto.
Qed.

(* ********** *)

(* W1: Examine each nonspacing mark (NSM) in the isolating run sequence, and
change the type of the NSM to Other Neutral if the previous character is an
isolate initiator or PDI, and to the type of the previous character otherwise.
If the NSM is at the start of the isolating run sequence, it will get the type
of sos. *)

Definition w1_next_head (c : bidi_class) (prev : bidi_class) : bidi_class :=
  match c, prev with
  | NSM, (LRI | RLI | FSI | PDI) => ON
  | NSM, _ => prev
  | c, _ => c
  end.

Definition w1_next_state (c : bidi_class) (prev : bidi_class) : bidi_class :=
  match c, prev with
  | NSM, (LRI | RLI | FSI | PDI) => ON
  | NSM, _ => prev
  | c, _ => c
  end.

Definition w1_fixed := fixed w1_next_head w1_next_state.

Fixpoint rule_w1 (text : list bidi_class) (prev : bidi_class) : list bidi_class :=
  match text, prev with
  | [], _ => []
  | NSM :: text', (LRI | RLI | FSI | PDI) => ON :: rule_w1 text' ON
  | NSM :: text', _ => prev :: rule_w1 text' prev
  | c :: text', _ => c :: rule_w1 text' c
  end.

Lemma x: forall (text : list bidi_class) (prev : bidi_class), rule_w1 text prev = w1_fixed text prev.
Proof.
  induction text as [ | c text' IH]; intros.
  - auto.
  - simpl.
    destruct c.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + destruct prev.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
      * rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
    + rewrite IH. unfold w1_fixed, w1_next_head, w1_next_state. simpl. auto.
Qed.

(* Assume in this example that sos is R:

AL  NSM NSM → AL  AL  AL

sos NSM     → sos R

LRI NSM     → LRI ON

PDI NSM     → PDI ON *)

(* helper function for writing the tests *)

(* Definition test_aux {V : Type} (func : V -> list bidi_class -> list bidi_class) (param : V) (text expected : list bidi_class) : bool :=
  eqb_list bidi_class eqb_bidi_class (func param text) expected. *)

(* Definition run_test {V : Type} (func : V -> list bidi_class -> list bidi_class) (tests : list (V * list bidi_class * list bidi_class)) : bool :=
  fold_right (fun '(param, text, expected) acc => test_aux func param text expected && acc) true tests.

Definition test_cases_rule_w1 : list (bidi_class * list bidi_class * list bidi_class) :=
  [
    (sos, [AL; NSM; NSM], [AL; AL; AL]);
    (sos, [LRI; NSM], [LRI; ON]);
    (sos, [PDI; NSM], [PDI; ON])
  ]. *)

(* Compute (run_test rule_w1 test_cases_rule_w1). *)

(* ********** *)

(* W2: Search backward from each instance of a European number until the first strong type (R, L, AL, or sos) is found. If an AL is found, change the type of the European number to Arabic number. *)

Definition next_is_al (c : bidi_class) (is_al : bool) : bool :=
  match c with
  | AL => true
  | L | R => false
  | _ => is_al
  end.

Fixpoint rule_w2 (text : list bidi_class) (is_al : bool) : list bidi_class :=
  match text with
  | [] => []
  | EN :: text' => (if is_al then AN else EN) :: rule_w2 text' is_al
  | c :: text' => c :: rule_w2 text' (next_is_al c is_al)
  end.

Definition w2_next_head (c : bidi_class) (is_al : bool) : bidi_class :=
  match c, is_al with
  | EN, true => AN
  | EN, false => EN
  | c, _ => c
  end.

Definition w2_next_state (c : bidi_class) (is_al : bool) : bool :=
  next_is_al c is_al.

Definition w2_fixed := fixed w2_next_head w2_next_state.

Lemma w2_fixed_correct: forall (text : list bidi_class) (is_al : bool), rule_w2 text is_al = w2_fixed text is_al.
Proof.
  induction text as [ | c text' IH]; intros.
  - auto.
  - destruct c, is_al; simpl; try rewrite -> IH; auto.
Qed.

Lemma w2_EN_AN: forall (text : list bidi_class),
  rule_w2 (EN :: text) true = rule_w2 (AN :: text) true.
Proof.
  auto.
Qed.

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

(* Compute (run_test rule_w2 test_cases_rule_w2). *)

(* ********** *)



(* Lemma foo : forall (text : list bidi_class) (is_al : bool) (prev : bidi_class),
rule_w2 is_al (rule_w1 prev text) = [].
unfold rule_w2.
unfold rule_w1.
destruct text.
simpl. *)

(* We always convert EN&is_al to AN *)

Fixpoint rule_w12 (text : list bidi_class) (prev : bidi_class) (is_al : bool) : list bidi_class :=
  match text, prev with
  | [] , _ => []
  | EN :: text', _ => (if is_al then AN else EN) :: rule_w12 text' (if is_al then AN else EN) is_al
  | NSM :: text', EN => (if is_al then AN else EN) :: rule_w12 text' (if is_al then AN else EN) is_al
  | NSM :: text', (LRI | RLI | FSI | PDI) => ON :: rule_w12 text' ON is_al
  | NSM :: text', _ => prev :: rule_w12 text' prev (next_is_al prev is_al)
  | c :: text', _ => c :: rule_w12 text' c (next_is_al c is_al)
  end.

Lemma w12_EN_AN: forall (text : list bidi_class),
    rule_w12 text EN true = rule_w12 text AN true.
Proof.
  destruct text; auto.
Qed.

Parameter w12_next_head : (bidi_class) -> (bidi_class * bool) -> bidi_class.
  (* let (prev, is_al) := state in
  match c, prev, is_al with
  | EN, _, true => AN
  | EN, _, false => EN
  | NSM, EN, true => AN
  | NSM, EN, false => EN
  | NSM :: text', (LRI | RLI | FSI | PDI) => ON :: rule_w12 text' ON is_al
  | NSM, _, _ => prev :: rule_w12 text' prev (next_is_al prev is_al)
  | c, _ => c
  end. *)

Parameter w12_next_state : (bidi_class) -> (bidi_class * bool) -> bidi_class * bool.
(* Parameter w12_eqv : (bidi_class) -> bool -> (bidi_class * bool) -> Prop. *)
Definition w12_eqv (w1_state : bidi_class) (w2_state : bool) (w12_state : bidi_class * bool) : Prop :=
  (w1_state, w2_state) = w12_state.

Definition w12_fixed := fixed w12_next_head w12_next_state.

(* Lemma w1_w2_w12 : 
 {S1 : Set} (next_head1 : bidi_class -> S1 -> bidi_class) (next_state1 : bidi_class -> S1 -> S1)
{S2 : Set} (next_head2 : bidi_class -> S2 -> bidi_class) (next_state2 : bidi_class -> S2 -> S2)
{S12 : Set} (next_head12 : bidi_class -> S12 -> bidi_class) (next_state12 : bidi_class -> S12 -> S12)
(eqv : S1 -> S2 -> S12 -> Prop)
(eq_head : forall (c : bidi_class) (state1 : S1) (state2 : S2) (state12 : S12),
  (eqv state1 state2 state12) -> next_head12 c state12 = next_head2 (next_head1 c state1) state2)
(eqv_next : forall (c : bidi_class) (state1 : S1) (state2 : S2) (state12 : S12),
  eqv (next_state1 c state1) (next_state2 (next_head1 c state1) state2) (next_state12 c state12))
: *)
(* forall (l : list bidi_class) (state1 : bidi_class) (state2 : bool) (state12 : bidi_class * bool)
(H_w12_eqv : w12_eqv state1 state2 state12)
,
fixed w12_next_head w12_next_state l state12 =
fixed w2_next_head w2_next_state
  (fixed w1_next_head w1_next_state l state1) state2.
Proof.
  apply (ff w12_eqv).
  - intros.
    admit.
    (* destruct c; simpl.
    + admit.
    + admit.
    + admit.
    + unfold w12_eqv in H. inversion H.
      destruct state2. *)
  - intros.
    unfold w12_eqv in *.
    destruct c; simpl.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + simpl.
    unfold w1_next_state, w2_next_state, w1_next_head.
    inversion H.
    destruct 
      *
     destruct state2.
      * inversion H. admit.
      * 

  intros. *)

Lemma w12_fixed_correct: forall (text : list bidi_class) (is_al : bool), rule_w2 text is_al = w2_fixed text is_al.
Proof.
  induction text as [ | c text' IH]; intros.
  - auto.
  - destruct c, is_al; simpl; try rewrite -> IH; auto.
Qed.

Lemma w12_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al : bool),
  rule_w12 text prev is_al = rule_w2 (rule_w1 text prev) is_al.
Proof.
  induction text as [ | c text' IH].
  - reflexivity.
  - destruct c, prev, is_al. all: simpl. all: rewrite <- IH. all: try rewrite -> w12_EN_AN. all: reflexivity.
Qed.

(* ********** *)

(* W3: Change all ALs to R. *)

Fixpoint rule_w3 (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | AL :: text' => R :: rule_w3 text'
  | c  :: text' => c :: rule_w3 text'
  end.

Fixpoint rule_w13 (text : list bidi_class) (prev : bidi_class) (is_al : bool) : list bidi_class :=
  match text, prev with
  | [] , _ => []
  | EN :: text', _ => (if is_al then AN else EN) :: rule_w13 text' (if is_al then AN else EN) is_al
  | NSM :: text', EN => (if is_al then AN else EN) :: rule_w13 text' (if is_al then AN else EN) is_al
  | NSM :: text', (LRI | RLI | FSI | PDI) => ON :: rule_w13 text' ON is_al
  | NSM :: text', _ => (if eq_dec_bidi_class prev AL then R else prev) :: rule_w13 text' prev (next_is_al prev is_al)
  | c :: text', _ => (if eq_dec_bidi_class c AL then R else c) :: rule_w13 text' c (next_is_al c is_al)
  end.

(* ********** *)

Lemma w13_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al : bool),
  rule_w13 text prev is_al = rule_w3 (rule_w12 text prev is_al).
Proof.
  induction text as [ | c text' IH].
  - reflexivity.
  - destruct c, prev, is_al. all: simpl. all: rewrite <- IH. all: reflexivity.
Qed.

(* ********** *)

(* W4: A single European separator between two European numbers changes to a European number. A single common separator between two numbers of the same type changes to that type. *)

Fixpoint rule_w4 (text : list bidi_class) (prev : bidi_class) : list bidi_class :=
  match text, prev with
  | [], _ => []
  | [c], _ => [c]
  | ES :: (EN :: _) as text', EN => EN :: rule_w4 text' EN
  | CS :: (EN :: _) as text', EN => EN :: rule_w4 text' EN
  | CS :: (AN :: _) as text', AN => AN :: rule_w4 text' AN
  | c :: text', _ => c :: rule_w4 text' c
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

(* Compute (run_test rule_w4 test_cases_rule_w4). *)

(* ********** *)

Fixpoint rule_w14 (text : list bidi_class) (prev : bidi_class) (is_al : bool) : list bidi_class :=
  match text, prev with
  | [] , _ => []
  | EN :: text', _ => (if is_al then AN else EN) :: rule_w14 text' (if is_al then AN else EN) is_al
  | NSM :: text', EN => (if is_al then AN else EN) :: rule_w14 text' (if is_al then AN else EN) is_al
  | NSM :: text', (LRI | RLI | FSI | PDI) => ON :: rule_w14 text' ON is_al
  | NSM :: text', _ => (if eq_dec_bidi_class prev AL then R else prev) :: rule_w14 text' prev (next_is_al prev is_al)
  | ES :: (EN :: _) as text', EN => (if is_al then ES else EN) :: rule_w14 text' (if is_al then ES else EN) is_al
  | CS :: (EN :: _) as text', EN => (if is_al then CS else EN) :: rule_w14 text' (if is_al then CS else EN) is_al
  | ES :: (EN :: _) as text', AN => (if is_al then ES else ES) :: rule_w14 text' (if is_al then ES else EN) is_al
  | CS :: (EN :: _) as text', AN => (if is_al then AN else CS) :: rule_w14 text' (if is_al then AN else CS) is_al
  | CS :: (AN :: _) as text', AN => AN :: rule_w14 text' AN is_al (* TODO: no if bc there are no ENs *)
  | c :: text', _ => (if eq_dec_bidi_class c AL then R else c) :: rule_w14 text' c (next_is_al c is_al)
  end.

(* Fixpoint rule_w14 (is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
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
  end. *)

Lemma w14_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al : bool),
  rule_w14 text prev is_al = rule_w4 (rule_w13 text prev is_al) prev.
Proof.
  induction text as [ | c text' IH].
  - reflexivity.
  - destruct prev, is_al, c.
    all: simpl.
    all: repeat rewrite -> IH.
    all: destruct text' as [ | c' text''].
    all: try destruct c'.
    all: auto.
Qed.
(* TODO: flip equation order *)

(* ********** *)

(* W5: A sequence of European terminators adjacent to European numbers changes to all European numbers. *)

Fixpoint w5_before_en (text : list bidi_class) : bool :=
  match text with
  | [] => false (* TODO: eos? *)
  | EN :: _ => true
  | ET :: text' => w5_before_en text'
  | _ :: _ => false
  end.

Fixpoint rule_w5 (text : list bidi_class) (after_en : bool) : list bidi_class :=
  match text with
  | [] => []
  | ET :: text' => (if after_en && w5_before_en text' then EN else ET) :: rule_w5 text' after_en
  | EN :: text' => EN :: rule_w5 text' true
  | c :: text' => c :: rule_w5 text' false
  end.
(* TODO: bug when after_en but not before_en *)

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

(* Compute (run_test rule_w5 test_cases_rule_w5). *)

(* ********** *)

Fixpoint w15_before_en (text : list bidi_class) (prev : bidi_class) (is_al : bool) : bool :=
  match text, prev with
  | EN :: _, _ => negb is_al
  | ES :: EN :: _, EN => negb is_al
  | CS :: EN :: _, EN => negb is_al
  | ET :: text', _ => w15_before_en text' ET is_al
  | NSM :: _, EN => negb is_al
  | NSM :: text', ET => w15_before_en text' ET is_al
  | _, _ => false
  end.

Lemma w15_before_en_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al : bool),
  w15_before_en text prev is_al = w5_before_en (rule_w14 text prev is_al).
Proof.
  induction text as [ | c text' IH].
  - destruct prev; reflexivity.
  - destruct prev, is_al, c.
    all: simpl.
    all: repeat rewrite -> IH.
    all: destruct text' as [ | c' text''].
    all: try destruct c'.
    all: auto.
Qed.

Fixpoint rule_w15 (text : list bidi_class) (prev : bidi_class) (is_al after_en : bool) : list bidi_class :=
  match text, prev with
  | [], _ => []
  | NSM :: text', AL => R :: rule_w15 text' AL true false
  | NSM :: text', L => L :: rule_w15 text' L false false
  | NSM :: text', R => R :: rule_w15 text' R false false
  | NSM :: text', LRI => ON :: rule_w15 text' ON is_al false
  | NSM :: text', RLI => ON :: rule_w15 text' ON is_al false
  | NSM :: text', FSI => ON :: rule_w15 text' ON is_al false
  | NSM :: text', PDI => ON :: rule_w15 text' ON is_al false
  | NSM :: text', EN => (if is_al then AN else EN) :: rule_w15 text' (if is_al then AN else EN) is_al (negb is_al)
  | NSM :: text', ET => if after_en && w15_before_en text' ET is_al then EN :: rule_w15 text' ET is_al after_en else ET :: rule_w15 text' ET is_al after_en
  | NSM :: text', _ => prev :: rule_w15 text' prev is_al false
  | AL :: text', _ => R  :: rule_w15 text' AL true false
  | L  :: text', _ => L  :: rule_w15 text' L false false
  | R  :: text', _ => R  :: rule_w15 text' R false false
  | EN :: text', _ => (if is_al then AN else EN) :: rule_w15 text' (if is_al then AN else EN) is_al (negb is_al)
  | ES :: (EN :: _) as text', EN => (if is_al then ES else EN) :: rule_w15 text' (if is_al then ES else EN) is_al (negb is_al)
  | CS :: (EN :: _) as text', EN => (if is_al then CS else EN) :: rule_w15 text' (if is_al then CS else EN) is_al (negb is_al)
  | CS :: (EN :: _) as text', AN => (if is_al then AN else CS):: rule_w15 text' (if is_al then AN else CS) is_al false
  | CS :: (AN :: _) as text', AN => AN :: rule_w15 text' AN is_al false
  | ET :: text', _ => if after_en && w15_before_en text' ET is_al then EN :: rule_w15 text' ET is_al after_en else ET :: rule_w15 text' ET is_al after_en
  | c :: text', _ => c :: rule_w15 text' c is_al false
  end.

Lemma w15_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en : bool),
rule_w15 text prev is_al after_en = rule_w5 (rule_w14 text prev is_al) after_en.
Proof.
intro text.
induction text as [ | c text' IH]; intros prev is_al after_en.
- destruct prev; reflexivity.
- simpl.
  destruct is_al, after_en.
  + simpl.
    destruct c, prev; try (simpl; repeat rewrite <- IH; progress auto).
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * rewrite -> IH. destruct text' as [ | c' text'']; auto; destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET true)); auto.
  + simpl.
    destruct c, prev; try (simpl; repeat rewrite <- IH; progress auto).
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
  + simpl.
    destruct c, prev; try (simpl; repeat rewrite <- IH; progress auto).
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * rewrite -> IH. simpl. rewrite w15_before_en_correct. simpl. destruct (w5_before_en (rule_w14 text' ET false)); auto.
  + simpl.
    destruct c, prev; try (simpl; repeat rewrite <- IH; progress auto).
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
    * repeat rewrite -> IH. destruct text' as [ | c' text'']; auto. destruct c'; auto.
Qed.

(* ********** *)

(* W6. All remaining separators and terminators (after the application of W4 and W5) change to Other Neutral. *)

Fixpoint rule_w6 (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | (ES | ET | CS) :: text' => ON :: rule_w6 text'
  | c :: text' => c :: rule_w6 text'
  end.

(* AN ET    → AN ON

L  ES EN → L  ON EN

EN CS AN → EN ON AN

ET AN    → ON AN *)

(* Definition test_aux' (func: list bidi_class -> list bidi_class) (text expected : list bidi_class) : bool :=
  eqb_list bidi_class eqb_bidi_class (func text) expected. *)

(* Definition run_test' (func : list bidi_class -> list bidi_class) (tests : list (list bidi_class * list bidi_class)) : bool :=
  fold_right (fun '(text, expected) acc => test_aux' func text expected && acc) true tests. *)

Definition test_cases_rule_w6 : list (list bidi_class * list bidi_class) :=
  [
    ([AN; ET], [AN; ON]);
    ([L; ES; EN], [L; ON; EN]);
    ([EN; CS; AN], [EN; ON; AN]);
    ([ET; AN], [ON; AN])
  ].

(* Compute (run_test' rule_w6 test_cases_rule_w6). *)

(* ********** *)

(* TODO: remove all false and true *)

Fixpoint rule_w16 (text : list bidi_class) (prev : bidi_class) (is_al after_en : bool) : list bidi_class :=
  match text, prev with
  | [], _ => []
  | NSM :: text', AL => R :: rule_w16 text' AL true false
  | NSM :: text', L => L :: rule_w16 text' L false false
  | NSM :: text', R => R :: rule_w16 text' R false false
  | NSM :: text', LRI => ON :: rule_w16 text' ON is_al false
  | NSM :: text', RLI => ON :: rule_w16 text' ON is_al false
  | NSM :: text', FSI => ON :: rule_w16 text' ON is_al false
  | NSM :: text', PDI => ON :: rule_w16 text' ON is_al false
  | NSM :: text', EN => (if is_al then AN else EN) :: rule_w16 text' (if is_al then AN else EN) is_al (negb is_al)
  | NSM :: text', ET => if after_en && w15_before_en text' ET is_al then EN :: rule_w16 text' ET is_al after_en else ON :: rule_w16 text' ET is_al after_en
  | NSM :: text', ES => ON :: rule_w16 text' ES is_al false
  | NSM :: text', CS => ON :: rule_w16 text' CS is_al false
  | NSM :: text', _ => prev :: rule_w16 text' prev is_al false
  | AL :: text', _ => R  :: rule_w16 text' AL true false
  | L  :: text', _ => L  :: rule_w16 text' L false false
  | R  :: text', _ => R  :: rule_w16 text' R false false
  | EN :: text', _ => (if is_al then AN else EN) :: rule_w16 text' (if is_al then AN else EN) is_al (negb is_al)
  | ES :: (EN :: _) as text', EN => (if is_al then ON else EN) :: rule_w16 text' (if is_al then ES else EN) is_al (negb is_al)
  | CS :: (EN :: _) as text', EN => (if is_al then ON else EN) :: rule_w16 text' (if is_al then CS else EN) is_al (negb is_al)
  | CS :: (EN :: _) as text', AN => (if is_al then AN else ON) :: rule_w16 text' (if is_al then AN else CS) is_al false
  | CS :: (AN :: _) as text', AN => AN :: rule_w16 text' AN is_al false
  | ET :: text', _ => if after_en && w15_before_en text' ET is_al then EN :: rule_w16 text' ET is_al after_en else ON :: rule_w16 text' ET is_al after_en
  | ES :: text', _ => ON :: rule_w16 text' ES is_al false
  | CS :: text', _ => ON :: rule_w16 text' CS is_al false
  | c  :: text', _ => c :: rule_w16 text' c is_al false
  end.

Lemma w16_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en : bool),
  rule_w16 text prev is_al after_en = rule_w6 (rule_w15 text prev is_al after_en).
Proof.
  intro text.
  induction text as [ | c text' IH]; intros prev is_al after_en.
  - destruct prev; reflexivity.
  - destruct text' as [ | c' text''].
    + destruct c, after_en, is_al, prev; auto.
    + remember (c' :: text'') as text' eqn:H_text'.
      destruct c, after_en, is_al, prev; simpl; repeat rewrite -> IH; try reflexivity; rewrite -> H_text'; destruct c'; auto;
      rewrite <- H_text';
      remember (w15_before_en text' _ _) as res_w15; destruct res_w15; reflexivity.
Qed.

(* ********** *)

(* W7. Search backward from each instance of a European number until the first strong type (R, L, or sos) is found. If an L is found, then change the type of the European number to L. *)

Fixpoint rule_w7 (text : list bidi_class) (after_l : bool) : list bidi_class :=
  match text with
  | [] => []
  | EN :: text' => (if after_l then L else EN) :: rule_w7 text' after_l
  | L  :: text' => L :: rule_w7 text' true
  | R  :: text' => R :: rule_w7 text' false
  | c  :: text' => c :: rule_w7 text' after_l
  end.

(* L  NI EN → L  NI  L

R  NI EN → R  NI  EN *)

Definition test_cases_rule_w7 : list (bool * list bidi_class * list bidi_class) :=
  [
    (true, [L; ON; EN], [L; ON; L]);
    (true, [R; ON; EN], [R; ON; EN]);
    (true, [L; R; EN; L; ON; EN], [L; R; EN; L; ON; L])
  ].

(* Compute (run_test bool rule_w7 test_cases_rule_w7). *)

(* ********** *)

Fixpoint rule_w17 (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) : list bidi_class :=
  match text, prev with
  | [], _ => []
  | NSM :: text', AL => R  :: rule_w17 text' prev true false false
  | NSM :: text', L => L  :: rule_w17 text' prev false false true
  | NSM :: text', R => R  :: rule_w17 text' prev false false false
  | NSM :: text', LRI => ON :: rule_w17 text' ON is_al false after_l
  | NSM :: text', RLI => ON :: rule_w17 text' ON is_al false after_l
  | NSM :: text', FSI => ON :: rule_w17 text' ON is_al false after_l
  | NSM :: text', PDI => ON :: rule_w17 text' ON is_al false after_l
  | NSM :: text', EN => (if is_al then AN else (if after_l then L else EN)) :: rule_w17 text' (if is_al then AN else EN) is_al (negb is_al) after_l
  | NSM :: text', ET => (if after_en && w15_before_en text' ET is_al then (if after_l then L else EN) else ON) :: rule_w17 text' ET is_al after_en after_l
  | NSM :: text', ES => ON :: rule_w17 text' prev is_al false after_l
  | NSM :: text', CS => ON :: rule_w17 text' prev is_al false after_l
  | NSM :: text', _ => prev :: rule_w17 text' prev is_al false after_l
  | AL :: text', _ => R  :: rule_w17 text' AL true false false
  | L  :: text', _ => L  :: rule_w17 text' L false false true
  | R  :: text', _ => R  :: rule_w17 text' R false false false
  | EN :: text', _ => (if is_al then AN else (if after_l then L else EN)) :: rule_w17 text' (if is_al then AN else EN) is_al (negb is_al) after_l
  | ES :: text', _ =>
    match next text', prev with
    | Some EN, EN => (if is_al then ON else (if after_l then L else EN)) :: rule_w17 text' (if is_al then ES else EN) is_al (negb is_al) after_l
    | _, _ => ON :: rule_w17 text' ES is_al false after_l
    end

  (* | ES :: (EN :: _) as text', EN => (if is_al then ON else (if after_l then L else EN)) :: rule_w17 text' (if is_al then ES else EN) is_al (negb is_al) after_l
  | ES :: text', _ => ON :: rule_w17 text' ES is_al false after_l *)

  | CS :: text', _ =>
    match next text', prev with
    | Some EN, EN => (if is_al then ON else (if after_l then L else EN)) :: rule_w17 text' (if is_al then CS else EN) is_al (negb is_al) after_l
    | Some EN, AN => (if is_al then AN else ON) :: rule_w17 text' (if is_al then AN else CS) is_al false after_l
    | Some AN, AN => AN :: rule_w17 text' AN is_al false after_l
    | _, _ => ON :: rule_w17 text' CS is_al false after_l
    end

  (* | CS :: (EN :: _) as text', EN => (if is_al then ON else (if after_l then L else EN)) :: rule_w17 text' (if is_al then CS else EN) is_al (negb is_al) after_l
  | CS :: (EN :: _) as text', AN => (if is_al then AN else ON) :: rule_w17 text' (if is_al then AN else CS) is_al false after_l
  | CS :: (AN :: _) as text', AN => AN :: rule_w17 text' AN is_al false after_l
  | CS :: text', _ => ON :: rule_w17 text' CS is_al false after_l *)
  | ET :: text', _ => (if after_en && w15_before_en text' ET is_al then (if after_l then L else EN) else ON) :: rule_w17 text' ET is_al after_en after_l
  | c  :: text', _ => c :: rule_w17 text' c is_al false after_l
  end.

(* TODO: change order of prev *)
Lemma w17_correct: forall (text : list bidi_class) (after_l after_en is_al : bool) (prev : bidi_class),
  rule_w17 text prev is_al after_en after_l = rule_w7 (rule_w16 text prev is_al after_en) after_l.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros after_l after_en is_al prev.
  - destruct prev; auto.
  - destruct text' as [ | c' text''].
    + destruct c, after_en, is_al, prev; auto.
    + remember (c, after_l, after_en, is_al, prev).
      remember (c' :: text'') as text' eqn:H_text'.
      destruct c, after_l, after_en, is_al, prev; simpl; repeat rewrite -> IH; try reflexivity; rewrite -> H_text'; destruct c'; auto;
      rewrite <- H_text'; try (remember (w15_before_en text' _ _) as res_w15; destruct res_w15); try reflexivity.
Qed.

(* NI : Neutral or Isolate formatting character (B, S, WS, ON, FSI, LRI, RLI, PDI). *)
      
(* N1. A sequence of NIs takes the direction of the surrounding strong text if the text on both sides has the same direction. European and Arabic numbers act as if they were R in terms of their influence on NIs. The start-of-sequence (sos) and end-of-sequence (eos) types are used at isolating run sequence boundaries. *)

Definition is_ni (c : bidi_class) : bool.
Admitted.

Definition is_strong (c : bidi_class) : bool :=
  match c with
  | L | R | EN | AN => true
  | _ => false
  end.

Definition is_number (c : bidi_class) : bool.
Admitted.

Fixpoint n1_next_strong (text : list bidi_class) : bidi_class :=
  match text with
  | [] => eos
  (* | c :: text' => if is_strong c || is_number c then c else n1_next_strong text' *)
  | (L | R | EN | AN) as c :: _ => c (* What about AL *)
  | _ :: text' => n1_next_strong text'
  end.

Definition unknown {A : Set} : A.
Admitted.

Fixpoint w17n1_next_strong (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) : bidi_class :=
  match text with
  | [] => eos
  | (L :: text') => L
  | (R :: text') => R
  | (AL :: text') => R
  | (AN :: text') => AN
  | (B :: text') => w17n1_next_strong text' B is_al false after_l
  | (S :: text') => w17n1_next_strong text' S is_al false after_l
  | (WS :: text') => w17n1_next_strong text' WS is_al false after_l
  | (ON :: text') => w17n1_next_strong text' ON is_al false after_l
  | (LRI :: text') => w17n1_next_strong text' LRI is_al false after_l
  | (RLI :: text') => w17n1_next_strong text' RLI is_al false after_l
  | (FSI :: text') => w17n1_next_strong text' FSI is_al false after_l
  | (PDI :: text') => w17n1_next_strong text' PDI is_al false after_l
  | (EN :: text') => if is_al then AN else if after_l then L else EN
  | (ES :: text') =>
    match next text' with
    | (Some L) => w17n1_next_strong text' ES is_al false after_l
    | (Some R) => w17n1_next_strong text' ES is_al false after_l
    | (Some AL) => w17n1_next_strong text' ES is_al false after_l
    | (Some ES) => w17n1_next_strong text' ES is_al false after_l
    | (Some ET) => w17n1_next_strong text' ES is_al false after_l
    | (Some AN) => w17n1_next_strong text' ES is_al false after_l
    | (Some CS) => w17n1_next_strong text' ES is_al false after_l
    | (Some NSM) => w17n1_next_strong text' ES is_al false after_l
    | (Some B) => w17n1_next_strong text' ES is_al false after_l
    | (Some S) => w17n1_next_strong text' ES is_al false after_l
    | (Some WS) => w17n1_next_strong text' ES is_al false after_l
    | (Some ON) => w17n1_next_strong text' ES is_al false after_l
    | (Some LRI) => w17n1_next_strong text' ES is_al false after_l
    | (Some RLI) => w17n1_next_strong text' ES is_al false after_l
    | (Some FSI) => w17n1_next_strong text' ES is_al false after_l
    | (Some PDI) => w17n1_next_strong text' ES is_al false after_l
    | (Some EN) =>
      match prev with
      | L => w17n1_next_strong text' ES is_al false after_l
      | R => w17n1_next_strong text' ES is_al false after_l
      | AL => w17n1_next_strong text' ES is_al false after_l
      | ES => w17n1_next_strong text' ES is_al false after_l
      | ET => w17n1_next_strong text' ES is_al false after_l
      | AN => w17n1_next_strong text' ES is_al false after_l
      | CS => w17n1_next_strong text' ES is_al false after_l
      | NSM => w17n1_next_strong text' ES is_al false after_l
      | B => w17n1_next_strong text' ES is_al false after_l
      | S => w17n1_next_strong text' ES is_al false after_l
      | WS => w17n1_next_strong text' ES is_al false after_l
      | ON => w17n1_next_strong text' ES is_al false after_l
      | LRI => w17n1_next_strong text' ES is_al false after_l
      | RLI => w17n1_next_strong text' ES is_al false after_l
      | FSI => w17n1_next_strong text' ES is_al false after_l
      | PDI => w17n1_next_strong text' ES is_al false after_l
      | EN =>
        if is_al
        then w17n1_next_strong text' ES is_al false after_l
        else
          if after_l
          then L
          else EN
      end
    | None => w17n1_next_strong text' ES is_al false after_l
    end
  | (ET :: text') =>
    if after_en && w15_before_en text' ET is_al
    then if after_l then L else EN
    else w17n1_next_strong text' ET is_al after_en after_l
  | (c :: text') => unknown text prev is_al after_en after_l

  end.

(* Fixpoint w17n1_next_strong (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) : bidi_class :=
  match text with
  | [] => eos
  | L :: text' => L
  | R :: text' => R
  | AL :: text' => R
  | AN :: text' => AN
  | B :: text' => w17n1_next_strong text' B is_al false after_l
  | S :: text' => w17n1_next_strong text' S is_al false after_l
  | WS :: text' => w17n1_next_strong text' WS is_al false after_l
  | ON :: text' => w17n1_next_strong text' ON is_al false after_l
  | LRI :: text' => w17n1_next_strong text' LRI is_al false after_l
  | RLI :: text' => w17n1_next_strong text' RLI is_al false after_l
  | FSI :: text' => w17n1_next_strong text' FSI is_al false after_l
  | PDI :: text' => w17n1_next_strong text' PDI is_al false after_l

  | EN :: text' =>
    match (if is_al then AN else if after_l then L else EN) with
    | L | R | EN | AN => if is_al then AN else if after_l then L else EN
    | _ => w17n1_next_strong text' (if is_al then AN else EN) is_al (negb is_al) after_l
    end

  | ET :: text' =>
    match (if after_en && w15_before_en text' ET is_al then if after_l then L else EN else ON) with
    | L | R | EN | AN => if after_en && w15_before_en text' ET is_al then if after_l then L else EN else ON
    | _ => w17n1_next_strong text' ET is_al after_en after_l
    end

  | NSM :: text' =>
    match prev with
    | L => L
    | R => R
    | AL => R
    | EN =>
      match (if is_al then AN else if after_l then L else EN) with
      | L | R | EN | AN => if is_al then AN else if after_l then L else EN
      | _ => w17n1_next_strong text' (if is_al then AN else EN) is_al (negb is_al) after_l
      end
    | ET =>
      match (if after_en && w15_before_en text' ET is_al then if after_l then L else EN else ON) with
      | L | R | EN | AN => if after_en && w15_before_en text' ET is_al then if after_l then L else EN else ON
      | _ => w17n1_next_strong text' ET is_al after_en after_l
      end
    | ES => w17n1_next_strong text' ES is_al false after_l
    | AN => AN
    | CS => w17n1_next_strong text' CS is_al false after_l
    | NSM => w17n1_next_strong text' NSM is_al false after_l
    | B => w17n1_next_strong text' B is_al false after_l
    | S => w17n1_next_strong text' S is_al false after_l
    | WS => w17n1_next_strong text' WS is_al false after_l
    | ON => w17n1_next_strong text' ON is_al false after_l
    | LRI => w17n1_next_strong text' ON is_al false after_l
    | RLI => w17n1_next_strong text' ON is_al false after_l
    | FSI => w17n1_next_strong text' ON is_al false after_l
    | PDI => w17n1_next_strong text' ON is_al false after_l
    end

  | CS :: text' =>
    match next text' with
    | Some L => w17n1_next_strong text' CS is_al false after_l
    | Some R => w17n1_next_strong text' CS is_al false after_l
    | Some AL => w17n1_next_strong text' CS is_al false after_l
    | Some ES => w17n1_next_strong text' CS is_al false after_l
    | Some ET => w17n1_next_strong text' CS is_al false after_l
    | Some CS => w17n1_next_strong text' CS is_al false after_l
    | Some NSM => w17n1_next_strong text' CS is_al false after_l
    | Some B => w17n1_next_strong text' CS is_al false after_l
    | Some S => w17n1_next_strong text' CS is_al false after_l
    | Some WS => w17n1_next_strong text' CS is_al false after_l
    | Some ON => w17n1_next_strong text' CS is_al false after_l
    | Some LRI => w17n1_next_strong text' CS is_al false after_l
    | Some RLI => w17n1_next_strong text' CS is_al false after_l
    | Some FSI => w17n1_next_strong text' CS is_al false after_l
    | Some PDI => w17n1_next_strong text' CS is_al false after_l
    | Some EN =>
      match prev with
      | L => w17n1_next_strong text' CS is_al false after_l
      | R => w17n1_next_strong text' CS is_al false after_l
      | AL => w17n1_next_strong text' CS is_al false after_l
      | EN => match (if is_al then ON else if after_l then L else EN) with
        | L | R | EN | AN => if is_al then ON else if after_l then L else EN
        | _ => w17n1_next_strong text' (if is_al then CS else EN) is_al (negb is_al) after_l
        end
      | ES => w17n1_next_strong text' CS is_al false after_l
      | ET => w17n1_next_strong text' CS is_al false after_l
      | AN => match (if is_al then AN else ON) with
        | L | R | EN | AN => if is_al then AN else ON
        | _ => w17n1_next_strong text' (if is_al then AN else CS) is_al false after_l
        end
      | CS => w17n1_next_strong text' CS is_al false after_l
      | NSM => w17n1_next_strong text' CS is_al false after_l
      | B => w17n1_next_strong text' CS is_al false after_l
      | S => w17n1_next_strong text' CS is_al false after_l
      | WS => w17n1_next_strong text' CS is_al false after_l
      | ON => w17n1_next_strong text' CS is_al false after_l
      | LRI => w17n1_next_strong text' CS is_al false after_l
      | RLI => w17n1_next_strong text' CS is_al false after_l
      | FSI => w17n1_next_strong text' CS is_al false after_l
      | PDI => w17n1_next_strong text' CS is_al false after_l
      end
    | Some AN =>
      match prev with
      | L => w17n1_next_strong text' CS is_al false after_l
      | R => w17n1_next_strong text' CS is_al false after_l
      | AL => w17n1_next_strong text' CS is_al false after_l
      | EN => w17n1_next_strong text' CS is_al false after_l
      | ES => w17n1_next_strong text' CS is_al false after_l
      | ET => w17n1_next_strong text' CS is_al false after_l
      | AN => AN
      | CS => w17n1_next_strong text' CS is_al false after_l
      | NSM => w17n1_next_strong text' CS is_al false after_l
      | B => w17n1_next_strong text' CS is_al false after_l
      | S => w17n1_next_strong text' CS is_al false after_l
      | WS => w17n1_next_strong text' CS is_al false after_l
      | ON => w17n1_next_strong text' CS is_al false after_l
      | LRI => w17n1_next_strong text' CS is_al false after_l
      | RLI => w17n1_next_strong text' CS is_al false after_l
      | FSI => w17n1_next_strong text' CS is_al false after_l
      | PDI => w17n1_next_strong text' CS is_al false after_l
      end
    | None => w17n1_next_strong text' CS is_al false after_l
    end

  | ES :: text' =>
    match next text' with
    | Some L => w17n1_next_strong text' ES is_al false after_l
    | Some R => w17n1_next_strong text' ES is_al false after_l
    | Some AL => w17n1_next_strong text' ES is_al false after_l
    | Some ES => w17n1_next_strong text' ES is_al false after_l
    | Some ET => w17n1_next_strong text' ES is_al false after_l
    | Some AN => w17n1_next_strong text' ES is_al false after_l
    | Some CS => w17n1_next_strong text' ES is_al false after_l
    | Some NSM => w17n1_next_strong text' ES is_al false after_l
    | Some B => w17n1_next_strong text' ES is_al false after_l
    | Some S => w17n1_next_strong text' ES is_al false after_l
    | Some WS => w17n1_next_strong text' ES is_al false after_l
    | Some ON => w17n1_next_strong text' ES is_al false after_l
    | Some LRI => w17n1_next_strong text' ES is_al false after_l
    | Some RLI => w17n1_next_strong text' ES is_al false after_l
    | Some FSI => w17n1_next_strong text' ES is_al false after_l
    | Some PDI => w17n1_next_strong text' ES is_al false after_l
    | Some EN =>
      match prev with
      | L => w17n1_next_strong text' ES is_al false after_l
      | R => w17n1_next_strong text' ES is_al false after_l
      | AL => w17n1_next_strong text' ES is_al false after_l
      | EN =>
        match (if is_al then ON else if after_l then L else EN) with
        | L | R | EN | AN => if is_al then ON else if after_l then L else EN
        | _ => w17n1_next_strong text' (if is_al then ES else EN) is_al (negb is_al) after_l
        end
      | ES => w17n1_next_strong text' ES is_al false after_l
      | ET => w17n1_next_strong text' ES is_al false after_l
      | AN => w17n1_next_strong text' ES is_al false after_l
      | CS => w17n1_next_strong text' ES is_al false after_l
      | NSM => w17n1_next_strong text' ES is_al false after_l
      | B => w17n1_next_strong text' ES is_al false after_l
      | S => w17n1_next_strong text' ES is_al false after_l
      | WS => w17n1_next_strong text' ES is_al false after_l
      | ON => w17n1_next_strong text' ES is_al false after_l
      | LRI => w17n1_next_strong text' ES is_al false after_l
      | RLI => w17n1_next_strong text' ES is_al false after_l
      | FSI => w17n1_next_strong text' ES is_al false after_l
      | PDI => w17n1_next_strong text' ES is_al false after_l
      end
    | None => w17n1_next_strong text' ES is_al false after_l
    end
  end. *)


  (* | [], _ => eos
  | ((L | R | AN) as c) :: text', _ => c
  | AL :: text', _ => R
  | EN :: text', _ => if is_al then AN else if after_l then L else EN
  | ET :: text', _ =>
    if after_en && w15_before_en text' ET is_al
    then if after_l then L else EN
    else w17n1_next_strong text' ET is_al after_en after_l
  | ((B | S | WS | ON | LRI | RLI | FSI | PDI | ES | CS) as c) :: text', _ => w17n1_next_strong text' c is_al false after_l
  | NSM :: text', (L | R | AN) as c => c
  | NSM :: text', AL => R
  | NSM :: text', (ES | CS | NSM | B | S | WS | ON) as c => w17n1_next_strong text' c is_al false after_l
  | NSM :: text', (LRI | RLI | FSI | PDI) => w17n1_next_strong text' ON is_al false after_l
  | NSM :: text', EN => if is_al then AN else if after_l then L else EN
  | NSM :: text', ET =>
    if after_en && w15_before_en text' ET is_al
    then if after_l then L else EN
    else w17n1_next_strong text' ET is_al after_en after_l
  end. *)

Lemma rule_w17_n1_next_strong_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool),
  w17n1_next_strong text prev is_al after_en after_l = n1_next_strong (rule_w17 text prev is_al after_en after_l).
  Proof.
  induction text as [ | c text' IH ]; intros.
  - simpl. reflexivity.
  - destruct c.
    all: simpl.
    all: try rewrite <- IH.
    all: try reflexivity.
    + destruct is_al, after_l; reflexivity.
    + destruct (next text') as [c' | ] eqn:H_text'; simpl; try rewrite <- IH; try reflexivity.
      * destruct c'; simpl; try rewrite <- IH; try reflexivity.
        { destruct prev; simpl; try rewrite <- IH; try reflexivity.
          { destruct is_al, after_l; simpl; try reflexivity. }
        }
    + destruct after_en, (w15_before_en text' ET is_al), after_l; simpl; reflexivity.
    admit.
    + admit.
    + destruct prev.
      * admit.
      * admit.
      * admit.
      *
            {


      * destruct b; simpl; try rewrite <- IH.
      { admit. }
      { admit. }
      { admit. }
      { destruct prev; simpl; try (rewrite <- IH).
        { admit. }
        { admit. }
        { admit. }
        { destruct is_al, after_l.
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
      * simpl. rewrite <- IH.

    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * rewrite <- IH. admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    all: safdsaf. all: asdfasfd
  try rewrite <- IH
  }
  {
Qed.
(* Proof.
  induction text as [ | c text' IH ]; intros.
  - simpl. reflexivity.
  - destruct c; simpl; try rewrite <- IH; try reflexivity.
    + destruct (next text') as [ c' | ].
      * destruct c'; simpl; try rewrite <- IH; try reflexivity.
        destruct prev; simpl; try rewrite <- IH; try reflexivity.
      * simpl; try rewrite <- IH; try reflexivity.

    + destruct (next text') as [ c' | ].
      * destruct c', prev; simpl; try rewrite <- IH; try reflexivity.
      * simpl; try rewrite <- IH; try reflexivity.

    + destruct prev; simpl; try rewrite <- IH; try reflexivity.
Qed. *)

Fixpoint rule_n1 (text : list bidi_class) (prev : bidi_class) : list bidi_class :=
  match text, prev, n1_next_strong text with
  | [], _, _ => []
  | (B | S | WS | ON | FSI | LRI | RLI | PDI) :: text', L, L => L :: rule_n1 text' prev
  | (B | S | WS | ON | FSI | LRI | RLI | PDI) :: text', (R | EN | AN), (R | EN | AN) => R :: rule_n1 text' prev
  | ((B | S | WS | ON | FSI | LRI | RLI | PDI) as c):: text', _, _ => c :: rule_n1 text' prev (* TODO: as default *)
  | c :: text', _, _ => c :: rule_n1 text' (if is_strong c then c else prev)
  end.

Fixpoint rule_w17n1 (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) (prev_n1 : bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | L :: text' => L :: rule_w17n1 text' L false false true L
  | R :: text' => R :: rule_w17n1 text' R false false false R
  | AN :: text' => AN :: rule_w17n1 text' AN is_al false after_l AN
  | AL :: text' => R :: rule_w17n1 text' AL true false false R

  | EN :: text' =>
    (if is_al then AN else if after_l then L else EN)
      :: rule_w17n1 text' (if is_al then AN else EN) is_al (negb is_al) after_l
           (if is_strong (if is_al then AN else if after_l then L else EN)
            then if is_al then AN else if after_l then L else EN
            else prev_n1)

  | ((B | S | WS | ON | LRI | RLI | FSI | PDI) as c) :: text' =>
    match prev_n1 with
    | L =>
        match w17n1_next_strong text' c is_al false after_l with
        | L => L :: rule_w17n1 text' c is_al false after_l prev_n1
        | _ => c :: rule_w17n1 text' c is_al false after_l prev_n1
        end
    | R | EN | AN =>
        match w17n1_next_strong text' c is_al false after_l with
        | R | EN | AN => R :: rule_w17n1 text' c is_al false after_l prev_n1
        | _ => c :: rule_w17n1 text' c is_al false after_l prev_n1
        end
    | _ => c :: rule_w17n1 text' c is_al false after_l prev_n1
    end

  | ES :: text' =>
    match next text' with
    | None =>
      match prev_n1 with
      | L =>
          match w17n1_next_strong text' ES is_al false after_l with
          | L => L :: rule_w17n1 text' ES is_al false after_l prev_n1
          | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
          end
      | R | EN | AN =>
          match w17n1_next_strong text' ES is_al false after_l with
          | R | EN | AN => R :: rule_w17n1 text' ES is_al false after_l prev_n1
          | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
          end
      | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
      end

    | Some ((L | R | AL | ES | ET | AN | CS | NSM | B | S | WS | ON | LRI | RLI | FSI | PDI) as c') =>
      match prev_n1 with
      | L =>
          match w17n1_next_strong text' ES is_al false after_l with
          | L => L :: rule_w17n1 text' ES is_al false after_l prev_n1
          | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
          end
      | R | EN | AN =>
          match w17n1_next_strong text' ES is_al false after_l with
          | R | EN | AN => R :: rule_w17n1 text' ES is_al false after_l prev_n1
          | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
          end
      | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
      end

    | Some EN =>
      match prev with
      | EN =>
        if negb is_al
        then ((if after_l then L else EN)
        :: rule_w17n1 text' EN false true after_l
             (if is_strong (if after_l then L else EN) then if after_l then L else EN else prev_n1))
        else (
          match prev_n1 with
          | L =>
              match w17n1_next_strong text' ES true false after_l with
              | L => L :: rule_w17n1 text' ES true false after_l prev_n1
              | _ => ON :: rule_w17n1 text' ES true false after_l prev_n1
              end
          | R | EN | AN =>
              match w17n1_next_strong text' ES true false after_l with
              | R | EN | AN => R :: rule_w17n1 text' ES true false after_l prev_n1
              | _ => ON :: rule_w17n1 text' ES true false after_l prev_n1
              end
          | _ => ON :: rule_w17n1 text' ES true false after_l prev_n1
          end)
      | _ =>
        match prev_n1 with
        | L =>
            match w17n1_next_strong text' ES is_al false after_l with
            | L => L :: rule_w17n1 text' ES is_al false after_l prev_n1
            | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
            end
        | R | EN | AN =>
            match w17n1_next_strong text' ES is_al false after_l with
            | R | EN | AN => R :: rule_w17n1 text' ES is_al false after_l prev_n1
            | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
            end
        | _ => ON :: rule_w17n1 text' ES is_al false after_l prev_n1
        end
      end
    end

  | ET :: text' =>
    if (after_en && w15_before_en text' ET is_al)
    then match prev_n1 with
      | L =>
          match w17n1_next_strong text' ET is_al after_en after_l with
          | L => L :: rule_w17n1 text' ET is_al after_en after_l prev_n1
          | _ => (if after_l then L else EN) :: rule_w17n1 text' ET is_al after_en after_l prev_n1
          end
      | R | EN | AN =>
          match w17n1_next_strong text' ET is_al after_en after_l with
          | R | EN | AN => R :: rule_w17n1 text' ET is_al after_en after_l prev_n1
          | _ => (if after_l then L else EN) :: rule_w17n1 text' ET is_al after_en after_l prev_n1
          end
      | _ => (if after_l then L else EN) :: rule_w17n1 text' ET is_al after_en after_l prev_n1
      end
    else unknown text prev is_al after_en after_l prev_n1
  | _ :: text' => unknown text prev is_al after_en after_l prev_n1

  end.

(* Inductive rule_w17n1_prev : forall (prev_w17n1 prev_w17 prev_n1 : bidi_class), Prop :=
| rule_w17n1_prev_id : forall (c : bidi_class), rule_w17n1_prev c c c
| rule_w17n1_prev_R_AL_R : rule_w17n1_prev R AL R. *)

Lemma rule_w17n1_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) (prev_n1 : bidi_class),
  rule_w17n1 text prev is_al after_en after_l prev_n1 = rule_n1 (rule_w17 text prev is_al after_en after_l) prev_n1.
Proof.
  induction text as [ | c text' IH ]; intros.
  - simpl. reflexivity.
  (* - destruct c; simpl; try rewrite <- (IH _) by constructor; try reflexivity. *)
  - destruct c; simpl; try rewrite <- IH; try rewrite <- rule_w17_n1_next_strong_correct; try reflexivity.
    + destruct is_al, after_l; reflexivity.
    + destruct (next text') as [ c' | ].
      * destruct c'; simpl; try rewrite <- IH; try rewrite <- rule_w17_n1_next_strong_correct; try reflexivity.
        destruct prev; simpl; try rewrite <- IH; try rewrite <- rule_w17_n1_next_strong_correct; try reflexivity.
        destruct is_al; try rewrite <- IH; simpl.
        { reflexivity. }
        { destruct after_l; reflexivity. }
      * simpl. rewrite <- IH. rewrite <- rule_w17_n1_next_strong_correct. reflexivity.
    + destruct (after_en && w15_before_en text' ET is_al).
      * rewrite <- IH.
        destruct after_l.
        { destruct prev_n1.
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
        {
      *
    + admit.
    + admit.
    + destruct prev_n1; try reflexivity.
    + destruct prev_n1; try reflexivity.
      * reflexivity.
      *
    ; simpl; try rewrite <- IH; try reflexivity.
    + admit.
    + admit.
    + admit.
  + admit.
  + simpl; try rewrite <- IH; try reflexivity.
  + simpl; try rewrite <- IH; try reflexivity.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl. rewrite <- IH. reflexivity.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + simpl; try rewrite <- IH; try reflexivity. admit.
  + 
  
    + admit. (* Lemma rule_w17 AL == rule_w17 R *)
    +

(* N2. Any remaining NIs take the embedding direction.

NI → e

The embedding direction for the given NI character is derived from its embedding level: L if the character is set to an even level, and R if the level is odd. *)

Fixpoint rule_n2 (level : nat) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | (B | S | WS | ON | FSI | LRI | RLI | PDI) :: text' => (if Nat.even level then L else R) :: rule_n2 level text'
  | c :: text' => c :: rule_n2 level text'
  end.
