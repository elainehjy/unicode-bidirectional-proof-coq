(* unicode-bidi-proof_v4.v *)
(* Mon 16 Sep 2024 *)

Set Default Goal Selector "!". (* Force use of bullets. *)

Require Import Bool List.
Import ListNotations.

Require generated_test_cases.

(*
Module generated_test_cases.
Load "generated_test_cases.v".
End generated_test_cases.
*)

Check generated_test_cases.bidi_class.

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

Parameter sos : bidi_class.
Parameter eos : bidi_class.
 
(* Definition sos := R.
   Definition eos := R. *)

Definition next (text : list bidi_class) : option bidi_class :=
  match text with
  | [] => None
  | c :: _ => Some c
  end.

(* ********** *)

(* W1: Examine each nonspacing mark (NSM) in the isolating run sequence, and change the type of the NSM to Other Neutral if the previous character is an isolate initiator or PDI, and to the type of the previous character otherwise. If the NSM is at the start of the isolating run sequence, it will get the type of sos. *)

Fixpoint rule_w1 (text : list bidi_class) (prev : bidi_class) : list bidi_class :=
  match text, prev with
  | [], _ => []
  | NSM :: text', (LRI | RLI | FSI | PDI) => ON :: rule_w1 text' ON
  | NSM :: text', _ => prev :: rule_w1 text' prev
  | c :: text', _ => c :: rule_w1 text' c
  end.

(* Assume in this example that sos is R:

AL  NSM NSM → AL  AL  AL

sos NSM     → sos R

LRI NSM     → LRI ON

PDI NSM     → PDI ON *)

(* helper function for writing the tests *)

Definition test_aux {V : Type} (func : list bidi_class -> V -> list bidi_class) (text : list bidi_class) (param : V) (expected : list bidi_class) : bool :=
  eqb_list bidi_class eqb_bidi_class (func text param) expected.

Definition run_test {V : Type} (func : list bidi_class -> V -> list bidi_class) (tests : list (list bidi_class * V * list bidi_class)) : bool :=
  fold_right (fun '(text, param, expected) acc => test_aux func text param expected && acc) true tests.

Definition test_cases_rule_w1 : list (list bidi_class * bidi_class * list bidi_class) :=
  [
    ([AL; NSM; NSM], sos, [AL; AL; AL]);
    ([LRI; NSM], sos, [LRI; ON]);
    ([PDI; NSM], sos, [PDI; ON])
  ].

Compute (run_test rule_w1 test_cases_rule_w1).

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

(* AL EN     → AL AN

AL NI EN  → AL NI AN

sos NI EN → sos NI EN

L NI EN   → L NI EN

R NI EN   → R NI EN *)

Definition test_cases_rule_w2 : list (list bidi_class * bool * list bidi_class) :=
  [
    ([AL; EN], true, [AL; AN]);
    ([AL; B; EN], true, [AL; B; AN]);
    ([R; S; EN], true, [R; S; EN]);
    ([L; ON; EN], true, [L; ON; EN])
  ].

Compute (run_test rule_w2 test_cases_rule_w2).

(* ********** *)

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
  intro text.
  destruct text; auto.
Qed.

Lemma w12_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al : bool),
  rule_w12 text prev is_al = rule_w2 (rule_w1 text prev) is_al.
Proof.
  intro text.
  induction text as [ | c text' IH].
  - reflexivity.
  - destruct c, prev, is_al; simpl; rewrite <- IH; try rewrite -> w12_EN_AN; reflexivity.
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
  intro text.
  induction text as [ | c text' IH].
  - reflexivity.
  - destruct c, prev, is_al; simpl; rewrite <- IH; reflexivity.
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

Definition test_cases_rule_w4 : list (list bidi_class * bidi_class * list bidi_class) :=
  [
    ([EN; ES; EN], sos, [EN; EN; EN]);
    ([EN; CS; EN], sos, [EN; EN; EN]);
    ([AN; CS; AN], sos, [AN; AN; AN]);
    ([EN; ES; EN; ES; EN], sos, [EN; EN; EN; EN; EN])
  ].

Compute (run_test rule_w4 test_cases_rule_w4).

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
  | CS :: (AN :: _) as text', AN => AN :: rule_w14 text' AN is_al
  | c :: text', _ => (if eq_dec_bidi_class c AL then R else c) :: rule_w14 text' c (next_is_al c is_al)
  end.

Lemma w14_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al : bool),
  rule_w14 text prev is_al = rule_w4 (rule_w13 text prev is_al) prev.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros prev is_al.
  - reflexivity.
  - destruct prev, is_al, c; simpl; repeat rewrite -> IH; destruct text' as [ | c' text'']; try destruct c'; auto.
Qed.

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
  | ET :: text' => (if after_en || w5_before_en text' then EN else ET) :: rule_w5 text' after_en (*if after_en && w5_before_en text'*)
  | EN :: text' => EN :: rule_w5 text' true
  | c :: text' => c :: rule_w5 text' false
  end.

(* ET ET EN → EN EN EN

EN ET ET → EN EN EN

AN ET EN → AN EN EN *)

Definition test_cases_rule_w5 : list (list bidi_class * bool * list bidi_class) :=
  [
    ([ET; ET; EN], true, [EN; EN; EN]);
    ([EN; ET; ET], true, [EN; EN; EN]);
    ([AN; ET; EN], true, [AN; EN; EN]);
    ([AN; ET; EN; ET; EN; ET; AN; ET], true, [AN; EN; EN; EN; EN; EN; AN; ET])
  ].

Compute (run_test rule_w5 test_cases_rule_w5).

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
  intro text.
  induction text as [ | c text' IH]; intros prev is_al.
  - destruct prev; reflexivity.
  - destruct prev, is_al, c; simpl; repeat rewrite -> IH; destruct text' as [ | c' text'']; try destruct c'; auto.
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
  | NSM :: text', ET => (if after_en || w15_before_en text' ET is_al then EN else ET) :: rule_w15 text' ET is_al after_en (* && *)
  | NSM :: text', _ => prev :: rule_w15 text' prev is_al false
  | AL :: text', _ => R  :: rule_w15 text' AL true false
  | L  :: text', _ => L  :: rule_w15 text' L false false
  | R  :: text', _ => R  :: rule_w15 text' R false false
  | EN :: text', _ => (if is_al then AN else EN) :: rule_w15 text' (if is_al then AN else EN) is_al (negb is_al)
  | ES :: (EN :: _) as text', EN => (if is_al then ES else EN) :: rule_w15 text' (if is_al then ES else EN) is_al (negb is_al)
  | CS :: (EN :: _) as text', EN => (if is_al then CS else EN) :: rule_w15 text' (if is_al then CS else EN) is_al (negb is_al)
  | CS :: (EN :: _) as text', AN => (if is_al then AN else CS):: rule_w15 text' (if is_al then AN else CS) is_al false
  | CS :: (AN :: _) as text', AN => AN :: rule_w15 text' AN is_al false
  | ET :: text', _ => (if after_en || w15_before_en text' ET is_al then EN else ET) :: rule_w15 text' ET is_al after_en (* && *)
  | c :: text', _ => c :: rule_w15 text' c is_al false
  end.

Lemma w15_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en : bool),
    rule_w15 text prev is_al after_en = rule_w5 (rule_w14 text prev is_al) after_en.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros prev is_al after_en.
  - destruct prev; reflexivity.
  - destruct c, prev, is_al, after_en; simpl; repeat rewrite <- IH; try progress auto; repeat rewrite -> IH.
    all: try (rewrite -> w15_before_en_correct; destruct w5_before_en; auto).
    all: try (destruct text' as [ | c' text'']; auto; destruct c'; auto).
Qed.

(*
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
        try rewrite -> rule_w15_before_en_correct; auto;
        rewrite -> H_text' in IH; rewrite <- IH; reflexivity.
Qed.
*)

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
  | NSM :: text', ET => (if after_en || w15_before_en text' ET is_al then EN else ON) :: rule_w16 text' ET is_al after_en (* && *)
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
  | ET :: text', _ => (if after_en || w15_before_en text' ET is_al then EN else ON) :: rule_w16 text' ET is_al after_en (* && *)
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
    + destruct c, prev, is_al, after_en; auto.
    + remember (c' :: text'') as text' eqn:H_text'.
      destruct c, prev, is_al, after_en; simpl; repeat rewrite -> IH; try reflexivity; rewrite -> H_text'; destruct c'; auto;
      rewrite <- H_text'; destruct w15_before_en; reflexivity.
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

Definition test_cases_rule_w7 : list (list bidi_class * bool * list bidi_class) :=
  [
    ([L; ON; EN], true, [L; ON; L]);
    ([R; ON; EN], true, [R; ON; EN]);
    ([L; R; EN; L; ON; EN], true, [L; R; EN; L; ON; L])
  ].

Compute (run_test rule_w7 test_cases_rule_w7).

(* ********** *)

Fixpoint rule_w17 (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) : list bidi_class :=
  match text, prev with
  | [], _ => []
  | NSM :: text', AL => R :: rule_w17 text' prev true false false
  | NSM :: text', L  => L :: rule_w17 text' prev false false true
  | NSM :: text', R  => R :: rule_w17 text' prev false false false
  | NSM :: text', LRI => ON :: rule_w17 text' ON is_al false after_l
  | NSM :: text', RLI => ON :: rule_w17 text' ON is_al false after_l
  | NSM :: text', FSI => ON :: rule_w17 text' ON is_al false after_l
  | NSM :: text', PDI => ON :: rule_w17 text' ON is_al false after_l
  | NSM :: text', EN => (if is_al then AN else (if after_l then L else EN)) :: rule_w17 text' (if is_al then AN else EN) is_al (negb is_al) after_l
  | NSM :: text', ET => (if after_en || w15_before_en text' ET is_al then (if after_l then L else EN) else ON) :: rule_w17 text' ET is_al after_en after_l (* && *)
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
  | ET :: text', _ => (if after_en || w15_before_en text' ET is_al then (if after_l then L else EN) else ON) :: rule_w17 text' ET is_al after_en after_l (* && *)
  | c  :: text', _ => c :: rule_w17 text' c is_al false after_l
  end.

(*
Fixpoint rule_w17 (after_l after_en is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | AL, NSM :: text' => R  :: rule_w17 false false true AL text'
  | L,  NSM :: text' => L  :: rule_w17 true false false L text'
  | R,  NSM :: text' => R  :: rule_w17 false false false R text'
  | LRI, NSM :: text' => ON :: rule_w17 after_l false is_al ON text'
  | RLI, NSM :: text' => ON :: rule_w17 after_l false is_al ON text'
  | FSI, NSM :: text' => ON :: rule_w17 after_l false is_al ON text'
  | PDI, NSM :: text' => ON :: rule_w17 after_l false is_al ON text'
  | EN, NSM :: text' => (if is_al then AN else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | ET, NSM :: text' =>
      if after_en
      then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
      else if rule_w15_before_en is_al ET text'
           then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
           else ON :: rule_w17 after_l after_en is_al ET text'
  | ES, NSM :: text' => ON :: rule_w17 after_l false is_al ES text'
  | CS, NSM :: text' => ON :: rule_w17 after_l false is_al CS text'
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
 *)

Lemma w17_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool),
  rule_w17 text prev is_al after_en after_l = rule_w7 (rule_w16 text prev is_al after_en) after_l.
Proof.
  intro text.
  induction text as [ | c text' IH]; intros prev is_al after_en after_l.
  - destruct prev; auto.
  - destruct text' as [ | c' text''].
    + destruct c, prev, is_al, after_en, after_l; auto.      
    + remember (c' :: text'') as text' eqn:H_text'.
      destruct c, prev, is_al, after_en, after_l; simpl; repeat rewrite -> IH; try reflexivity; rewrite -> H_text'; destruct c'; auto;
      rewrite <- H_text'; destruct w15_before_en; reflexivity.
Qed.

(* ********** *)

(* NI : Neutral or Isolate formatting character (B, S, WS, ON, FSI, LRI, RLI, PDI). *)
      
(* N1. A sequence of NIs takes the direction of the surrounding strong text if the text on both sides has the same direction. European and Arabic numbers act as if they were R in terms of their influence on NIs. The start-of-sequence (sos) and end-of-sequence (eos) types are used at isolating run sequence boundaries. *)

Definition is_ni (c : bidi_class) : bool :=
  match c with
  | B | S | WS | ON | FSI | LRI | RLI | PDI => true
  | _ => false
  end.

Definition is_strong (c : bidi_class) : bool :=
  match c with
  | L | R | EN | AN => true
  | _ => false
  end.

Fixpoint n1_next_strong (text : list bidi_class) : bidi_class :=
  match text with
  | [] => eos
  (* | c :: text' => if is_strong c || is_number c then c else n1_next_strong text' *)
  | (L | R | EN | AN) as c :: _ => c (* What about AL *)
  | _ :: text' => n1_next_strong text'
  end.

Definition unknown {A : Set} : A.
Admitted.

(* Fixpoint w17n1_next_strong (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) : bidi_class :=
  match text with
  | [] => eos
  | (c :: text') => unknown text prev is_al after_en after_l
  end. *)

(* Lemma rule_w17_n1_next_strong_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool),
  w17n1_next_strong text prev is_al after_en after_l = n1_next_strong (rule_w17 text prev is_al after_en after_l).
Proof.
  intro text.
  induction text as [ | c text' IH]; intros.
  - reflexivity.
  - destruct c.
    all: simpl.
    all: try rewrite <- IH.
    all: try reflexivity.
    + destruct is_al, after_en.
      reflexivity. *)

Fixpoint w17n1_next_strong (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) : bidi_class :=
  match text with
  | [] => eos
  | L :: text' => L
  | R :: text' => R
  | AL :: text' => R
  | AN :: text' => AN
  | (B | S | WS | ON | LRI | RLI | FSI | PDI) as c :: text' => w17n1_next_strong text' c is_al false after_l
  | EN :: text' =>
    match (if is_al then AN else if after_l then L else EN) with
    | L | R | EN | AN => if is_al then AN else if after_l then L else EN
    | _ => w17n1_next_strong text' (if is_al then AN else EN) is_al (negb is_al) after_l
    end

  | ET :: text' =>
    match (if after_en || w15_before_en text' ET is_al then if after_l then L else EN else ON) with (* && *)
    | L | R | EN | AN => if after_en || w15_before_en text' ET is_al then if after_l then L else EN else ON (* && *)
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
      match (if after_en || w15_before_en text' ET is_al then if after_l then L else EN else ON) with (* && *)
      | L | R | EN | AN => if after_en || w15_before_en text' ET is_al then if after_l then L else EN else ON (* && *)
      | _ => w17n1_next_strong text' ET is_al after_en after_l
      end
    | (ES | CS | NSM | B | S | WS | ON) as c => w17n1_next_strong text' c is_al false after_l
    | AN => AN
    | (LRI | RLI | FSI | PDI) => w17n1_next_strong text' ON is_al false after_l
    end

  | CS :: text' =>
    match next text' with
    | Some EN =>
      match prev with
      | EN => match (if is_al then ON else if after_l then L else EN) with
              | L | R | EN | AN => if is_al then ON else if after_l then L else EN
              | _ => w17n1_next_strong text' (if is_al then CS else EN) is_al (negb is_al) after_l
        end
      | AN => match (if is_al then AN else ON) with
              | L | R | EN | AN => if is_al then AN else ON
              | _ => w17n1_next_strong text' (if is_al then AN else CS) is_al false after_l
        end
      | _ => w17n1_next_strong text' CS is_al false after_l
      end
    | Some AN =>
      match prev with
      | AN => AN
      | _ => w17n1_next_strong text' CS is_al false after_l
      end
    | _ => w17n1_next_strong text' CS is_al false after_l
    end

  | ES :: text' =>
    match next text' with
    | Some EN =>
      match prev with
      | EN =>
        match (if is_al then ON else if after_l then L else EN) with
        | L | R | EN | AN => if is_al then ON else if after_l then L else EN
        | _ => w17n1_next_strong text' (if is_al then ES else EN) is_al (negb is_al) after_l
        end
      | _ => w17n1_next_strong text' ES is_al false after_l
      end
    | _ => w17n1_next_strong text' ES is_al false after_l
    end
  end. 

Lemma rule_w17_n1_next_strong_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool),
  w17n1_next_strong text prev is_al after_en after_l = n1_next_strong (rule_w17 text prev is_al after_en after_l).
Proof.
  intro text.
  induction text as [ | c text' IH ]; intros.
  - reflexivity.
  - destruct c; simpl; try rewrite <- IH; try reflexivity.
    + destruct (next text') as [ c' | ].
      * destruct c', prev; simpl; try rewrite <- IH; try reflexivity.
      * simpl; try rewrite <- IH; try reflexivity.

    + destruct (next text') as [ c' | ].
      * destruct c', prev; simpl; try rewrite <- IH; try reflexivity.
      * simpl; try rewrite <- IH; try reflexivity.

    + destruct prev; simpl; try rewrite <- IH; try reflexivity.
Qed.

(*
Fixpoint rule_n1_between_strong (prev : bidi_class) (text : list bidi_class) : bool := 
  match prev, text with
  | _, [] => match prev, eos with
             | L, L => true
             | R,  R => true
             | EN, R => true
             | AN, R => true
             | _, _ => false
             end
  | L, L :: _ => true
  | _, L :: _ => false
  | R,  R :: _ => true
  | EN, R :: _ => true
  | AN, R :: _ => true
  | _,  R :: _ => false
  | R,  AN :: _ => true
  | EN, AN :: _ => true
  | AN, AN :: _ => true
  | _,  AN :: _ => false
  | R,  EN :: _ => true
  | EN, EN :: _ => true
  | AN, EN :: _ => true
  | _,  EN :: _ => false
  | _, _ :: text' => rule_n1_between_strong prev text' 
  end.

Fixpoint rule_n1 (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | c :: text' =>
      if is_ni c && rule_n1_between_strong prev text'
      then match prev with
           (* | L => L :: rule_n1 L text' *)
           | EN | AN | R => R :: rule_n1 R text'
           | _ => prev :: rule_n1 prev text'
           end
      else c :: rule_n1 c text'
  end.
 *)

Fixpoint rule_n1 (text : list bidi_class) (prev : bidi_class) : list bidi_class :=
  match text, prev, n1_next_strong text with
  | [], _, _ => []
  | (B | S | WS | ON | FSI | LRI | RLI | PDI) :: text', L, L => L :: rule_n1 text' prev
  | (B | S | WS | ON | FSI | LRI | RLI | PDI) :: text', (R | EN | AN), (R | EN | AN) => R :: rule_n1 text' prev
  | ((B | S | WS | ON | FSI | LRI | RLI | PDI) as c):: text', _, _ => c :: rule_n1 text' prev (* TODO: as default *)
  | c :: text', _, _ => c :: rule_n1 text' (if is_strong c then c else prev)
  end.

(* L  NI   L  →   L  L   L

 R  NI   R  →   R  R   R

 R  NI  AN  →   R  R  AN

 R  NI  EN  →   R  R  EN

AN  NI   R  →  AN  R   R

AN  NI  AN  →  AN  R  AN

AN  NI  EN  →  AN  R  EN

EN  NI   R  →  EN  R   R

EN  NI  AN  →  EN  R  AN

EN  NI  EN  →  EN  R  EN *)

Definition test_cases_rule_n1 : list (list bidi_class * bidi_class * list bidi_class) :=
  [
    ([L; ON; ON; R], sos, [L; ON; ON; R]);
    ([L; ON; B; WS; L], sos, [L; L; L; L; L]);
    ([R; ON; ON; R], sos, [R; R; R; R]);
    ([R; ON; AN], sos, [R; R; AN]);
    ([R; ON; EN], sos, [R; R; EN]);
    ([AN; PDI; FSI; ON; R], sos, [AN; R; R; R; R]);
    ([AN; ON; ON; AN], sos, [AN; R; R; AN]);
    ([AN; ON; EN], sos, [AN; R; EN]);
    ([EN; ON; B; WS; R], sos, [EN; R; R; R; R]);
    ([EN; ON; AN], sos, [EN; R; AN]);
    ([EN; ON; EN], sos, [EN; R; EN])
  ].

Compute (run_test rule_n1 test_cases_rule_n1).

(* ********** *)


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
    if (after_en || w15_before_en text' ET is_al) (* && *)
    then (if after_l then L else EN) :: rule_w17n1 text' ET is_al after_en after_l (if is_strong (if after_l then L else EN) then if after_l then L else EN else prev_n1)
    else match prev_n1 with
         | L =>
             match w17n1_next_strong text' ET is_al false after_l with
             | L => L :: rule_w17n1 text' ET is_al false after_l prev_n1
             | _ => ON :: rule_w17n1 text' ET is_al false after_l prev_n1
             end
         | (R | EN | AN) =>
             match w17n1_next_strong text' ET is_al false after_l with
             | R | EN | AN => R :: rule_w17n1 text' ET is_al false after_l prev_n1
             | _ => ON :: rule_w17n1 text' ET is_al false after_l prev_n1
             end
         | _ => ON :: rule_w17n1 text' ET is_al false after_l prev_n1
         end
  | CS :: text' =>
      match (next text') with
      | Some L =>
          match prev_n1 with
          | L =>
              match n1_next_strong (rule_w17 text' CS is_al false after_l) with
              | L => L :: rule_w17n1 text' CS is_al false after_l prev_n1
              | _ => ON :: rule_w17n1 text' CS is_al false after_l prev_n1
              end
          | R | EN | AN =>
                       match n1_next_strong (rule_w17 text' CS is_al false after_l) with
                       | R | EN | AN => R :: rule_w17n1 text' CS is_al false after_l prev_n1
                       | _ => ON :: rule_w17n1 text' CS is_al false after_l prev_n1
                       end
          | _ => ON :: rule_w17n1 text' CS is_al false after_l prev_n1
         end
    | Some AN =>
        match prev with
        | AN => AN :: rule_w17n1 text' AN is_al false after_l prev_n1
        | _ => ON :: rule_w17n1 text' CS is_al false after_l prev_n1
        end
    | _ => ON :: rule_w17n1 text' CS is_al false after_l prev_n1
    end
      
  | _ :: text' => unknown text prev is_al after_en after_l prev_n1

  end.

Lemma rule_w17n1_correct: forall (text : list bidi_class) (prev : bidi_class) (is_al after_en after_l : bool) (prev_n1 : bidi_class),
  rule_w17n1 text prev is_al after_en after_l prev_n1 = rule_n1 (rule_w17 text prev is_al after_en after_l) prev_n1.
Proof.
  induction text as [ | c text' IH ]; intros.
  - reflexivity.
  - destruct c; simpl; try rewrite <- IH; try rewrite <- rule_w17_n1_next_strong_correct; try reflexivity.
    + destruct is_al, after_l; reflexivity.
    + destruct (next text') as [ c' | ].
      * destruct c'; simpl; try rewrite <- IH; try rewrite <- rule_w17_n1_next_strong_correct; try reflexivity.
        destruct prev; simpl; try rewrite <- IH; try rewrite <- rule_w17_n1_next_strong_correct; try reflexivity.
        destruct is_al, after_l; try rewrite <- IH; reflexivity. 
      * simpl. rewrite <- IH. rewrite <- rule_w17_n1_next_strong_correct. reflexivity.
    + destruct after_en, w15_before_en.
      * simpl.
        destruct after_l; reflexivity.
      * simpl.
        destruct after_l; reflexivity.
      * simpl.
        destruct after_l; reflexivity.
      * simpl. rewrite -> IH. reflexivity.
    + destruct (next text') as [ c' | ].
      * destruct c'.
        { simpl. destruct prev_n1.
          { destruct w17n1_next_strong, n1_next_strong; rewrite -> IH.
          { rewrite -> IH.
          rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
        { rewrite -> IH. admit. }
      * simpl.

        rewrite <- IH.
        destruct after_l.
        { simpl.
          destruct prev_n1.
          { destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
          { simpl. destruct (w17n1_next_strong text' ET is_al after_en true); auto. }
        {
      *


(* Definition check_rule_n1_w17_between_strong_spec (after_l after_en is_al : bool) (prev : bidi_class) (text : list bidi_class) : bool :=
  Bool.eqb (rule_n1_between_strong prev (rule_w17 after_l after_en is_al prev text)) (rule_n1_w17_between_strong after_l after_en is_al prev text).

QuickChick check_rule_n1_w17_between_strong_spec. 

Fixpoint rule_n1_w17 (after_l after_en is_al : bool) (prev : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | AL, NSM :: text' => R  :: rule_n1_w17 false false true AL text'
  | L,  NSM :: text' => L  :: rule_n1_w17 true false false L text'
  | R,  NSM :: text' => R  :: rule_n1_w17 false false false R text'
  | LRI, NSM :: text' => ON :: rule_n1_w17 after_l false is_al ON text'
  | RLI, NSM :: text' => ON :: rule_n1_w17 after_l false is_al ON text'
  | FSI, NSM :: text' => ON :: rule_n1_w17 after_l false is_al ON text'
  | PDI, NSM :: text' => ON :: rule_n1_w17 after_l false is_al ON text'
  | EN, NSM :: text' => (if is_al then AN else (if after_l then L else EN)) :: rule_n1_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | ET, NSM :: text' =>
      if after_en
      then (if after_l then L else EN) :: rule_n1_w17 after_l after_en is_al ET text'
      else if rule_n1_between_strong prev text'
           then (if after_l then L else EN) :: rule_n1_w17 after_l after_en is_al ET text'
           else ON :: rule_n1_w17 after_l after_en is_al ET text'
  | ES, NSM :: text' => ON :: rule_n1_w17 after_l false is_al ES text'
  | CS, NSM :: text' => ON :: rule_n1_w17 after_l false is_al CS text'
  | _,  NSM :: text' => prev :: rule_n1_w17 after_l false is_al prev text'
  | _, AL :: text' => R  :: rule_n1_w17 false false true AL text'
  | _, L  :: text' => L  :: rule_n1_w17 true false false L text'
  | _, R  :: text' => R  :: rule_n1_w17 false false false R text'
  | _, EN :: text' => (if is_al then AN else (if after_l then L else EN)) :: rule_n1_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) text'
  | EN, ES :: (EN :: _) as text' => (if is_al then ON else (if after_l then L else EN)) :: rule_n1_w17 after_l (if is_al then false else true) is_al (if is_al then ES else EN) text'
  | EN, CS :: (EN :: _) as text' => (if is_al then ON else (if after_l then L else EN)) :: rule_n1_w17 after_l (if is_al then false else true) is_al (if is_al then CS else EN) text'
  | AN, CS :: (EN :: _) as text' => (if is_al then AN else ON) :: rule_n1_w17 after_l false is_al (if is_al then AN else CS) text'
  | AN, CS :: (AN :: _) as text' => AN :: rule_n1_w17 after_l false is_al AN text'
  | _, ET :: text' =>
      if after_en
      then (if after_l then L else EN) :: rule_n1_w17 after_l after_en is_al ET text'
      else if rule_n1_between_strong prev text'
           then (if after_l then L else EN) :: rule_n1_w17 after_l after_en is_al ET text'
           else ON :: rule_n1_w17 after_l after_en is_al ET text'
  | _, ES :: text' => ON :: rule_n1_w17 after_l false is_al ES text'
  | _, CS :: text' => ON :: rule_n1_w17 after_l false is_al CS text'
  | _, c  :: text' => if is_ni c && rule_n1_between_strong prev text'
                      then match prev with
                           | EN | AN | R => R :: rule_n1_w17 after_l after_en is_al R text'
                           | _ => prev :: rule_n1_w17 after_l after_en is_al prev text'
                           end
                      else c :: rule_n1_w17 after_l after_en is_al c text'
  end.

Compute (rule_n1 R (rule_w17 true true true R [ES])).
Compute (rule_n1_w17 true true true R [ES]).

Lemma rule_n1_w17_correct: forall (text : list bidi_class) (after_l after_en is_al : bool) (prev : bidi_class),
    rule_n1 prev (rule_w17 after_l after_en is_al prev text) = rule_n1_w17 after_l after_en is_al prev text.
Proof.
  intro text. 
  induction text as [ | c text' IH]; intros after_l after_en is_al prev.
  - destruct prev; auto.
  - destruct text' as [ | c' text''].
    + destruct c, after_l, after_en, is_al, prev; auto. Admitted.
   (* + remember (c' :: text'') as text' eqn:H_text'.
      destruct c, after_l, after_en, is_al, prev; simpl; repeat rewrite <- IH; try reflexivity; rewrite -> H_text'; destruct c'; auto;
      rewrite <- H_text'; try (remember (rule_w15_before_en _ _ text') as res_w15; destruct res_w15); reflexivity. *)

*)

(* ********** *)

(* N2. Any remaining NIs take the embedding direction.

NI → e

The embedding direction for the given NI character is derived from its embedding level: L if the character is set to an even level, and R if the level is odd. *)

Fixpoint rule_n2 (dir : bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | c :: text' => if is_ni c
                  then dir :: rule_n2 dir text'
                  else c :: rule_n2 dir text'
  end.


(* 1. use boolean - ambiguous
 2. define a separate type - bidi_direction: need conversion func
qualifiers? e.g. bidi_direction.L
 3. define a subtype - Definition lbin : Type := {b1 : bin | Legal b1}.
 4. define a predicate - Fixpoint foo : (dir : bidi_class) (p : is_dir dir) ... *)

Compute (rule_n2 R [L; ON; PDI; R]).

(*
Assume in the following example that eos is L and sos is R. Then an application of N1 and N2 yields the following:

L   NI eos → L   L eos

R   NI eos → R   e eos

sos NI L   → sos e L

sos NI R   → sos R R *)

Fixpoint rule_n12_w17 (after_l after_en is_al : bool) (prev dir : bidi_class) (text : list bidi_class) : list bidi_class :=
  match prev, text with
  | _, [] => []
  | AL, NSM :: text' => R  :: rule_n12_w17 false false true AL dir text'
  | L,  NSM :: text' => L  :: rule_n12_w17 true false false L dir text'
  | R,  NSM :: text' => R  :: rule_n12_w17 false false false R dir text'
  | LRI, NSM :: text' => ON :: rule_n12_w17 after_l false is_al ON dir text'
  | RLI, NSM :: text' => ON :: rule_n12_w17 after_l false is_al ON dir text'
  | FSI, NSM :: text' => ON :: rule_n12_w17 after_l false is_al ON dir text'
  | PDI, NSM :: text' => ON :: rule_n12_w17 after_l false is_al ON dir text'
  | EN, NSM :: text' => (if is_al then AN else (if after_l then L else EN)) :: rule_n12_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) dir text'
  | ET, NSM :: text' =>
      if after_en
      then (if after_l then L else EN) :: rule_n12_w17 after_l after_en is_al ET dir text'
      else if rule_n1_between_strong prev text'
           then (if after_l then L else EN) :: rule_n12_w17 after_l after_en is_al ET dir text'
           else ON :: rule_n12_w17 after_l after_en is_al ET dir text'
  | ES, NSM :: text' => ON :: rule_n12_w17 after_l false is_al ES dir text'
  | CS, NSM :: text' => ON :: rule_n12_w17 after_l false is_al CS dir text'
  | _,  NSM :: text' => prev :: rule_n12_w17 after_l false is_al prev dir text'
  | _, AL :: text' => R  :: rule_n12_w17 false false true AL dir text'
  | _, L  :: text' => L  :: rule_n12_w17 true false false L dir text'
  | _, R  :: text' => R  :: rule_n12_w17 false false false R dir text'
  | _, EN :: text' => (if is_al then AN else (if after_l then L else EN)) :: rule_n12_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) dir text'
  | EN, ES :: (EN :: _) as text' => (if is_al then ON else (if after_l then L else EN)) :: rule_n12_w17 after_l (if is_al then false else true) is_al (if is_al then ES else EN) dir text'
  | EN, CS :: (EN :: _) as text' => (if is_al then ON else (if after_l then L else EN)) :: rule_n12_w17 after_l (if is_al then false else true) is_al (if is_al then CS else EN) dir text'
  | AN, CS :: (EN :: _) as text' => (if is_al then AN else ON) :: rule_n12_w17 after_l false is_al (if is_al then AN else CS) dir text'
  | AN, CS :: (AN :: _) as text' => AN :: rule_n12_w17 after_l false is_al AN dir text'
  | _, ET :: text' =>
      if after_en
      then (if after_l then L else EN) :: rule_n12_w17 after_l after_en is_al ET dir text'
      else if rule_n1_between_strong prev text'
           then (if after_l then L else EN) :: rule_n12_w17 after_l after_en is_al ET dir text'
           else ON :: rule_n12_w17 after_l after_en is_al ET dir text'
  | _, ES :: text' => ON :: rule_n12_w17 after_l false is_al ES dir text'
  | _, CS :: text' => ON :: rule_n12_w17 after_l false is_al CS dir text'
  | _, c  :: text' => if is_ni c
                      then if rule_n1_between_strong prev text'
                           then match prev with
                                | EN | AN | R => R :: rule_n12_w17 after_l after_en is_al R dir text'
                                | _ => prev :: rule_n12_w17 after_l after_en is_al prev dir text'
                                end
                           else dir :: rule_n12_w17 after_l after_en is_al dir dir text'
                      else c :: rule_n12_w17 after_l after_en is_al c dir text'
  end.

Lemma rule_n12_w17_correct: forall (text : list bidi_class) (after_l after_en is_al : bool) (prev dir : bidi_class),
    rule_n1 prev (rule_w17 after_l after_en is_al prev text) = rule_n12_w17 after_l after_en is_al prev dir text.
Proof.
  intro text. 
  induction text as [ | c text' IH]; intros after_l after_en is_al prev dir.
  - destruct prev; auto.
  - destruct text' as [ | c' text''].
    + destruct c, after_en, is_al, prev, dir; auto.

(* ********** *)


