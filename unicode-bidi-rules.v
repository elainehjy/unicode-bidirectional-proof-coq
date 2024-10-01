(* unicode-bidi-rules.v *)
(* Mon 23 Sep 2024 *)

Set Default Goal Selector "!". (* Force use of bullets. *)

Require Import Arith Bool List String Ascii.
Import ListNotations.

(*Require generated_test_cases.
Import generated_test_cases.*)

(*
Module generated_test_cases.
Load "generated_test_cases.v".
End generated_test_cases.
*)


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

(*
Definition apply_rules (input : list bidi_class) : list bidi_class :=
  let after_w1 := rule_w1 input ON in
  rule_w2 after_w1 false.

(* Function to test a single data case against the rules *)
Definition test_rule_on_case (input : list bidi_class) (expected_output : list bidi_class) : bool :=
  let result := apply_rules input in
  eqb_list bidi_class eqb_bidi_class result expected_output.

(* Function to test a single Test_Case (data field) *)
Definition test_on_data (tc_data : list (list bidi_class * nat)) : bool :=
  fold_left (fun acc (input_pair : list bidi_class * nat) =>
               let input := fst input_pair in
               let expected_output := input in  (* In this example, the expected output is the same as input; adjust based on actual expected output *)
               acc && test_rule_on_case input expected_output
            ) tc_data true.

(* Test all cases in the generated list *)
Definition test_all_cases (test_cases : list generated_test_cases.Test_Case) : bool :=
  fold_left (fun acc (tc : generated_test_cases.Test_Case) =>
               acc && test_on_data (generated_test_cases.data tc)
            ) test_cases true.

(* Sample test run *)
Compute (test_all_cases generated_test_cases.test_cases).
*)

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

(* ********** *)

(* W3: Change all ALs to R. *)

Fixpoint rule_w3 (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | AL :: text' => R :: rule_w3 text'
  | c  :: text' => c :: rule_w3 text'
  end.

(* ********** *)

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

(* ********** *)

(* W6. All remaining separators and terminators (after the application of W4 and W5) change to Other Neutral. *)

Fixpoint rule_w6 (text : list bidi_class) : list bidi_class :=
  match text with
  | [] => []
  | (ES | ET | CS) :: text' => ON :: rule_w6 text'
  | c :: text' => c :: rule_w6 text'
  end.

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

(* ********** *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* List the definitions you want to extract, typically the main functions or rules *)
Extraction "unicode_bidi_rules.ml" rule_w1 rule_w2 rule_w12.

(* end of unicode-bidi-rules.v *)
