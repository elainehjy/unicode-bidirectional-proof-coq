(* unicode_bidi_proof.v *)
(* Mon 17 June 2024 *)

(* Ltac destr term := let H := fresh in destruct term as [] _eqn: H. *)

Require Import Arith Bool List String Ascii.

(*equal function for lists *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
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
| BN 	(* Boundary_Neutral   default ignorables, non-characters, and control characters *)

(* Neutral *)
| B 	(* Paragraph_Separator *)
| S 	(* Segment_Separator   Tab *)
| WS 	(* White_Space *)
| ON 	(* Other_Neutrals *)

(* Explicit formatting *)
| LRE 	(* Left_To_Right_Embedding *)
| LRO 	(* Left_To_Right_Override *)
| RLE 	(* Right_To_Left_Embedding *)
| RLO 	(* Right_To_Left_Override *)
| PDF 	(* Pop_Directional_Format *)
| LRI	(* Left-to-Right Isolate *)
| RLI	(* Right-to-Left Isolate *)
| FSI	(* First Strong Isolate	*)
| PDI.	(* Pop Directional Isolate *)

(* equality for datatypes *)
Fixpoint eqb_bidi_class (bc1 bc2 : bidi_class) : bool :=
  match bc1, bc2 with
  | L, L => true
  | R, R => true
  | AL, AL => true
  | EN, EN => true
  | ES, ES => true
  | ET, ET => true
  | AN, AN => true
  | CS, CS => true
  | NSM, NSM => true
  | BN, BN => true
  | B, B => true
  | S, S => true
  | WS, WS => true
  | ON, ON => true
  | LRE, LRE => true
  | LRO, LRO => true
  | RLE, RLE => true
  | RLO, RLO => true
  | PDF, PDF => true
  | LRI, LRI => true
  | RLI, RLI => true
  | FSI, FSI => true
  | PDI, PDI => true
  | _, _ => false
  end.

(* assume sos has type bidi? *)
Definition sos := R.

(* ********** *)

(* W1: Examine each nonspacing mark (NSM) in the isolating run sequence, and change the type of the NSM to Other Neutral if the previous character is an isolate initiator or PDI, and to the type of the previous character otherwise. If the NSM is at the start of the isolating run sequence, it will get the type of sos. *)

(*
Fixpoint rule_w1 (prev : bidi_class) (text : list bidi_class) :=
  match text with
  | nil => prev :: nil
  | NSM :: text' =>
      match prev with
      | LRI | RLI | FSI | PDI => prev :: (rule_w1 ON text')
      | other => other :: rule_w1 other text'
      end
  | c :: text' => c :: (rule_w1 c text')
  end.
*)
(*
Definition rule_w1_pre (pre : list bidi_class) : bidi_class :=
  match pre with
  | nil => sos
  | c :: _ => c
  end. *)

Fixpoint rule_w1 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | NSM :: text' =>
      match pre with
      | LRI :: _ | RLI :: _ | FSI :: _ | PDI :: _ =>
                                           ON :: (rule_w1 (ON :: pre) text')
      | p :: _ => p :: (rule_w1 (p :: pre) text')
      | nil => sos :: rule_w1 (sos :: pre) text'
      end
  | c :: text' =>
      c :: rule_w1 (c :: pre) text'
  end.

(* Assume in this example that sos is R:

AL  NSM NSM → AL  AL  AL

sos NSM     → sos R

LRI NSM     → LRI ON

PDI NSM     → PDI ON *)

(* helper function for writing the tests, check for shorter syntax for list *)

Definition test_rule_w1 (candidate : list bidi_class  -> list bidi_class -> list bidi_class) :=
  (eqb_list bidi_class eqb_bidi_class (candidate nil (AL :: NSM :: NSM :: nil)) (AL :: AL :: AL :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (sos :: NSM :: nil)) (R :: R :: nil)) && (* sos :: R :: nil *)
    (eqb_list bidi_class eqb_bidi_class (candidate nil (LRI :: NSM :: nil)) (LRI :: ON :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (PDI :: NSM :: nil)) (PDI :: ON :: nil)).

Compute (test_rule_w1 rule_w1).

(* ********** *)

(* W2: Search backward from each instance of a European number until the first strong type (R, L, AL, or sos) is found. If an AL is found, change the type of the European number to Arabic number. *)

Fixpoint after_al (pre : list bidi_class) : bool :=
  match pre with
  | nil => false
  | AL :: _ => true
  | L :: _ => false
  | R :: _ => false
  | _ :: pre' => after_al pre'
  end.

Fixpoint rule_w2 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | EN :: text' =>
      let c := if after_al pre
               then AN
               else EN in
      c :: rule_w2 (c :: pre) text'
  | c :: text' =>
      c :: rule_w2 (c :: pre) text'
  end.


Compute (rule_w2 nil (AL :: EN :: nil)).

(* AL EN     → AL AN

AL NI EN  → AL NI AN

sos NI EN → sos NI EN

L NI EN   → L NI EN

R NI EN   → R NI EN *)

Definition test_rule_w2 (candidate : list bidi_class  -> list bidi_class -> list bidi_class) :=
  (eqb_list bidi_class eqb_bidi_class (candidate nil (AL :: EN :: nil)) (AL :: AN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (AL :: BN :: EN :: nil)) (AL :: BN :: AN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (sos :: BN :: EN :: nil)) (R :: BN :: EN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (L :: BN :: EN :: nil)) (L :: BN :: EN :: nil)).

Compute (test_rule_w2 rule_w2).

(* ********** *)

(* W3: Change all ALs to R. *)
(* [AL -> R] *)

(*
Fixpoint rule_w3 (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | AL :: text' => R :: rule_w3 text'
  | c  :: text' => c :: rule_w3 text'
  end.
 *)

Fixpoint rule_w3 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | AL :: text' => R :: rule_w3 (R :: pre) text'
  | c :: text' => c :: rule_w3 (c :: pre) text'
  end.

Definition test_rule_w3 (candidate : list bidi_class  -> list bidi_class -> list bidi_class) :=
  (eqb_list bidi_class eqb_bidi_class (candidate nil (AL :: nil)) (R :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (AL :: AL :: AL :: nil)) (R :: R :: R :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (AL :: AL :: EN :: AN :: nil)) (R :: R :: EN :: AN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (AL :: R :: AL :: LRI :: nil)) (R :: R :: R :: LRI :: nil)).

Compute (test_rule_w3 rule_w3).

(* ********** *)

(* W4: A single European separator between two European numbers changes to a European number. A single common separator between two numbers of the same type changes to that type. *)

(* one char at a time; might get rid of pre? *)

Fixpoint rule_w4 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | EN :: ES :: EN :: text' => EN :: EN :: EN :: rule_w4 (EN :: pre) text'
  | EN :: CS :: EN :: text' => EN :: EN :: EN :: rule_w4 (EN :: pre) text'
  | AN :: CS :: AN :: text' => AN :: AN :: AN :: rule_w4 (AN :: pre) text'
  | c :: text' => c :: rule_w4 (c :: pre) text'
  end.

Compute (rule_w4 nil (EN :: ES :: EN :: ES :: EN :: nil)).

(* EN ES EN → EN EN EN

EN CS EN → EN EN EN

AN CS AN → AN AN AN *)

Definition test_rule_w4 (candidate : list bidi_class  -> list bidi_class -> list bidi_class) :=
  (eqb_list bidi_class eqb_bidi_class (candidate nil (EN :: ES :: EN :: nil)) (EN :: EN :: EN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (EN :: CS :: EN :: nil)) (EN :: EN :: EN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (AN :: CS :: AN :: nil)) (AN :: AN :: AN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (L :: AN :: CS :: AN :: CS :: EN :: ES :: EN :: BN :: ES :: nil)) (L :: AN :: AN :: AN :: CS :: EN :: EN :: EN :: BN :: ES :: nil)).

Compute (test_rule_w4 rule_w4).

(* ********** *)

(* W5: A sequence of European terminators adjacent to European numbers changes to all European numbers. *)

(* ETs after EN *)
Fixpoint forward_pass_w5 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | ET :: text' =>
      let c := match pre with
               | EN :: _ => EN
               | _ => match text' with
                      | EN :: _ => EN
                      | _ => ET
                      end
               end in
      c :: forward_pass_w5 (c :: pre) text'
  | c :: text' =>
      c :: forward_pass_w5 (c :: pre) text'
  end.

(* ETs before an EN *)
Fixpoint backward_pass_w5 (post : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | ET :: text' =>
      let rest := backward_pass_w5 (text' ++ post) text' in
      let c := match rest with
               | EN :: _ => EN
               | _ => match text' with
                      | EN :: _ => EN
                      | _ => ET
                      end
               end in
      c :: rest
  | c :: text' =>
      c :: backward_pass_w5 (text' ++ post) text'
  end.

Definition rule_w5 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  backward_pass_w5 nil (forward_pass_w5 pre text).

Compute (rule_w5 nil (ET :: ET :: EN :: nil)).

(* Fixpoint rule_w5_before_en text :=
  match text with
  | nil => false
  | EN :: _ => true
  | ET :: text' => rule_w5_before_en text'
  | _ :: _ => false
  end.

Fixpoint rule_w5 after_en text :=
  match text with
  | nil => nil
  | ET :: text' =>
      if after_en then EN :: rule_w5 after_en text'
      else if rule_w5_before_en text' then EN :: rule_w5 after_en text'
           else ET :: rule_w5 after_en text'
  | EN :: text' => EN :: rule_w5 true text'
  | c :: text' => c :: rule_w5 false text'
  end. *)

(* ET ET EN → EN EN EN

EN ET ET → EN EN EN

AN ET EN → AN EN EN *)

Definition test_rule_w5 (candidate : list bidi_class  -> list bidi_class -> list bidi_class) :=
  (eqb_list bidi_class eqb_bidi_class (candidate nil (ET :: ET :: EN :: nil)) (EN :: EN :: EN :: nil)) &&
  (eqb_list bidi_class eqb_bidi_class (candidate nil (EN :: ET :: ET :: nil)) (EN :: EN :: EN :: nil)) &&
  (eqb_list bidi_class eqb_bidi_class (candidate nil (AN :: ET :: EN :: nil)) (AN :: EN :: EN :: nil)).

Compute (test_rule_w5 rule_w5).

(* ********** *)

(* W6. All remaining separators and terminators (after the application of W4 and W5) change to Other Neutral. *)

(* AN ET    → AN ON

L  ES EN → L  ON EN

EN CS AN → EN ON AN

ET AN    → ON AN *)

Fixpoint rule_w6 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | ES :: text' | ET :: text' | CS :: text' => ON :: (rule_w6 (ON :: pre) text')
  | c :: text' => c :: rule_w6 (c :: pre) text'
  end.

Definition test_rule_w6 (candidate : list bidi_class  -> list bidi_class -> list bidi_class) :=
  (eqb_list bidi_class eqb_bidi_class (candidate nil (AN :: ET :: nil)) (AN :: ON :: nil)) &&
  (eqb_list bidi_class eqb_bidi_class (candidate nil (L :: ES :: EN :: nil)) (L :: ON :: EN :: nil)) &&
  (eqb_list bidi_class eqb_bidi_class (candidate nil (EN :: CS :: AN :: nil)) (EN :: ON :: AN :: nil)) &&
  (eqb_list bidi_class eqb_bidi_class (candidate nil (ET :: AN :: nil)) (ON :: AN :: nil)).

Compute (test_rule_w6 rule_w6).

(* ********** *)

(* W7. Search backward from each instance of a European number until the first strong type (R, L, or sos) is found. If an L is found, then change the type of the European number to L. *)

Fixpoint after_l (pre : list bidi_class) : bool :=
  match pre with
  | nil => false
  | L :: _ => true
  | R :: _ => false
  | _ :: pre' => after_l pre'
  end.

Fixpoint rule_w7 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | EN :: text' =>
      let c := if after_l pre
               then L
               else EN in
      c :: rule_w7 (c :: pre) text'
    | c :: text' =>
        c :: rule_w7 (c :: pre) text'
    end.

(* L  NI EN → L  NI  L

R  NI EN → R  NI  EN *)

Definition test_rule_w7 (candidate : list bidi_class  -> list bidi_class -> list bidi_class) :=
  (eqb_list bidi_class eqb_bidi_class (candidate nil (L :: BN :: EN :: nil)) (L :: BN :: L :: nil)) &&
  (eqb_list bidi_class eqb_bidi_class (candidate nil (R :: BN :: EN :: nil)) (R :: BN :: EN :: nil)).

Compute (test_rule_w7 rule_w7).

(* ********** *)

(* N1. A sequence of NIs takes the direction of the surrounding strong text if the text on both sides has the same direction. European and Arabic numbers act as if they were R in terms of their influence on NIs. The start-of-sequence (sos) and end-of-sequence (eos) types are used at isolating run sequence boundaries. *)

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

Definition is_ni (c : bidi_class) : bool :=
  match c with
  | B | S | WS | ON | FSI | LRI | RLI | PDI => true
  | _ => false
  end.

(* Helper function to check if a character is strong *)
Definition is_strong_ni (c : bidi_class) : bool :=
  match c with
  | L | R | AL | AN | EN => true
  | _ => false
  end.

Fixpoint rule_n1 (pre : list bidi_class) (text : list bidi_class) : list bidi_class :=
  match text with
  | nil => nil
  | c :: text' =>
      if is_strong_ni c
      then match text' with
           | nil => c :: rule_n1 (c :: pre) text'
           | c' :: text'' => if is_ni c'
                             then
                               let c'' := if is_strong_ni c'
                                          then c'
                                          else c
                               in c'' :: rule_n1 (c'' :: pre) text''
                             else c :: rule_n1 (c :: pre) text'
           end
      else c :: rule_n1 (c :: pre) text'
  end.

Compute (rule_n1 nil (L :: B :: L :: nil)).

Definition test_rule_n1 (candidate : list bidi_class  -> list bidi_class -> list bidi_class) :=
    (eqb_list bidi_class eqb_bidi_class (candidate nil (L :: B :: L :: nil)) (L :: L :: L :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (R :: S :: R :: nil)) (R :: R :: R :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (R :: WS :: AN :: nil)) (R :: R :: AN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (R :: B :: EN :: nil)) (R :: R :: EN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (AN :: ON :: R :: nil)) (AN :: R :: R :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (AN :: LRI :: AN :: nil)) (AN :: R :: AN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (AN :: RLI :: EN :: nil)) (AN :: R :: EN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (EN :: FSI :: R :: nil)) (EN :: R :: R :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (EN :: PDI :: AN :: nil)) (EN :: R :: AN :: nil)) &&
    (eqb_list bidi_class eqb_bidi_class (candidate nil (EN :: B :: EN :: nil)) (EN :: R :: EN :: nil)).

Compute (test_rule_n1 rule_n1).
