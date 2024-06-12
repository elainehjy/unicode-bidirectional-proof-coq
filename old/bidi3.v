Require Import Coq.Lists.List.

Ltac destr term := let H := fresh in destruct term as [] _eqn: H.

Definition char := nat.

Inductive bidi_class : Set :=
(* Strong *)
| L  	(* Left_To_Right  	any strong left-to-right character *)
| LRE 	(* Left_To_Right_Embedding 	U+202A: the LR embedding control *)
| LRO 	(* Left_To_Right_Override 	U+202D: the LR override control *)
| R 	(* Right_To_Left 	any strong right-to-left (non-Arabic-type) character *)
| AL 	(* Arabic_Letter 	any strong right-to-left (Arabic-type) character *)
| RLE 	(* Right_To_Left_Embedding 	U+202B: the RL embedding control *)
| RLO 	(* Right_To_Left_Override 	U+202E: the RL override control *)

(* Weak *)
| PDF 	(* Pop_Directional_Format 	U+202C: terminates an embedding or override control *)
| EN 	(* European_Number 	any ASCII digit or Eastern Arabic-Indic digit *)
| ES 	(* European_Separator 	plus and minus signs *)
| ET 	(* European_Terminator 	a terminator in a numeric format context, includes currency signs *)
| AN 	(* Arabic_Number 	any Arabic-Indic digit *)
| CS 	(* Common_Separator 	commas, colons, and slashes *)
| NSM 	(* Nonspacing_Mark 	any nonspacing mark *)
| BN 	(* Boundary_Neutral 	most format characters, control codes, or noncharacters *)

(* Neutral *)
| B 	(* Paragraph_Separator 	various newline characters *)
| S 	(* Segment_Separator 	various segment-related control codes *)
| WS 	(* White_Space 	spaces *)
| ON 	(* Other_Neutral 	most other symbols and punctuation marks *)
.

(*
Rule := C'* [C -> C] C'*
C := CharCode
C' := C | C* | C or C | not C

pre [from -> to] post
pre(

*)

(* W1: Examine each nonspacing mark (NSM) in the level run, and change the type of the NSM to the type of the previous character. If the NSM is at the start of the level run, it will get the type of sor.*)
(* c [NSM -> c] *)
(* c NSM* [NSM -> c] *)
Fixpoint rule_w1_pre (pre : list bidi_class) :=
match pre with
| nil => NSM
| c :: _ => c
end.

Fixpoint rule_w1 (pre : list bidi_class) (text : list bidi_class) :=
match text with
| nil => nil
| NSM :: text' => let c := rule_w1_pre pre in c :: rule_w1 (c :: pre) text'
| c :: text' => c :: rule_w1 (c :: pre) text'
end.

(* W2: Search backward from each instance of a European number until the first strong type (R, L, AL, or sor) is found. If an AL is found, change the type of the European number to Arabic number. *)
(* AL [^R L AL]* [EN -> AN] *)

Fixpoint after_al (pre : list bidi_class) :=
match pre with
| nil => false
| AL :: _ => true
| L  :: _ => false
| R  :: _ => false
| c  :: pre' => after_al pre'
end.

Fixpoint rule_w2 (pre : list bidi_class) (text : list bidi_class) :=
match text with
| nil => nil
| EN :: text' =>
  let c := if after_al pre then AN else EN in c :: rule_w2 (c :: pre) (text')
| c :: text' => c :: rule_w2 (c :: pre) text'
end.

Fixpoint rule_w12 (pre : list bidi_class) (text : list bidi_class) :=
match text with
| nil => nil
| NSM :: text' =>
  let c := if after_al pre then AN else rule_w1_pre pre in c :: rule_w12 (c :: pre) text'
| EN :: text' =>
  let c := if after_al pre then AN else EN in c :: rule_w12 (c :: pre) (text')
| c :: text' => c :: rule_w12 (c :: pre) text'
end.

Ltac crush IH :=
match goal with
| |- (match ?b with |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ => destr b
| |- _ _ (match ?b with |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ => destr b
| |- context[if ?b then _ else _] => destr b
end; simpl; rewrite ?IH; auto.

Lemma w12_lemma : forall text pre,
  rule_w2 (AN :: pre) (rule_w1 (EN :: pre) text) =
  rule_w2 (AN :: pre) (rule_w1 (AN :: pre) text).
Proof.
induction text; intros.
(* nil *) auto.
(* cons *)
simpl.
crush IHtext.
Admitted.

Lemma foo : forall text pre, rule_w2 pre (rule_w1 pre text) = rule_w12 pre text.
Proof.
induction text; intros.
(* nil *) auto.
(* cons *)
simpl.
crush IHtext.
destr (after_al pre).
rewrite <- IHtext.
admit.
rewrite <- IHtext. auto.
crush IHtext.
crush IHtext.

destr text.
auto.
simpl.
destr b.
simpl.

after_al=true EN -> AN
rewrite <- IHtext.
TODO
crush IHtext.
destr a.
rewrite IHtext. simpl.



Ltac w15_before_en_tac IH :=
match goal with
| |- _ (match ?text with nil => _ | _ :: _ => _ end) = _ =>
  let H := fresh in destruct text as [|] _eqn: H; [auto|rewrite <- H in *]

Lemma rule_w

| AL :: text' => AL :: rule_w2 true  text'
| L  :: text' => L  :: rule_w2 false text'
| R  :: text' => R  :: rule_w2 false text'
| EN :: text' => (if is_al then AN else EN) :: rule_w2 is_al text'
| c  :: text' => c  :: rule_w2 is_al text'
end.

Fixpoint rule_w12 is_al prev (text : list bidi_class) :=
match text, prev with
| nil, _ => nil
| NSM :: text', AL => AL :: rule_w12 true prev text'
| NSM :: text', L  => L  :: rule_w12 false prev text'
| NSM :: text', R  => R  :: rule_w12 false prev text'
| NSM :: text', EN => (if is_al then AN else EN) :: rule_w12 is_al prev text'
| NSM :: text', _  => prev :: rule_w12 is_al prev text'
| AL :: text', _ => AL :: rule_w12 true AL text'
| L  :: text', _ => L  :: rule_w12 false L text'
| R  :: text', _ => R  :: rule_w12 false R text'
| EN :: text', _ => (if is_al then AN else EN) :: rule_w12 is_al EN text'
| c  :: text', _ => c :: rule_w12 is_al c text'
end.

Lemma w12_correct: forall text is_al sor,
  rule_w2 is_al (rule_w1 sor text) = rule_w12 is_al sor text.
Proof.
intro text.
induction text.
 (* nil *)
  auto.
 (* cons *)
  intros.
  case_eq a; intro; simpl; rewrite <- IHtext; trivial.
  case_eq sor; intro; simpl; try (rewrite <- IHtext); trivial.
Qed.

(* W3: Change all ALs to R. *)
(* [AL -> R] *)
Fixpoint rule_w3 (text : list bidi_class) :=
match text with
| nil => nil
| AL :: text' => R :: rule_w3 text'
| c  :: text' => c :: rule_w3 text'
end.

Fixpoint rule_w13 is_al prev (text : list bidi_class) :=
match text, prev with
| nil, _ => nil
| NSM :: text', AL => R  :: rule_w13 true prev text'
| NSM :: text', L  => L  :: rule_w13 false prev text'
| NSM :: text', R  => R  :: rule_w13 false prev text'
| NSM :: text', EN => (if is_al then AN else EN) :: rule_w13 is_al prev text'
| NSM :: text', _  => prev :: rule_w13 is_al prev text'
| AL :: text', _ => R  :: rule_w13 true AL text'
| L  :: text', _ => L  :: rule_w13 false L text'
| R  :: text', _ => R  :: rule_w13 false R text'
| EN :: text', _ => (if is_al then AN else EN) :: rule_w13 is_al EN text'
| c  :: text', _ => c :: rule_w13 is_al c text'
end.

Lemma w13_correct: forall text is_al sor,
  rule_w3 (rule_w12 is_al sor text) = rule_w13 is_al sor text.
Proof.
intro text.
induction text.
 (* nil *)
  auto.
 (* cons *)
  intros.
  case_eq a; intro; simpl; try (rewrite <- IHtext); trivial;
  case_eq is_al; intro; simpl; try (rewrite <- IHtext); trivial;
  case_eq sor; intro; simpl; try (rewrite <- IHtext); trivial.
Qed.

(* W4: A single European separator between two European numbers changes to a European number. A single common separator between two numbers of the same type changes to that type. *)
(* EN [ES -> EN] EN *)
(* EN [CS -> EN] EN *)
(* AN [CS -> AN] AN *)

Fixpoint rule_w4 prev (text : list bidi_class) :=
match text, prev with
| nil, _ => nil
| (c :: nil), _ => (c :: nil)
| ES :: (EN :: _) as text', EN => EN :: rule_w4 EN text'
| CS :: (EN :: _) as text', EN => EN :: rule_w4 EN text'
| CS :: (AN :: _) as text', AN => AN :: rule_w4 AN text'
| EN :: text', _ => EN :: rule_w4 EN text'
| AN :: text', _ => AN :: rule_w4 AN text'
| c :: text', _ => c :: rule_w4 c text'
end.

Fixpoint rule_w14 is_al prev (text : list bidi_class) :=
match text, prev with
| nil, _ => nil
| NSM :: text', AL => R  :: rule_w14 true prev text'
| NSM :: text', L  => L  :: rule_w14 false prev text'
| NSM :: text', R  => R  :: rule_w14 false prev text'
| NSM :: text', EN => (if is_al then AN else EN) :: rule_w14 is_al (if is_al then AN else EN) text'
| NSM :: text', _  => prev :: rule_w14 is_al prev text'
| AL :: text', _ => R  :: rule_w14 true AL text'
| L  :: text', _ => L  :: rule_w14 false L text'
| R  :: text', _ => R  :: rule_w14 false R text'
| EN :: text', _ => (if is_al then AN else EN) :: rule_w14 is_al (if is_al then AN else EN) text'
| ES :: (EN :: _) as text', EN => (if is_al then ES else EN) :: rule_w14 is_al (if is_al then ES else EN) text'
| CS :: (EN :: _) as text', EN => (if is_al then CS else EN) :: rule_w14 is_al (if is_al then CS else EN) text'
| CS :: (EN :: _) as text', AN => (if is_al then AN else CS):: rule_w14 is_al (if is_al then AN else CS) text'
| CS :: (AN :: _) as text', AN => AN :: rule_w14 is_al AN text'
| c  :: text', _ => c :: rule_w14 is_al c text'
end.

Lemma w13_EN_AN: forall text, rule_w13 true EN text = rule_w13 true AN text.
Proof.
induction text; [ auto | simpl; rewrite IHtext; auto ].
Qed.

Lemma w14_correct: forall text is_al sor,
  rule_w4 sor (rule_w13 is_al sor text) = rule_w14 is_al sor text.
Proof.
induction text; intros.
(* nil *) auto.
(* cons *)
  destruct text.
   (* nil *)
    destr a; auto; destr is_al; auto; destr sor; auto.
   (* cons *)
    remember (b :: text) as text'.
    destr a; simpl; repeat (rewrite <- IHtext); rewrite Heqtext'; clear Heqtext'.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
    destr is_al; destr b; auto; destr sor; auto; rewrite w13_EN_AN; auto.
Qed.

(* W5: A sequence of European terminators adjacent to European numbers changes to all European numbers. *)
(* [ET* -> EN*] EN *)
(* EN [ET* -> EN*] *)

(* [ET -> EN] ET* EN *)
(* EN ET* [ET -> EN] *)

Fixpoint rule_w5_before_en text :=
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
end.

Fixpoint rule_w15_before_en (is_al : bool) sor text :=
let head :=
  match text with
  | nil => L (* don't care *)
  | NSM :: text' => sor
  | c :: text' => c
  end in
match head, text with
| _, nil => false
| EN, _ :: _ => if is_al then false else true
| ET, _ :: text' => rule_w15_before_en is_al ET text'
| ES, _ :: EN :: _ =>
  match sor with
  | EN => if is_al then false else true
  | _ => false
  end
| CS, _ :: EN :: _ =>
  match sor with
  | EN => if is_al then false else true
  | _ => false
  end
| _, _ :: _ => false
end.

Ltac w15_before_en_tac IH :=
match goal with
| |- _ (match ?text with nil => _ | _ :: _ => _ end) = _ =>
  let H := fresh in destruct text as [|] _eqn: H; [auto|rewrite <- H in *]
| |- _ = (match ?text with nil => _ | _ :: _ => _ end) =>
  let H := fresh in destruct text as [|] _eqn: H; [auto|rewrite <- H in *]
| |- _ (match ?b with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ =>
  destr b
| |- (match (if ?b then _ else _) with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ =>
  destr b
| |- _ = (match ?b with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) =>
  destr b
| |- _ (if ?b then _ else _) = _ => destr b
| |- (if ?b then _ else _) = _ => destr b
| |- _ = (if ?b then _ else _) => destr b
end; simpl; try (rewrite IH); auto.

Lemma rule_w15_before_en_correct: forall text is_al sor,
  rule_w5_before_en (rule_w14 is_al sor text) = rule_w15_before_en is_al sor text.
Proof.
induction text; intros.
(* nil *) auto.
(* cons *)
simpl. repeat (w15_before_en_tac IHtext).
Qed.

Fixpoint rule_w15 after_en is_al prev (text : list bidi_class) :=
match text, prev with
| nil, _ => nil
| NSM :: text', AL => R  :: rule_w15 false true prev text'
| NSM :: text', L  => L  :: rule_w15 false false prev text'
| NSM :: text', R  => R  :: rule_w15 false false prev text'
| NSM :: text', EN => (if is_al then AN else EN) :: rule_w15 (if is_al then false else true) is_al (if is_al then AN else EN) text'
| NSM :: text', ET =>
  if after_en then EN :: rule_w15 after_en is_al ET text'
  else if rule_w15_before_en is_al ET text' then EN :: rule_w15 after_en is_al ET text'
  else ET :: rule_w15 after_en is_al ET text'
| NSM :: text', _  => prev :: rule_w15 false is_al prev text'
| AL :: text', _ => R  :: rule_w15 false true AL text'
| L  :: text', _ => L  :: rule_w15 false false L text'
| R  :: text', _ => R  :: rule_w15 false false R text'
| EN :: text', _ => (if is_al then AN else EN) :: rule_w15 (if is_al then false else true) is_al (if is_al then AN else EN) text'
| ES :: (EN :: _) as text', EN => (if is_al then ES else EN) :: rule_w15 (if is_al then false else true) is_al (if is_al then ES else EN) text'
| CS :: (EN :: _) as text', EN => (if is_al then CS else EN) :: rule_w15 (if is_al then false else true) is_al (if is_al then CS else EN) text'
| CS :: (EN :: _) as text', AN => (if is_al then AN else CS):: rule_w15 false is_al (if is_al then AN else CS) text'
| CS :: (AN :: _) as text', AN => AN :: rule_w15 false is_al AN text'
| ET :: text', _ =>
  if after_en then EN :: rule_w15 after_en is_al ET text'
  else if rule_w15_before_en is_al ET text' then EN :: rule_w15 after_en is_al ET text'
  else ET :: rule_w15 after_en is_al ET text'
| c  :: text', _ => c :: rule_w15 false is_al c text'
end.

Ltac w15_tac IH :=
match goal with
| |- _ _ (match ?text with nil => _ | _ :: _ => _ end) = _ =>
  let H := fresh in destruct text as [|] _eqn: H; [auto|rewrite <- H in *]
| |- _ _ (match ?b with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ =>
  destr b
| |- (match (if ?b then _ else _) with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ =>
  destr b
| |- _ _ (if ?b then _ else _) = _ => destr b
| |- (if ?b then _ else _) = _ => destr b
| |- _ = (if ?b then _ else _) => destr b
end; simpl; try (rewrite IH); try (rewrite rule_w15_before_en_correct); auto.

Lemma w15_correct: forall text after_en is_al sor,
  rule_w5 after_en (rule_w14 is_al sor text) = rule_w15 after_en is_al sor text.
Proof.
induction text; intros.
(* nil *) auto.
(* cons *)
simpl. repeat (w15_tac IHtext).
Qed.

(* W6. Otherwise, separators and terminators change to Other Neutral. *)
(* [Separators and terminators -> ON] *)
(* [ES -> ON] *)
(* [ET -> ON] *)
(* [CS -> ON] *)
Fixpoint rule_w6 text :=
match text with
| nil => nil
| ES :: text' | ET :: text' | CS :: text' => ON :: rule_w6 text'
| c :: text' => c :: rule_w6 text'
end.

Fixpoint rule_w16 after_en is_al prev (text : list bidi_class) :=
match text, prev with
| nil, _ => nil
| NSM :: text', AL => R  :: rule_w16 false true prev text'
| NSM :: text', L  => L  :: rule_w16 false false prev text'
| NSM :: text', R  => R  :: rule_w16 false false prev text'
| NSM :: text', EN => (if is_al then AN else EN) :: rule_w16 (if is_al then false else true) is_al (if is_al then AN else EN) text'
| NSM :: text', ET =>
  if after_en then EN :: rule_w16 after_en is_al ET text'
  else if rule_w15_before_en is_al ET text' then EN :: rule_w16 after_en is_al ET text'
  else ON :: rule_w16 after_en is_al ET text'
| NSM :: text', ES => ON :: rule_w16 false is_al prev text'
| NSM :: text', CS => ON :: rule_w16 false is_al prev text'
| NSM :: text', _  => prev :: rule_w16 false is_al prev text'
| AL :: text', _ => R  :: rule_w16 false true AL text'
| L  :: text', _ => L  :: rule_w16 false false L text'
| R  :: text', _ => R  :: rule_w16 false false R text'
| EN :: text', _ => (if is_al then AN else EN) :: rule_w16 (if is_al then false else true) is_al (if is_al then AN else EN) text'
| ES :: (EN :: _) as text', EN => (if is_al then ON else EN) :: rule_w16 (if is_al then false else true) is_al (if is_al then ES else EN) text'
| CS :: (EN :: _) as text', EN => (if is_al then ON else EN) :: rule_w16 (if is_al then false else true) is_al (if is_al then CS else EN) text'
| CS :: (EN :: _) as text', AN => (if is_al then AN else ON):: rule_w16 false is_al (if is_al then AN else CS) text'
| CS :: (AN :: _) as text', AN => AN :: rule_w16 false is_al AN text'
| ET :: text', _ =>
  if after_en then EN :: rule_w16 after_en is_al ET text'
  else if rule_w15_before_en is_al ET text' then EN :: rule_w16 after_en is_al ET text'
  else ON :: rule_w16 after_en is_al ET text'
| ES :: text', _ => ON :: rule_w16 false is_al ES text'
| CS :: text', _ => ON :: rule_w16 false is_al CS text'
| c  :: text', _ => c :: rule_w16 false is_al c text'
end.

Ltac w16_tac IH :=
match goal with
| |- _ (match ?text with nil => _ | _ :: _ => _ end) = _ =>
  let H := fresh in destruct text as [|] _eqn: H; [auto|rewrite <- H in *; clear H]
| |- _ (match ?b with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ =>
  destr b
| |- (match (if ?b then _ else _) with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ =>
  destr b
| |- _ (if ?b then _ else _) = _ => destruct b
end; simpl; try (rewrite IH); auto.

Lemma w16_correct: forall text after_en is_al sor,
  rule_w6 (rule_w15 after_en is_al sor text) = rule_w16 after_en is_al sor text.
Proof.
induction text; intros.
(* nil *) auto.
(* cons *)
simpl. repeat (w16_tac IHtext).
Qed.

(* W7. Search backward from each instance of a European number until the first strong type (R, L, or sor) is found. If an L is found, then change the type of the European number to L. *)
(* L [^R L]* [EN -> L] *)

Fixpoint rule_w7 (after_l : bool) text :=
match text with
| nil => nil
| (EN :: text') => (if after_l then L else EN) :: rule_w7 after_l text'
| (L :: text') => L :: rule_w7 true text'
| (R :: text') => R :: rule_w7 false text'
| (c :: text') => c :: rule_w7 after_l text'
end.

Fixpoint rule_w17 after_l after_en is_al prev (text : list bidi_class) :=
match text, prev with
| nil, _ => nil
| NSM :: text', AL => R  :: rule_w17 false false true prev text'
| NSM :: text', L  => L  :: rule_w17 true false false prev text'
| NSM :: text', R  => R  :: rule_w17 false false false prev text'
| NSM :: text', EN => (if is_al then AN else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) text'
| NSM :: text', ET =>
  if after_en then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
  else if rule_w15_before_en is_al ET text' then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
  else ON :: rule_w17 after_l after_en is_al ET text'
| NSM :: text', ES => ON :: rule_w17 after_l false is_al prev text'
| NSM :: text', CS => ON :: rule_w17 after_l false is_al prev text'
| NSM :: text', _  => prev :: rule_w17 after_l false is_al prev text'
| AL :: text', _ => R  :: rule_w17 false false true AL text'
| L  :: text', _ => L  :: rule_w17 true false false L text'
| R  :: text', _ => R  :: rule_w17 false false false R text'
| EN :: text', _ => (if is_al then AN else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then AN else EN) text'
| ES :: (EN :: _) as text', EN => (if is_al then ON else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then ES else EN) text'
| CS :: (EN :: _) as text', EN => (if is_al then ON else (if after_l then L else EN)) :: rule_w17 after_l (if is_al then false else true) is_al (if is_al then CS else EN) text'
| CS :: (EN :: _) as text', AN => (if is_al then AN else ON):: rule_w17 after_l false is_al (if is_al then AN else CS) text'
| CS :: (AN :: _) as text', AN => AN :: rule_w17 after_l false is_al AN text'
| ET :: text', _ =>
  if after_en then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
  else if rule_w15_before_en is_al ET text' then (if after_l then L else EN) :: rule_w17 after_l after_en is_al ET text'
  else ON :: rule_w17 after_l after_en is_al ET text'
| ES :: text', _ => ON :: rule_w17 after_l false is_al ES text'
| CS :: text', _ => ON :: rule_w17 after_l false is_al CS text'
| c  :: text', _ => c :: rule_w17 after_l false is_al c text'
end.

Ltac w17_tac IH :=
match goal with
| |- _ _ (match ?text with nil => _ | _ :: _ => _ end) = _ =>
  let H := fresh in destruct text as [|] _eqn: H; [auto|rewrite <- H in *; clear H]; try (simpl; rewrite IH; auto)
| |- _ _ (match ?b with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ =>
  destr b
| |- (match (if ?b then _ else _) with
  |L=>_|LRE=>_|LRO=>_|R=>_|AL=>_|RLE=>_|RLO=>_|PDF=>_|EN=>_
  |ES=>_|ET=>_|AN=>_|CS=>_|NSM=>_|BN=>_|B=>_|S=>_|WS=>_|ON=>_ end) = _ =>
  destr b
| |- _ _ (if ?b then _ else _) = _ => destr b
end; simpl; try (rewrite IH); auto.

Lemma w17_correct: forall text after_l after_en is_al sor,
  rule_w7 after_l (rule_w16 after_en is_al sor text) = rule_w17 after_l after_en is_al sor text.
Proof.
induction text; intros.
(* nil *) auto.
(* cons *)
simpl. repeat (w17_tac IHtext).
Qed.

(* N1. A sequence of neutrals takes the direction of the surrounding strong text if the text on both sides has the same direction. European and Arabic numbers act as if they were R in terms of their influence on neutrals. Start-of-level-run (sor) and end-of-level-run (eor) are used at level run boundaries. *)

(* N2. Any remaining neutrals take the embedding direction. *)
