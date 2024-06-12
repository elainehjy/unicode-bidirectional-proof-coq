Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Datatypes.

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
Definition is_strong (c : bidi_class) : bool := .
Definition is_weak (c : bidi_class) : bool := .
Definition is_neutral (c : bidi_class) : bool := .
Definition is_al_or_r (c : bidi_class) : bool := .
Definition is_l_al_or_r (c : bidi_class) : bool := .
*)

(*
prefix

Fixpoint embedding level 

embedding level := LRE (non-LRE-RLE-LRO-RLO-PDF | embedding (level + 1))* PDF
embedding 61 := non-PDF*

BN
B

Reparse

Segment into regions by AL, L and R.

NSM

ENum = ET* EN+ ((ET* | ES | CS) EN+)* ET*
ANum = AN+ (CS AN+)*
AENum = ((AN|EN)+ (CS (AN|EN)+)*

L ([ENum -> L]|[ANum -> AN]|[else -> ON])*
R ([ENum ->EN]|[ANum -> AN]|[else -> ON])*
AL ([AENum->AN]|[else -> ON])*

L [ON* -> L] L
L [ON* -> e] (R|AL|EN|AN)
(R|AL|EN|AN) [ON* -> R] (R|AL|EN|AN)
(R|AL|EN|AN) [ON* -> e] L

I1 and I2
Type  	Embedding Level
	Even 	Odd
L 	EL 	EL+1
R 	EL+1 	EL
AN 	EL+2 	EL+1
EN 	EL+2 	EL+1

reparse

Fixpoint bidi_alg (

*)

Definition char_bidi_class (c : char) : bidi_class :=
  L.

(* Q: paragraph separator is not defined.  Also in X8. *)
(* rule_p1: split into paragraphs keeping separator with previous paragraph *)
(* rule_p2: In each paragraph, find the first character of type L, AL, or R. *)
Fixpoint rule_p2 (text : list char) : option char :=
  match text with
    | nil => None
    | (x :: xs) =>
      match char_bidi_class x with
        | L => Some x
        | AL => Some x
        | R => Some x
        | _ => rule_p2 xs
      end
  end.

(* rule P3: If a character is found in P2 and it is of type AL or R,
then set the paragraph embedding level to one; otherwise, set it to
zero. *)
Definition rule_p3 (c : option char) : nat :=
match c with
| Some c =>
  match char_bidi_class c with
  | AL => 1
  | R => 1
  | _ => 0 end
| _ => 0
end.

(* Inductive embed_level (0 <= <= 62). *)
Definition embed_level := nat.
Inductive directional_override :=
| Neutral
| LTR
| RTL
.

Definition x1_state := (embed_level * directional_override)%type.
Definition char_state := (char * bidi_class * embed_level)%type.
Fixpoint foo (x:nat) := match x with O => O | Datatypes.S x' => bar x' end
with
  bar y := match y with O => O | Datatypes.S y' => foo y' end
.
Definition is_even (n:nat) : bool := true.

Definition next_odd (n:nat) : option nat :=
  if is_even n
    then Some (n+1)
    else Some (n+2).
(*TODO: limit to 61*)

Definition next_even (n:nat) : option nat :=
  if is_even n
    then Some (n+2)
    else Some (n+1).

(*
Fixpoint rule_x1_aux
  (state : x1_state)
  (states : list x1_state)
  (text : list char) {struct text} :
  (list char_state) :=
  match text with
    | nil => nil
    | (c :: cs) =>
      match char_bidi_class c with
        (* rule x2 and x9 *)
        | RLE => rule_x1_explicit next_odd Neutral state states cs
        (* rule x3 and x9 *)
        | LRE => rule_x1_explicit next_even Neutral state states cs
        (* rule x4 and x9 *)
        | RLO => rule_x1_explicit next_odd RTL state states cs
        (* rule x5 and x9 *)
        | LRO => rule_x1_explicit next_even LTR state states cs
        (* rule x7 *)
        (* Q: What to do if no matching override? *)
        (* Q: If no matching because to many PDF? *)
        (* Q: If no matching because to many embeddings? *)
        (*| PDF => rule_x (pop) text*)
        (* rule x8 *)
        (* Q: Clarify: Does parsep mean B?*)
        (* Q: Clarify with example. *)
        (* Q: Does B then need to be listed in X6? *)
        (*| B => not inn embedding*)
        (* rule x9 *) (* remove but not really remove b/c of zwj and zwnj *)
        | BN => rule_x1_aux state states cs
        (* rule x6 *)
        | class => match state with
                     | (level, Neutral) => (c, class, level)
                     | (level, LTR) => (c, L, level)
                     | (level, RTL) => (c, R, level)
                   end :: rule_x1_aux state states cs
      end
  end
  with
    rule_x1_explicit
    next_embedding override state states text : list char_state :=
    match next_embedding (fst state) with
      | Some new_level =>
        rule_x1_aux (new_level, override) (state :: states) text
      | None => rule_x1_aux state states text
    end.
*)

(*
Definition rule_x1 (text : list char) : ?? :=
  rule_x2 (rule_p3 (rule_p2 text)) Neutral.
*)

(* rule x10 *)
(* Q: The "base embedding level" is not defined.
      Is "paragraph embedding level" intended? *)
(* Q: What about adjacent equal embedding levels?
      E.g. RLE x PDF RLE y PDF? *)
Definition pair_to_cons {t} (x:t*list t) := match x with (a,b) => a :: b end.
Fixpoint rule_x10_aux
  (c : char_state) (cs : list char_state)
  : (list char_state * list (list char_state)) :=
  match cs with
    | nil => (c :: nil, nil)
    | c' :: cs' =>
      match (nat_compare (snd c) (snd c'), rule_x10_aux c' cs') with
        | (Eq, (y, ys)) => (c :: y, ys)
        | (_,  (y, ys)) => (c :: nil, y :: ys)
      end
  end.      
Definition rule_x10 (cs : list char_state) : list (list char_state) :=
  match cs with
    | nil => nil
    | c :: cs => pair_to_cons (rule_x10_aux c cs)
  end.

(*Lemma post_x.*) (* no rle, lre, rlo, lro, pdf or bn *)

(*
Fixpoint accum {a b s : Type} (f : s -> a -> (s * b)) (state : s) (l : list a) :=
  match l with
    | nil => nil
    | x :: xs => match f state x with (state', x') => x' :: accum f state' xs end
  end.
*)

(*
Fixpoint accum_lookahead {a b s : Type}
  (f : s -> a -> a -> (s * b)) (state : s) (l : list a) (last : a) :=
  match l with
    | nil => nil
    | x :: xs =>
      match f state x (match xs with y :: _ => y | _ => last end) with
        (state', x') => x' :: accum_lookahead f state' xs last
      end
  end.
*)

Inductive bidi_class' :=
| UseNext
| LitClass (c : bidi_class).

Fixpoint accum {s : Type}
  (f : s -> bidi_class' -> list bidi_class' -> bidi_class' -> (s * bidi_class'))
  (state : s) (text : list bidi_class') (eor : bidi_class') :
  (list bidi_class') :=
  match text with
    | nil => nil
    | class :: text' =>
      let (state', class') := f state class text' eor in
        class' :: accum f state' text' eor
  end.

Fixpoint rep {s : Type} (x : s) (n : nat) : list s :=
  match n with
    | 0 => nil
    | Datatypes.S n => x :: rep x n
  end.

Fixpoint unbidi_class' n (text : list bidi_class') eor :=
  match text with
    | nil => rep eor n
    | (LitClass x) :: xs => rep x (n+1) ++ unbidi_class' 0 xs eor
    | UseNext :: xs => unbidi_class' (n+1) xs eor
  end.

Definition inj_bidi_class' (text : list bidi_class) := map LitClass text.

Fixpoint accum2 {s : Type}
  (f : s -> bidi_class -> bidi_class -> (s * bidi_class))
  (sor : s) (text : list bidi_class) (eor : bidi_class) :
  (list bidi_class) :=
  match text with
    | nil => nil
    | class :: text' =>
      match f sor class (match text' with
                             | nil => eor
                             | class :: _ => class
                           end) with
      (state', class') => class' :: accum2 f state' text' eor
      end
  end.

Fixpoint accum3_aux {s : Type}
  (f : s -> bidi_class -> bidi_class -> (s * bidi_class))
  (sor : s) (c : bidi_class) (text : list bidi_class) (eor : bidi_class) :
  (list bidi_class) :=
  match text with
    | nil => let (sor', c') := f sor c eor in c' :: nil
    | c' :: text' =>
      let (sor', c'') := f sor c c' in c'' :: accum3_aux f sor' c' text' eor
  end.

Definition accum3 {s : Type}
  (f : s -> bidi_class -> bidi_class -> (s * bidi_class))
  (sor : s) (text : list bidi_class) (eor : bidi_class) :
  (list bidi_class) :=
  match text with
    | nil => nil
    | c :: text => accum3_aux f sor c text eor
  end.


Fixpoint accum4 {s : Type}
  (f : s -> bidi_class -> bidi_class -> (s * bidi_class))
  (sor : s) (eor : bidi_class) (text : list bidi_class) :
  (list bidi_class) :=
  match text with
    | nil => nil
    | c :: text =>
      let s := f sor c (match text with
                                 | nil => eor
                                 | c' :: _ => c'
                               end) in
      (snd s) :: accum4 f (fst s) eor text
  end.

(*
    | c :: nil => let (sor', c') := f sor c eor in c' :: nil
    | c :: (c' :: _) as text =>
      let (sor', c) := f sor c c' in c :: accum4 f sor' eor text
  end.
*)

(* Q: "type of the previous character" should be
      "type of the previous non-NSM character" because
      the rule doesn't say whether the rule is applied left to right
      or right to left. *)
(* x [NSM -> x:type] *)
Definition rule_w1_fun (sor c eor : bidi_class) :=
    match c with
      | NSM => (sor, sor)
      | _ => (c, c)
    end.
Fixpoint new_rule_w1_fun (prev : bidi_class) (text : list bidi_class) :=
match text with
  | nil => nil
  | NSM :: text' => prev :: new_rule_w1_fun prev text'
  | c :: text' => c :: new_rule_w1_fun c text'
end.
Definition new_rule_w1 sor := new_rule_w1_fun sor.

Definition rule_w1 := accum4 rule_w1_fun.

Fixpoint rule_w1' sor (eor : bidi_class) text :=
  match text with
    | nil => nil
    | NSM :: text => sor :: rule_w1' sor eor text
    | c :: text => c :: rule_w1' c eor text
  end.

(* Q: Use type name (i.e. EN) in addition to descriptive name
   otherwise "European Number" might seem to include
   "European Number Separator".  Same for other rules. *)
(* AL Non-strong* [EN -> AN] *)
Definition rule_w2_fun (is_al : bool) (c _ : bidi_class) :=
    match c with
      | AL => (true, AL)
      | L  => (false, L)
      | R  => (false, R)
      | EN => (is_al, if is_al then AN else EN)
      | _  => (is_al, c)
    end.
Definition rule_w2 (sor : bidi_class) :=
  accum4 rule_w2_fun (match sor with AL => true | _ => false end).

Definition rule_w12_fun class'is_al c (_ : bidi_class) :=
  match c, class'is_al with
    | AL, _      => ((AL,true ), AL)
    | L , _      => ((L ,false), L)
    | R , _      => ((R ,false), R)
    | EN, (_,true ) => ((EN,true ), AN)
    | EN, (_,false) => ((EN,false), EN)

    | NSM, (AL, _ ) => ((AL,true ), AL)
    | NSM, (L , _ ) => ((L ,false), L)
    | NSM, (R , _ ) => ((R ,false), R)
    | NSM, (EN, true ) => ((EN,true ), AN)
    | NSM, (EN, false) => ((EN,false), EN)
    | NSM, (c,al) => ((c,al), c)

    | _ , (_,al)  => ((c,al), c)
  end.

Definition rule_w12 sor := accum4 rule_w12_fun (sor, match sor with AL => true | _ => false end).

Lemma w12_correct : forall text sor1 sor2 eor,
   accum4 rule_w12_fun (sor1, sor2) eor text =
   accum4 rule_w2_fun sor2 eor (accum4 rule_w1_fun sor1 eor text).
Proof.
  induction text.
   intros sor1 sor2 eor. trivial.
   intros sor1 sor2 eor. destruct text.
    destruct a as [] _eqn; destruct sor1 as [] _eqn; destruct sor2 as [] _eqn;
      trivial.
    remember (b :: text).
    destruct a as [] _eqn; destruct sor1 as [] _eqn; destruct sor2 as [] _eqn;
      simpl; rewrite IHtext; trivial.
Qed.

(* Q: "European separator" is not defined. Use "European Number Separator". *)
(* [AL -> R] *)
Definition rule_w3_fun (_ : unit) (c _ : bidi_class) :=
  (tt, match c with
         | AL => R
         | _ => c
       end).

Definition rule_w3 (_ : bidi_class) := accum4 rule_w3_fun tt.

Definition rule_w13_fun class'is_al c (_ : bidi_class) :=
    match c, class'is_al with
      | AL, _      => ((AL,true ), R)
      | L , _      => ((L ,false), L)
      | R , _      => ((R ,false), R)
      | EN, (_,true ) => ((EN,true ), AN)
      | EN, (_,false) => ((EN,false), EN)

      | NSM, (AL, _ ) => ((AL,true ), R)
      | NSM, (L , _ ) => ((L ,false), L)
      | NSM, (R , _ ) => ((R ,false), R)
      | NSM, (EN, true ) => ((EN,true ), AN)
      | NSM, (EN, false) => ((EN,false), EN)
      | NSM, (c,al) => ((c,al), c)

      | _ , (_,al)  => ((c,al), c)
    end.

Definition rule_w13 sor := accum4 rule_w13_fun (sor,match sor with AL => true | _ => false end).

Lemma w13_correct : forall text sor1 sor2 sor3 eor,
   accum4 rule_w13_fun (sor1, sor2) eor text =
   accum4 rule_w3_fun sor3 eor (accum4 rule_w12_fun (sor1,sor2) eor text).
Proof.
  induction text.
   intros sor1 sor2 sor3 eor; trivial.
   intros sor1 sor2 sor3 eor. destruct text.
     destruct a as [] _eqn; destruct sor2 as [] _eqn; destruct sor1 as [] _eqn;
       trivial.
     remember (b :: text).
     destruct a as [] _eqn; destruct sor2 as [] _eqn; destruct sor1 as [] _eqn;
       simpl; rewrite <- IHtext; trivial.
Qed.

(* Q: Is this rule applied recursively? Order doesn't matter. *)
(* Q: Define "number". *)
(* Q: This is two rules in one. *)
(* EN [ES -> EN] EN *)
(* EN [CS -> EN] EN *)
(* AN [CS -> AN] AN *)
Inductive AfterNum := AfterEN | AfterAN | AfterOther.
Definition toAfterNum c :=
  match c with AN => AfterAN | EN => AfterEN | _ => AfterOther end.
Definition rule_w4_fun sor c eor :=
  (toAfterNum c,
    match sor, c, eor with
      | AfterEN, ES, EN => EN
      | AfterEN, CS, EN => EN
      | AfterAN, CS, AN => AN
      | _, _, _ => c
    end).

Definition rule_w4 sor := accum4 rule_w4_fun (toAfterNum sor).

(* sor = w1_last * w2_isal * w4_after *)
Definition rule_w14_fun sor c eor :=
    match c, sor, eor with
      | AL, _        ,_ => ((c,true ,AfterOther), R)
      | L , _        ,_ => ((c,false,AfterOther), L)
      | R , _        ,_ => ((c,false,AfterOther), R)
      | EN, (_,true ,_ ),_ => ((c,true ,AfterAN), AN)
      | EN, (_,false,_ ),_ => ((c,false,AfterEN), EN)

(*
      | ES, (_,AL,EN),EN => ((c,AL,ES),ES)
      | ES, (_,al,EN),EN => ((c,al,EN),EN)
      | CS, (_,AL,EN),EN => ((c,AL,CS),CS)
      | CS, (_,al,EN),AN => ((c,al,CS),CS)
      | CS, (_,AL,AN),EN => ((c,AL,AN),AN)
      | CS, (_,al,AN),AN => ((c,al,AN),AN)
*)

(*      | ES, (_,true ,AfterEN),EN => ((c,true ,AfterOther),ES)*)
      | ES, (_,al,AfterEN),EN => ((c,al,AfterEN),EN)
      | CS, (_,al,AfterEN),EN => ((c,al,AfterEN),EN)
      | CS, (_,al,AfterAN),AN => ((c,al,AfterAN),AN)

      | NSM, (AL,_ ,_),_ => ((AL,true ,AfterOther), R)
      | NSM, (L ,_ ,_),_ => ((L ,false,AfterOther), L)
      | NSM, (R ,_ ,_),_ => ((R ,false,AfterOther), R)
      | NSM, (EN,true ,_),_ => ((EN,true ,AfterAN), AN)
      | NSM, (EN,false,_),_ => ((EN,false,AfterEN), EN)

(*      | NSM, (ES,AL,EN),EN => ((c,AL,ES),ES) *)
      | NSM, (ES,al,AfterEN),EN => ((c,al,AfterEN),EN)
(*      | NSM, (CS,AL,EN),EN => ((c,AL,CS),CS) *)
      | NSM, (CS,al,AfterEN),EN => ((c,al,AfterEN),EN)
(*      | NSM, (CS,AL,AN),EN => ((c,AL,AN),AN) *)
      | NSM, (CS,al,AfterAN),AN => ((c,al,AfterAN),AN)

      | NSM, (c,al,_),_ => ((c,al,toAfterNum c), c)
      | _  , (_,al,_),_ => ((c,al,toAfterNum c), c)
    end.

Definition rule_w14 sor := accum4 rule_w14_fun (sor,match sor with AL => true | _ => false end,toAfterNum sor).

(*
Lemma accum4_comp :
  forall {S1 S2} f g h,
    (forall c s1 s2 eor,
      let text := c :: nil in
        accum4 (s := S1 * S2) f (s1,s2) eor text =
        accum4 (s := S2) g s2 eor (accum4 (s := S1) h s1 eor text)) ->
    (forall c1 c2 s1 s2 eor,
      let text := c1 :: c2 :: nil in
        accum4 f (s1,s2) eor text = accum4 g s2 eor (accum4 h s1 eor text)) ->
    (forall text s1 s2 eor,
      accum4 f (s1,s2) eor text = accum4 g s2 eor (accum4 h s1 eor text)).
Proof.
  intros S1 S2 f g h. intros text1 text2.
  induction text.
   (* nil *) trivial.
   intros. destruct text as [nil | c text].
    (* nil *) compute. admit.
    (* cons *)
     remember (c :: text) as ctext. simpl. rewrite Heqctext.
     unfold accum4 at 2. remember (c :: text) as ctext'. simpl.
     rewrite Heqctext'.
     unfold accum4 at 3. remember (c :: text) as ctext''. simpl.
     remember (fst (h s1 a c)) as s1'.
     remember ((fst
           (g s2 (snd (h s1 a c))
              (snd (h s1' c match text with
                            | nil => eor
                            | c' :: _ => c'
                            end))))) as s2'.
*)

(*
snd (f (s1, s2) a c) =
snd (g s2 (snd (h s1 a c)) c);

snd (f (s1, s2) a c) =
snd (g s2 (snd (h s1 a c)) (snd (h (fst (h s1 a c)) c c')))

(fst (fst (f (s1, s2) a c))) = (fst (h s1 a c))
(snd (fst (f (s1, s2) a c))) =
     (fst (g s2 (snd (h s1 a c)) (snd (h (fst (h s1 a c)) c c')))))

---

snd (f (s1, s2) a c) =
snd (g s2 (snd (h s1 a c)) c);

snd (f (s1, s2) a c) =
snd (g s2 (snd (h s1 a c)) (snd (h (fst (h s1 a c)) c c')))

let (Xfst,Xsnd) := (h s1 a c) in
let (Zfst,Zsnd) := (h Xfst c c') in
let (Yfst,Ysnd) := (g s2 Xsnd Zsnd) in
  (f (s1, s2) a c) = (Xfst, Yfst, Ysnd)

let (Xfst,Xsnd) := (h s1 a c) in
let (Zfst,Zsnd) := (h Xfst c c') in
let (Yfst,Ysnd) := 
(f (s1, s2) a c) =
(Xfst,
  fst (g s2 Xsnd Zsnd),
  snd (g s2 Xsnd c))

:: accum4 f (fst (f (s1, s2) a c)) eor ctext'' =
:: accum4 g
(fst
  (g s2 (snd (h s1 a c))
    (snd
      (h (fst (h s1 a c)) c
        match text with
          | nil => eor
          | c' :: _ => c'
        end))))
eor (accum4 h (fst (h s1 a c)) eor ctext'')


     
 simpl.
     remember ((fix accum4 (s0 : Type)
                          (f0 : s0 ->
                                bidi_class -> bidi_class -> s0 * bidi_class)
                          (sor : s0) (eor0 : bidi_class)
                          (text0 : list bidi_class) {struct text0} :
                 list bidi_class :=
                 match text0 with
                 | nil => nil
                 | c0 :: text3 =>
                     let s3 :=
                       f0 sor c0
                         match text3 with
                         | nil => eor0
                         | c' :: _ => c'
                         end in
                     snd s3 :: accum4 s0 f0 (fst s3) eor0 text3
                 end) S1 h) as X.

(fix accum4 (s0 : Type)
                          (f0 : s0 ->
                                bidi_class -> bidi_class -> s0 * bidi_class)
                          (sor : s0) (eor0 : bidi_class)
                          (text0 : list bidi_class) {struct text0} :
                 list bidi_class :=
                 match text0 with
                 | nil => nil
                 | c0 :: text3 =>
                     let s3 :=
                       f0 sor c0
                         match text3 with
                         | nil => eor0
                         | c' :: _ => c'
                         end in
                     snd s3 :: accum4 s0 f0 (fst s3) eor0 text3
                 end) as X. rewrite <- HeqX.
 fold (accum4 (s := S2)).
 simpl.
     compute.


(f (s1, s2) a c)
(g s2 (snd (h s1 a c))
  match accum4 h (fst (h s1 a c)) eor (c :: text) with
    | nil => eor
    | c' :: _ => c'
  end)

accum4 f (fst
  (f (s1, s2) a c)) eor (c :: text) =
accum4 g (fst
  (g s2 (snd (h s1 a c))
    match accum4 h (fst (h s1 a c)) eor (c :: text) with
      | c' :: _ => c'
    end)) eor (accum4 h (fst (h s1 a c)) eor (c :: text))


(f (s1, s2) a c) =
(g s2 (snd (h s1 a c))
  match
    accum4 h (fst (h s1 a c)) eor (c :: text)
    with
    | c' :: _ => c'
  end)

:: accum4 f
(fst (f (s1, s2) a match ctext with
                     | c' :: _ => c'
                   end)) eor ctext =
:: accum4 g
(fst
  (g s2
    (snd (h s1 a match ctext with
                   | nil => eor
                   | c' :: _ => c'
                 end))
    match
      accum4 h
      (fst
        (h s1 a
          match ctext with
            | nil => eor
            | c' :: _ => c'
          end)) eor ctext
              with
              | nil => eor
              | c' :: _ => c'
              end)) eor
        (accum4 h
           (fst (h s1 a match ctext with
                        | nil => eor
                        | c' :: _ => c'
                        end)) eor ctext)


simpl.
destruct text
    compute.

  (forall, f (s1,s2) c eor =
    let (s1,c) = h s1 c eor in
      let () = h s1 c2 
      let (s2,c) = g s2 c eor in
        (s1, s2, c)
  ->
  accum4 f (s1,s2) eor text =
  accum4 g s1 eor (accum4 h s2 eor text)
*)

(*
Lemma w14_correct : forall text sor1 sor2 sor4 eor,
  accum4 rule_w14_fun (sor1, sor2, sor4) eor text =
  accum4 rule_w4_fun sor4 eor (accum4 rule_w13_fun (sor1,sor2) eor text).
Proof.
  induction text.
   intros sor1 sor2 sor4 eor; trivial.
   intros sor1 sor2 sor4 eor; destruct text.
     destruct a as [] _eqn; destruct sor1 as [] _eqn;
       destruct sor2 as [] _eqn; destruct sor4 as [] _eqn; trivial;
         destruct eor as [] _eqn; trivial.
     Eval compute in accum4 rule_w14_fun (L,true,AfterEN) EN (ES :: nil).
     Eval compute in accum4 rule_w13_fun (L, true) EN (ES :: nil).
     Eval compute in accum4 rule_w4_fun AfterEN EN (ES :: nil).
     remember (b :: text).
     destruct a as [] _eqn;
     destruct sor4 as [] _eqn; try (simpl; rewrite <- IHtext; trivial; fail);
     try (destruct sor2 as [] _eqn; simpl; rewrite <- IHtext; trivial; fail).
     simpl. rewrite <- IHtext. rewrite Heql. destruct b as [] _eqn; try (trivial; fail). simpl.
Qed.
*)

Inductive w5_state :=
| AfterET nat
| AfterEN
| AfterOther'
.

Fixpoint rule_w5_fun state  :=
  match state, text with
    | AfterOther', nil => []
    | AfterOther', ET :: text => rec (AfterET 1) text
    | AfterOther', EN :: text => EN :: rec AfterEN text
    | AfterOther', c  :: text =>
    | AfterEN, nil => []
    | AfterEN, ET :: text => EN :: rec AfterEN text
    | AfterEN, EN :: text => EN :: rec AfterEN text
    | AfterEN, c  :: text => c  :: rec AfterEN text
    | AfterET n, nil => times ET n
    | AfterET n, ET :: text => rec (AfterET (n+1)) text
    | AfterET n, EN :: text => times EN (n+1) ++ rec AfterEN text
    | AfterET n, c  :: text => times ET n ++ rec AfterEN text
  match c, eor with
    | ET, ET => rec
    | ET, EN => mult EN EN ++ rec
    | _, _ => mult ET ++ rec
  end
  

Lemma w15_correct : forall,
  accum4 rule_w15_fun (sor1, sor2, sor4, sor5) eor text =
  accum4 rule_w5_fun sor5 eor (accum4 rule_w14_fun (sor1, sor2, sor4) eor text).

Eval compute in accum4 rule_w14_fun (NSM,true,AfterEN) NSM (ES :: EN :: L :: nil). (* EN :: AN :: L :: nil *)
Eval compute in accum4 rule_w13_fun (NSM,true) NSM (ES :: EN :: L :: nil). (* ES :: AN :: L :: nil *)
Eval compute in accum4 rule_w4_fun AfterEN NSM (ES :: EN :: L :: nil). (* ES :: AN :: L :: nil *)

Eval compute in accum4 rule_w14_fun (L,true,AfterEN) EN (ES :: nil).
Eval compute in accum4 rule_w13_fun (L, true) EN (ES :: nil).
Eval compute in accum4 rule_w4_fun AfterEN EN (ES :: nil).

(* The problem is that the true eor doesn't change from EN to AN
but the local sor of EN does change. *)

Eval compute in accum4 rule_w13_fun (ES, sor2) eor (EN :: nil).

simpl. destruct sor2 as [] _eqn. simpl.

ES :: EN :: text
AfterEN
is_al=true


     rewrite Heql; try (destruct b as [] _eqn; simpl; rewrite <- IHtext; trivial; fail). rewrite
 simpl. destruct b. simpl.
     simpl.

     simpl. destruct sor2. simpl. trivial.
       destruct sor4
     try (destruct eor as [] _eqn; simpl; rewrite <- IHtext; trivial; fail).
     simpl. destruct sor4 as [] _eqn. trivial.
     
     destruct a as [] _eqn;
     destruct sor4 as [] _eqn; try (simpl; rewrite <- IHtext; trivial; fail);
     try (destruct sor1 as [] _eqn; simpl; rewrite <- IHtext; trivial; fail).
     
     simpl.
     trivial.
     destruct sor1 as [] _eqn;
     destruct sor2 as [] _eqn;
     destruct sor4 as [] _eqn;
     destruct eor as [] _eqn;
     simpl;
     try (rewrite <- IHtext); trivial.
     rewrite Heql.

destruct a.
destruct sor2.
destruct sor1.
destruct sor4.
destruct eor.

 compute.
     remember a; destruct b; remember sor4; destruct b;
       remember sor2; destruct b; trivial; remember eor; destruct b; trivial;
       remember sor1; destruct b; trivial.
       Admitted.

(sor1, L, EN) EN (CS :: nil)

Definition h : rule_w14_fun (R,AL,EN) ES EN = (R,R,R,R). simpl. (ES,AL,ES,ES)
Definition f : rule_w13_fun (R,AL) ES EN = (R,R,R). simpl. (ES,AL,ES).
Definition g : rule_w4_fun EN ES EN = (R,R). unfold rule_w4_fun. (ES,EN).
(sor1, AL, EN) EN (ES :: nil)
     simpl.
     simpl.
     destruct a; destruct sor4; trivial; destruct sor2; trivial; destruct eor; trivial. simpl.
simpl.
     destruct eor; destruct a; trivial; destruct sor4; trivial.
     simpl. destruct eor; simpl. unfold rule_w14_fun. destruct a;
     destruct sor4; trivial.
simpl; trivial.
     remember a; destruct b; simpl; destruct sor4; simpl; trivial; destruct eor; simpl; trivial.
trivial.
     remember sor4; destruct b; simpl; trivial;
     remember sor2; destruct b; simpl; trivial;
     remember eor; destruct b; simpl; trivial.
     destruct a; simpl; trivial; destruct sor4; simpl; trivial.
     remember a. destruct b; simpl; trivial. remember sor4. destruct b; trivial.
     destruct a; trivial; destruct sor2; trivial. destruct sor1; trivial.
     remember (b :: text).
     destruct a; simpl; try (rewrite <- IHtext; trivial);
     destruct sor2; simpl; try (rewrite <- IHtext; trivial);
     destruct sor1; simpl; try (rewrite <- IHtext; trivial).
Qed.


(*
W1: x [NSM -> x]
W2: AL non-L-or-R* [EN -> AN]
    (fresh by complement of W2)
W3: [AL -> R] (permutes out to end)
W4: EN [ES -> EN] EN
W4: EN [CS -> EN] EN
W4: AN [CS -> AN] AN (permutes up to W2 (non-complement))
W5: [ET* -> EN*] EN and EN [ET* -> EN*]
W6: [S&T -> ON]
W7: L W/N* [EN -> L]


Segment into regions by AL, L and R.

L: [EN (ES|CS) EN -> EN]

X in Y = X (Y X)*
X out Y = Y (X Y)+

ENum = (EN NSM)+ in ((ES|CS) out ET*
ANum = AN+ in CS
AENum = (AN|EN)+ in CS

L: [ENum -> L][ANum -> AN][else -> ON]
R: [ENum ->EN][ANum -> AN][else -> ON]
AL:[AENum->AN]            [else -> ON]



L: [ET* (EN+ ((ES|CS) EN+)* ET* )+ -> L]
   [     AN+ (    CS  AN+)*        -> AN]
   [else -> ON]
R: [ET* (EN+ ((ES|CS) EN+)* ET* )+ -> EN]
   [     AN+ (    CS  AN+)*        -> AN]
   [else -> ON]
AL:[   (AN|EN)+ (CS (AN|EN)+)*     -> AN]
   [else -> ON]

*)

Definition W1234 (sor eor : bidi_class) text :=
  accum3 (fun (s : bidi_class * bidi_class) (c e : bidi_class) =>
    match s, c, e with
      | (alr, prev), NSM, _ => ((alr, prev), prev)
      | _, AL, _ => ((AL, AL), R)
      | _, L , _ => ((L, L), L)
      | _, R , _ => ((R, R), R)
      | (AL,_), EN, _ => ((AL, AN), AN)
      | (L,_), EN, _ => ((L, EN), L)
      | (R,_), EN, _ => ((R, EN), EN)
      | (alr,_), AN, _ => ((alr, AN), AN)
      | (alr,EN), ES, EN => ((alr, EN), EN)
      | (alr,EN), CS, EN => ((alr, EN), EN)
      | (alr,AN), CS, AN => ((alr, AN), AN)
      | (alr,EN), ET, _ => ((alr, EN), EN)
      | _, _, _ => (s, c)
    end) (sor, sor) text eor.

AL 
R [
L [W/N* (but not AN) EN* -> L]* [W/N* (not AN or EN) -> e] (AL|R)
L [W/N* -> L] L

Lemma : w1234 sor eor text = 

(*
W234567: (ALR, last, count) x lookahead
*)

(*
Fixpoint rule_w234567_aux alr last n text :=
  match text with
    | nil => rep ET n
    | AL :: text => rep ++ R :: rule_w234567_aux AL R 0 text
    | L  :: text => rep ++ L :: rule_w234567_aux L  L 0 text
    | R  :: text => rep ++ R :: rule_w234567_aux R  R 0 text
    | EN :: text =>
      match alr with
        | AL => rep ++ AN :: rule_w234567_aux AL AN 0 text
        | _  => rep EN ++ EN :: rule_w234567_aux alr EN 0 text
    | AN :: text => rep ++ AN :: rule_w234567_aux alr AN 0 text
    | ES :: text =>
      match last, lookahead text eor with
        | EN, EN => rep EN ++ EN :: rule_w234567_aux alr EN 0 text
        | _ , _  => rep ++ ES :: rule_w234567_aux alr ES 0 text
      end
    | CS :: text =>
      match last, lookahead text eor with
        | EN, EN => rep EN ++ EN :: rule_w234567_aux alr EN 0 text
        | AN, AN => rep ++ AN :: rule_w234567_aux alr AN 0 text
        | _ , _  => rep ++ CS :: rule_w234567_aux alr CS 0 text
      end
    | ET :: text =>
      match last, lookahead text eor with
        | EN, _  => rep ++ EN :: rule_w234567_aux alr EN 0 text
        | _ , ET => rule_w234567_aux alr 
    | _
*)
      
(*
Fixpoint rule_w5a_aux (n : nat) (c : list bidi_class) : list bidi_class :=
  match c with
    | ET :: cs => rule_w5a_aux (n+1) cs
    | EN :: cs => rep EN n ++ EN :: rule_w5a_aux 0 cs
    | c :: cs => rep ET n ++ rule_w5a_aux 0 cs
    | nil => rep ET n
  end.
*)

(*
NON = non-L-or-R-or-AL-or-EN-or-AN
LR = L-or-R-or-sor

TEXT = (AL | LR | NON | EN | AN)*

TEXT = (AL (NON | EN | AN)* | LR (NON | EN | AN)* )*

TEXT = (AL (NON* (EN | AN)* )* |LR (NON* (EN | AN)* )* )*

Apply W2
TEXT = (AL (NON* [EN | AN : AN]* )* | LR (NON* (EN | AN)* )* )*

TEXT = (A | B)*
A = AL (NON* [EN | AN : AN]*
B = LR (NON* (EN | AN)* )*

TEXT = (A | B)*
A = AL (NON* [EN | AN : AN]*
B = LR NON* (EN* NON* | AN* NON* )*

TEXT = (A | B)*
A = AL (NON* [EN | AN : AN]*
B = LR NON* ( | EN+ ((ES|CS) EN+ )* NON* | AN* NON* )*


ENum = [ET* EN+  ((ES|CS|ET+) EN+)* ET* : L ]
ANum = [(EN|AN)+ (    CS (EN|AN)+)*     : AN]
L  ((not in ENum : non-AN -> ON) [ENum : L ])* (not in ENum)*
R  ((not in ENum) [ENum : XN])* (not in ENum)*
AL ((not in ANum) [ANum : XN])* (not in ANum)*

(AN|EN|R) [N+:R] (AN|EN|R)
L [N+:R] L
(AN|EN|R) [N+:e] L
L [N+:e] (AN|EN|R)


L  (ALR-EN* ALR-EN-ET)? ([ET* EN+ ((ES|CS) EN+)* ET* : L] (ALR-EN* ALR-EN-ET)? )*
L  (ALR-EN* ALR-EN-ET)? ([ET* EN+ ((ES|CS) EN+)* ET* : L] (ALR-EN* ALR-EN-ET)? )*
R  blah* ([ET* EN+ ((ES|CS) EN+)* ET* : EN] blah* )*
AL blah* ([    EN+ (    CS  EN+)*     : AN] blah* )*
AL blah* ([    AN+ (    CS  AN+)*     : AN] blah* )*

W4: EN [ES -> EN] EN
W4: EN [CS -> EN] EN
W4: AN [CS -> AN] AN (permutes up to W2 (non-complement))
W5: [ET* -> EN*] EN [ET* -> EN*]
W6: [S&T -> ON]
W7: L W/N* [EN -> L]
*)

(* -or-AN
W2: AL non-L-or-R-or-AL-or-EN* ([EN+ (EN+)* -> AN] non-L-or-R-or-AL-or-EN* )*
W4: AN [CS -> AN] AN (permutes up to W2)
    L-or-R non-L-or-R-or-AL-or-EN* ([EN+ ((ES|CS) EN+)* -> EN] non-L-or-R-or-AL-or-EN* )*
      (complement of W2)
W4: EN [ES -> EN] EN
W4: EN [CS -> EN] EN
W5: [ET* -> EN*] EN [ET* -> EN*]
W6: [S&T -> ON]
W7: L W/N* [EN -> L]
*)

(*
AL (non-L-or-R-or-EN* [EN+ -> AN])*
AN [CS -> AN] AN
L-or-R (non-AL* [ET* EN+ ((ES|CS) EN+)* ET* -> EN])*
[S&T -> ON]
L W/N* [EN -> L]
[AL -> R]

--------
L non-R* [ET* EN+ ((ES|CS) EN+)* ET* -> L]
AL non-L-or-R* [EN -> AN]
[AN+ (CS AN+)* -> AN]
*)

(* Q: "European numbers" should be "a European number"
      unless you intend to require more than one. *)
(* FLAG *)
(* [ET* -> EN*] EN *)
(* EN [ET* -> EN*] *)

Fixpoint rule_w5a_aux (n : nat) (c : list bidi_class) : list bidi_class :=
  match c with
    | ET :: cs => rule_w5a_aux (n+1) cs
    | EN :: cs => rep EN n ++ EN :: rule_w5a_aux 0 cs
    | c :: cs => rep ET n ++ rule_w5a_aux 0 cs
    | nil => rep ET n
  end.

Definition rule_w5a (sor eor : bidi_class) text := rule_w5a_aux 0 text.

Definition rule_w5b sor eor text :=
  accum3 (fun s c _,
    match s, c with
      | EN, ET => (EN, EN)
      | _, _ => (c, c)
    end) sor text eor.

(* Q: "separators and terminators" is not defined. *)
(* [S&T -> ON] *)
(* == something like (non-EN S&T non-EN -> non-EN ON non-EN) *)
Definition rule_w6 (sor eor : bidi_class) text :=
  accum3 (fun s c n,
    (sor,
      match c with
        | ES | ET | CS => ON
        | _ => c
      end)) sor text eor.

(* L W/N* [EN -> L] *)
Definition rule_w7 (sor eor : bidi_class) text :=
  accum3 (fun s c _,
    (match s, c with
       | _, L  => (L, c)
       | _, R  => (R, c)
       | L, EN => (s, L)
       | _, _  => (s, c)
     end)) sor text eor.

Fixpoint rule_w1_2 (sor eor : bidi_class) text :=
  match text with
    | nil => nil
    | NSM :: text => sor :: rule_w1_2 sor eor text
    | c :: text => c :: rule_w1_2 c eor text
  end.

Fixpoint accum3_aux'
  (f : bidi_class -> bidi_class -> bidi_class)
  (c : bidi_class) (text : list bidi_class) (eor : bidi_class) :
  (list bidi_class) :=
  match text with
    | nil => f c eor :: nil
    | c' :: text' => f c c' :: accum3_aux' f c' text' eor
  end.

Definition accum3'
  (f : bidi_class -> bidi_class -> bidi_class)
  (text : list bidi_class) (eor : bidi_class) :
  (list bidi_class) :=
  match text with
    | nil => nil
    | c :: text => accum3_aux' f c text eor
  end.

Definition rule_w1' (eor : bidi_class) text :=
  accum3' (fun c _,
    match c with
      | NSM => L
      | _ => c
    end) text eor.

Fixpoint rule_w1_2' (eor : bidi_class) text :=
  match text with
    | nil => nil
    | NSM :: text => L :: rule_w1_2' eor text
    | c :: text => c :: rule_w1_2' eor text
  end.

Definition f (_ _ : bidi_class) := L.

Fixpoint plus1 a :=
  match a with
    | O => Datatypes.S O
    | Datatypes.S a' => Datatypes.S (plus1 a')
  end.

Lemma test : forall text eor, rule_w1' eor text = rule_w1_2' eor text.
  intro.
  unfold rule_w1'. unfold accum3'.
  destruct text.
   unfold rule_w1_2'. trivial.
   generalize dependent b.
    induction text.
     destruct b; unfold accum3_aux'; unfold rule_w1_2'; trivial.
     intros.
      unfold accum3_aux'. fold accum3_aux'.
      remember (a :: text) as text'. unfold rule_w1_2'. fold rule_w1_2'. rewrite Heqtext'.
      specialize (IHtext a eor).
      destruct b; rewrite IHtext; trivial.
Qed.

(*
Lemma test2 : forall text sor eor, rule_w1 sor eor text = rule_w1_2 sor eor text.
  intro.
  unfold rule_w1. unfold accum3.
  destruct text.
   trivial.
   generalize dependent b.
    induction text.
     unfold accum3_aux. unfold rule_w1_2. destruct b; trivial.
     intros. unfold accum3_aux. fold accum3_aux.
      remember (a :: text) as atext. unfold rule_w1_2. fold rule_w1_2. rewrite Heqatext.
      destruct b; rewrite IHtext; trivial.
Qed.
*)

Lemma accum3_aux_preserves_length : forall s f text (sor : s) c eor,
  length text + 1 = length (accum3_aux f sor c text eor).
Proof.
  induction text.
   intros.
    unfold accum3_aux. remember (f0 sor c eor) as fres. destruct fres.
    unfold length. trivial.
   intros.
    unfold accum3_aux. fold (accum3_aux (s := s)).
    remember (f0 sor c a) as fres. destruct fres.
    unfold length. fold (length (A := bidi_class)). simpl.
    rewrite (IHtext s0 a eor). trivial.
Qed.

Lemma text3 : forall {s1 s2 : Type} f1 f2 text (sor1 : s1) (sor2 : s2) eor,
  f1 
  accum2 f2 sor2 (accum2 f1 sor1 text eor) eor =
  accum2 (fun (sor : s1 * s2) c eor,
    let (sor1, sor2) := sor in
      let (sor1, c) := f1 sor1 c eor in
        let (sor2, c) := f2 sor2 c eor in
          (* eor is wrong, we need eor' *)
          ((sor1, sor2), c))
    (sor1, sor2) text eor.
Proof.
  induction text.
   intros.
    unfold accum2. trivial.
   intros.
    unfold accum2 at 3. fold (accum2 (s := s1 * s2)).
    unfold accum2 at 2. fold (accum2 (s := s1)).
    destruct (f1 sor1 a match text with
                          | nil => eor
                          | class :: _ => class
                        end).
    unfold accum2 at 1. fold (accum2 (s := s2)).
    destruct text.
     unfold accum2 at 1. destruct (f2 sor2 b eor).
      rewrite (IHtext s s0 eor). trivial.
     unfold accum2 at 1. fold (accum2 (s := s1)).
      destruct (f1 s b0
        match text with
          | nil => eor
          | class :: _ => class
        end).
    destruct (

    destruct text.
     unfold accum2 at 3.
      unfold accum2 at 2.
      destruct (f1 sor1 a eor).
      unfold accum2 at 1.
      destruct (f2 sor2 b eor). trivial.
     unfold accum2 at 3. fold (accum2 (s := s1 * s2)).
      unfold accum2 at 2. fold (accum2 (s := s1)).
      destruct (f1 sor1 a b).
      unfold accum2 at 1. fold (accum2 (s := s2)).
      destruct (f2 
      
     remember (f1 sor1 a eor) as f1res. inversion f1res.
 destruct f1res.
 fold (accum2 (s := s1 * s2)).
    unfold accum2 at 2. fold (accum2 (s := s1)).
    remember (f1 sor1 a match text with
                          | nil => eor
                          | class :: _ => class
                        end) as f1res. destruct f1res.
    unfold accum2 at 1. fold (accum2 (s := s2)).
    remember (f2 sor2 b match text with
                          | nil => eor
                          | class :: _ => class
                        end) as f2res. destruct f2res.
    unfold accum2 at 1. fold (accum2 (s := s2)).


Lemma text3 : forall {s1 s2 : Type} f1 f2 text (sor1 : s1) (sor2 : s2) c eor,
  match accum3_aux f1 sor1 c text eor with
    | nil => nil
    | c :: text => accum3_aux f2 sor2 c text eor
  end =
  accum3_aux (fun (sor : s1 * s2) c eor,
    let (sor1, sor2) := sor in
      let (sor1, c) := f1 sor1 c eor in
        let (sor2, c) := f2 sor2 c eor in
          ((sor1, sor2), c))
    (sor1, sor2) c text eor.
Proof.
  induction text.
   intros.
    unfold accum3_aux at 3. unfold accum3_aux at 1.
    remember (f1 sor1 c eor) as f1res. destruct f1res.
    unfold accum3_aux. remember (f2 sor2 b eor) as f2res. destruct f2res.
    trivial.
   intros.
    unfold accum3_aux at 1. fold (accum3_aux (s := s1)).
    unfold accum3_aux at 3. fold (accum3_aux (s := s1 * s2)).
    remember (f1 sor1 c a) as f1res. destruct f1res. clear Heqf1res.
    unfold accum3_aux at 2. unfold accum3_aux at 1.
    destruct 
    unfold accum3_aux at 3. simpl.
    unfold accum3_aux at 3. fold (accum3_aux (s := s1 * s2)).
    unfold accum3_aux at 2. fold (accum3_aux (s := s1)).
    unfold accum3_aux at 3. fold (accum3_aux (s := s1 * s2)).
  intros s1 s2 f1 f2.
  intros.


Lemma text3 : forall {s1 s2 : Type} f1 f2 text (sor1 : s1) (sor2 : s2) eor,
  
  accum3 f2 sor2 (accum3 f1 sor1 text eor) eor =
  accum3 (fun (sor : s1 * s2) c eor,
    let (sor1, sor2) := sor in
      let (sor1, c) := f1 sor1 c eor in
        let (sor2, c) := f2 sor2 c eor in
          ((sor1, sor2), c))
    (sor1, sor2) text eor.
  intros.
  destruct text.
   unfold accum3. trivial.
   unfold accum3. 
   generalize dependent eor. generalize dependent b.
    generalize dependent sor1. generalize dependent sor2.
    generalize dependent text.
    unfold accum3. remember
    induction text.
     intros. unfold accum3. unfold accum3_aux.
      fold (accum3_aux (s := s1)). fold (accum3_aux (s := s2)).
      remember (f1 sor1 b eor) as f1res. destruct f1res.
      unfold accum3_aux. remember (f2 sor2 b0 eor) as f2res. destruct f2res.
      trivial.
     intros.
      unfold accum3 at 3. unfold accum3_aux. fold (accum3_aux (s := s1 * s2)).
 unfold accum3.
      unfold accum3_aux.
      fold (accum3_aux (s := s)). fold (accum3_aux (s := s * s)).
      remember (f1 sor b a) as f1res. destruct f1res.
      destruct text.
       unfold accum3_aux at 2.
        remember (f1 s0 a eor) as f1res. destruct f1res.
        unfold accum3_aux at 1. remember (f2 sor b0 b1) as f2res. destruct f2res.
        unfold accum3_aux.
unfold accum3_aux at 2.
      fold (accum3_aux (s := s)). fold (accum3_aux (s := s * s)).
      
unfold accum3_aux. fold accum3_aux.
      remember (f1 sor b eor) as f1res. destruct f1res.
      unfold accum3_aux.
      destruct X.
      inversion c'.
      rembmer (f sor b eor) as (x,y).
      remember (let (_, c') := f1 sor b eor in c' :: nil) as c'nil.
      destruct c'nil. simpl.
simpl.
    destruct b. unfold accum3. unfold accum3_aux.
      

  accum3 (fun class c _,
    match c with
      | NSM => (class, class)
      | _ => (c, c)
    end) sor text eor.


Lemma post_w_types.

(* Q: Define "neutral". E.g. "BN" is not a neutral. *)

(* Q: "Start-of-level-run (sor) and end-of-level-run (eor) are used at
level run boundaries." is unneeded in this rule since it is covered at
the start of the section.  Similar rules in W don't have this
phrasing. (TODO: but W1 does) *)

(* FLAG *)
(* x [N* -> x*] x where EN and AN are like R *)
Definition rule_n1 :.

(* [N* -> e] *)
Definition rule_n2 (sor eor : bidi_class) text :=
  map (fun (c : char_state),
    match c with
      (c, class, level) =>
      (c, match class with
            | B | S | WS | ON => if is_even level then L else R
            | _ => class
          end,
      level)
    end) text.

Lemma post_n_types L R AN EN.

(*
Type  	Embedding Level
	Even 	Odd
L 	EL 	EL+1
R 	EL+1 	EL
AN 	EL+2 	EL+1
EN 	EL+2 	EL+1
*)
Definition rule_i := .

(* Q: Embedding levels reparsed? *)
(* Q: What about [[L]]EN[[L]]? Do they go together? *)
