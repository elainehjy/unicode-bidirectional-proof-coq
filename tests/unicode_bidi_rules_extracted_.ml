
type bidi_class =
| WS
| S
| RLO
| RLI
| RLE
| R
| PDI
| PDF
| ON
| NSM
| LRO
| LRI
| LRE
| L
| FSI
| ET
| ES
| EN
| CS
| BN
| B
| AN
| AL

(** val rule_w1 : bidi_class list -> bidi_class -> bidi_class list **)

let rec rule_w1 text prev =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | NSM ->
       (match prev with
        | RLI -> ON :: (rule_w1 text' ON)
        | PDI -> ON :: (rule_w1 text' ON)
        | LRI -> ON :: (rule_w1 text' ON)
        | FSI -> ON :: (rule_w1 text' ON)
        | _ -> prev :: (rule_w1 text' prev))
     | _ -> c :: (rule_w1 text' c))

(** val next_is_al : bidi_class -> bool -> bool **)

let next_is_al c is_al =
  match c with
  | R -> false
  | L -> false
  | AL -> true
  | _ -> is_al

(** val rule_w2 : bidi_class list -> bool -> bidi_class list **)

let rec rule_w2 text is_al =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | EN -> (if is_al then AN else EN) :: (rule_w2 text' is_al)
     | _ -> c :: (rule_w2 text' (next_is_al c is_al)))

(** val rule_w3 : bidi_class list -> bidi_class list **)

let rec rule_w3 = function
| [] -> []
| c :: text' -> (match c with
                 | AL -> R :: (rule_w3 text')
                 | _ -> c :: (rule_w3 text'))

(** val rule_w4 : bidi_class list -> bidi_class -> bidi_class list **)

let rec rule_w4 text prev =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | ES ->
       (match text' with
        | [] -> c :: []
        | b :: _ ->
          (match b with
           | EN ->
             (match prev with
              | EN -> EN :: (rule_w4 text' EN)
              | _ -> c :: (rule_w4 text' c))
           | _ -> c :: (rule_w4 text' c)))
     | CS ->
       (match text' with
        | [] -> c :: []
        | b :: _ ->
          (match b with
           | EN ->
             (match prev with
              | EN -> EN :: (rule_w4 text' EN)
              | _ -> c :: (rule_w4 text' c))
           | AN ->
             (match prev with
              | AN -> AN :: (rule_w4 text' AN)
              | _ -> c :: (rule_w4 text' c))
           | _ -> c :: (rule_w4 text' c)))
     | _ -> (match text' with
             | [] -> c :: []
             | _ :: _ -> c :: (rule_w4 text' c)))

(** val w5_before_en : bidi_class list -> bool **)

let rec w5_before_en = function
| [] -> false
| b :: text' -> (match b with
                 | ET -> w5_before_en text'
                 | EN -> true
                 | _ -> false)

(** val rule_w5 : bidi_class list -> bool -> bidi_class list **)

let rec rule_w5 text after_en =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | ET -> (if (||) after_en (w5_before_en text') then EN else ET) :: (rule_w5 text' after_en)
     | EN -> EN :: (rule_w5 text' true)
     | _ -> c :: (rule_w5 text' false))

(** val rule_w6 : bidi_class list -> bidi_class list **)

let rec rule_w6 = function
| [] -> []
| c :: text' ->
  (match c with
   | ET -> ON :: (rule_w6 text')
   | ES -> ON :: (rule_w6 text')
   | CS -> ON :: (rule_w6 text')
   | _ -> c :: (rule_w6 text'))

(** val rule_w7 : bidi_class list -> bool -> bidi_class list **)

let rec rule_w7 text after_l =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | R -> R :: (rule_w7 text' false)
     | L -> L :: (rule_w7 text' true)
     | EN -> (if after_l then L else EN) :: (rule_w7 text' after_l)
     | _ -> c :: (rule_w7 text' after_l))

(** val is_ni : bidi_class -> bool **)

let is_ni = function
| WS -> true
| S -> true
| RLI -> true
| PDI -> true
| ON -> true
| LRI -> true
| FSI -> true
| B -> true
| _ -> false

(** val is_strong : bidi_class -> bool **)

let is_strong = function
| R -> true
| L -> true
| EN -> true
| AN -> true
| _ -> false

(** val n1_next_strong : bidi_class list -> bidi_class -> bidi_class **)

let rec n1_next_strong text eos =
  match text with
  | [] -> eos
  | c :: text' ->
    (match c with
     | R -> c
     | L -> c
     | EN -> c
     | AN -> c
     | _ -> n1_next_strong text' eos)

(** val rule_n1 : bidi_class list -> bidi_class -> bidi_class -> bidi_class list **)

let rec rule_n1 text prev eos =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | WS ->
       (match prev with
        | R ->
          (match n1_next_strong (WS :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | L ->
          (match n1_next_strong (WS :: text') eos with
           | L -> L :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | EN ->
          (match n1_next_strong (WS :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | AN ->
          (match n1_next_strong (WS :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | _ -> c :: (rule_n1 text' prev eos))
     | S ->
       (match prev with
        | R ->
          (match n1_next_strong (S :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | L ->
          (match n1_next_strong (S :: text') eos with
           | L -> L :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | EN ->
          (match n1_next_strong (S :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | AN ->
          (match n1_next_strong (S :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | _ -> c :: (rule_n1 text' prev eos))
     | RLI ->
       (match prev with
        | R ->
          (match n1_next_strong (RLI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | L ->
          (match n1_next_strong (RLI :: text') eos with
           | L -> L :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | EN ->
          (match n1_next_strong (RLI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | AN ->
          (match n1_next_strong (RLI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | _ -> c :: (rule_n1 text' prev eos))
     | PDI ->
       (match prev with
        | R ->
          (match n1_next_strong (PDI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | L ->
          (match n1_next_strong (PDI :: text') eos with
           | L -> L :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | EN ->
          (match n1_next_strong (PDI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | AN ->
          (match n1_next_strong (PDI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | _ -> c :: (rule_n1 text' prev eos))
     | ON ->
       (match prev with
        | R ->
          (match n1_next_strong (ON :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | L ->
          (match n1_next_strong (ON :: text') eos with
           | L -> L :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | EN ->
          (match n1_next_strong (ON :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | AN ->
          (match n1_next_strong (ON :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | _ -> c :: (rule_n1 text' prev eos))
     | LRI ->
       (match prev with
        | R ->
          (match n1_next_strong (LRI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | L ->
          (match n1_next_strong (LRI :: text') eos with
           | L -> L :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | EN ->
          (match n1_next_strong (LRI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | AN ->
          (match n1_next_strong (LRI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | _ -> c :: (rule_n1 text' prev eos))
     | FSI ->
       (match prev with
        | R ->
          (match n1_next_strong (FSI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | L ->
          (match n1_next_strong (FSI :: text') eos with
           | L -> L :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | EN ->
          (match n1_next_strong (FSI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | AN ->
          (match n1_next_strong (FSI :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | _ -> c :: (rule_n1 text' prev eos))
     | B ->
       (match prev with
        | R ->
          (match n1_next_strong (B :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | L ->
          (match n1_next_strong (B :: text') eos with
           | L -> L :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | EN ->
          (match n1_next_strong (B :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | AN ->
          (match n1_next_strong (B :: text') eos with
           | R -> R :: (rule_n1 text' prev eos)
           | EN -> R :: (rule_n1 text' prev eos)
           | AN -> R :: (rule_n1 text' prev eos)
           | _ -> c :: (rule_n1 text' prev eos))
        | _ -> c :: (rule_n1 text' prev eos))
     | _ -> c :: (rule_n1 text' (if is_strong c then c else prev) eos))

(** val rule_n2 : bidi_class list -> bidi_class -> bidi_class list **)

let rec rule_n2 text dir =
  match text with
  | [] -> []
  | c :: text' -> if is_ni c then dir :: (rule_n2 text' dir) else c :: (rule_n2 text' dir)
