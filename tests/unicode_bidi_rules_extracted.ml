
open Unicode_bidi_class

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
