
open Generated_test_cases

(* open Unicode_bidi_class *)

(* type bidi_class =
| L
| R
| AL
| EN
| ES
| ET
| AN
| CS
| NSM
| B
| S
| WS
| ON
| LRI
| RLI
| FSI
| PDI *)

(** val rule_w1 : bidi_class list -> bidi_class -> bidi_class list **)

let rec rule_w1 text prev =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | NSM ->
       (match prev with
        | LRI -> ON :: (rule_w1 text' ON)
        | RLI -> ON :: (rule_w1 text' ON)
        | FSI -> ON :: (rule_w1 text' ON)
        | PDI -> ON :: (rule_w1 text' ON)
        | _ -> prev :: (rule_w1 text' prev))
     | _ -> c :: (rule_w1 text' c))

(** val next_is_al : bidi_class -> bool -> bool **)

let next_is_al c is_al =
  match c with
  | L -> false
  | R -> false
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

(** val rule_w12 : bidi_class list -> bidi_class -> bool -> bidi_class list **)

let rec rule_w12 text prev is_al =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | EN -> (if is_al then AN else EN) :: (rule_w12 text' (if is_al then AN else EN) is_al)
     | NSM ->
       (match prev with
        | EN -> (if is_al then AN else EN) :: (rule_w12 text' (if is_al then AN else EN) is_al)
        | LRI -> ON :: (rule_w12 text' ON is_al)
        | RLI -> ON :: (rule_w12 text' ON is_al)
        | FSI -> ON :: (rule_w12 text' ON is_al)
        | PDI -> ON :: (rule_w12 text' ON is_al)
        | _ -> prev :: (rule_w12 text' prev (next_is_al prev is_al)))
     | _ -> c :: (rule_w12 text' c (next_is_al c is_al)))



(* Helper function to take the first n elements from a list *)
let rec take n l =
  match l with
  | [] -> []
  | x :: xs -> if n > 0 then x :: (take (n - 1) xs) else []

(* Helper function to convert bidi_property to string for debugging *)
let string_of_bidi_property = function
  | WS -> "WS"
  | S -> "S"
  | RLO -> "RLO"
  | RLI -> "RLI"
  | RLE -> "RLE"
  | R -> "R"
  | PDI -> "PDI"
  | PDF -> "PDF"
  | ON -> "ON"
  | NSM -> "NSM"
  | LRO -> "LRO"
  | LRI -> "LRI"
  | LRE -> "LRE"
  | L -> "L"
  | FSI -> "FSI"
  | ET -> "ET"
  | ES -> "ES"
  | EN -> "EN"
  | CS -> "CS"
  | BN -> "BN"
  | B -> "B"
  | AN -> "AN"
  | AL -> "AL"


(* Function to apply a rule to a test case and check the result *)
let apply_rule_to_test_case rule test_case =
  List.map (fun (props, bitset) ->
    let result = rule props in
    (* Compare the result to the expected value (props in this case) *)
    if result = props then
      Printf.printf "Test passed for input %s\n" (String.concat "; " (List.map string_of_bidi_property props))
    else
      Printf.printf "Test failed for input %s\n" (String.concat "; " (List.map string_of_bidi_property props));
    result
    ) test_case.data

(* Run tests for the first n test cases *)
let run_tests rule n =
  let first_n_cases = take n Generated_test_cases.test_cases in
  List.iter (fun test_case ->
    Printf.printf "Running test case with levels: [%s]\n"
      (String.concat "; " (List.map (function Some l -> string_of_int l | None -> "None") test_case.levels));
    apply_rule_to_test_case rule test_case;
    ()
  ) first_n_cases
;;

(* Run tests for rule_w1 against the first 5 test cases *)
let () =
  Printf.printf "Running tests for rule_w1 on the first 5 test cases...\n";
  run_tests (fun text -> rule_w1 text L) 5
            (*    rule_w1 5 *)


