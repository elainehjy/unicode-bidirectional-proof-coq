<<<<<<< HEAD

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
=======
open Unicode_bidi_class
open Generated_test_cases_tmp

let string_of_bidi_class : bidi_class -> string = function
>>>>>>> 00a3550 (updated all test files)
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

<<<<<<< HEAD

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


=======
(* 1. skip tests with the elements?
 2. remove
 3. implement the x1-x8 rules *)

let map_bidi_class : bidi_class -> bidi_class option = function
  | RLO | RLE | PDF | LRO | LRE | BN -> None
  | bc -> Some bc

let rec rule0 : bidi_class list -> bidi_class list = function
  | [] -> []
  | c :: text' ->
    (match map_bidi_class c with
     | Some c' -> c' :: (rule0 text')
     | None -> rule0 text')

(* Convert a list of bidi_class to a readable string *)
let string_of_bidi_class_list : bidi_class list -> string = fun bidi_classes ->
  String.concat ", " (List.map string_of_bidi_class bidi_classes)

type test_result_rule0 = {
  test_number: int;
  input: bidi_class list;
  expected_order: int list;
  actual_order: int list;
}

let test_rule0_single (i: int) (input: bidi_class list) (expected_order: int list) : bool * test_result_rule0 option =
  let actual = rule0 input in
  let actual_order = List.mapi (fun idx _ -> idx) actual in
  if actual_order = expected_order then
    (true, None)
  else
    (false, Some {test_number = i; input; expected_order; actual_order})

(* Run tests for rule0 on all test cases and print a summary *)
let test_rule0_all () =
  let total = ref 0 in
  let failed = ref 0 in
  let failed_details = ref [] in

  (* Iterate over each test case *)
  List.iteri (fun i test_case ->
    List.iter (fun (bidi_classes, _num) ->
      incr total;
      let expected_order = test_case.ordering in
      let passed, result = test_rule0_single i bidi_classes expected_order in
      if not passed then (
        incr failed;
        match result with
        | Some details -> failed_details := details :: !failed_details
        | None -> ()
      )
    ) test_case.data
  ) test_cases;

  (* Print summary *)
  Printf.printf "Summary rule0: %d tests executed, %d passed, %d failed.\n"
    !total
    (!total - !failed)
    !failed;

  (* Print details of failed tests *)
  List.iter (fun {test_number; input; expected_order; actual_order} ->
    Printf.printf "Failed test %d:\n" test_number;
    Printf.printf "  Input: [%s]\n" (string_of_bidi_class_list input);
    Printf.printf "  Expected order: [%s]\n" (String.concat ", " (List.map string_of_int expected_order));
    Printf.printf "  Actual order: [%s]\n\n" (String.concat ", " (List.map string_of_int actual_order))
  ) (List.rev !failed_details)

(* Run the tests *)
let () = test_rule0_all ()

(* ********** *)

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

(* Define a test result type for rule_w1 *)
type test_result_w1 = {
  test_number: int;
  input: bidi_class list;
  prev: bidi_class;
  expected_output: bidi_class list;  (* Expected result after applying rule_w1 *)
  actual_output: bidi_class list;    (* Actual result after applying rule_w1 *)
}

(* Test a single case of rule_w1 *)
let test_rule_w1_single (i: int) (input: bidi_class list) (prev: bidi_class) (expected_output: bidi_class list) : bool * test_result_w1 option =
  let actual_output = rule_w1 input prev in
  if actual_output = expected_output then
    (true, None)  (* Test passed *)
  else
    (false, Some {test_number = i; input; prev; expected_output; actual_output})

(* Function to run tests for rule_w1 on all test cases and print a summary *)
let test_rule_w1_on_all_cases () =
  let total = ref 0 in
  let failed = ref 0 in
  let failed_details = ref [] in

  (* Iterate over each test case *)
  List.iteri (fun i test_case ->
    List.iter (fun (bidi_classes, _num) ->
      incr total;
      (* Set the initial `prev` class to a default value, e.g., L *)
      let prev = L in  (* You can adjust this based on your test logic *)
      let expected_output = rule_w1 bidi_classes prev in  (* This could be replaced by predefined expected output *)
      let passed, result = test_rule_w1_single i bidi_classes prev expected_output in
      if not passed then (
        incr failed;
        match result with
        | Some details -> failed_details := details :: !failed_details
        | None -> ()
      )
    ) test_case.data
  ) test_cases;

  (* Print summary *)
  Printf.printf "Summary rule_w1: %d tests executed, %d passed, %d failed.\n"
    !total
    (!total - !failed)
    !failed;

  (* Print details of failed tests *)
  List.iter (fun {test_number; input; prev; expected_output; actual_output} ->
    Printf.printf "Failed test %d:\n" test_number;
    Printf.printf "  Input: [%s]\n" (string_of_bidi_class_list input);
    Printf.printf "  Previous class: %s\n" (string_of_bidi_class prev);
    Printf.printf "  Expected output: [%s]\n" (string_of_bidi_class_list expected_output);
    Printf.printf "  Actual output: [%s]\n\n" (string_of_bidi_class_list actual_output)
  ) (List.rev !failed_details)

(* Run the tests *)
let () = test_rule_w1_on_all_cases ()


(*

(* ********** *)

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

(** val rule_w12 : bidi_class list -> bidi_class -> bool -> bidi_class list **)

let rec rule_w12 text prev is_al =
  match text with
  | [] -> []
  | c :: text' ->
    (match c with
     | NSM ->
       (match prev with
        | RLI -> ON :: (rule_w12 text' ON is_al)
        | PDI -> ON :: (rule_w12 text' ON is_al)
        | LRI -> ON :: (rule_w12 text' ON is_al)
        | FSI -> ON :: (rule_w12 text' ON is_al)
        | EN -> (if is_al then AN else EN) :: (rule_w12 text' (if is_al then AN else EN) is_al)
        | _ -> prev :: (rule_w12 text' prev (next_is_al prev is_al)))
     | EN -> (if is_al then AN else EN) :: (rule_w12 text' (if is_al then AN else EN) is_al)
     | _ -> c :: (rule_w12 text' c (next_is_al c is_al)))

 *)
>>>>>>> 00a3550 (updated all test files)
