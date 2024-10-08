(*
   This script reads the BidiTest.txt file and generates a Coq file with the test cases.
   The BidiTest.txt file is available at
   https://raw.githubusercontent.com/unicode-org/icu/main/icu4c/source/test/testdata/BidiTest.txt *)

(* 
 * Constants
 *)

(* The name of the input file containing the test cases *)
let input_filename : string = "BidiTest.txt"

(* The name of the output file where the generated gallina test cases are written *)
let generated_filename : string = "generated_test_cases.v"

(* 
 * File Input/Output functions 
 *)

(* Function to read the lines of a file *)
let read_lines (filename : string) : string list =
  let contents = In_channel.with_open_bin filename In_channel.input_all in
  String.split_on_char '\n' contents
;;

(* Function to write lines to a file *)
(*let write_lines (filename : string) (lines : string list) : unit =
  let contents = String.concat "\n" lines in
  Out_channel.with_open_bin filename (fun oc -> Out_channel.output_string oc contents)
;; *)

let write_lines (filename : string) (lines : string list) : unit =
  let contents = String.concat "\n" lines in
  Out_channel.with_open_bin filename (fun oc -> Out_channel.output_string oc (contents ^ "\n"))
;;


(* 
 * Test Case type and printing functions
 *)

(* Type representing a test case *)
type test_case =
  { levels : int option list
      (* List of numbers indicating the resulting levels for each input property value.
         The UBA does not assign levels to certain values (indicated with an 'x').
         Unassigned levels are represented as None *)
  ; orderings : int list
      (* An ordered list of numbers indicating the resulting visual ordering from left to right.
         The numbers are zero-based, and are indexes into the input string.
         Items with a level of x are skipped. *)
  ; datalines : (string list * int) list
  (* An ordered list of BiDi property values and a hex bitset for paragraph levels.
     1 = auto-LTR, 2 = LTR, 4 = RTL.*)
  }

(* Function to convert the levels of a test case to a string *)
let print_levels (levels : int option list) : string =
  let level_to_string l =
    match l with
    | Some i -> string_of_int i
    | None -> "x"
  in
  List.map level_to_string levels |> String.concat "; "
;;

(* Function to convert the datalines of a test case to a string *)
let print_datalines (datalines : (string list * int) list) : string =
  let props_to_string props = String.concat " " props in
  let dataline_to_string (props, bitset) =
    Printf.sprintf "      ([%s], %i);" (props_to_string props) bitset  (* Adds a semicolon and spaces *)
  in
  let datalines_strings = List.map dataline_to_string datalines in (* Create a list of formatted strings and join them with newlines *)
  "\n" ^ String.concat "\n" datalines_strings  (* Concatenate each dataline with a newline *)
;;

(* Function to convert the datalines of a test case to a string 
let print_datalines (datalines : (string list * int) list) : string =
  let props_to_string props = String.concat " " props in
  let dataline_to_string (props, bitset) =
    Printf.sprintf "%s:%i" (props_to_string props) bitset
  in
  List.map dataline_to_string datalines |> String.concat "; " 
;; *)

(* Function to pretty print a test case *)
let print_test_case (testcase : test_case) : unit =
  print_endline "{";
  Printf.printf "   Levels: %s\n" (print_levels testcase.levels);
  Printf.printf
    "   Ordering: %s\n"
    (String.concat "; " (List.map string_of_int testcase.orderings));
  Printf.printf "   Data: %s\n" (print_datalines testcase.datalines);
  print_endline "}"
;;

(*
 * Set of strings
 *)
module StringSet = Set.Make (String)

(*
 * Parsing functions
 *)

(* Function to check if a line is a comment or blank *)
let is_comment_or_blank (str : string) : bool =
  String.starts_with ~prefix:"#" str || String.equal str ""
;;

(* Function to remove heading and trim string *)
let trim_heading (input : string) (heading_len : int) : string =
  let len = String.length input in
  String.sub input heading_len (len - heading_len) |> String.trim
;;

(* Parses a string of levels, converting it to a list of optional integers *)
let parse_levels (input : string) : int option list =
  let levels_str = trim_heading input 8 in
  let levels_ls = String.split_on_char ' ' levels_str in
  let string_to_int_option l =
    if String.equal l "x" then None else Some (int_of_string l)
  in
  List.map string_to_int_option levels_ls
;;

(* Parses a string of orderings, converting it to a list of integers *)
let parse_orderings (input : string) : int list =
  let ordering_str = trim_heading input 9 in
  let not_empty x = not @@ String.equal x "" in
  let ordering_ls = String.split_on_char ' ' ordering_str |> List.filter not_empty in
  List.map int_of_string ordering_ls
;;

(* Parses the datalines of a test case into a list of property value and bitset pairs.
   Additionally, it collects a set of bidi property values. *)
let rec parse_datalines
  (input : string list)
  (acc : (string list * int) list)
  (props_set : StringSet.t)
  : (string list * int) list * StringSet.t
  =
  match input with
  | hd :: tl ->
    let ls = String.split_on_char ';' hd in
    (match ls with
     | [ props_str; bitset_str ] ->
       let props = String.split_on_char ' ' (String.trim props_str) in
       let bitset = int_of_string @@ String.trim bitset_str in
       let updated_set =
         List.fold_left (fun acc x -> StringSet.add x acc) props_set props
       in
       parse_datalines tl ((props, bitset) :: acc) updated_set
     | _ -> failwith "Illformed property value and bitset string")
  | [] -> List.rev acc, props_set
;;

(* Parses a test case from a list of strings. Additionally, returns the set of
   bidi property values. *)
let parse_test_case (input : string list) : test_case * StringSet.t =
  match input with
  | levels_str :: ordering_str :: dataline_str ->
    let datalines, props_set = parse_datalines dataline_str [] StringSet.empty in
    ( { levels = parse_levels levels_str
      ; orderings = parse_orderings ordering_str
      ; datalines
      }
    , props_set )
  | _ -> failwith "Illformed test case list"
;;

(* Function to convert a set to a list by folding over the set *)
let set_to_list set =
  StringSet.fold (fun elt acc -> elt :: acc) set []
;;

(* Parses a list of test cases from a list of strings. Additionally, returns the set of
   bidi property values. *)
let parse_test_cases (input : string list) : test_case list * string list =
  let process_line (acc : test_case list * string list * StringSet.t) (str : string) =
    let test_cases, strings, props_set = acc in
    if not (is_comment_or_blank str) (* finished processing a test case *)
    then test_cases, str :: strings, props_set
    else if List.length strings = 0 (* nothing to parse*)
    then test_cases, [], props_set
    else (
      let test_case, updated_set = parse_test_case @@ List.rev strings in
      let combined_set = StringSet.union props_set updated_set in
      test_case :: test_cases, [], combined_set)
  in
  let rev_test_cases, _, properties_set =
    List.fold_left process_line ([], [], StringSet.empty) input
  in
  List.rev rev_test_cases, set_to_list properties_set
;;

(*
 * Generating Coq test case file 
 *)

(* Header and imports for the generated file *)
let header_and_imports : string list =
  [ "(* " ^ generated_filename ^ " *)"
  ; ""
  ; "Require Import List."
  ; "Import ListNotations."
  ; ""
  ]
;;

<<<<<<< HEAD
(* Generates the Coq definition of the Bidi_Property type based on the
   set of property values *)
let generate_bidi_properties_type (props : string list) : string list =
  let edited_props = List.map (fun x -> "  | " ^ x) props in
  [ "Inductive Bidi_Property : Type :=" ] @ edited_props @ [ "."; "" ]
=======
(* Generates the Coq definition of the Bidi_Class type based on the
   set of property values *)
let generate_bidi_class_type (props : string list) : string list =
  let edited_props = List.map (fun x -> "  | " ^ x) props in
  [ "Inductive Bidi_Class : Type :=" ] @ edited_props @ [ "."; "" ]
>>>>>>> 00a3550 (updated all test files)
;;

(* Test case type in Coq *)
let test_case_type : string list =
  [ "Record Test_Case : Type := {"
  ; "  levels : list (option nat);"
  ; "  ordering : list nat;"
<<<<<<< HEAD
  ; "  data : list (list Bidi_Property * nat);"
=======
  ; "  data : list (list Bidi_Class * nat);"
>>>>>>> 00a3550 (updated all test files)
  ; "}."
  ; ""
  ]
;;

(* Generates the Coq definition of a test case *)
let generate_test_case_definition (test_case : test_case) : string list =
  let levels_to_string l =
    let level_to_string x =
      match x with
      | Some x -> "Some " ^ string_of_int x
      | None -> "None"
    in
    List.map level_to_string l |> String.concat "; "
  in
  let dataline_to_string (prop, bitset) =
    Printf.sprintf "([%s], %i)" (String.concat "; " prop) bitset
  in
  let formatted_data = List.map dataline_to_string test_case.datalines in
  [ "  {|"
  ; "    levels := [" ^ levels_to_string test_case.levels ^ "];"
  ; "    ordering := ["
    ^ String.concat "; " (List.map string_of_int test_case.orderings)
    ^ "];"
  ; "    data := ["
  ; "      " ^ String.concat ";\n      " formatted_data  (* Force newlines here *)
  ; "    ]"
  ; "  |}"
  ]
;;

(* Generates the Coq definition of all test cases *)
let generate_test_cases_definition (tcs : test_case list) : string list =
  let rec separated_definitions (cs : test_case list) : string list =
    match cs with
    | [] -> []
    | [ tc ] -> generate_test_case_definition tc
    | hd :: tl -> generate_test_case_definition hd @ [ "  ;" ] @ separated_definitions tl
  in
  [ "Definition test_cases : list Test_Case := [" ] @ separated_definitions tcs @ [ "]." ]
;;

(* Generates the Coq file with the test cases *)
let generate_test_cases_file (test_cases : test_case list) (prop_set : string list) =
  let contents =
    header_and_imports
<<<<<<< HEAD
    @ generate_bidi_properties_type prop_set
=======
    @ generate_bidi_class_type prop_set
>>>>>>> 00a3550 (updated all test files)
    @ test_case_type
    @ generate_test_cases_definition test_cases
  in
  write_lines generated_filename contents
;;

(*
 * Running the script 
 *)

(* Slice of the BidiTest.txt file for testing *)
let testcase_slice : string list =
  let contents_arr = Array.of_list @@ read_lines input_filename in
  let slice = Array.sub contents_arr 102 30 in
  (* let slice = Array.sub contents_arr 1012 32 in *)
  Array.to_list slice
;;

(* Main function to run the script *)
let () =
  (* Testing on slice *)
  (* let test_cases, props = parse_test_cases testcase_slice in
     List.iter print_test_case test_cases;
     List.iter print_endline props;
     generate_test_cases_file test_cases props *)

  (* Generate test cases from the entire input file *)
  let contents = read_lines input_filename in
  let test_cases, props = parse_test_cases contents in
  generate_test_cases_file test_cases props
;;
