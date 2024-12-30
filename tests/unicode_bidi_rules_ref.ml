(* unicode_bidi_rules_ref.ml *)

open Generated_test_cases
open Unicode_bidi_class

(* ********** *)

let implicit_embedding_level : int option = None

type bidi_reference = {
    mutable paragraph_embedding_level: int option;
    initial_types: Unicode_bidi_class.bidi_class array;
    mutable text_length: int;
    mutable result_types: Unicode_bidi_class.bidi_class array;
    mutable result_levels: int option array;
    mutable matching_pdi: int array;
    mutable matching_isolate_initiator: int array;
    pair_types: int array;
    pair_values: int array;
  }

(* Converts a list of bidi classes to a string for printing *)
let string_of_bidi_class_list lst =
  String.concat " " (List.map (function
                         | L -> "L" | R -> "R" | AL -> "AL" | EN -> "EN" | ES -> "ES" | ET -> "ET"
                         | AN -> "AN" | CS -> "CS" | NSM -> "NSM" | BN -> "BN" | B -> "B" | S -> "S"
                         | WS -> "WS" | ON -> "ON" | LRE -> "LRE" | RLE -> "RLE" | LRO -> "LRO"
                         | RLO -> "RLO" | PDF -> "PDF" | LRI -> "LRI" | RLI -> "RLI" | FSI -> "FSI"
                         | PDI -> "PDI") lst)

(* ********** *)

(* rule P1 - no tests *)

(* rules P2 & P3 *)
let determine_paragraph_level
      (result_types: bidi_class array)
      (matching_pdi: int array)
      (start_index: int)
      (end_index: int) : int option =
  let rec find_strong_type i =
    if i < end_index then
      match result_types.(i) with
      | L -> Some 0
      | AL | R -> Some 1
      | FSI | LRI | RLI -> find_strong_type matching_pdi.(i)  (* skip isolates *)
      | _ -> find_strong_type (i + 1)
    else None
  in
  match find_strong_type start_index with
  | Some level -> Some level
  | None -> None  (* Default to None if no strong type is found *)

(* ********** *)

(* rule BD9 *)

let determine_matching_isolates (bidi_ref: bidi_reference) : unit =
  for i = 0 to bidi_ref.text_length - 1 do (* Array.make -1 *)
    bidi_ref.matching_isolate_initiator.(i) <- -1
  done;
  for i = 0 to bidi_ref.text_length - 1 do
    bidi_ref.matching_pdi.(i) <- -1;
    match bidi_ref.result_types.(i) with
    | LRI | RLI | FSI ->
       let depth_counter = ref 1 in
       let rec find_matching_pdi j =
         if j < bidi_ref.text_length then
           match bidi_ref.result_types.(j) with
           | LRI | RLI | FSI -> incr depth_counter; find_matching_pdi (j + 1)
           | PDI ->
              decr depth_counter;
              if !depth_counter = 0 then (
                bidi_ref.matching_pdi.(i) <- j;
                bidi_ref.matching_isolate_initiator.(j) <- i
              ) else find_matching_pdi (j + 1)
           | _ -> find_matching_pdi (j + 1)
       in
       find_matching_pdi (i + 1);
       if bidi_ref.matching_pdi.(i) = -1 then
         bidi_ref.matching_pdi.(i) <- bidi_ref.text_length
    | _ -> ()
  done

(* ********** *)

(* rules x1-x8 *)

let max_depth = 125

type directional_status_stack = {
    mutable stack_counter: int;
    embedding_level_stack: int option array;
    override_status_stack: bidi_class array; (* directional_override_status *)
    isolate_status_stack: bool array; (* directional_isolate_status *)
  }

let init_stack (): directional_status_stack = {
    stack_counter = 0;
    embedding_level_stack = Array.make (max_depth + 1) None;
    override_status_stack = Array.make (max_depth + 1) ON;
    isolate_status_stack = Array.make (max_depth + 1) false;
  }

let empty_stack (stack: directional_status_stack): unit =
  stack.stack_counter <- 0

let push_stack (stack: directional_status_stack) (level: int option) (override_status: bidi_class) (isolate_status: bool): unit =
  stack.embedding_level_stack.(stack.stack_counter) <- level;
  stack.override_status_stack.(stack.stack_counter) <- override_status;
  stack.isolate_status_stack.(stack.stack_counter) <- isolate_status;
  stack.stack_counter <- stack.stack_counter + 1

let pop_stack (stack: directional_status_stack): unit =
  stack.stack_counter <- stack.stack_counter - 1

let depth_stack (stack: directional_status_stack): int =
  stack.stack_counter

let last_embedding_level (stack: directional_status_stack): int option =
  stack.embedding_level_stack.(stack.stack_counter - 1)

let last_override_status (stack: directional_status_stack): bidi_class =
  stack.override_status_stack.(stack.stack_counter - 1)

let last_isolate_status (stack: directional_status_stack): bool =
  stack.isolate_status_stack.(stack.stack_counter - 1)

let determine_explicit_embedding_levels
      (text_length: int)
      (result_types: bidi_class array)
      (result_levels: int option array)
      (paragraph_embedding_level: int option)
      (determine_paragraph_level: bidi_class array -> int array -> int -> int -> int option)
      (matching_pdi: int array): unit =

  (* Initialize necessary variables *)
  let stack = init_stack () in
  let overflow_isolate_count = ref 0 in
  let overflow_embedding_count = ref 0 in
  let valid_isolate_count = ref 0 in

  (* rule X1 *)
  empty_stack stack;
  push_stack stack paragraph_embedding_level ON false;
  overflow_isolate_count := 0;
  overflow_embedding_count := 0;
  valid_isolate_count := 0;

  for i = 0 to text_length - 1 do
    let t = result_types.(i) in
    match t with
    | RLE | LRE | RLO | LRO | RLI | LRI | FSI ->
       let is_isolate = (t = RLI || t = LRI || t = FSI) in
       let is_rtl = (t = RLE || t = RLO || t = RLI) in
       let is_rtl = if t = FSI then
                      (determine_paragraph_level result_types matching_pdi (i + 1) matching_pdi.(i) = Some 1)
                    else is_rtl in

       if is_isolate then begin
           result_levels.(i) <- last_embedding_level stack;
           if last_override_status stack <> ON then
             result_types.(i) <- last_override_status stack
         end;

       let last_level = last_embedding_level stack in
       let new_level = match last_level with
         | Some lvl ->
            if is_rtl then
              Some ((lvl + 1) lor 1)  (* least greater odd *)
            else
              Some ((lvl + 2) land lnot 1)  (* least greater even *)
         | None -> None
       in

       if (match new_level with Some lvl -> lvl <= max_depth | None -> false)
          && !overflow_isolate_count = 0 && !overflow_embedding_count = 0 then begin
           if is_isolate then incr valid_isolate_count;
           push_stack stack new_level (if t = LRO then L else if t = RLO then R else ON) is_isolate;
           if not is_isolate then result_levels.(i) <- new_level
         end else begin
           if is_isolate then incr overflow_isolate_count
           else if !overflow_isolate_count = 0 then incr overflow_embedding_count
         end

    | PDI ->
       if !overflow_isolate_count > 0 then decr overflow_isolate_count
       else if !valid_isolate_count = 0 then ()
       else begin
           overflow_embedding_count := 0;
           while not (last_isolate_status stack) do
             pop_stack stack
           done;
           pop_stack stack;
           decr valid_isolate_count
         end;
       result_levels.(i) <- last_embedding_level stack

    | PDF ->
       if !overflow_isolate_count > 0 then ()
       else if !overflow_embedding_count > 0 then decr overflow_embedding_count
       else if not (last_isolate_status stack) && depth_stack stack >= 2 then pop_stack stack

    | B ->
       result_levels.(i) <- paragraph_embedding_level

    | _ ->
       result_levels.(i) <- last_embedding_level stack;
       if last_override_status stack <> ON then
         result_types.(i) <- last_override_status stack
  done

(* rule X9 *)

type isolating_run_sequence = {
    indexes: int array;
    mutable types: bidi_class array; 
    mutable resolved_levels: int option array;
    length: int;              
    level: int option;              
    sos: bidi_class; (* L or R *)
    eos: bidi_class; (* L or R *)
  }

(* Checks if a character is removed by Rule X9 *)
let is_removed_by_x9 (bidi_type: bidi_class) : bool =
  match bidi_type with
  | RLE | LRE | RLO | LRO | PDF | BN -> true
  | _ -> false

(* Determines type based on level, for sos/eos determination *)
let type_for_level (level: int option) : bidi_class =
  match level with
  | Some lvl -> if lvl mod 2 = 0 then L else R
  | None -> L  (* Default to L if level is None *)

(* ********** *)

(* print out the level runs - single array w no elem *)

let determine_level_runs 
      (initial_types: bidi_class array)
      (result_levels: int option array)
      (text_length: int) : int array array =

  (* Temporary array to hold the current run of indexes *)
  let temporary_run = Array.make text_length 0 in
  (* Array to hold all level runs *)
  let all_runs = Array.make text_length [||] in
  let num_runs = ref 0 in

  let current_level = ref None in
  let run_length = ref 0 in

  for i = 0 to text_length - 1 do
    if not (is_removed_by_x9 initial_types.(i)) then (* LRE *)
      (* Start a new run if the level changes *)
      if result_levels.(i) <> !current_level then begin
          (* Wrap up the previous run if it exists *)
          (match !current_level with
           | Some _ when !run_length > 0 ->
              let run = Array.sub temporary_run 0 !run_length in
              all_runs.(!num_runs) <- run;
              incr num_runs
           | _ -> ());
          (* Start a new run *)
          current_level := result_levels.(i);
          run_length := 0
        end;
    temporary_run.(!run_length) <- i;
    incr run_length
  done;

  (* Wrap up the final run if there is one *)
  if !run_length <> 0 then begin
      let run = Array.sub temporary_run 0 !run_length in
      all_runs.(!num_runs) <- run;
      incr num_runs
    end;

  (* Return a copy of the array with only the filled level runs *)
  Array.sub all_runs 0 !num_runs


(* ********** *)

(* rule BD13 *)

let determine_isolating_run_sequences
      (text_length: int)
      (initial_types: bidi_class array)
      (matching_isolate_initiator: int array)
      (matching_pdi: int array)
      (determine_level_runs: unit -> int array array)
      (init_isolating_run_sequence: int array -> isolating_run_sequence) : isolating_run_sequence array =
  
  let level_runs = determine_level_runs () in
  let num_runs = Array.length level_runs in
  
  (* Compute the run each character belongs to *)
  let run_for_character = Array.make text_length (-1) in
  Array.iteri (fun run_number run ->
      Array.iter (fun character_index ->
          run_for_character.(character_index) <- run_number
        ) run
    ) level_runs;

  let sequences = Array.make num_runs  {
                      indexes = [||];
                      types = [||];
                      resolved_levels = [||];
                      length = -1;
                      level = None;
                      sos = L; (* default to L *)
                      eos = L; (* default to L *)
                    } in

  let num_sequences = ref 0 in
  let current_run_sequence = Array.make text_length 0 in
  
  for i = 0 to num_runs - 1 do
    let first_character = level_runs.(i).(0) in
    if initial_types.(first_character) <> PDI || matching_isolate_initiator.(first_character) = -1 then
      let current_run_sequence_length = ref 0 in
      let rec collect_runs run =
        Array.blit level_runs.(run) 0 current_run_sequence !current_run_sequence_length (Array.length level_runs.(run));
        current_run_sequence_length := !current_run_sequence_length + Array.length level_runs.(run);

        let last_character = current_run_sequence.(!current_run_sequence_length - 1) in
        let last_type = initial_types.(last_character) in
        if (last_type = LRI || last_type = RLI || last_type = FSI) &&
             matching_pdi.(last_character) <> text_length then
          collect_runs run_for_character.(matching_pdi.(last_character))
      in
      collect_runs i;

      sequences.(!num_sequences) <- init_isolating_run_sequence (Array.sub current_run_sequence 0 !current_run_sequence_length);
      incr num_sequences
  done;

  Array.sub sequences 0 !num_sequences


(* ********** *)

(* rules w1-w7 *)

(* Find the limit of a run consisting only of specific types starting at index *)
let find_run_limit
      (types: bidi_class array)
      (index: int)
      (limit: int)
      (valid_set: bidi_class list) : int =
  let rec loop idx =
    if idx < limit && List.mem types.(idx) valid_set
    then loop (idx + 1)
    else idx
  in loop index

(* Set types from start up to (but not including) limit to new_type *)
let set_types (types: bidi_class array) (start: int) (limit: int) (new_type: bidi_class) : unit =
  for i = start to limit - 1 do
    types.(i) <- new_type
  done

(* Validation function to assert that all values in types are in the provided set *)
let assert_only (types: bidi_class array) (length: int) (valid_set: bidi_class list) : unit =
  for i = 0 to length - 1 do
    let t = types.(i) in
    if not (List.mem t valid_set) then
      let error_msg = Printf.sprintf "invalid bidi code present in assertOnly at position %d\n types: %s\n valid_set: %s\n" i (string_of_bidi_class_list (Array.to_list types)) (string_of_bidi_class_list valid_set) in
      failwith error_msg
  done

let resolve_weak_types (sequence: isolating_run_sequence) : unit =
  
  let types = sequence.types in
  let length = sequence.length in

  assert_only types length [L; R; AL; EN; ES; ET; AN; CS; B; S; WS; ON; NSM; LRI; RLI; FSI; PDI];

  (* Rule W1 *)
  let preceding_character_type = ref sequence.sos in
  for i = 0 to length - 1 do
    match types.(i) with
    | NSM -> types.(i) <- !preceding_character_type
    | LRI | RLI | FSI | PDI -> preceding_character_type := ON
    | t -> preceding_character_type := t
  done;

  (* Rule W2 *)
  for i = 0 to length - 1 do
    if types.(i) = EN then
      let rec find_previous_strong j =
        if j >= 0 then
          match types.(j) with
          | L | R -> ()
          | AL -> types.(i) <- AN
          | _ -> find_previous_strong (j - 1)
      in
      find_previous_strong (i - 1)
  done;

  (* Rule W3 *)
  for i = 0 to length - 1 do
    if types.(i) = AL then types.(i) <- R
  done;

  (* Rule W4 *)
  for i = 1 to length - 2 do
    if types.(i) = ES || types.(i) = CS then
      let prev_type = types.(i - 1) in
      let succ_type = types.(i + 1) in
      if prev_type = EN && succ_type = EN then
        types.(i) <- EN
      else if types.(i) = CS && prev_type = AN && succ_type = AN then
        types.(i) <- AN
  done;

  (* Rule W5 *)
  let i = ref 0 in
  while !i < length do
    if types.(!i) = ET then
      let run_start = !i in
      let run_limit = find_run_limit types run_start length [ET] in
      let t0 = if run_start = 0
               then sequence.sos
               else types.(run_start - 1) in
      let surrounding_type = if t0 = EN
                             then t0
                             else if run_limit == length
                             then sequence.eos
                             else types.(run_limit) in
      if surrounding_type = EN then set_types types run_start run_limit EN;
      i := run_limit
      else
        incr i
  done;

  (* Rule W6 *)
  for i = 0 to length - 1 do
    if types.(i) = ES || types.(i) = ET || types.(i) = CS then
      types.(i) <- ON
  done;

  (* Rule W7 *)
  for i = 0 to length - 1 do
    if types.(i) = EN then
      let prev_strong_type = ref sequence.sos in
      let rec find_previous_strong j =
        if j >= 0 then
          match types.(j) with
          | L | R -> prev_strong_type := types.(j)
          | _ -> find_previous_strong (j - 1)
      in
      find_previous_strong (i - 1);
      if !prev_strong_type = L then types.(i) <- L
  done

(* ********** *)

(* rule n0 : no tests *)

(* rules n1-n2 *)

let resolve_neutral_types (sequence: isolating_run_sequence) : unit =
  let types = sequence.types in
  let length = sequence.length in

  (* Ensure only allowed types are in `types` *)
  assert_only types length [L; R; EN; AN; B; S; WS; ON; RLI; LRI; FSI; PDI];

  let i = ref 0 in
  while !i < length do
    match types.(!i) with
    | WS | ON | B | S | RLI | LRI | FSI | PDI ->
       (* Handle neutrals *)
       let run_start = !i in
       let run_limit = find_run_limit types run_start length [B; S; WS; ON; RLI; LRI; FSI; PDI] in
       (* Determine effective types at ends of run *)
       let leading_type =
         if run_start = 0 then sequence.sos
         else
           let prev_type = types.(run_start - 1) in
           if prev_type = AN || prev_type = EN then R else prev_type
       in
       let trailing_type =
         if run_limit = length then sequence.eos
         else
           let next_type = types.(run_limit) in
           if next_type = AN || next_type = EN then R else next_type
       in
       let resolved_type =
         if leading_type = trailing_type then leading_type
         else type_for_level sequence.level
       in
       set_types types run_start run_limit resolved_type;
       (* Skip over the run of neutrals *)
       i := run_limit
    | _ ->
       (* For all other types, move to the next index *)
       incr i
  done


(* ********** *)

(* rules I1-I2 *)

let resolve_implicit_levels (sequence: isolating_run_sequence) : unit =
  let types = sequence.types in
  let length = sequence.length in
  let level = sequence.level in

  assert_only types length [L; R; EN; AN];

  (* Initialize resolved levels to the base level *)
  let resolved_levels = Array.make length level in

  begin
    match level with
    | Some lvl ->
       if lvl land 1 = 0 then
         (* Even level (Rule I1) *)
         for i = 0 to length - 1 do
           match types.(i) with
           | L -> ()  (* No change *)
           | R -> resolved_levels.(i) <- Some (lvl + 1)
           | AN | EN -> resolved_levels.(i) <- Some (lvl + 2)
           | _ -> ()
         done
       else
         (* Odd level (Rule I2) *)
         for i = 0 to length - 1 do
           match types.(i) with
           | R -> ()  (* No change *)
           | L | AN | EN -> resolved_levels.(i) <- Some (lvl + 1)
           | _ -> ()
         done
    | None -> ()
  end;

  (* Assign the resolved levels to the sequence *)
  sequence.resolved_levels <- resolved_levels


(* ********** *)

(* Applies the levels and types resolved in rules W1-I2 to the result levels and types *)
let apply_levels_and_types
      (sequence: isolating_run_sequence)
      (result_types: bidi_class array)
      (result_levels: int option array) : unit =
  let indexes = sequence.indexes in
  let types = sequence.types in
  let resolved_levels = sequence.resolved_levels in

  for i = 0 to sequence.length - 1 do
    let original_index = indexes.(i) in
    result_types.(original_index) <- types.(i);
    result_levels.(original_index) <- resolved_levels.(i)
  done


(* ********** *)

let assign_levels_to_characters_removed_by_x9
      (initial_types: bidi_class array)
      (result_types: bidi_class array)
      (result_levels: int option array)
      (paragraph_embedding_level: int option) : int =

  Array.iteri (fun i t ->
      match t with
      | LRE | RLE | LRO | RLO | PDF | BN ->
         result_types.(i) <- t;
         result_levels.(i) <- None
      | _ -> ()
    ) initial_types;

  (* Propagate level information forward *)
  if result_levels.(0) = None then
    result_levels.(0) <- paragraph_embedding_level;

  for i = 1 to Array.length initial_types - 1 do
    if result_levels.(i) = None then
      result_levels.(i) <- result_levels.(i - 1)
  done;

  Array.length initial_types


let set_levels (levels: int option array) (start: int) (limit: int) (new_level: int option) : unit =
  for i = start to limit - 1 do
    levels.(i) <- new_level
  done


(* ********** *)

(* Converts a single bidi_class to a string *)
let string_of_bidi_class (bidi_class: bidi_class) : string =
  match bidi_class with
  | L -> "L" | R -> "R" | AL -> "AL" | EN -> "EN" | ES -> "ES" | ET -> "ET"
  | AN -> "AN" | CS -> "CS" | NSM -> "NSM" | BN -> "BN" | B -> "B" | S -> "S"
  | WS -> "WS" | ON -> "ON" | LRE -> "LRE" | RLE -> "RLE" | LRO -> "LRO"
  | RLO -> "RLO" | PDF -> "PDF" | LRI -> "LRI" | RLI -> "RLI" | FSI -> "FSI"
  | PDI -> "PDI"

let run_algorithm
      (bidi_ref: bidi_reference)
      (determine_paragraph_level: bidi_class array -> int array -> int -> int -> int option)
      (set_levels: int option array -> int -> int -> int option -> unit)
      (determine_explicit_embedding_levels)
      (determine_isolating_run_sequences)
      (assign_levels_to_characters_removed_by_x9)
      (resolve_weak_types: isolating_run_sequence -> unit)
      (resolve_neutral_types: isolating_run_sequence -> unit)
      (resolve_implicit_levels: isolating_run_sequence -> unit)
      (apply_levels_and_types: isolating_run_sequence -> bidi_class array -> int option array -> unit) : unit =

  (* Set text length and initialize result types *)
  let text_length = Array.length bidi_ref.initial_types in
  bidi_ref.result_types <- Array.copy bidi_ref.initial_types;

  (* Preprocessing to find matching isolates *)
  determine_matching_isolates bidi_ref;

  (* Rules P2-P3 *)
  if bidi_ref.paragraph_embedding_level = None then
    bidi_ref.paragraph_embedding_level <- determine_paragraph_level
                                            bidi_ref.result_types bidi_ref.matching_pdi 0 text_length;

  (* Initialize result levels to the paragraph embedding level *)
  bidi_ref.result_levels <- Array.make text_length bidi_ref.paragraph_embedding_level;
  set_levels bidi_ref.result_levels 0 text_length bidi_ref.paragraph_embedding_level;

  (* Rules X1-X8 *)
  determine_explicit_embedding_levels
    text_length
    bidi_ref.result_types
    bidi_ref.result_levels
    bidi_ref.paragraph_embedding_level
    determine_paragraph_level  (* Pass the function directly *)
    bidi_ref.matching_pdi;

  (* Assign levels to characters removed by Rule X9 *)
  ignore (assign_levels_to_characters_removed_by_x9
            bidi_ref.initial_types bidi_ref.result_types bidi_ref.result_levels bidi_ref.paragraph_embedding_level);

  (* Define init_isolating_run_sequence inside run_algorithm *)
  let init_isolating_run_sequence (input_indexes: int array) : isolating_run_sequence =
    let indexes = input_indexes in

    (* Filter out indexes corresponding to characters removed by X9 *)
    let filtered_indexes = Array.of_list (
                               Array.to_list indexes
                               |> List.filter (fun idx -> not (is_removed_by_x9 bidi_ref.result_types.(idx)))
                             ) in

    let length = Array.length filtered_indexes in

    (* Handle empty sequence *)
    if length = 0 then
      {
        indexes = [||];
        types = [||];
        resolved_levels = [||];
        length = 0;
        level = None; (* default to None *)
        sos = type_for_level bidi_ref.paragraph_embedding_level;
        eos = type_for_level bidi_ref.paragraph_embedding_level;
      }
    else
      let types = Array.init length (fun i -> bidi_ref.result_types.(filtered_indexes.(i))) in
      let level = bidi_ref.result_levels.(filtered_indexes.(0)) in

      (* Determine sos *)
      let rec find_prev_char prev_char =
        if prev_char >= 0 && is_removed_by_x9 bidi_ref.initial_types.(prev_char) then
          find_prev_char (prev_char - 1)
        else
          prev_char
      in
      let prev_char = find_prev_char (filtered_indexes.(0) - 1) in
      let prev_level =
        if prev_char >= 0 then bidi_ref.result_levels.(prev_char) else bidi_ref.paragraph_embedding_level
      in
      let max_prev_level = match prev_level, level with
        | Some l1, Some l2 -> Some (max l1 l2)
        | Some l, None | None, Some l -> Some l
        | None, None -> None
      in
      let sos = type_for_level max_prev_level in

      (* Determine eos *)
      let last_type = types.(length - 1) in
      let succ_level =
        if last_type = LRI || last_type = RLI || last_type = FSI then
          bidi_ref.paragraph_embedding_level
        else
          let rec find_limit limit =
            if limit < bidi_ref.text_length && is_removed_by_x9 bidi_ref.initial_types.(limit) then
              find_limit (limit + 1)
            else
              limit
          in
          let limit = find_limit (filtered_indexes.(length - 1) + 1) in
          if limit < bidi_ref.text_length then bidi_ref.result_levels.(limit) else bidi_ref.paragraph_embedding_level
      in
      let max_succ_level = match succ_level, level with
        | Some l1, Some l2 -> Some (max l1 l2)
        | Some l, None | None, Some l -> Some l
        | None, None -> None
      in
      let eos = type_for_level max_succ_level in

      (* Construct the isolating_run_sequence *)
      {
        indexes = filtered_indexes;
        types = types;
        resolved_levels = Array.make length level;
        length = length;
        level = level;
        sos = sos;
        eos = eos;
      }
  in

  (* Rule X10 *)
  let sequences = determine_isolating_run_sequences
                    text_length
                    bidi_ref.result_types
                    bidi_ref.matching_isolate_initiator
                    bidi_ref.matching_pdi
                    (fun () -> determine_level_runs bidi_ref.initial_types bidi_ref.result_levels text_length)
                    init_isolating_run_sequence
  in

  (* Apply rules to each sequence *)
  Array.iter (fun sequence ->
      resolve_weak_types sequence;
      resolve_neutral_types sequence;
      resolve_implicit_levels sequence;
      apply_levels_and_types sequence bidi_ref.result_types bidi_ref.result_levels) sequences

(* ********** *)

(* Converts a list of optional integers to a string for printing *)
let string_of_levels lst =
  String.concat " " (List.map (function None -> "x" | Some n -> string_of_int n) lst)

let string_of_int_list lst =
  String.concat " " (List.map (function Some n -> string_of_int n | None -> "x") lst)

let run_tests test_cases =
  let total_tests = ref 0 in
  let failed_tests = ref 0 in
  List.iteri (fun test_number test_case ->
      List.iteri (fun data_index (input, bitset) ->
          let expected_levels = test_case.levels in

          (* Determine paragraph levels from bitset *)
          let paragraph_levels =
            match bitset with
            | 1 -> [None]  (* Auto-LTR *)
            | 2 -> [Some 0]  (* LTR *)
            | 3 -> [None; Some 0]  (* Auto-LTR and LTR *)
            | 4 -> [Some 1]  (* RTL *)
            | 5 -> [None; Some 1]  (* Auto-LTR and RTL *)
            | 6 -> [Some 0; Some 1]  (* LTR and RTL *)
            | 7 -> [None; Some 0; Some 1]  (* Auto-LTR, LTR, and RTL *)
            | _ -> []
          in

          (* Iterate over each paragraph level *)
          List.iter (fun paragraph_level ->
              incr total_tests;
              let success = ref true in
              (* Set up the bidi_reference *)
              let text_length = List.length input in
              let bidi_ref = {
                  paragraph_embedding_level = paragraph_level;
                  initial_types = Array.of_list input;
                  text_length = text_length;
                  result_types = [||];  (* Initialized in run_algorithm *)
                  result_levels = [||];  (* Initialized in run_algorithm *)
                  matching_pdi = Array.make text_length (-1);
                  matching_isolate_initiator = Array.make text_length (-1);
                  pair_types = [||];  (* Not used here *)
                  pair_values = [||];  (* Not used here *)
                } in

              (* Run the algorithm *)
              try
                run_algorithm bidi_ref
                  determine_paragraph_level set_levels
                  determine_explicit_embedding_levels
                  determine_isolating_run_sequences
                  assign_levels_to_characters_removed_by_x9
                  resolve_weak_types resolve_neutral_types
                  resolve_implicit_levels apply_levels_and_types;
              with e ->
                    success := false;
                    Printf.printf "Exception during run_algorithm: %s\n" (Printexc.to_string e);
                    flush stdout;

                    (* Compare the levels *)
                    let actual_levels = Array.to_list bidi_ref.result_levels in

                    (* Adjust the expected levels and actual levels to the input length *)
                    let expected_levels_adjusted =
                      if List.length expected_levels = List.length input then expected_levels
                      else List.init (List.length input) (fun _ -> None)
                    in

                    if List.length expected_levels_adjusted <> List.length actual_levels then begin
                        success := false;
                        Printf.printf "Failed test %d data entry %d, paragraph level %s: expected levels length %d, got %d\n"
                          (test_number + 1) (data_index + 1)
                          (match paragraph_level with None -> "Auto" | Some lvl -> string_of_int lvl)
                          (List.length expected_levels_adjusted) (List.length actual_levels);
                      end else begin
                        List.iteri (fun i expected_level ->
                            match expected_level, List.nth actual_levels i with
                            | None, _ -> ()  (* 'x', skip *)
                            | Some expected_level, Some actual_level ->
                               if actual_level <> expected_level then begin
                                   success := false;
                                   Printf.printf "Failed test %d data entry %d, paragraph level %s at position %d: expected level %d, got %d\n"
                                     (test_number + 1) (data_index + 1)
                                     (match paragraph_level with None -> "Auto" | Some lvl -> string_of_int lvl)
                                     i expected_level actual_level
                                 end
                            | Some expected_level, None ->
                               success := false;
                               Printf.printf "Failed test %d data entry %d, paragraph level %s at position %d: expected level %d, got None\n"
                                 (test_number + 1) (data_index + 1)
                                 (match paragraph_level with None -> "Auto" | Some lvl -> string_of_int lvl)
                                 i expected_level
                          ) expected_levels_adjusted;
                      end;

                    (* If failed, print detailed information *)
                    if not !success then begin
                        incr failed_tests;
                        Printf.printf "Input: %s\n" (string_of_bidi_class_list input);
                        Printf.printf "Expected levels: %s\n" (string_of_levels expected_levels_adjusted);
                        Printf.printf "Actual levels: %s\n" (string_of_int_list actual_levels);
                        Printf.printf "\n";
                        flush stdout;
                      end;

            ) paragraph_levels
        ) test_case.data
    ) test_cases;
  Printf.printf "Failed %d of %d tests\n" !failed_tests !total_tests;
  flush stdout

let () = run_tests test_cases

