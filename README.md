# unicode-bidirectional-proof-coq
This project contains a **Coq** and **OCaml**-based implementation of the Unicode **Bidirectional Algorithm** (UBA). The repository includes:

1. **Rules Implemention (weak) and Proofs**: A series of Coq definitions and functions for each step of the bidirectional algorithm (W1–W7, N1–N2, etc.), which are then extracted to OCaml. Combinations of the individual rules and proofs of their correctness.
2. **Reference Implementation**: An OCaml reference approach translated from Java (https://www.unicode.org/Public/PROGRAMS/BidiReferenceJava/BidiReference.java).
3. **Testing Framework**: A generated test suite from https://raw.githubusercontent.com/unicode-org/icu/main/icu4c/source/test/testdata/BidiTest.txt, which verifies the reference implementation. Test functions that execute each test input, apply the reference logic, apply the extracted rules, and compare the results.

## Project Overview
- **`unicode_bidi_proof_v4.v`**  
  Contains the latest original functions of all the W and N rules, their combination rules and the correctness proofs in Coq.
  
- **`unicode_bidi_rules_test.ml`**  
  Contains the main `run_tests` function that:
  1. Iterates over generated test cases.
  2. Applies the reference implementation via `run_algorithm`.
  3. Compares the final levels and extracted rule outcomes (W1–W7, N1–N2) to ensure correctness.
  4. Prints pass/fail information, including how many comparisons failed or succeeded.

- **`unicode_bidi_rules_extracted.ml`**  
  Contains Coq-extracted weak rules: `rule_w1`, `rule_w2`, `rule_w3`, `rule_w4`, `rule_w5`, `rule_w6`, `rule_w7`, plus neutral rules `rule_n1` and `rule_n2`.

- **`generated_test_cases.ml`**  
  Contains test-case data generated from BidiTest.txt to OCaml using the generator `generate_test_cases.ml`.
