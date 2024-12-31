# Unicode Bidirectional Proof Coq Project Runbook (Tests)

This section outlines the steps taken to run tests for the implemented Unicode Bidirectional rules. Since Coq does not have built-in `printf` functions, the workflow involves extracting Coq code to OCaml, writing the tests in OCaml, and running the tests using generated test cases.

## Generating Test Cases

- `generate_bidi_tests.ml` will be used to generate the test suite in Coq from `BidiTest.txt`, which can be found at https://raw.githubusercontent.com/unicode-org/icu/main/icu4c/source/test/testdata/BidiTest.txt.
- The generated test cases will be placed in a `.v` file (`generated_test_cases.v`), which will then be extracted to a `.ml` file (`generated_test_cases.ml`), which will then be used to run the tests against the implemented rules.

### Compile `unicode_bidi_class.ml` to import into tests file and rules file

```bash
cd Desktop/Research/Unicode/tests/coq/tests # change directory accordingly
ocamlc unicode_bidi_class.ml
```

### Generate .v file from the generator `generate_bidi_tests_coq.ml`

The following steps will generate `generated_test_cases.v`

```bash
wget https://raw.githubusercontent.com/unicode-org/icu/main/icu4c/source/test/testdata/BidiTest.txt # if have not downloaded the .txt file
ocamlc -o generate_bidi_tests generate_bidi_tests_coq.ml # compile
./generate_bidi_tests # run the script to generate the .v file
```

### Extract the generated test cases from Coq to Ocaml `generated_test_cases.ml`

Add to the end of the `generated_test_cases.v` file:

```coq
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inductive nat => int [ "0" "(fun x -> x + 1)" ].

Extraction "generated_test_cases.ml" Bidi_Class Test_Case test_cases.
```

This will generate the `generated_test_cases.ml` file.
To resolve the conflict between the 2 definitions of Bidi_Class, replace the `type Bidi_Class` at the beginning of the `.ml` file to 
```ocaml
open Unicode_bidi_class
```

### Compile `generated_test_cases.ml`
```bash
ulimit -a # check ulimit
ulimit -s unlimited # change stack size
ocamlc "generated_test_cases.ml"
ocamlopt "generated_test_cases.ml"
```

### Troubleshooting

If Ocaml version is not new enough for the `Inchannel` module, update Ocaml:

```bash
opam update
opam switch list-available
opam switch create 4.14.1
eval $(opam env) # set environment variables for the new switch
opam install core
opam list | grep core # verify installation
```

## Generating Unicode Bidi Rules in Ocaml

In the `unicode-bidi-rules.v` file, which contains only the definitions of `w` rules, extract the rule implementations from Coq to OCaml:

```coq
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction "unicode_bidi_rules.ml" rule_w1 rule_w2 rule_w12. (* add more rules if necessary *)
```
In the generated `unicode-bidi-rules.ml` file, replace the `type Bidi_Class` at the beginning of the `.ml` file to 
```ocaml
open Unicode_bidi_class
open Generated_test_cases (* import the test cases *)
```

## Running the tests using `unicode-bidi-rules_test.ml`, `unicode-bidi-rules_extracted.ml` and `generated_test_cases.ml`
After adding the test functions in `unicode-bidi-rules.ml`, run the following code:


```bash
ocamlc -c generated_test_cases.cmo unicode_bidi_rules_extracted.cmo unicode_bidi_rules_test.ml
ocamlc -o run_tests generated_test_cases.cmo unicode_bidi_rules_extracted.cmo unicode_bidi_rules_test.cmo
./run_tests
```

You should see output like:

```bash
Failed X of Y tests
Failed A of B w1 comparisons
Failed C of D w2 comparisons
...
Failed M of N n2 comparisons
```

Failed X of Y tests: Summarizes how many test scenarios failed overall (including all steps).
Failed A of B w1 comparisons: Summarizes how many times the extracted rule_w1 code diverged from the reference’s W1 result.
Similarly for W2, W3, W4, W5, W6, W7, N1, N2.
If everything matches perfectly, you should see zero failures for both the overall tests and the individual rule comparisons.
