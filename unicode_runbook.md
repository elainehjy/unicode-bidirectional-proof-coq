# Unicode Bidirectional Proof Coq Project Runbook

## Steps to Get the Tests Running for the Implemented Rules

This section outlines the steps taken to run tests for the implemented Unicode Bidirectional rules. Since Coq does not have built-in `printf` functions, the workflow involves extracting Coq code to OCaml, writing the tests in OCaml, and running the tests using generated test cases.

### Generating Test Cases in OCaml

- `generate_bidi_tests_ocaml.ml` will be used to generate the test suite from `BidiTest.txt`.
- The generated test cases will be placed in an `.ml` file (`generated_test_cases.ml`).
- Initial error encountered: The `Inchannel` module cannot be used despite having installed the `Core` package.

### Solution: Update OCaml to a Newer Version

To resolve the error, update OCaml from version `4.12.0` to `4.14.1` which is more compatible with `Core`. Follow these steps:

1. **Update OPAM's Repository:**

```bash
opam update
```

2. **Check Available OCaml Versions:**

```bash
opam switch list-available
```

3. **Create a New OCaml Switch for Version 4.14.1:**

```bash
opam switch create 4.14.1
```

4. **Set Environment Variables for the New OCaml Switch:**

```bash
eval $(opam env)
```

5. **Install the Core Package:**

```bash
opam install core
```

6. **Verify Installation of the Core Package:**

```bash
opam list | grep core
```

### Generate the `generated_test_cases.ml` File

Follow the steps below to generate the test cases:

1. **Navigate to the Correct Directory:**

```bash
cd Desktop/Research/Unicode/tests/ocaml
```

2. **Download the `BidiTest.txt` File:**

Use the `wget` command to download the `BidiTest.txt` file from the Unicode project:

```bash
wget https://raw.githubusercontent.com/unicode-org/icu/main/icu4c/source/test/testdata/BidiTest.txt
```

3. **Compile the OCaml Script:**

```bash
ocamlc -o generate_bidi_tests generate_bidi_tests_ocaml.ml
```

4. **Run the Script to Generate the Test Cases:**

```bash
./generate_bidi_tests
```

### Extraction of Unicode Bidi Rules from Coq to OCaml

In the `unicode-bidi-rules.v` file, which contains only the definitions of `w` rules, extract the rule implementations from Coq to OCaml:

```coq
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction "unicode_bidi_rules.ml" rule_w1 rule_w2 rule_w12.
```

This will generate a `unicode_bidi_rules.ml` file containing the implementation of `rule_w1`, `rule_w2`, and `rule_w12` in OCaml. Eventually, all rules will be added (this example is for testing the first two rules).

#### Note: Two Versions of `bidi_class`

- There are two versions of the `bidi_class` type:
  1. In the **tests**
  2. In the **rules**

  The rules version excludes: `BN | LRE | LRO | RLE | RLO | PDF` because of rule X9.

---

### Import `generated_test_cases` into `unicode_bidi_rules`

#### For Coq:

1. **Compile `generated_test_cases.v`:**

   First, navigate to the correct directory:

   ```bash
   cd Desktop/Research/Unicode/tests/coq
   ```

   Then compile the file:

\```bash
coqc "generated_test_cases.v"
\```

2. **Use the `Require` statement in `unicode_bidi_rules.v`:**

After compiling, you can import the module using the following:

\```coq
Require generated_test_cases.
\```

3. **Alternatively: Use a Module:**

If you don’t want to use the `Require` statement, you can load the file directly using a module:

\```coq
Module generated_test_cases.
  Load "generated_test_cases.v".
End generated_test_cases.
\```

Note: This method has a longer waiting time when running the code.

---

#### For OCaml (Tentative):

1. **Wrap the `generated_test_cases.ml` content in a Module:**

Make sure the contents of `generated_test_cases.ml` are wrapped in a module for easy reference:

```ocaml
module Generated_test_cases = struct
  type bidi_class = ...

  let test_cases : test_case list = [
    ...
  ]
end
```

2. **Access `test_cases` and Other Definitions:**

Access `test_cases` and other definitions in `generated_test_cases.ml` by referencing them with the `Generated_test_cases` prefix:

```ocaml
let run_test () =
  let cases = Generated_test_cases.test_cases in
  ...
;;
```

---

### Step 3: Compile the OCaml Files Together

To compile both `generated_test_cases.ml` and `unicode_bidi_rules.ml` together, use the following command:

```bash
ocamlc -o bidi_test generated_test_cases.ml unicode_bidi_rules.ml
```

This will generate the final executable `bidi_test`.

