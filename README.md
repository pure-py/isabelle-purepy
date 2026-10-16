# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

Mechanisation of the PurePy specification in Isabelle/HOL. The syntax follows the specification's grammar.
The operational semantics covers a fragment: literals, variables, operators, conditionals, lists, tuples,
lambdas and calls, and the statements for assignment, assertion, return, conditionals, sequencing and
mutual definition regions; floats are reals, so `nan` is not modelled. Evaluation produces a result, either a value or an abort
with a termination kind, following the specification's treatment of runtime errors.

## Building

Install the [Isabelle](https://isabelle.in.tum.de/) release named in `.isabelle-version`, and LaTeX,
which the session document needs; `make build` checks that the `isabelle` on `PATH` is that release. On
macOS, either download the release's `_macos.tar.gz` and move its `.app` to `/Applications`, or run
`brew install --cask isabelle`. Put the `isabelle` executable on `PATH`:

```bash
export PATH="/Applications/$(cat .isabelle-version).app/bin:$PATH"
```

Then check the proofs and build the session document, `output/document.pdf`:

```bash
make build
```

If `isabelle` is not on `PATH`, pass it explicitly: `make build ISABELLE=<path to isabelle>`.

To browse the theories with the prover running, open the session directory in the bundled editor:
`isabelle vscode .`

GitHub Actions runs `make build` on every push (`.github/workflows/build.yml`).

## File contents

| File              | Content                                                              |
|-------------------|----------------------------------------------------------------------|
| `Syntax.thy`      | Abstract syntax                                                      |
| `Semantics.thy`   | Values, results, auxiliary functions and evaluation judgements       |
| `Correctness.thy` | Inversion lemmas and determinism of evaluation                       |
| `Examples.thy`    | Example evaluations                                                  |
| `Eval.thy`        | Evaluation as a recursive function (placeholder)                     |
| `Extraction.thy`  | Code extraction (placeholder)                                        |
