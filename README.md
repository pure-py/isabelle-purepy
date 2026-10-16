# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

Mechanisation of the PurePy specification in Isabelle/HOL, covering a fragment of the syntax and
operational semantics: literals, variables, operators, conditionals, lists, tuples, lambdas and calls, and
the statements for assignment, assertion, return, conditionals, sequencing and mutual definition regions.
Evaluation produces a result, either a value or an abort with a termination kind, following the
specification's treatment of runtime errors.

## Building

Install [Isabelle2025-2](https://isabelle.in.tum.de/). On macOS, either download
`Isabelle2025-2_macos.tar.gz` and move `Isabelle2025-2.app` to `/Applications`, or run
`brew install --cask isabelle`. Put the `isabelle` executable on `PATH`:

```bash
export PATH="/Applications/Isabelle2025-2.app/bin:$PATH"
```

Then check the proofs:

```bash
make build
```

`make document` also builds the session document, which needs LaTeX. If `isabelle` is not on `PATH`,
pass it explicitly: `make build ISABELLE=/Applications/Isabelle2025-2.app/bin/isabelle`.

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
