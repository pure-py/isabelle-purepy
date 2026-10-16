# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

Mechanisation of the PurePy specification in Isabelle/HOL.

## Building

Install the [Isabelle](https://isabelle.in.tum.de/) release named in `.isabelle-version`. Then check the
proofs:

```bash
make build
```

The target checks that `isabelle` is that release; if it is not on `PATH`, pass it explicitly with
`make build ISABELLE=<path to isabelle>`.

To browse the theories with the prover running, open the session directory in the bundled editor:
`isabelle vscode .`

## Theories

| File              | Content                                                        |
|-------------------|----------------------------------------------------------------|
| `Syntax.thy`      | Abstract syntax                                                |
| `Semantics.thy`   | Values, results, auxiliary functions and evaluation judgements |
| `Correctness.thy` | Inversion lemmas and determinism of evaluation                 |
| `Examples.thy`    | Example evaluations                                            |
