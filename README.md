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

The build also generates Python from the executable definitions, under `python/python_out`, with the
[Python code generator](https://github.com/pure-py/isabelle-python-codegen) at the commit named in
`.python-codegen-version`, which the build fetches into `python/isabelle-python-codegen`. It then runs the
generated interpreter and type checker on small programs, with Python provided by
[uv](https://docs.astral.sh/uv/). This test will be deleted once the PurePy conformance suite is run on
the generated code.

To browse the theories with the prover running, open the session directory in the bundled editor:
`isabelle vscode .`

## Theories

| File                   | Content                                                        |
|------------------------|----------------------------------------------------------------|
| `Syntax.thy`           | Abstract syntax                                                |
| `Semantics.thy`        | Values, results, auxiliary functions and evaluation judgements |
| `Correctness.thy`      | Inversion lemmas and determinism of evaluation                 |
| `Typing.thy`           | Subtyping, contexts, static outcomes and typing                |
| `Executable.thy`       | Code equations and executable evaluation                       |
| `Examples.thy`         | Example evaluations                                            |
| `python/Codegen.thy`   | Python generation                                              |
| `python/smoke_test.py` | Temporary test of the generated interpreter and type checker   |
