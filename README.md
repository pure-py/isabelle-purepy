# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

Mechanisation of the PurePy specification in Isabelle/HOL.

## Building

Install the [Isabelle](https://isabelle.in.tum.de/) release named in `.isabelle-version` and
[uv](https://docs.astral.sh/uv/). Then check the proofs:

```bash
make build
```

The target checks that `isabelle` is that release; if it is not on `PATH`, pass it explicitly with
`make build ISABELLE=<path to isabelle>`.

The build also generates Python from the executable definitions, under `python/python_out`, with the
[Python code generator](https://github.com/pure-py/isabelle-python-codegen) at the commit named in
`.python-codegen-version`, fetched into `python/isabelle-python-codegen`. The build then runs the generated
type checker on small programs; this test will be deleted once the PurePy conformance suite is run on the
generated code.

To browse the theories with the prover running, open the session directory in the bundled editor, after a
build has fetched the generator:

```bash
isabelle vscode -d . -d python/isabelle-python-codegen .
```

## Theories

| File                   | Content                                                                 |
|------------------------|-------------------------------------------------------------------------|
| `Syntax.thy`           | Abstract syntax                                                         |
| `Semantics.thy`        | Values, results, auxiliary functions and evaluation judgements          |
| `Correctness.thy`      | Inversion lemmas and determinism of evaluation                          |
| `Typing.thy`           | Subtyping, contexts, static outcomes and typing                         |
| `Examples.thy`         | Example evaluations                                                     |
| `python/Codegen.thy`   | Operator resolution and subtyping in executable form; Python generation |
| `python/smoke_test.py` | Test of generated type checker                                          |
