# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

Mechanisation of the PurePy specification in Isabelle/HOL.

## Building

Install the [Isabelle](https://isabelle.in.tum.de/) release named in `.isabelle-version` and
[uv](https://docs.astral.sh/uv/). Then check the proofs:

```bash
make build
```

To browse the theories with the prover running, open the session directory in the bundled editor:

```bash
./vscode.sh
```

## Theories

| File                   | Content                                                                 |
|------------------------|-------------------------------------------------------------------------|
| `Util.thy`             | Shared utilities                                                        |
| `Syntax.thy`           | Abstract syntax and its analyses                                        |
| `Semantics.thy`        | Values, results and evaluation judgements                               |
| `Correctness.thy`      | Inversion lemmas and determinism of evaluation                          |
| `Typing.thy`           | Subtyping, contexts, static outcomes and typing                         |
| `Examples.thy`         | Example evaluations                                                     |
| `python/Codegen.thy`   | Operator resolution and subtyping in executable form; Python generation |
| `python/smoke_test.py` | Test of generated type checker                                          |
