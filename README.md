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

<!-- theories -->
| File                 | Content                                                                        |
|----------------------|--------------------------------------------------------------------------------|
| `Util.thy`           | Shared utilities                                                               |
| `Syntax.thy`         | Abstract syntax and its analyses                                               |
| `Contexts.thy`       | Context entries, class tables, name resolution, predefined modules, programs   |
| `Reasons.thy`        | Reasons for ill-formedness                                                     |
| `Types.thy`          | Type resolution, substitution and class definitions                            |
| `Semantics.thy`      | Values, results and evaluation judgements                                      |
| `Determinism.thy`    | Inversion lemmas and determinism of evaluation                                 |
| `Eval.thy`           | Evaluation as a function with fuel, and its executable code equations          |
| `Correctness.thy`    | Soundness and completeness of the evaluator against the evaluation judgements  |
| `Subtyping.thy`      | Subtyping, join and meet; element, subscript and attribute types               |
| `Shapes.thy`         | Heads and shapes for pattern matching; head and shape typing; shapes of a type |
| `Patterns.thy`       | Pattern checking; matched and remaining types of patterns                      |
| `Matching.thy`       | Splitting of shapes; matching of patterns against shapes                       |
| `Operators.thy`      | Equality types and operator overloads                                          |
| `Typing.thy`         | Static outcomes; typing of expressions, statements and type definitions        |
| `Programs.thy`       | Typing of imports, modules and programs                                        |
| `Examples.thy`       | Example evaluations                                                            |
| `python/Codegen.thy` | Operator resolution and subtyping in executable form; Python generation        |
<!-- /theories -->
