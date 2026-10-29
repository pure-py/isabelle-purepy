# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

Mechanisation of the PurePy specification in Isabelle/HOL.

## Building

Install the [Isabelle](https://isabelle.in.tum.de/) release named in `.isabelle-version` and
[uv](https://docs.astral.sh/uv/). Then check the proofs and generate the type checker:

```bash
make build
```

The generated Python is written to `python/generated/`, which is committed, so that the type checker can be
used without Isabelle; commit it with the change to the theories. The build fails unless the code generator
targets the Python version in `.python-version`, and `make check-generated`, run by CI, fails if the
committed code differs from the build output. With the specification repository checked out alongside this one,
`make check-tests` runs its conformance suite under the generated code of this checkout, before committing;
`SPEC=<path>` names another checkout.

To browse the theories with the prover running, open the session directory in the bundled editor:

```bash
./vscode.sh
```

## Theories

<!-- theories -->
| File                 | Content                                                                        |
|----------------------|--------------------------------------------------------------------------------|
| `Util.thy`           | Shared utilities                                                               |
| `Floats.thy`         | Floats as an abstract type with uninterpreted arithmetic                       |
| `Strings.thy`        | Strings and identifiers as lists of Unicode code points                        |
| `Positions.thy`      | Syntax nodes with their positions in the source                                |
| `Syntax.thy`         | Abstract syntax and syntactic analyses                                         |
| `Semantics.thy`      | Values, results and evaluation judgements                                      |
| `Correctness.thy`    | Inversion lemmas and determinism of evaluation                                 |
| `Contexts.thy`       | Context entries, class tables, name resolution, predefined modules             |
| `Reasons.thy`        | Reasons for ill-formedness                                                     |
| `Types.thy`          | Type resolution, substitution and class definitions                            |
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
