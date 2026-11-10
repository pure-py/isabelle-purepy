# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

This repository holds the Isabelle/HOL mechanisation of the PurePy specification and the `purepy` type checker
generated from the mechanisation.

## Building

Install the [Isabelle](https://isabelle.in.tum.de/) release named in `.isabelle-version` and
[uv](https://docs.astral.sh/uv/). Then check the proofs and generate the type checker:

```bash
make build
```

To browse the theories with the prover running, open the session directory in the bundled editor:

```bash
./vscode.sh
```

## Type checker and reference interpreter (`purepy`)

The `purepy` package in `src/purepy/` contains the generated type checker and reference interpreter, and the
code which runs them on source files.

Install the wheel attached to the latest [release](https://github.com/pure-py/isabelle-purepy/releases) as a
standalone command-line tool with `uv tool install <wheel URL>`. Then check a single module, or a whole program
from the entry module:

```bash
purepy --check --module path/to/module.py
purepy --check path/to/main.py
```

Without `--check`, `purepy` checks the program and, if it is well-formed, runs it by the reference interpreter,
with any further arguments as `sys.argv[1:]`:

```bash
purepy path/to/main.py arg1 arg2
```

An ill-formed program is rejected with the same message and exit status as `--check` gives. Otherwise the
program runs, printing what it prints, and `purepy` exits with:

- the program's own exit status, when the run ends as in Python;
- 4, when the run has undefined behaviour in PurePy;
- 6, when the interpreter gets stuck, which cannot happen for a well-formed program;
- 7, when the run nests deeper than `--fuel` allows (default 100000).

From a checkout, after `make build`, the same commands run with `uv run --locked python -m purepy`.

## Tests

After `make build`:

```bash
make check-conformance
```

The conformance suite comes from the pinned specification. The tests are run by Python unless another
interpreter is given, such as the generated reference interpreter:

```bash
uv run --locked ./test/check-conformance.sh "python -m purepy"
```

The evaluator tests in `test/evaluator/` cover what the conformance suite cannot reach. They run the generated
reference interpreter on syntax built directly, without the type checker: aborts which typing rules out, runs
to which no rule applies, and runs out of fuel.

```bash
uv run --locked ./test/evaluator/run.py
```

## Development

Synchronise the project environment and install the development dependencies:

```bash
uv sync --locked
```

Format the sources:

```bash
uv run --locked ruff format ./src/purepy ./test/check-conformance.py
```

After changing dependencies or metadata in `pyproject.toml`, run `uv lock` and commit `pyproject.toml` and
`uv.lock`.

## Release workflow

Run the `Release` GitHub Action manually. The version number of a release is that of the pinned
`purepy-conformance` release.

## Theories

<!-- theories -->
| File                                  | Content                                                                                                |
|---------------------------------------|--------------------------------------------------------------------------------------------------------|
| `Util.thy`                            | Shared utilities                                                                                       |
| `Floats.thy`                          | Floats as an abstract type, with its IEEE 754 interface uninterpreted                                  |
| `Strings.thy`                         | Strings and identifiers as lists of Unicode code points                                                |
| `Positions.thy`                       | Syntax nodes with their positions in the source                                                        |
| `Syntax.thy`                          | Abstract syntax and syntactic analyses                                                                 |
| `Contexts.thy`                        | Context entries, class tables, name resolution, predefined modules, programs                           |
| `Reasons.thy`                         | Reasons for ill-formedness                                                                             |
| `Types.thy`                           | Type resolution, substitution, class definitions and well-formed class tables                          |
| `Values.thy`                          | Values, results and functions on values                                                                |
| `Semantics.thy`                       | Evaluation judgements                                                                                  |
| `Determinism.thy`                     | Inversion lemmas and determinism of evaluation                                                         |
| `Eval.thy`                            | Evaluation as a function with fuel, and its executable code equations                                  |
| `Correctness.thy`                     | Soundness and completeness of the evaluator against the evaluation judgements                          |
| `Subtyping.thy`                       | Subtyping and its transitivity, join and meet; element, subscript and attribute types                  |
| `Shapes.thy`                          | Heads and shapes for pattern matching; head and shape typing; shapes of a type                         |
| `Patterns.thy`                        | Pattern checking; matched and remaining types of patterns                                              |
| `Matching.thy`                        | Splitting of shapes; matching of patterns against shapes                                               |
| `Operators.thy`                       | Equality types and operator overloads                                                                  |
| `Typing.thy`                          | Static outcomes; typing of expressions, statements and type definitions                                |
| `Programs.thy`                        | Typing of imports, modules and programs                                                                |
| `Examples.thy`                        | Example evaluations                                                                                    |
| `python/Codegen.thy`                  | Operator resolution and subtyping in executable form; Python generation                                |
| `soundness/WellFormed.thy`            | Well-formedness and type variables of the types produced by operations on types and contexts           |
| `soundness/WellFormedExpressions.thy` | Well-formedness and type variables of the types synthesised for expressions and matched by patterns    |
| `soundness/WellFormedStatements.thy`  | Well-formedness and type variables of pattern bindings and of the contexts produced by statements      |
| `soundness/Extension.thy`             | Stability of the type checker under extension of the class table                                       |
| `soundness/ExtensionExpressions.thy`  | Stability of pattern checking, shape matching and expression typing under extension of the class table |
| `soundness/ExtensionStatements.thy`   | Stability of statement, definition and type definition checking under extension of the class table     |
| `soundness/ValueTyping.thy`           | Value and environment typing                                                                           |
| `soundness/ResultTyping.thy`          | Typing of evaluation results; canonical forms of values                                                |
| `soundness/Instances.thy`             | Instances of a class along its chain of base classes, and matching of type arguments                   |
| `soundness/Expressions.thy`           | Soundness of evaluation of expressions other than calls, subscripts, attributes and comprehensions     |
| `soundness/Attributes.thy`            | Soundness of evaluation of subscripts and attributes                                                   |
| `soundness/Comprehensions.thy`        | Soundness of evaluation of comprehensions                                                              |
| `soundness/Calls.thy`                 | Soundness of call evaluation                                                                           |
| `soundness/Match.thy`                 | Soundness of pattern matching and of dispatch over the cases of a match statement                      |
| `soundness/Statements.thy`            | Soundness of statement evaluation                                                                      |
| `soundness/WellFormedTopLevel.thy`    | Well-formedness of the class tables and contexts produced by type regions and modules                  |
| `soundness/ExtensionTopLevel.thy`     | Stability of module checking under extension of the class table; settled class tables                  |
| `soundness/TopLevel.thy`              | Soundness of top-level statement, module and program evaluation                                        |
| `soundness/Soundness.thy`             | Type soundness                                                                                         |
| `soundness/LoadsTermination.thy`      | Termination of the order of loading of a well-formed program                                           |
<!-- /theories -->
