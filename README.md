# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

Mechanisation of the PurePy specification in Isabelle/HOL, the `purepy` type checker generated from it, and the
conformance suite of the specification.

## Building

Install the [Isabelle](https://isabelle.in.tum.de/) release named in `.isabelle-version` and
[uv](https://docs.astral.sh/uv/). Then check the proofs and generate the type checker:

```bash
make build
```

The generated Python is written to `src/purepy/generated/`, a subpackage of `purepy` which is not committed.
The build fails unless the code generator targets the Python version in `.python-version`.

To browse the theories with the prover running, open the session directory in the bundled editor:

```bash
./vscode.sh
```

## Type checker (`purepy`)

`src/purepy/` holds the `purepy` package: the parser, built on Python's `ast`, the translation of parsed
programs into the generated syntax and of the generated reasons into messages, module discovery and output
formatting, around the generated type checker. The conformance suite is shipped in the package.

Install the wheel attached to the latest [release](https://github.com/pure-py/isabelle-purepy/releases) as a
standalone command-line tool with `uv tool install <wheel URL>`. Then check a single module, or a whole program
from the entry module:

```bash
purepy --check --module path/to/module.py
purepy --check path/to/main.py
```

From a checkout, after `make build`, the same checks run with `uv run --locked python -m purepy --check`.

## Tests

After `make build`:

```bash
make check-tests
```

The target runs mypy and ruff over the front end, then the conformance suite under the generated type checker,
which must pass; `make wheel` also builds the wheel under `dist/`. The suite installed with the package runs
with `purepy-conformance`; `purepy-conformance --help` lists its options.

Tests in `src/purepy/conformance-suite/` are organised by the outcome under Python and the outcome under
PurePy, following the grid in the conformance section of the specification; the runner derives every
assertion from the path. A test of one module is a `.py` file with expectation files as siblings
(`.expected`, `.error.expected`, `.exception.expected`, `.status.expected`); a test of a program of several
modules is a directory holding `main.py`, the expectation files of `main.py` and the other modules.

The outcome under Python is one of:

- `python-rejects/`: Python raises `SyntaxError` before running the program
- `python-raises/`: Python raises another exception while running the program
- `python-succeeds/`: Python runs the program with the expected output

The outcome under PurePy is one of:

- `parser-rejects/`: rejected by the parser
- `typing-rejects/`: rejected by the type checker
- `undefined/`: well-formed, and the run aborts with termination kind `undef`
- `agrees/`: well-formed, and the run yields the same result as under Python, including the same exception

The directory `python-succeeds/agrees/mypy-bug/` holds tests rejected by mypy because of a behaviour reported as a
mypy bug; every other test in `python-succeeds/agrees/` type-checks under mypy. The tests in `syntactic-only/`
construct a form as an AST, because Python source cannot express the form, and check that PurePy rejects it.

A test has `.expected` under `python-succeeds/` and `.exception.expected` elsewhere, naming `SyntaxError` exactly
under `python-rejects/`, so a misfiled test fails. A test that exits with a nonzero status through `sys.exit`
states the status in `.status.expected`.

Every test under `typing-rejects/`, `undefined/` and `agrees/` names a rule of the specification on its first line,
as `# rule: name`. Under `typing-rejects/` the rule is the one with a premise or side condition that fails for the
program. Under `undefined/` and `agrees/` the rule is the one yielding the result. The specification repository
checks the rule names and the mypy claims against each release.

## Development

Synchronise the project environment and install the development dependencies:

```bash
uv sync --locked
```

Format the sources:

```bash
uv run --locked ruff format ./src/purepy ./test/run-all.py
```

After changing dependencies or metadata in `pyproject.toml`, run `uv lock` and commit `pyproject.toml` and
`uv.lock`.

## Release workflow

Run the `Release` GitHub Action manually with a version in the form `x.y.z` (for example, `0.24.0`). The action
updates and commits the package version on `main`, creates and pushes the tag `v0.24.0`, checks the proofs,
generates the type checker, runs the conformance suite and creates the GitHub Release for the tag with the
wheel of the `purepy` package attached. The specification repository depends on the latest release.

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
