# PurePy formalisation in Isabelle/HOL

[![build](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml/badge.svg)](https://github.com/pure-py/isabelle-purepy/actions/workflows/build.yml)

This is an experiment of how a formalisation of PurePy could look like in Isabelle/HOL.

This tries to find out:

- How easy it is to translate from Ott to Isabelle/HOL 
- How easy it is to automatically extract an evaluation function from the given inductive semantics rules
- How easy it is extract an executable OCaml evaluator from the formalisation

Currently, only a really small subset of the expression syntax + semantics is formalised

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

| File              | Content                                           |
|-------------------|---------------------------------------------------|
| `Syntax.thy`      | Syntax definition (to be generated from Ott)      |
| `Semantics.thy`   | Semantics definition as inductive predicate       |
| `Eval.thy`        | Semantics definition as recursive function        |
| `Correctness.thy` | Correctness proof between the two semantics defs  |
| `Extraction.thy` | Extraction to OCaml (todo)                        |

## Observations

The Isabelle `code_pred` tool which can automatically generated executable evaluators
from inductive definitions has a very specific input format, i.e., the inductive
rules must be in a form that allows automatic conversion to a recursive evaluation
scheme. Right now, the rules in `Semantics.thy` do not fulfil these requirements.

The correctness proof in `Correctness.thy` is divided into forward (safety) and
backward (completeness) proofs. All proofs in that file are a collaboration between
Claude, ChatGPT, Sledgehammer, and myself, and definitely could do with some work.
However, it was quite interesting to see, that the completeness proof was almost
fully derived by Sledgehammer, with the occasional nudge into the right direction.

Code extraction remains a TODO