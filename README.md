# PurePy formalisation in Isabelle/HOL

This is an experiment of how a formalisation of PurePy could look like in Isabelle/HOL.

This tries to find out:

- How easy it is to translate from Ott to Isabelle/HOL 
- How easy it is to automatically extract an evaluation function from the given inductive semantics rules
- How easy it is extract an executable OCaml evaluator from the formalisation

Currently, only a really small subset of the expression syntax + semantics is formalised

## File contents

| File              | Content                                           |
|-------------------|---------------------------------------------------|
| `Syntax.thy`      | Syntax definition (to be generated from Ott)      |
| `Semantics.thy`   | Semantics definition as inductive predicate       |
| `Eval.thy`        | Semantics definition as recursive function        |
| `Correctness.thy` | Correctness proof between the two semantics defs  |
| `Exctraction.thy` | Extraction to OCaml (todo)                        |

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