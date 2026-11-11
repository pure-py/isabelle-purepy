#!/usr/bin/env python3
"""Index of the theorem, constant and type names declared by the session theories, as names.txt"""

import pathlib
import re
import sys

from theories import theories

HERE = pathlib.Path(__file__).parent
INDEX = HERE / "names.txt"

NAME = r"([A-Za-z][\w']*)"
TYPE_PARAMS = r"(?:'\w+\s+|\([^)]*\)\s+)?"
# Comments, strings and cartouches, which may contain text resembling a declaration
QUOTED = re.compile(r"\(\*.*?\*\)|\"(?:[^\"\\]|\\.)*\"|\\<open>.*?\\<close>|‹[^›]*›", re.DOTALL)
CONSTANT = r"(?:definition|abbreviation|fun|function|primrec|inductive|inductive_set|coinductive|partial_function)"
DECLARATIONS = [
    re.compile(
        rf"^\s*(?:theorem|lemma|corollary|proposition|lemmas)\s+(?:\(in\s+\w+\)\s+)?{NAME}\s*(?:\[[^\]]*\]\s*)?[:=]",
        re.MULTILINE,
    ),
    re.compile(rf"^\s*{CONSTANT}(?:\s*\([^)]*\))?\s+{NAME}", re.MULTILINE),
    re.compile(rf"^\s*{CONSTANT}\b.*\band\s+{NAME}\s*::", re.MULTILINE),
    re.compile(rf"^\s*and\s+{NAME}\s*::", re.MULTILINE),
    re.compile(rf"\band\s*\n\s*{NAME}\s*::"),
    re.compile(
        rf"^\s*(?:datatype|codatatype|type_synonym|record|typedef)\s+{TYPE_PARAMS}{NAME}",
        re.MULTILINE,
    ),
    re.compile(rf"^\s*and\s+{TYPE_PARAMS}{NAME}\s*=", re.MULTILINE),
]


def names(theory: pathlib.Path) -> set[str]:
    text = QUOTED.sub('""', (HERE / theory).read_text())
    return {name for declaration in DECLARATIONS for name in declaration.findall(text)}


def index() -> str:
    entries = sorted((name, theory) for theory in theories() for name in names(theory))
    return "".join(f"{name}\t{theory}\n" for name, theory in entries)


def main() -> None:
    if sys.argv[1:] == ["--check"]:
        if not INDEX.exists() or INDEX.read_text() != index():
            sys.exit("names.txt out of date: run ./names.py")
    else:
        INDEX.write_text(index())


if __name__ == "__main__":
    main()
