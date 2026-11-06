#!/usr/bin/env python3
import argparse
import pathlib
import re
import sys

import purepy_conformance
from purepy_conformance import (
    PurePyOutcome,
    Results,
    figure_numbers,
    main_module,
    run,
    suite,
    tests,
)

from purepy.check_program import check_module, check_program
from purepy.rules import JUDGEMENT, RULE, spec_names

ROOT = pathlib.Path(__file__).resolve().parent.parent
TEST = ROOT / "test"
SRC = ROOT / "src" / "purepy"
PYTHON_VERSION = (ROOT / ".python-version").read_text().strip()
CITATION = re.compile(r"# judgement: ([a-z0-9-]+)(?:, rule: ([a-z0-9-]+))?$")


def check_lint(r: Results) -> None:
    with r.test("mypy and ruff"):
        sources = sorted(str(path) for path in SRC.glob("*.py")) + [
            str(TEST / "check-conformance.py")
        ]
        for tool in (
            ["mypy", "--strict", "--python-version", PYTHON_VERSION],
            ["ruff", "check"],
            ["ruff", "format", "--check"],
        ):
            proc = run([*tool, *sources])
            if proc.returncode != 0:
                r.fail((proc.stdout + proc.stderr).strip()[:400])
                break


type Citation = tuple[str | None, str | None]


def citation_of(test: pathlib.Path) -> Citation:
    """Judgement which selects no rule, or rule violated, by the rejection of test"""
    d = check_program(main_module(test)) if test.is_dir() else check_module(test)
    return (None, None) if d is None else (d.judgement, d.rule)


def cited(judgement: str, rule: str | None) -> Citation:
    """Citation of a judgement, with its rule if any; the rule alone determines the judgement"""
    return (judgement, None) if rule is None else (None, rule)


def show(c: Citation) -> str:
    judgement, rule = c
    return f"rule {rule}" if judgement is None else f"judgement {judgement}"


def check_citations(r: Results) -> None:
    """Each test of an ill-formed program rejected under the judgement or rule it cites; each judgement and rule
    of the mechanisation reached by such a test, and named in the specification"""
    with r.test("judgements and rules cited"):
        with suite() as path:
            citations = {
                test.relative_to(path): (cited(m.group(1), m.group(2)), citation_of(test))
                for test in tests(path)
                if test.relative_to(path).parts[1] == PurePyOutcome.TYPING_REJECTS
                and (m := CITATION.match(main_module(test).read_text().split("\n", 1)[0]))
            }
        for test, (expected, actual) in sorted(citations.items()):
            if actual != expected:
                r.fail(f"{test} cites {show(expected)}, rejected under {show(actual)}")
        reached = {expected for expected, actual in citations.values() if actual == expected}
        figures = figure_numbers()
        tags = [((j, None), j in figures.judgements) for j in sorted(spec_names(JUDGEMENT))] + [
            ((None, n), n in figures.rules) for n in sorted(spec_names(RULE))
        ]
        for c, specified in tags:
            if not specified:
                r.fail(f"{show(c)} not in the specification")
            elif c not in reached:
                r.fail(f"{show(c)} reached by no test citing it")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-lint", action="store_true")
    args, conformance_args = parser.parse_known_args()
    if not args.no_lint:
        lint = Results()
        check_lint(lint)
        check_citations(lint)
        lint.summary()
        if lint.failed:
            sys.exit(1)
    purepy_conformance.main(
        [
            "--type-checker",
            f"{sys.executable} -m purepy --check",
            "--check-messages",
            *conformance_args,
        ]
    )


if __name__ == "__main__":
    main()
