#!/usr/bin/env python3
import argparse
import pathlib
import re
import sys

import purepy_conformance
from purepy_conformance import PurePyOutcome, Results, main_module, run, suite, tests

from purepy.check_program import check_module, check_program
from purepy.rules import rule_names

ROOT = pathlib.Path(__file__).resolve().parent.parent
TEST = ROOT / "test"
SRC = ROOT / "src" / "purepy"
PYTHON_VERSION = (ROOT / ".python-version").read_text().strip()
CITATION = re.compile(r"# rule: ([a-z0-9-]+)")


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


def rule_violated(test: pathlib.Path) -> str | None:
    d = check_program(main_module(test)) if test.is_dir() else check_module(test)
    return None if d is None else d.rule


def check_rules(r: Results) -> None:
    """Each test of an ill-formed program rejected under the rule it cites, and each rule reached by such a test"""
    with r.test("rules violated"):
        with suite() as path:
            cited = {
                test.relative_to(path): (m.group(1), rule_violated(test))
                for test in tests(path)
                if test.relative_to(path).parts[1] == PurePyOutcome.TYPING_REJECTS
                and (m := CITATION.match(main_module(test).read_text().split("\n", 1)[0]))
            }
        for test, (name, violated) in sorted(cited.items()):
            if violated != name:
                r.fail(f"{test} cites {name}, rejected under {violated}")
        reached = {name for name, violated in cited.values() if violated == name}
        for name in sorted(rule_names() - reached):
            r.fail(f"{name} reached by no test citing it")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-lint", action="store_true")
    args, conformance_args = parser.parse_known_args()
    if not args.no_lint:
        lint = Results()
        check_lint(lint)
        check_rules(lint)
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
