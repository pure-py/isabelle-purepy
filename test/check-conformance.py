#!/usr/bin/env python3
import argparse
import pathlib
import re
import sys

import purepy_conformance
from purepy_conformance import Results, main_module, run, suite, tests

from purepy.rules import rules_cited

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


def check_rules(r: Results) -> None:
    """Every rule the type checker cites is cited by a test of the suite, so exists in the specification"""
    with r.test("rules cited by the type checker"):
        with suite() as path:
            cited = {
                m.group(1)
                for test in tests(path)
                if (m := CITATION.match(main_module(test).read_text().split("\n", 1)[0]))
            }
        for name in sorted(rules_cited() - cited):
            r.fail(f"{name} not cited by the conformance suite")


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
