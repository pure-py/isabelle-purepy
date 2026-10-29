#!/usr/bin/env python3
"""Conformance suite under the reference interpreter: each test checked by the type checker, as by
purepy-conformance, and each test on which PurePy agrees with Python, or is undefined, run by the reference
interpreter against the outcome expected of Python"""

import argparse
import contextlib
import pathlib
import shutil
import sys
import tempfile
from collections.abc import Iterator, Sequence

from purepy.conformance import (
    EXCEPTION_EXPECTED,
    EXPECTED,
    MAIN,
    STATUS_EXPECTED,
    SYNTACTIC_ONLY,
    PurePyOutcome,
    PythonOutcome,
    Runner,
    run,
    suite,
)
from purepy.run_program import UNDEFINED


@contextlib.contextmanager
def alone(path: pathlib.Path) -> Iterator[pathlib.Path]:
    """Path of the test's main module in a directory of its own, since the interpreter takes every module of the
    directory as part of the program: a single-module test is copied to a new directory"""
    with tempfile.TemporaryDirectory() as d:
        yield path if path.name == MAIN else pathlib.Path(shutil.copy(path, d))


class PurePyRunner(Runner):
    def __init__(self) -> None:
        super().__init__(None)  # not run under Python

    def interpret(
        self, path: pathlib.Path, python: PythonOutcome, purepy: PurePyOutcome
    ) -> list[str]:
        """For a test on which PurePy agrees with Python, the same output and exit status, or the same
        exception; for undefined behaviour, the interpreter's undefined status"""
        with alone(path) as program:
            proc = run([sys.executable, "-m", "purepy", str(program)])
        first = (proc.stdout + proc.stderr).strip().split("\n", 1)[0]
        if purepy == PurePyOutcome.UNDEFINED:
            if proc.returncode != UNDEFINED:
                return [f"interpret: exit {proc.returncode}, expected {UNDEFINED}: {first}"]
            return []
        if python == PythonOutcome.RAISES:
            name = path.with_suffix(EXCEPTION_EXPECTED).read_text().strip()
            if proc.returncode == 0 or name not in proc.stderr:
                return [
                    f"interpret: expected {name}, got exit {proc.returncode}: {proc.stderr.strip()}"
                ]
            return []
        status_path = path.with_suffix(STATUS_EXPECTED)
        status = int(status_path.read_text()) if status_path.exists() else 0
        if proc.returncode != status:
            return [f"interpret: exit {proc.returncode}, expected {status}: {first}"]
        if proc.stdout != path.with_suffix(EXPECTED).read_text():
            return ["interpret: output mismatch"]
        return []

    def run_test(self, suite: pathlib.Path, test: pathlib.Path) -> list[str]:
        failures = super().run_test(suite, test)
        dirs = test.relative_to(suite).parts[:-1]
        if dirs[0] == SYNTACTIC_ONLY:
            return failures
        python, purepy = PythonOutcome(dirs[0]), PurePyOutcome(dirs[1])
        if purepy not in (PurePyOutcome.AGREES, PurePyOutcome.UNDEFINED):
            return failures
        return [*failures, *self.interpret(test / MAIN if test.is_dir() else test, python, purepy)]


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(prog="conformance-purepy")
    parser.add_argument(
        "--jobs", type=int, help="number of tests run in parallel (default: number of cores)"
    )
    args = parser.parse_args(argv)
    r = PurePyRunner()
    with suite() as path:
        r.run_suite(path, args.jobs)
    r.summary()
    sys.exit(0 if not r.failed else 1)


if __name__ == "__main__":
    main()
