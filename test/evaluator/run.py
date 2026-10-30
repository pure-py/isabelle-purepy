#!/usr/bin/env python3
"""Evaluator tests: each test_eval_* function of each *_tests.py module here, run against the generated evaluator
of src/purepy/generated (make build). The tests build syntax directly, without the type checker, so they also reach
the aborting cases that the type system rules out"""

import importlib
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
GREEN, RED, RESET = "\033[32m", "\033[31m", "\033[0m"


def main() -> None:
    sys.path.insert(0, str(HERE))
    importlib.import_module("located")  # before the tests, which build syntax as they are imported
    passed, failed = 0, []
    for path in sorted(HERE.glob("*_tests.py")):
        module = importlib.import_module(path.stem)
        print(path.stem)
        for name, test in sorted(vars(module).items()):
            if not name.startswith("test_eval") or not callable(test):
                continue
            try:
                test()
            except Exception as exc:  # noqa: BLE001 - any failure of a test is reported
                failed.append(f"{path.stem}.{name}")
                print(f"  {RED}✗{RESET} {name} ({type(exc).__name__}: {exc})")
            else:
                passed += 1
                print(f"  {GREEN}✓{RESET} {name}")
    total = passed + len(failed)
    print()
    if failed:
        print(f"{RED}✗ {passed}/{total} passed, {len(failed)} failed{RESET}")
    else:
        print(f"{GREEN}✓ {total}/{total} passed{RESET}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
