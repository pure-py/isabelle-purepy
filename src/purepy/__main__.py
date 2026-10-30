import argparse
import pathlib
import sys

from .check_program import check_module, check_program, format_program_result
from .conformance import Exit
from .run_program import DEFAULT_FUEL, run_program


def main() -> None:
    parser = argparse.ArgumentParser(prog="purepy")
    parser.add_argument("path", type=pathlib.Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--module", action="store_true")
    parser.add_argument("--fuel", type=int, default=DEFAULT_FUEL)
    parser.add_argument("args", nargs="*", help="command-line arguments of the program run")

    args = parser.parse_args()

    if not args.check:
        sys.exit(run_program(args.path, args.args, args.fuel))

    result = check_module(args.path) if args.module else check_program(args.path)
    print(format_program_result(result, args.path))
    sys.exit(Exit.OK if result is None else result.exit_code)


if __name__ == "__main__":
    main()
