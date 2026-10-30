import argparse
import pathlib
import sys

from .check_program import check_module, check_program, exit_code, format_program_rejection
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

    rejection = check_module(args.path) if args.module else check_program(args.path)
    print(format_program_rejection(rejection, args.path))
    sys.exit(exit_code(rejection))


if __name__ == "__main__":
    main()
