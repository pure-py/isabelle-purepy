#!/usr/bin/env python3
"""Copy the exit statuses and the wording for excluded features of the pinned conformance package into the type
checker, which is installed without the package"""

import inspect
import pathlib
import sys

from purepy_conformance import Classification, Exit, excluded


def main() -> None:
    (path,) = map(pathlib.Path, sys.argv[1:])
    sources = "\n\n".join(inspect.getsource(d) for d in (Exit, Classification, excluded))
    path.write_text(f"from enum import IntEnum, StrEnum\n\n\n{sources}")


if __name__ == "__main__":
    main()
