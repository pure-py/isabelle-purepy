#!/usr/bin/env python3
"""Generated modules copied from the code generator's output directory into a package directory, their imports
of one another made relative, so that the package can be installed under any name."""

import pathlib
import re
import shutil
import sys


def main() -> None:
    source, package = map(pathlib.Path, sys.argv[1:])
    modules = sorted(p.stem for p in source.glob("*.py"))
    shutil.rmtree(package, ignore_errors=True)
    package.mkdir()
    (package / "__init__.py").write_text("")
    for module in modules:
        text = (source / f"{module}.py").read_text()
        text = re.sub(
            r"^import (\w+)$",
            lambda m: f"from . import {m.group(1)}" if m.group(1) in modules else m.group(0),
            text,
            flags=re.M,
        )
        (package / f"{module}.py").write_text(text)


if __name__ == "__main__":
    main()
