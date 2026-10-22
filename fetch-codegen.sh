#!/usr/bin/env bash
# Python code generator at the commit named in .python-codegen-version, under python/isabelle-python-codegen.
set -euo pipefail

CODEGEN=python/isabelle-python-codegen
VERSION="$(cat .python-codegen-version)"

test -d "$CODEGEN/.git" || git init -q "$CODEGEN"
test "$(git -C "$CODEGEN" rev-parse -q --verify HEAD)" = "$VERSION" || {
  git -C "$CODEGEN" fetch -q --depth 1 https://github.com/pure-py/isabelle-python-codegen.git "$VERSION"
  git -C "$CODEGEN" checkout -q --detach "$VERSION"
}
