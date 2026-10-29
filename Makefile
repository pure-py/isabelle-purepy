# Build session. Set ISABELLE to isabelle executable if not on PATH.
ISABELLE ?= isabelle
PYTHON ?= uv run --no-project python

ISABELLE_VERSION := $(shell cat .isabelle-version)
CODEGEN := python/isabelle-python-codegen
CODE := python/python_out/isabelle-purepy-python.Codegen/code
GENERATED := src/purepy/generated

default: build

# Isabelle on path is the version the session is checked with.
check-version:
	@test "$$($(ISABELLE) version)" = "$(ISABELLE_VERSION)" || \
		{ echo "$(ISABELLE) is $$($(ISABELLE) version), not $(ISABELLE_VERSION)"; exit 1; }

codegen:
	@test -e $(CODEGEN)/Python.thy -a ! -e $(CODEGEN)/.git || ./fetch-codegen.sh

# Check the proofs, then generate the type checker as a subpackage of purepy
build: check-version codegen
	@test "$$(cat .python-version)" = "$$(cat $(CODEGEN)/.python-version)" || \
		{ echo "code generator targets Python $$(cat $(CODEGEN)/.python-version), not $$(cat .python-version)"; exit 1; }
	$(PYTHON) theories.py --check
	rm -rf python/python_out
	$(ISABELLE) build -v -e -d $(CODEGEN) -D .
	$(PYTHON) generated.py $(CODE) $(GENERATED)

# Lint and conformance suite, under the generated type checker
check-tests:
	@test -e $(GENERATED) || { echo "$(GENERATED) not generated: make build"; exit 1; }
	uv run --locked ./test/run-all.sh

wheel: check-tests
	rm -rf dist && uv build --wheel

# Self-contained copy under DEST
dist: codegen
	@test -n "$(DEST)" || { echo "usage: make dist DEST=<dir>"; exit 1; }
	@test ! -e $(DEST) || { echo "$(DEST) exists"; exit 1; }
	mkdir -p $(DEST)/$(CODEGEN)
	git archive --format=tar HEAD | tar -x -C $(DEST)
	git -C $(CODEGEN) archive --format=tar HEAD | tar -x -C $(DEST)/$(CODEGEN)
	rm -rf $(DEST)/.github $(DEST)/.claude $(DEST)/fetch-codegen.sh

.PHONY: default check-version codegen build check-tests wheel dist
