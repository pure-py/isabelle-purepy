# Build session. Set ISABELLE to isabelle executable if not on PATH.
ISABELLE ?= isabelle
PYTHON ?= uv run --no-project python

ISABELLE_VERSION := $(shell cat .isabelle-version)
CODEGEN := python/isabelle-python-codegen
CODE := python/python_out/isabelle-purepy-python.Codegen/code

default: build

# Isabelle on path is the version the session is checked with.
check-version:
	@test "$$($(ISABELLE) version)" = "$(ISABELLE_VERSION)" || \
		{ echo "$(ISABELLE) is $$($(ISABELLE) version), not $(ISABELLE_VERSION)"; exit 1; }

# Python code generator, fetched unless copied in by dist
codegen:
	@test -e $(CODEGEN)/Python.thy -a ! -e $(CODEGEN)/.git || ./fetch-codegen.sh

build: check-version codegen
	rm -rf python/python_out
	$(ISABELLE) build -v -e -d $(CODEGEN) -D .
	$(PYTHON) -m py_compile $$(find $(CODE) -name '*.py')
	PYTHONPATH=$(CODE) $(PYTHON) python/smoke_test.py

# Sources and code generator under DEST, without CI configuration or the fetch script
dist: codegen
	@test -n "$(DEST)" || { echo "usage: make dist DEST=<dir>"; exit 1; }
	@test ! -e $(DEST) || { echo "$(DEST) exists"; exit 1; }
	mkdir -p $(DEST)/$(CODEGEN)
	git archive --format=tar HEAD | tar -x -C $(DEST)
	git -C $(CODEGEN) archive --format=tar HEAD | tar -x -C $(DEST)/$(CODEGEN)
	rm -rf $(DEST)/.github $(DEST)/.claude $(DEST)/fetch-codegen.sh

.PHONY: default check-version codegen build dist
