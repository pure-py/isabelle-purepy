# Build session. Set ISABELLE to isabelle executable if not on PATH.
ISABELLE ?= isabelle
PYTHON ?= uv run --no-project python

ISABELLE_VERSION := $(shell cat .isabelle-version)
CODEGEN := python/isabelle-python-codegen
CODEGEN_VERSION := $(shell cat .python-codegen-version)
CODE := python/python_out/isabelle-purepy-python.Codegen/code

default: build

# Isabelle on path is the version the session is checked with.
check-version:
	@test "$$($(ISABELLE) version)" = "$(ISABELLE_VERSION)" || \
		{ echo "$(ISABELLE) is $$($(ISABELLE) version), not $(ISABELLE_VERSION)"; exit 1; }

# Python code generator at pinned commit
codegen:
	@test -d $(CODEGEN)/.git || git init -q $(CODEGEN)
	@test "$$(git -C $(CODEGEN) rev-parse -q --verify HEAD)" = "$(CODEGEN_VERSION)" || \
		{ git -C $(CODEGEN) fetch -q --depth 1 https://github.com/pure-py/isabelle-python-codegen.git \
			$(CODEGEN_VERSION) && git -C $(CODEGEN) checkout -q --detach $(CODEGEN_VERSION); }

build: check-version codegen
	rm -rf python/python_out
	$(ISABELLE) build -v -e -d $(CODEGEN) -D .
	$(PYTHON) -m py_compile $$(find $(CODE) -name '*.py')
	PYTHONPATH=$(CODE) $(PYTHON) python/smoke_test.py

.PHONY: default check-version codegen build
