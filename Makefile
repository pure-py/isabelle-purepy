# Build session. Set ISABELLE to isabelle executable if not on PATH.
ISABELLE ?= isabelle

ISABELLE_VERSION := $(shell cat .isabelle-version)

default: build

# Isabelle on path is the version the session is checked with.
check-version:
	@test "$$($(ISABELLE) version)" = "$(ISABELLE_VERSION)" || \
		{ echo "$(ISABELLE) is $$($(ISABELLE) version), not $(ISABELLE_VERSION)"; exit 1; }

# Check proofs and build document, which needs LaTeX.
build: check-version
	$(ISABELLE) build -v -D .

clean:
	rm -rf output

.PHONY: default check-version build clean
