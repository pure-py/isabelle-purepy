# Build session. Set ISABELLE to isabelle executable if not on PATH.
ISABELLE ?= isabelle

ISABELLE_VERSION := $(shell cat .isabelle-version)

default: build

# Isabelle on path is the version the session is checked with.
check-version:
	@test "$$($(ISABELLE) version)" = "$(ISABELLE_VERSION)" || \
		{ echo "$(ISABELLE) is $$($(ISABELLE) version), not $(ISABELLE_VERSION)"; exit 1; }

build: check-version
	$(ISABELLE) build -v -D .

.PHONY: default check-version build
