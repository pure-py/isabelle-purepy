# Build session. Set ISABELLE to isabelle executable if not on PATH.
ISABELLE ?= isabelle

default: build

# Check proofs, without building document.
build:
	$(ISABELLE) build -v -o document=false -D .

# Check proofs and build document, which needs LaTeX.
document:
	$(ISABELLE) build -v -D .

clean:
	rm -rf output

.PHONY: default build document clean
