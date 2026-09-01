# Build the session. Set ISABELLE to the isabelle executable if it is not on PATH.
ISABELLE ?= isabelle

default: build

# Check the proofs, without building the document.
build:
	$(ISABELLE) build -v -o document=false -D .

# Check the proofs and build the document, which needs LaTeX.
document:
	$(ISABELLE) build -v -D .

clean:
	rm -rf output

.PHONY: default build document clean
