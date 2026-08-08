ISABELLE        ?= isabelle
AFP             ?= $(HOME)/afp/thys
SESSION         := Voblint_Examples
# All sessions, so a clean build forces every one to be (re)presented.
# Isabelle only presents sessions it actually builds; on warm heaps the
# up-to-date ancestors are skipped and their links render as [brackets].
SESSIONS        := Voblint_VIMP Voblint_CFG Voblint_Core Voblint_Analysis Voblint_Formalization Voblint_Examples
ISABELLE_HOME_USER ?= $(shell $(ISABELLE) getenv -b ISABELLE_HOME_USER 2>/dev/null)
HTML_DIR        := docs/html

TD_DIR          := vendor/td-verification
TD_PATCH        := vendor/td-verification.patch

AC_DIR          := vendor/autocorrode

LINTER_DIR      := /tmp/isabelle-linter
LINTER_TAG      := Isabelle2025-2-v1.0.0

.PHONY: all vendor bootstrap build html lint jedit clean clean-vendor update-autocorrode refresh-td-patch codegen codegen-check regression

all: build

# Initialize the td-verification submodule (pinned via the superproject
# gitlink) and apply our local patch on top. Idempotent.
vendor:
	@test -e $(TD_DIR)/.git || git submodule update --init $(TD_DIR)
	@if [ -s $(TD_PATCH) ]; then \
	  if git -C $(TD_DIR) apply --check $(CURDIR)/$(TD_PATCH) 2>/dev/null; then \
	    git -C $(TD_DIR) apply $(CURDIR)/$(TD_PATCH); \
	    echo "Applied $(TD_PATCH)."; \
	  elif git -C $(TD_DIR) apply --check --reverse $(CURDIR)/$(TD_PATCH) 2>/dev/null; then \
	    : ; \
	  else \
	    echo "ERROR: $(TD_PATCH) does not apply cleanly to $(TD_DIR)."; \
	    exit 1; \
	  fi; \
	fi

# Bootstrap: build all 5 sessions in topological order (fresh clone, no heaps).
# Use -d (not -D) per session to avoid validating downstream sessions before
# upstream heaps exist.
bootstrap: vendor
	@test -d $(AFP) || { echo "ERROR: AFP not found at $(AFP). Set AFP=<path> or install AFP."; exit 1; }
	$(ISABELLE) build -v -N -d $(AFP) -d $(TD_DIR) -d src/VIMP Voblint_VIMP
	$(ISABELLE) build -v -N -d $(AFP) -d $(TD_DIR) -d src/VIMP -d src/CFG Voblint_CFG
	$(ISABELLE) build -v -N -d $(AFP) -d $(TD_DIR) -d src/VIMP -d src/CFG -d src/Core Voblint_Core
	$(ISABELLE) build -v -N -d $(AFP) -d $(TD_DIR) -d src/VIMP -d src/CFG -d src/Core -d src/Analysis Voblint_Analysis
	$(ISABELLE) build -v -N -d $(AFP) -d $(TD_DIR) -D . Voblint_Formalization

# Build the top-level session (incremental; requires bootstrap heaps).
build: vendor
	@test -d $(AFP) || { echo "ERROR: AFP not found at $(AFP). Set AFP=<path> or install AFP."; exit 1; }
	$(ISABELLE) build -v -j12 -o threads=12 -N -d $(AFP) -d $(TD_DIR) -D . $(SESSION)

# Regenerate codegen/generated/ from the export_code declarations in
# src/Examples/{Sign,Interval}/Exec_*.thy. Do not hand-edit generated files.
codegen: vendor
	@test -d $(AFP) || { echo "ERROR: AFP not found at $(AFP). Set AFP=<path> or install AFP."; exit 1; }
	AFP=$(AFP) ./scripts/regenerate-codegen.sh

# Regenerate codegen/generated/ and fail if the tracked output drifted from
# the export_code declarations, i.e. someone edited a *.thy export and forgot
# to run `make codegen` and commit the result.
codegen-check: codegen
	git diff --exit-code -- codegen/generated/

# Compile and run the hand-written Haskell/OCaml drivers under
# codegen/regression/ against the tracked codegen/generated/ sources, and
# check their output against the values already proved by
# src/Examples/Mixed/Example_Analysis_Dispatch.thy's dispatch_demo_*
# lemmas. Requires ghc and ocamlfind on PATH; does not require Isabelle.
regression:
	cd codegen/regression/haskell && \
	  ghc -i../../generated -o regression-hs Main.hs && \
	  ./regression-hs
	cd codegen/regression/ocaml && \
	  cp ../../generated/Voblint_Analyse_OCaml.ocaml ./Voblint_Analyse_OCaml.ml && \
	  ocamlfind ocamlopt -package str -linkpkg Voblint_Analyse_OCaml.ml main.ml -o regression-ml && \
	  ./regression-ml

# HTML browser info for all session theories (see Isabelle System Manual, browser_info).
# Output is copied to $(HTML_DIR)/ for a repo-local entry point; Isabelle also keeps a
# copy under $(BROWSER_INFO_SRC)/. See https://stackoverflow.com/questions/17833567/
html: vendor
	@test -d $(AFP) || { echo "ERROR: AFP not found at $(AFP). Set AFP=<path> or install AFP."; exit 1; }
	@test -n "$(ISABELLE_HOME_USER)" || { echo "ERROR: could not resolve ISABELLE_HOME_USER."; exit 1; }
	# Clean build (-c) so every session is rebuilt and therefore presented.
	# Isabelle emits HTML only for sessions it actually builds; -o browser_info
	# on warm heaps would skip up-to-date ancestors (and re-presenting them
	# collides on the isabelle_sources PRIMARY KEY). In fresh CI -c is a no-op.
	$(ISABELLE) build -v -N -d $(AFP) -d $(TD_DIR) -D . -o browser_info -c $(SESSIONS)
	rm -rf "$(HTML_DIR)"
	mkdir -p "$(HTML_DIR)"
	cp -R "$(ISABELLE_HOME_USER)/browser_info/." "$(HTML_DIR)/"
	touch "$(HTML_DIR)/.nojekyll"
	@echo "Open $(HTML_DIR)/Unsorted/$(SESSION)/index.html"

# Style-lint our own sessions with the community isabelle-linter
# (https://github.com/isabelle-prover/isabelle-linter). Installs the CLI-only
# component on first run (cached across steps by $(LINTER_DIR)); reuses
# whatever heaps are already built, so run this after `build`/`html` in the
# same environment rather than cold. -f error fails the build on any
# error-severity finding -- notably unfinished_proof (sorry/<proof>) and the
# rest of the afp_mandatory bundle.
lint: vendor
	@test -d $(AFP) || { echo "ERROR: AFP not found at $(AFP). Set AFP=<path> or install AFP."; exit 1; }
	@test -d $(LINTER_DIR) || git clone --depth 1 --branch $(LINTER_TAG) https://github.com/isabelle-prover/isabelle-linter $(LINTER_DIR)
	$(ISABELLE) components -u $(LINTER_DIR)/linter_base
	$(ISABELLE) lint -v -d $(AFP) -d $(TD_DIR) -D . -o lint_bundles=default,afp_mandatory -f error $(SESSIONS)

# Launch jEdit with the right session roots loaded.
jedit: vendor
	$(ISABELLE) jedit -d $(AFP) -d $(TD_DIR) -d .

# Discard local TD patch + working-tree edits (the submodule itself stays
# initialized; rerun `make vendor` to reapply the patch).
clean-vendor:
	git -C $(TD_DIR) reset --hard HEAD

clean:
	$(ISABELLE) build -n -c -d $(AFP) -D . $(SESSION) ||:

# Fast-forward vendor/autocorrode to upstream main. After this, review `git diff`
# and commit the submodule pointer.
update-autocorrode:
	@test -e $(AC_DIR)/.git || { echo "ERROR: $(AC_DIR) not initialized. Run ./scripts/setup.sh first."; exit 1; }
	git submodule update --remote --merge $(AC_DIR)

# Same, for td-verification.
refresh-td-patch:
	git -C $(TD_DIR) --no-pager diff > $(TD_PATCH)
	@echo "Wrote $(TD_PATCH) ($$(wc -l < $(TD_PATCH)) lines). Review with: git diff -- $(TD_PATCH)"
