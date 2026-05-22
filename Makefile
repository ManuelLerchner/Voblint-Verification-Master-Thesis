ISABELLE        ?= isabelle
AFP             ?= $(HOME)/afp/thys
SESSION         := Goblint_Formalization

TD_URL          := https://github.com/stilscher/td-verification
TD_COMMIT       := af78761e62c28bf299863b5735c32b7c2cfcd93e
TD_DIR          := vendor/td-verification
TD_PATCH        := vendor/td-verification.patch

AC_DIR          := vendor/autocorrode
AC_PATCH        := vendor/autocorrode.patch

.PHONY: all vendor build jedit clean-vendor clean update-autocorrode refresh-autocorrode-patch

all: build

# Fetch upstream TD solver, pin to TD_COMMIT, apply local patch.
$(TD_DIR)/.patched:
	@test ! -d $(TD_DIR) || { echo "ERROR: $(TD_DIR) exists. Run 'make clean-vendor' first."; exit 1; }
	git clone $(TD_URL) $(TD_DIR)
	cd $(TD_DIR) && git checkout $(TD_COMMIT)
	cd $(TD_DIR) && git apply ../td-verification.patch
	touch $@

vendor: $(TD_DIR)/.patched

# Build the project session. Depends on vendored TD solver.
build: vendor
	@test -d $(AFP) || { echo "ERROR: AFP not found at $(AFP). Set AFP=<path> or install AFP."; exit 1; }
	$(ISABELLE) build -d $(AFP) -d $(TD_DIR) -D . $(SESSION)

# Launch jEdit with the right session roots loaded.
jedit: vendor
	$(ISABELLE) jedit -d $(AFP) -d $(TD_DIR) -d .

clean-vendor:
	rm -rf $(TD_DIR)

clean: clean-vendor
	$(ISABELLE) build -n -c -d $(AFP) -D . $(SESSION) ||:

# Fast-forward vendor/autocorrode to upstream main, reapply autocorrode.patch,
# stage the bump. After this, review `git diff` and commit the submodule pointer.
update-autocorrode:
	@test -e $(AC_DIR)/.git || { echo "ERROR: $(AC_DIR) not initialized. Run ./setup.sh first."; exit 1; }
	git submodule update --remote --merge $(AC_DIR)
	@if [ -s $(AC_PATCH) ]; then \
	  if git -C $(AC_DIR) apply --check $(CURDIR)/$(AC_PATCH) 2>/dev/null; then \
	    git -C $(AC_DIR) apply $(CURDIR)/$(AC_PATCH); \
	    echo "Patch reapplied. Review and run: git add $(AC_DIR) && git commit"; \
	  else \
	    echo "WARNING: $(AC_PATCH) no longer applies cleanly to new upstream."; \
	    echo "  Resolve manually, then run: make refresh-autocorrode-patch"; \
	    exit 1; \
	  fi; \
	fi

# Regenerate vendor/autocorrode.patch from the current working tree (use after
# manually merging conflicts from an upstream bump).
refresh-autocorrode-patch:
	git -C $(AC_DIR) --no-pager diff > $(AC_PATCH)
	@echo "Wrote $(AC_PATCH) ($$(wc -l < $(AC_PATCH)) lines). Review with: git diff -- $(AC_PATCH)"
