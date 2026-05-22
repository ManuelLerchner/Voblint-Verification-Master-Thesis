ISABELLE        ?= isabelle
AFP             ?= $(HOME)/afp/thys
SESSION         := Goblint_Formalization

TD_DIR          := vendor/td-verification
TD_PATCH        := vendor/td-verification.patch

AC_DIR          := vendor/autocorrode
AC_PATCH        := vendor/autocorrode.patch

.PHONY: all vendor build jedit clean clean-vendor update-autocorrode refresh-autocorrode-patch refresh-td-patch

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

# Build the project session. Depends on vendored TD solver.
build: vendor
	@test -d $(AFP) || { echo "ERROR: AFP not found at $(AFP). Set AFP=<path> or install AFP."; exit 1; }
	$(ISABELLE) build -d $(AFP) -d $(TD_DIR) -D . $(SESSION)

# Launch jEdit with the right session roots loaded.
jedit: vendor
	$(ISABELLE) jedit -d $(AFP) -d $(TD_DIR) -d .

# Discard local TD patch + working-tree edits (the submodule itself stays
# initialized; rerun `make vendor` to reapply the patch).
clean-vendor:
	git -C $(TD_DIR) reset --hard HEAD

clean:
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

# Same, for td-verification.
refresh-td-patch:
	git -C $(TD_DIR) --no-pager diff > $(TD_PATCH)
	@echo "Wrote $(TD_PATCH) ($$(wc -l < $(TD_PATCH)) lines). Review with: git diff -- $(TD_PATCH)"
