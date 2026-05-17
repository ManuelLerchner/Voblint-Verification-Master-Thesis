ISABELLE        ?= isabelle
AFP             ?= $(HOME)/afp/thys
SESSION         := Goblint_Formalization

TD_URL          := https://github.com/stilscher/td-verification
TD_COMMIT       := af78761e62c28bf299863b5735c32b7c2cfcd93e
TD_DIR          := vendor/td-verification
TD_PATCH        := vendor/td-verification.patch

.PHONY: all vendor build jedit clean-vendor clean

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
