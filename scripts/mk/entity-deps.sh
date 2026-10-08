#!/usr/bin/env bash
# Export the statement-level entity dependency graph of every project theory
# into build/entity-deps/raw.json, on the built Voblint_Examples heap.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/require-afp.sh"
cd "$REPO_ROOT"
OUT="$REPO_ROOT/build/entity-deps"
python3 thesis/tools/entity_deps.py --export-theory "$OUT/Entity_Deps.thy"
"$ISABELLE" process_theories \
  -d "$AFP" \
  -d "$TD_DIR" \
  -d "$REPO_ROOT" \
  -l Voblint_Examples \
  -D "$OUT" \
  Entity_Deps
echo "wrote build/entity-deps/raw.json"
