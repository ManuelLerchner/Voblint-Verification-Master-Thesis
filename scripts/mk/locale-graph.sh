#!/usr/bin/env bash
# Regenerate thesis/shared/dot/locale_deps.dot from the built Voblint_Examples heap.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/require-afp.sh"
cd "$REPO_ROOT"
"$ISABELLE" process_theories \
  -d "$AFP" \
  -d "$TD_DIR" \
  -d "$REPO_ROOT" \
  -l Voblint_Examples \
  -D "$REPO_ROOT/thesis/tools" \
  Locale_Graph
echo "wrote thesis/shared/dot/locale_deps.dot"
