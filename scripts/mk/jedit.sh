#!/usr/bin/env bash
# Launch jEdit with the right session roots loaded.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

"$ISABELLE" jedit -d "$AFP" -d "$TD_DIR" -d "$REPO_ROOT"
