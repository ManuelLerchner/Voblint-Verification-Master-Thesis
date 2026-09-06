#!/usr/bin/env bash
# Bootstrap: build the upstream sessions in topological order (fresh
# clone, no heaps), one target session per invocation so each session is
# validated only once its parents have heaps.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"
# ROOTS order is topological, so building in it never asks for a heap that
# does not exist yet.  The example and codegen leaves are left to `build`.
while read -r session; do
  case "$session" in Voblint_Examples*|Voblint_Codegen) continue ;; esac
  "$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" "$session"
done < <(bash "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/sessions.sh")
