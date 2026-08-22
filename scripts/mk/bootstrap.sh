#!/usr/bin/env bash
# Bootstrap: build all 5 upstream sessions in topological order (fresh
# clone, no heaps). Uses -d (not -D) per session to avoid validating
# downstream sessions before upstream heaps exist.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -d "$REPO_ROOT/src/VIMP" Voblint_VIMP
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -d "$REPO_ROOT/src/VIMP" -d "$REPO_ROOT/src/CFG" Voblint_CFG
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -d "$REPO_ROOT/src/VIMP" -d "$REPO_ROOT/src/CFG" -d "$REPO_ROOT/src/Core" Voblint_Core
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -d "$REPO_ROOT/src/VIMP" -d "$REPO_ROOT/src/CFG" -d "$REPO_ROOT/src/Core" -d "$REPO_ROOT/src/Analysis" Voblint_Analysis
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_Soundness
