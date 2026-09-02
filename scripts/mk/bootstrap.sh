#!/usr/bin/env bash
# Bootstrap: build the upstream sessions in topological order (fresh
# clone, no heaps), one target session per invocation so each session is
# validated only once its parents have heaps.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_VIMP
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_Domain
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_Solver
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_CFG
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_Framework
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_Compile
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_Exec
"$ISABELLE" build -v -N -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" Voblint_Analysis
