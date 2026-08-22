#!/usr/bin/env bash
# Style-lint our own sessions with the community isabelle-linter
# (https://github.com/isabelle-prover/isabelle-linter). Installs the
# CLI-only component on first run (cached across runs under LINTER_DIR);
# reuses whatever heaps are already built, so run this after `build`/`html`
# in the same environment rather than cold. -f error fails on any
# error-severity finding -- notably unfinished_proof (sorry/<proof>) and the
# rest of the afp_mandatory bundle.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

LINTER_DIR="${LINTER_DIR:-/tmp/isabelle-linter}"
LINTER_TAG="Isabelle2025-2-v1.0.0"
SESSIONS="Voblint_VIMP Voblint_CFG Voblint_Core Voblint_Analysis Voblint_Soundness Voblint_Examples"

test -d "$LINTER_DIR" || git clone --depth 1 --branch "$LINTER_TAG" https://github.com/isabelle-prover/isabelle-linter "$LINTER_DIR"
"$ISABELLE" components -u "$LINTER_DIR/linter_base"
"$ISABELLE" lint -v -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" -o lint_bundles=default,afp_mandatory -f error $SESSIONS
