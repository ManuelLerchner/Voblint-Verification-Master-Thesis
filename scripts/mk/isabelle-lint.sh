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
SESSIONS="$(bash "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/sessions.sh" | tr '\n' ' ')"

# Install only when the tool is missing. Registering a second copy alongside a
# hand-installed one makes every later `isabelle` invocation die with
# "Duplicate declaration of option lint_bundles" -- including invocations that
# have nothing to do with linting, since the components list is global and
# persistent. In fresh CI this branch always runs.
# `isabelle lint -?` prints usage and exits non-zero, so capture rather than
# pipe: under `set -o pipefail` the tool's own exit status would sink the
# pipeline and the test would always say "missing".
linter_help="$("$ISABELLE" lint -? 2>&1 || true)"
case "$linter_help" in
  *"Usage: isabelle lint"*) ;;
  *)
    test -d "$LINTER_DIR" || git clone --depth 1 --branch "$LINTER_TAG" https://github.com/isabelle-prover/isabelle-linter "$LINTER_DIR"
    "$ISABELLE" components -u "$LINTER_DIR/linter_base"
    ;;
esac
"$ISABELLE" lint -v -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" -o lint_bundles=default,afp_mandatory -f error $SESSIONS
