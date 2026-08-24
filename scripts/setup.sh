#!/usr/bin/env bash
# One-shot bootstrap:
#   - init submodules (autocorrode, td-verification)
#   - sparse-checkout autocorrode (ir/, iq/)
#   - apply the td-verification patch
#   - install the pixi environment (I/R's Python deps, grammar generators,
#     property-test suite, lefthook) and the lefthook git hooks
#   - build + install the I/Q jEdit plugin (skip with --no-iq)
#
# Re-run safe. vendor/autocorrode is a plain git submodule: bump it with
# git commands in that directory, not with a pixi task.

set -euo pipefail

WITH_IQ=1
for arg in "$@"; do
  case "$arg" in
    --no-iq) WITH_IQ=0 ;;
    -h|--help)
      echo "Usage: $0 [--no-iq]"
      echo "  --no-iq   Skip building/installing the jEdit I/Q plugin."
      exit 0
      ;;
    *) echo "ERROR: unknown arg '$arg'" >&2; exit 1 ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
AC_DIR="$REPO_ROOT/vendor/autocorrode"

echo "Initializing submodules ..."
git -C "$REPO_ROOT" submodule update --init vendor/autocorrode vendor/td-verification

echo "Applying td-verification patch (via pixi run vendor) ..."
( cd "$REPO_ROOT" && pixi run vendor )

echo "Configuring sparse-checkout (ir/, iq/) ..."
git -C "$AC_DIR" sparse-checkout init --cone
git -C "$AC_DIR" sparse-checkout set ir iq

echo "Installing pixi environment (see pixi.toml) ..."
( cd "$REPO_ROOT" && pixi install && pixi run lefthook-install )

if [[ "$WITH_IQ" == "1" ]]; then
  echo
  echo "Building + installing the I/Q jEdit plugin ..."

  IQ_DIR="$AC_DIR/iq"
  if [[ ! -d "$IQ_DIR" ]]; then
    echo "ERROR: I/Q sources not found at '$IQ_DIR' (sparse-checkout failed?)." >&2
    exit 1
  fi

  export ISABELLE_HOME="${ISABELLE_HOME:-/Applications/Isabelle2025-2.app}"
  if [[ ! -d "$ISABELLE_HOME" ]]; then
    echo "ERROR: Isabelle not found at '$ISABELLE_HOME'." >&2
    echo "  Set ISABELLE_HOME=/path/to/Isabelle2025-2.app and retry," >&2
    echo "  or rerun with --no-iq to skip the jEdit plugin install." >&2
    exit 1
  fi

  ( cd "$IQ_DIR" && make install )

  echo
  echo "Done. Next steps:"
  echo "  - GUI:      ./scripts/start-iq.sh    (jEdit + I/Q, port 8765)"
  echo "  - Headless: ./scripts/start-ir.sh    (REPL MCP, port 9148)"
  echo "  - Both:     ./scripts/start-both.sh"
  echo "  - MCP token: 'isabelle-local' (matches .mcp.json)"
else
  echo
  echo "Done (skipped I/Q plugin). Next: ./scripts/start-ir.sh"
fi
