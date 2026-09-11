#!/usr/bin/env bash
# One-shot bootstrap:
#   - init the td-verification submodule
#   - install a pinned local AutoCorrode checkout under vendor/ (ir/, iq/)
#     and register its I/Q component in Isabelle's user configuration
#   - install the pixi environment, the voblint.opam OCaml dependencies, and
#     the lefthook git hooks
#   - build + install the I/Q jEdit plugin (skip with --no-iq)
#
# Re-run safe. An existing AutoCorrode checkout is never reset or updated.

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
AUTOCORRODE_URL="https://github.com/awslabs/AutoCorrode"
AUTOCORRODE_REV="${AUTOCORRODE_REV:-eccf4feac0b813ab420e7c12fa694f32383ab4ad}"
AC_DIR="${AUTOCORRODE_HOME:-$REPO_ROOT/vendor/autocorrode}"

echo "Initializing the TD solver submodule ..."
git -C "$REPO_ROOT" submodule update --init vendor/td-verification

echo "Installing AutoCorrode developer tooling ..."
if [[ ! -e "$AC_DIR/.git" ]]; then
  mkdir -p "$(dirname "$AC_DIR")"
  git clone --filter=blob:none --no-checkout "$AUTOCORRODE_URL" "$AC_DIR"
  git -C "$AC_DIR" sparse-checkout init --cone
  git -C "$AC_DIR" sparse-checkout set ir iq
  git -C "$AC_DIR" checkout --detach "$AUTOCORRODE_REV"
else
  actual_rev="$(git -C "$AC_DIR" rev-parse HEAD)"
  if [[ "$actual_rev" != "$AUTOCORRODE_REV" ]]; then
    echo "ERROR: AutoCorrode at '$AC_DIR' is checked out at $actual_rev." >&2
    echo "  Expected pinned revision: $AUTOCORRODE_REV" >&2
    echo "  Existing tool checkouts are never reset automatically." >&2
    exit 1
  fi
fi

export ISABELLE_HOME="${ISABELLE_HOME:-/Applications/Isabelle2025-2.app}"
ISABELLE="${ISABELLE:-$ISABELLE_HOME/bin/isabelle}"
if [[ ! -x "$ISABELLE" ]]; then
  echo "ERROR: Isabelle binary not found at '$ISABELLE'." >&2
  exit 1
fi

echo "Registering the I/Q component in Isabelle's user configuration ..."
"$ISABELLE" components -u "$AC_DIR/iq"

echo "Installing pixi and OCaml environments ..."
(
  cd "$REPO_ROOT"
  pixi install
  pixi run ocaml-deps-install
  pixi run hooks-install
)

if [[ "$WITH_IQ" == "1" ]]; then
  echo
  echo "Building + installing the I/Q jEdit plugin ..."

  IQ_DIR="$AC_DIR/iq"
  if [[ ! -d "$IQ_DIR" ]]; then
    echo "ERROR: I/Q sources not found at '$IQ_DIR' (sparse-checkout failed?)." >&2
    exit 1
  fi

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
