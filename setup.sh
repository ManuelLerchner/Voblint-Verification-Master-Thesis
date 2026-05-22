#!/usr/bin/env bash
# Initialize the AutoCorrode submodule (vendor/autocorrode/), restrict it to
# ir/ + iq/ via sparse-checkout, apply our local patch, and install the
# Python venv for the I/R MCP daemon.
#
# Re-run safe. To bump to a newer upstream commit, use:  make update-autocorrode

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AC_DIR="$SCRIPT_DIR/vendor/autocorrode"
PATCH="$SCRIPT_DIR/vendor/autocorrode.patch"

echo "Initializing vendor/autocorrode submodule ..."
git -C "$SCRIPT_DIR" submodule update --init vendor/autocorrode

echo "Configuring sparse-checkout (ir/, iq/) ..."
git -C "$AC_DIR" sparse-checkout init --cone
git -C "$AC_DIR" sparse-checkout set ir iq

if [[ -s "$PATCH" ]]; then
  if git -C "$AC_DIR" apply --check "$PATCH" 2>/dev/null; then
    echo "Applying vendor/autocorrode.patch ..."
    git -C "$AC_DIR" apply "$PATCH"
  elif git -C "$AC_DIR" apply --check --reverse "$PATCH" 2>/dev/null; then
    echo "vendor/autocorrode.patch already applied, skipping."
  else
    echo "ERROR: vendor/autocorrode.patch does not apply cleanly." >&2
    echo "  Inspect with:  git -C $AC_DIR apply --check $PATCH" >&2
    echo "  After resolving, refresh the patch with:  make refresh-autocorrode-patch" >&2
    exit 1
  fi
fi

echo "Installing Python requirements into venv ..."
python3 -m venv "$SCRIPT_DIR/.venv"
"$SCRIPT_DIR/.venv/bin/pip" install -r "$AC_DIR/ir/requirements.txt"

echo ""
echo "Done. Start the daemon with:  ./start-ir.sh"
echo "Install the I/Q jEdit plugin with:  ./setup-iq.sh"
