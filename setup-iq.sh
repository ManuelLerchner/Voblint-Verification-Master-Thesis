#!/usr/bin/env bash
# Build and install the Isabelle/Q (I/Q) jEdit plugin from the vendored
# AutoCorrode checkout in vendor/autocorrode/iq/.
#
# Run this once after `git submodule update --init` (or after the I/Q
# sources change in vendor/autocorrode). Installs the JAR to
# ~/.isabelle/Isabelle2025-2/jedit/jars/iq_plugin.jar.
#
# Requires Isabelle2025-2 installed (override with ISABELLE_HOME).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IQ_DIR="$SCRIPT_DIR/vendor/autocorrode/iq"

if [[ ! -d "$IQ_DIR" ]]; then
  echo "ERROR: I/Q sources not found at '$IQ_DIR'." >&2
  echo "  Run ./setup.sh first (initializes vendor/autocorrode submodule with sparse-checkout ir/+iq/)." >&2
  exit 1
fi

export ISABELLE_HOME="${ISABELLE_HOME:-/Applications/Isabelle2025-2.app}"

if [[ ! -d "$ISABELLE_HOME" ]]; then
  echo "ERROR: Isabelle not found at '$ISABELLE_HOME'." >&2
  echo "  Set ISABELLE_HOME=/path/to/Isabelle2025-2.app and retry." >&2
  exit 1
fi

cd "$IQ_DIR"
make install

echo
echo "Done. Next steps:"
echo "  1. Start jEdit:     ./start-iq.sh"
echo "  2. Verify:          Utilities -> Plugin Manager -> I/Q Plugin (active)"
echo "  3. MCP token:       'isabelle-local' (matches .mcp.json IQ_AUTH_TOKEN)"
