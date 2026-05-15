#!/usr/bin/env bash
# Build and install the Isabelle/Q (I/Q) jEdit plugin from the vendored
# AutoCorrode checkout in ir-repo/iq/.
#
# Run this once after `git submodule update --init` (or after the I/Q
# sources change in ir-repo). Installs the JAR to
# ~/.isabelle/Isabelle2025-2/jedit/jars/iq_plugin.jar.
#
# Requires Isabelle2025-2 installed (override with ISABELLE_HOME).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IQ_DIR="$SCRIPT_DIR/ir-repo/iq"

if [[ ! -d "$IQ_DIR" ]]; then
  echo "ERROR: I/Q sources not found at '$IQ_DIR'." >&2
  echo "  Expand the ir-repo sparse-checkout to include /iq/:" >&2
  echo "    printf '/*\\n!/*/\\n/ir/\\n/iq/\\n' > ir-repo/.git/info/sparse-checkout" >&2
  echo "    (cd ir-repo && git read-tree -mu HEAD)" >&2
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
