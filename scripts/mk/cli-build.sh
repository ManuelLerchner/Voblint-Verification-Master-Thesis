#!/usr/bin/env bash
# Builds the voblint CLI: a thin, unverified adapter over the
# Isabelle-generated Voblint_CLI OCaml module
# (src/Executable_Surface/Codegen/Export/Voblint_Codegen.thy's export_code
# block), plus the Menhir/ocamllex frontend generated from
# grammar/vimp.yaml (scripts/gen_vimp_menhir.py; only needed if that
# changed -- cli/vimp_parser.mly and cli/vimp_lexer.mll are committed).
# Requires dune + menhir + ocamllex + the zarith/unix OCaml libraries on PATH;
# does not require Isabelle or Python to build.
set -euo pipefail

# Property and smoke tests invoke this script directly from Pixi's Python
# environment. Always select the opam switch when one is available, avoiding
# accidental mixing with a different system OCaml installation.
if [ "${VOBLINT_OPAM_EXEC:-0}" != "1" ] && command -v opam >/dev/null 2>&1; then
  exec env VOBLINT_OPAM_EXEC=1 opam exec -- "$0" "$@"
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
CLI_DIR="$REPO_ROOT/cli"

# codegen/generated/ is a checked-in artifact, not rebuilt here (this script
# "does not require Isabelle" is load-bearing, see header) -- so warn if it
# doesn't correspond to the current .thy sources rather than silently
# compile-testing a stale copy left over from before a proof/definition fix.
# codegen-hash.sh defines "corresponds to" identically for both this check
# and the stamp regenerate-codegen.sh writes. Non-fatal: a stale stamp is
# common (e.g. git index state that doesn't reflect a just-regenerated
# codegen/), and blocking every voblint invocation on it is worse than
# occasionally compile-testing a stale copy -- run 'pixi run codegen' to
# clear the warning.
stamp="$REPO_ROOT/codegen/generated/.source-hash"
current_hash="$("$SCRIPT_DIR/codegen-hash.sh")"
if [ ! -f "$stamp" ] || [ "$(cat "$stamp")" != "$current_hash" ]; then
  echo "cli-build.sh: warning: codegen/generated/ is stale (or missing its .source-hash stamp)." >&2
  echo "Run 'pixi run codegen' to refresh it; building with the checked-in copy anyway." >&2
fi

# Dune owns generated OCaml, parser, and lexer outputs in `_build/`.
rm -f "$CLI_DIR/vimp_parser.ml" "$CLI_DIR/vimp_parser.mli" "$CLI_DIR/vimp_lexer.ml"

# `pixi run voblint` chains this build directly ahead of voblint's own
# stdout in the same pipe (e.g. `pixi run voblint -- --dot ... | dot
# -Tsvg`), so any build-tool banner on stdout here corrupts every piped
# consumer downstream -- ocamllex's automaton-stats banner was one such
# case. Dune is silent on success; assert the whole build
# stays silent (captured via a temp file, not `$()`, so a lone trailing
# blank line can't slip past an empty-string check) so a future regression
# here fails loudly at the source instead of corrupting output elsewhere.
build_out="$(mktemp)"
trap 'rm -f "$build_out"' EXIT
(
  cd "$CLI_DIR"
  dune build ./main.exe
  cp "$REPO_ROOT/_build/default/cli/main.exe" voblint
) >"$build_out"
if [ -s "$build_out" ]; then
  echo "cli-build.sh wrote to stdout (would corrupt piped voblint output):" >&2
  cat "$build_out" >&2
  exit 1
fi
