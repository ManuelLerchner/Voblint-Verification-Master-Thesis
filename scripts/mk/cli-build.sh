#!/usr/bin/env bash
# Builds the voblint CLI: a thin, unverified adapter over the
# Isabelle-generated Voblint_CLI OCaml module
# (src/Examples/Tooling/Example_State_Report_GraphViz.thy's export_code
# block), plus the Menhir/ocamllex frontend generated from
# grammar/vimp.yaml (scripts/gen_vimp_menhir.py; only needed if that
# changed -- cli/vimp_parser.mly and cli/vimp_lexer.mll are committed).
# Requires ocamlfind + menhir + ocamllex + the zarith/unix findlib packages
# on PATH; does not require Isabelle or Python to build.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
CLI_DIR="$REPO_ROOT/cli"

# codegen/generated/ is a checked-in artifact, not rebuilt here (this script
# "does not require Isabelle" is load-bearing, see header) -- so verify it
# actually corresponds to the current .thy sources rather than silently
# compile-testing a stale copy left over from before a proof/definition fix.
# codegen-hash.sh defines "corresponds to" identically for both this check
# and the stamp regenerate-codegen.sh writes.
stamp="$REPO_ROOT/codegen/generated/.source-hash"
current_hash="$("$SCRIPT_DIR/codegen-hash.sh")"
if [ ! -f "$stamp" ] || [ "$(cat "$stamp")" != "$current_hash" ]; then
  echo "cli-build.sh: codegen/generated/ is stale (or missing its .source-hash stamp)." >&2
  echo "Run 'pixi run codegen' first, then retry." >&2
  exit 1
fi

# Copied in (not symlinked) so ocamlopt can infer the module name
# "Voblint_CLI" from the filename, matching codegen/regression/ocaml's own
# convention. Do not hand-edit the copy; rerun `pixi run codegen` and this
# script instead.
cp "$REPO_ROOT/codegen/generated/ml/Voblint_CLI.ml" "$CLI_DIR/Voblint_CLI.ml"

# `pixi run voblint` chains this build directly ahead of voblint's own
# stdout in the same pipe (e.g. `pixi run voblint -- --dot ... | dot
# -Tsvg`), so any build-tool banner on stdout here corrupts every piped
# consumer downstream -- ocamllex's automaton-stats banner was one such
# case. menhir/ocamlfind are silent on success; assert the whole build
# stays silent (captured via a temp file, not `$()`, so a lone trailing
# blank line can't slip past an empty-string check) so a future regression
# here fails loudly at the source instead of corrupting output elsewhere.
build_out="$(mktemp)"
trap 'rm -f "$build_out"' EXIT
(
  cd "$CLI_DIR"
  # --unused-precedence-levels: LT/EQEQ's %nonassoc level is real (the
  # Isabelle mixfix generator and the property-test printer both key off
  # grammar/vimp.yaml's precedence table for it) but VIMP comparisons don't
  # chain, so no shift/reduce conflict in Menhir's automaton ever consults
  # it -- an expected, not a signal-carrying, warning.
  menhir --unused-precedence-levels vimp_parser.mly
  # Its automaton-stats banner is routine, expected stdout on every
  # successful run -- redirect it inline so only genuinely unexpected
  # output from any step trips the silence assertion below.
  ocamllex vimp_lexer.mll >/dev/null
  # -8/-11/-20: routine artifacts of Isabelle's OCaml serializer (see
  # codegen/regression's regression.sh for the same suppression), not
  # signs of a real problem in the generated Voblint_CLI.ml.
  ocamlfind ocamlopt -w -8-11-20 -package str,zarith,unix -linkpkg \
    Voblint_CLI.ml vimp_parser.mli vimp_parser.ml vimp_lexer.ml vimp_frontend.ml main.ml -o voblint
) >"$build_out"
if [ -s "$build_out" ]; then
  echo "cli-build.sh wrote to stdout (would corrupt piped voblint output):" >&2
  cat "$build_out" >&2
  exit 1
fi
