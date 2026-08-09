#!/usr/bin/env bash
# `pixi run voblint -- --dot|--graph-snapshot ...` chains cli-build as a
# dependency ahead of the CLI's own machine-readable stdout, in the same
# pipe -- a build step that writes anything to stdout on success (menhir,
# ocamllex, ocamlopt are all normally silent, but a regression here is easy
# to miss locally since it only breaks piped consumers, e.g. `| dot
# -Tsvg`) would land in front of voblint's own output and corrupt it.
# Asserts scripts/mk/cli-build.sh is silent on stdout, not just that
# voblint's own output happens to start correctly -- catches the
# contamination at its source instead of downstream in every consumer.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

out="$("$SCRIPT_DIR/cli-build.sh")"
if [ -n "$out" ]; then
  echo "cli-build.sh wrote to stdout (would corrupt piped voblint output):" >&2
  echo "$out" >&2
  exit 1
fi
