#!/usr/bin/env bash
# Format OCaml sources and dune files through dune's @fmt alias, or with
# --check report the diff without changing anything. .ocamlformat pins the
# ocamlformat version; .ocamlformat-ignore excludes generated and vendored
# sources.
set -euo pipefail

if [ "${VOBLINT_OPAM_EXEC:-0}" != "1" ] && command -v opam >/dev/null 2>&1; then
  exec env VOBLINT_OPAM_EXEC=1 opam exec -- "$0" "$@"
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/../.."

if [ "${1:-}" = "--check" ]; then
  exec dune build @fmt
fi

# Explicit paths, as the pre-commit hook passes its staged files. ocamlformat
# honours .ocamlformat-ignore for them; dune files go through dune's formatter.
# Any other path is skipped: the hook's glob can match Isabelle/ML sources
# (*.ML) on a case-insensitive file system, and format-dune-file would read them
# as S-expressions. dune-project is left to the check, since format-dune-file
# separates its stanzas with blank lines that @fmt does not ask for.
if [ "$#" -gt 0 ]; then
  for path in "$@"; do
    case "$path" in
      *.ml | *.mli) ocamlformat -i "$path" ;;
      dune | */dune)
        formatted="$(dune format-dune-file "$path")"
        printf '%s\n' "$formatted" >"$path"
        ;;
    esac
  done
  exit 0
fi

# `dune fmt` promotes the formatted files but still exits non-zero when it
# changed any, so a second pass decides success.
dune fmt >/dev/null 2>&1 || dune build @fmt
