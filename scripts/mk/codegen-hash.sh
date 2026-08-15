#!/bin/sh
# Prints one hash of codegen's actual inputs: every .thy under src/ (the
# Voblint_Codegen session's dependency closure, which extends the six-session
# chain, is what regenerate-codegen.sh builds and exports), every ROOT/ROOTS
# session-structure file, and the two generation scripts themselves. Shared
# by regenerate-codegen.sh (writes the stamp) and cli-build.sh (checks it) so
# the two can never define "codegen's inputs" differently.
#
# Hashes source text, not proof outcomes: a comment or proof-only edit still
# changes the hash even though it can't change generated OCaml. A false
# "stale" is a wasted `pixi run codegen`; a false "fresh" would silently
# compile-test old generated code against new source, the actual failure
# mode this guards against -- so the safe direction to err is deliberate.
set -eu

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"

if command -v sha256sum >/dev/null 2>&1; then
  HASH() { sha256sum; }
else
  HASH() { shasum -a 256; }
fi

# Relative paths only: an absolute checkout path (this machine's vs. CI's
# /__w/...) must never leak into the hash, or the same source tree hashes
# differently on every machine that checks it out.
cd "$REPO_ROOT"
{
  find src \( -name '*.thy' -o -name 'ROOT' \) -type f
  printf '%s\n' ROOTS scripts/regenerate-codegen.sh scripts/mk/codegen.sh
} | LC_ALL=C sort | while IFS= read -r f; do
  HASH <"$f" | awk -v f="$f" '{print $1, f}'
done | HASH | awk '{print $1}'
