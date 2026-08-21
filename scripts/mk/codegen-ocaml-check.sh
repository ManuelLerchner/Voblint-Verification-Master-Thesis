#!/usr/bin/env bash
# Isabelle's own `checking OCaml` clause for the codegen export_code
# declarations (src/CodegenCheck/Voblint_OCaml_Check.thy). Kept out of the
# default build/codegen/codegen-check tasks: on Apple Silicon macOS,
# Isabelle's bundled opam (2.0.7) is x86_64-only, so its managed OCaml
# toolchain links against an x86_64 libgmp while the platform is arm64 --
# not a defect in the generated OCaml itself (see that theory's header
# comment). Run only in Linux CI, where this mismatch does not occur; run
# `isabelle ocaml_setup` first to provision the managed OCaml/zarith
# toolchain this depends on.
set -euo pipefail
source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/require-afp.sh"

# -d for the repository root, not -D, for the same reason
# scripts/regenerate-codegen.sh gives: -D selects every session it finds
# there, so this check would drag Voblint_Examples in behind it. Naming
# Voblint_OCaml_Check alone still builds its own dependency chain.
"$ISABELLE" build -v -d "$AFP" -d "$TD_DIR" -d "$REPO_ROOT" -d "$REPO_ROOT/src/CodegenCheck" Voblint_OCaml_Check
