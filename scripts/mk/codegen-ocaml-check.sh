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

"$ISABELLE" build -v -d "$AFP" -d "$TD_DIR" -D "$REPO_ROOT" -d "$REPO_ROOT/src/CodegenCheck" Voblint_OCaml_Check
