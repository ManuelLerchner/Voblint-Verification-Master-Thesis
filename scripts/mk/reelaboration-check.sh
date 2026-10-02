#!/usr/bin/env bash
# Report what an `isabelle build -v` log re-elaborated, and fail when a library
# session exceeds its budget.
#
# A session inherits its parent chain's heaps and nothing else: a theory of a
# library session that is no ancestor is re-elaborated inside every session
# that imports it. The build stays green; only the clock shows it (19% of a
# clean build once). Every library session not listed below gets 0, so a new
# one slipping in fails. The fix is ancestry, or building the theory into the
# nearest common ancestor's heap with a qualified `theories` entry.
#
# A log that rebuilt nothing proves nothing and passes (--allow-empty); CI's
# html job does a clean build.
set -euo pipefail

log="${1:-build/isabelle-build.log}"

# HOL-Library                0  an ancestor since Voblint_VIMP = "HOL-Library"
# TD                         8  Framework hoists the expensive ones; Domain keeps two (~8s)
# HOL-Computational_Algebra  2  hoisted into Voblint_VIMP
# Deriving                   8  8 tiny theories, ~3s total, one user
# HOL-IMP                    1  one theory, under a second
# Root_Balanced_Tree         1  Time_Monad, inside TD itself when TD is rebuilt
exec isar stats build "$log" \
  --budget HOL-Library=0 \
  --budget TD=8 \
  --budget HOL-Computational_Algebra=2 \
  --budget Deriving=8 \
  --budget HOL-IMP=1 \
  --budget Root_Balanced_Tree=1 \
  --default-budget 0 \
  --project . \
  --allow-empty
