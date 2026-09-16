#!/usr/bin/env python3
"""Reports what an Isabelle build re-elaborated, and fails on a known regression.

A session inherits its *parent chain's* heaps and nothing else. A theory
imported from a session that is not an ancestor is re-elaborated from scratch
inside the importing session, once per importing session. Nothing about that is
visible in a build: it stays green, the session graph still looks right, and the
only symptom is the clock.

It cost this development 19% of a clean build. `HOL-Library` was elaborated 31
times across 8 sessions because `Voblint_VIMP` was parented on `HOL` with the
library merely beside it, and `TD.TD_side_upd_rule` -- one 2400-line theory --
6 times, because the two solver theories reaching it first appeared at the
`Analysis_*` layer, where five sibling domains cannot share a heap.

Two spellings fix it: make the library an ancestor (`Voblint_VIMP =
"HOL-Library"`), free when every session wants it; or build the theory into the
nearest common ancestor's heap with a qualified `theories` entry
(`"Voblint_Solver.TD_Solver_Bridge"` in `Voblint_Framework`), which costs one
elaboration and saves the rest.

This reads a build log rather than the sources, because whether a theory is
covered depends on the full import closure of every ancestor, including vendored
and distribution sessions -- `HOL-Library.Monad_Syntax` reaches `Voblint_Solver`
through `TD`'s heap, which no reading of this repository would reveal. The log
says what actually happened.

Produce a log with:

    isabelle build -v -o threads=12 -d $AFP -d vendor/td-verification -D . > build.log

Usage: python3 scripts/check_build_reelaboration.py build.log [--top N]
"""

import collections
import re
import sys

# Library sessions with their own heaps. Re-elaborating one is always waste:
# unlike a project session, nothing here is ours to restructure, and the fix is
# always ancestry. BUDGET is the number of elaborations tolerated -- the ones a
# hoist deliberately pays for, plus what is too small to be worth a session.
BUDGET = {
    "HOL-Library": 0,  # an ancestor since Voblint_VIMP = "HOL-Library"
    "TD": 8,  # Framework hoists the expensive ones; Domain keeps two (~8s)
    "HOL-Computational_Algebra": 2,  # hoisted into Voblint_Nonrelational
    "Deriving": 8,  # 8 tiny theories, ~3s total, one user
    "HOL-IMP": 1,  # one theory, under a second
}

LINE = re.compile(r"(\S+): theory (\S+)\.(\S+) 100% \(([\d.]+)s cumulated time\)")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    top = 10
    if "--top" in sys.argv:
        top = int(sys.argv[sys.argv.index("--top") + 1])
    if not args:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2

    per_lib = collections.Counter()
    lib_cost = collections.defaultdict(float)
    per_thy = collections.defaultdict(list)
    total = 0.0
    for line in open(args[0], errors="replace"):
        m = LINE.search(line)
        if not m:
            continue
        builder, owner, thy, secs = (
            m.group(1),
            m.group(2),
            m.group(3),
            float(m.group(4)),
        )
        total += secs
        if builder == owner:
            continue
        per_thy[(owner, thy)].append(secs)
        if owner in BUDGET or not owner.startswith("Voblint_"):
            per_lib[owner] += 1
            lib_cost[owner] += secs

    if not per_thy and total == 0.0:
        # An incremental build that rebuilt nothing has no theory lines, so the
        # budgets below would pass without having looked at anything. Say so:
        # the deciding run is a clean build (CI's html job), not this one.
        print(
            f"{args[0]} has no theory elaboration lines -- nothing was rebuilt, "
            "so this run proves nothing. A clean build (isabelle build -c) is "
            "what exercises the budgets."
        )
        return 0

    waste = sorted(
        (
            (sum(v) - min(v), o, t, len(v))
            for (o, t), v in per_thy.items()
            if len(v) > 1
        ),
        reverse=True,
    )
    print(f"re-elaboration in {args[0]} ({total / 3600:.1f}h of theory elaboration)\n")
    print(f"{'theory':<52}{'x':>3}{'wasted':>9}")
    for w, o, t, c in waste[:top]:
        print(f"{o + '.' + t:<52}{c:>3}{w:>8.0f}s")
    print(f"\ntotal re-elaboration waste: {sum(w for w, _, _, _ in waste):.0f}s\n")

    problems = []
    print(f"{'library session':<30}{'elaborations':>13}{'budget':>8}{'cpu':>9}")
    for lib in sorted(set(BUDGET) | set(per_lib)):
        n, budget = per_lib[lib], BUDGET.get(lib, 0)
        flag = "" if n <= budget else "   <-- REGRESSION"
        print(f"{lib:<30}{n:>13}{budget:>8}{lib_cost[lib]:>8.0f}s{flag}")
        if n > budget:
            problems.append(
                f"{lib}: {n} elaborations inside project sessions, budget {budget} "
                f"({lib_cost[lib]:.0f}s cpu). Make it an ancestor, or build the theory "
                f"into the nearest common ancestor's heap with a qualified `theories` entry."
            )
    if problems:
        print(file=sys.stderr)
        for p in problems:
            print(p, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
