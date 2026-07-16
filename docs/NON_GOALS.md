# Non-Goals

What this project deliberately does **not** do. Each entry is grounded in a
decision doc so it stops being re-litigated every session. Goals and the live
backlog live in `docs/ROADMAP.md`; this file is only the "not doing" half.

## Scope of the verification

- **No `alpha` / best-abstraction.** Domains use semantic `gamma`-axioms
  (`sound_domain`) only. Soundness needs `gamma` alone. The claim is *strict
  improvement*, not *optimality* — an optimality claim would make `alpha`
  load-bearing. See `docs/THESIS_SCOPE_MEMO.md`.
- **No total-correctness / termination of the solver.** P1 keeps `solve_dom` as
  an explicit, documented TD hypothesis rather than proving the solver
  terminates. See `docs/P1_TOTAL_CORRECTNESS_ROUTE.md`.
- **No octagon / relational domain (for now).** Scope A (sign + interval, trace
  pivot, precision) is the defensible thesis. Octagon is acknowledged future
  work with no Isabelle prior art and from-scratch DBM closure proofs — reopen
  only on explicit go. See `docs/THESIS_SCOPE_MEMO.md`, `docs/RELATIONAL_DOMAIN_PLAN.md`.

## Solver and spine

- **No plain top-down solver.** `TD.TD_plain` and its spine were retired; the
  analysis rides only on `TD.TD_side`. See `docs/TD_SIDE_ONLY_MIGRATION.md`.
- **No intra-procedural (classical) analysis spine in this repo.** The
  intra-only top layer (`TD_Soundness`, intra `Sign`/`Interval`, `Pipeline`,
  intra examples) was extracted to the sibling repo
  `voblint-formalization-classical` and removed here. The intra *substrate*
  (`cfg_collect`, collecting layer) stays — it is load-bearing for the IP/Side
  spine. See `docs/CLASSICAL_SPINE_RETIREMENT.md`, `docs/IP_ONLY_CONSOLIDATION.md`.
- **No `Direct_Equations` layer.** The CFG layer won; direct equations were
  deleted as off-path.

## Language and tooling

- **Not re-deriving HOL-IMP.** Built on `HOL-IMP` (`Com`, `Big_Step`); IMP2 is
  the surface. No fresh operational semantics from scratch.
- **No C/CIL memory semantics in the current scope.** IMP2 has no addresses,
  pointer aliasing, heap allocation, or C front-end translation theorem. Array
  syntax is a separate deferred extension; see
  `docs/ARRAY_SYNTAX_EXTENSION.md` and
  `docs/GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`.
- **No new solver.** The TD solver is vendored and already verified
  (`stilscher/td-verification`); it is not re-proved here.
- **No unicode in `.thy` sources.** ASCII Isabelle tokens only — batch build
  rejects unicode outside comments. (Tooling constraint, not a research scope
  limit; see `CLAUDE.md`.)
