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

## Research-gap items classified out of scope (2026-07 audit)

Reconciled from the *Second-Pass Research-Gap Audit*. Items the audit surfaced that are
**deliberately not** on the critical path — the in-scope reconciled milestones (T1, A1, A2, E1,
E2, P1–P3, G1) live in `docs/ROADMAP.md` "Research-gap reconciliation".

- **No broad generic solver-totality theorem** (finite-height + monotone ⇒ terminates, for an
  arbitrary domain/update rule). The vendor proves termination only for the plain / warrow / wn
  solvers (`TD_*_term`), each demanding a finite unknown *type*; there is no `TD_side_term`. The
  narrow Sign instance (T1) is tracked, gated on P5; the *general* theorem is a stretch, not a
  goal. See `docs/ROADMAP.md` "Total correctness".
- **No constant-propagation or taint analysis.** Faithfulness breadth only. Taint additionally
  needs the inter-analysis query gap (`docs/GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`, Gap 7a), itself
  out of scope. Not a critical-path deliverable.
- **Benchmarks are not a verification goal.** Framework-effort evaluation (G1) is a
  publication/evaluation task, not a proof obligation — recorded so it is not silently omitted,
  but it does not gate any soundness claim.

*Not* non-goals (moved onto the tracked backlog, listed here to prevent re-litigation): **Parity**
is now the preferred second finite-height validation instance (ROADMAP E1); the **non-exit query
witness** (E2) and the **bundled run-analysis theorem** (A1) are near-term thesis items.

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
