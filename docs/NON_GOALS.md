# Non-goals

The following claims are outside the supported framework.

- No root-level return. Main terminates only by fall-through.
- No semantic completeness claim. The analyzer over-approximates concrete
  executions.
- No Retain analysis. Its routing discipline differs from the supported D/G
  interface, and no equivalence theorem is claimed.
- No plain top-down solver pipeline. Executable analyses use the side-effecting
  verified solver.
- No parallel classical intra-procedural pipeline.
- No unconditional termination proof. Soundness theorems are conditional on
  the explicit `solve_dom`/`side_solve_dom` hypothesis; discharging that
  hypothesis (e.g. via lattice-height induction for Sign, or a widening
  termination argument for Interval) is out of scope.
- No generic reduced-product constructor. The mixed Sign/Interval instance is a
  concrete D/G analysis.
- No guarantee that every abstract context choice is finite or precise.
- No implicit arrays, pointers, heap, C, or CIL semantics.
- No backward compiler equivalence. The source compiler theorem is a forward
  simulation sufficient for soundness.
- No claim that demand-cone coverage changes the concrete CFG semantics.
- No theorem about external analyzer implementations unless a separate
  correspondence proof is supplied.
- No general `DefExc`/exclusion-set `int_dom` component. A persistent,
  join-surviving "exclude an arbitrary literal" fact over unbounded `int`
  cannot satisfy `bounded_semilattice_sup_bot` -- proved infeasible, not
  merely undone (`docs/GOBLINT_ALIGNMENT_REGISTER.md`, Value domains row,
  issue #162).
