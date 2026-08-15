# Check-discharge architecture

Overview of how a compiled `__voblint_check(...)` condition becomes both a
GraphViz-rendered proof status and a semantic soundness guarantee. This is
a map of responsibilities across layers, not a proof-status inventory —
proof status lives in the `.thy` files themselves (`docs/PROOF_PHASES.md`).

## Pipeline

`abstract_check_domain` produces two independent outputs from the same
node-indexed abstract environment: an *executable classification* that
GraphViz renders directly, and a *logical discharge* that `checks_proven`
turns into a semantic guarantee. GraphViz never consumes `checks_proven`
— rendering does not depend on proving anything.

```text
VIMP source
    |
    | compile_prog (VIMP_Proc_to_CFG)
    v
CFG + checks : (pp * bexp) set     -- zero or more compiled checks per node
    |
    | verified TD solver, per domain (Sign_Exec_Sound / Interval_Exec_Sound)
    v
node-indexed abstract environment  -- <domain>_exec_prog_at :: pname -> imp_prog -> pp -> 'a abs_state
    |
    | domain-specific abstract_numeric_queries instance
    v
abstract_check_domain (Abstract_Checks.thy)
    |
    +--> classify_check                              [executable]
    |        |
    |        v
    |    Check_Proved / Check_Refuted / Check_Unknown
    |        |
    |        v
    |    check_result_annotation (Analysis_GraphViz.thy)
    |        |
    |        v
    |    rendered CFG, proof status as node color
    |
    +--> abstract_checks_proven                       [proposition]
             |
             | node-local collecting soundness
             v
         checks_proven (Checks.thy, domain-independent)
             |
             v
         concrete stores satisfy every selected check
```

The check-classification and discharge layers above the node-indexed
solver state are domain-generic; each domain supplies its own solver
frontend and `abstract_numeric_queries` instance below that line.
`Sign_Checks.thy` and `Interval_Checks.thy` are thin instantiations of the
generic layers, not separate implementations of the pipeline.

## Layer responsibilities

### `Abstract_Domain.thy` — lattice and backward refinement

Owns `sound_domain`/`abstract_domain` (the type-class every domain value
type instantiates), `semantic_intersection`, `backward_domain` (guard narrowing: `inv_less`,
`inv_eq`, `afilter`/`bfilter`), and `backward_domain_mono`. Nothing here
knows about checks. `derived_less_queries`/`derived_eq_true_from_less`/
`derived_eq_false_from_intersection` do **not** live here — see the next layer.

### `Abstract_Numeric_Queries.thy` — atomic-value entailment/refutation

Owns the `abstract_numeric_queries` locale (`less_true`, `less_false`,
`eq_true`, `eq_false` over one abstract value + four soundness
assumptions) and its generic derivation from any `backward_domain`
instance's own narrowing operators. The derivation locales are registered
as sublocales of the backward capability hierarchy, precisely:

```text
backward_domain -> derived_less_queries -> derived_eq_true_from_less
backward_domain -> derived_eq_false_from_intersection
```

(`derived_eq_true_from_less` sublocales under `derived_less_queries`, not
directly under `backward_domain`; `derived_eq_false_from_intersection`
sublocales under `backward_domain` directly, reusing its own
`intersect_sound` premise.)
A concrete `backward_domain` interpretation inherits all four query
functions with no extra proof obligation *once `Abstract_Numeric_Queries.thy`
is in scope at the point that interpretation is processed* — `Sign_Backward.thy`
needed an explicit import added for exactly this reason (see below).

The derivation is a **sound default, not a mandatory implementation**.
`sublocale backward_domain \<subseteq> abstract_numeric_queries` was deliberately
never added — see "Why no automatic sublocale" below.

### `Abstract_Checks.thy` — expression/check evaluation

Owns `abstract_expression_domain` (adds `gamma_state`/`aval_abs` on top of
the numeric queries) and `abstract_check_domain` (mutually recursive
`check_true`/`check_false` over `bexp`, the three-way `classify_check`,
and `abstract_checks_proven`, the node-indexed bridge to
`Checks.thy`'s domain-independent `checks_proven`).

`Check_Proved`/`Check_Refuted` are universal claims over the abstract
value's whole concretization, not witness-based: `Check_Refuted` means
every concrete state the abstract state represents falsifies the
condition, not that one counterexample was found. `Check_Unknown` means
neither `check_true` nor `check_false` could be established — the
condition may in fact always hold, always fail, or vary; the classifier
makes no claim either way.

### Per-domain instances

`Sign_Checks.thy` and `Interval_Checks.thy` each do one
`global_interpretation abstract_check_domain ...`, `defines`-exporting
`<domain>_check_true`/`<domain>_classify_check`/`<domain>_checks_proven`.
Neither restates the Boolean recursion, the classification logic, or the
`checks_proven` bridge — that would be duplicating what `Abstract_Checks.thy`
already proves once.

They differ only in **which four query functions they feed in**:

| | Sign (`Sign_Checks.thy`) | Interval (`Interval_Checks.thy`) |
| --- | --- | --- |
| `less_true`/`less_false` | derived from `inv_less_sign` | specialized, compares interval bounds directly |
| `eq_true`/`eq_false` | derived from `sign_less_false` / semantic intersection (`meet_sign`) | specialized, compares interval bounds directly |
| Source | `Sign_Numeric_Queries.thy` | `Interval_Numeric_Queries.thy` |

### Solver frontends: `Sign_Exec_Sound.thy` / `Interval_Exec_Sound.thy`

Domain-specific, not domain-generic: each provides
`<domain>_exec_prog_at :: pname -> imp_prog -> pp -> 'a abs_state`, a
node-parametric query into *that domain's own* computed post-solution,
plus `<domain>_exec_prog_sound_collecting_at` connecting it back to
`ltr_collect` at *any* reachable node — not only the solver's own query
seed (`cfg_exit`). The computed environment and transfer soundness are
necessarily per-domain; what both instantiate is the same domain-generic
`side_collect_sound_in_eff_cone` theorem underneath. This is what lets a
check be discharged at its own CFG node without forwarding stores to the
procedure exit.

### `Analysis_GraphViz.thy` — rendering

`check_result_annotation :: check_result -> bexp -> graphviz_node_annotation`
is the single status-to-style mapping (`Check_Proved` dark green,
`Check_Refuted` red, `Check_Unknown` grey), shared by every domain's
worked example. It depends only on `check_result` and `bexp` — nothing
Sign- or Interval-specific. The generic entry/exit/default node styling
(`analysis_node_attrs`) uses green/light-yellow for entry and neutral
gray for exit, so a refuted check's red never collides with an unrelated
procedure-exit node.

## Why no automatic sublocale

The natural-looking generalization —
`sublocale backward_domain \<subseteq> abstract_numeric_queries` — was tried and
reverted (`docs/CHECK_DISCHARGE_HANDOFF.md`, "Numeric-query theory split").
It answers two different questions, both against it:

1. **Should the derived queries be canonical for every backward domain?**
   No — they inherit the precision of that domain's backward operators, which
   need only be sound. A domain may expose sharper direct queries without
   making those queries part of backward filtering. Interval does this for
   bound comparisons, while its normalized `intersect_ivl` also makes the
   generic equality-refutation default precise on disjoint intervals. An
   automatic sublocale would still force one interface choice on every domain.
2. **Would a downstream `sublocale` declaration have worked anyway?**
   The specific experiment tried it in the wrong place and failed for a
   second, narrower reason: the relation was declared in a theory
   processed *after* Sign's own `backward_domain` interpretation, so
   Isabelle's sublocale-to-existing-interpretation composition never
   reached back into it. Even with correct theory placement (the
   `Abstract_Numeric_Queries.thy` split now gives every future domain the
   option to import it *before* interpreting `backward_domain`), an
   unconditional sublocale would still be the wrong canonical
   architecture for reason 1 — reason 2 was a placement bug in one
   experiment, not the standing argument against the design.

Each domain instead interprets `abstract_numeric_queries` explicitly and
chooses its own source for the four functions: Sign takes the generic
derivation because it is exact there; Interval keeps its specialized
tables because the generic derivation would be a real precision loss.

## Worked examples

`Example_Checks_Store_Only.thy` (Sign) and
`Example_Interval_Checks_Store_Only.thy` (Interval) compile a program,
run the verified solver, and discharge checks at each check's own node —
one proved, one refuted, one unknown, plus a `checks_proven` bridge
exercised on the singleton that is actually true. The Interval example
additionally demonstrates a precision gain: a bound Interval proves
outright (`x < 11` after narrowing `x` to `[1,9]`) that Sign's `SPos`
alone cannot.

## Known limitations (not yet addressed)

- The three checks compiled from `Example_Interval_Checks_Store_Only.thy`
  still generate visible `nop` edges between them — zero-width check
  compilation remains a possible, unstarted, later compiler milestone
  (`docs/NEXT_STEPS.md`). The `checks` relation already permits multiple
  checks at one program point (`(pp * bexp) set`, not a function from
  `pp`); the compiler currently happens to allocate one node per check,
  but the data model does not require that.
- No domain besides Sign and Interval has a check-discharge instance.
  Parity is not wired up.
