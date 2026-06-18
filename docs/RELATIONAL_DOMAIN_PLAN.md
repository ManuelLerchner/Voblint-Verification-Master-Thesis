# Relational Domain Support

Status: **PLANNED** (Approach A chosen). Authored 2026-06-14. Not yet started.

## Goal

Today every abstract domain is **nonrelational**: the state is a box, one
independent abstract value per variable. We want a single generic interface
that both nonrelational (Sign, Interval) and relational (order constraints,
octagons) domains instantiate, without forking the soundness spine.

End state: the IP soundness chain is stated over an abstract whole-state
concretization `gamma_st :: 'd => store set`. The existing box domains
re-interpret it (`'d = vname => 'a`, `gamma_st = gamma_state`); relational
domains supply their own `'d` and discharge the same four facts.

## Why nonrelationality is currently hardwired

Five spots, in dependency order. File:line as of authoring.

1. **Representation type** — `src/Analysis/Domains/Abstract_Domain.thy:23`
   `type_synonym 'a abs_state = "vname => 'a"`. One independent abstract
   value per variable. This *is* the nonrelational commitment.

2. **Box concretization** — `Abstract_Domain.thy:66`
   `gamma_state sigma = {s. \<forall>x. s x \<in> gamma (sigma x)}`. A Cartesian
   product over variables. Cannot express `x = y`, `x <= y`, `x + y <= 10`.

3. **Pointwise lattice** — `Abstract_Domain.thy:27`
   `instance "fun" :: (..) bounded_semilattice_sup_bot`. Join/bot lifted
   componentwise. A relational join is *not* pointwise.

4. **Per-transfer soundness** — `src/Analysis/Equations/Constraint_System.thy:519`
   (`sound_transfer` locale). Phrased via `gamma_state`, inherits the box.

5. **Variable-projection combinators** — `combine_abs`
   (`Constraint_System.thy:403`) and `enter_state`. Procedure call/return
   split state by `is_global`, per variable. Purely nonrelational.

## The leverage point

The **core soundness theorem already speaks store-sets, not boxes**:

```
trace_ip_analysis_sound : cfg_collect_trace_ip g S v  <=  gamma_state (env v)
```

`gamma_state :: 'a abs_state => store set` — a set-of-stores inclusion, the
relational-compatible shape. The box structure is unfolded (`gamma_state_def`)
only in the leaf read corollaries that project to a single variable
(`src/Formalization/Pipeline/Trace_IP_Analysis_Sound.thy:77,137`):
`(last tr) x \<in> gamma (env v x)`.

The solver-soundness chain (`src/Analysis/Solver/TD_Side_IP_Eff_Soundness.thy`)
depends on `gamma_state` through exactly **four abstract facts**, never its
structure:

- `gamma_state_mono`   (`Abstract_Domain.thy:72`)
- `gamma_state_bot`    (`Abstract_Domain.thy:77`)
- `gamma_state_sup_ub1`(`Abstract_Domain.thy:81`)
- `gamma_state_sup_ub2`(`Abstract_Domain.thy:86`)

So the migration is mostly: parameterize the spine on those four facts;
re-interpret the box case; instantiate one toy relational domain.

## Approach A (chosen): abstract the concretization

```isabelle
locale rel_domain =
  fixes gamma_st :: "'d => store set"
    and bot  :: "'d"
    and join :: "'d => 'd => 'd"
  assumes gamma_st_bot:      "gamma_st bot = {}"
      and gamma_st_join_ub1: "gamma_st a \<subseteq> gamma_st (join a b)"
      and gamma_st_join_ub2: "gamma_st b \<subseteq> gamma_st (join a b)"
      and gamma_st_mono:     "a \<le> b \<Longrightarrow> gamma_st a \<subseteq> gamma_st b"
```

- **Box domains interpret it.** `'d = vname => 'a`, `gamma_st = gamma_state`,
  `join = sup`, `bot = bot`. The four assumptions are exactly the existing
  `gamma_state_*` lemmas — discharged by `interpretation`, zero new proof.
- **Relational domains** supply their own `'d` and prove the four facts.
- **Transfers become `'d => 'd`** (was `(vname=>'a) => (vname=>'a)`); the
  `apply_tf` dispatch shape is unchanged.
- **Leaf read corollary stays box-only.** Add an *optional* extra assumption
  `gamma_st_read : s \<in> gamma_st d \<Longrightarrow> s x \<in> gamma_var d x`
  that only box domains discharge. The core store-set theorem needs nothing
  variable-wise.

### Rejected: Approach B (sibling locale)

Keep the nonrelational spine untouched; add a parallel `rel_domain` +
`rel_sound_transfer` + a *copy* of the IP soundness theorem over `gamma_st`.
Lower risk to the green build, but duplicates the entire IP chain to avoid
touching ~4 lemmas that already abstract cleanly. Net more proof to maintain.
A wins because the core theorem only ever used the four facts.

| | A (unify) | B (sibling) |
| --- | --- | --- |
| Existing proofs | re-interpret; moderate churn | untouched |
| Duplication | none | full copy of IP chain |
| Build risk | moderate (touches core) | low |
| Generic-interface goal | fully met | half-met |

## The genuinely hard part: interprocedural combine/enter

`combine_abs` today is "globals from callee, locals from caller, per
variable." Relationally that is wrong: a relation `local_caller <= global`
learned across the call must be reconstructed via **projection + meet**, not
variable selection.

**MVP decision: restrict the relational domain to intraprocedural**, or treat
`Call` conservatively (havoc all relations touching locals at the boundary)
and prove combine soundness only for that restricted combinator. Full
relational IP combine is a research-grade extension, out of MVP scope.

## First concrete relational domain

Not octagons. Start with **two-variable order constraints** `{ x <= y }`:

- `'d = (vname \<times> vname) set` — the pairs known ordered.
- `gamma_st d = {s. \<forall>(x,y)\<in>d. s x \<le> s y}`.
- `join = \<inter>` (intersection of known orderings).
- `bot = UNIV` (every pair ordered — empty concretization unless consistent;
  pick the bottom that gives `gamma_st bot = {}`, refine during the spike).

Intersection is monotone and an upper bound under reverse inclusion, so the
four facts are near-trivial. Transfers are small. Octagon is the natural
follow-up once the interface holds.

## Plan of record

### Phase 0 — spike (do first, ~30 lines)

Prove the interface is discharge-able **before** migrating the spine:

1. Add `rel_domain` locale to `Abstract_Domain.thy`.
2. `interpretation box: rel_domain gamma_state bot sup` reusing
   `gamma_state_*` — proves the box case costs nothing.
3. New toy `Rel_Order_Domain.thy`: the `x<=y` domain + `interpretation
   rel_domain`. Proves a non-box `'d` discharges the same four facts.

Exit: both interpretations green in I/Q. If the box interpretation does not
go through verbatim, the abstraction is wrong — stop and revisit before any
spine edits.

### Phase 1 — generalize the spine

- `Constraint_System.thy`: `domain_transfer` over `'d` carriers; restate
  `sound_transfer` over `gamma_st`; keep `apply_tf`.
- `TD_Side_IP_Eff_Soundness.thy`, `Trace_IP_Analysis_Sound.thy`: swap
  `gamma_state` -> `gamma_st`; leaf read corollary gains the optional
  `gamma_st_read` assumption.
- Re-interpret Sign through the new locale; confirm `Sign_Side_IP_Soundness`
  still green.

### Phase 2 — relational transfers + restricted IP

- `Rel_Order_Domain.thy`: assign/assume/assume_not transfers + per-action
  soundness against `gamma_st`.
- Conservative `combine_abs`/`enter` for the relational case (havoc local
  relations at the call boundary) + soundness, OR intraprocedural-only.
- End-to-end soundness for the `x<=y` domain mirroring
  `side_ip_sign_analysis_sound`.

## Scope of edits (Phase 1+2)

- `Abstract_Domain.thy`: `rel_domain` locale + box `interpretation`.
- `Constraint_System.thy`: generalize transfer carrier + `sound_transfer`.
- `TD_Side_IP_Eff_Soundness.thy` / `Trace_IP_Analysis_Sound.thy`:
  `gamma_state` -> `gamma_st`, optional read assumption.
- New `src/Analysis/Domains/Rel_Order_Domain.thy`.
- IP combine: restricted/conservative combinator + soundness, or defer.

## Open questions

- `bot`/consistency for the order domain (`gamma_st bot = {}` shape).
- Does `widen` need a relational analogue now, or only when octagons land?
- Conservative-combine precision: is local-relation havoc acceptable, or does
  the MVP go strictly intraprocedural?
