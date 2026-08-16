# Architecture audit: Deadcode / reachability representation

Read-only audit requested by `docs/HANDOVER_DEADCODE_REACHABILITY_REFACTOR.md`. No
source files were changed while producing this report; the only edits made were to the
handover document itself (adding its section 8, the Goblint reference-architecture
writeup, and a cross-reference from section 17).

Base state audited: commit `c6c77443` ("wip(branch): forward-feasibility branch
transfer + Sign local-edge-invariant conflict") on `refining-int-domain`, plus the live
(unsaved) jEdit buffer for `Sign_Local_Effects.thy`.

## Executive conclusion

**Where reachability should live:** at a new lifted sibling of `branch`, added once in
`Abstract_Domain.thy`'s `backward_domain_refined` locale (generic across every domain
instance), and consumed only by the TD-Side effectful pipeline's branch-edge tree
construction. It should *not* replace `branch :: exp => bool => 'a abs_state => 'a
abs_state`, and it should *not* touch `apply_tf` or the `domain_transfer` record's
shared field type. This is candidate **C** (Section 12 below), narrowed further by what
the audit found: the boundary that needs the lift is specifically the branch case of
`local_edge_tree`/`unit_edge_tree`'s tree construction, not `apply_tf` generally.

**Does the locked solver RHS interface need to change?** No. Two independent findings
establish this:

1. The plain `rhs :: pp => (pp => abs_state) => abs_state` interface
   (`Constraint_System.thy:775-800`, `is_post_fixpoint`) is a **declarative
   specification predicate**, not a second live solver. No domain in `src/` is actually
   solved through the unlifted classical `TD` locale (`TD.TD`) — every executed/proved
   solve path (Sign, Interval, Parity, the mixed int_dom) imports `TD.TD_side_upd_rule`,
   the effectful family, and never reconnects to `rhs`/`is_post_fixpoint` at all. **Correction
   (M7 obsolescence audit, post-migration):** there is no exec/spec bridge from the
   TD-Side solution back to `rhs`. `AD-51`/`AD-52` (`Exec_Bridge.thy:225,957`) is the
   executable-state/function-state commutation *inside* the lifted TD-Side route and
   never mentions `rhs`/`is_post_fixpoint` — confirmed by direct grep of
   `Exec_Bridge.thy`. The classical `rhs`/`is_post_fixpoint` route is a parallel,
   solver-independent specification with exactly two consumers
   (`Example_Interval_Loop_Coverage.thy`, `Example_Proc_Call.thy`), both of which
   hand-construct their own post-fixpoint witness rather than running any solver. See
   `docs/VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md`'s "Classical `rhs` specification vs.
   TD-Side execution" section for the settled picture.
2. The vendored solver itself is already polymorphic: `TD.TD` fixes `T :: ('x,'d::bot)
   eqsT` and `TD.TD_side` fixes `T :: ('x,'g,'d::bounded_semilattice_sup_bot) eqsT`
   (`vendor/td-verification/TD.thy:27-28`, `TD_side.thy:18-22`). Neither locale
   mentions `abs_state`. The TD-Side effectful route is already the generic solver
   instantiated at `'d = 'a abs_state lifted` (`TD_Side_Eff_Interface.thy:29`).

So "changing the lattice a generic solver is instantiated with" (handover section 12,
option D) already happened for the route that matters, and required zero vendored-file
edits. The remaining question was only ever where `apply_tf`/`branch`'s own codomain
needs a matching lift — and the answer is: nowhere at the `domain_transfer`/`apply_tf`
level, only at the two tree-construction call sites that build the branch edge for the
already-lifted pipeline.

## Current type/data-flow diagram

Two coexisting, independently-typed routes share one `domain_transfer` record and
diverge immediately after it:

```text
edge_action
     |
     v
apply_tf :: 'a domain_transfer => edge_action => 'a abs_state => 'a abs_state
     |                                                        (Constraint_System.thy:89)
     |
     +-----------------------------------------------+
     |  classical / specification route               |  TD-Side effectful route
     v                                                 v
rhs :: pp => (pp => 'a abs_state) => 'a abs_state       apply_etf ::
     |  (Constraint_System.thy:775, built directly       ('g,'d) effectful_domain_transfer
     |   from apply_tf; never executed)                  => edge_action => pp
     v                                                    => (pp,'g,'d abs_state lifted)
is_post_fixpoint :: ... => bool                                strategy_tree
     |  (a predicate, discharged as a proof                (Constraint_System.thy:1055)
     |   obligation -- see Example_Interval_               |
     |   Loop_Coverage.thy:149)                             v
     |                                              mixed_etf_of_transfer /
     |                                              unit_etf_of_transfer
     |                                              (TD_Side_CFG.thy) build this
     |                                              record's fields by wrapping
     |                                              apply_tf's fields with
     |                                              local_edge_tree / unit_edge_tree
     |                                              via map_lift / transfer_lift
     |                                                       |
     |                                                       v
     |                                              cfg_pkg_eff :: (pp,'g,'a abs_state
     |                                                             lifted) eqsT
     |                                              (TD_Side_Eff_Interface.thy:29)
     |                                                       |
     |                                                       v
     |                                              TD_side.solve  (vendor, generic
     |                                              in 'd::bounded_semilattice_sup_bot)
     |                                                       |
     |                                                       v
     |                                              nu_at :: pp => pp+'g => 'a abs_state
     |                                                       lifted   (actual solution)
     |                                                       |
     |                                              (no bridge back to rhs: AD-51/AD-52
     |                                               is the exec-state/function-state
     |                                               commutation inside this route --
     |                                               confirmed by the M7 audit, see below)
     v                                                       v
is_post_fixpoint holds only for hand-constructed          nu_at is never checked
witnesses (Example_Interval_Loop_Coverage.thy,             against is_post_fixpoint
Example_Proc_Call.thy) -- never for a computed nu_at
```

The executable mirror sits alongside the mathematical route, not below it:

```text
'a abs_state ---------- branch -----------> 'a abs_state
     ^                                            ^
     | fun_of_resolved_st_q_for gs                | fun_of_resolved_st_q_for gs
     |                                             |
'a resolved_st_q ----- branch_st gs -----> 'a resolved_st_q
     (Exec_St.thy:186, quotient_type)   (Exec_Backward.thy:234-247)
```

`branch_st_commute` (`Exec_Backward.thy`) proves this square commutes by a plain `simp`
— no gap, no `sorry`. This layer is unaffected by the Sign conflict and needs no rework
under the recommended design, because it mirrors `branch` (unchanged), not `apply_tf`'s
lifted consumers.

## Existing reachability representation

`'a lifted = Bot | Lifted 'a` (`Abstract_Domain.thy:399`) is mature, general
infrastructure, not a stub: `bot`/`order`/`semilattice_sup`/`widening`/`narrowing`
instances, `gamma_lift` (`gamma_lift gam Bot = {}`, matching Goblint's Deadcode having
empty concretization), `is_bot_lift`, `map_lift`, `bind_lift`, `normalize_lift`,
`transfer_lift`/`transfer_lift2` (run a raw-domain function then re-normalize its
output through an `is_bot_pred` check), and code-generation support (it's a genuine
`datatype`, unlike some deferred-representation approaches).

Critically, `assemble_local_global :: 'b::semilattice_sup lifted => 'b lifted => 'b
lifted` (`Abstract_Domain.thy:735-772`) already **is** the reachability layer the
handover asks the audit to locate. Its own doc comment (tagged `AD-51`/`AD-52`,
predating this branch-migration commit) states the exact distinction section 8 of the
handover independently rediscovers from Goblint:

> A local `Bot` means this control-flow point is unreachable and must dominate
> regardless of what the global side holds; a global `Bot` means only that no side
> contribution has been published yet and must act as `⊔`'s identity.

```isabelle
fun assemble_local_global :: "'b::semilattice_sup lifted => 'b lifted => 'b lifted" where
  "assemble_local_global Bot g = Bot"
| "assemble_local_global (Lifted su) Bot = Lifted su"
| "assemble_local_global (Lifted su) (Lifted sg) = Lifted (su ⊔ sg)"
```

This combinator is already wired through the entire TD-Side pipeline: `unit_edge_tree`,
`local_edge_tree`, `res_local`, `side_env_lift`, `glob_env`, `etf_collecting_full_lift`,
`sound_effectful_transfer`'s locale assumptions — all quantify over `'a abs_state
lifted` and reconstruct local/global inputs through `assemble_local_global`, not `⊔`.
**The Voblint side of the AD-51/AD-52 decision already answers the handover's core
research question for the effect/solver layer.** (`AD-51`/`AD-52` is scoped to that
layer's own local/global `Bot` semantics; it does not bridge to the classical `rhs`
specification — see the correction above.) The only place the codebase still
conflates "no successor" with "successor whose coordinates are bottom" is one layer
upstream of all this: inside `apply_tf`/`branch` itself, whose codomain is still plain
`'a abs_state`.

## Why the Sign theorem fails

`local_edge_invariant gs f` (`TD_Side_CFG.thy:585-591`):

```isabelle
"local_edge_invariant gs f <->
   (forall su g. local_bot_on_locals gs g -->
      f (restrict_local_for gs su ⊔ g) =
      restrict_local_for gs (f (restrict_local_for gs su)) ⊔ g)"
```

Take `f = apply_tf (sign_tf_for gs) (EA_Assume b)` for a purely-local, infeasible
condition `b`, `su` some local store, and `g` a witness with `G = Pos` at a global
position (`local_bot_on_locals gs g` only requires `g` to be bot *at local positions*;
it may be arbitrary at global ones). Because `b` doesn't mention globals
(`local_edge_action` requires `~ exp_mentions_where gs b`), feasibility agrees on both
sides of the equation — `branch`'s `is_bot`/`tobool` case split reaches the same
"infeasible" branch whether evaluated on `restrict_local_for gs su ⊔ g` or on
`restrict_local_for gs su` alone. Both sides of `branch`'s current definition
(`Abstract_Domain.thy:1165-1170`) then return `bot :: 'a abs_state` — bottom at *every*
coordinate, not just the local ones:

* LHS: `f (restrict_local_for gs su ⊔ g) = bot` (all coordinates, including `G`).
* RHS: `restrict_local_for gs (f (restrict_local_for gs su)) ⊔ g = restrict_local_for gs
  bot ⊔ g = bot ⊔ g = g` (since `bot` is `⊔`'s identity) — i.e. `G = Pos`.

`bot != g` whenever `g` is non-bot anywhere, so the invariant is false the moment a live
global exists at an infeasible local branch — exactly the counterexample the handover
sketches in section 6. This is a genuine falsity in the current formulation, not a
missing-automation gap: the live jEdit buffer for `Sign_Local_Effects.thy:553-570`
currently has an unclosed-paren parse error at the abandoned `by (metis ...)` proof
attempt, confirming the previous agent stopped mid-edit on discovering this rather than
leaving a `sorry`.

Only Sign's *named-global, multi-key* route is exposed to this: `local_edge_invariant`
is consumed exclusively by `sound_effectful_transfer_mixed_of_transfer`
(`TD_Side_CFG.thy:1272`), used only by `sign_sound_etf`
(`Sign_Side_Soundness.thy:40-44`) for `Sign_Named_Global_Eff.thy`'s multi-key global
route. Interval, Parity, and the mixed int_dom domains only ever call
`sound_effectful_transfer_unit_of_transfer` (`TD_Side_CFG.thy:1195`), which needs no
`local_edge_invariant` at all — their `branch` migration is structurally incapable of
tripping this bug regardless of domain precision. This is why the handover's proposed
"Sign stays on `bfilter`, Interval/int_dom get `branch`" split looked plausible: it
happened to work around the one place the conflict is actually reachable, without
explaining why.

## Meaning of `local_edge_invariant`

`sound_effectful_transfer_mixed_of_transfer` (`TD_Side_CFG.thy:1272-`) proves each
`etf_*` obligation of `sound_effectful_transfer` by case-splitting on
`local_edge_action`. For the local case it invokes `in_gamma_local_edge_tree`, which
needs `local_edge_invariant` to bridge two different views of the *same* transfer call:

* the soundness fact for `f` as stated generically (`tf_sound_assign_forD` etc.), which
  quantifies over an arbitrary, possibly globally-live store `s`;
* `local_edge_tree`'s own literal computation, `restrict_local_for gs (f
  (restrict_local_for gs su)) ⊔ restrict_global_for gs su` — which always **discards**
  whatever `f` itself computed for global positions and reattaches the pre-transfer
  globals verbatim (`TD_Side_CFG.thy:663-671`).

Because `local_edge_tree` already ignores `f`'s own global output structurally, its
*literal soundness* does not, by itself, require `f` to be globals-preserving. What
breaks is the *algebraic equality* used to prove that literal recipe sound for a fully
assembled (globally-live) input — an equality that only holds when `f`'s output on a
live-global input and `f`'s output on a locally-blanked input agree up to which
coordinates get thrown away. Whole-state `bot` breaks exactly this equality, because it
makes `f`'s output depend on `g` (via annihilating it) when the recipe's other side
assumes it doesn't.

`local_edge_invariant` is load-bearing precisely because it is the only fact standing
between "a local transfer's soundness proof, stated over live global stores" and "the
solver's local/global-separated execution recipe." It is not legacy scaffolding; it
formalizes the same local/global channel separation Goblint's `man.local` /
`man.global` / `man.sideg` split expresses (handover section 8.2).

## Goblint architecture

Recorded in full in the handover, section 8 (`Deadcode` exception, `Dom(D)` lifting
with "bottom means dead code," the `local`/`global`/`sideg` manager split,
`Base.branch`'s forward `eval_rv`/`ID.to_bool` gate ahead of backward `invariant`).

Verification tiering (no live Goblint checkout exists on this machine, so this is
audited against this repo's own doc corpus, not a fresh source read):

* **Independently corroborated**, with verbatim excerpts already present in this
  repo's docs from earlier sessions: the `local`/`global`/`sideg` three-channel manager
  split (`docs/DGC_ALIGNMENT_ANALYSIS.md:34` and five other docs) and the literal `raise
  Deadcode` exception (`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md:570`,
  `docs/GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md:83`).
* **Asserted this session, not found verbatim in this repo's docs**: the specific
  `module Dom (LD)` / "Dom (D) produces D lifted where bottom means dead code" comment
  text, and `Base.branch`'s exact `eval_rv -> ID.to_bool -> (raise Deadcode |
  invariant)` sequencing. Structurally consistent with everything independently
  corroborated, but flagged per the caveat now in handover section 17 — worth a fresh
  source check before this is cited as settled fact in a proof comment.

Where Voblint currently differs: Goblint's `Deadcode` is raised by the transfer function
itself and caught by the framework, so a `D`-typed transfer function that decides
infeasibility never has to *express* it as a value of `D` at all. Voblint's `branch` is
a pure function with no exception mechanism, so it must express infeasibility as a
returned value — and today conflates that value with `D`'s own bottom instead of
returning `D lifted`'s `Bot`.

## Candidate comparison

| Design | Sound | Local-safe | Goblint-like | Refactor size | Future-proof |
| --- | ---: | ---: | ---: | ---: | ---: |
| A. Whole-state bottom (current) | yes (per-domain) | **no** | no | none | no — breaks every domain that reaches the mixed/named-global route |
| B. Poison only the local component | yes | yes, syntactically | no | small per-domain | no — reintroduces a store-representation encoding of deadness, arbitrary variable choice, breaks for a globals-only condition |
| C. Explicit Dead/Reach at the local transfer/effect boundary (`branch_lifted`, consumed only by tree construction) | yes | yes | yes | small, generic (once in `Abstract_Domain.thy` + `TD_Side_CFG.thy`); zero per-other-domain proof work | yes |
| D. Lift the whole solver domain (`apply_tf :: ... => abs_state lifted`) | yes | yes | yes | large — ripples through `domain_transfer`, `rhs`/`is_post_fixpoint`, every domain's record instantiation, the exec/spec bridge | yes, but redundant given the TD-Side route is already lifted |
| E. Hybrid (move the lift boundary inward without touching the generic solver or every domain transfer) | yes | yes | yes | **this is what already exists** for the RHS/solver layer (`assemble_local_global`, `cfg_pkg_eff` at `'d = abs_state lifted`) — C is E applied one layer further inward, at `branch` itself | yes |

D is not wrong, merely unnecessary: the audit in "Executive conclusion" above shows the
solver-facing layer already got D's treatment years before this branch-migration
commit. Applying D again at `apply_tf` would duplicate work E/C already did at the
solver boundary, and would force every domain (including ones with no bearing on this
bug — Interval, Parity, Congruence, int_dom) to re-touch their `domain_transfer`
instantiation for no soundness benefit.

## Recommended target architecture

Add, once, generically, in `Abstract_Domain.thy`'s `backward_domain_refined` locale
(same locale that already proves `branch_sound`/`branch_mono`/`branch_le_bfilter`):

```isabelle
definition branch_lifted :: "exp => bool => 'a abs_state => 'a abs_state lifted" where
  "branch_lifted e pol sigma =
     (if is_bot (aval_abs e sigma) then Bot
      else case tobool (aval_abs e sigma) of
        Some c => if c = pol then Lifted (bfilter e pol sigma) else Bot
      | None => Lifted (bfilter e pol sigma))"

lemma branch_lifted_sound:
  "s : <<sigma>> ==> truthy (aval e s) = pol ==> s : gamma_lift gamma_state (branch_lifted e pol sigma)"

lemma branch_lifted_mono:
  "sigma1 <= sigma2 ==> branch_lifted e pol sigma1 <= branch_lifted e pol sigma2"

lemma branch_eq_unlift_branch_lifted:
  "branch e pol sigma = (case branch_lifted e pol sigma of Bot => bot | Lifted s => s)"
```

`branch` (unchanged) becomes a derived projection of `branch_lifted`, so the classical
`rhs`/`is_post_fixpoint` spec route and `apply_tf`/`domain_transfer` need zero changes
— every existing `branch_sound`/`branch_mono`/`branch_le_bfilter`/`branch_st_commute`
proof for every domain (Sign, Interval, Parity, Congruence, int_dom) stays exactly as
proved today, inherited generically from the locale.

Add one new tree combinator in `TD_Side_CFG.thy`, alongside `local_edge_tree` /
`unit_edge_tree`, dispatched on `local_edge_action` exactly the way `EA_Assign` already
is (`TD_Side_CFG.thy:1303-1320`):

```isabelle
definition local_branch_tree ::
  "(vname => bool) => (exp => bool => 'a abs_state => 'a abs_state lifted) => exp
   => bool => unit => (unit, 'a) edge_tf_tree"
where
  "local_branch_tree gs bl e pol u = do {
     su <- read_local u;
     answer (bind_lift su (%s.
       map_lift (%r. restrict_local_for gs r ⊔ restrict_global_for gs s)
                 (bl e pol (restrict_local_for gs s))))
   }"
```

(An analogous `unit_branch_tree` for the non-local case is very likely *unnecessary*:
`unit_edge_tree`'s existing `transfer_lift is_bot_state f (...)` already re-normalizes a
whole-state-bot output to `Bot` correctly, because it has live globals in hand and is
not subject to the `local_edge_tree`-specific vacuity trap documented at
`TD_Side_CFG.thy:647-661`. Confirm this with a direct proof attempt before assuming it;
if it holds, `unit_edge_tree`'s current wiring for branch is left untouched.)

Then re-derive `local_edge_invariant`'s role at the lifted type, once, generically:

```isabelle
definition local_edge_invariant_lifted ::
  "(vname => bool) => ('a abs_state => 'a abs_state lifted) => bool"
where
  "local_edge_invariant_lifted gs f <->
     (forall su g. local_bot_on_locals gs g -->
        (case f (restrict_local_for gs su ⊔ g) of
           Bot => f (restrict_local_for gs su) = Bot
         | Lifted r => f (restrict_local_for gs su) = Lifted r' &
                       restrict_local_for gs r ⊔ g = r for some r'))"
```

(exact shape to be worked out during implementation; the point proved above is that the
`Bot` case trivially discharges on both sides — there are no coordinates to disagree
about — so this statement is provable by the same case-split `branch_lifted` already
performs, not by a per-domain argument). Sign's own obligation shrinks to proving this
generic fact holds for `branch_lifted` (inherited, zero Sign-specific work) plus
restricting `sign_tf_local_edge_invariant`'s existing statement to the non-branch
`local_edge_action` cases it already covers, since branch no longer routes through
plain `local_edge_tree`.

## Solver impact

```text
Vendored solver changes:                 NO
Generic Voblint solver framework changes: NO (TD_side already generic in 'd;
                                               cfg_pkg_eff already instantiated at
                                               'a abs_state lifted)
Domain instantiation changes:             NO for domain_transfer/apply_tf/rhs;
                                           ONE new generic lemma set in
                                           Abstract_Domain.thy (locale-level, proved
                                           once, inherited by every domain);
                                           ONE new tree combinator in TD_Side_CFG.thy
                                           (generic, proved once);
                                           rewire mixed_etf_of_transfer's (and, if
                                           needed, unit_etf_of_transfer's) branch case
                                           to build etf_branch from local_branch_tree
                                           instead of local_edge_tree/unit_edge_tree
                                           applied to the plain branch# field.
```

## Proof migration

| Proof / area | Classification | Why |
| --- | --- | --- |
| `branch_sound` / `branch_mono` / `branch_le_bfilter` (all domains) | unchanged | `branch` itself is untouched; new `branch_lifted` proofs are additive |
| `branch_lifted_sound` / `branch_lifted_mono` | mechanical | same case split as `branch_sound`/`branch_mono`, one extra `Bot`/`Lifted` tag to track |
| `branch_st` / `branch_st_commute` (executable mirror) | unchanged | mirrors `branch`, which is unchanged |
| `local_edge_invariant` (non-branch `local_edge_action` cases: assign/special/skip/return-local/nop) | unchanged | never collapses to whole-state bot; the conflict is branch-specific |
| `local_edge_invariant_lifted` / `local_branch_tree` soundness & monotonicity | moderate | new combinator, but proved once generically against `branch_lifted`'s case split, not per domain |
| `sign_tf_local_edge_invariant` | moderate | statement narrows to non-branch cases (deletes the now-provably-false branch case rather than repairing it); the abandoned mid-edit proof is replaced, not patched |
| `sign_sound_etf` / `Sign_Side_Soundness.thy` | moderate | re-derive the branch obligation via `local_branch_tree`'s new soundness lemma instead of `in_gamma_local_edge_tree` |
| `sign_etf_cone_compatible` / `sign_etf_threefold_mono` | mechanical, pending re-check | not shown to depend on the branch/local_edge_invariant mechanism directly; re-verify after the above lands |
| `Sign_Exec_Sound.thy`, `Sign_Named_Global_Eff.thy`, `Example_Side_Proc_Global.thy`, `Example_Mixed_Flow_Sign.thy`, `Voblint.thy` | proof-only, downstream | consume `sign_sound_etf` transitively; expected to go green once it does, no statement-shape changes anticipated |
| Interval / Parity / Congruence / int_dom (`branch_sound`/`branch_mono`/`branch_st_commute`/`branch_le_bfilter` instances) | unaffected | none of these domains touch `local_edge_invariant` or the mixed/named-global route |
| `Example_Interval_Loop_Coverage.thy`, classical `rhs`/`is_post_fixpoint` obligations | unaffected | consume `apply_tf`/`branch` directly, both unchanged |
| Exec/spec bridge (`Exec_Bridge.thy:225,957`, AD-51/AD-52) | proof-only, re-verify | executable-state/function-state commutation internal to the TD-Side route (does **not** relate to `rhs`, corrected post-M7); should be unaffected since neither changes type, but re-check once `etf_branch`'s construction is rewired |

None of this is a fundamental redesign in the sense the handover worried about (no
solver-interface change, no ripple into every domain's transfer record).

## Executable migration

No migration needed. `branch_st`/`branch_st_commute` (`Exec_Backward.thy:234-247`)
already mirror `branch` (unchanged by this design) and are already proved by a plain
`simp`, with `resolved_st_q` (`Exec_St.thy:186`) as the finite/sparse executable
representation and `fun_of_resolved_st_q_for` as the abstraction map. If a `branch_st`
counterpart of `branch_lifted` is ever needed for a fully-executable TD-Side run, it is
the same shape — `branch_lifted_st`, commuting with `branch_lifted` via
`map_lift resolve` — but nothing in the audited soundness chain currently requires the
effectful route to also be executable end to end, so this can be deferred.

## File impact map

| File | Class |
| --- | --- |
| `src/Core/Domain/Abstract_Domain.thy` | MUST CHANGE — add `branch_lifted` + soundness/monotonicity, generic, once |
| `src/Core/Solver/TD_Side/TD_Side_CFG.thy` | MUST CHANGE — add `local_branch_tree`, `local_edge_invariant_lifted`, rewire branch construction |
| `src/Core/Equations/Constraint_System.thy` | LIKELY UNCHANGED — `apply_tf`, `domain_transfer`, `rhs`, `is_post_fixpoint` all untouched |
| `src/Core/Solver/Exec/Exec_Bridge.thy` | PROOF-ONLY, re-verify — exec/spec bridge, types unaffected |
| `src/Core/Domain/Exec_Backward.thy` | EXECUTABLE MIRROR, unaffected — `branch_st`/`branch_st_commute` already green |
| `src/Core/Domain/Exec_St.thy` | EXECUTABLE MIRROR, unaffected |
| `src/Analysis/Instances/Sign/Sign_Local_Effects.thy` | MUST CHANGE — replace the abandoned `sign_tf_local_edge_invariant` proof; statement narrows to non-branch cases |
| `src/Analysis/Instances/Sign/Sign_Side_Soundness.thy` | MUST CHANGE — `sign_sound_etf`'s branch obligation re-derived via the new combinator |
| `src/Analysis/Instances/Sign/Sign_Exec_Sound.thy` | PROOF-ONLY, downstream |
| `src/Analysis/Instances/NamedGlobalSign/Sign_Named_Global_Eff.thy` | PROOF-ONLY, downstream |
| `src/Examples/Sign/Example_Side_Proc_Global.thy` | EXAMPLES/REGRESSIONS, downstream |
| `src/Examples/Sign/Example_Mixed_Flow_Sign.thy` | EXAMPLES/REGRESSIONS, downstream |
| `src/Examples/Sign/CallString/Example_Sign_DG_CallString_K1.thy` | EXAMPLES/REGRESSIONS, downstream (path corrected from `CLAUDE.md`'s flat guess — it lives under `Sign/CallString/`) |
| `src/Examples/Voblint.thy` | EXAMPLES/REGRESSIONS, downstream |
| `src/Analysis/Instances/Sign/Sign_Backward.thy`, `Sign_Transfer.thy`, `Sign_Exec.thy` | LIKELY UNCHANGED / EXECUTABLE MIRROR — generic locale citations only, no `local_edge_invariant` reference |
| `src/Analysis/Instances/Interval/*.thy`, `src/Analysis/Instances/Mixed/*.thy`, `src/Analysis/Instances/Congruence/Congruence_Backward.thy` | LIKELY UNCHANGED / EXECUTABLE MIRROR — confirmed no `local_edge_invariant` reference in any of them; all cite the generic locale's `branch_sound`/`branch_mono`/`branch_st_commute` |
| `src/Examples/Interval/Example_Interval_Loop_Coverage.thy`, `Exec_Ivl_Run.thy` | LIKELY UNCHANGED / EXAMPLES — consume the classical `rhs`/`is_post_fixpoint` route or executable mirror directly |

## Locked-decision recommendation

No change recommended. Old wording (`CLAUDE.md`):

> | Solver interface | `rhs :: pp => (pp => abs_state) => abs_state` |

Proposed replacement: none — this audit confirms the interface is correct as stated and
does not need superseding. What is worth adding to `CLAUDE.md` (a documentation
clarification, not a decision change) is the fact this audit surfaced and that the
handover's own "locked" framing didn't anticipate: this `rhs` is a specification
predicate that no domain is actually solved through today, with the live solve always
going through the generic side-effecting `TD_side` locale at a lifted domain instead.
That is useful context for the next person who assumes "locked" means "this is the
executed solver" and reaches for it when debugging solve behavior.

## Migration phases

```text
M1  Add branch_lifted + branch_lifted_sound/mono + branch_eq_unlift_branch_lifted
    in Abstract_Domain.thy (generic, one locale, inherited by every domain instance;
    checkpoint: existing branch_sound/branch_mono/branch_le_bfilter/branch_st_commute
    for every domain remain green, since branch itself is untouched).

M2  Add local_branch_tree + local_edge_invariant_lifted (or its settled shape) +
    soundness/monotonicity in TD_Side_CFG.thy, generic (checkpoint: new lemmas
    compile in isolation, no existing lemma touched yet).

M3  Confirm (or refute, with a proof attempt) that unit_edge_tree's existing
    transfer_lift is_bot_state self-recheck already correctly handles branch edges
    that are NOT local_edge_action-classified, so no unit_branch_tree is needed.

M4  Rewire mixed_etf_of_transfer's (and unit_etf_of_transfer's, if M3 says
    necessary) branch-edge construction to use local_branch_tree instead of
    local_edge_tree/unit_edge_tree applied to the plain branch# field (checkpoint:
    Interval/Parity/int_dom's effectful soundness chains, which don't touch this
    code path via sound_effectful_transfer_unit_of_transfer for non-branch reasons,
    remain green as a regression check).

M5  Sign: replace the abandoned sign_tf_local_edge_invariant proof with one scoped to
    the non-branch local_edge_action cases; re-derive sign_sound_etf's branch
    obligation via local_branch_tree's soundness lemma (checkpoint: Sign_Side_
    Soundness.thy green).

M6  Restore Sign_Exec_Sound.thy, Sign_Named_Global_Eff.thy, and the three downstream
    example/capstone theories (checkpoint: each compiles independently).

M7  Re-verify the AD-51/AD-52 exec/spec bridge in Exec_Bridge.thy against the
    rewired etf_branch construction (checkpoint: bridge lemma unchanged in
    statement, proof revalidated).

M8  Full batch build (AFP=<path> pixi run build) + regression suite + codegen check.
```

## Acceptance criteria

```text
1. contradictory guard denotes no successor explicitly       -- branch_lifted's Bot
2. Sign local-edge invariant true without special pleading   -- M5, generic lemma
                                                                  inherited from M1/M2
3. all domains use the same branch architecture               -- branch_lifted defined
                                                                  once, generically, in
                                                                  the shared locale
4. Goblint-style forward feasibility retained                 -- branch/branch_lifted
                                                                  unchanged in structure
5. backward filtering remains the second phase                 -- bfilter call inside
                                                                  branch_lifted unchanged
6. executable mirror provably commutes                         -- already true (M0,
                                                                  branch_st_commute);
                                                                  extend only if M
                                                                  needs an executable
                                                                  effectful route later
7. TD-side solver soundness chain remains intact                -- M7
8. no arbitrary local-variable poisoning                        -- candidate B rejected
9. no hidden state-bottom/deadcode conflation                   -- branch_lifted's Bot
                                                                  is a distinct
                                                                  constructor, not a
                                                                  value of 'a
10. full build and executable regressions green                -- M8
```
