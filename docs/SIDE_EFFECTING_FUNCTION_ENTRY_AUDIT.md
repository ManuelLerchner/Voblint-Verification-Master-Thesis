# Audit — issue #142, side-effecting function entry

Scope: feasibility of replacing structural call-entry propagation with a
Goblint-style side-effecting function-entry model. Audit only; nothing outside
this file was edited.

## Verdict

Voblint's production path performs **Goblint-style push-based entry
propagation**, but through a **global seed proxy**, and over a **statically
materialized call relation**. Both are real architectural distances from
Goblint's equation system. #142 should be **rewritten, not closed**:

> The intermediate migration is done. The destination architecture is not
> reached.

Three separate statements, kept apart deliberately:

1. **Done.** No production migration remains for push-based entry propagation.
   Caller computes the entry contribution; it is published under
   procedure + context; the callee entry reads the accumulation; recursion is a
   cyclic contribution; structural call edges stay in the CFG semantics.
2. **Approximated.** Goblint side-effects the *local* `FunctionEntry` unknown
   (`sidel`). Voblint side-effects a *global* seed key and reads it back with a
   `QueryG` in the callee's local entry equation. Same collecting dependency;
   operational equivalence unproved (§4).
3. **Not started.** Goblint's call-site RHS resolves its target set from the
   abstract state and iterates. Voblint's equations are built from a statically
   enumerated `calls` relation (§5).

The issue text is additionally stale on naming: it is written against
`EA_Enter`, a constructor that no longer exists. Calls moved out of
`edge_action` into a separate four-place `calls` relation labelled `CallEdge`.

## 1. What Goblint actually does

Verified against `goblint/analyzer`, `src/framework/constraints.ml`, functor
`FromSpec` (`master`, fetched 2026-08-22). Function names, not line numbers, are
the stable anchors.

`tf_proc` — the call-site transfer — owns target resolution:

```ocaml
let functions =
  match e with
  | Lval (Var v, NoOffset) -> [v]                     (* direct-call fast path *)
  | _ -> Queries.AD.to_var_may (man.ask (Queries.EvalFunvar e))   (* state-dependent *)
in
let funs = List.filter_map one_function functions in  (* per target: tf_normal_call *)
```

`tf_normal_call` — per resolved target:

```ocaml
let paths = S.enter man lv f args in                                    (* (caller-cont, callee-entry) LIST *)
let paths = List.map (fun (c,v) -> (c, S.context man f v, v)) paths in  (* context FROM the entry state *)
List.iter (fun (c,fc,v) ->
    if not (S.D.is_bot v) then sidel (FunctionEntry f, fc) v) paths;    (* PUBLISH: local side effect *)
let paths = List.map (fun (c,fc,v) ->
    (c, fc, if S.D.is_bot v then v else getl (Function f, fc))) paths;  (* READ callee exit *)
... S.combine_env ... then S.combine_assign ...
```

Four properties matter: the call-site RHS resolves targets; `enter` returns a
*list*; the context is derived from the *callee-entry* state `v`; and
`(FunctionEntry f, fc)` is a **local** unknown. `spawn` (in `common_man`) uses
the identical `sidel (FunctionEntry fd, c) d` shape for thread entry.

## 2. What Voblint does — correspondence, not identity

`routed_cmb_g` (`src/Framework/DG/Routed_Context.thy:63`):

| Goblint | `routed_cmb_g` | Same? |
| --- | --- | --- |
| caller state | `caller_state <- read_local (cc, ctx)` | yes |
| `S.context man f v` | `ctx' = route cc ctx caller ca` | see §3 |
| `S.enter` | `enter_local S fs as caller globals1` | single result, not a list |
| `sidel (FunctionEntry f, fc) v` | `Side (seed_key (FunctionEntry (result_proc ex)) ctx') (DG (enter_local ...) bot)` | global proxy, not local |
| `getl (Function f, fc)` | `callee_state <- read_local (ex, ctx')` | yes |
| `combine_env`; `combine_assign` | `combine_local S ci dcont callee globals2` | fused, not two hooks |
| target resolution in the RHS | statically enumerated `calls` tuple | **no** (§5) |

`routed_extra_g` supplies the other half — the callee entry equation reads its
own seed back:

```isabelle
routed_extra_g seed_key gk0 route ctx v =
  (case v of FunctionEntry _ =>
     [do { seed_state <- read_global (seed_key v ctx); answer_local (locals seed_state) }]
   | _ => [])
```

Both are hooks of the generator `side_cfg_T_eff_keyed_seed_dg[_buffered]`
(`DG_Constraint_Trees.thy`). Three routing instances exist: `unit_routed_context`
(`route_unit`), `call_string_routed_context` (`cs_route`),
`entry_state_routed_context` (`formals_route_lifted_gen`).

**Reachability evidence, independent of any reading of the sources.** The
checked-in export `codegen/generated/ml/Voblint_CLI.ml` (12,186 lines) contains
`routed_extra_g` (11), `routed_cmb_g_contribution` (11), and seven distinct
`Seed*` constructors — and **zero** occurrences of `dg_gen`, `hook_gen`,
`placed_dg`, `placed_abs_dg`, `dg_extra`, `dg_cmb`, `dg_trees`. Isabelle emits
the transitive closure of the export roots, so this is machine-computed proof
that the exported analyses run exclusively on the routed side-effecting model
and that the pull families are unreachable from every export root.

Outside `src/**/*.thy` and `docs/`, the pull families are named in exactly one
place: `src/Framework/ROOT:52` (`DG_LTR_Sound`). No CI workflow, script, CLI source,
generated artifact, or test references them.

## 3. Routing order — the apparent difference, resolved

Concern: Goblint derives the context from the `enter` *result*
(`S.context man f v`), whereas Voblint's `route` signature
`pp => 'c => 'D => call_action => 'c` receives the **caller** state.

**Resolved for the EntryState instance.** `formals_route_lifted` applies
`enter_local` first and projects the context off the *entered* state
(`Routed_Context.thy:761`):

```isabelle
formals_route_lifted S d ca =
  (case ca of CallEdge dst pars args =>
     formals_context pars (case enter_local S pars args d bot of Bot => bot | Lifted d0 => d0))
```

and `formals_context pars d = map d pars`. The theory's own comment states the
intent: *"using only the entered store."* So `route caller ca` **is**
`context_of (enter_local ... caller ...)`. The `docs/GOBLINT_ALIGNMENT_REGISTER.md`
entry recording this as the load-bearing correction ("context is now selected
from the callee-entry abstract state after parameter binding") is accurate.

The difference is in the **interface**, not the instance: `route` re-derives the
entered state internally instead of receiving it. `route_unit` and `cs_route`
(`cs_route k u ctx d ca = take k (u # ctx)`) discard the state argument
outright, which is legitimate — Goblint's `S.context` is likewise per-analysis
and need not read `v`.

**One latent discrepancy this exposed.** The route computes
`enter_local S pars args d bot` — globals bottomed — while `routed_cmb_g`
publishes `enter_local S fs as caller globals1` with the real globals. Goblint
uses the *same* `v` for `S.context man f v` and for `sidel`. Today the two agree,
because every spec in this development is Base-shaped and its
`dgs_enter` local half discards its global argument
(`local_state_dg_spec_for_lifted`, `DG_Local_State_Spec.thy:45`:
`dgs_enter = (\<lambda>xs es d g. (g, transfer_lift is_bot_pred (enter\<^sup># tf xs es) d))`).

This holds by a property of the current specs, not by construction.

**The fix is the shared-entry invariant, not an independence lemma.** Compute the
entry state once and use that exact value for both context selection and
publication:

```text
entry   = enter_local caller actual_globals
context = context_of entry
publish (FunctionEntry callee, context, entry)
```

An `enter_local ... d g = enter_local ... d bot` lemma would correctly
characterize today's domains, but it would encode into the generic interface
precisely the restriction that should be removed. Acceptable as a temporary
characterization; never as the resolution.

**Soundness status: currently sound by construction, and fragile.** Not simply
"sound but imprecise". The load-bearing assumption is `route_enterc_agree`
(`routed_context_base_hetero`, `Routed_Context.thy:240`):

```isabelle
route u ctx (locals (sigma (Inl (u, ctx)))) (CallEdge dst pars args)
  = enterc u ctx (call_enter gs (CallEdge dst pars args) s)
```

All three live instances discharge it trivially, because every current `enterc`
either ignores its store argument (`enterc_unit`, `cs_context`) or is *defined*
as the abstract route itself (`route_enterc_of_sigma`, EntryState). So the
`bot`/`globals1` split never enters a soundness proof today.

But `route_enterc_agree` is exactly where it would. `formals_context_sem` -- a
genuine store-decoding context function -- already exists in this same theory and
is instantiated nowhere. Instantiate `enterc` with it and the obligation compares
the abstract route (from `enter_local ... bot`) against a context derived from
the **concrete entered store**, which carries real globals. That obligation is
then not dischargeable, or is discharged wrongly. A genuine local/global split or
a relational domain reaches the same place.

## 4. The global seed proxy

The vendored solver's tree is

```isabelle
datatype ('x,'g,'d) strategy_tree =
  Answer 'd | QueryL 'x (...) | QueryG 'g (...) | Side 'g 'd (...)
```

and `sides_of_rhs (Side y d t) sigma = (let m = ... in m(Inr y := m (Inr y) \<squnion> d))`
(`vendor/td-verification/Basics_side.thy:94,295`). **`Side` targets globals
only.** There is no `sidel`. So Goblint's

```text
sidel (FunctionEntry f, fc) v
```

becomes, in Voblint,

```text
SideG (Seed f ctx) v  →  QueryG (Seed f ctx)  →  local (FunctionEntry f, ctx)
```

### What can and cannot be claimed

**Can be claimed:** the encoding expresses the same collecting dependency —
the callee entry's value is bounded below by the join of every caller's entry
contribution at that context, and `TD_side.thy` destabilizes the influenced
unknowns whenever a `Side` raises a value.

**Cannot be claimed** (an earlier draft of this audit overstated it): that the
two compute *the same fixpoint*. That does not follow from the code shape. The
seed is a plain join accumulator with no equation of its own and is never
widened; widening happens one hop later, at the callee's local entry unknown
where the `QueryG` lands. Different variable classification and different
update timing can change solver iteration order, widening points, and therefore
precision. Nothing here has been proved equivalent to Goblint's local-side-effect
formulation, and the honest statement is:

> The encoding appears to express the same collecting dependency, but
> operational equivalence to Goblint's local-side-effect formulation has not
> been proved.

Anything iterating *local* unknowns — `IterSysVars`, per-origin widening gates —
also sees a variable Goblint does not have.

### Closing it is deferred vendor work, not impossible

An earlier draft called this gap unclosable. That was wrong. The direct route is
to split the effect constructor:

```isabelle
datatype ('x, 'g, 'd) strategy_tree =
    Answer 'd
  | QueryL 'x "..." | QueryG 'g "..."
  | SideL 'x 'd "..." | SideG 'g 'd "..."
```

so function entry becomes `SideL (FunctionEntry callee, ctx) entry_state`
directly. That removes the synthetic seed keys, the extra seed-to-local hop,
the internal-global filtering that hides seeds from the renderer, and the
seed-specific routing and transport machinery.

The constructor is trivial. **The solver semantics is the project.** A local
unknown must satisfy both its own equation and every side contribution:

```text
value(x) >= rhs(x)
value(x) >= every SideL contribution targeting x
```

and the following must be re-established: dependency tracking for local
side-effect targets; destabilization when a local contribution rises;
**preservation of contributions when the target's own RHS is re-evaluated**
(the obvious failure mode is a re-evaluated `rhs(x)` overwriting a published
contribution); widening/narrowing at side-effected locals — Goblint-like
behaviour likely requires contributions to participate in widening *at the
target*, since storing them separately and joining afterwards recreates today's
mismatch in a new place; per-origin handling of repeated contributions;
post-solution soundness; termination; recursion and multiple callers.

Buffering does not disappear. `buffer_sides` exists because two contributions to
one key inside one RHS evaluation destabilized the per-origin gate (#123); the
same hazard applies to repeated `SideL` writes.

### A second, smaller delta

Goblint's `enter` returns a *list* of (caller-continuation, callee-entry) pairs
and side-effects each. `routed_cmb_g` publishes exactly one. VIMP needs no
split today, but the interface shape differs.

## 5. The static call-target dependency (missed by the first draft)

The production path still operates on an already-determined call relation. The
combine tree is attached per statically enumerated tuple:

```isabelle
comb = map (\<lambda>(cc, ca, ex). cmb route c ca cc ex) (return_call_action_list g v)
```

and `return_call_action_list` / `entry_call_list` filter the materialized
`calls g` set. The callee is fixed when the equation system is *constructed*.
Publishing the entry state as a side effect does not change that.

Goblint's shape is the opposite: one call-site equation resolves a target set
from the abstract state and iterates it. `call_info`'s own comment already
records the choice — *"Goblint's `fexp` has no separate counterpart: VIMP calls a
statically named procedure, so `ci_callee` already carries what the call
expression identifies"* (`CFG_Def.thy`) — which is true of VIMP and false of the
architecture being modelled.

The distinction bites the moment targets depend on abstract values (function
pointers, indirect calls). Introducing the abstraction *now*, while every
resolution is a singleton, is what makes the constraint system Goblint-shaped
without pretending VIMP has indirect calls:

```isabelle
resolve_targets :: "call_expression => abstract_state => pname set"
resolve_targets (DirectCall f) d = {f}
```

with the call-site equation owning the iteration. **The structural `calls`
relation can and should stay in the concrete CFG semantics** — it is what
`wf_cfg`, `call_enter_store`, `valid_ltr`, and the renderer read. The
architectural problem is only that the *analysis equations* are built from a
statically materialized caller-callee relation.

The target shape:

```isabelle
do {
  caller  <- query_local caller_key;
  targets <- resolve_targets call_expr caller;
  results <- for_each targets (\<lambda>callee. do {
    entries <- enter caller callee args;
    for_each entries (\<lambda>(caller_cont, callee_entry). do {
      ctx' <- context_of callee callee_entry;
      side_local (FunctionEntry callee, ctx') callee_entry;
      exit <- query_local (FunctionExit callee, ctx');
      answer (combine caller_cont exit) }) });
  answer (join results) }
```

which simultaneously fixes the list-valued `enter` and makes the
context-from-entry-state order structural rather than an instance property (§3).

## 6. Legacy pull families

Two equation families remain that are *not* push-based. Neither is reachable
from any export root (§2).

**Base family** — `DG_Soundness.thy`, in `sound_dg_spec_core`:

```isabelle
dg_extra g route ctx v =
  map (\<lambda>(cl, ca). case ca of CallEdge dst fs as => dg_enter ctx fs as cl)
      (entry_call_list g v)
```

The *callee's* entry equation enumerates its callers and reads each caller's
local unknown — push inverted into pull. Endpoint:
`dg_postfix_collect_sound_ltr_for` (`DG_LTR_Sound.thy`).

**Hook family** — `sound_dg_hooks` / `hook_gen` over
`side_cfg_T_eff_keyed_seed_trees`, whose `enter` list is again
`entry_call_list g v`. Fixed at `pp \<times> unit` / `unit`; it cannot carry a context.

Footprint (`dg_gen|dg_trees|dg_postfix|dg_cmb|dg_enter|dg_extra|hook_gen|sound_dg_hooks|dg_hook_`):

| File | Hits | Note |
| --- | --- | --- |
| `Core/Solver/Context/DG/DG_Soundness.thy` | 297 | both families; the rest of the file (fold bounds, `gammaDG`, `enter_sound`/`combine_sound`, canonical spec) is **shared with the routed path** |
| `Core/Solver/Context/DG/Exec_DG_Bridge.thy` | 194 | mostly generic transport; the `placed_*`/hook transport is the pull-specific part |
| `Core/Solver/Context/DG/DG_LTR_Sound.thy` | 33 | pull-only endpoint |
| `Soundness/Run_Analysis_Sound.thy` | 29 | pull-only endpoint |
| `Core/Solver/Context/DG/DG_Constraint_Trees.thy` | 2 | `side_cfg_T_eff_keyed_seed_trees` + four single-tree lemmas |

`Routed_Context` imports `DG_Ctx_Activation` and `DG_Local_State_Spec`, both of which import
`DG_Soundness`. The routed path depends on `sound_dg_spec_core`'s record and transfer
soundness, **not** on its generator. The generator is a separable leaf; the
locale is not.

Examples that would need migration, by whether a call actually occurs:

| Theory | `CallEdge` sites | Effect |
| --- | --- | --- |
| `Examples/Interval/Example_Interval_Placement.thy` | 29 | live call at `Statement 5`; 162 hook references |
| `Examples/Sign/Example_Sign_Placement.thy` | 13 | `calls` is empty, coverage lemmas vacuous; 51 hook references, no semantic change |
| `Examples/Interval/Example_Interval_DG_IP_Flagship.thy` | 6 | interprocedural flagship |
| `Examples/Interval/Example_Interval_DG_Flagship.thy` | 2 | real migration |
| `Examples/Parity/Example_Parity_DG_Flagship.thy` | 2 | real migration |
| `Examples/Sign/Exec_Sign_DG_Run.thy` | 2 | real migration |
| `Examples/Sign/Example_Sign_DG_Custom_Combine.thy` | 1 | real migration |
| `Examples/Mixed/Exec_Int_DG_Run.thy` | 0 | call-free; generator rename |
| `Examples/Mixed/Example_Relational_DG_Demo.thy` | 0 | call-free; generator rename |
| `Examples/Interval/Example_Interval_Global_Flow_Sensitivity.thy` | 0 | call-free; generator rename |
| `Examples/Voblint.thy` | — | capstone prose; text edit |

No `sorry` exists anywhere in `src/`, so each is a proved fact that must be
re-proved against the routed generator or deleted with its example.

**Before deleting, decide whether the duplication is wanted.** These families
prove a *different* generator sound against the same collecting semantics.
That is cross-validation: two independent equation constructions reaching the
same `ltr_collect` bound. If that diversity is intentional, keep them and say so.
If it is only historical residue, retire them. Retirement is cleanup — it is
**not** required to complete #142.

## 7. Rendering

Unaffected, and already correct for the side-effecting model.

`Analysis_GraphViz.thy` builds from the CFG (`cfg_calls_list`) and the solution,
not the equation shape. `analysis_enter_edges` draws
`LocalNode caller ctx --EnterEdge--> LocalNode entry (route ...)` using the same
`route` the equations use; `analysis_combine_edges` draws the return.

Seed globals are already handled:
`visible_global cfg k = is_shared_global cfg k \<or> show_internal_globals cfg`, and
every context-sensitive config sets
`is_shared_global = (\<lambda>k. case k of Global => True | Seed _ _ => False)` with
`show_internal_globals = False`. Seeds are classified as internal plumbing and
hidden; the diagram shows the conceptual enter/combine edges. Flip
`show_internal_globals` to expose the mechanism.

A `SideL` migration (§4) would *simplify* this: with entry publication landing
on the local entry unknown, the seed-hiding special case disappears.

## 8. Recursion

Works end to end, regression-covered:

- `tests/regression/03-procedures/precision/06-recursive_factorial_dead_branch_no_bottom_leak.vimp`
  — recursive factorial under entry-state context, four exact contexts, all
  checks PROVED.
- `tests/regression/17-call-string/known-imprecision/01-deep_recursion_bounded_context.vimp`
  — 50-deep self-recursion under a depth-1 call string; three clusters; the
  `EXPECT-GRAPH` block shows `enter fact(n-1)` re-entering the *same* context
  cluster, i.e. a cyclic seed contribution, rendered.
- `src/Examples/Interval/Ctx/Example_Interval_DG_Ctx_Factorial_Regression.thy`.

The issue asks whether the TD side solver handles recursive entry contributions
"without additional machinery". Recorded in the first fixture's own header, the
answer is **no**: it needed `buffer_sides` /
`side_cfg_T_eff_keyed_seed_dg_buffered` (#123). That machinery exists and is
proved (`distinct_side_path_buffer_sides`); it is not new work, and §4 notes it
does not disappear under `SideL`.

Termination for entry-state contexts over a non-finite domain (Interval) stays
conditional on `solve_c ... \<noteq> None`. Call-string contexts are proved finite
(`compiled_call_strings_finite`). Unchanged either way by this issue.

## 9. Recommendation

**#142 was rewritten, not closed** (done 2026-08-22): *Goblint-style call-site
target resolution and local function-entry side effects*, with objectives —
local `SideL` into `(FunctionEntry p, ctx)`; call-site-owned target resolution;
contexts derived from the exact published entry state; eventual multi-result
`enter`; preservation of the existing CFG and collecting semantics.

Four workstreams. They are related but **not technically inseparable**, and
should not run as one chain — making all progress contingent on a difficult
solver proof is the failure mode to avoid.

**W0 — shared-entry invariant. Do first.** Refactor routing so the computed
callee-entry state is shared between context selection and publication (§3). Add
a regression using a transfer whose local entry component genuinely depends on
the global state; existing domains cannot expose the bug because they ignore that
argument. Small, self-contained, removes the trap before any relational or
split-domain spec lands.

**W1 — call-site-owned target resolution.** Independent of the solver work.
`resolve_targets (DirectCall f) d = {f}` already removes the architectural
dependency on pre-instantiated caller-callee equations, with no vendored-solver
change (§5).

**W2 — bounded `SideL` prototype, before promising migration.** Answer the six
questions in §4 concretely first: contribution preservation across RHS
re-evaluation; where widening applies; repeated contributions from one origin;
which termination and post-solution proofs change; whether `buffer_sides`
generalizes; the maintenance cost of a forked vendored solver.

**W3 — documentation, now, separate from implementation.** Update
`GOBLINT_ALIGNMENT_REGISTER.md`: drop the stale `EA_Enter` references and
distinguish **existing behaviour**, **intended behaviour**, and **unproved
equivalence**. Record the global seed proxy, the extra seed unknown, the possibly
different scheduling/widening, single-result `enter`, statically enumerated
targets, and the context-routing assumption. Classify direct local side effects
as deferred vendor work, not impossible work.

**Explicitly out of scope: do not delete the pull families yet.** They do not
block #142. They prove a *different* generator sound against the same
`ltr_collect` bound — cross-validation that may be useful during the solver
migration. Reconsider only after the new architecture is proved. The inventory in
§2 and §6 stands for whenever that decision is taken.

### The actual decision

Whether the thesis prioritizes minimizing change to the verified vendored solver,
or faithfully modelling Goblint's constraint system. If Goblint alignment is a
substantive thesis goal, then extending the solver with `SideL` and eliminating
statically prewired call equations is a defensible research contribution, not
cleanup. The migration order for that route:

1. Add `SideL` to the vendored solver, leaving `SideG` behaviour intact.
2. Adapt solver semantics; prove the post-solution obligations of §4.
3. Solver-level regressions: one contribution; multiple contributors; duplicate
   contributions; recursive contributions.
4. One monovariant VIMP analysis publishing entry directly via `SideL`.
5. Prove its call-entry/call-return soundness against the existing concrete CFG
   semantics.
6. Replace statically enumerated callee-specific equations with a call-site-owned
   `resolve_targets`, singleton for direct VIMP calls.
7. Context-sensitive routing derived from the computed entry state (structural,
   per §3/§5).
8. List-valued `enter`, if wanted for fidelity.
9. Migrate remaining analyses; remove seed proxies only once equivalent
   regressions and soundness theorems exist.
10. Remove obsolete pull generators, seed infrastructure, and static
    equation-construction dependencies.

## 10. Verification status

| Check | Result |
| --- | --- |
| Export reachability (`codegen/generated/ml/Voblint_CLI.ml`) | routed constants present (`routed_extra_g`, `routed_cmb_g_contribution`, 7 `Seed*` constructors); **zero** pull-family constants |
| Consumer graph outside `src/**/*.thy`, `docs/` | one hit: `src/Framework/ROOT:52` (`DG_LTR_Sound`). No CI, script, CLI, generated artifact, or test reference |
| `sorry`/`oops` in `src/` | none |
| Full Isabelle batch build | **not run** |

No batch build backs this audit. An attempt was made and abandoned; the
findings rest on the source, on the export-reachability check above -- which
needs no build, since it reads the artifact Isabelle already produced -- and on
the CLI regression suite, which runs against the prebuilt `cli/voblint`.

Working tree at audit time was **not clean**: staged `src/Examples/ROOT` +
`Example_Per_Origin_Widening_Precision.thy`, and an unstaged comment revision to
`tests/regression/04-globals/known-imprecision/01-repeated_call_site_widening.vimp`.
That work is per-origin widening precision, unrelated to #142.

### Not verified

- Goblint line numbers are omitted deliberately; `constraints.ml` on `master`
  moves. Functor and function names are the anchors.
- The deletion estimate in §6 is a reading of occurrence counts, not a trial
  removal.
- No claim of operational fixpoint equivalence with Goblint (§4).
- No Isabelle-level confirmation that the pull families still build, or that
  removing them would leave the routed path green. §6's blast radius is a
  reading of the sources, not a trial removal.
