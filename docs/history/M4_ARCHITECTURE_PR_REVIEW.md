# M4 storage/placement architecture: fresh PR review

Reviewer note: this is a from-scratch review of the M4 placement PR on
`better-context-routing` against `main` (71 files changed, +12466/-2158).
Green batch status and zero `sorry`/`oops` in tracked `.thy` sources were
checked textually (`rg -n '\bsorry\b|\boops\b' src/` returns no hits); no
batch build was run for this review. Findings are evidence-based: every
claim below cites a specific file and, where useful, a line range.

## 1. Executive verdict

**Merge after a bounded architectural correction (option 3).** The core
mechanism -- finite owner-scoped executable placement completed into a
total abstract state -- is sound in design, not just in proof, and every
migration this PR performs for its own nine core identifiers follows the
project's own locked pattern: a generic parametric definition first, a
named `is_global` (or `classic_*`) specialization second, connected by an
explicit one-line bridge lemma. That pattern holds for `fun_of_exec_dg_st`,
`fun_of_dg_st`, `dg_tree_st_commute`, and `ivl_tf`'s classifier-dependent
field. It does **not** hold for `unit_dg_spec`, which still hand-duplicates
`is_global` internally instead of being derived from
`unit_dg_spec_placed`/`unit_dg_spec_for`, and it does not hold for the
`Split_State.thy` module, which is orphaned scaffolding that collides by
name with the live `Exec_Placement.thy` vocabulary. Both are small,
mechanical fixes, not redesigns. Scoped abstract states are a real
alternative but not a merge blocker: the current completion tax is paid
once, generically, and instantiated per node kind, and a scoped carrier
would have to be threaded through every existing domain instance
(`sound_domain`, `gamma_state`, `dg_spec`, seven-plus analysis instances)
to be worth it. That is a separate, later decision, not something this PR
needs to resolve.

The one finding that should block merge until addressed is scope, not
soundness: this PR proves its new architecture sound for exactly one
example (`Example_Interval_Placement.thy`). Every other D/G example in the
repository -- Sign, Parity, Mixed, all CallString and Ctx instances --
still runs entirely on the classic, `is_global`-fixed spine and uses zero
`_for`/`_placed` constructs. The PR title claims "hook-parametric D/G
generation and soundness" and "classifier-parametric interval transfer and
D/G readback" as delivered capabilities; both are true only in the narrow
sense that the generic definitions exist and are proved sound for one
instantiation. Framing that gap honestly (in the PR description and in
`docs/ROADMAP.md`/`docs/NEXT_STEPS.md`) is a documentation fix, not a code
fix, but it needs to happen before merge so the next contributor does not
read "M4 placement architecture" as "the repository's placement policy,"
when it is currently "one worked example of a placement policy."

## 2. Current architecture

```text
Source (declaration-driven storage)
  imp_prog.declared_global_vars : vname list
        |
        v
  storage_of p owner x = if declared_global p x then GlobalVar else LocalVar owner
  (VIMP_Notation.thy)  -- storage is a source-declaration fact, independent of
                            spelling; no G-prefix test anywhere in this layer

Executable location resolution
        |
        v
  location_of gs x = if gs x then Global_Location x else Local_Location x
  scoped_location = pname * location            (Exec_Placement.thy)
  scope_locations p owner : location list        -- one owner's finite scope

Independent placement policy (orthogonal to storage)
        |
        v
  keep_local, publish_side :: scoped_location => bool
  placement_keep_local / placement_publish_side  -- per-example choice:
    every local stays local; among declared globals, `balance` stays local,
    `request_count` is routed to the shared G side channel

Finite executable carrier
        |
        v
  resolved_st_q = (dl, dg, [(location, value)]) quotient   (Exec_St.thy)
  project_resolved_on_strict owner universe placed s
    -- materializes exactly `universe`, gated by `placed`, defaulting bot
       (Exec_Placement.thy, "Strict projection")

D/G equation generation (hook-parametric)
        |
        v
  placed_dg_edge_tree_with proj owner_of locations_of keep_local publish_side
    transfer read_node write_node                (Exec_DG_Bridge.thy:618)
  placed_dg_edge_tree       = ... project_resolved_on          (defensive)
  placed_dg_edge_tree_strict = ... project_resolved_on_strict  (used by placement)
  sound_dg_hooks / sound_dg_hooks_ltr locales    (DG_Soundness.thy, DG_LTR_Sound.thy)

Executable solve
        |
        v
  TD_side_warrowing_apinis_Interp_solve  -- vendored verified solver
  placement_dg_td_sol : (pp*unit) set * ((pp*unit)+unit => (ivl exec_dg_st, ivl exec_dg_st) dg_state)

Executable-to-abstract transport
        |
        v
  dg_refines_on universe executable abstract      -- pointwise equality on scope
  complete_abs_on gs universe outside s x =
    if location_of gs x in universe then fun_of_exec_dg_st_for gs s x else outside x
  le_lift_if_dg_refines_on_and_le                 -- lifts scoped equality + exec <=
                                                      into abstract <= against the
                                                      completed total state

Abstract post-solution and collecting soundness
        |
        v
  part_post_solution (over the hook-generated abstract equation system)
  hook_post_solution_collect_sound_ltr
        |
        v
  ltr_collect (declared_global placement_prog) placement_cfg (cinit_stores ...) v
    \<subseteq> dg_hook_gamma gamma_unit placement_sigma_abs v
```

Four layers are genuinely independent in this design, and the PR keeps
them independent in the code, matching the project's own stated
distinction (`source storage != analysis placement != update precision`):

1. **Storage** (`storage_of`): a source-declaration fact. `balance` is
   `GlobalVar` because it is declared global; `answer` is
   `LocalVar "main"` because it is not declared and appears in `main`'s
   body. Neither depends on spelling.
2. **Location** (`location_of gs`): a resolution of storage into an
   executable tag (`Local_Location`/`Global_Location`), parametric in
   whatever classifier `gs` the caller supplies -- `declared_global p` for
   the new spine, `is_global` for the classic one.
3. **Placement** (`keep_local`/`publish_side`): a policy decision, wholly
   independent of storage. The worked example proves this independence
   concretely: `balance` and `request_count` are both declared globals
   (both `Global_Location`), yet one is placed in `D` and the other in
   `G` by `placement_keep_local`/`placement_publish_side` alone.
4. **Update precision**: which values differ across nodes and how
   sharply, downstream of (1)-(3), governed by the domain transfer and
   the solver's fixpoint behavior -- see the proof audit (Section 7) for
   why `balance`'s `[3,3]` and `answer`'s `[3,3]` are not the same
   mechanism as each other, let alone attributable to placement alone.

### Serious alternatives

**Alternative A -- scoped abstract state** (Section 5 has the full
comparison): replace `'a abs_state = vname => 'a` with a carrier whose
own type carries a scope, e.g. `record 'a scoped_abs_state = scope ::
"source_location set"; value :: "source_location => 'a"`, or a finite
map. Concretization, join, and the D/G split would all be stated against
that carrier directly, and `complete_abs_on`/`le_lift_if_dg_refines_on_and_le`
would not be needed because there would be no finite/total mismatch to
bridge.

**Alternative B -- push placement into the executable carrier's type**,
i.e. make `resolved_st_q` itself owner-indexed (`pname => location =>
'a`) rather than resolving ownership only at projection time via
`scoped_location = pname * location`. This would remove the
"disambiguate same-named locals of different owners" burden that
`project_resolved_on`'s `owner` parameter currently carries, at the cost
of touching every executable operation (`update_resolved_st`,
`merge_resolved_st`, `combine_resolved_st`, ...) to add an owner index
they do not currently need. Not attempted in this PR; not recommended
now (Section 5).

**Alternative C -- keep the current shape, finish the migration**: no
type change, but (i) collapse `unit_dg_spec` into an
`is_global`-instantiated call to `unit_dg_spec_placed`/`unit_dg_spec_for`
the same way `fun_of_exec_dg_st`, `fun_of_dg_st`, `dg_tree_st_commute`,
and `ivl_tf_for`'s combine field already are; (ii) delete or fold
`Split_State.thy`'s dead `_for` scaffolding into `Exec_Placement.thy`'s
live one; (iii) route the heavily-used `restrict_local_resolved_q`/
`restrict_global_resolved_q` call sites (`Exec_Bridge.thy`,
`Call_String_Solver_Refinement.thy`) through `project_resolved_on` the
same way the classic-equivalence lemmas already show is possible. This is
the recommended path (Section 8).

## 3. Semantic walkthrough

Program (`Example_Interval_Placement.thy:18-28`):

```text
global balance, request_count;
void add(x) {
  tmp := balance + x;
  balance := tmp;
  request_count := request_count + 1;
  return balance
}
void main() { answer := add(3) }
```

### `balance` -- a declared global kept in `D`

| Stage | Representation | Value/meaning |
| --- | --- | --- |
| Source declaration | `declared_global placement_prog ''balance''` | `True` (in `declared_global_vars`) |
| `storage_of` | `storage_of placement_prog owner ''balance''` | `GlobalVar` for every `owner` -- storage is program-global, not owner-relative, once declared |
| Executable location | `location_of (declared_global placement_prog) ''balance''` | `Global_Location ''balance''` |
| `scope_locations` | `Global_Location ''balance'' \<in> set (scope_locations placement_prog owner)` for every `owner` (`declared_global_in_scope_locations`) | every procedure's scope includes every declared global |
| Placement | `placement_keep_local (owner, Global_Location ''balance'') = True` (fixed at `x = ''balance''`) | routed to `D`, **not** `G`, despite being a `Global_Location` |
| Strict projection | `project_resolved_on_strict owner (placement_locations_of node) placement_keep_local s` | keeps `balance`'s value in the local unknown's materialized support |
| Tree generation | `placed_dg_edge_tree_strict` at `Statement 2` (the `balance := tmp` edge) | local answer carries `balance`'s new value; side answer carries `bot` there (`placed_dg_edge_tree_strict`'s `Side`/`Answer` split) |
| Solver result | `placement_dg_td_values`: `lookup_resolved_st_q (locals (snd placement_dg_td_sol (Inl (Statement 2, ())))) (Global_Location ''balance'') = Ivl (Fin 3) (Fin 3)` | exact, because `add` is called exactly once on this path |
| Completed readback | `placement_sigma_abs (Inl (Statement 2, ()))`'s `locals` component at `''balance''`, via `complete_abs_on`: inside `Statement 2`'s scope, so read straight through `fun_of_exec_dg_st_for`, no `top` substitution | `Ivl (Fin 3) (Fin 3)` |
| `gamma_state` | `gamma_ivl (Ivl (Fin 3) (Fin 3)) = {3}` | every reached concrete `balance` at this point is exactly 3 |

`balance` demonstrates that "declared global" and "placed in `G`" are
unrelated axes: it is a `Global_Location` throughout, and is in `D` only
because the placement policy said so.

### `answer` -- a main-local absent from the callee's scope

| Stage | Representation | Value/meaning |
| --- | --- | --- |
| Source declaration | `declared_global placement_prog ''answer''` | `False` -- not in `declared_global_vars` |
| `storage_of` | `storage_of placement_prog prog_main_name ''answer'' = LocalVar prog_main_name` (`Example_Interval_Placement.thy:271`) | implicitly local to `main`, by absence, not by spelling |
| Executable location | `location_of (declared_global placement_prog) ''answer''` | `Local_Location ''answer''` |
| `scope_locations` | `Local_Location ''answer'' \<in> set (placement_locations_of (Statement 5))`, `... (Statement 6)` (`placement_node_scope`); **absent** from `placement_locations_of (FunctionEntry ''add'')`'s scope, since `scope_vnames` is computed per `(p, owner)` and `''answer''` occurs only in `main`'s body | scope is owner-relative: `add`'s activation has no notion of `''answer''` at all |
| Placement | `placement_keep_local (owner, Local_Location ''answer'') = True` (every local is kept, unconditionally) | routed to `D` |
| Executable-to-abstract transport at a node owned by `add`: | For any location outside `add`'s own scope (which never contains `Local_Location ''answer''`), `complete_abs_on`'s `outside` branch fires: `complete_abs_on gs universe outside s x = outside x` when `location_of gs x \<notin> universe` | at every node inside `add`, `answer`'s abstract value is `ivl_top`, not `bot` and not "absent" -- `gamma_ivl ivl_top = UNIV`, i.e. "no information", which is the only sound reading, since some other, unrelated activation could in principle reuse the name `''answer''` and the total carrier cannot represent "this name simply does not exist here" |
| Combine at `Statement 6` (the call's continuation) | `placement_abs_combine_tree`/`combine_collect_abs`: caller's own pre-call `answer` (whatever it was, restored via `combine_states`) is joined against the callee's returned value only at the reserved `ret_var` destination, then read out at `''answer''` | `answer` gets the callee's return value exactly, because `combine_collect_resolved_for_q ... (Some ''answer'') ...` targets that one destination |
| Solver result | `placement_dg_td_values`: `lookup_resolved_st_q (locals (snd placement_dg_td_sol (Inl (Statement 6, ())))) (Local_Location ''answer'') = Ivl (Fin 3) (Fin 3)` | exact |
| `gamma_state` | `{3}` | sound and precise here |

`answer` demonstrates the opposite edge of the same mechanism: `top`
completion for a foreign/out-of-scope local is not "proof repair" -- it
is the only sound value a *total*, unowned `abs_state` can assign to a
name it structurally cannot know is absent. That soundness is bought by
carrying a completion premise (`complete_abs_on`, `placement_local_bound`)
at every node with an owner-relative scope; Section 4 evaluates whether
that premise is worth its proof cost relative to a carrier that could
represent absence directly.

## 4. `gamma_state` alternatives

Current definition (`Abstract_Domain.thy:58-59`):

```isabelle
definition gamma_state :: "('a::sound_domain) abs_state => store set" ("[[_]]") where
  "gamma_state sigma = {s. ALL x. s x : gamma (sigma x)}"
```

### A. Keep current `gamma_state` (total, unscoped)

- **Mathematical clarity**: high. One universal quantifier, no side
  conditions, no partiality. Every downstream lemma
  (`gamma_state_mono`, `gamma_state_bot`, `gamma_state_sup_ub1/2`,
  `gamma_state_upd`) is a one-line `unfold; auto`.
- **Proof obligations**: the completion tax identified in
  `docs/SCOPED_STATE_VS_COMPLETION_REVIEW.md` -- `complete_abs_on`,
  `placement_local_bound`/`placement_side_bound`,
  `le_lift_if_dg_refines_on_and_le` -- exists precisely because this
  `gamma_state` quantifies over every `vname`, including ones a given
  node's executable computation never touches.
- **Lattice structure**: `'a abs_state` inherits `bounded_semilattice_sup_bot`
  pointwise from `fun`, for free (`Abstract_Domain.thy:33`). No custom
  order/join proofs needed for any instance.
- **Transfer soundness**: every existing domain transfer
  (`sound_transfer`, `Sign`, `Parity`, `Mixed`) is proved against this
  shape already; touching it touches all of them.
- **Call/return semantics**: `enter_state`/`combine_states` are plain
  total-function operations; no scope bookkeeping at call boundaries.
- **Compatibility**: total. This is the one point every other proof in
  the repository currently depends on, directly or through `sound_domain`.
- **Executable implementation**: `abs_state` itself is never executed
  (it is the *specification* side); the executable carrier
  (`resolved_st_q`) is already sparse, so this alternative pays the
  finite/total conversion cost once, at the boundary, rather than
  threading scope through the specification.
- **Maintainability**: the completion lemmas are proved once, generically,
  and instantiated per node kind (`placement_se_edge`/`_enter`/`_combine`
  each cite the same three lemmas) -- this is not a per-example tax that
  grows with program size, but it is a tax every future placement example
  will re-pay in the same shape.

### B. Scoped concretization, `gamma_state_on U sigma`

```isabelle
gamma_state_on U sigma = {s. ALL x : U. s x : gamma (sigma x)}
```

- **Mathematical clarity**: deceptively worse, not better, if `sigma`
  itself stays a plain total function. `gamma_state_on` alone does not
  say what `s x` means for `x notin U` -- nothing constrains it, so a
  store agreeing with `sigma` inside `U` and doing anything at all
  outside `U` is in the set. That is a strictly weaker (not wrong, but
  differently-shaped) guarantee than the current design, and every
  consumer of a `gamma_state`-typed fact (e.g. `cinit_stores ... subseteq
  gamma_state s0`) would need to be re-examined for which `U` it now
  implicitly needs.
- **The scope-in-the-type question is not optional here.** Once
  concretization is scoped, two different scopes' concretizations are
  incomparable except by agreeing on `U`. A join
  `gamma_state_on U1 sigma1` and `gamma_state_on U2 sigma2` at *different*
  program points with different owners (exactly the M4 setup: `add`'s
  nodes and `main`'s nodes have different `placement_locations_of`) has
  no single well-defined "combined scope" gamma unless scope is
  threaded alongside `sigma` from the start -- which is Option C, not a
  free add-on to Option B.
- **Verdict**: Option B by itself (scope as a parameter to `gamma_state`,
  carrier unchanged) is not a stable middle ground; it either degenerates
  to Option A with an unused parameter, or it forces Option C.

### C. Scoped/partial abstract state as the carrier

- **Mathematical clarity**: highest *if* done consistently -- absence,
  `top`, and `bot` become three genuinely distinct representable states
  (`None` vs `Some top` vs `Some bot` in a partial map, or membership vs.
  non-membership in a scoped record's domain) rather than `top`/`bot`
  both being total-map values that happen to carry no/all information.
- **Proof obligations**: removes `complete_abs_on`'s outside-scope case
  entirely (no "else" branch to bound), but replaces it with new
  obligations this repository has never had to prove: scope-transition
  laws at call entry (what is the callee's scope, derived from what?),
  scope-transition laws at combine/return (how do caller and callee
  scopes recombine -- is the result's scope the caller's, the union, or
  something else?), and a join operation defined only for
  *compatible*-scope operands, needing an explicit policy for
  mismatched scopes (extend-then-join, or reject).
  `docs/SCOPED_STATE_VS_COMPLETION_REVIEW.md` names this cost directly:
  "a scoped design would still need its own laws for scope transitions,
  split/recombination, joining states with different scopes ... this is
  not a lemma that simply disappears without replacement."
- **Lattice structure**: a scoped/partial map is not automatically a
  `bounded_semilattice_sup_bot` the way `fun` is; `sup` on two different
  scopes needs a definition and a full re-proof of associativity,
  commutativity, and idempotence relative to whatever "extend to the
  wider scope, default the rest" convention is chosen -- which is
  exactly a hand-rolled version of `complete_abs_on`, just moved inside
  the carrier's own `sup` instance instead of at the D/G bridge.
- **Transfer soundness**: every `sound_transfer`/`domain_transfer`
  instance (Sign, Interval, Parity, Mixed) currently states its
  transfer's soundness against `'a abs_state = vname => 'a`
  unconditionally. A scoped carrier changes the *type* those locales
  quantify over, so this is not a localized change to
  `Exec_Placement.thy`/`Exec_DG_Bridge.thy` -- it is a change to
  `Abstract_Domain.thy`, `Constraint_System.thy`, and every instance file
  under `src/Analysis/Instances/`.
- **Call/return semantics**: needs a first-class "new scope" primitive
  at `FunctionEntry`/`FunctionResult` nodes that does not exist today;
  `placement_abs_enter_tree`/`placement_abs_combine_tree` currently reuse
  the same completion apparatus as plain edges (`SCOPED_STATE_VS_COMPLETION_REVIEW.md`,
  "Call/return scope transitions reuse the same completion machinery
  rather than a first-class 'new scope' primitive" -- true today, and
  would need to become false for a scoped carrier to pay for itself).
- **Compatibility with existing analyses**: none of Sign, Parity, Mixed,
  CallString, or Ctx use anything but the current total carrier; this is
  a framework-wide migration, not an addition.
- **Executable implementation**: closer to the executable side's own
  shape (`resolved_st_q` is already scoped/sparse), which is the main
  argument in favor -- but the specification side does not need to match
  the executable side's shape to be sound, only to be bridgeable to it,
  which the current completion lemmas already do.
- **Maintainability**: best *after* the migration; materially worse
  *during* it, since every existing soundness proof would need
  re-statement against the new carrier before any new work could resume.

**Recommendation**: keep Option A (current `gamma_state`) for this PR.
Option C is the right target if and when scoped states become load-bearing
for more than one example, but changing `gamma_state` now, on the evidence
of one worked example, would mean re-deriving soundness for every existing
domain instance before the placement architecture itself has been proved
out beyond that one example. That is out of proportion to the problem
this PR is solving.

## 5. Scoped-state comparison (framework-wide)

Repeating the structural questions from the task, answered against the
*whole* repository, not just the interval instance:

- **Concretization**: Section 4 covers this; Option C's `gamma` would
  need a scope-compatibility side condition wherever two abstract values
  are compared or joined -- currently zero such side conditions exist
  anywhere in `Constraint_System.thy`.
- **Joins between different scopes**: every `Finite_Set.fold`-based join
  in the equation system (`Constraint_System.thy`'s locked "Joins" row)
  currently assumes a homogeneous carrier with an unconditional `sup`.
  Scoped joins need an explicit widen-to-common-scope step first; this is
  a new operation, not a re-derivation of an existing one.
- **Outside-scope values**: absent, `top`, or ignored are three different
  answers with three different soundness consequences (absence needs a
  three-valued carrier; `top` is what Option A/completion already gives
  you; "ignored" silently reintroduces the same ambiguity Option B has).
  The current PR's answer -- `top` for locals via completion, and no
  scoping at all for the shared `G` side channel (it is genuinely
  global, one unknown, `Inr ()`) -- is internally consistent and matches
  Goblint's own "unknown widens to top" convention for context-insensitive
  reads.
- **Call-entry scope transition**: today, `enter_state`/`enter_frame_D`
  (classic) and `enter_ivl_for`/`enter_D` (generic) build a fresh callee
  store/state with no scope object at all -- the callee's "scope" is
  implicit in which locations its own CFG nodes later query. A scoped
  carrier needs this to become explicit and provable (`callee_scope =
  scope_locations p callee_name`, and a lemma that entry produces a value
  well-formed for exactly that scope).
- **Return/combine scope transition**: `combine_states`/`combine_abs`/
  `combine_collect_abs` restore the caller's locals and take the callee's
  globals; a scoped carrier needs an explicit "caller scope ∪ (callee
  scope ∩ globals)" law here, proved once and reused, mirroring what
  `placement_project_split_join` already proves for the *placement* split
  today (locals vs. side) but would need again for the *scope* split
  (in-scope vs. out-of-scope).
- **Owner-sensitive locals**: this is the one place a scoped carrier
  would remove real complexity. `scoped_location = pname * location`
  exists in `Exec_Placement.thy` specifically because the *executable*
  carrier is not owner-indexed; if the abstract carrier's own type
  carried an owner (or, more precisely, a scope that is inherently
  owner-relative), `project_abs_on`'s owner parameter and
  `placement_project_split_join`'s reconstruction proof would not be
  needed. This is real, bounded savings -- not the dominant cost, but not
  zero either.
- **Interaction with D/G placement**: placement (`keep_local`/
  `publish_side`) and scope are orthogonal today (Section 3 shows this
  directly: `balance` and `request_count` are both `Global_Location`,
  both in every procedure's scope, placed differently). A scoped carrier
  would need to keep that orthogonality -- scope answers "does this node
  know about this location," placement answers "which channel carries
  it" -- and nothing about scoping simplifies placement's own logic.
- **Executable correspondence**: closer by construction (see above), but
  "closer" is not the same as "necessary" -- the existing bridge lemmas
  (`dg_refines_on`, `complete_abs_on`, `le_lift_if_dg_refines_on_and_le`)
  already discharge the correspondence obligation for the current shape,
  generically, in three lemmas total.
- **Context-sensitive unknowns**: `activation_collect`/context-sensitive
  D/G instances index local facts by activation keys already (locked
  architecture); a scoped carrier interacts with that indexing
  orthogonally -- scope would be per-node-per-owner, keying is
  per-activation -- so this is additional dimension, not a simplification
  of the existing one.
- **Migration cost across the repository**: `sound_domain`,
  `gamma_state`, `abs_state`, `domain_transfer`, `dg_spec`,
  `sound_dg_spec`, and every instance under `src/Analysis/Instances/`
  (Sign, Parity, Mixed, Interval, plus every CallString/Ctx example) are
  built on the total carrier. None of that code needs to change for this
  PR's one example to be sound. All of it would need to change for a
  scoped carrier to replace the total one.

**Conclusion**: the current PR is not "accumulating complexity that a
scoped carrier would remove structurally" in aggregate -- most of what
Section 4/5 catalogue as scoped-carrier benefits are either already
handled generically (bridge lemmas, reused three times) or would trade a
proof tax paid once per node-kind for a framework-wide retrofit. The one
genuine structural win (owner-indexing folding into the carrier's type
instead of into a separate `scoped_location`) is real but insufficient by
itself to justify the migration now.

## 6. Old-spine deletion/replacement map

Audited via direct definition/usage inspection plus a repository-wide
identifier trace (see prompt-scoped subagent audit for exhaustive
per-file counts; figures below are corroborated by direct reads of each
definition site).

| Constant | Classification | Recommendation |
| --- | --- | --- |
| `is_global` (`VIMP_Globals.thy:26`) | (a) still-active classic classifier; also the base-case instance for every `_for`/`_placed` generalization via `X_for is_global = X` bridge lemmas | **Keep permanently.** It is the fixed classifier for every non-placement analysis instance (Sign, Parity, Mixed, all CallString/Ctx examples -- 60+ files) and is not superseded by anything in this PR. |
| `fun_of_exec_dg_st` / `fun_of_dg_st` (`Exec_DG_Bridge.thy:22-65`) | (b) thin `is_global`-fixed specialization of `fun_of_exec_dg_st_for`/`fun_of_dg_st_for`, bridged by `fun_of_exec_dg_st_for_is_global`/`fun_of_dg_st_for_is_global` | **Keep as classic specialization.** Correct generalize-in-place shape; heavily used (40+ sites) by every un-migrated example. |
| `dg_tree_st_commute` (`Exec_DG_Bridge.thy:2719`) | (b) same pattern, bridged by `dg_tree_st_commute_for_is_global` | **Keep.** Used by all CallString/Ctx examples exclusively; `_for` used by none of them yet. |
| `ivl_tf` (`Interval_Transfer.thy:78-83`) | (b) for the `tf_combine` field (bridged via `ivl_tf_for_is_global`); (a) for `tf_assign`/`tf_assume`/`tf_assume_not`, which never depended on a classifier and are not superseded by anything | **Keep.** Still the record every classic Interval example targets. |
| `unit_dg_spec` (`DG_Framework.thy:490-501`) | **(c) obsolete-shaped duplicate.** Its constituent operations (`unit_step`, `unit_combine_step_env`, `unit_combine_step_assign`, `DG_Framework.thy:461-477`) inline `is_global`/`restrict_local`/`restrict_global` directly rather than being derived from `unit_dg_spec_placed`/`unit_dg_spec_for`. Unlike the two items above, **no** `unit_dg_spec_for_is_global`-style bridge lemma connects `unit_dg_spec` to `unit_dg_spec_for is_global`. | **Redefine as a specialization before merge.** This is the one identifier in the audited list that does not already follow the project's own generalize-then-specialize pattern; every classic soundness interpretation (`Interval_DG.thy`, `Sign_DG.thy`, `Example_Interval_DG_Ctx_Sound.thy`, both CallString K1/K2 pairs) calls it directly, so the fix is adding one definitional equation and one lemma (`unit_dg_spec_def : unit_dg_spec tf = unit_dg_spec_for is_global tf`, or the equivalent through `unit_dg_spec_placed`), not touching any call site. |
| `dg_spec` (`DG_Framework.thy:408`) | (a) foundational, architecture-neutral record type; both classic and placement code target it | **Keep permanently**, no action. |
| `restrict_local_resolved_q` / `restrict_global_resolved_q` (`Exec_St.thy:1061-1079`) | (a)/(d) mixed: still the load-bearing tag-based split for the executable carrier, used pervasively (`Exec_Bridge.thy`, `Call_String_Solver_Refinement.thy`, dozens of sites); connected to the new `project_resolved_on` only by a one-directional classic-equivalence lemma (`lookup_project_resolved_on_classic_local/side`, `Exec_Placement.thy:1057-1099`), not a definitional replacement | **Retain, with a scoped follow-up.** `docs/M4_EXECUTABLE_STORE_HANDOFF.md` already documents this as scaffold-stage ("the resolved carrier is not yet used by the verified solver"); that status is accurate and should stay explicit until `Exec_Bridge.thy`'s own call sites are rerouted through `project_resolved_on`. Not a merge blocker on its own. |

### Additional findings beyond the nine named identifiers

- **`Split_State.thy` is orphaned scaffolding that collides by name with
  `Exec_Placement.thy`.** Both files define `classic_keep_local`/
  `classic_publish_side` (`Split_State.thy:115-119`:
  `(vname => bool) => vname => bool`; `Exec_Placement.thy:17-23`:
  `scoped_location => bool`) -- same names, same intent, different types,
  in the same session (`Voblint_Core`). `Split_State.thy`'s own
  generalization layer (`merge_state_for`, `split_state_for`,
  `wf_split_for`, the `state_placement` locale) has **no downstream
  consumer anywhere in the repository** -- the only importer,
  `TD_Side_CFG.thy`, uses solely the classic, `is_global`-fixed
  `merge_state`/`split_state`/`wf_split`, never the `_for` layer or the
  locale. The `_for` layer is also missing the isomorphism/order/lattice
  transport lemmas its classic sibling has (`merge_state_bij`,
  `merge_state_le_iff`, `merge_state_sup`, `split_state_sup`, ...) --
  an incomplete generalization that was never finished and never wired
  to anything. **Recommendation: delete `Split_State.thy`'s `_for`
  layer, `state_placement` locale, and its own `classic_keep_local`/
  `classic_publish_side` before merge**, or explicitly fold them into
  `Exec_Placement.thy`'s vocabulary if the intent is to keep both. Leave
  the classic `merge_state`/`split_state`/`wf_split` in place (still used
  by `TD_Side_CFG.thy`).
- **`sound_dg_hooks` vs. `sound_dg_spec`**: not a duplicate -- these are
  two different construction routes (tree-based hook generation vs.
  spec-record-based equation generation) for conceptually the same D/G
  soundness obligation, and `sound_dg_spec` is already fully
  classifier-generic (`gs` is a plain locale parameter, not hardcoded).
  This is a legitimate open architecture question, not a merge blocker:
  decide, as a deferred follow-up, whether `sound_dg_spec` should
  eventually be re-expressed as an instance of `sound_dg_hooks` (one
  interface, one soundness proof) or whether both routes are meant to
  coexist permanently for different use cases (hooks for
  placement/routed equation systems, spec for the classic uniform-carrier
  case).
- **No example migration is missing that should have happened.** None of
  the existing CallString/Ctx/Flagship examples are scope-duplicates of
  `Example_Interval_Placement.thy` -- they exercise call-string
  context-sensitivity, routed context, or compile-to-solve pipelines,
  genuinely different concerns from independent per-global placement.
  Nothing needs to be deleted here; they simply have not yet been
  ported to the new spine, which is a scope statement (Section 1), not a
  cleanup item.

## 7. Proof and maintenance risks

Attributing the proof complexity in `Example_Interval_Placement.thy` to
its actual sources, per the task's five categories:

- **Inherent to mixed flow sensitivity**: the D/G split itself (local
  answer vs. side answer, each always carrying `bot` in the other half --
  `placement_hook_gen_globs_bot`, `sides_of_rhs_Inl_bot`) is inherent to
  having *any* flow-sensitive/flow-insensitive mix, independent of
  placement or completion. This complexity would exist even for the
  classic `is_global`-only split.
- **Caused by the finite/sparse executable representation vs. total
  abstract carrier**: `complete_abs_on`, `placement_local_bound`/
  `placement_side_bound`, `le_lift_if_dg_refines_on_and_le` -- this is
  the completion tax analyzed in Section 4, and it is real, but it is
  proved generically (three lemmas, reused per node kind) rather than
  re-derived per node.
- **Caused by owner-sensitive locals needing a separate projection
  step**: `project_abs_on`'s `owner` parameter,
  `placement_project_split_join`'s reconstruction proof -- this is the
  cost Section 5 identifies as the one place a scoped/owner-indexed
  carrier would remove real work, not just move it.
- **Caused by compatibility with the old spine**: none, in
  `Example_Interval_Placement.thy` itself -- it uses only `_for`/generic
  constructs (confirmed: zero bare `fun_of_exec_dg_st`, zero bare
  `fun_of_dg_st`, zero bare `dg_tree_st_commute` hits in that file). The
  compatibility cost this PR pays lives in `Exec_DG_Bridge.thy`/
  `DG_Framework.thy`, where each classic construct's bridge lemma is
  maintained *in addition to* the generic one -- small and one-line each,
  but it is a permanent doubling of definitions for as long as both
  spines are live.
- **Isabelle-engineering-only**: the `resolved_st_q` quotient's
  `eq_resolved_st`-transport lemmas (`eq_resolved_st_effective_support`,
  `eq_resolved_st_rep_project_resolved_on_strict`, etc., throughout
  `Exec_Placement.thy`) exist because the executable carrier is a
  quotient over association lists rather than a canonical finite map;
  this machinery is proof-engineering overhead specific to the chosen
  executable representation, not to the placement architecture's
  semantics. `docs/M4_EXECUTABLE_STORE_HANDOFF.md` already flags this
  ("a balanced executable map is a later performance option") as a
  known, deferred concern.

**Maintenance risk going forward**: every future placement example pays
the completion tax (bounded, acceptable) and, until Section 6's
`unit_dg_spec` fix lands, risks copying the same hand-duplicated
`is_global`-inlining pattern for any new classic-shaped spec rather than
deriving it. The `Split_State.thy` name collision is a standing trap for
the next contributor who greps for `classic_keep_local` expecting one
definition and finds two with incompatible types.

## 8. Required pre-merge changes

1. **Bridge `unit_dg_spec` to `unit_dg_spec_for`/`unit_dg_spec_placed`.**
   Add `lemma unit_dg_spec_is_global: "unit_dg_spec tf = unit_dg_spec_for
   is_global tf"` (or restate `unit_dg_spec` outright as
   `unit_dg_spec_for is_global`), matching the pattern already used for
   `fun_of_exec_dg_st`, `fun_of_dg_st`, `dg_tree_st_commute`, and
   `ivl_tf_for`. Mechanical; no call site changes needed since
   `unit_dg_spec`'s type is unchanged.
2. **Resolve the `Split_State.thy`/`Exec_Placement.thy` name collision.**
   Delete `Split_State.thy`'s unused `_for` layer
   (`merge_state_for`/`split_state_for`/`wf_split_for`,
   `state_placement` locale, its own `classic_keep_local`/
   `classic_publish_side`) since it has zero consumers, or explicitly
   reconcile it with `Exec_Placement.thy`'s vocabulary if a future PR
   intends to use it. Keep `Split_State.thy`'s classic
   `merge_state`/`split_state`/`wf_split` (still used by
   `TD_Side_CFG.thy`).
3. **Narrate the `placement_eqs`/`placement_td_sol` comparison already
   present in `Example_Interval_Placement.thy:3025-3101`.** This block
   computes the *same* placement policy through the flat, single-etf
   route (`side_cfg_T_eff_st`/`unit_etf_st_of_transfer_placed`) instead
   of the D/G split route, and gets `answer = Ivl (Fin 0) (Fin 3)`
   instead of the D/G route's exact `Ivl (Fin 3) (Fin 3)`
   (`placement_dg_td_values`, line 377, vs. `placement_td_values`, line
   3079). This is exactly the controlled comparison the review brief
   asked for -- it shows precision comes from the D/G *split* (separate
   per-node local unknowns), not from the placement *policy* alone --
   but it currently has no `text` block explaining it. Either add that
   explanation (recommended -- it is a genuinely valuable data point) or
   remove the block if it was left over from exploratory work and is not
   meant to be read as a comparison.
4. **Correct the PR's own scope framing.** State plainly, in whatever
   summary accompanies this merge, that "hook-parametric D/G generation
   and soundness" and "classifier-parametric interval transfer and D/G
   readback" are proved for one worked example
   (`Example_Interval_Placement.thy`), not retrofitted onto the existing
   Sign/Parity/Mixed/CallString/Ctx suite, all of which remain entirely
   on the classic `is_global`-fixed spine (confirmed: zero `_for`/
   `_placed` usage in any of them). This matches `docs/M4_EXECUTABLE_STORE_HANDOFF.md`'s
   own "do not begin M4.3/M4.5/M4.6 work from this handoff" scope note,
   but that scope note is not visible from `docs/ROADMAP.md` or the PR
   title, and should be before merge.

None of the above touches `gamma_state`, `abs_state`, or any existing
domain instance's soundness statement.

## 9. Deferred follow-ups

- Decide whether `sound_dg_spec` should eventually be re-expressed atop
  `sound_dg_hooks`, or whether both are permanent, parallel construction
  routes (Section 6).
- Route `Exec_Bridge.thy`'s and `Call_String_Solver_Refinement.thy`'s
  direct uses of `restrict_local_resolved_q`/`restrict_global_resolved_q`
  through `project_resolved_on` once the resolved-carrier bridge is
  judged stable enough to touch the verified-solver-facing consumers
  (matches `docs/M4_EXECUTABLE_STORE_HANDOFF.md`'s own "Next steps" list
  -- this review found no reason to accelerate that beyond what the
  handoff already plans).
- Migrate at least one additional analysis instance (Sign is the
  cheapest, since it shares the same `unit_dg_spec`-shaped record as
  Interval) onto the `_for`/`_placed` generic spine, to get a second data
  point on whether the completion tax generalizes across domains before
  investing further in the placement architecture's breadth.
- Revisit the scoped-abstract-state question (Sections 4-5) once a
  second placement example exists; one example is not enough evidence to
  justify a framework-wide carrier change, but it may become compelling
  evidence with two or three.
- Consider whether `owner`-indexing the executable carrier itself
  (Alternative B, Section 2) is worth it once `project_resolved_on`'s
  `owner` parameter shows up in enough call sites that its bookkeeping,
  rather than the completion bookkeeping, becomes the dominant proof
  cost.

## 10. Final merge recommendation

**Option 3: merge after a bounded architectural correction.**

Concrete change list before merge (all small, all mechanical, none
requires touching `gamma_state`, `abs_state`, or any existing domain
instance):

1. Bridge `unit_dg_spec` to `unit_dg_spec_for`/`unit_dg_spec_placed` with
   an `is_global`-instance lemma (Section 8.1).
2. Delete or reconcile `Split_State.thy`'s orphaned `_for` layer and its
   colliding `classic_keep_local`/`classic_publish_side` names
   (Section 8.2).
3. Add explanatory text for the `placement_eqs`/`placement_td_sol`
   flat-vs-split comparison at the end of
   `Example_Interval_Placement.thy`, or remove it (Section 8.3).
4. State the PR's actual scope (one worked example, not a suite-wide
   migration) in the merge summary and in `docs/ROADMAP.md`/
   `docs/NEXT_STEPS.md` (Section 8.4).

Everything else -- the finite/total bridge design, the `top`-for-foreign-
locals completion, the independence of storage/placement/precision, the
generalize-then-specialize pattern used for eight of the nine audited
identifiers -- is sound architecture, not merely green proof state, and
does not need to change for this merge. Scoped abstract states remain a
legitimate future direction but are not this PR's problem to solve; the
evidence gathered here (Sections 4-5) says the completion tax this PR
pays is bounded and reusable, while a scoped-carrier migration would be
framework-wide and is not justified by one example.
