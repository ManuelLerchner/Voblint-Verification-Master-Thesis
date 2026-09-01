# One merge/split spec: unifying the unit and placed D/G specifications

Status: **design, not yet executed.** The research record and execution plan
for generalizing the homogeneous "unit" D/G specification and its executable
pullback so that the placement policy becomes a second instantiation instead
of a second implementation. Written before any theory edit; update it the way
`CORE_REFACTOR_PLAN.md` is updated -- correct it where the build disagrees,
in place, dated.

This document supersedes the 2026-09-01 decision entry in
`CORE_REFACTOR_PLAN.md` that called step 3.1 (`dead_code_lift`) a
precondition for closing step 2.3's owner-aware half. It is not. The
research below found the abstract-carrier soundness of the placement policy
already proved (`sound_dg_spec_unit_placed`, `Placement_Policy.thy`); the
actual gap is the executable mirror, and `dead_code_lift` is orthogonal to
it (see "Relation to step 3.1").

## The two specifications, side by side

Both existing "homogeneous" specifications -- `unit_dg_spec_for`
(`DG_Unit_Spec.thy`, exclusive classifier routing) and `unit_dg_spec_placed`
(`Placement_Policy.thy`, non-exclusive covering) -- are instances of one
skeleton that neither theory names:

```text
step  f d g   =  let res = f (M d g)                 in (sg res, sd res)
enter tf ci   =  the same skeleton at (snd o enter# tf ci)
combine       =  let res = combine_assign dst ((M de g) ret_var)
                            (combine_env gs (M dc g) (M de g))
                 in (sg res, sd res)          -- see "The combine wrinkle"
gamma d g     =  [[ M d g ]]
```

with a merge `M :: 'a abs_state => 'a abs_state => 'a abs_state` and a split
pair `sg, sd :: 'a abs_state => 'a abs_state`. The two instances:

| Piece | `unit_dg_spec_for gs tf` | `unit_dg_spec_placed gs kl ps tf` |
| --- | --- | --- |
| merge `M` | `combine_env gs` | `(\<squnion>)` |
| split `sg` | `restrict_global_for gs` | `project_component ps` |
| split `sd` | `restrict_local_for gs` | `project_component kl` |
| gamma | `gamma_unit gs d g = [[combine_env gs d g]]` | `gamma_join d g = [[d \<squnion> g]]` |
| reassembly law | `combine_env_restrict_id`: exact | `project_component_cover_sup`: exact, needs `cover` |
| extra premise | `reserved_ret_var gs` | `\<forall>x. ps x \<or> kl x` (cover) |
| abstract soundness | `sound_dg_spec_unit_for` (DG_Soundness 1977) | `sound_dg_spec_unit_placed` (Placement_Policy 209) |

Two identities make the table exact rather than analogical
(`State_Restriction.thy` 15-21 against `Placement_Policy.thy` 18-20):

```text
restrict_global_for gs = project_component gs
restrict_local_for  gs = project_component (\<lambda>n. \<not> gs n)
```

So the split pair is `project_component` at two predicates in *both*
instances; `unit_for` picks the exclusive partition `(gs, \<not>gs)`, `placed`
an arbitrary covering `(ps, kl)`. The merge differs because exclusivity is
what licenses the precise selector: with a partition, `combine_env` can
route each name to its owner; with an overlapping covering there is no owner
and only `(\<squnion>)` is sound (this is `Placement_Policy.thy`'s own
documented rationale, and why `gamma_unit gs d g \<subseteq> gamma_join d g`
is a strict refinement, not an equivalence).

The two abstract soundness proofs are structurally isomorphic: each case is
"transfer/combine/enter soundness at `[[M _ _]]`, then the reassembly law
folds the split back". Every generic fact they need is one of:

1. `M` monotone in both arguments (`gamma_unit_mono` / `gamma_join_mono`).
2. Reassembly: `M (sd res) (sg res) = res`
   (`combine_env_restrict_id` / `project_component_cover_sup2`).
3. `sound_transfer_for gs tf` (shared verbatim).
4. One instance-specific discharge for the combine case (next section).

## The combine wrinkle

The generic combine shape above is what `placed` computes literally
(`unit_combine_step_env_placed` merges `combine_env gs (dc \<squnion> g)
(de \<squnion> g)`; the assign step reads `(de \<squnion> g) ret_var`).
`unit_for`'s record is an *optimized* form of the same value:

- its env step merges only `combine_env gs dc g` -- correct because
  `combine_env gs (combine_env gs dc g) (combine_env gs de g) =
  combine_env gs dc g` (absorption, already `[simp]` in `DG_Soundness`);
- its assign step reads the bare `de ret_var` -- correct because
  `reserved_ret_var gs` pins `ret_var` local, so
  `(combine_env gs de g) ret_var = de ret_var`.

So the generalization must not force `unit_for` to change its definition
(that would ripple through every `unit_combine_step_env_for_def` unfold
site). Instead:

**Design decision: characterize, don't rebuild.** The generic layer is a
locale that *fixes* an arbitrary spec `S` together with `(M, sg, sd)` and
*assumes* the four shape equations (step, enter, caller_cont = identity,
combine up to the generic value), plus `M`-monotonicity and reassembly. It
proves `sound_dg_spec S (\<lambda>d g. [[M d g]]) gs` once. The two existing
records interpret it: `unit_for` discharges the combine equation via
absorption + `reserved_ret_var`, `placed` via `cover`. No existing
definition changes; the two ~60-line soundness proof bodies
(`sound_dg_spec_unit_for` with its two helper lemmas,
`sound_dg_spec_unit_placed` with its two) collapse to interpretations, and
their theorem names survive as re-exports. This is the same
"characterize by equations" pattern the executable layer already uses
(`Hstep`/`Henter`/`Hcomb`/`Hcont`).

Proposed names (Core, `DG_Unit_Spec.thy` -- the file already owns the unit
skeleton): locale `merge_split_spec` for the abstract half; keep
`unit_step_for`/`unit_step_placed` untouched as the instance witnesses.

## The executable layer

The pullback to the executable carrier already exists for `unit_for` and is
already generic in the domain -- just not in `(M, sg, sd)`:

- `unit_dg_spec_st_for` (`Exec_DG_Refines.thy` 636) mirrors the record over
  `'a exec_dg_st`, with `combine_resolved_st_q` for `combine_env` and
  `restrict_local_resolved_q`/`restrict_global_resolved_q` for the split.
- `unit_step_st_commute_for` / `unit_combine_step_st_commute_for` prove the
  readback commutes, from the `fun_of_resolved_st_q_for_*` homomorphism
  simps.
- `unit_dg_Hstep_for`/`_Henter_for`/`_Hcomb_for`/`_Hcont_for`
  (`Run_Analysis_Sound.thy` 96-128) package those per record field, and
  `unit_dg_exec_analysis.sound_dg_spec_st` (234) derives
  `sound_dg_spec (unit_dg_spec_st_for ...) gamma_unit_exec gs` from them
  plus the abstract theorem -- the same five-case pullback
  `routed_dg_domain_exec` performs for the lifted Base shape.

The generalized executable locale (`merge_split_spec_exec`, extending
`merge_split_spec`) fixes the executable mirror `S_st` and assumes the four
*record-level* commute facts (`dg_spec_step`/`dgs_enter`/`dgs_combine`/
`dgs_caller_cont` of `S_st` each commuting with `S`'s under
`fun_of_exec_dg_st_for`); the `sound_dg_spec_st` derivation is then the
existing `unit_dg_exec_analysis` proof verbatim, with `(M, sg, sd)`
abstract. (G2 refinement over the first draft: the interface is the four
record-level facts, not `(M_st, sg_st, sd_st)`-level operator commutes --
strictly weaker assumptions, exactly what the derivation consumes, and the
per-operator packaging stays per-instance where it belongs.)
`unit_dg_exec_analysis` re-derives its `sound_dg_spec_st` by a `sublocale`
interpretation discharged from the untouched generic
`unit_dg_Hstep_for`/`_Henter_for`/`_Hcomb_for`/`_Hcont_for`, unchanged
outward; the batch build is the regression check that the Interval flagship
is unaffected.

### The one genuinely new piece: an executable split for arbitrary predicates

`restrict_local_resolved_q`/`restrict_global_resolved_q` filter by location
*constructor*, and their readback simps produce exactly the
`(gs, \<not>gs)` partition. The placed instance needs
`project_component p` for an arbitrary `vname => bool` at the executable
carrier, and this is where the representation bites: a `resolved_st` carries
two *defaults* (`dl`, `dg`) for unmaterialized locations, so "bot outside
`p`" is not representable by entry filtering alone when a default is
non-bot -- an unmaterialized location inside `p` must keep its default
while one outside `p` must read bot.

This is a solved problem in the codebase: `Exec_Placement.thy`'s
`project_resolved_on(_strict) owner universe placed` materializes an
explicit finite `universe` before filtering, precisely to make defaults
projectable, and already carries the lookup-correspondence lemmas
(`lookup_project_resolved_on`, `..._strict`, `..._relevant`). Two options:

1. **Reuse `project_resolved_on_strict` with a degenerate owner.** The
   examples' predicates never read the owner component (verified: both
   `sign_placement_*` and `placement_*` ignore it), so
   `placed := \<lambda>(_, loc). p (location_vname loc)` at a fixed dummy
   owner gives exactly the flat projection. Universe: because the
   *vname-level* predicates are node-independent (below), one program-wide
   location list works -- no per-node universes, which is most of what made
   the owner-aware tree machinery heavy.
2. A new `lift_definition` projecting by vname predicate directly, with a
   bot-default precondition or its own universe parameter.

Recommendation: option 1 first -- it reuses proved correspondence lemmas and
keeps `Exec_Placement.thy` (the projection algebra) as the piece of the Exec
session that *deserves* to survive, while the tree/generator machinery on
top of it goes. Fall back to option 2 only if threading the degenerate owner
through the commute proofs turns out noisier than a fresh five-line
`lift_definition`.

### Covering holds at the vname level for both examples

The examples state `keep_local`/`publish_side` over `scoped_location`, and
the Interval pair looks non-covering (a global that is neither `balance`
nor `request_count` is in neither). But the spec consumes *vname*
predicates derived through the classifier:

```text
kl_v x = if gs x then (x = balance)       else True
ps_v x = if gs x then (x = request_count) else False
```

with `gs = declared_global placement_prog = {balance, request_count}`, so
every `gs`-global is one of the two named ones and every other vname is
covered by `kl_v`'s local clause: **cover holds**. Sign's `(\<top>, \<bottom>)`
pair covers trivially. Both examples are therefore genuine
`sound_dg_spec_unit_placed` instances at the vname level, and since neither
predicate depends on the node's owner, the node-independent `dg_spec` route
applies without any per-node policy plumbing.

## What the generalization buys

Immediately, on landing:

- `sound_dg_spec_unit_for` and `sound_dg_spec_unit_placed` become two
  interpretations of one theorem (~120 lines of isomorphic proof retired).
- The four `unit_dg_Hxxx_for` lemmas and `unit_dg_exec_analysis`'s
  `sound_dg_spec_st` become instances of one executable pullback locale;
  the placed instance gets the same theorem for the cost of its commute
  obligations only.

Downstream, it is the missing prerequisite chain for the remaining
`CORE_REFACTOR_PLAN.md` items:

- **Step 2.3 closes.** `Example_Sign_Placement` and
  `Example_Interval_Placement` migrate onto the executable carrier by the
  established flagship recipe (interpret, read the solver's own table),
  deleting their `sigma_abs`/`completed_sigma_abs` transport and the
  per-node `hook_gen_*`/`dg_refines_*`/`se_*` lemma walls (~700 and ~2500
  lines). With their last citations gone, the owner-aware halves die:
  `placed_dg_*_tree*` and `dg_refines_on_placed_*` in
  `Exec_DG_Trees.thy`/`Exec_DG_Refines.thy`, and
  `placed_abs_dg_gen_of`/`placed_dg_gen_of_strict` in
  `Exec_DG_Generator.thy`.
- **Step 2.7 unblocks partially.** What is left of `Voblint_Exec` after the
  deletion is the quotient state, the projection algebra, the flat
  `dg_gen_of` (still cited by `Run_Analysis_Sound`'s registration locales
  and two examples), and the Base pullback -- the moves 2.7 lists become
  mechanical again.
- **Step 3.1 shrinks and clarifies.** `dead_code_lift` was conflating two
  axes. The merge/split axis is this document; what remains for 3.1 is only
  the orthogonal Bot-carrier wrapper
  (`('dl,'dg) dg_spec => ('dl lifted,'dg) dg_spec` with
  `sound_dg_spec S ==> sound_dg_spec (dead_code_lift S)`), which then wraps
  *one* unlifted core instead of two -- and `unit_step_for_lifted` /
  `unit_dg_spec_for_lifted` / `base_dg_spec_for_lifted` /
  `base_dg_spec_st_for_lifted` become its instances as planned.
- The alignment register's kept alternative stays true: `sound_dg_hooks`
  remains in Core (it is what `sound_dg_spec` reduces to), and
  `gamma_join` is *promoted* from example-only to the generic locale's
  second instantiation target rather than deleted.

What this deliberately does **not** touch: `routed_dg_domain_exec`,
`base_dg_spec_st_for_lifted`, and everything the nine production instances
interpret. The Base shape's exclusive routing and its lifted carrier are a
different, sharper target (`gamma_unit \<subset> gamma_join`); folding it
into this locale would trade proven precision for uniformity. If a later
pass wants one roof over both, it goes through 3.1's wrapper, not through
widening this locale.

## Execution sequence

All six steps executed and committed (2026-09-01). G3's fallback became
the primary route: the classifier-split projection
(`project_placed_resolved_q`) replaced the owner-aware
`project_resolved_on_strict` transport outright, and G4 additionally grew
the `placed_dg_exec_analysis` registration locale mirroring
`unit_dg_exec_analysis`. G5 also migrated
`Example_Interval_Global_Flow_Sensitivity` (an unplanned consumer found by
the citation check); every value, check-verdict, and equation-count
regression reproduced unchanged across all three migrated examples.

Each step was I/Q-clean then batch-gated, committed separately, in
dependency order. A failed step falls back without stranding the previous
ones -- every intermediate state is a working build.

| # | Step | Gate risk |
| --- | --- | --- |
| G1 | `merge_split_spec` locale in `DG_Unit_Spec.thy`; re-derive `sound_dg_spec_unit_for` (in `DG_Soundness.thy`) and `sound_dg_spec_unit_placed` (in `Placement_Policy.thy`) as interpretations, names kept | combine-equation discharge for `unit_for` needs absorption + `reserved_ret_var`; if the characterization equations fight the record simps, fall back to keeping the two concrete proofs and generalizing only G2 |
| G2 | `merge_split_spec_exec` in `Exec_DG_Refines.thy` (or beside `unit_dg_exec_analysis`); re-derive the four `unit_dg_Hxxx_for` + `unit_dg_exec_analysis.sound_dg_spec_st` via interpretation | Interval flagship must rebuild unchanged; that is the whole regression content of this step |
| G3 | Executable placed mirror: flat projection via `project_resolved_on_strict` at a degenerate owner + program-wide universe, commute lemmas, `unit_dg_spec_placed_st` | the universe-threading through the commute facts is the untested part; fall back to a fresh vname-predicate `lift_definition` |
| G4 | Interpret `merge_split_spec_exec` for placed; migrate `Example_Sign_Placement` by the flagship recipe | first end-to-end validation; Sign chosen because its policy is the trivial covering |
| G5 | Migrate `Example_Interval_Placement` | largest file; per-node scope lists replaced by the program-wide universe |
| G6 | Delete the owner-aware halves; codegen + module-map + full gate; close 2.3 in `CORE_REFACTOR_PLAN.md` | name-by-name citation check before deleting, per the `pp_abs` lesson (2026-09-01 entry) |

## Open questions to settle during G1-G3, not before

- Whether the characterization locale states the combine equation at the
  record level or at the `gamma` level (weaker, easier to discharge, still
  sufficient for the soundness case). Start at the record level; weaken if
  `unit_for`'s discharge is awkward.
- Whether `Monovariant_Analysis_Result.thy` needs anything here at all: its
  `normalize_point`/`analysis_surface` are production readback machinery
  used by the migrated instances and only its `Exec_DG_Generator` import
  ties it to this cleanup; expected outcome is "unaffected", to be
  confirmed at G6.
- The exact home for `merge_split_spec_exec` given the session boundary
  (`DG_Unit_Spec` is Core and must not see `exec_dg_st`; the locale
  belongs where `unit_step_st` lives today).

## External review (2026-09-01)

An independent literature review of the carrier architecture (HOL-IMP
`Abs_State`, CompCert value analysis, SAS'13 domain functors, Verasco,
Refine_Monadic/Autoref, Transfer/Lifting) returned these verdicts; they are
recorded here because they settle the open architecture questions this doc
raised and constrain step 3.1 in `CORE_REFACTOR_PLAN.md`.

- **Keep `merge_split_spec` and `merge_split_spec_exec` as built.** The
  characterization-locale shape with four record-level commute facts is a
  good abstraction boundary; no surveyed system replaces it with something
  lighter. The two-carrier layout (representation-free `sound_dg_spec`
  above, quotient carrier below, readback homomorphism between) has no
  exact precedent but follows from keeping Core representation-free; the
  closest description is "HOL-IMP's executable quotient with a
  Verasco-style semantic interface retained above it".
- **No Refine_Monadic/Autoref migration, no full Lifting treatment.** The
  readback `fun_of gs` is left-total and right-unique but neither
  right-total (arbitrary functions have no finite two-default
  representation) nor left-unique, so `Quotient`/`bi_unique`-based
  automation does not apply. Estimated migration cost 800-1500+ lines for
  ~9 frozen instances; does not amortize.
- **Optional pilot only:** plain Transfer (a `st_rel gs` correspondence
  plus rules for the primitive layer: bot, sup, lookup, update,
  `combine_env`, `project_component`) as local proof automation *inside*
  the four commute lemmas, ~150-300 lines setup. Try on one hard placed
  instance; keep only if obviously shorter and batch-stable. No
  `rel_dg_spec` record relator -- it renames the four facts without
  eliminating the proofs.
- **`dead_code_lift` (step 3.1) shape is settled:** a genuine spec
  functor `('d,'g) dg_spec => ('d lifted,'g) dg_spec` with one generic
  preservation theorem, *reachability-first* -- `Bot` propagates strictly,
  `lift_gamma gamma Bot g = {}`, and the generic functor never normalizes
  a semantically empty live state to `Bot` (emptiness is not decidable
  from `d` alone and may depend on `g`). Normalization is a separate layer
  over an explicit emptiness interface (`empty d ==> gamma d g = {}`,
  strengthened to exactness where the executable mirror needs literal
  operation equality); the existing `*_for_lifted` records should be
  proved equal to the normalized specialization, keeping frozen names and
  generated OCaml unchanged. Precedent: Verasco's `t + Bot` outer layer,
  CompCert's `VA.Bot | State`, SAS'13 `botlift`.
- **The multiplicative win is the executable mirror theorem:** per lifter,
  one naturality/commute-preservation theorem
  (`commute rb S_st S ==> commute (map_lift rb) (L_exec S_st) (L S)`),
  changing growth from instances x lifters to instances + lifters. This
  outranks automating the ~40-line per-instance commute proofs.
- **Lifters do not commute in general** (Goblint: widening tokens must sit
  outside hashconsing and dead-code lifting; DeadCodeLifter deliberately
  emits one dead path rather than zero so `combine_env` still fires).
  Prove one preservation theorem per lifter and pairwise interaction laws
  only where needed; dead-code goes outermost for canonicality of `Bot`.
- **No deep embedding** of the spec family (`analysis_desc` AST +
  interpreter): the CLI dispatches over fully applied records, which is
  the Isabelle analogue of Goblint's first-class-module registry; the unit
  combine optimization (equal to the generic shape only under
  `reserved_ret_var`) is exactly what a reified normalizer would trip on.

## Lifter pipeline design (settles step 3.1's design pass)

The follow-up design session fixed the concrete shape for the lifter layer.
This supersedes the "needs its own design pass" caveat on step 3.1 in
`CORE_REFACTOR_PLAN.md`.

### Three layers per lifter

Every lifter contributes at three levels, and nothing else:

1. **Domain transformer** -- the carrier construction (`'a lifted`, later
   `'a x gas`, `'a x nat`), with its lattice instances. Already exists for
   dead code (`Reachability_Lift`).
2. **Spec transformer** -- an ordinary polymorphic function, Goblint's
   functor at the HOL term level:
   `dead_code_lift :: ('d,'g) dg_spec => ('d lifted,'g) dg_spec`. Every
   record field is `Bot -> dead, Lifted d -> unwrap, delegate to S, wrap`;
   global effects on a dead local input are inert. Future:
   `context_gas_lift :: nat => ('d,'g) dg_spec => ('d x gas,'g) dg_spec`,
   `widen_delay_lift :: nat => ('d,'g) dg_spec => ('d x nat,'g) dg_spec`.
3. **Verification transformer** -- two theorems per lifter:
   - soundness preservation:
     `sound_dg_spec S gamma gs ==> sound_dg_spec (dead_code_lift S) (lift_gamma gamma) gs`;
   - executable commute preservation (the multiplicative one):
     `commute rb S_st S ==> commute (map_lift rb) (dead_code_lift_exec S_st) (dead_code_lift S)`.

### Composition: pipe syntax, not a monad, not a DSL

Lifters are `Spec -> Spec` functions, so composition is function
application. A three-line bundle gives Goblint's visual pipeline:

```isabelle
bundle spec_lifter_syntax
begin
definition pipe :: "'a => ('a => 'b) => 'b"  (infixl "|>" 55)
  where [simp]: "x |> f = f x"
end
```

so a production stack reads, in Goblint's `control.ml` order (dead code
outermost, for one canonical `Bot` rather than a `(Bot, gas = k)` family):

```isabelle
interval_base
  |> context_gas_lift 3
  |> widen_delay_lift 2
  |> dead_code_lift
```

Rejected alternatives, with reasons: monadic `do` notation (no effect to
sequence -- `bind`/`return` buy nothing over application); a custom
`spec_pipeline` DSL via syntax translations (a second language, worse type
errors, no benefit over `|>`); a generic `spec_lifter` locale quantifying
over the carrier constructor (HOL cannot quantify over `L :: type => type`
first-class -- concrete lifters first, a preservation-property locale only
if a third lifter makes the pattern real); a deep `analysis_desc` datatype
(already rejected above).

Once two lifters exist, a named `production_spec S = S |> ... |> ...`
definition with chained `production_spec_sound` / `production_spec_commute`
corollaries mirrors `control.ml` exactly and is the intended endpoint.

### Implementation order for 3.1

1. **Landed** (`src/Core/Lifters/DG_Dead_Code_Lift.thy`): `dead_code_lift` +
   `lift_gamma` + `dead_code_lift_sound`; `sound_dg_spec_cong` (soundness
   sees only the four composed operations); `renormalize` /
   `dead_code_normalize` + `dead_code_normalize_sound` over the explicit
   emptiness interface.
2. **Landed** (in `DG_Base.thy`): the unlifted core `base_dg_spec_for` with
   its own soundness, four composed-operation agreement lemmas, and
   `base_dg_spec_sound` re-derived through the functor chain -- the three
   hand-rolled per-obligation walls are deleted. Field-level record
   equality is impossible (the frozen `dgs_combine_env` passthrough is not
   strict in the callee value; the generic lifter's is), so the connection
   is composed-operation agreement + `sound_dg_spec_cong`, the
   characterize-don't-rebuild lesson again.
3. **Landed** (same theory, representation-free): `dg_spec_commute` (four
   readback-commute equations over arbitrary local/global readbacks) with
   `dead_code_lift_commute` and `dead_code_normalize_commute` -- the
   instances-plus-lifters naturality theorems. Wiring the Base executable
   records onto them (subsuming `routed_dg_domain_exec`'s per-domain
   discharge) is the remaining Exec-side step; DG_Base_Exec's four
   whole-record commute theorems are already proved once, so this is
   packaging for the second lifter, not deduplication.
3a. **Resolved by deletion**: the unit route's `unit_dg_spec_for_lifted` /
   `gamma_unit_lifted` lifted *both* carriers, but the G-side lift was
   representation, not semantics -- `gamma_unit_lifted` sent `g = Bot` to
   `gamma_unit d0 bot`, i.e. the ordinary G-bottom, not the empty set, so
   global `Bot` never meant unreachability (the Goblint alignment:
   `DeadCodeLifter` wraps only `Spec.D`; global bottom means "no
   contribution"). A follow-up review proposed factoring it as
   `dead_code_lift` on D plus a `collapse_global` readback on G wired by
   `dg_spec_commute` -- but a citation sweep found the entire layer
   (`unit_step_for_lifted`, `assemble_env_abs`, `unit_dg_spec_for_lifted`,
   `gamma_unit_lifted`, its three soundness walls and
   `sound_dg_spec_unit_for_lifted`, ~460 lines) had zero consumers: absent
   from every other theory and from the generated OCaml. Deleted instead.
   When a consumer wants a dead-code-aware unit analysis, the canonical
   construction is one expression --
   `dead_code_normalize empty_pred (dead_code_lift (unit_dg_spec_for gs tf))`
   at `lift_gamma (gamma_unit gs)` -- with soundness falling out of
   `sound_dg_spec_unit_for` plus the two preservation theorems.
4. `|>` bundle when the second lifter lands, not before.
