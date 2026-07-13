# Stage 1: split local/global state representation

Goal: independent local and global abstract domains (`'l` for locals, `'g` for
globals), Goblint-style. Stage 1 is a representation refactoring in four
phases. No semantic change or analysis-specific framework hook is introduced.
Existing homogeneous theorem statements remain available as compatibility
endpoints.

Status: **Stages 1A--1D implemented for the abstract analysis pipeline**. 1A:
`src/Analysis/Generic/Domain/Split_State.thy` plus a bridge subsection in
`src/Analysis/Generic/Solver/Core/TD_Side_CFG.thy`. 1B:
`src/Analysis/Generic/Solver/Context/Split_Cmp_Gen.thy` (split-shaped trees,
transfer factory and CMP generator, each proven equal to its homogeneous
original) plus the sign instantiation in
`src/Analysis/Instances/Sign/Sign_Call_Spec.thy`. 1C: the remaining generic
tree constructors and factories, in the same theory (see the Stage 1C section
below for the constructor audit, the retain finding, and the executable-mirror
audit). 1D: `DG_Framework.thy` now carries independent `D`/`G` values through
strategy trees and the complete seeded CMP generator; homogeneous equality,
post-fixpoint transport, sign soundness transport, and the Retain validation
live in `DG_Framework.thy`, `Retain_Analysis.thy`, and `Sign_Call_Spec.thy`.

Stage 2's primary proof spine is implemented in `DG_Soundness.thy`.
`sound_dg_spec` derives solver post-fixpoints and collecting soundness directly
from a `dg_spec`, its two slot domains, and an analysis-supplied joint
concretization. `Mixed_Sign_Interval` is a direct interpretation. The
homogeneous unit framework is recovered by the `sound_transfer` sublocale;
its existing public endpoints remain available.

**Architectural correction (post-1C, executed through Stage 2):** comparing
against Goblint's `analyses.ml` showed the generic retain tree sits at the
wrong abstraction level -- retain is an *analysis* (its `D` = locals x global
snapshot), not a framework execution strategy. Section 6 has the corrected
framework/analysis boundary, the component classification, the replacement
design, and the migration sequence. Implemented: the framework core
`src/Analysis/Generic/Solver/Context/DG_Framework.thy` (value-opaque trees,
the heterogeneous `D`/`G` interface `dg_spec`, unit compatibility) and the
pure analysis theory `Retain_Analysis.thy` (all retain machinery, moved out
of `TD_Side_CFG` / `TD_Side_Eff_Cmp_Gen` / `Exec_Bridge`, plus the
hetero-framework validation); Stage-1C `split_*` scaffolding deleted.

## 1. Where the homogeneous representation is assumed

The representation is `type_synonym 'a abs_state = "vname => 'a"`
(`Abstract_Domain.thy:23`). Its consumers fall into five groups.

### Representation (definition site)

| Definition | File | Uses of the `vname => 'a` structure |
| --- | --- | --- |
| `abs_state` | `Generic/Domain/Abstract_Domain.thy` | the synonym itself |
| `fun :: (type, bounded_semilattice_sup_bot)` instance | same | pointwise lattice, inherited by every consumer |
| `is_global`, `combine_states <s\|t>`, `enter_state` | `IMP2/IMP2_Globals.thy` | the *store-level* local/global split the abstract split must mirror |

### Proof only (soundness statements)

| Definition | File | Structure use |
| --- | --- | --- |
| `gamma_state` | `Abstract_Domain.thy` | pointwise concretization `{s. ALL x. s x : gamma (sigma x)}` |
| collecting soundness spine (`TD_Side_Eff_Sound/Bounds/Soundness`, `TD_Side_Eff_Cmp_*`, `Call_Spec*`, `Analysis_Sound`, `Trace_Analysis_Sound`, `Mixed_Flow_Sound`, `*_Side_Soundness`) | Core/Context/Pipeline | only through `gamma_state` and the lattice; states otherwise opaque |

### Transfer only (point reads and updates)

| Definition | File | Structure use |
| --- | --- | --- |
| `aval_abs` locale, `afilter`, `bfilter` | `Abstract_Domain.thy` | `sigma x`, `sigma(x := a)` |
| `domain_transfer` record, `apply_tf` | `Generic/Equations/Constraint_System.thy` | fields typed over `'a abs_state` |
| `sign_transfer`, `enter_sign`, `interval` transfers, `Sign_Local_Effects` | `Instances/` | point updates + `is_global` in `enter` |

### Solver (lattice-opaque, except the restrictions)

| Definition | File | Structure use |
| --- | --- | --- |
| `restrict_local`, `restrict_global` | `Generic/Solver/Core/TD_Side_CFG.thy` | **the only generic code that inspects `vname => 'a` for the local/global split** (via `is_global`) |
| `unit_edge_tree`, `retain_edge_tree`, `local_edge_tree`, `unit_combine_tree`, `local_bot_on_locals`, `local_edge_invariant` | same | built from the restrictions |
| `side_env`, `glob_env`, `side_env_cmp`, generators (`TD_Side_Tree`, `TD_Side_RHS_Generator`, cmp/ctx/digest layers) | Core/Context | treat `'a abs_state` as an opaque `bounded_semilattice_sup_bot` element keyed by `pp + 'g` |
| vendor `strategy_tree`, `TD_side`, `part_post_solution` | `vendor/td-verification` | fully polymorphic in the value type `'d` -- **no assumption, never needs changes** |

### Executable only

| Definition | File | Structure use |
| --- | --- | --- |
| `'a st` quotient, `fun_of_st`, `restrict_local_st`, `restrict_global_st` | `Generic/Domain/Exec_St.thy` | association-list mirror of `vname => 'a`, already carries the executable restrictions |
| fold mirrors + transports | `Generic/Solver/Exec/Exec_*Bridge.thy`, `Solver_Menu.thy` | via `'a st` and `fun_of_st` |
| `Example_*` runs | `Formalization/Examples/` | via the above |

### Dependency graph

```
'a abs_state = vname => 'a            (Abstract_Domain)
 |
 +-- gamma_state ................ proof spine (all soundness statements)
 |
 +-- afilter / bfilter,
 |   domain_transfer record ..... transfer layer (point reads/updates)
 |    +-- Sign / Interval instances
 |
 +-- restrict_local/_global ..... ONLY generic structural inspection
 |    +-- unit/retain/local edge trees, unit_combine_tree   (TD_Side_CFG)
 |         +-- effectful_domain_transfer, generators, side_env,
 |             cmp/ctx/digest layers, Call_Spec ............ opaque in the
 |             state type; vendor solver polymorphic in 'd
 |
 +-- 'a st mirror ............... executable layer (restrict_*_st already split)
```

Two structural observations drive the staging:

1. The solver's unknown space `pp + 'g` already separates local unknowns
   (`Inl`) from global unknowns (`Inr`). The split-state migration moves the
   same separation from the *unknown space* into the *value type*; the vendor
   solver never sees the difference.
2. All structural knowledge of "locals vs globals inside one state" is
   concentrated in `is_global` (store level), `restrict_local`/`restrict_global`
   (abstract level), and `enter`/`combine` transfers. Everything else is
   lattice-opaque or pointwise.

## 2. Representation design (Stage 1A, implemented)

`src/Analysis/Generic/Domain/Split_State.thy`:

```
type_synonym ('l, 'g) split_state = "'l abs_state * 'g abs_state"
```

* `wf_split lg`: the local component is `bot` on globals, the global component
  `bot` on locals -- exactly the shape `restrict_local`/`restrict_global`
  produce.
* `merge_state lg = (%x. if is_global x then snd lg x else fst lg x)`
  (homogeneous `('a,'a) split_state => 'a abs_state`; selection, so total and
  class-free; coincides with `fst lg \/ snd lg` on well-formed states:
  `merge_state_eq_sup`).
* `split_state sigma` = the pair of restrictions (`split_state_eq_restrict`
  in `TD_Side_CFG`).

Why a pair with an invariant, not a `typedef`/`quotient_type`: the pair stays
executable and pattern-matchable, needs no lifting/transfer setup in
consumers, and the invariant is exactly the shape the existing restrictions
already produce. Why merge by selection, not join: no class constraints,
`merge_state (split_state sigma) = sigma` holds unconditionally, and on
well-formed states it agrees with the join anyway.

### Isomorphism and transport lemmas (all proved, no `sorry`)

| Lemma | Statement |
| --- | --- |
| `merge_split_id` | `merge_state (split_state sigma) = sigma` (merge o split = id, unconditional) |
| `split_merge_id` | `wf_split lg ==> split_state (merge_state lg) = lg` (split o merge = id on well-formed states) |
| `wf_split_split_state` | `split_state` lands in well-formed states |
| `merge_state_bij` | `bij_betw merge_state {lg. wf_split lg} UNIV` -- the headline isomorphism |
| `merge_state_le_iff` | order transports both ways: `merge_state lg1 <= merge_state lg2 <-> fst lg1 <= fst lg2 & snd lg1 <= snd lg2` (needs `wf_split lg1` only) |
| `merge_state_mono`, `split_state_mono1/2` | monotone conversions |
| `merge_state_bot/sup`, `split_state_bot/sup`, `wf_split_bot/sup` | lattice operations commute with the conversions and preserve well-formedness |
| `gamma_split_merge` | `gamma_split lg = [[merge_state lg]]` -- split concretization agrees with `gamma_state` under the isomorphism |
| `gamma_split_split_state`, `gamma_split_eq_sup`, `gamma_split_bot`, `gamma_split_mono` | derived concretization transport |

`gamma_split` is the *heterogeneous* concretization
(`('l::sound_domain, 'g::sound_domain) split_state => store set`, guarded by
`is_global`); it is the statement form Stage 1D soundness theorems will use.

Bridge to the existing machinery (`TD_Side_CFG.thy`, subsection
"Split-state bridge"):

| Lemma | Statement |
| --- | --- |
| `split_state_eq_restrict` | `split_state sigma = (restrict_local sigma, restrict_global sigma)` |
| `wf_split_restrict` | restriction pairs are well-formed |
| `merge_state_restrict` | `merge_state (restrict_local A, restrict_global B) = restrict_local A \/ restrict_global B` -- the abstract combine `restrict_combine` in split form |

Nothing instantiates the split representation yet, so every existing analysis
is byte-for-byte unchanged; the homogeneous instance `'l = 'g = 'a` is what the
isomorphism certifies.

## 3. Migration boundary

The first change belongs in the **Abstract_Domain layer** (as the sibling
theory `Split_State`), not in `Constraint_System`, `TD_Side_CFG`,
`strategy_tree`, or `effectful_domain_transfer`:

* `strategy_tree` / the vendor solver are polymorphic in the value type --
  there is nothing to change there, at any stage.
* `effectful_domain_transfer` and the generators only *consume* the state type
  carried by the trees; re-typing them first would force the whole solver
  spine to change in one step.
* `TD_Side_CFG` is where the split is *used* (restrictions, trees), not where
  the representation is *defined*; it becomes the Stage 1B target and for now
  only receives the bridge lemmas.
* Defining the representation standalone costs nothing downstream: Stage 1A
  adds one theory plus three bridge lemmas and changes no existing statement.

## 4. Staged migration plan

### Stage 1A (this change) -- representation + isomorphism

Done, see section 2. Exit criterion: `Voblint_Analysis` batch green, no new
`sorry`, no existing statement changed.

### Stage 1B -- thread `split_state` through the CMP generator, `'l = 'g` (implemented)

Implemented in `Split_Cmp_Gen.thy` (+ `combine_split` in `Split_State.thy`,
sign instantiation in `Sign_Call_Spec.thy`).

**Boundary.** The audit of the CMP pipeline
(`effectful_domain_transfer`, `strategy_tree`, `side_cfg_T_eff_cmp_seed`,
`side_rhs_fold_ctx`, `side_env_cmp`, global/local routing) shows the
`vname => 'a` structure is inspected in exactly two places:

1. the tree bodies produced by the transfer factory (`unit_edge_tree`,
   `unit_combine_tree` -- via `restrict_local` / `restrict_global`), and
2. the generator's entry-seed decomposition of `s0`
   (`restrict_local s0` accumulator seed, `restrict_global s0` entry `Side`).

`side_rhs_fold_ctx`, `map_ltree`/`map_gtree` routing, `side_env_cmp` and the
vendor solver are opaque in the state type -- unchanged.

**Split artefacts, each proven equal to its original** (so the migrated
generator produces literally the same equation system):

| Split artefact | Original | Equality |
| --- | --- | --- |
| `combine_split` (pair surgery: caller locals, callee globals) | `combine_abs` | `combine_split_split_state`: `combine_split (split_state A) (split_state B) = split_state <A\|B>` |
| `split_edge_tree` (splits the transfer result once; `Side` = global half, `Answer` = local half) | `unit_edge_tree` | `split_edge_tree_eq_unit` |
| `split_combine_tree` (`combine_split` of the two split query results) | `unit_combine_tree` | `split_combine_tree_eq_unit` |
| `split_etf_of_transfer` | `unit_etf_of_transfer` | `split_etf_of_transfer_eq_unit` (+ `sound_effectful_transfer_split_of_transfer`) |
| `side_cfg_T_eff_cmp_split_seed` (entry seed via `split_state s0` components) | `side_cfg_T_eff_cmp_seed` | `side_cfg_T_eff_cmp_split_seed_eq` (+ `_const` collapse to the fixed-frame generator, `part_post_solution_split_seed_iff`) |
| `spec_generator_split` (in `goblint_analysis_spec`) | `spec_generator` | `spec_generator_split_eq`, `part_post_solution_spec_split_iff` |
| `sign_etf_split`, sign endpoint `sign_spec_post_fixpoint_sound_split` | `sign_etf_unit`, `sign_spec_post_fixpoint_sound` | `sign_etf_split_eq_unit`, `Sign_spec_generator_split_eq` |

**Theorem audit.** No existing theorem changed -- statements, proofs and types
are untouched; the migration is purely additive. Every new fact is either a
definition, an equality to an existing constant, or a wrapper discharged by
rewriting along such an equality (`pp[unfolded Sign_spec_generator_split_eq]`
for the sign endpoint). Executable behaviour is unchanged twice over: the
`'a st` mirror is untouched, and post-fixpoints of the migrated and original
generators coincide by `part_post_solution_split_seed_iff`.

**Dependency graph after 1B** (new nodes marked `*`):

```
Split_State ('l,'g) split_state, merge/split iso, combine_split*
  |
  +-- TD_Side_CFG bridge (split_state_eq_restrict, ...)
        |
        +-- Split_Cmp_Gen* : split trees = unit trees
        |     split_etf_of_transfer = unit_etf_of_transfer
        |     side_cfg_T_eff_cmp_split_seed = side_cfg_T_eff_cmp_seed
        |     spec_generator_split = spec_generator
        |
        +-- Sign_Call_Spec : sign_etf_split = sign_etf_unit,
              sign_spec_post_fixpoint_sound_split
```

### Stage 1C -- remaining tree infrastructure, `'l = 'g` (implemented)

Implemented in `Split_Cmp_Gen.thy` (Stage 1C section; new import
`Clean_RRead_Sound` for the clean tree).

#### Constructor audit

Every tree constructor in the generic layer, classified. "Naturally split"
means the body is a composition of split-level operations
(`split_state` components, `combine_split`, `merge_state`); all such
constructors are migrated with a proven equality `split_version = original`.

| Constructor | File | Classification | Split version / equality |
| --- | --- | --- | --- |
| `unit_edge_tree` | `TD_Side_CFG` | naturally split | `split_edge_tree` (1B), `split_edge_tree_eq_unit` |
| `unit_combine_tree` | `TD_Side_CFG` | naturally split | `split_combine_tree` (1B), `split_combine_tree_eq_unit` |
| `retain_edge_tree` | `TD_Side_CFG` | **intentionally mixes** (flow-sensitive global copy in the local unknown); still split-representable via pair reassembly | `split_retain_edge_tree`, `split_retain_edge_tree_eq` |
| `clean_edge_tree` | `Clean_RRead_Sound` | same pattern as retain (Answer keeps the whole result; reads only the local slot) | `split_clean_edge_tree`, `split_clean_edge_tree_eq` |
| `local_edge_tree` | `TD_Side_CFG` | naturally split (`combine_split` of split result with pass-through globals) | `split_local_edge_tree`, `split_local_edge_tree_eq` |
| `mixed_etf_edge_tree` | `TD_Side_CFG` | dispatcher (no own body) | `split_mixed_etf_edge_tree`, `split_mixed_etf_edge_tree_eq` |
| `unit_combine_tree_ctx` | `TD_Side_Tree` | naturally split (same `combine_split` shape; the context routing is value-dependent but state-opaque) | `split_combine_tree_ctx`, `split_combine_tree_ctx_eq` |
| `make_side_rhs_tree_eff` | `TD_Side_Tree` | naturally split (entry-seed decomposition only) | `split_make_side_rhs_tree_eff`, `split_make_side_rhs_tree_eff_eq`, `side_cfg_T_eff_split_eq` |
| `edge_constraint_tree` | `TD_Side_Tree` | homogeneous-opaque (alias for `apply_etf`; no structure inspection) | nothing to migrate |
| `seqcomp_tree`, `map_ltree`, `map_gtree` | monad/relabel layer | fully polymorphic in the payload | nothing to migrate |
| `route_tree`, `sideg_tree` | `Instances/NamedGlobalSign` | instance-level (named-global writer), outside the generic layer | Stage 1D instance work |

`retain_combine_tree` and `local_combine_tree` do not exist: all three
factories (`unit`, `retain`, `mixed`) share `unit_combine_tree` as their
`etf_combine` field, and `clean` does too.

Factories migrated with equalities: `split_retain_etf_of_transfer` (=
`retain_etf_of_transfer`), `split_mixed_etf_of_transfer` (=
`mixed_etf_of_transfer`), `split_clean_etf_of_transfer` (=
`clean_etf_of_transfer`), each with the soundness corollary transported by
rewriting (`sound_effectful_transfer_split_retain` / `_split_mixed`).

#### The retain finding (design audit)

Why retain stores global information inside the `Answer` payload:

* The global unknown (`Inr` slot) is *flow-insensitive* -- `glob_env` joins
  every published write, everywhere. A transfer that wants the globals *as
  known at this program point* must carry that information in the only
  pp-indexed unknown available: the local slot. `TD_Side_CFG`'s retain
  subsection states this directly ("the local slot ... now carrying the
  flow-sensitive global"), and the keyed retain example
  (`Exec_Sign_Cmp_Keyed_Retain_Run`) exists to exhibit the precision gain.
* It is **not an implementation artifact**: `sides_retain_eq_unit` and
  `etf_full_retain_eq_unit_edge_tree` prove retain differs from `unit_edge_tree`
  *only* in the Answer payload -- the whole point of the constructor is that
  payload.
* It **is cleanly split-representable**: the split version publishes the
  global half (`snd (split_state res)`) and answers the *reassembled pair*
  (`merge_state (split_state res) = res`, the Stage 1A isomorphism), giving a
  definitional equality (`split_retain_edge_tree_eq`). Nothing blocks the
  split representation.
* The architectural consequence (corrected post-1C, see section 6): the
  snapshot belongs to the **retain analysis's own `D`**, not to the framework.
  Goblint's framework never copies `G` into `D`; an analysis that wants a
  flow-sensitive global snapshot chooses `D = locals x snapshot` itself.
  `retain_edge_tree` is therefore reclassified from framework strategy to
  analysis implementation; the pair-domain version lives in
  `Retain_Analysis.thy` and is proven to reproduce it exactly. Unit/local/mixed
  transfers keep a locals-only `D`. This remains a typing decision, not a
  semantic blocker.

#### Executable mirror audit

Every `*_st` implementation, classified per the Stage 1C criterion (migrate
only what is mechanically identical):

| Mirror | Classification |
| --- | --- |
| `unit_edge_tree_st`, `unit_combine_tree_st`, `retain_edge_tree_st`, `clean_edge_tree_st` (`Exec_Bridge`) | duplicated implementation at `'a st` (quotient type, lifted `restrict_local_st`/`restrict_global_st`), connected by `fun_of_st` simulation lemmas -- not mechanically identical, no migration |
| `unit_combine_tree_ctx_st`, `side_rhs_fold_ctx_st` (`Exec_Ctx_Bridge`) | same |
| `make_side_rhs_tree_eff_st`, `side_cfg_T_eff_cmp_st`, `side_cfg_T_eff_cmp_seed_st` (`Exec_Bridge`/`Exec_Cmp_Bridge`) | same |
| `restrict_local_st`, `restrict_global_st`, `combine_abs_st`, `st_of_abs` (`Exec_St`, `Exec_Ctx_Bridge`) | executable split *components* already exist; a split executable state is `('l st * 'g st)` -- a Stage 1D type change only |

None are semantically different from their abstract counterparts (each has a
`fun_of_st` simulation lemma); none are mechanically derivable (the `'a st`
quotient forces separate definitions + transfer proofs). Hence no executable
migration in 1C -- and none is needed: post-fixpoints transport through the
existing simulation lemmas to the abstract generators, which 1B/1C prove
equal to their split versions.

#### Stage 1D pre-implementation audit (resolved)

| Component | Readiness for independent `('l, 'g)` |
| --- | --- |
| vendor solver, `strategy_tree`, `seqcomp_tree`, `map_ltree`/`map_gtree`, `side_rhs_fold*` | **ready** (polymorphic in the payload) |
| split trees / factories / generators (1B+1C artefacts) | **blocked only by type changes**: `Side` payloads become `'g abs_state` (`snd`), `Answer` payloads `'l abs_state`; retain/clean carry their snapshot inside their own analysis `D` (section 6), not in a framework payload type |
| solver unknown-value type | **blocked only by a type decision**: the vendor `eqsT` has a single value type `'d`, so `Inl`/`Inr` slots cannot be typed differently; Stage 1D sets `'d` to a componentwise-ordered D-x-G value with `wf_split`-style slot invariants (the existing `inr_slot_locals_bot` / `inl_slot_globals_bot` are exactly the two halves of `wf_split`). **Not the raw pair**: `CFG_Def` imports `HOL-Library.Product_Lexorder`, so `'l * 'g` already carries the lexicographic order repo-wide and the componentwise `Product_Order` instances clash (arity conflict, observed). Stage 1D uses the copy type `dg_state` (`Retain_Analysis.thy`), which carries the componentwise `bounded_semilattice_sup_bot` instance. No solver modification needed. |
| soundness statements | **blocked only by type changes**: `gamma_state` -> `gamma_split` (Stage 1A already provides it, heterogeneous, with `gamma_split_merge` recovering today's statements at `'l = 'g`) |
| transfer records (`domain_transfer`, `effectful_domain_transfer`) | **blocked only by type changes**: fields over the pair; enter/combine get genuinely split types mirroring `enter_state` / `<s\|t>` |
| executable layer | **blocked only by type changes**: `('l st * 'g st)` pair, components already exist |
| retain/clean transfers | **resolved as analyses** (section 6): each defines its own snapshot-carrying `D`; the framework stays `Answer : D`, `Side : G`. Not a semantic blocker. |
| **semantic blockers** | **none identified at the tree level.** The single constraint of substance is the vendor solver's one-value-type interface, and it is absorbed by `'d := dg_state` (componentwise copy type) without touching the solver. |

The audit produced the following implementation map, completed in Stage 1D:

```
'd := ('l abs_state, 'g abs_state) dg_state at the eqsT level
  |
  +-- trees: step_edge_tree (analysis-parametric); Side globs-typed,
  |     Answer locals-typed; retain/clean become analyses whose D carries
  |     the snapshot (Retain_Analysis.thy is the template)
  +-- transfer records over dg_state; enter/combine split-typed
  +-- side_env / glob_env readings via gamma_split
  |     (slot invariants = wf_split halves, already stated)
  +-- soundness endpoints restated with gamma_split
  |     (homogeneous case recovered via gamma_split_merge)
  +-- exec mirror at ('l st * 'g st)  [later executable slice]
```

### Stage 1D -- independent `D` and `G` (implemented)

The solver still has one value type. `dg_state D G` encodes the two typed
slots without changing the vendored solver:

* local unknowns contain `DG d bot`;
* global unknowns contain `DG bot g`;
* analysis steps have type `D => G => G * D`;
* `side_rhs_fold_dg` joins only the `D` component of Answers;
* `side_cfg_T_eff_cmp_seed_dg` seeds the entry `D` and `G` independently.

The new generator preserves predecessor routing, context relabeling, combine
routing, frame seeding, and entry publication. Only the transported value
types differ.

#### Homogeneous-interface audit and implemented type changes

| Component | Before | Stage-1D form | Disposition |
| --- | --- | --- | --- |
| `effectful_domain_transfer` | every tree returns and publishes one `'a abs_state` | `dg_spec D G`, whose edge and combine fields implement `D => G => G * D` | legacy record retained as a compatibility and soundness bridge |
| `edge_tf_tree` | `strategy_tree pp unit ('a abs_state)` | `dg_edge_tree step`, returning `dg_state D G` with pure-D Answers and pure-G Sides | heterogeneous path implemented |
| `unit_edge_tree` | homogeneous restriction-based tree | `dg_edge_tree (apply_unit_dg_spec ...)` | equality/denotation compatibility proved |
| `unit_combine_tree` | caller/callee values share one state type | `dg_combine_tree` / `dg_spec_combine_tree` over `D` and `G` | unit compatibility proved |
| `side_rhs_fold_ctx` | joins homogeneous Answers | `side_rhs_fold_dg` joins `locals` only | implemented with traverse/sides/dependency transport |
| `side_cfg_T_eff_cmp_seed` | one state supplies local accumulator and entry Side | `side_cfg_T_eff_cmp_seed_dg ... botD entryD entryG` | implemented |
| strategy-tree wrappers | payload-polymorphic `seqcomp_tree`, `map_ltree`, `map_gtree` | unchanged; `pack_dg_tree` and Retain transport commute with them | no retyping required |
| generator interfaces | `effectful_domain_transfer` plus one seed state | `dg_spec D G` plus separate D/G seeds | implemented additively |
| post-fixpoint predicates | one homogeneous solver value | same vendored predicate over `dg_state D G` | homogeneous and Retain representation equivalences proved |
| soundness locales | stated over the homogeneous transfer record and `gamma_state` | existing endpoints are recovered by representation transport | theorem statements preserved; direct heterogeneous locale restatement is unnecessary for Stage 1D |

#### Compatibility and validation

For `D = G = 'a abs_state`, `pack_dg_tree` embeds the old system. Theorems in
`DG_Framework.thy` prove tree traversal, side effects, dependencies, equation
systems, exact solutions, and post-fixpoints coincide. The sign instance then
reuses the existing collecting-soundness endpoint without changing or
weakening it.

Retain uses a genuinely heterogeneous choice:

```
D = dg_state ('a abs_state) ('a abs_state)   -- locals + snapshot
G = 'a abs_state                             -- published globals
```

`retain_dg_spec` is an ordinary `dg_spec`. `retain_dg_generator` uses the same
generic CMP generator as the unit/sign instance. Its equation results, side
effects, dependencies, order, and post-fixpoints transport to the existing
Retain analysis through `retain_hetero_rep`. The framework never observes the
snapshot field. `sign_retain_dg_post_fixpoint_iff` is the concrete sign/Retain
witness.

#### First mixed-domain analysis

`Mixed_Sign_Interval.thy` supplies the first analysis whose two domains have
different meanings:

```
D = sign abs_state    -- flow-sensitive answer at each CFG point
G = ivl abs_state     -- one flow-insensitive invariant for the whole CFG
```

Here `G` means the analysis's shared side fact. It is not the subset of an
IMP2 store whose names satisfy `is_global`. The generic `dg_state.globs`
projection names the solver slot and imposes no meaning on its contents. This
analysis chooses an Interval store over all program variables as `G`; another
analysis may publish a reachability set, a counter, or a different invariant.

Each edge applies the Sign transfer to its local `D` input and the Interval
transfer to the shared `G` input. It returns the next Sign state as the
`Answer` and publishes the next Interval state through `Side`. Procedure
combines follow the same separation. The analysis uses the ordinary
`dg_spec`, `dg_edge_tree`, and `side_cfg_T_eff_cmp_seed_dg` interfaces;
the framework contains no mixed-analysis hook.

The old homogeneous interface required both results to inhabit one lattice.
Representing this analysis there would require a Sign/Interval product, an
artificial sum with routing invariants, or an embedding of one abstraction
into the other. A product would copy the flow-insensitive Interval component
through every local unknown. An embedding would discard either Sign's compact
local precision or Interval's numeric bounds. Independent `D` and `G`
slots express the intended information flow directly.

`mixed_si_post_solution_collect_sound` composes the generic solver
post-solution predicate with the existing Sign and Interval transfer
soundness theorems. Its only analysis-specific obligations identify entry,
edge-target, and combine-target coverage and exclude procedure-entry edges
from this intentionally intraprocedural witness. The generic collecting
mathematics is reused.

`Example_Mixed_Sign_Interval_GraphViz.thy` compiles `x := -1; x := 2`,
runs the TD side solver, proves termination and the resulting post-solution,
and checks:

* `x` is an IMP2 local variable (`is_global ''x''` is false);
* the intermediate Sign answer for `x` is negative;
* the exit-local Sign value for `x` is positive;
* the published Interval invariant for `x` is `[-1, 2]`.

The interval follows directly from the side equations. The initial side seed
publishes the singleton `[0, 0]`. The first assignment applies the Interval
transfer to the shared summary and publishes `[-1, -1]`; the second publishes
`[2, 2]`. The side-effecting solver joins all contributions into its single
`Inr ()` unknown:

```
[0, 0] ⊔ [-1, -1] ⊔ [2, 2] = [-1, 2]
```

The exit Sign answer only follows the final control-flow state, so it is
`SPos`. The shared Interval invariant intentionally also describes earlier
reachable states, so it contains `-1` and the entry seed `0`. The same local
variable appears in both facts because their meanings differ by sensitivity
and abstraction, not because `x` belongs to two source-language namespaces.

#### Where `G` flows (mechanism)

The five stations of a `G` value, with the definitions that carry it:

1. **Transfer.** The analysis supplies `dg_spec_step S a : D => G => G x D`
   (`mixed_si_step a d g = (apply_tf ivl_tf a g, apply_tf sign_tf a d)`).
   The framework never applies `a` to `G` itself; it only calls the step.
2. **Side publication.** `dg_edge_tree step u` queries the predecessor's
   local unknown and the global slot, then emits
   `Side () (DG bot (fst r))` before answering `Answer (DG (snd r) bot)`.
   The boundary theorems `dg_edge_tree_answer_pure_D` /
   `dg_edge_tree_side_pure_G` hold for every step: Answers carry no `G`,
   publications carry no `D`.
3. **Equation system.** `side_cfg_T_eff_cmp_seed_dg` folds the edge and
   combine trees with `side_rhs_fold_dg`, which joins only the `locals` of
   Answers into the per-point equation result; `Side` nodes pass through the
   fold untouched (`seqcomp_tree`). The entry equation additionally wraps
   `Side (gkey c) (DG bot s0g)`: the `G` seed is published, never folded
   into an answer.
4. **Solver.** The vendored side-effecting TD solver accumulates every
   publication into the global unknown by join; its output contract
   `part_post_solution` demands `sides_of_rhs (T u) sigma <= sigma` for each
   solved unknown, so the final `sigma (Inr ())` upper-bounds every
   publication *evaluated at the final `sigma`*.
5. **Theorem.** `mixed_si_postfix` reads that contract back as
   `apply_tf ivl_tf a (mixed_si_G sigma) <= mixed_si_G sigma` for every edge,
   i.e. `G` is one transfer-closed invariant. `mixed_si_postfix_collect_sound`
   then instantiates the generic `sound_transfer.post_fixpoint_sound_at` with
   the *constant* environment `(%_. mixed_si_G sigma)`, and intersects with
   the flow-sensitive `D` result: `mixed_si_gamma sigma v =
   [[mixed_si_D sigma v]] Int [[mixed_si_G sigma]]`.

So `G` is **analysis-defined shared information**: whatever the analysis
publishes through `Side`, joined by the solver, constrained only by the
analysis's own soundness proof. It is not the `is_global` half of an IMP2
store (that is one possible choice, the one the unit analysis makes), not a
copy of `D` (slot purity), and flow-insensitivity is a property of *this*
analysis's decision to publish transfer images of the single shared summary —
the digest/keyed layers publish context-indexed `G`s through the same
mechanism. The final interval is exactly the join of the entry seed and one
publication per edge because the example is loop-free and each publication is
a constant-assignment image: nothing else ever reaches the `Inr ()` unknown,
and `part_post_solution` forces at least that join while the always-join TD
run computes exactly it.

Its DOT output annotates CFG nodes with Sign stores and renders the shared
Interval store in a separate side-invariant cluster. This exposes the domain
split in the executable pipeline.

#### Architecture before and after

Before Stage 1D:

```
effectful_domain_transfer ('a abs_state)
        |
homogeneous trees: Answer = Side = 'a abs_state
        |
side_cfg_T_eff_cmp_seed
        |
TD_side + homogeneous soundness locales
```

After Stage 1D:

```
analysis: dg_spec D G, step : D => G => G * D
        |
dg_edge_tree / dg_combine_tree
        |
side_rhs_fold_dg
        |
side_cfg_T_eff_cmp_seed_dg
        |
TD_side over dg_state D G
        |
post-fixpoint transport -> preserved soundness endpoints
```

## 5. Verification

The migration gate is run once after the complete slice: every touched theory
must be error-free in I/Q, the analysis `sorry` inventory must be empty, and
`Voblint_Analysis` must pass the batch build. Intermediate stages use I/Q only.
The mixed executable witness is part of the final formalization gate.

## 6. Architectural correction: retain is an analysis, not a framework strategy

Stage 1C classified `retain_edge_tree` as "intentionally mixes" and planned to
carry it into Stage 1D as a framework tree with a pair-valued Answer type.
Comparing against Goblint's framework shows that classification put retain at
the wrong abstraction level. This section is the corrected design; it
supersedes any earlier wording that suggested generic retain survives into the
final framework.

### 6.1 Goblint comparison (`src/framework/analyses.ml`)

In Goblint, `module type Spec` declares per analysis:

* `module D : Lattice.S` -- the flow-sensitive local domain, chosen by the
  analysis;
* `module G : Lattice.S` -- the flow-insensitive global domain, chosen by the
  analysis;
* `ctx.global : V.t -> G.t` / `ctx.sideg : V.t -> G.t -> unit` -- the only
  channel between the two.

The framework transports `D` values along edges and accumulates `G` values at
global unknowns. It **never automatically copies `G` into `D`**: a transfer
that wants global information calls `ctx.global` and decides itself what (if
anything) of the result to keep in its `D`. Analyses that retain flow-sensitive
copies of global information (e.g. the privatization variants of the base
analysis) do so by *defining `D` to contain that copy* -- a per-analysis domain
decision, invisible to the framework.

Our `retain_edge_tree` (`TD_Side_CFG.thy`) instead bakes "the local unknown
carries the written globals" into a *generic tree constructor*, and
`inl_glob_le_glob_env` / `sound_effectful_transfer_framed_le`
(`Constraint_System.thy`) compensate at the framework level for local slots
containing globals. Both exist only because the homogeneous `'a abs_state`
made D and G the same type, so "keep the globals in the Answer" was a one-line
payload change. That is historical, not architectural.

### 6.2 Corrected responsibilities

Framework:

* the strategy tree transports `Answer : D` and `Side : G` (in
  `Retain_Analysis.thy`: `step_edge_tree`, which queries the local and global
  unknowns and forwards both to an analysis-supplied step function);
* the solver knows only `D` and `G` (one `eqsT` value type; slot invariants);
* the framework never assumes `D` contains `G` and never copies `G` into `D`.

Analysis:

* chooses `D` and `G`;
* decides whether `D` contains only local information, local information plus
  cached globals, summaries, snapshots, or anything else flow-sensitive;
* implements its transfer, its `Side` publication, and discharges its own
  soundness obligations (for a snapshot-carrying `D`: the analogue of
  `inl_glob_le_glob_env`, i.e. "my snapshot is bounded by the published
  globals", becomes an analysis lemma, not a framework premise).

Retain under this boundary is one example analysis with
`D = Local x GlobalSnapshot`, `G = Global`, not a framework feature.

```
                       FRAMEWORK (value-opaque)
  vendor TD_side solver -- eqsT over one value type 'd; slot invariants
      |
  step_edge_tree step u = QueryL u; QueryG (); Side (fst (step d g));
      |                   Answer (snd (step d g))        [never inspects 'd]
      |
      |  step : D => G => G x D          <-- the analysis boundary
      v
                       ANALYSES (choose D, G, step)
  unit analysis            retain analysis                clean analysis
  D = locals only          D = locals x snapshot          D = locals x snapshot
  step = unit_step         step = retain_dg_step          (same pattern,
  (restrict_local /        (snapshot maintained by         local-slot read
   restrict_global)         the analysis itself)           only)
      |                        |
  = unit_edge_tree         = retain_edge_tree  (definitional equalities:
                             step_edge_tree_unit / _retain; dg-form proven
                             equivalent via the Stage-1A isomorphism)
```

### 6.3 Component classification (evidence-based, Stage-2 state)

| Component | Evidence | Layer | State |
| --- | --- | --- | --- |
| `unit_edge_tree`, `unit_combine_tree` (`TD_Side_CFG.thy`) | pure `Answer(restrict_local)` / `Side(restrict_global)` transport | framework; `step_edge_tree_unit` factors the restricts into the unit analysis step | KEEP |
| `step_edge_tree`, `dg_edge_tree`, `dg_combine_tree`, `dg_spec`, `dg_state` (`DG_Framework.thy`) | value-opaque trees, slot packing only; `dg_edge_tree_answer_pure_D` / `dg_edge_tree_side_pure_G` hold for *every* step | framework core | KEEP (framework theory, no analysis knowledge) |
| `retain_edge_tree` + traverse/sides/etf_full lemma set | differs from unit only in the Answer payload (`sides_retain_eq_unit`, `etf_full_retain_eq_unit_edge_tree`) | retain analysis | **MOVED** to `Retain_Analysis.thy` (was `TD_Side_CFG`) |
| `retain_etf_of_transfer` + `sound_effectful_transfer_retain_of_transfer` | factory instantiating every edge with `retain_edge_tree` | retain analysis | **MOVED** to `Retain_Analysis.thy` (was `TD_Side_CFG`) |
| `inl_glob_le_glob_env`, `sound_effectful_transfer_framed_le` (`Constraint_System.thy`) | **audit corrected the earlier MOVE verdict**: `sign_sound_etf_unit_framed_le` shows the *unit* transfer discharges the same contract, and the `_le` endpoints in `TD_Side_Eff_Cmp_Gen` are analysis-agnostic. The contract states the framework's enter obligation under the *weakest* slot invariant -- it never mentions snapshots structurally | framework contract, discharged per analysis | KEEP (prose reworded analysis-agnostic: "snapshot relaxation") |
| `inl_glob_le_keyed_ctx`, `pull_gk` lemmas, `_le` enter/combine/collect endpoints (`TD_Side_Eff_Cmp_Gen.thy`) | parametric in the transfer; premises are slot invariants, not tree shapes | framework | KEEP (prose reworded: "keyed snapshot invariant") |
| exact-solution reduction (`restrict_global_traverse_retain_intra`, `part_solution_imp_inl_glob_le_keyed_ctx`, `inl_glob_le_keyed_ctx_on_vars`/`_full`) | statements assume `apply_etf etf a u = retain_edge_tree (F a) u` -- the retain analysis's signature | retain analysis soundness | **MOVED** to `Retain_Analysis.thy` (was `TD_Side_Eff_Cmp_Gen`); the generic domination helpers stayed |
| `retain_edge_tree_st` + commutation lemmas | executable mirror, `fun_of_st`-simulated | retain analysis, executable layer | **MOVED** to `Retain_Analysis.thy` (was `Exec_Bridge`) |
| `sign_etf_retain` + `framed_le` instance (`Sign_Side_Soundness.thy`) | Sign instantiation of the retain factory | analysis instance | KEEP (now imports `Retain_Analysis`) |
| `split_retain_*`, `split_clean_*`, `split_local_*`, `split_mixed_*`, `split_combine_tree_ctx`, `split_make_side_rhs_tree_eff`, `merge_combine_split` (Stage-1C block of `Split_Cmp_Gen.thy`) | zero consumers outside the theory | historical migration scaffolding | **DELETED** (the 1B layer -- `split_edge_tree`, `split_etf_of_transfer`, split seed generator, `spec_generator_split` -- stays: `Sign_Call_Spec` consumes it) |
| `clean_edge_tree`, `clean_etf_of_transfer` (`Clean_RRead_Sound.thy`) | same Answer-keeps-result pattern as retain | clean analysis (same correction applies) | remaining blocker: follows the retain path in a later slice |
| Keyed retain examples (`Exec_Sign_Cmp_Keyed_Retain_*`, `Exec_Sign_Cmp_RRead_Split`, `Exec_Sign_Cmp_Keyed_Gen_Run`) | consumers exhibiting the precision gain | analysis usage | unchanged -- they resolve the moved constants transitively via `Sign_Exec_Sound` -> `Sign_Side_Soundness` -> `Retain_Analysis` |

No component is kept for historical reasons: everything whose *statement*
mentions retain lives in `Retain_Analysis.thy`; the framework keeps only
value-opaque trees, slot invariants, and analysis-agnostic contracts.

### 6.4 Replacement design (implemented: `DG_Framework.thy` + `Retain_Analysis.thy`)

Domain. `datatype ('l, 'g) dg_state = DG (locals: 'l) (globs: 'g)` with the
componentwise `bounded_semilattice_sup_bot` instance. A copy type is
*required*, not stylistic: `CFG_Def` imports `HOL-Library.Product_Lexorder`,
so raw pairs carry the lexicographic order repo-wide and the componentwise
`Product_Order` instances raise an arity conflict (observed:
`prod :: (inf, inf) inf` vs `prod :: (linorder, linorder) inf`). The retain
analysis's local domain is `D = ('a abs_state, 'a abs_state) dg_state`:
locals in `locals`, the flow-sensitive global snapshot in `globs`.
Conversions `pair_of_dg` / `dg_of_pair` connect to the Stage-1A
`split_state` pair, `merge_dg` / `split_dg` to the homogeneous state
(`merge_split_dg`), `wf_dg` to `wf_split`.

Transfer. `retain_dg_step f d g = (let res = f (merge_dg d ⊔ globs g) in
(emb_glob (restrict_global res), split_dg res))`: read own `D` (which contains
the snapshot) joined with the global slot, run the base transfer, keep the new
snapshot in the Answer. The snapshot is written by the analysis's own step --
the framework tree (`step_edge_tree`) forwards values it never inspects.

Publication. `Side` carries `emb_glob (restrict_global res)` -- a pure-`G`
value (local part `bot`). `retain_dg_sides_locals_bot` proves the analysis
never publishes locals; `retain_dg_traverse_wf` proves every Answer is
well-split. Both hold for arbitrary assignments, not just represented ones.

Soundness responsibilities. The framework keeps: slot typing (`Inl` = `D`,
`Inr` = `G`) and the generic collecting spine. The analysis owes: (a) its
transfer soundness (today: `sound_effectful_transfer` for
`retain_etf_of_transfer`, discharged from the base transfer), (b) the snapshot
bound "`globs` of my `D` sits below the published globals" (today:
`inl_glob_le_glob_env`, derived from exactness in `TD_Side_Eff_Cmp_Gen`), and
(c) the framed enter bound under that snapshot invariant (today:
`sound_effectful_transfer_framed_le`).

Equivalence to current behaviour (proved, first-pass):

| Theorem | Statement |
| --- | --- |
| `step_edge_tree_unit` / `step_edge_tree_retain` | the framework tree with the unit/retain step *is* `unit_edge_tree` / `retain_edge_tree` (definitional) |
| `retain_dg_traverse` (+ `_merge`) | pair-domain evaluation = `split_dg` of the homogeneous retain evaluation; `merge_dg` recovers it exactly |
| `retain_dg_sides_Inr` (+ `_globs`) | pair-domain global publication = embedded homogeneous retain publication |
| `retain_dg_traverse_wf`, `retain_dg_sides_locals_bot` | slot discipline for every assignment |

Identical semantics, identical (executable-layer untouched) behaviour,
identical soundness: nothing existing was modified, weakened, or deleted.

### 6.5 Migration sequence

1. **(done)** First step: framework `step_edge_tree`; unit/retain as steps
   with definitional equalities; `dg_state` copy lattice; the pair-domain
   retain analysis with traverse/sides equivalence to `retain_edge_tree`
   under the Stage-1A isomorphism.
2. **(done)** Retain extraction: `retain_edge_tree` + lemma set + factory +
   soundness moved from `TD_Side_CFG` to `Retain_Analysis.thy`;
   the exact-solution reduction moved from `TD_Side_Eff_Cmp_Gen`;
   `retain_edge_tree_st` moved from `Exec_Bridge`. Audit correction:
   `inl_glob_le_glob_env` / `sound_effectful_transfer_framed_le` stay in the
   framework -- they are analysis-agnostic contracts also discharged by the
   unit transfer (`sign_sound_etf_unit_framed_le`); only their prose was
   de-retained. Stage-1C `split_*` scaffolding deleted (no consumers).
3. **(done)** Framework split: `DG_Framework.thy` carries the framework half
   (homogeneous `step_edge_tree`, the `dg_state` lattice, the heterogeneous
   `dg_edge_tree` / `dg_combine_tree` / `dg_spec` interface, unit
   compatibility); `Retain_Analysis.thy` imports it and is pure analysis.
4. **(done)** Stage 1D typing: `side_rhs_fold_dg` and
   `side_cfg_T_eff_cmp_seed_dg` let `dg_spec` analyses drive the complete CMP
   equation generator. Homogeneous generator equality and post-fixpoint
   equivalence recover the old pipeline; Retain has its own representation
   transport and requires no framework hook.
5. Clean analysis: `clean_edge_tree` follows the retain path (its own theory,
   its own `D`). Executable layer: `dg_state` over `'a st`; retarget the keyed
   retain examples to the analysis's executable form.

State after step 4: the generic retain tree is gone from the framework,
Retain drives the complete equation generator through the standard
`Answer : D` / `Side : G` interface, and no framework code depends on "local
state contains globals". The homogeneous pipeline remains as a proved
compatibility and soundness layer.

### 6.6 The heterogeneous framework (`DG_Framework.thy`)

The framework is now parameterized by two independent, fully opaque analysis
domains, packed into the solver's single value type by slot:

```
FRAMEWORK (DG_Framework.thy -- no analysis knowledge)
  dg_state             componentwise copy lattice ('l, 'g) with
                       bounded_semilattice_sup_bot (raw pairs blocked by
                       Product_Lexorder, see 6.4)
  dg_edge_tree step u  QueryL; QueryG; Side (DG bot (fst r)); Answer (DG (snd r) bot)
                       where r = step (locals d) (globs g)
                       step : D => G => G x D   <-- the analysis boundary
  dg_combine_tree comb the two-D procedure-return shape
  dg_spec              Goblint-Spec-shaped record: one D => G => G x D step
                       per edge action + the combine; apply_dg_spec
  boundary theorems    dg_edge_tree_answer_pure_D, dg_edge_tree_side_pure_G:
                       for EVERY step and assignment, Answers carry no G and
                       Sides carry no D

ANALYSES
  unit   (DG_Framework compat layer)   D = G = 'a abs_state
         unit_dg_spec tf; traverse/sides equal the legacy homogeneous trees
         under dg_rep_flat (unit_dg_spec_traverse/_sides/_combine_*)
  retain (Retain_Analysis.thy)         D = locals x snapshot, G = 'a abs_state
         retain_hetero_step; retain_hetero_traverse/_sides prove behaviour
         identical to the legacy retain_edge_tree under retain_hetero_rep
```

Retain validation (the expressiveness witness): `retain_hetero_step` runs on
the same analysis-agnostic `dg_edge_tree` as every other analysis --
`DG_Framework.thy` contains no retain knowledge -- and reproduces the legacy
homogeneous retain semantics exactly. The snapshot lives inside the retain
analysis's `D`; the framework never copies `G` into it.

#### Proof audit (what replaced what)

| Deleted / moved | Replacement | Obligations moved to the analysis? |
| --- | --- | --- |
| `TD_Side_CFG`'s retain subsection | same lemmas, verbatim, in `Retain_Analysis.thy` | yes -- they *are* the analysis now; no proof got longer |
| `TD_Side_Eff_Cmp_Gen`'s exact-solution reduction | same theorems in `Retain_Analysis.thy`; the framework keeps the generic domination helpers they build on | yes -- deriving `inl_glob_le_keyed_ctx` from exactness is the retain analysis's job; other analyses use `inl_slot_globals_bot_ctx_le_keyed` |
| `Exec_Bridge`'s retain_st subsection | same lemmas in `Retain_Analysis.thy` | yes |
| Stage-1C `split_*` block (~200 lines, `Split_Cmp_Gen`) | superseded by `dg_edge_tree`/`dg_spec` + the 6.4 equivalence theorems; no replacement lemma needed (zero consumers) | n/a |
| `unit_edge_tree` as primitive | unchanged, but now provably `step_edge_tree (unit_step f)` and reproduced on the hetero framework by `unit_dg_spec` | the unit steps are the base analysis's transfer |

No proof was weakened; every moved lemma kept its statement and its proof
text. The framework shrank by the retain subsections plus ~200 lines of
scaffolding; `Retain_Analysis.thy` grew by exactly the moved material plus the
hetero validation.

#### "Would Goblint's framework contain this?" (remaining framework audit)

| Remaining framework component | Goblint analogue / justification |
| --- | --- |
| `dg_edge_tree`, `dg_combine_tree`, `dg_spec` | yes: `constraints.ml`'s transfer-function-to-constraint-system plumbing over opaque `D`/`G` |
| `step_edge_tree`, `unit_edge_tree`, `unit_combine_tree`, homogeneous generators | transitional: Goblint has no homogeneous layer, but the mechanized soundness spine is stated over it; retired only when Stage-1D re-types the generator (step 4) |
| `inl_slot_globals_bot`, `inr_slot_locals_bot`, `inl_glob_le_keyed_ctx` | slot-typing invariants of the single-value-type encoding; Goblint has real two-typed unknowns and needs none -- the formalization requires them until (and after, as wf-invariants) `'d := dg_state` |
| `sound_effectful_transfer(_framed, _framed_le)` | the mechanized counterpart of `Spec`'s implicit soundness obligations; Goblint states none (unverified), a verified framework must; `_le` is the weakest (analysis-agnostic) form |
| `restrict_local` / `restrict_global` | the homogeneous encoding of slot projection; dissolves into `locals`/`globs` at Stage 1D |
| `clean_edge_tree` (`Clean_RRead_Sound`) | no -- clean is an analysis; remaining blocker, follows the retain path |

#### Remaining homogeneous components (classification)

Everything in the framework that still assumes one lattice, `'a abs_state`,
`gamma_state`, `combine_abs`, or exists only as migration transport. None
blocks the heterogeneous pipeline; the classification drives Stage 2 (§7).

| Component | Where | Classification | Justification |
| --- | --- | --- | --- |
| `dg_state` slot packing (one solver value type) | `DG_Framework` | KEEP | the vendored TD solver has a single value lattice; `dg_edge_tree_answer_pure_D` / `dg_edge_tree_side_pure_G` prove the packing is invisible to analyses |
| slot-typing invariants (`inl_slot_globals_bot`, `inr_slot_locals_bot`, keyed variants) | `Constraint_System`, cmp layers | KEEP | wf-facts of the single-value-type encoding; Goblint's two-typed unknowns need none, a packed encoding does |
| `sound_effectful_transfer(_framed, _framed_le)` | `Constraint_System` | KEEP (until §7 GENERALIZE lands) | the analysis-agnostic soundness contract of the homogeneous API; the whole existing endpoint tower is stated over it |
| `sound_transfer` + `gamma_state`-typed collecting lemmas (`post_fixpoint_sound_at`) | `Constraint_System(_Sound)` | GENERALIZE | Stage 2 hoists the mixed analysis's two-invocation pattern into a `(D, G, gammaD, gammaG)` locale; the homogeneous lemmas become its `D = G` instance |
| `effectful_domain_transfer`, `edge_tf_tree`, homogeneous generators (`side_cfg_T_eff_cmp`, `side_cfg_T_eff_cmp_seed`, `spec_generator`) | `Constraint_System`, `TD_Side_Eff_Cmp_Gen`, `Exec_Cmp_Bridge`, `Call_Spec_Generator` | DEFER | the proven soundness spine and every instance ride on them; retire only after Stage 2 re-derives the endpoints as specializations |
| `restrict_local` / `restrict_global` | `TD_Side_CFG` + homogeneous analyses | KEEP | the *unit analysis's* definition of its store split; analysis-layer semantics, no longer framework plumbing (`locals`/`globs` are) |
| `combine_abs` | homogeneous analyses, `dgs_combine` fields | KEEP | an analysis's combine choice, not a framework assumption; the mixed analysis picks its own combine per domain |
| `unit_edge_tree`, `unit_combine_tree`, `unit_etf_of_transfer`, `step_edge_tree` | `TD_Side_CFG`, `DG_Framework` | DEFER | the base analysis's homogeneous trees; consumed by the existing spine and by `Retain_Analysis`; fold onto `unit_dg_spec` when Stage 2 flips primary/derived |
| unit transport (`dg_env`, `dg_rep_flat`, `pack_dg_tree` + traverse/sides/dep lemmas, `part_post_solution_pack_dg_iff`, `side_cfg_T_eff_cmp_seed_dg_unit`) | `DG_Framework` | REMOVE (after §7) | pure compatibility bridge; once the homogeneous endpoints are `D = G` specializations of the native locale, the bridge carries nothing |
| retain transport (`retain_hetero_rep`, `retain_dg_*_rep*`, `part_post_solution_retain_dg_iff`) | `Retain_Analysis` | REMOVE (after §7) | validation-era equivalence; a native retain soundness proof replaces the detour through the homogeneous endpoint |
| Stage-1B split layer (`Split_Cmp_Gen`: `split_etf_of_transfer`, `side_cfg_T_eff_cmp_split_seed`, `spec_generator_split`) + `Sign_Call_Spec` Stage-1B subsection | `Split_Cmp_Gen`, `Sign_Call_Spec` | REMOVE (after §7) | superseded scaffolding; sole remaining consumer is its own sign witness; `DG_Framework` imports it only as a conduit to `Call_Spec_Generator`/`Split_State` |
| `clean_edge_tree` + `clean_etf_of_transfer` | `Clean_RRead_Sound` | DEFER | clean is an analysis (same finding as retain); extraction follows the retain path, independent of Stage 2 |
| homogeneous executable examples (`Exec_*` runs, keyed retain examples) | `Formalization/Examples` | KEEP | they demonstrate the homogeneous instances, which remain first-class `D = G` analyses |

#### Post-cleanup dependency graph

```
Constraint_System (framework: slot invariants, sound_effectful_transfer*,
 |                 incl. the analysis-agnostic framed_le contract)
 +-- TD_Side_CFG (framework: restricts, unit/local/mixed trees + factories)
      +-- ... cmp/ctx/digest layers, Call_Spec* (framework, retain-free)
      |    +-- TD_Side_Eff_Cmp_Gen (framework: keyed generator, _le endpoints,
      |    |                        generic domination helpers)
      |    +-- Exec_Bridge (framework exec: unit/clean _st trees, transports)
      +-- Split_Cmp_Gen (Stage-1B split layer; consumer: Sign_Call_Spec)
           +-- DG_Framework (framework core: dg_state, step/dg trees, dg_spec,
                |            unit compatibility)
                +-- Retain_Analysis (ANALYSIS: retain tree + factory +
                     |               soundness + exactness reduction +
                     |               executable mirror + hetero validation)
                     +-- Sign_Side_Soundness (instances: sign unit/retain)
                          +-- Sign_Exec_Sound -> keyed retain examples
```

## 7. Stage 2: native heterogeneous soundness

Stage 2 makes `DG_Soundness.thy` the primary proof layer. It extracts a
heterogeneous post-fixpoint directly from `part_post_solution`, then proves
collecting soundness against the analysis's joint concretization. The mixed
analysis no longer invokes a homogeneous theorem or a packing equivalence.

### 7.1 Primary semantics

The locale takes the joint concretization as an analysis parameter:

```
gammaDG : D => G => store set
```

This parameter is necessary. Independent analyses use
`gamma_dg d g = gamma_state d Int gamma_state g`. The homogeneous unit step
first joins its slots and therefore uses
`gamma_unit d g = gamma_state (d sup g)`. Replacing `gamma_state` mechanically
with an intersection would make restricted unit states denote the empty set.
The locale remains unaware of either choice.

### 7.2 The native locale

The locale is parameterized only by the analysis interface and its semantic
reading:

```
locale sound_dg_spec =
  fixes S       :: "(D, G) dg_spec"
    and gammaDG :: "D => G => store set"
  assumes gammaDG_mono
      and step_sound
      and combine_sound
```

Generic theorems inside the locale, all following the existing mixed proof
line by line with `dg_spec_step` in place of the concrete transfers:

1. `dg_post_solution_postfix` — `part_post_solution` of
   `side_cfg_T_eff_cmp_seed_dg` + coverage of entry / edge targets / combine
   targets implies the edge-wise postfix facts for `D` and the
   publication-closure facts for `G` (generalizes
   `mixed_si_post_solution_postfix`).
2. `dg_postfix_collect_sound` — the postfix facts imply
   `cfg_collect g S0 v <= dg_gamma sigma v`. The proof uses the generic
   semantic post-fixpoint lemma `cfg_collect_semantic_postfix`; it does not
   reduce either slot to a homogeneous equation system.

The concrete mixed dependency chain is now:

```
mixed_si_post_solution_collect_sound
 +-- mixed_si_post_solution_postfix
 |    +-- sound_dg_spec.dg_post_solution_postfix
 |         +-- part_post_solution_imp_se_constraint_holds
 +-- mixed_si_postfix_collect_sound
      +-- sound_dg_spec.dg_postfix_collect_sound
           +-- cfg_collect_semantic_postfix
                +-- cfg_collect_post_fixpoint_sound
```

Proof architecture before Stage 2:

```
heterogeneous analysis
  -> representation compatibility
  -> homogeneous post-fixpoint soundness
  -> collecting soundness
```

Proof architecture after Stage 2:

```
dg_spec + gammaDG
  -> sound_dg_spec
       +-> mixed analyses
       +-> unit_dg_spec (D = G) through sound_transfer
  -> collecting soundness
```

No `dg_env`, `pack_dg_tree`, `part_post_solution_dg_unit_iff`, or
`sound_transfer.post_fixpoint_sound_at` theorem occurs in this chain.

### 7.3 What disappears, what specializes

Compatibility lemmas are retained until their complete dependency cones are
empty. Consumer counts below exclude each declaration and were measured over
`src/**/*.thy` after the native mixed endpoint landed.

| Lemma | Reason | Consumers | Delete now? | Delete later? |
| --- | --- | ---: | --- | --- |
| `unit_dg_spec_traverse`, `unit_dg_spec_sides`, `unit_dg_spec_combine_traverse`, `unit_dg_spec_combine_sides` | tree-denotation witnesses from Stage 1D | 0 each | no; keep the compatibility API together | yes, with the unit transport block |
| `dg_env_Inl`, `dg_env_Inr`, `DG_local_le_iff`, `dg_env_le_iff` | packing support | 0 each | no; definitions remain live internally | yes |
| `pack_dg_tree_seqcomp` | packing proof support | 1 | no | after its caller is removed |
| `pack_dg_tree_map_ltree`, `pack_dg_tree_map_gtree` | packing proof support | 2 each | no | after their callers are removed |
| `pack_dg_tree_fold` | generator equality proof | 1 | no | yes |
| `traverse_rhs_pack_dg_tree`, `sides_of_rhs_pack_dg_tree`, `dep_aux_pack_dg_tree` | solution transport | 2 each | no | yes |
| `locals_sides_of_rhs_pack_dg_tree`, `globs_sides_of_rhs_pack_dg_tree` | projection witnesses | 0 each | no; same-block cleanup | yes |
| `part_post_solution_pack_dg_iff` | post-solution transport | 2 | no | yes |
| `part_solution_pack_dg_iff` | exact-solution transport | 0 | no; same-block cleanup | yes |
| `apply_unit_dg_spec_pack`, `combine_unit_dg_spec_pack` | generator equality support | 1 each | no | yes |
| `map_pack_dg_tree_routed`, `map_pack_dg_tree_combine` | generator equality support | 1 each | no | yes |
| `side_cfg_T_eff_cmp_seed_dg_unit` | homogeneous generator equality | 2 | no | yes |
| `part_post_solution_dg_unit_iff` | public transport endpoint | 0 | no; preserve Stage 1D compatibility until block removal | yes |
| `retain_hetero_rep` | Retain representation bridge | 44 | no | after a native Retain interpretation |
| `retain_dg_generator` | Retain compatibility generator | 10 | no | after a native Retain interpretation |
| `part_post_solution_retain_dg_iff` | Retain solver transport | 1 | no | after a native Retain interpretation |
| `sign_retain_dg_post_fixpoint_iff` | Retain validation endpoint | 0 | no; its supporting cone remains live | after native Retain soundness |

The following groups therefore remain scheduled for coherent cleanup:

* unit transport: `dg_env`, `dg_rep_flat`, `pack_dg_tree` and its
  traverse/sides/dep lemmas, `part_post_solution_pack_dg_iff`,
  `part_solution_pack_dg_iff`, `side_cfg_T_eff_cmp_seed_dg_unit`,
  `unit_dg_spec_traverse/_sides/_combine_*`;
* retain transport: `retain_hetero_rep`, `retain_dg_generator` rep-equality
  chain, `part_post_solution_retain_dg_iff`,
  `sign_retain_dg_post_fixpoint_iff` (its *statement* is subsumed by the
  native retain interpretation);
* the Stage-1B layer: `Split_Cmp_Gen.thy` and the `Sign_Call_Spec` Stage-1B
  subsection (`DG_Framework` then imports `Call_Spec_Generator` directly).

Existing proofs that are now specializations (statements preserved):

* `mixed_si_post_solution_postfix` / `mixed_si_postfix_collect_sound` — an
  interpretation of `sound_dg_spec` at `mixed_si_spec`, `gammaD` the sign
  `gamma_state`, `gammaG` the interval `gamma_state` (the two concrete
  transfer-soundness facts discharge the locale assumptions);
* every `sound_transfer` instance, including Sign and Interval, is a sublocale
  at `unit_dg_spec tf` with `gamma_unit d g = gamma_state (d sup g)`;

Retain is the next planned specialization: `D` carries locals plus the
snapshot, and its joint concretization reads the merged state. Its transport
chain remains live until those analysis-specific semantic obligations are
discharged.

What stays untouched: the vendored solver and its `part_post_solution`
contract, `dg_state` packing + slot-purity boundary theorems,
`side_rhs_fold_dg` and the generic fold/traverse/sides lemmas, every
per-domain transfer-soundness fact (`sign_is_sound_transfer`,
`ivl_is_sound_transfer`, ...) — they become the locale-premise suppliers.

### 7.4 Progress and remaining work

1. **Done:** add `gammaDG`, `sound_dg_spec`, native post-fixpoint extraction,
   and native collecting soundness.
2. **Done:** reprove `Mixed_Sign_Interval` as a direct interpretation and
   preserve its public theorem statements.
3. **Done:** recover the homogeneous unit framework as the `sound_transfer`
   sublocale. Sign and Interval inherit this interpretation.
4. **Remaining:** native Retain interpretation; delete the retain transport
   chain. Gate:
   `Retain_Analysis` shrinks, no consumer breaks.
5. **Remaining:** delete the unit transport block in `DG_Framework` and the
   Stage-1B layer as one dependency-cone cleanup.
   Gate: full-DAG green build; the §6.6 classification table's REMOVE rows
   are empty.

Context-indexed and digest-refined `G` (the cmp/ctx/digest tower) is *not*
re-proved in Stage 2; it keeps riding the homogeneous API until the clean
analysis extraction (DEFER rows) migrates it.
