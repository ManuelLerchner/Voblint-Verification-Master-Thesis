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
The executable layer is outside this abstract-pipeline gate.

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

#### Remaining legacy homogeneous components

These components remain intentionally; none blocks the abstract heterogeneous
pipeline:

1. `effectful_domain_transfer`, `edge_tf_tree`, `unit_edge_tree`,
   `unit_combine_tree`, and `side_cfg_T_eff_cmp_seed` provide the existing
   homogeneous API, executable transports, and compatibility target.
2. The collecting-soundness locales remain stated over that API. The
   heterogeneous homogeneous instance reaches them through proved equation
   and post-fixpoint equality, preserving the endpoint statements.
3. `restrict_local` / `restrict_global` remain in homogeneous analyses and in
   the compatibility definitions. Heterogeneous framework plumbing uses
   `locals` / `globs` projections instead.
4. **Clean analysis extraction** (step 5): `clean_edge_tree` +
   `clean_etf_of_transfer` still sit in `Clean_RRead_Sound` with the seeded
   spine built on them. This is a later analysis migration, not Stage 1D.
5. **Executable dg layer**: `dg_state` over `'a st` and example retargeting.
   The current deliverable covers the abstract `Voblint_Analysis` pipeline.

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
