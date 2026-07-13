# Stage 1: split local/global state representation

Goal: independent local and global abstract domains (`'l` for locals, `'g` for
globals), Goblint-style. Stage 1 is a representation refactoring in four
phases; only Stage 1A is implemented. No semantic change, no new analyses, no
generator or context redesign. All existing theorem statements are preserved;
the split representation exists alongside the homogeneous one and is proven
isomorphic to it.

Status: **Stages 1A, 1B and 1C implemented**. 1A:
`src/Analysis/Generic/Domain/Split_State.thy` plus a bridge subsection in
`src/Analysis/Generic/Solver/Core/TD_Side_CFG.thy`. 1B:
`src/Analysis/Generic/Solver/Context/Split_Cmp_Gen.thy` (split-shaped trees,
transfer factory and CMP generator, each proven equal to its homogeneous
original) plus the sign instantiation in
`src/Analysis/Instances/Sign/Sign_Call_Spec.thy`. 1C: the remaining generic
tree constructors and factories, in the same theory (see the Stage 1C section
below for the constructor audit, the retain finding, the executable-mirror
audit and the Stage 1D readiness report). Stage 1D is design only.

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
* The genuine Stage 1D consequence: for retain-style (and clean-style)
  transfers the local unknown's value type must be the **full pair**
  `('l, 'g) split_state` -- Goblint's `D` carrying a global copy -- whereas
  unit/local/mixed transfers only ever put the local component in the Answer.
  This is a typing decision, not a semantic blocker.

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

#### Stage 1D readiness report

| Component | Readiness for independent `('l, 'g)` |
| --- | --- |
| vendor solver, `strategy_tree`, `seqcomp_tree`, `map_ltree`/`map_gtree`, `side_rhs_fold*` | **ready** (polymorphic in the payload) |
| split trees / factories / generators (1B+1C artefacts) | **blocked only by type changes**: `Side` payloads become `'g abs_state` (`snd`), `Answer` payloads `'l abs_state` (unit/local/mixed) or the pair (retain/clean) |
| solver unknown-value type | **blocked only by a type decision**: the vendor `eqsT` has a single value type `'d`, so `Inl`/`Inr` slots cannot be typed differently; Stage 1D sets `'d := ('l, 'g) split_state` with `wf_split`-style slot invariants (the existing `inr_slot_locals_bot` / `inl_slot_globals_bot` are exactly the two halves of `wf_split`). No solver modification needed. |
| soundness statements | **blocked only by type changes**: `gamma_state` -> `gamma_split` (Stage 1A already provides it, heterogeneous, with `gamma_split_merge` recovering today's statements at `'l = 'g`) |
| transfer records (`domain_transfer`, `effectful_domain_transfer`) | **blocked only by type changes**: fields over the pair; enter/combine get genuinely split types mirroring `enter_state` / `<s\|t>` |
| executable layer | **blocked only by type changes**: `('l st * 'g st)` pair, components already exist |
| retain/clean transfers | **resolved** (see the retain finding): need pair-valued local unknowns; not a semantic blocker |
| **semantic blockers** | **none identified at the tree level.** The single constraint of substance is the vendor solver's one-value-type interface, and it is absorbed by `'d := ('l, 'g) split_state` without touching the solver. |

What remains before `locals : 'l, globals : 'g`:

```
'd := ('l,'g) split_state at the eqsT level
  |
  +-- trees: Side snd-typed, Answer fst-typed (pair for retain/clean)
  |     [1B/1C split versions are the templates; drop merge_state at the
  |      boundary instead of reassembling]
  +-- transfer records over the pair; enter/combine split-typed
  +-- side_env / glob_env readings via gamma_split
  |     (slot invariants = wf_split halves, already stated)
  +-- soundness endpoints restated with gamma_split
  |     (homogeneous case recovered via gamma_split_merge)
  +-- exec mirror at ('l st * 'g st)
```

### Stage 1D -- allow `'l ~= 'g`

* Soundness statements switch from `gamma_state` to `gamma_split` (the
  homogeneous case remains available through `gamma_split_merge`).
* `enter` / `combine` transfers get genuinely split types
  (`combine: 'l abs_state => 'g abs_state => ...`), mirroring the store-level
  `<s|t>` / `enter_state` split of `IMP2_Globals`.
* The global unknown slots (`Inr` keys) change value type to `'g abs_state`;
  the local slots to `'l abs_state`. The unknown space `pp + 'g` already keeps
  them apart, so only `side_env`-style joins need the split reading
  (`merge_state`-free, via `gamma_split`).
* Only here do existing theorem *statements* change; 1A-1C keep them intact.

## 5. Verification

Stage 1A gate: `Split_State.thy` and `TD_Side_CFG.thy` error-free in I/Q,
`isabelle build ... Voblint_Analysis` green, `rg -n '^\s*sorry' src/Analysis`
empty. The `Voblint_Formalization` session is gated separately (an unrelated
in-progress prototype theory currently breaks it); no Formalization theory is
touched by Stage 1A.
