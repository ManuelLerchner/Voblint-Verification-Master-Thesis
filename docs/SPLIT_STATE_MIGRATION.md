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

**Architectural correction (post-1C, implemented first step):** comparing
against Goblint's `analyses.ml` showed the generic retain tree sits at the
wrong abstraction level -- retain is an *analysis* (its `D` = locals x global
snapshot), not a framework execution strategy. Section 6 has the corrected
framework/analysis boundary, the component classification, the replacement
design, and the migration sequence; the first implementation step is
`src/Analysis/Generic/Solver/Context/Retain_Analysis.thy`.

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

#### Stage 1D readiness report

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

What remains before `locals : 'l, globals : 'g`:

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

### 6.3 Component classification (evidence-based)

| Component | Evidence | Layer | Verdict |
| --- | --- | --- | --- |
| `unit_edge_tree`, `unit_combine_tree` (`TD_Side_CFG.thy:150,163`) | pure `Answer(restrict_local)` / `Side(restrict_global)` transport | framework (its `restrict_*` calls become the unit *analysis step* once `D`/`G` split; `step_edge_tree_unit` already factors them out) | KEEP |
| `step_edge_tree`, `unit_step`, `retain_step` (`Retain_Analysis.thy`) | value-opaque tree + the two steps; `step_edge_tree_unit` / `step_edge_tree_retain` are definitional | framework core + analysis steps | KEEP (new) |
| `retain_edge_tree` + traverse/sides/etf_full lemmas (`TD_Side_CFG.thy:201-245,444`) | differs from unit only in the Answer payload (`sides_retain_eq_unit`, `etf_full_retain_eq_unit_edge_tree`); the payload is analysis behaviour | retain analysis, currently in a framework file | REWRITE to a compatibility wrapper over `retain_step` / the retain analysis; then MOVE the retain-specific lemmas next to the analysis; DELETE once no caller remains |
| `retain_etf_of_transfer` + soundness (`TD_Side_CFG.thy:590-644,877-928`) | factory instantiating every edge with `retain_edge_tree` | retain analysis implementation | MOVE (to the retain analysis theory) |
| `inl_glob_le_glob_env` (`Constraint_System.thy:738`) | "a local unknown may carry globals, bounded by `glob_env`" -- a property of snapshot-carrying `D`s | retain analysis soundness obligation stated framework-wide | REWRITE: becomes the retain analysis's invariant on its own `D`; the framework keeps only `inl_slot_globals_bot` (= `wf_split` halves) |
| `sound_effectful_transfer_framed_le` (`Constraint_System.thy:792`) | enter bound under the weaker retain premise; `framed_le_imp_framed` recovers the strict contract | retain analysis soundness | MOVE with the analysis; the framework contract stays `sound_effectful_transfer_framed` |
| retain keyed invariant + exact-solution reduction (`TD_Side_Eff_Cmp_Gen.thy:314-658`), retain combine/collect endpoints (`:943,1036`) | soundness theorems for solutions whose local slots carry globals | retain analysis soundness theory | MOVE (they are parametric in the transfer only through `apply_etf etf a u = retain_edge_tree (F a) u` -- exactly the analysis's signature) |
| `retain_edge_tree_st` (`Exec_Bridge.thy:212-278`) | executable mirror of the retain tree, `fun_of_st`-simulated | retain analysis, executable layer | MOVE with the analysis |
| `sign_etf_retain` + `framed_le` instance (`Sign_Side_Soundness.thy:69-93,192-221`) | Sign instantiation of the retain factory | analysis instance (already analysis-layer) | KEEP (retarget imports when the factory moves) |
| `split_retain_edge_tree`, `split_clean_edge_tree`, split factories (`Split_Cmp_Gen.thy:190-295`) | 1B/1C bridges, each `= original` | historical migration scaffolding | DELETE after the retain analysis replaces its callers (they were stepping stones to `Retain_Analysis.thy`) |
| `clean_edge_tree`, `clean_etf_of_transfer` (`Clean_RRead_Sound.thy`) | same Answer-keeps-result pattern as retain (reads only the local slot) | clean analysis (same correction applies) | REWRITE/MOVE along the same sequence as retain |
| Keyed retain examples (`Exec_Sign_Cmp_Keyed_Retain_*`, `Exec_Sign_Cmp_RRead_Split`, `Exec_Sign_Cmp_Keyed_Gen_Run`) | consumers exhibiting the precision gain | analysis usage | KEEP (retarget to the retain analysis when its executable layer lands) |

No component is retained for historical reasons: everything retain-specific is
scheduled to the analysis layer; the only framework survivors are the
value-opaque tree shape and the slot invariants.

### 6.4 Replacement design (implemented first step: `Retain_Analysis.thy`)

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

1. **(done)** `Retain_Analysis.thy`: framework `step_edge_tree`; unit/retain
   as steps with definitional equalities; `dg_state` copy lattice; the
   pair-domain retain analysis with traverse/sides equivalence to
   `retain_edge_tree` under the Stage-1A isomorphism.
2. Redefine `retain_edge_tree` as the wrapper
   `step_edge_tree (retain_step f)` (definitional, `step_edge_tree_retain`
   makes it a one-line change) and move the retain factory + its soundness
   lemmas into the analysis theory. Same for `clean_edge_tree`.
3. Move `inl_glob_le_glob_env` + `sound_effectful_transfer_framed_le` + the
   keyed retain invariant block (`TD_Side_Eff_Cmp_Gen.thy:314-658`) into the
   retain analysis theory; the framework keeps `inl_slot_globals_bot` and
   `sound_effectful_transfer_framed` only.
4. Stage 1D typing: `'d := dg_state` at the `eqsT` level; unit/local/mixed
   analyses use a locals-only `D`, the retain/clean analyses use the
   snapshot-carrying `D` from step 1; the 1B/1C `split_*` scaffolding in
   `Split_Cmp_Gen.thy` is deleted as its callers retarget.
5. Executable layer: `dg_state` over `'a st`, retarget the keyed retain
   examples; delete `retain_edge_tree_st` from `Exec_Bridge`.

End state: generic retain tree gone (or reduced to the step-2 wrapper during
the transition), retain implemented through the standard `Answer : D` /
`Side : G` interface, and no framework code depending on "local state contains
globals".
