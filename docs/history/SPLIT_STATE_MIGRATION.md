# Heterogeneous D/G architecture

Status: **migration complete**.

The abstract pipeline supports independent analysis domains:

```text
Answer : D
Side   : G
step   : D => G => G x D
```

`DG_Framework.thy` carries these values through strategy trees and the seeded
CMP generator. `DG_Soundness.thy` is the canonical soundness layer. The mixed
Sign/Interval analysis reaches collecting soundness without a homogeneous
equation system or representation transport.

This document records the historical architecture, the completed migration,
the final dependency graph, the compatibility audit, and the remaining gaps
to a more Goblint-like framework.

## Historical architecture

The original pipeline used one abstract-state type everywhere:

```text
'a abs_state
  |
  +-- local Answer values
  +-- global Side values
  +-- effectful_domain_transfer
  +-- strategy_tree payload
  +-- side_cfg_T_eff_cmp_seed
  +-- homogeneous soundness locales
```

Local and global slots were distinguished by unknown keys and by
`restrict_local` / `restrict_global`. Their values still shared one lattice.
An analysis needing different meanings had to embed both into a product, sum,
or common over-approximation.

The proof direction during migration was:

```text
heterogeneous candidate
  -> packing/equality compatibility
  -> homogeneous post-fixpoint theorem
  -> collecting soundness
```

## Completed migration

### Stage 0: call specification

`Call_Spec.thy`, `Call_Spec_Generator.thy`, and `Call_Spec_Sound.thy` introduced
the Goblint-inspired call/routing contract and a post-fixpoint soundness
endpoint for the configured generator.

### Stage 1A: split representation

`Split_State.thy` introduced the local/global pair representation, its
well-formedness predicate, split/merge conversions, order transport, and joint
concretization. The isomorphism remains useful to Retain's product-shaped local
domain and to the packed solver carrier.

### Stages 1B and 1C: equality scaffolding

`Split_Cmp_Gen.thy` expressed homogeneous trees and generators through split
states and proved equality with the existing pipeline. It established the
migration boundary but did not provide independent types.

This layer had no consumers after Stage 2. It and its Sign witnesses have been
deleted.

### Stage 1D: independent domains

`DG_Framework.thy` introduced:

- `dg_state`, the componentwise `D x G` carrier required by the vendor solver's
  single value parameter;
- `dg_edge_tree` and `dg_combine_tree`;
- `dg_spec`, the ordinary analysis interface;
- `side_rhs_fold_dg` and `side_cfg_T_eff_cmp_seed_dg`;
- `unit_dg_spec`, the homogeneous `D = G` analysis.

`Retain_Analysis.thy` instantiates the same framework with a product-shaped
local domain containing a flow-sensitive snapshot. The framework contains no
Retain-specific operation.

`Mixed_Sign_Interval.thy` supplies the first genuinely mixed instance:

```text
D = Sign abstract state
G = Interval abstract state
```

### Stage 2: native heterogeneous soundness

`DG_Soundness.thy` introduced `sound_dg_spec`. An analysis supplies:

```text
S       : (D, G) dg_spec
gammaDG : D => G => store set
```

and proves monotonicity plus semantic soundness of `step` and `combine`.
Independent state domains use:

```text
gamma_dg d g = gamma_state d Int gamma_state g
```

The unit analysis uses:

```text
gamma_unit d g = gamma_state (d Sup g)
```

because its transfer merges the two restricted homogeneous slots before
applying `domain_transfer`.

## Final architecture

```text
analysis definitions
  |-- mixed_si_spec                  D = Sign, G = Interval
  |-- unit_dg_spec tf                D = G
  `-- retain_dg_spec tf              D = locals x snapshot, G = globals
            |
            v
DG_Framework
  dg_spec -> dg_edge_tree / dg_combine_tree
          -> side_cfg_T_eff_cmp_seed_dg
          -> vendor strategy_tree / TD solver via dg_state
            |
            v
DG_Soundness
  sound_dg_spec S gammaDG
          -> structural DG post-fixpoint
          -> semantic CFG post-fixpoint
          -> cfg_collect soundness
            |
            +-- Mixed Sign/Interval interpretation
            `-- homogeneous unit interpretation
```

The vendor solver remains polymorphic in one value lattice. `dg_state` is the
adapter at that boundary; analyses and soundness reason through separate `D`
and `G` projections.

## Public soundness dependency graph

The graph below follows actual theorem references in `src/**/*.thy`.

```text
sound_dg_spec
  |
  +-- dg_post_solution_postfix
  |     `-- part_post_solution_imp_se_constraint_holds
  |
  +-- dg_postfix_collect_sound
  |     `-- cfg_collect_semantic_postfix
  |           `-- cfg_collect_post_fixpoint_sound
  |
  `-- dg_post_solution_collect_sound
        |-- dg_post_solution_postfix
        `-- dg_postfix_collect_sound

interpretations
  |
  +-- sound_dg_spec_indep
  |     `-- mixed_si : sound_dg_spec mixed_si_spec gamma_dg
  |           |-- mixed_si_post_solution_postfix
  |           |-- mixed_si_postfix_collect_sound
  |           `-- mixed_si_post_solution_collect_sound
  |                 `-- mixed_si.dg_post_solution_collect_sound
  |
  `-- sound_dg_spec_unit
        `-- sound_transfer.dg :
              sound_dg_spec (unit_dg_spec tf) gamma_unit
```

The final mixed endpoint invokes the generic composite theorem directly. Its
two layered public endpoints remain available for clients that already possess
either a solver post-solution or a DG post-fixpoint.

No path reachable from `sound_dg_spec` uses:

- `pack_dg_tree`, `dg_env`, or a representation equality;
- a post-solution transport theorem;
- the Stage-1B split generator;
- a homogeneous collecting-soundness theorem.

`sound_dg_spec_unit` is a semantic `D = G` interpretation. It is not a packing
or equation-system transport wrapper.

## Remaining homogeneous proof tower

Several production APIs predate `dg_spec` and remain live:

- `effectful_domain_transfer`, `edge_tf_tree`, and `combine_tf_tree`;
- `side_cfg_T_eff_cmp_seed` and the context/digest generator tower;
- `sound_effectful_transfer*` and their context/digest soundness locales;
- `Call_Spec` and the Sign/Interval/named-global endpoints built on those APIs;
- executable bridges over the homogeneous state representation.

Examples include `sign_spec_post_fixpoint_sound`,
`side_sign_analysis_sound`, `side_ivl_analysis_sound`, and
`named_analysis_sound`. These paths do not transport from heterogeneous to
homogeneous and back; they are an independent legacy API family. Porting the
context/digest tower to `dg_spec` remains framework work.

## Dead-code audit

Consumer counts are source-level theorem/constant references outside the
listed cone, excluding declarations. A final full-session build checks
implicit uses through simplification, locales, and imports.

### Deleted

| Cone | External consumers | Reason | Replacement |
| --- | ---: | --- | --- |
| `Split_Cmp_Gen.thy`: `split_edge_tree*`, `split_combine_tree*`, `split_etf_of_transfer*`, split seeded generator, split spec generator, post-solution equalities | 0 | Stage-1B equality scaffolding | `dg_spec` and `side_cfg_T_eff_cmp_seed_dg` |
| Sign split witnesses: `sign_etf_split`, `Sign_spec_generator_split_eq`, `sign_spec_post_fixpoint_sound_split` | 0 | terminal migration witnesses | ordinary Sign endpoint or `unit_dg_spec` interpretation |
| Unit packing transport: `dg_rep_flat`, `dg_env`, `pack_dg_tree*`, traverse/sides/dep transports, solution transports, generator equality | 0 | representation bridge after native soundness | `sound_dg_spec_unit` |
| Sign DG packing witnesses: `sign_dg_*`, `sign_spec_post_fixpoint_sound_dg` | 0 | terminal transport validation | `sound_transfer.dg` interpretation |
| Homogeneous factoring: `step_edge_tree*`, `step_edge_tree_unit`, `retain_step`, `step_edge_tree_retain` | 0 | intermediate equality layer | `dg_edge_tree` and analysis-owned steps |
| Flat Retain bridge: `retain_dg_step`, `retain_dg_edge_tree`, `dg_rep`, traverse/sides equalities | 0 | intermediate representation validation | `retain_hetero_step` |
| Retain packing transport: `retain_hetero_rep`, `retain_pack_tree*`, fold/generator equivalences, `part_post_solution_retain_dg_iff` | 0 | terminal compatibility cone | `retain_dg_spec` and `retain_dg_generator` |
| Sign Retain witness: `sign_retain_dg_post_fixpoint_iff` | 0 | sole root of the Retain transport cone | no replacement required; no consumer used the endpoint |
| `wf_dg`, `emb_glob` | 0 | helpers used only by deleted transport | direct `dg_state` construction |
| Retain equation wrappers: `dg_spec_step_retain`, `apply_retain_dg_spec`, `combine_retain_dg_spec`, `eq_retain_dg_generator` | 0 | unreferenced migration witnesses | definitions of `retain_dg_spec` and `retain_dg_generator` |

### Kept

| Theorem family | Source consumers | Classification | Reason |
| --- | ---: | --- | --- |
| `traverse_dg_edge_tree`, `sides_dg_edge_tree_Inr` | 2 each | KEEP | structural extraction used by native DG soundness |
| `traverse_dg_combine_tree`, `sides_dg_combine_tree_Inr` | 1 each | KEEP | combine extraction used by native DG soundness |
| `dg_edge_tree_answer_pure_D`, `dg_edge_tree_side_pure_G` | 0 each | KEEP | public boundary guarantees that the framework preserves slot types |
| `traverse_side_rhs_fold_dg` | 1 | KEEP | equation form of the heterogeneous fold |
| `eq_side_cfg_T_eff_cmp_seed_dg` | 1 | KEEP | generator equation consumed by native soundness |
| `dg_spec_step_unit` | 1 | KEEP | unit semantic reduction consumed by `sound_dg_spec_unit` |
| `dg_post_solution_postfix`, `dg_postfix_collect_sound` | 2 each | KEEP | layered public soundness endpoints and components of the composite theorem |
| `dg_post_solution_collect_sound` | 1 | KEEP | canonical composite endpoint used by Mixed Sign/Interval |
| `sound_dg_spec_indep`, `sound_dg_spec_unit` | 1 each | KEEP | mixed and homogeneous interpretations |
| `mixed_si_post_solution_postfix`, `mixed_si_postfix_collect_sound` | 0 each | KEEP | public layered endpoints with distinct input contracts |
| `mixed_si_post_solution_collect_sound` | 0 | KEEP | terminal public theorem demonstrated by the executable mixed example |
| split/merge lattice and concretization laws in `Split_State.thy` | implicit simplifier and DG representation uses | KEEP | representation mathematics used by `split_dg` / `merge_dg` |

No item remains classified `UNKNOWN`. No `DELETE AFTER X` item remains in the
completed cleanup.

## Remaining limitations toward Goblint

Importance ranks describe architectural leverage, not implementation effort.

### Language and CFG limitations

| Rank | Limitation | Consequence |
| ---: | --- | --- |
| 1 | `combines g` has caller, callee exit, and return point but no return destination/lvalue | no faithful `combine_assign` or return-value assignment contract |
| 2 | IMP2's call/return model has no first-class return value and limited call metadata | Goblint's split `combine_env` / `combine_assign` interface cannot be represented directly |
| 3 | CFG activation and recursive-return witnesses remain specialized | context-sensitive recursive soundness requires additional witness plumbing |
| 4 | IMP2 stores integers only and has no pointer or memory model | memory domains, aliases, and Goblint-style library models are outside the language |

### Framework limitations

| Rank | Limitation | Consequence |
| ---: | --- | --- |
| 1 | `sound_dg_spec` currently fixes `D = 'd abs_state` and `G = 'g abs_state` | product-shaped `D`, including Retain's locals-plus-snapshot carrier, runs through the framework but cannot directly interpret the native soundness locale |
| 2 | context/digest generators and their soundness tower still use `effectful_domain_transfer` with one homogeneous value type | mixed `D`/`G` analyses currently use the plain heterogeneous CMP soundness path only |
| 3 | the vendor TD solver accepts one value lattice | `dg_state` packing and slot-purity invariants remain necessary at the solver boundary |
| 4 | the native DG theorem handles the simple CFG collecting endpoint and assumes ordinary edges exclude `EA_Enter` | enter/context/digest semantics need native heterogeneous counterparts |
| 5 | homogeneous executable bridges remain separate from `dg_spec` | mixed analyses need analysis-specific executable wiring rather than one shared bridge |

The highest-leverage next framework change is to generalize
`sound_dg_spec` from abstract-state-shaped `D`/`G` to arbitrary sound lattice
carriers with an analysis-supplied joint concretization. That unlocks native
Retain soundness without changing the executable framework.

### Analysis limitations

| Rank | Limitation | Consequence |
| ---: | --- | --- |
| 1 | no Goblint-style manager/query interface (`ask`, query result types, cross-analysis queries) | analyses cannot communicate through typed queries |
| 2 | Retain lacks a native `sound_dg_spec` interpretation because of the framework carrier restriction above | its heterogeneous instance is executable framework plumbing, while soundness still comes from the homogeneous Retain analysis |
| 3 | only the small Sign/Interval mixed analysis exercises native heterogeneous soundness | no mixed context-sensitive or digest-refined analysis yet |
| 4 | the analysis portfolio lacks relational domains and general widening/narrowing integration | precision remains below Goblint-class analyzers on relational programs |
| 5 | expression-range queries remain embedded in transfers | no reusable `range` query boundary for assumptions and clients |

## Verification contract

Completion requires:

- no references to deleted compatibility names;
- zero `sorry` under `src/`;
- all touched theories fully processed by I/Q;
- a green `Voblint_Formalization` batch build.
