# CTX Dependency-Cone Audit (2026-07-12)

Produced during execution of the context-generator migration. This is the real
dependency audit; the file of this name referenced by the original migration plan never
existed. Import edges are taken directly from the `theory ... imports ... begin` headers.

## Key finding: CMP is layered on the context-indexed soundness core

The migration plan assumed the CMP path is standalone and the three "CTX core" theories
are used only by CTX examples. The import graph refutes this:

```
TD_Side_Eff_Cmp_Gen        (canonical CMP generator)
  imports TD_Side_Eff_Cmp_Pull
    imports TD_Side_Eff_Cmp_Sound
      imports TD_Side_Eff_Ctx_Sound   <-- context-indexed soundness CORE
              Global_Cmp_Read
              Context_Domain

Exec_Cmp_Bridge            (canonical CMP executable bridge)
  imports Exec_Ctx_Bridge          <-- shared executable helpers
          TD_Side_Eff_Cmp_Gen

Seeded_Activation_Sound    (activation spine)
  imports Seeded_Clean_Ctx_Collect <-- not orphaned
```

`TD_Side_Eff_Cmp_Sound` reuses `TD_Side_Eff_Ctx_Sound`'s theorems pervasively:
`post_fixpoint_sound_at_ctx_semantic`, `combine_case_ctx_sound`, `side_env_ctx`,
`cfg_collect_ctx`, `semantic_entry_store_ctx_analysis_sound`. `TD_Side_Eff_Cmp_Gen` is
defined over `side_rhs_fold_ctx` / `side_acc_ctx` / `side_cfg_T_eff_ctx` from
`TD_Side_Tree`. The "Ctx" label denotes **context-indexed** collecting soundness shared by
both enter strategies, not the query-based enter strategy.

## Classification

### RETAIN — shared substrate (non-empty cone)

| Theory / definition | Required by |
|---|---|
| `TD_Side_Eff_Ctx_Sound` | `TD_Side_Eff_Cmp_Sound` (CMP spine → `Analysis_Sound`) |
| `Exec_Ctx_Bridge` (shared helpers) | `Exec_Cmp_Bridge` (`unit_combine_tree_ctx_st`, `st_of_abs`, `side_rhs_fold_ctx_st`) |
| `Seeded_Clean_Ctx_Collect` | `Seeded_Activation_Sound` |
| `TD_Side_Tree` CTX generators (`side_cfg_T_eff_ctx*`, `unit_combine_tree_ctx`) | CMP_Gen, CMP_Sound, Ctx_Sound |
| `Example_Global_Ctx_Read_Precision` | context-precision witness over `glob_env_cmp` (no CTX generator) |
| `Example_Entry_Store_Context_Precision` | witnesses retained `semantic_entry_store_ctx_analysis_sound` |

### DELETE — empty cone (query-executable demo surface)

| Item | Kind | Cone before deletion |
|---|---|---|
| `Canonical_Generator.thy` | broken prototype | never in any ROOT |
| `Analysis_Configuration.thy` | premature locale | only Canonical_Generator |
| `Exec_Sign_Ctx_Run` | example | leaf |
| `Exec_Sign_Ctx_Gen_Run` | example | leaf |
| `Exec_Sign_Ctx_Seeded_Run` | example (unsound-by-construction) | leaf |
| `Exec_Ivl_Ctx_Run` | example | leaf |
| `Exec_Ivl_Ctx_Gen_Run` | example | leaf |
| `Exec_Context_Run_Common` | shared scaffold | only the two `_Ctx_Run` examples |
| `side_cfg_T_eff_ctx_st`, `side_cfg_T_eff_ctx_seeded_st` (+ their transport clusters in `Exec_Ctx_Bridge`) | executable generators | only the deleted examples |

Two retained CMP examples (`Exec_Sign_Cmp_Keyed_Gen_Run`, `Exec_Ivl_Cmp_Seed_Clean_Run`)
imported CTX examples **only for transitive dependencies** — a full name-by-name check
found no retained file uses any CTX-example definition. They were repointed to
`Sign_Exec_Sound` / `Exec_Ivl_Run`.

## Verification

- `rg` for each of the ~55 definitions in the deleted examples: zero uses in retained `src/`.
- `rg` for the four executable-transport theorems and cluster lemmas: zero uses outside
  `Exec_Ctx_Bridge`.
- `Voblint_Formalization` batch build green after each deletion phase.

## Consequence for the plan's headline figures

"8 generators → 1", "one soundness spine" are not achieved and were not attempted:
collapsing the generators would require re-proving CMP soundness independently of the
retained context-indexed core, an explicit non-goal. The abstract CMP generator is already
single (`side_cfg_T_eff_cmp`, seeding via the `fresh_frame` parameter); the executable
unseeded generator already reduces to the seeded one with a constant seed
(`Exec_Cmp_Bridge.seed_generalises`).
