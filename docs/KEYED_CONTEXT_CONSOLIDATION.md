# Keyed context-analysis consolidation

Status: reviewed 2026-07-01. This pass adds no functionality and weakens no
theorem. The implementation remains the source of truth; this note records the
architecture and remaining debt.

## Executive summary

The redesign solves the precision loss caused by context-sensitive local unknowns
reading from a context-blind global pot. Before the redesign, a callee reached
under two different caller-global values still read `glob_env`, the join of all
global slots. Indexing only local unknowns by context could not recover the
callee's per-context global input.

Filtering `EA_Enter` was insufficient on its own. The collecting semantics still
contains every enter edge, and `post_fixpoint_sound_at_eff` asks for a bound for
each one. Dropping enter edges from the generator fold removes the proof route
for those edges. The key observation is that enter has a special shape: it resets
locals to a fresh frame and preserves globals. The framed-enter contract states
that shape as an upper bound:

```
etf_full (etf_enter etf u) sigma <= fresh_frame sup glob_env sigma
```

under the local/global-slot invariants. This lets the keyed generator filter
`EA_Enter` out of the intra fold, seed a context-independent fresh frame at
frame-entry nodes, and still discharge the enter-edge proof obligation.

The key abstraction is therefore the framed-enter contract, not the concrete
sign example. It separates a semantic fact about procedure entry from the
keyed generator's routing logic. Domains that want to use the keyed generator
prove one framed instance; the generator proof then handles enter and non-enter
edges uniformly at the final theorem boundary.

Formally proved now: `glob_env_cmp` and `side_env_cmp`; the `pull_cmp` reduction
from filtered reads to monovariant soundness; the read-agnostic semantic-context
backbone; the keyed generator `side_cfg_T_eff_cmp`; the enter/non-enter routing
theorem `side_cfg_T_eff_cmp_collect_sound`; the executable `_st` keyed generator;
the sign framed instance `sign_sound_etf_unit_framed`; and executable sign
witnesses, including the finite-context example that separates `SZero` and
`SPos` while the join-all read yields `SNonNeg`.

Open work remains in certification and generalisation: bridge concrete executable
`st` solver runs to the abstract post-fixpoint theorem, instantiate the framed
contract for interval, factor a reusable finite context interface, and decide how
far to pursue value-dependent combine and semantic Path-B contexts.

## Responsibility table

| Theory | Purpose | Inputs | Outputs | Later dependents |
| --- | --- | --- | --- | --- |
| `Global_Cmp_Read` | Defines context-compatible global reads. | `TD_Side_CFG`, finite global keys, compatibility `cmp`. | `glob_env_cmp`, `side_env_cmp`, collapse/monotonicity/code lemmas. | `TD_Side_Eff_Cmp_Sound`, `TD_Side_Eff_Cmp_Pull`, examples. |
| `sound_effectful_transfer_framed` | States the enter upper bound needed when enter is filtered from the fold. | `sound_effectful_transfer`, `fresh_frame`, `inr_slot_locals_bot`, `inl_slot_globals_bot`. | Framed locale/contract, consumed through `etf_enter_framed_le`; sign instance `sign_sound_etf_unit_framed`. | `TD_Side_Eff_Cmp_Gen`, finite and generator examples. |
| `TD_Side_Eff_Cmp_Pull` | Pulls a filtered keyed read back to the existing monovariant effectful theorem. | `side_env_cmp`, `pull_cmp`, `post_fixpoint_sound_at_eff`. | `post_fixpoint_sound_at_cmp_pull`, `cmp_edge_sound`, `cmp_entry_sound`. | `TD_Side_Eff_Cmp_Gen`, semantic keyed soundness wiring. |
| `TD_Side_Eff_Cmp_Gen` | Builds and proves the abstract keyed generator. | Unit-global `etf`, `map_ltree`, `map_gtree`, `gkey`, combine builder, framed contract. | `side_cfg_T_eff_cmp`, routing lemmas, `side_cfg_T_eff_cmp_collect_sound`, `_eq` corollary. | `Exec_Cmp_Bridge`, `Exec_Sign_Cmp_Keyed_Gen_Run`, `Example_Finite_Sign_Context_Analysis`. |
| `TD_Side_Eff_Cmp_Sound` | Gives the semantic-context theorem for arbitrary reads and the keyed `cmp` instance. | Trace witnesses, digest compatibility, `side_env_cmp`, combine reassembly obligations. | `post_fixpoint_sound_at_ctx_semantic_cmp_final`, `combine_read_cmp`, `combine_read_cmp_le`. | `TD_Side_Eff_Cmp_Pull`, `Exec_Sign_Cmp_Keyed_DG_Run`. |
| `Exec_Cmp_Bridge` | Mirrors the keyed generator for executable `st` states. | `_st` transfer trees, `map_gtree`, executable fold, side-result invariant. | `side_cfg_T_eff_cmp_st`, `eq_side_cfg_T_eff_cmp_st`, `side_rg_side_cfg_T_eff_cmp_st_unit`. | `Exec_Sign_Cmp_Keyed_Gen_Run`, `Example_Finite_Sign_Context_Analysis`. |
| `Exec_Sign_Cmp_Keyed_DG_Run` | Current keyed witness for sign. | `TD_Side_Eff_Cmp_Sound`, `Sign_DG`, bool contexts. | `dg_D_val`, `dg_G_val`, `dg_meaning`, `dg_combine_obligation`. | roadmap/design docs. |
| `Exec_Sign_Cmp_Keyed_Gen_Run` | Runs the real compiled CFG through the executable keyed generator. | `Exec_Cmp_Bridge`, sign executable transfer, seeding combine. | `kgen_part_post_solution_st`, materialised slots, `kgen_keyed_generator_sound_if_post_fixpoint`. | Finite-context design comparison, future executable-to-abstract bridge. |
| `Example_Global_Ctx_Read_Precision` | Read-layer witness: filtered reads separate global-derived contexts. | `Global_Cmp_Read`, sign domain, bool keys. | `read_ctx_False`, `read_ctx_True`, `filtered_below_join_all`. | Design rationale only. |
| `Example_Finite_Sign_Context_Analysis` | Canonical executable finite-context demonstration. | `Exec_Sign_Cmp_Keyed_Gen_Run`, finite `sign_gctx`, compiled program. | `fctx_slot_zero_precise`, `fctx_slot_pos_precise`, `fctx_join_all`, `fctx_keyed_sound_if_post_fixpoint`. | Thesis/example narrative, future finite context interface. |

## End-to-end graph

```text
Concrete semantics
  cfg_collect / trace_witness / enter_state
    |
    v
Abstract transfer contract
  sound_effectful_transfer
  post_fixpoint_sound_at_eff
    |
    v
Framed enter contract
  sound_effectful_transfer_framed
  etf_enter_framed_le
  sign_sound_etf_unit_framed
    |
    v
Filtered read layer
  glob_env_cmp
  side_env_cmp
  pull_cmp
  side_env_cmp_pull
    |
    v
Semantic keyed theorem
  post_fixpoint_sound_at_ctx_semantic_generic
  post_fixpoint_sound_at_ctx_semantic_cmp_final
  combine_read_cmp_le
    |
    v
Keyed generator
  map_gtree
  side_cfg_T_eff_cmp
  pull_gk
  side_cfg_T_eff_cmp_edge_le
  side_cfg_T_eff_cmp_enter_le
  side_cfg_T_eff_cmp_combine_le
  side_cfg_T_eff_cmp_collect_sound
    |
    v
Solver / post-solution
  part_post_solution over side_cfg_T_eff_cmp
  side_cfg_T_eff_cmp_collect_sound_eq
    |
    v
Executable bridge
  side_cfg_T_eff_cmp_st
  side_rg_side_cfg_T_eff_cmp_st_unit
  TD_side_always_join_Interp_solve
    |
    v
Examples
  Example_Global_Ctx_Read_Precision
  Exec_Sign_Cmp_Keyed_DG_Run
  Exec_Sign_Cmp_Keyed_Gen_Run
  Example_Finite_Sign_Context_Analysis
    |
    v
Soundness-facing theorem
  fctx_keyed_sound_if_post_fixpoint
  kgen_keyed_generator_sound_if_post_fixpoint
```

## Theory cleanup review

No `.thy` edit was made in this pass.

- Duplicated helper lemmas: no dead duplication found. Similar names are
  pullback-specific: `pull_cmp` masks incompatible keyed globals for arbitrary
  `cmp`; `pull_gk` maps a unit-global transfer to one selected keyed slot. Keeping
  them separate makes the two proof obligations readable.
- Naming: consistent enough to keep. The `cmp_*` names denote filtered reads;
  `*_gk_*` denotes the single-key generator pullback; `_st` denotes executable
  state mirrors.
- Dead definitions: none found in the reviewed theories. Some examples are
  design witnesses rather than later imports; they still carry documented value.
- Obsolete comments: no stale implementation claims found. The finite and `kgen`
  examples correctly state that executable-to-abstract certification remains open.
- Duplicate proofs: the edge/combine routing proofs have similar structure but
  different predecessor lists and transfer constructors. Extracting a helper now
  would add abstraction without reducing proof risk enough.
- Unnecessary specialisation: the finite sign example is deliberately specialised;
  the generalisation belongs in a future `context_domain` locale.

## Example review

| Example | Demonstrates | Semantic/executable | Abstract/concrete | Precision | Soundness | Limitations |
| --- | --- | --- | --- | --- | --- | --- |
| `Example_Global_Ctx_Read_Precision` | `glob_env_cmp` separates two global-derived bool contexts; join-all merges them. | Semantic/read-layer, executable `eval` only for join-all witness. | Abstract sign states. | Yes, at read layer. | Not end-to-end; only shows filtered read is below join-all. | No solver/generator; no CFG analysis result. |
| `Exec_Sign_Cmp_Keyed_DG_Run` | Current keyed DG witness discharges the DG combine theorem and keyed meaning equalities. | Semantic proof witness. | DG `dg_state` values. | Yes, keyed context separation. | Shows the DG combine and read obligations directly. | No homogeneous compatibility stack. |
| `Exec_Sign_Cmp_Keyed_Gen_Run` | Compiled CFG plus executable keyed `_st` generator runs through TD side. | Executable, with a soundness-facing abstract theorem schema. | Concrete `sign st` run plus abstract theorem counterpart. | Partial: pure zero context precise; merged context stays `SNonNeg`. | `kgen_keyed_generator_sound_if_post_fixpoint` for any abstract post-fixpoint. | Concrete `st` result is not yet bridged to the abstract post-fixpoint theorem; context type `sign st` is not finite in the theorem instance. |
| `Example_Finite_Sign_Context_Analysis` | Finite context/key type derived from global `G`; two call activations stay separated. | Executable canonical demo plus abstract theorem schema. | Concrete `sign st` run and abstract post-fixpoint theorem. | Yes: `GZero` slot gives `SZero`, `GPos` slot gives `SPos`, join-all gives `SNonNeg`. | `fctx_keyed_sound_if_post_fixpoint` connects the finite generator shape to `side_cfg_T_eff_cmp_collect_sound_eq`. | Still needs concrete executable-to-abstract bridge for the specific solver result. |

The finite-context example is the canonical executable demonstration. It uses a
finite key type, a compiled program, the executable keyed generator, the real
side solver, and proves the expected separated slots by evaluation.

## Documentation audit

- `docs/ROADMAP.md`: matches the implementation. It names the keyed read layer,
  pullback, generator, framed enter contract, sign instance, finite example, and
  the remaining bridge.
- `docs/history/KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md`: matches the implementation and
  accurately describes why filtering `EA_Enter` needs a framed contract.
- `docs/GLOBAL_CONTEXT_REDESIGN.md`: mostly historical, but its status header
  correctly says the design landed and points to the finite example. The older
  "decision needed" section is preserved as design history; do not read it as
  current backlog.
- `docs/history/EXECUTABLE_CONTEXT_MIGRATION.md` and `docs/history/SEMANTIC_CONTEXT_MIGRATION.md`:
  correctly mark the old seeded/context-local route as limited and point to the
  keyed/framed solution for the executable precision route.
- `docs/GLOSSARY.md`: now has keyed-context entries.
- `docs/PROOF_OVERVIEW.md` and `docs/PROOF_PHASES.md`: now point to this note so
  the keyed branch is visible from the main proof docs.
- Thesis references: `docs/thesis/trace-pivot-and-history-sensitive-globals.md`
  predates the landed keyed generator. Treat it as chapter draft material; update
  before quoting it as current implementation status.

No remaining stale claim was found that asserts a missing theorem as complete.

## Technical debt

Small engineering tasks:

- Executable-to-abstract bridge: mostly a transport lemma from `sign st`
  post-solutions to `sign abs_state` post-fixpoints for the keyed generator. It is
  local and mechanical, but proof details matter.
- Interval framed instance: prove `sound_effectful_transfer_framed` for interval.
  It mirrors the sign instance and should not change architecture.
- Renderer cleanup: context GraphViz/debug output can follow the settled finite
  context shape. This is presentation/tooling, not proof architecture.
- Theorem naming: align names around `cmp`, `gk`, `_st`, and finite contexts.
  Useful for navigation, low semantic risk.
- Helper extraction: only extract after the edge/combine routing pattern repeats
  in another domain. Premature extraction would obscure the current proofs.

Medium architectural tasks:

- `context_domain` locale: factors finite context/key operations, digesting, and
  compatibility assumptions. It changes the interface shape across examples.
- Reusable finite context interface: separates enumerability, key selection,
  compatibility, and executable context computation. This affects generator
  clients and example structure.

Research tasks:

- Value-dependent combine: the current generic theorem uses the conservative
  combine shape. Fully value-dependent combines interact with monotonicity and
  side effects, so this is proof-design work.
- Path B semantic contexts: semantic entry-state contexts need a different bridge
  from traces/digests to executable contexts. This is beyond cleanup.
- Optimality questions: proving precision optimality for keyed contexts requires a
  specification of the best abstraction and comparison theorem, not just soundness.
