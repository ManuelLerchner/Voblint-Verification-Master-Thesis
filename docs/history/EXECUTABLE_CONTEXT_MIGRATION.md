# Executable semantic-context migration plan (S4 runnability axis)

Historical note: the `TD_Side_Eff_Ctx_Sound` / `side_env_ctx` spine discussed in this plan has been deleted. Shared helpers now live in `TD_Side_Eff_Ctx_Shared`.

> **Agent entry point:** `SEMANTIC_CONTEXT_MIGRATION.md` (Track B / S0–S4).
> This file is the S4 detail: turning the *proven-sound* semantic entry-state
> context analysis into a *generator-driven executable* one. Source of truth for
> what is proved = the `.thy` files; this doc holds the runnability path only.

> **STATUS:** E0/E1 **DONE, batch-sealed** for sign. `Exec_Ctx_Bridge.thy`
> defines the executable context generator and the `_st`/abstract post-solution
> bridge. `Exec_Sign_Ctx_Gen_Run.thy` runs a compiled CFG through the real
> `TD_side_always_join_Interp_solve` and connects the result to
> `post_fixpoint_sound_at_ctx_semantic`. E2 precision remains open: the canonical
> two-call-site compiled example is not a strict witness under the current
> executable call semantics.

## Goal

Run the semantic (entry-state) context-sensitive analysis through the real
vendored side solver on a **compiled CFG**, driven by the equation-system
**generator** (`side_cfg_T_eff_ctx`), and exhibit a **machine-checked**
(`by eval`) precision gain over the monovariant analysis on the same program.

Not "a hand-built equation system that runs" (that is the viability probe, already
done) — the actual analysis: program -> `compile_prog` -> CFG -> context-indexed
generator -> solver -> context-separated result.

## What already exists (verified this session — do not rebuild)

- **Abstract soundness DONE, batch-sealed.** `semantic_entry_store_ctx_analysis_sound`,
  `post_fixpoint_sound_at_ctx_semantic`, `side_collect_sound_exit_pruned_ctx`
  (`TD_Side_Eff_Ctx_Sound.thy`); precision witness `entry_store_context_precision_witness`
  (`Example_Entry_Store_Context_Precision.thy`).
- **Abstract context generator + denotation + bounds** (`TD_Side_Tree.thy`):
  `side_cfg_T_eff_ctx` (over the abstract etf record), `unit_combine_tree_ctx` (the
  value-dependent semantic combine, single unit global), `eq_side_cfg_T_eff_ctx`,
  the `side_acc_ctx` bounds. NOT executable: abstract etf record, abstract
  `restrict_local` / `restrict_global`.
- **Solver viability PROVEN executable** (`Exec_Sign_Ctx_Run.thy`,
  `Exec_Ivl_Ctx_Run.thy`): a *hand-built* `pp \<times> 'a st` equation system runs through
  `TD_side_always_join_Interp_solve`; `by eval` seals per-context separation
  (`Gg = SZero` vs `SPos`; `[0,0]` vs `[5,5]`) and strict precision over the merge.
  Establishes: (a) `pp \<times> 'a st` code-generates as the unknown index; (b) the
  solver runs over context-indexed unknowns; (c) the precision is real and
  evaluable. These are stepping stones, NOT the deliverable.
- **Monovariant executable generator EXISTS** (`Exec_Bridge.thy`): `side_cfg_T_eff_st`
  over the executable `_st` etf record (`ivl_etf_st` / `sign_etf_st`,
  `Interval_Exec.thy` / `Sign_Exec.thy`), run on compiled CFGs in `Exec_Ivl_Run.thy`
  through both `TD_side_always_join_Interp_solve` and
  `TD_side_warrowing_apinis_Interp_solve` (real widening). This is the executable
  spine the context version must mirror.

## Key design findings (verified, ground the phases)

1. **Context propagates by recursive query — no special proc-entry seeding.**
   Querying `(exit, c')` pulls the whole callee subgraph re-evaluated at `c'`,
   bottoming out at the *context-independent* program-entry seed (cfg_entry has no
   predecessors; its `acc0` is the fixed `s0` seed for every context). So the
   uniform intra relabel `map_ltree (\<lambda>w. (w, c))` (context unchanged along intra
   edges, including `EA_Enter`) plus the value-dependent combine `cmb` creates
   distinct callee-exit unknowns for distinct call contexts. This is necessary for
   precision but not sufficient: the callee body still receives only the state
   produced by the executable transfer trees.
2. **Executability needs the `_st` record, not the abstract one.**
   `side_cfg_T_eff_ctx` uses `apply_etf etf` / abstract `restrict_*`; the runnable
   version needs `apply_etf_st` / `restrict_*_st` and an executable `cmb`. ->
   define `side_cfg_T_eff_ctx_st` + `unit_combine_tree_ctx_st` (mechanical `_st`
   mirrors of the proven-sound abstract defs).
3. **Context type `'c = 'a st`** (abstract entry state) code-generates (lifted type
   carries `equal`; product `pp \<times> 'a st` works — demo-verified). The *soundness*
   instance's `entry_store_ec = edge_collect EA_Enter` is an infinite store set and
   is NOT code-generatable; the executable `ec` keys on the abstract value:
   `ec ctx sc = sc` (or a projection) — callee context = abstract caller state.
4. **Globals stay shared** (Goblint encoding: `'g` not context-indexed). Two context
   writes to a shared global JOIN -> that is the monovariant baseline, not a gain.
   The context precision lives in the context-LOCAL / return view. Encode the
   observed value as a context-local (as the demos do), not a shared global.
5. **Compiled calls currently do not pass caller locals into the callee body.**
   `EA_Enter` keeps globals and resets locals to top. Globals are then read through
   the shared side slot. Therefore a compiled `x := v; f(); ...` witness with
   `f` reading local `x` loses `x` at enter, while a witness with `f` reading a
   global sees the joined global side value. The hand-built
   `Exec_Sign_Ctx_Run.thy` witness separates because its entry equation returns
   the context state directly; the generator-built compiled CFG does not currently
   have that per-context callee-entry seed. (The sibling keyed `cmp` generator
   `side_cfg_T_eff_cmp` *does* add exactly this: it filters `EA_Enter` from the
   intra fold and seeds a context-independent fresh frame at frame-entry nodes,
   sound via `sound_effectful_transfer_framed` — see
   `docs/KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md`. The `ctx` generator described
   here keeps the uniform-relabel approach and is unchanged.)
6. **Finiteness.** Contexts materialize only as the solver reaches them; finite for
   a terminating program. A guaranteed bound (`solve_dom` / Context-Gas) is future
   (E4), unchanged from the monovariant `solve_dom` assumption.

## Phases (dependency-ordered)

```
E0  executable context generator (infra)      moderate   side_cfg_T_eff_ctx_st
E1  soundness link (fun_of_st bridge)          moderate   inherit abstract proof
E2  two-call-site precision witness            moderate   the headline deliverable
E3  interval real-widening analogue            low-mod    ties to interval-apinis
E4  termination / solve_dom (Context Gas)      FUTURE     out of scope
```

### E0 — Executable context generator (infrastructure)

**New theory** `src/Analysis/Generic/Solver/Exec_Ctx_Bridge.thy` (imports
`Exec_Bridge` + `TD_Side_Tree`). Two pure-executable definitions, `_st` mirrors of
the proven-sound abstract ones:

- `unit_combine_tree_ctx_st ec cc ex ctx` — `unit_combine_tree_ctx` with
  `restrict_local_st` / `restrict_global_st` (the value-dependent semantic combine,
  single unit global, executable).
- `side_cfg_T_eff_ctx_st cmb g etf bot0_st s0_st gseed (v, c)` —
  `side_cfg_T_eff_ctx` with `apply_etf_st` and `restrict_*_st`: intra trees
  relabelled `(w, c)` via `map_ltree`, combine trees from `cmb`, folded by
  `side_rhs_fold_ctx`, entry `Side` seed.

**Acceptance:** the generator EVALUATES — `value` / `by eval` on a small compiled
CFG (`compile_prog`) with `etf = ivl_etf_st` / `sign_etf_st`, `'g = unit`,
`cmb = unit_combine_tree_ctx_st ec`, `ec ctx sc = sc`, through
`TD_side_always_join_Interp_solve`, returns a result. (Single-call is fine here —
E0 proves the GENERATOR runs, not yet precision.)

### E1 — Soundness link (inherit the abstract proof)

The runnable witness must be a *sound over-approximation*, not just a printout.
Mirror the monovariant `_st` bridge (`fun_of_st_eq_side_cfg_T_eff_st`,
`Exec_Bridge.thy:667`): prove the `_st` context generator's denotation maps, under
`fun_of_st`, onto the abstract `side_cfg_T_eff_ctx` the soundness chain
(`post_fixpoint_sound_at_ctx_semantic`) already covers — with `cmb =`
`unit_combine_tree_ctx_st ec` matching the abstract `unit_combine_tree_ctx ec`.

**Acceptance:** a lemma connecting an executable post-solution of
`side_cfg_T_eff_ctx_st` to `cfg_collect_ctx ... \<le> gamma (side_env_ctx ...)`, so
the `by eval` numbers in E2 carry a machine-checked soundness guarantee.
**Risk:** the abstract `ec`/`cmb` of the soundness theorem vs the executable
`ec`/`cmb` must line up (the `_st` vs abstract `restrict_*` reconciliation via
`fun_of_st`). The instance `ec` here (`ec ctx sc = sc`) differs from the soundness
witness's `entry_store_ec`; E1 must either (a) re-instantiate
`post_fixpoint_sound_at_ctx_semantic` for the abstract-value `ec` and its digest
`dg` (define a `value_ctx_dg` whose `DG_*`/`ENTER_MONO` discharge), or (b) accept
E2 as runnability-only and keep soundness on the entry-store instance. **Decide at
E1 start** (open question 1).

### E2 — Two-call-site precision witness (headline)

**Current gap.** Two witness designs have been checked and do not give a strict
compiled precision result:

- Global-input design: assign a global differently before two calls and let the
  callee read it. The callee reads the shared global side slot, so the two values
  are joined before the context-specialised callee states can separate them.
- Caller-local design: assign a local differently before two calls and let the
  callee read or preserve it. The compiled `EA_Enter` transfer resets locals to
  top, and the outer caller context is not changed on return.

Under the current executable generator, context sensitivity changes which callee
exit unknown is queried. It does not make the context value itself the callee-entry
state. A strict compiled E2 witness therefore needs either a program observable
that becomes context-dependent despite `EA_Enter` and the shared global side slot,
or a deliberate executable-semantics extension that seeds procedure entry from
the context value and is then bridged to the abstract soundness theorem.

The original concrete target was a new
`src/Formalization/Examples/Example_Exec_Ctx_Precision.thy` theory compiling a
program with two call sites at different abstract caller states: the canonical
`x := 0; f(); x := 1; f();` with `f` doing `Gg := x`. That target is blocked by
the current executable call semantics above.

The next E2 attempt should first identify a compiled program whose callee exit is
genuinely context-dependent under `side_cfg_T_eff_ctx_st`. Then run
`side_cfg_T_eff_ctx_st` and, on the same CFG, the monovariant
`side_cfg_T_eff_st`. `by eval` should seal:

- per-call-site context separation (call 1 context -> `Gg = SZero`/`[0,0]`,
  call 2 context -> `SPos`/`[5,5]`);
- `generator_context_strictly_more_precise`: each context value `<` the
  monovariant `side_cfg_T_eff_st` value at the same point.

**Acceptance:** machine-checked, generator-driven (NOT hand-built `eqsT`), over a
compiled CFG. This is the deliverable the demos only gesture at.
**Risk:** the IMP2 procedure encoding — get two call sites that genuinely see
different abstract `x` (flow-sensitive). Needs the `com` Scope/Call/Restore +
`compile_prog` understood (cf. `Example_Side_Branch_Calls.thy`,
`Example_Entry_Store_Context_Precision.thy`). And empirical confirmation that the
recursive-query context propagation terminates and separates on the real CFG
(finding 1 in theory; verify in practice).

### E3 — Interval real-widening analogue (stretch)

Repeat E2 with `TD_side_warrowing_apinis_Interp_solve` (real interval widening) so
the executable context analysis runs on the infinite-height domain through the
genuinely-terminating solver. Ties to the deferred interval-apinis SOUNDNESS
(separate transport; the `restrict_global_st`-closure-under-`\<nabla>\<Delta>` first
obligation is already de-risked — see `crispy-snuggling-hinton.md`). Runnability
here does not need that soundness; it needs the solver to terminate (it does — the
apinis solver is the one `Exec_Ivl_Run` already runs).

### E4 — Termination / solve_dom (FUTURE, out of scope)

A guaranteed finite context set (Context Gas) + a real `solve_dom` for the
warrowing side solver. Same standing assumption as the whole pipeline today.

## Open questions (decide before the relevant phase)

1. **E1 soundness scope.** Re-instantiate `post_fixpoint_sound_at_ctx_semantic` for
   the executable abstract-value `ec` (full machine-checked soundness on the
   runnable instance), or keep soundness on the entry-store instance and treat E2
   as runnability-only? Trade: full re-instantiation = more proof, a `value_ctx_dg`
   - its `DG_*`/`ENTER_MONO` discharge; runnability-only = faster, but the executed
   numbers are not formally tied to the soundness theorem.
2. **`ec` shape.** `ec ctx sc = sc` (full caller state as context) is simplest and
   separates; a projection (e.g. only the parameter/observed variables) gives a
   coarser-but-still-precise context and smaller context sets. Pick per the witness
   program.
3. **Program encoding.** Reuse a two-call-site IMP2 program shape (scope/param) that
   compiles to distinct abstract caller states at the two sites — confirm against
   the existing proc examples before committing.

## Verification

Per CLAUDE.md: I/Q inner loop (`get_diagnostics` clean per file), ASCII-only
sources, batch build as the gate. Per slice: `isabelle build ... Voblint_Analysis`
(E0/E1/E3), `... Voblint_Formalization` (E2). Done = green `-v` batch log +
`by eval` theorems, not `value` printouts.
