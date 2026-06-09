# Handoff — Start the Seidl Trace Migration

Pick-up doc for the **trace-semantics pivot** in this repo. Read this top-to-bottom
once. **New work:** **consolidate first** (`docs/UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md`,
U1–U2), then execute **M3.5 — the interprocedural trace bridge**
(`docs/M3_5_INTERPROC_TRACE_HANDOFF.md`), the prerequisite for M4. M0/M2/M3/M1 are
**done** on `trace-spike`. **Historical gate:** §3 (Phase 0 / M0). The deep reasoning
lives in the KB; this doc is the actionable extract.

KB companion (read these for *why*, not just *what*):

- `~/git/goblint-formalization-kb/wiki/research/seidl-pivot-migration-plan.md` — the
  phased plan (this doc executes its Phase 0 + Phase 1).
- `~/git/goblint-formalization-kb/wiki/research/seidl-restructuring-2026-06.md` —
  impact analysis, file-by-file table, what survives.
- `~/git/goblint-formalization-kb/wiki/concepts/trace-semantics.md` — the concrete
  foundation and the "semantics stronger than analysis" argument.
- `~/git/goblint-formalization-kb/wiki/concepts/imp2.md` — §"Why vendor-trim" (Phase 1).
- `~/git/goblint-formalization-kb/wiki/research/architecture-decisions.md` — the AD
  ledger. **Respect locked ADs; do not flip them — see §6.**
- `docs/PROCEDURES_EXTENSION_PLAN.md` — interprocedural CE1–CE4, §9 thesis path (M1).
- `docs/UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` — **follow-on migration** (consolidate
  parallel stacks before M4); KB: `unified-analysis-migration-plan.md`.

> Status when written (2026-06-05): planning complete, **no proof-repo code changed
> yet**. Branch `main` is sorry-free. This doc is the first executable step.

> **Status update (2026-06-09) — next milestone is M3.5, consolidate-first.** KB review
> (`~/git/goblint-formalization-kb`, meeting 5 + Cousot TCS 2002 read) surfaced that the
> trace work is **intraprocedural** (`cfg_collect_trace`, `trace = store list`) and the
> procedures are **state-based** (`cfg_collect_ip`, `combine_states`). Their product —
> the **interprocedural trace collecting** (`enter`/`combine` *on traces*) — is the
> missing piece and M4's real prerequisite. Tracked as **M3.5**; scoped handoff in
> **`docs/M3_5_INTERPROC_TRACE_HANDOFF.md`**.
>
> **Sequencing decision (Manuel, 2026-06-09): consolidate first.** Do
> `UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` U1–U2 *before* M3.5, so the trace-IP collecting
> lands as a `collecting_trace` **interpretation** of the one locale, not a fifth
> parallel stack.
>
> **Trace type — decided against Cousot (TCS 2002 §3–5).** A trace is a **state
> sequence** ($\Sigma$ = config); actions are an optional enrichment. `store list`
> (action-free) was enough for the `last`-only lift lemma; M3.5 enriches to the
> **action-labelled** form `(edge_action × store) list` so the global read (M4) can find
> the **last preceding write**. Composition is **junction** (overlap the shared boundary
> state), not raw concatenation; `cfg_collect_trace_ip` is an `lfp` of the shape
> `base ∪ (step ⌢ X)` — the same skeleton as `cfg_collect_paths`. KB:
> `wiki/concepts/trace-semantics.md` §Representation.

> **Progress update (2026-06-06, branch `trace-spike`).** M0 + the Phase 2
> soundness layer are **green** (full `isabelle build`, sorry-free):
>
> - `src/CFG/Collecting/CFG_Trace_Collect.thy` — `edge_step`, `edges_trace`,
>   `cfg_collect_trace`, `alpha_last`, and the gate theorem `lift`
>   (`alpha_last (cfg_collect_trace g S v) = cfg_collect_paths g S v`). **M0.**
> - `src/Pipeline/Trace_Soundness.thy` — `cfg_collect_eq_alpha_last_trace`
>   (master equation, AD-3 content), `pipeline_sound_trace` (generic, covers
>   every `sound_domain`), `runs_to_iff_exit_trace` (operational reading),
>   `sign_pipeline_invariant_sound_trace` (concrete witness).
> - `src/Examples/Example_Trace_NonTerminating.thy` — per-pp trace safety on a
>   non-terminating program + empty-exit-trace lemma.
>
> Phase 2 was done **additively**: because `lift` is an equality, the trace
> soundness is derived from the existing state-based theorems through
> `alpha_last`, leaving the CFG/Collecting/Domains/Pipeline spine untouched.
> This satisfies M2's exit criterion (examples pass via `alpha_last`, sorry-free)
> without the destructive spine rewrite the original Phase 2 sketch envisioned.
>
> **Phase 1 (frame-stack route) — substrate + procedure semantics green:**
>
> - `src/IMP2/IMP2_Globals.thy` — `pname`, `is_global`, `combine_states` (`<_|_>`)
>   + the combine algebra (collapse/nest/upd/cases). The Level-1 locals/globals
>   split over the scalar store; self-contained, no `com` ripple.
> - `src/IMP2/IMP2_Proc.thy` — procedure-extended command type `pcom`
>   (`PScope`/`PCall`/runtime `PRestore`), `proc_table`, frame-stack `pstep`
>   small-step, `pstep_deterministic`, and `scope_local_assign_noop` (frame
>   mechanism validation). Built **additively** (separate from `com`) so the
>   spine stays green; the `com`->`pcom` pipeline rewire is the next step.
>
> **Plan correction (verified).** Handoff §4 / KB "Step 0 — delete countability
> first" is **wrong for this repo**: the `edge_action` linorder (derived from
> countability) is load-bearing — `cfg_edges_list` (`CFG_Def.thy`) uses
> `sorted_list_of_set (edges g)`, and `predecessor_list` (built on it) drives the
> TD solver core (`rhs_eq_fold_predecessor_list`, `set_predecessor_list`).
> Deleting countability breaks the solver. It is also **unnecessary** for the
> frame-stack route (`com`/`pcom` are never declared countable; adding
> constructors doesn't touch `edge_action`). **Step 0 skipped.**
>
> **M3 solver wiring (green, 2026-06-06).** The handoff's "remaining for solver
> wiring" block is **closed** on `trace-spike`:
>
> - `src/Solver/TD_Side_Interface.thy` — `td_cfg_side_solver` locale; mono derived
>   from `tf_mono`; `side_part_post_solution_at` via `least_partial_post_solution`;
>   `side_analyse` / `side_env_at`.
> - `src/Solver/TD_Side_Soundness.thy` — `side_analyse_collect_sound_at_solver`,
>   `side_analyse_collect_sound_solver`, `side_solver_sound`, `side_sign_analysis_sound`
>   (entry coverage discharged from `s0` + `restrict_global s0 = bot`).
>
> **M3 witness still open:** no `Example_*` yet exercises `side_analyse` on a program
> with G-prefixed globals (optional quick win — see §9 slice 0).
>
> **Next milestone: M1** — wire `pcom` through CFG translation + interprocedural
> collecting + analysis. **Then:** M4 (digests / trace-combine). See §9.
>
> **Second plan correction (verified).** A flat `EA_Combine` CFG edge for
> procedure return is **not soundly abstractable** in the current domain
> framework. Its concrete locals-forgetting semantics (`locals -> top`) needs a
> top element, but the domains are `bounded_semilattice_sup_bot` (`Domains/
> Abstract_Domain.thy`) -- `sup`/`bot` only, **no `top`**. So the interprocedural
> combine cannot live on a flat CFG edge: the sound combine must keep the
> *caller's* abstract state (no top needed), which requires caller context --
> i.e. the constraint system reading the call-site state (side-effecting /
> TD_side, Phase 3) or the trace foundation (Phase 4), not `edge_action`.
> Conclusion: do **not** add `EA_Combine` as a flat unary `edge_action` (binary
> combine needs two sources). **Enter** may appear as a unary edge (`EA_Enter`) with
> `enter_abs`; **return** uses **combine triples** `(call, proc_exit, return)` plus a
> multi-`Query` RHS (see `docs/PROCEDURES_EXTENSION_PLAN.md` §9.2–§9.4), not a flat
> combine edge. Abstract combine at call boundaries reuses `restrict_combine` /
> `combine_states` (already in `TD_Side_CFG.thy` / `IMP2_Globals.thy`).
>
> Procedure operational substrate so far (`IMP2_Proc.thy`, green): pstep
> determinism, `pruns_to` (+ skip/assign), `pstep_PSKIP_stuck`,
> `combine_after_{local,global}_assign`, `pcall_global_increment`,
> `psteps_PSeq2` (sequencing lifts through the frame-stack step), plus
> `pruns_to` composition for seq/if/while and `pruns_to_determ`
> (runs are input/output functional).

> **Phase 3 started (green): side-effecting constraint construction.**
> `src/Solver/TD_Side_CFG.thy` builds the `'l + 'g` side-effecting constraint
> system on the vendored `TD_side` solver:
>
> - `restrict_local` / `restrict_global` split an abstract state by `is_global`
>   (`restrict_local_global_join` recovers the original).
> - `side_rhs_fold` / `make_side_rhs_tree`: per program point a strategy tree
>   that `QueryL`s each predecessor's local state, `QueryG`s the single global
>   unknown, applies the edge transfer, then `Side`-contributes the global
>   component and flows the local component on.
> - `side_cfg_T`: the resulting `eqsT` (local unknowns = program points; one
>   global unknown of type `unit`).
>
> The denotation + post-fixpoint of `side_cfg_T` are now proved (all green):
>
> - `side_acc` / `traverse_side_rhs_fold` / `eq_side_cfg_T` -- `eq` of the tree
>   is the local fold over predecessors.
> - `side_glob` / `sides_side_rhs_fold_{Inr,Inl}` -- the `Side` contributions
>   land entirely in the one global slot `Inr ()`.
> - `restrict_combine` -- `restrict_local A | restrict_global B` = abstract
>   combine.
> - `side_post_solution_le_local` / `_le_global` -- from a `part_post_solution`
>   of `side_cfg_T`, the two per-pp bounds: `side_acc ... <= sigma (Inl v)` and
>   `side_glob ... <= sigma (Inr ())`.
> - `apply_tf_combined_le` -- per-edge closure of the combined env.
> - **`side_collect_sound_path` / `side_collect_sound_at` (M3)** -- a
>   `part_post_solution` combined env soundly over-approximates `cfg_collect`
>   (path member and subset forms).
>
> **M4** (precise trace-combine / digest-indexed globals) is still open — M1
> collecting now exists; M4 is unblocked (§9 slice 5).

> **M1 slice 4 exit (green, 2026-06-07, branch `trace-spike`).** Non-recursive
> procedural witness end-to-end, sorry-free, full `isabelle build`:
>
> - `src/CFG/IMP2_Proc_to_CFG.thy` — `compile_prog`, enter edges + combine triples (CE1).
> - `src/CFG/Collecting/CFG_Collect_IP.thy` — `cfg_collect_ip` (interprocedural collecting).
> - `src/CFG/Collecting/CFG_Collect_IP_Adeq.thy` — L-adeq (`pruns_to_ip`, `pcall_global_increment`).
> - `src/Solver/TD_CFG_IP_Core.thy` — `make_rhs_tree_ip`, `ip_rhs_tree`, combine queries on plain TD.
> - `src/Solver/TD_IP_Soundness.thy` — `post_fixpoint_sound_at_ip`, `ip_sign_analysis_sound`.
> - `src/Examples/Example_Proc_Global.thy` — `inc_pi` / single `PCall ''p''`; sign via `td_analyse_ip`.
> - `src/Examples/Example_Side_Global.thy` — M3 witness (TD_side on G-prefixed globals).
> - `ROOT` — registers `TD_IP_Soundness`, `Example_Proc_Global`, `Example_Side_Global`.
>
> Design notes for the IP example: initial state `(λ_. STop)` (not `bot`); return
> semantics via **combine triples** at the exit PP, not edge-only paths.
>
> **Next:** merge `trace-spike` → `main` (§5 gate met); then **unified analysis
> migration** (`docs/UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md`, recommended before M4);
> then **M4** (§9 slice 5). Optional: recursive Example 2 (factorial), interval IP example.

---

## Milestone checklist (branch `trace-spike`, updated 2026-06-07)

| Milestone | Status | Notes |
| --- | --- | --- |
| **M0** — lift lemma | **Done** | `CFG_Trace_Collect.thy` |
| **M2** — trace soundness via `alpha_last` | **Done** | `Trace_Soundness.thy`, `Example_Trace_NonTerminating.thy` |
| **M3** — TD_side theory + solver soundness | **Done** | `TD_Side_CFG` / `Interface` / `Soundness` |
| **M3 witness** — concrete global example | **Done** | `Example_Side_Global.thy` |
| **M1** — procedures end-to-end | **Done** | §9 slices 1–4; `Example_Proc_Global.thy` |
| **U1–U4** — unified analysis migration | **Done** (2026-06-09) | `docs/UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` |
| **M3.5** — interprocedural **trace** bridge | **Done** (core) | projection lemma green; `CFG_Trace_Collect_IP.thy` |
| **M4** — globals over traces (digests) | **Open** | needs M3.5 Slice 1 (action-labelled trace) — §9 slice 5 |

Migration is **substantially complete**: the unified-analysis consolidation (U1–U4)
and the M3.5 interprocedural-trace projection are green on `trace-spike`. **M4**
(history-sensitive globals over reaching traces / digests) is the remaining
research frontier; its locale extension point is proved (U4
`trace_ip_analysis_sound`). (§5 build gate passed 2026-06-09.)

> **Progress (2026-06-09) — consolidation + M3.5 projection green.**
> Full `isabelle build` sorry-free. New theories: `CFG_Collect_Unified` (U1),
> `Analysis_Sound` (U2), `Trace_IP_Analysis_Sound` (U4), `CFG_Trace_Collect_IP`
> (M3.5). M3.5 milestone:
> `alpha_last (cfg_collect_trace_ip g S v) \<subseteq> cfg_collect_ip g S v`
> (`ip_trace_witness`; enter = edge step, combine = junction splice with
> `combine_states` restore). Composed to analyzer soundness over interprocedural
> trace semantics in `trace_ip_analysis_sound`.
>
> **Remaining for M4:** (a) M3.5 Slice 1 — enrich `trace` to
> `(edge_action \<times> store) list` so "last preceding write to a global" is statable
> (re-close `lift`); (b) M3.5 Slice 4 — single-context equality witness on
> `Example_Proc_Global` (adequacy / reverse inclusion); (c) the digest-indexed
> global-read transfer + its soundness below the U4 projection.

---

## 1. Mission in one paragraph

Re-base the concrete semantics from **reachable states** onto **traces** so that
flow-insensitive globals become expressible and provable. The repo is *already
path-based* (`cfg_collect_paths` enumerates CFG paths); only one fold throws away
history. The whole pivot hinges on one lemma — the **lift lemma**
`cfg_collect = α_last(cfg_collect_trace)` — which lets every existing numeric-domain
proof (sign/interval/parity) compose **unchanged** through the projection. Prove that
lemma first (Phase 0). Everything else waits on it.

## 2. Orientation — the one fact that makes this feasible

The collecting semantics is built on **enumerated edge paths**. In
`src/CFG/Collecting/CFG_Collecting_Core.thy`:

```
cfg_collect_paths g S v = (UN es : {es. g |- cfg_entry g ->[es] v}. edges_collect es S)
```

`es` is an explicit edge list — the **control-flow history is already first-class**.
What discards the *data* history is the fold in
`src/CFG/Collecting/CFG_Edges_Collect.thy`:

```
fun edges_collect :: "(edge_action * pp) list => store set => store set" where
  "edges_collect [] S = S"
| "edges_collect ((a, _) # es) S = edges_collect es (edge_collect a S)"   (* keeps only FINAL stores *)

type_synonym cenv = "pp => store set"     (* reachable states per point — history flattened *)
```

So the migration **enriches an existing layer** rather than rebuilding it. The trace
switch records the *sequence* of stores instead of only the last.

---

## 3. Phase 0 — Trace spike + lift lemma (THE GATE) — start here

**Objective.** On a throwaway branch, define a trace-valued collecting next to the
existing one and prove the lift lemma. One lemma decides whether the foundation swap
is a few weeks or a rewrite. **Go/no-go for the whole pivot (milestone M0).**

**Branch:** `trace-spike` off `main`.

**Suggested shape (refine as you see fit — do not over-commit the encoding):**

```
type_synonym trace = "(pp * store) list"          (* or plain `store list` if that suffices for the lemma *)

(* single-store step along one path; None when an EA_Assume filters the store out *)
(* build the trace of stores visited along an edge path from one start store *)
fun edges_trace :: "(edge_action * pp) list => store => trace option"

(* trace-valued collecting, mirroring cfg_collect_paths *)
definition cfg_collect_trace :: "cfg => store set => pp => trace set"

(* projection: last store of each trace *)
definition alpha_last :: "trace set => store set"
```

**Target lemma (the load-bearing one):**

```
lemma lift:  "alpha_last (cfg_collect_trace g S v) = cfg_collect_paths g S v"
```

Mirror the proof skeleton of the existing `cfg_collect_le_paths` /
`cfg_collect_witness` in `CFG_Collecting_Core.thy` — the **path skeleton is unchanged**;
you are threading a sequence through where a single final store used to flow. The
key reusable facts: `edges_collect_append`, `edges_collect_member`,
`cfg_collect_paths_step`.

**Exit / M0:**

- `lift` proved, **sorry-free**, building green (§5).
- *Or* a concrete obstacle identified and written up in the KB
  (`seidl-pivot-migration-plan.md` §"First concrete step"). Either outcome is a
  valid decision gate — do **not** proceed to Phase 2 work until M0 is green.

**Do not** touch `Domains/`, `Equations/`, `Pipeline/` in Phase 0. The spike is
confined to `src/CFG/Collecting/`.

---

## 4. Phase 1 — IMP2 vendor-trim (parallel, independent of Phase 0)

Adds **procedures + global variables** to the language. Independent of the trace
work — can run in parallel or after M0. Full shape + rationale:
`seidl-pivot-migration-plan.md` §"Phase 1 vendor-trim" and `imp2.md` §"Why vendor-trim".

**Decision already made (do not re-litigate):** **vendor-trim, not `imports
IMP2.Semantics`.** Keep this repo's deep-embedded `aexp`/`bexp` and scalar
`store = vname => int`. Graft only IMP2's *command/procedure* layer. The full-import
alternative was weighed and rejected (it gives a precision-less ⊤-everywhere abstract
evaluator unless you rebuild a deep embedding by hand) — see the KB §"Considered &
rejected — full import" before reopening this.

**Step 0 — delete countability first. ~~SUPERSEDED — do not do.~~** Verified on
`trace-spike`: the `edge_action` linorder (from countability) is load-bearing for
`cfg_edges_list` → `predecessor_list` → TD solver core. Removing it breaks the
solver and is unnecessary for the additive `pcom` route. See progress block above.

**Keep (unchanged):** deep `aexp`/`bexp`, `store = vname => int`, the small-step shape,
`runs_to`, and the whole CFG/collecting/domain/soundness spine.

**Graft (port IMP2 → scalar store; their proofs are the template):**

```
definition is_global :: "vname => bool" where "is_global x = (x ~= [] & hd x = CHR ''G'')"
definition combine_states :: "store => store => store"   (* <s|t>: locals from s, globals from t *)
  where "combine_states s t n = (if ~ is_global n then s n else t n)"
(* + combine_collapse / combine_nest / combine_query / combine_upd / combine_cases — all `by auto` *)

datatype com = SKIP | Assign vname aexp | Seq com com | If bexp com com | While bexp com
  | Scope com | PCall pname          (* pname = string; com stays countable *)
```

**Drop:** arrays (`Vidx`/`AssignIdx`/`ArrayCpy`/`ArrayClear`) **and** the
function-carrying `PScope "pname ~=> com" com` / `Assign_Locals "vname => val"`.
`PScope` (nested local procedure environments) is unneeded for a monovariant analysis
with one global procedure table `pi :: pname ~=> com` passed as a parameter.

**Return-on-`Scope` — pick one (settle during Phase 1):**

1. *Frame stack in the small-step config* (recommended, self-contained):
   `com * store * frame list`; `Scope` pushes a restore-locals frame, `Return` pops
   and restores via `combine_states`. Keeps `com` countable; restore lives in the
   machine state, not the syntax.
2. *Push calls to the CFG layer*: leave command small-step procedure-free; introduce
   `enter`/`combine` (call/return) edges in `IMP2_to_CFG.thy` and handle call/return
   soundness in the path-based collecting. Leaner, but couples procedure semantics to
   the CFG translation.

**Three senses of "global" — keep them distinct** (this trips people up):

- **Level 1 — global *variables*** (G-prefixed, persist across `Scope`): **this phase**.
- **Level 2 — global *unknowns*** (`pp => 'l + 'g`, side-effecting): Phase 3.
- **Level 3 — globals over *reaching traces*** (join, digest-indexed): Phase 4.

This phase delivers Level 1 only; it is the prerequisite for 2 and 3.

**Files:** `src/IMP2/IMP2_Syntax.thy` (add `Scope`/`PCall`, `is_global`,
`combine_states`; remove `countable` per Step 0), `src/IMP2/IMP2_SmallStep.thy`
(frame stack + clauses + `runs_to` bridge), `src/CFG/CFG_Def.thy` /
`src/CFG/IMP2_to_CFG.thy` (call/return edges; recheck `edge_action` needs no order
once countability is gone). `Collecting`/`Domains`/`Equations`/`Pipeline` **untouched**.

**Effort:** ~150–250 LOC. **Exit / M1:** a non-recursive then recursive procedural
example compiles to a CFG and analyzes end-to-end with the existing interval domain,
scalar store, **sorry-free** — *state-based, before traces*.

---

## 5. Build & verification gate (non-negotiable)

```bash
isabelle build -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization
```

- Run `make vendor` first if `vendor/td-verification` is missing.
- **A change is "done" only when the full `isabelle build` is green** (or shows
  *exactly* the expected sorries). The interactive I/Q checker passing is not enough.
  This matches the `isabelle-verify` discipline.
- `.thy` files: **ASCII symbols only** (`\<Longrightarrow>`, not the unicode arrow) —
  batch rejects unicode. (This markdown doc uses lighter pseudo for readability;
  ASCII-ize when you write the actual theory.)
- `sorry` in a batch build needs `options [quick_and_dirty]` in `ROOT`.
- Full build & MCP traps: `docs/ISABELLE_AGENT_NOTES.md`. Project rules: `AGENTS.md`.

## 6. Constraints — what NOT to do

- **Do not flip locked ADs.** The pivot supersedes AD-1/2/3/4/5 + AD-27 and resolves
  AD-28/29 — but **only as each phase lands**, never ahead of the code. Append a
  superseding row when a phase is green; never rewrite an old row. See the KB AD
  ledger and `seidl-pivot-migration-plan.md` §"ADR actions".
- **Do not touch the solver layer.** TD / TD_side (`vendor/td-verification`,
  `src/Solver/`), per-pp solve (AD-16), the vendored-solver pattern (AD-13) all
  survive untouched. This is a foundation-and-frontend swap, not a solver rewrite.
- **Do not `imports IMP2.Semantics`** (see §4). Keep the deep expressions.
- **Do not start Phase 4 (globals over traces) before M0 + M3.** Globals can only be
  proved sound once the concrete semantics is strong enough to *state* the property
  ("semantics stronger than analysis").
- **Phase 0 stays in `src/CFG/Collecting/`.** Resist refactoring the domain or
  pipeline layers during the spike — that risk is what M0 exists to retire first.

## 7. Sequencing / milestones

```
Phase 1 (IMP2 vendor-trim) ──┐  (independent, parallel)
                             ├─► Phase 3 (split 'l+'g + TD_side) ─► Phase 4 (globals/digests)
Phase 0/2 (trace + lift) ────┘            ▲
        (THE GATE) ───────────────────────┘
```

- **M0** — `lift` proves (Phase 0). **Done.**
- **M2** — all existing examples pass via `alpha_last`, sorry-free (Phase 2). **Done**
  (additive; spine untouched).
- **M3** — flow-insensitive globals via TD_side (Phase 3). **Done** (proofs +
  `Example_Side_Global.thy` witness).
- **M1** — IMP2 procedural example analyzes end-to-end, state-based, sorry-free
  (Phase 1). **Done** (`Example_Proc_Global.thy`, 2026-06-07).
- **M4** — history-sensitive global read proved sound (Phase 4). **← current focus**
  (§9 slice 5); M1 collecting + trace foundation are in place.

After M0, Phase 2 generalizes the spike across the rest of `CFG/Collecting/*` and lifts
the domain interface through `alpha_last` — full file list in
`seidl-pivot-migration-plan.md` §"Phase 2".

## 8. First action (historical — M0 complete)

M0 gate passed on `trace-spike`. M1 slice 4 passed 2026-06-07. **Start at §9**
for merge / M4.

---

## 9. Next steps — M1 done; merge and M4

**Companion:** `docs/PROCEDURES_EXTENSION_PLAN.md` §9 (thesis-scoped interprocedural
plan; CE1–CE4 lemma names). The two layers compose:

| Layer | Mechanism | Status |
| --- | --- | --- |
| Flow-insensitive **global variables** (`Gx`, …) | `TD_side` + `restrict_local` / `restrict_global` | M3 **done** (`Example_Side_Global`) |
| **Call/return** (locals preserved, globals merged) | `combine_states` / `restrict_combine` + combine triples | M1 **done** (`Example_Proc_Global`) |

Do **not** reopen: countability deletion (§4 Step 0), flat `EA_Combine` edges.

### Slice 0 — M3 witness — **Done**

- `src/Examples/Example_Side_Global.thy` — plain `com` with G-prefixed assigns;
  `side_sign_analysis_sound` discharged. Registered in `ROOT`.

### Slice 1 — `compile_prog` (CE1, additive) — **Done**

New theory; **do not rewrite** `IMP2_to_CFG.thy` / `to_cfg` (spine stays green).

**File:** `src/CFG/IMP2_Proc_to_CFG.thy` (name flexible).

**Input:** `proc_table` + main `pcom`.

**Output:** whole-program `cfg` plus auxiliary relations:

- one sub-CFG per procedure body (reuse `compile` pattern from `IMP2_to_CFG.thy`);
- **enter edges** `(call_site, EA_Enter, proc_entry)` per call site;
- **combine triples** `(call_site, proc_exit, return_site) ∈ combines g` — **not**
  a flat `edge_action` (see plan correction above).

**First proof targets:** freshness, counter monotonicity, `finite (edges g)`,
`finite (combines g)` — mirror existing `compile_*` lemmas.

**Do not** prove soundness in this slice.

Delivered in `src/CFG/IMP2_Proc_to_CFG.thy`.

### Slice 2 — interprocedural collecting — **Done**

**File:** `src/CFG/Collecting/CFG_Collect_IP.thy` (or locale in a sibling).

Extend collecting with a combine clause (concrete semantics from
`PROCEDURES_EXTENSION_PLAN.md` §9.2):

```
cfg_collect_ip g S v = lfp F  where
  F C v = … edge_collect on intra/enter edges …
        ∪ { combine_states s t | (c, ex, v) ∈ combines g, s ∈ C c, t ∈ C ex }
        ∪ (if v = entry then S else {})
```

Reuse `combine_states` from `IMP2_Globals.thy`.

**First proof target:** operational adequacy for the non-recursive example
(`pruns_to` ⟹ member of `cfg_collect_ip` at return sites) — **L-adeq** shape from
§9.4. Path-based version can follow the existing `cfg_collect_paths` skeleton.

Delivered in `CFG_Collect_IP.thy` + `CFG_Collect_IP_Adeq.thy`.

### Slice 3 — abstract RHS + soundness (L-sound') — **Done**

Wire combine into the constraint system. Two compatible routes (pick one per slice;
both may coexist):

1. **Plain TD + `rhs_ip`** — `make_rhs_tree` emits multi-`Query` at combine nodes;
   `combine_abs` = `restrict_combine` on abstract states. See §9.3–§9.4 in the
   procedures plan. Extends existing `TD_CFG_Core` / `post_fixpoint_sound`.
2. **TD_side at intra edges + combine queries** — reuse M3 trees for flow-sensitive
   locals/globals inside bodies; combine nodes pull call-site + callee-exit via
   `QueryL`/`QueryG`.

**Load-bearing lemmas:** L-enter, L-comb (pointwise γ), L-sound' (one new union
case over existing `post_fixpoint_sound`), per-pp L-td' (already Fix B:
`td_analyse_collect_sound_at` / `side_analyse_collect_sound_at_solver`).

Route taken: plain TD + `rhs_ip` (`TD_CFG_IP_Core`, `TD_IP_Soundness`,
`Constraint_System_IP_Sound.thy`).

### Slice 4 — first end-to-end example (M1 exit) — **Done**

**Example 1** from `PROCEDURES_EXTENSION_PLAN.md` §9.6 (non-recursive, global effect,
locals preserved):

```
global Gx;   proc inc() { Gx := Gx + 1; }
main() { local x;  x := 5;  inc();  inc(); }
```

Operational witness in `IMP2_Proc.thy` (`pcall_global_increment`) + adequacy in
`CFG_Collect_IP_Adeq.thy`. Soundness: `proc_global_sign_analysis` in
`Example_Proc_Global.thy` via `td_analyse_ip`. Batch green 2026-06-07.

**Optional follow-up:** recursive Example 2 (factorial) — same machinery, widening
unchanged.

### Slice 5 — M4 — **after M3.5** (and unified migration)

History-sensitive globals over **reaching traces** (digest-indexed join). Requires the
**interprocedural _trace_ collecting** `cfg_collect_trace_ip` — that is **M3.5**
(`docs/M3_5_INTERPROC_TRACE_HANDOFF.md`), not the state-based `cfg_collect_ip` — so the
"last preceding write over reaching traces" property is even statable. Prerequisites
M0 + M3 + M1 collecting are in place; **M3.5 is the missing one (§6).**

**Sequence:** `docs/UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` (U1–U2) → M3.5 → M4, so each
lands as a locale interpretation, not a fifth parallel stack.

### What not to do next

| Skip | Reason |
| --- | --- |
| Delete countability | Breaks TD solver |
| Flat `EA_Combine` on edges | Binary combine; needs caller context |
| Destructive Phase 2 spine rewrite | M2 already closed additively via `alpha_last` |

**Recommended next integration step:** consolidate (`UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md`
U1–U2), then **M3.5** (`M3_5_INTERPROC_TRACE_HANDOFF.md`). Merging `trace-spike` → `main`
is optional and orthogonal (M1 slice 4 green; §5 gate passed 2026-06-07).

### M1 file map (delivered)

```
src/CFG/IMP2_Proc_to_CFG.thy           -- compile_prog; enter + combines (CE1)
src/CFG/Collecting/CFG_Collect_IP.thy  -- cfg_collect_ip
src/CFG/Collecting/CFG_Collect_IP_Adeq.thy -- L-adeq witness
src/Equations/Constraint_System_IP_Sound.thy -- IP constraint soundness
src/Solver/TD_CFG_IP_Core.thy          -- make_rhs_tree_ip / rhs_ip bridge
src/Solver/TD_IP_Soundness.thy         -- post_fixpoint_sound_at_ip
src/Examples/Example_Proc_Global.thy   -- §9.6 Example 1 (M1 exit)
src/Examples/Example_Side_Global.thy   -- M3 witness (slice 0)
ROOT                                   -- TD_IP_Soundness, Example_* registered
```
