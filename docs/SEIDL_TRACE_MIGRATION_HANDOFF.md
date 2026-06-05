# Handoff — Start the Seidl Trace Migration

Pick-up doc for an agent starting the **trace-semantics pivot** in this repo. Read
this top-to-bottom once, then start at **§3 (Phase 0 — the gate)**. The deep
reasoning lives in the KB; this doc is the actionable extract.

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

> Status when written (2026-06-05): planning complete, **no proof-repo code changed
> yet**. Branch `main` is sorry-free. This doc is the first executable step.

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
> **Remaining for M1:** wire `pcom` through the CFG translation, then
> collecting + pipeline, for an end-to-end procedural example.
> **Then:** M3 (TD_side globals), M4 (digests).
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
> Conclusion: do **not** add `EA_Enter`/`EA_Combine` to `edge_action`; handle
> call/return at the constraint-system / trace layer instead.
>
> Procedure operational substrate so far (`IMP2_Proc.thy`, green): pstep
> determinism, `pruns_to` (+ skip/assign), `pstep_PSKIP_stuck`,
> `combine_after_{local,global}_assign`, `pcall_global_increment`,
> `psteps_PSeq2` (sequencing lifts through the frame-stack step).

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

**Step 0 — delete countability first.** Its only consumers are the `to_nat`-derived
order on `edge_action` (`src/CFG/CFG_Def.thy:63`) and `code_pred small_step`
(executability) — neither is soundness. Remove the `instance ... :: countable`
declarations, the `to_nat`-based `<=`/`<` on `edge_action`, and `code_pred`. This
unblocks free experimentation; deep expressions hand countability back for free later
if wanted.

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

- **M0** — `lift` proves (Phase 0). *Go/no-go for the whole pivot.* ← **your first target**
- **M1** — IMP2 procedural example analyzes, state-based, sorry-free (Phase 1).
- **M2** — all existing examples pass via `alpha_last`, sorry-free (Phase 2). The hard one.
- **M3** — first monovariant global, flow-insensitive via TD_side (Phase 3).
- **M4** — a history-sensitive global read proved sound (Phase 4). The thesis payoff.

After M0, Phase 2 generalizes the spike across the rest of `CFG/Collecting/*` and lifts
the domain interface through `alpha_last` — full file list in
`seidl-pivot-migration-plan.md` §"Phase 2".

## 8. First action

Create branch `trace-spike`, copy `CFG_Edges_Collect.thy`'s fold into a trace-valued
sibling, and attempt **`lift`**. Report green or the obstacle. Nothing else starts
until M0.
