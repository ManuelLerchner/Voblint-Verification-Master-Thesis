# Handoff — M3.5: Interprocedural Trace Bridge (`enter`/`combine` on traces)

Scoped pick-up doc for **one milestone**: lift the trace collecting to procedures and
prove it projects onto the existing state-based interprocedural collecting. This is the
missing product of M2 (traces, intraprocedural) and M1 (procedures, state-based), and the
real prerequisite for M4 (globals over reaching traces). **Do M3.5 only — not M4.**

KB companions (read for *why*):

- `~/git/voblint-formalization-kb/wiki/meetings/2026-06-05-meeting5.md` — the `enter`/`combine`
  specification (§A trace type, §C edge transformer, §D `enter`, §E `combine`, §F projection).
- `~/git/voblint-formalization-kb/wiki/concepts/trace-semantics.md` §"Representation" — the
  Cousot-decided trace encoding (state sequence + optional action label; **junction** composition).
- `~/git/voblint-formalization-kb/wiki/concepts/improving-thread-modular-ai.md` §3 — Schwarz's
  `new` / binary `lock` / `sink`/`loc`/`last`; the `enter`≈`new`, `combine`≈binary-`lock` mapping.
- `~/git/voblint-formalization-kb/wiki/research/seidl-pivot-migration-plan.md` §"Phase 3.5" — the plan row.
- `docs/UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` — **do U1–U2 first** (see §2); U4 is the trace-overlay hook M3.5 fills.
- `docs/SEIDL_TRACE_MIGRATION_HANDOFF.md` — parent pivot status (M0–M3 + M1 done).

> Status (2026-06-09): **Slices 2–3 done, green.** Branch `trace-spike`.
> Consolidation U1–U4 landed first (see `UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md`),
> then M3.5: `src/CFG/Collecting/CFG_Collect_Trace_IP.thy` defines
> `cfg_collect_trace_ip` (`ip_trace_witness`: entry / edge / junction-combine) and
> proves the milestone projection
> `alpha_last (cfg_collect_trace_ip g S v) \<subseteq> cfg_collect_ip g S v`
> (`alpha_last_cfg_collect_trace_ip_le`). Composed to analyzer soundness over the
> interprocedural trace semantics in `Trace_IP_Analysis_Sound.thy`
> (`trace_ip_analysis_sound`, U4). Built on the unified `collecting` locale
> (`cfg_collect_ip = ip.collect`), not a fifth parallel stack. **Open:** Slice 1
> (enrich `trace` to action-labelled for M4), Slice 4 (single-context equality
> witness). Full `isabelle build` sorry-free.

---

## 1. Mission in one paragraph

M2 lifted the *intraprocedural* collecting to traces (`cfg_collect_trace`, `alpha_last`,
`lift`). M1 added procedures *state-based* (`cfg_collect_ip` over `store set`, with
`combine_states <s|t>` at combine triples). M3.5 forms their product: a **trace-valued
interprocedural collecting** `cfg_collect_trace_ip` whose `enter`/`combine` operate on
*traces*, and the **interprocedural projection lemma**

```
alpha_last (cfg_collect_trace_ip g S v)  ⊆  cfg_collect_ip g S v       (* REFINEMENT, not equality *)
```

**Why ⊆ and not =.** The existing `cfg_collect_ip` *over-combines*: `collect_combine_pp`
(`CFG_Collect_IP.thy:17`) pairs **every** `s ∈ rho call` with **every** `t ∈ rho exit`,
including caller/callee states that never co-occurred on a real run. The trace `combine`
only splices a callee trace with the caller it actually returned to (same calling-context
prefix, §4), so it is **strictly more precise** — equality holds only when each procedure
has a single calling context (e.g. the non-recursive witness). The ⊆ direction is exactly
what we want: it lets M1's soundness (`analysis ⊒ cfg_collect_ip`) carry to the trace
foundation by transitivity (`analysis ⊒ cfg_collect_ip ⊇ alpha_last(cfg_collect_trace_ip)`),
*and* the strict cases are the precision payoff of the pivot. (Intraprocedurally there is
no combine, so M0's `lift` stays an equality; ⊆ becomes strict only at combine/return pps.)

That is the whole milestone. It unblocks M4 because a global's "last preceding write over
reaching traces" is only *statable* once reaching traces cross calls.

---

## 2. Sequencing — consolidate first (hard gate)

**Do `UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` U1 + U2 before writing M3.5 proofs.**
Reason: M3.5 built additively would be the *fifth* parallel collecting/soundness stack —
exactly the debt the unified migration exists to remove. After U1/U2 the trace-IP
collecting lands as a **`collecting_trace` interpretation** of the one collecting locale,
with `enter`/`combine` supplied as the locale's `combine_at` hook (U4 is the slice that
opens that hook).

```
U1 (collecting locale: intra + ip interpretations)
U2 (soundness locale: plain/side/ip corollaries)   <-- GATE: both green
        |
        v
M3.5  = collecting_trace interpretation
        + combine_at := junction-then-combine_states
        + interprocedural lift lemma
        |
        v
M4 (digests / globals over reaching traces)
```

If U1/U2 slip, the fallback is to build `cfg_collect_trace_ip` additively and refactor it
into the locale later — **but that re-incurs the debt; prefer the gate.**

---

## 3. What exists — reuse, do not rebuild

| Artifact | File | Role in M3.5 |
| --- | --- | --- |
| `cfg_collect_trace`, `alpha_last`, `lift` | `CFG/Collecting/CFG_Collect_Trace.thy` | intraprocedural template; `alpha_last` is the projection |
| `cfg_collect_ip` (state-based) | `CFG/Collecting/CFG_Collect_IP.thy` | the **projection target** of the new lift |
| `combine_states <s|t>` + algebra | `IMP2/IMP2_Globals.thy` | the `restore` in `combine` (locals from caller, globals from callee) |
| `pstep` / `pruns_to` / determinism | `IMP2/IMP2_Proc.thy` | the small step each trace step reuses; adequacy witness |
| `compile_prog`, enter edges, `combines g` triples | `CFG/IMP2_Proc_to_CFG.thy` | the CFG structure `enter`/`combine` thread through |
| path-enumeration skeleton | `CFG/Collecting/CFG_Collect_Core.thy` | `cfg_collect_trace_ip` mirrors its lfp/path proofs |

**~80% of the substrate is here.** M3.5 is new *glue*, not a new foundation.

---

## 4. The spec (from meeting 5 + Cousot)

### Trace type — enrich `store list` to carry the action

Cousot's base trace is a **state sequence** (actions optional); `store list` is its
action-free abstraction, enough for `last` and therefore for M2's lift. M3.5/M4 need the
**last preceding write** to a global identifiable, so enrich:

```
type_synonym trace = "(edge_action * store) list"   (* or (pp * store) list + edge lookup *)
(* meeting-5 §A: Q × (Edge × Q)*, Q = (pp, store).  Keep the START state + per-step (edge, state). *)
```

Keep `alpha_last` = last store of the sequence; the existing `lift` proof should re-close
modulo the added action component (it never inspects it).

### Composition is junction, not concatenation (Cousot §4.3)

Two traces join iff the **last state of one = first state of the next**; the join
*overlaps* that shared boundary state. `enter`/`combine` are junctions:

```
enter f t   = t ⌢ <call-edge step into f's entry, locals reset to INIT>   (* set-valued: input nondet *)
combine f T R = { junction(tau, rho) then restore-locals
                | tau in T (caller, at call site),
                  rho in R (callee summary, at proc exit),
                  rho extends tau (SAME calling-context prefix) }       (* see below *)
restore = combine_states (last tau) (last rho)   (* caller locals, callee globals + return *)
```

`cfg_collect_trace_ip` is then an `lfp` of the **Theorem-11 shape** `base ∪ (step ⌢ X)` —
identical skeleton to `cfg_collect_paths`, so reuse `edges_collect_append` /
`_member` / `cfg_collect_paths_step`-style lemmas.

### The same-prefix combine is CORRECTNESS, not precision

Concretely each return trace `rho` already carries its own caller prefix (it was built by
`enter`-ing from one `tau`), so `combine` matches by **identity of the prefix**. A
foreign-caller splice produces a trace that never ran -> the lift lemma would be
**unsound**, not merely imprecise. So this is a definitional constraint on `combine`,
*not* a context-sensitivity knob. (Context-sensitive *summaries* are the analysis layer =
M4 / a later milestone, not M3.5.) Template: Schwarz §3 Theorem 1 lock-compatibility
(`last(t1) = unlock(a)`) is the concurrent analog of "same calling-context prefix."

---

## 5. Slices (each exits sorry-free, full `isabelle build`)

### Slice 1 — trace type + intraprocedural re-close
- Enrich `trace` to `(edge_action * store) list` in `CFG_Collect_Trace.thy`.
- Re-close `edges_trace`, `cfg_collect_trace`, `alpha_last`, and **`lift`** over the new type.
- **Exit:** intraprocedural `lift` green on the enriched type; no regression in `Trace_Soundness` / `Example_Trace_*`.

### Slice 2 — `cfg_collect_trace_ip`
- Define the trace-valued interprocedural collecting (junction-based `enter`/`combine`,
  `combine_states` for restore), mirroring `cfg_collect_ip`'s lfp.
- **Exit:** definition + basic lemmas (monotone RHS, `finite` side-conditions, path/junction append).

### Slice 3 — interprocedural projection lemma (the milestone)
- Prove `alpha_last (cfg_collect_trace_ip g S v) ⊆ cfg_collect_ip g S v` (refinement; see §1).
- Strategy: induct on the lfp / path skeleton; intra/`enter` pps give equality (reuse the
  M0 `lift` argument), the **combine/return pp** gives the ⊆ step — every matched
  `combine_states (last tau) (last rho)` is also produced by the over-combining
  `collect_combine_pp` (witness `s = last tau ∈ rho call`, `t = last rho ∈ rho exit`).
  Discharge via `combine_states` algebra + `edges_collect_append`/`_member`; numeric
  content factors through `alpha_last`.
- **Optional (precision win):** show strict `⊊` on a 2-call-site example — the thesis evidence
  that traces beat the state collecting. Not required for the milestone.
- **Exit:** ⊆ lemma green, sorry-free.

### Slice 4 — witness
- Reuse the M1 example (`Example_Proc_Global`, `inc()`/`Gx`): show its reaching traces
  project (`alpha_last`) to the IP collecting at the return site. This example has a
  **single calling context**, so here the ⊆ is an **equality** — a sanity check that the
  refinement is tight when there is no cross-context over-combination.
- **Exit:** `alpha_last (cfg_collect_trace_ip …) = cfg_collect_ip …` for this example, green.

**Definition of done (M3.5):** Slice 3 lemma green on `trace-spike`, full `isabelle build`
sorry-free, no regression; built as a `collecting_trace` interpretation (post-U1/U2), not
a new parallel stack.

---

## 6. Build gate (non-negotiable)

```bash
isabelle build -v -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

- "Done" = full batch green (or exactly the expected sorries with `quick_and_dirty`).
  Interactive I/Q is **not** enough (matches `isabelle-verify`).
- `.thy`: **ASCII symbols only** (`\<Longrightarrow>`, not unicode). Traps: `docs/ISABELLE_AGENT_NOTES.md`.

---

## 7. Constraints — what NOT to do

| Don't | Why |
| --- | --- |
| Start M4 (digests / global read) here | M3.5 is the *prerequisite*; keep it separate and reviewable |
| Build `cfg_collect_trace_ip` as a 5th parallel stack | Do U1/U2 first; land it as a locale interpretation |
| Make `combine` match across calling contexts | Concretely unsound — same-prefix is identity (§4) |
| Add context-sensitivity / digest indexing | That is the analysis layer (M4 / meeting-5 Milestone 4), not the concrete bridge |
| Touch the vendored TD / TD_side solver | AD-13; bridge only |
| Flat `EA_Combine` edge | Binary combine needs caller context (see Seidl handoff plan correction) |

---

## 8. First action

Confirm U1/U2 status (`UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` §5 checklist). If green,
start Slice 1. If not, do U0→U2 first, or take the documented additive fallback (§2) only
with eyes open. Then keep the KB plan (`seidl-pivot-migration-plan.md` §Phase 3.5) and
this doc in sync as slices land.
