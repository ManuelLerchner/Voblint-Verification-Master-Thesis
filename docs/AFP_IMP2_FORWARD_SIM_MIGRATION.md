<!-- markdownlint-disable-file MD025 -->

# Migration: forward simulation to AFP IMP2 + operational adequacy

Status: **NOT STARTED** (2026-06-28). Follow-up to
`docs/AFP_IMP2_REBASE_MIGRATION.md` (Phases 1–3 **done**, `backward_sim`
batch-green). This doc tracks the **open** directions: completing the IMP2
bridge bidirectionally and grounding `cfg_collect` on `pruns_to`.

Related: `docs/AFP_IMP2_REUSE_DECISION.md`, `docs/PROCEDURES_EXTENSION_PLAN.md`
(§9.4 **L-adeq**), `src/IMP2/IMP2_Bridge.thy`, `src/IMP2/IMP2_Proc.thy`,
`src/CFG/Collecting/CFG_Collect_Runs.thy`.

---

## Goal

Close two gaps in the operational story that the analyzer pipeline currently
*assumes* but does not prove:

1. **Forward IMP2 bridge (Track A):** every terminating run of our frame-stack
   small-step semantics (`pruns_to`) corresponds to an AFP IMP2 big-step run of
   the translated program (read back through `proj0` / `embed`).
2. **CFG operational adequacy (Track B):** every terminating AST run
   (`pruns_to`) is witnessed by the compiled CFG collecting semantics at exit
   (`cfg_runs_to`).

Together with the existing **`backward_sim`** (IMP2 → `pruns_to`), Track A
yields **bidirectional equivalence** on terminating source programs. Track B
links the AST-level operational semantics to the CFG spec the analyzer is
actually proved against.

---

## What is already done

| Item | Where | Statement |
| --- | --- | --- |
| Expression agreement | `IMP2_Bridge.thy` | `aval_to_imp2_sim`, `bval_to_imp2_sim` under `proj0 S = s` |
| State split agreement | `IMP2_Bridge.thy` | `is_global_eq`, `proj0_combine_states`, `proj0_null_combine` |
| Translation | `IMP2_Bridge.thy` | `to_imp2_com`, `to_imp2_pi`, `source_com`, `source_pi` |
| **Backward simulation** | `IMP2_Bridge.thy` | `backward_sim`: IMP2 `big_step` ⟹ `pruns_to` |
| Frame-stack infrastructure | `IMP2_Proc.thy` | `pstep_frame_extend`, `pruns_to_Scope`, `pruns_to_Call`, `pruns_to_Scope_Call`, … |
| Entry semantics aligned (route 2b) | `IMP2_Proc.thy`, `IMP2_Globals.thy` | `Scope`/`Call` zero locals on entry via `enter_state`; matches IMP2 `SCOPE` |
| VCG pull-back example | `IMP2_VCG_Example.thy` | `count_via_imp2_vcg` composes IMP2 VCG + `backward_sim` |

---

## What this buys (and what it does not)

### Track A — forward IMP2 (`pruns_to` ⟹ `big_step`)

| Buys | Does not buy |
| --- | --- |
| **No spurious runs:** our semantics does not admit terminating behaviors IMP2 rejects | New analyzer soundness the top-level theorem (pipeline already sound vs `cfg_collect`) |
| **Bidirectional bridge:** `backward_sim` + forward ⟹ operational equivalence on terminating source programs | Coverage of diverging / partial runs (big-step is vacuous there by design) |
| Stronger thesis sentence: "equivalent to AFP IMP2 on terminating programs" | Array programs (still scalar-only; see `docs/ARRAY_SYNTAX_EXTENSION.md`) |
| Optional reverse VCG route (`pruns_to` proof ⟹ IMP2 wp) | Executable analyzer changes |

### Track B — CFG adequacy (`pruns_to` ⟹ `cfg_runs_to`)

| Buys | Does not buy |
| --- | --- |
| **L-adeq (SE4):** operational runs ⊆ collecting semantics at exit | Per–program-point adequacy (only exit sugar is in scope for slice 1) |
| Justifies treating `cfg_runs_to` as the compiled counterpart of `pruns_to` | Soundness of the abstract interpreter (already proved upstream) |
| Enables composing: IMP2 big-step ⟹ `pruns_to` ⟹ `cfg_runs_to` ⟹ `cfg_collect` | Trace-level adequacy (`cfg_collect_trace`) — separate, harder slice |

**Priority.** Track B is **more load-bearing for the pipeline narrative**
(analyzer spec = `cfg_collect`). Track A is **more load-bearing for the AFP
anchor narrative** (thesis credibility vs Lammich–Wimmer IMP2). Neither
unblocks a missing soundness lemma; both tighten definition–statement alignment.

---

## Terminology (avoid confusion)

| Name | Direction | Status |
| --- | --- | --- |
| **`backward_sim`** | IMP2 `big_step` → `pruns_to` | **Done** |
| **`forward_sim`** (target) | `pruns_to` → IMP2 `big_step` | **Open** (this doc, Track A) |
| **`bidirectional_sim`** (corollary) | Both directions under `source_com` / `source_pi` | **Open** (compose A + backward) |
| **`pruns_to_adeq`** (target) | `pruns_to` → `cfg_runs_to` | **Open** (this doc, Track B) |

In simulation literature "backward" often means the implementation simulates the
spec; here **`backward_sim` means induct on the spec (IMP2) and construct our
run** — the direction soundness *transfer* needs. Forward closes the converse.

---

## Track A — forward IMP2 simulation

### Target theorem

```isabelle
theorem forward_sim:
  assumes sp: "source_pi \<Pi>"
      and sc: "source_com c"
      and run: "pruns_to \<Pi> c s t"
  shows "big_step (to_imp2_pi \<Pi>) (to_imp2_com c, embed s)
           (embed t)"   (* or array state S with proj0 S = t — pick one invariant *)
```

**Corollary (`bidirectional_sim`).** Under the same side conditions,
`pruns_to \<Pi> c s t` ↔ IMP2 big-step from `embed s` to some `T` with
`proj0 T = t`. Instantiated from `forward_sim` + `backward_sim`.

### Proof-route decision (pick one before coding)

| Route | Idea | Pros | Cons |
| --- | --- | --- | --- |
| **A1 — invert `pruns_to`** | Decomposition lemmas (`pruns_to_SeqE`, `pruns_to_IfE`, …) on `psteps`; build IMP2 derivation bottom-up | Stays on the existing small-step relation; no new semantics | Inversion on frame stack is fiddly; `While` needs loop iteration measure |
| **A2 — big-step layer** | Define `pbig_step` on our `com` mirroring IMP2 rules; prove `pbig_step ↔ pruns_to`; prove `pbig_step` → IMP2 `big_step` by translation | Standard small↔big pattern; forward to IMP2 is structural | New inductive + equivalence proof is its own phase |
| **A3 — invert `pstep` + star lift** | Strong `pstep` inversion, replay IMP2 rule per step | Fine-grained control | Very granular; easy to get lost in `Restore`/`Seq`/`While` unfolding |

**Recommendation: A2.** The backward proof already matched IMP2 rules to
`pruns_to` combinators; a parallel `pbig_step` makes forward a symmetric
translation induction. Route A1 is viable if you prefer not to introduce
`pbig_step`, but budget extra time for `While` and framed `Scope`/`Call`.

### Lemma checklist (Route A2)

| ID | Statement | Reuses |
| --- | --- | --- |
| **F-pbig-skip** | `pbig_step \<Pi> SKIP s s` | def |
| **F-pbig-assign** | `pbig_step \<Pi> (Assign x a) s (s(x := aval a s))` | def |
| **F-pbig-seq** | `pbig_step c1 s s2 ⟹ pbig_step c2 s2 t ⟹ pbig_step (Seq c1 c2) s t` | def |
| **F-pbig-if** | guard + branch ⟹ `pbig_step (If b c1 c2) s t` | def |
| **F-pbig-while** | standard while rules | def |
| **F-pbig-scope** | `pbig_step c (enter_state s) t' ⟹ pbig_step (Scope c) s <s\|t'>` | `combine_states` |
| **F-pbig-call** | lookup + body ⟹ `pbig_step (Call p) s <s\|t'>` | `pruns_to_Scope_Call` shape |
| **F-pbig↔pruns** | `pbig_step \<Pi> c s t ↔ pruns_to \<Pi> c s t` | `pruns_to_*` forward direction + `psteps` inversion |
| **F-trans** | `pbig_step \<Pi> c s t ⟹ big_step (to_imp2_pi \<Pi>) (to_imp2_com c, embed s) T` with `proj0 T = t` | `aval_to_imp2_sim`, `proj0_*`, rule induction |
| **F-forward** | `forward_sim` | compose |

For Route A1, replace **F-pbig-*** with **F-pruns-E-*** decomposition lemmas and
prove **F-forward** directly by induction on `psteps`.

### Invariants (Route A2 / F-trans)

Do **not** aim for `S = embed t` at the end of an arbitrary run — array
assignment breaks `embed` preservation (`IMP2_Bridge.thy` comment at Phase 3
foundation). Use throughout:

- **Entry:** `proj0 S = s` (scalar store being tracked).
- **Exit:** `proj0 T = t`.
- **Assignment:** IMP2 state updates index 0 only; show `proj0` commutes with
  scalar update (`proj0_Assign` already proved).

### Scope / Call alignment (post route 2b)

Route 2b resolved the entry mismatch documented in
`AFP_IMP2_REBASE_MIGRATION.md` §Phase 3 gate: our `Scope`/`Call` now use
`enter_state` (locals zeroed, globals kept), matching IMP2 `SCOPE` entry
(`proj0_null_combine`). Forward simulation should **not** need translation
workarounds (`Assign_Locals` padding). Verify in the **F-pbig-scope** /
**F-trans-Scope** case before investing in the full proof.

### Exit criteria (Track A)

- `forward_sim` (+ optional `bidirectional_sim`) in `IMP2_Bridge.thy`, no
  `sorry`, batch-green in `Voblint_IMP2`.
- One example corollary: e.g. `pruns_to` on `Example_Inc_Proc` implies IMP2
  big-step (sanity check, not a new headline).
- `README.md` / `PROOF_OVERVIEW.md`: one sentence each — bidirectional IMP2
  agreement on terminating source programs.

---

## Track B — operational adequacy (`pruns_to` ⟹ `cfg_runs_to`)

### Target theorem

```isabelle
theorem pruns_to_cfg_runs_to:
  assumes sp: "source_pi \<Pi>"
      and sc: "source_com c"
      and run: "pruns_to \<Pi> c s t"
  shows "cfg_runs_to \<Pi> ps c s t"
```

Requires a well-formedness side condition on `ps` (procedure list passed to
`compile_prog`) — state explicitly when slicing (likely `set ps = dom \<Pi>` or
the finite support actually compiled).

### Why this is separate from Track A

- Track A compares **two AST-level** semantics (our small-step vs IMP2 big-step).
- Track B compares **AST operational** vs **compiled CFG collecting** —
  the spec the analyzer soundness theorem uses (`cfg_collect` at `cfg_exit`).

The pipeline today:

```
cfg_collect / cfg_collect_trace  ←── analyzer soundness (proved)
        ↑
   cfg_runs_to (definitional exit projection)
        ↑
     [GAP — not proved]
        ↑
     pruns_to  ←── backward_sim ←── IMP2 big_step (proved)
```

Track B fills the middle gap. Track A fills the bottom-right converse of
`backward_sim`.

### Proof strategy (sketch)

Induction on the **height** of `pruns_to` (mirror **L-adeq** in
`PROCEDURES_EXTENSION_PLAN.md` §9.5):

1. **Base commands** (Assign, Skip): show a single CFG path / edge fold reaches
   the same store at exit.
2. **Seq / If / While:** compose sub-derivations using existing CFG path
   infrastructure (`cfg_path`, `edges_collect`, compound compilation offsets in
   `CFG_Path.thy`).
3. **Scope / Call:** use enter edges + combine triples in `compile_prog`; match
   `enter_state` on entry and `combine_states` on return — the same operations
   `cfg_collect` already threads.

Reuse targets:

- `IMP2_Proc_to_CFG.thy` — compilation structure.
- `CFG_Collect_Runs.thy` — introduction lemmas for `cfg_collect` at exit.
- `CFG_Path.thy` / collecting path lemmas — witness construction.

**First slice:** non-recursive programs, single procedure in `ps`, no nested
`Call` — same shape as `Example_Inc_Proc.thy`. Extend to mutual recursion once
the witness pattern is stable.

### Exit criteria (Track B)

- `pruns_to_cfg_runs_to` (name TBD) batch-green in `Voblint_CFG` or
  `Voblint_Formalization` (imports both sides).
- Example instantiation on `inc_pi` / `Example_Inc_Proc`.
- Optional compose lemma:
  `big_step … ⟹ cfg_runs_to …` via `backward_sim` + adequacy.

---

## Phasing

| Phase | Track | Deliverable | Depends on |
| --- | --- | --- | --- |
| **0** | — | Pick Route A1 vs A2; confirm `ps` side condition for Track B | — |
| **1A** | A | `pbig_step` + `pbig_step ↔ pruns_to` (or A1 decomposition lemmas) | route 2b (done) |
| **2A** | A | `forward_sim` + `bidirectional_sim` | Phase 1A |
| **1B** | B | Adequacy for straight-line + `Seq`/`If`/`While` (no `Call`) | `compile_prog` paths |
| **2B** | B | Add `Scope`/`Call` + combine witnesses | Phase 1B, enter/combine in collecting |
| **3** | both | Example corollaries; doc touch-up | 2A, 2B |

Tracks A and B are **independent** after Phase 0 — parallelize if desired.

---

## Risks

| Risk | Mitigation |
| --- | --- |
| **`While` inversion needs a measure** | Use `while_option` / bounded iteration on guard, or prove via A2 big-step layer |
| **Frame-stack cases multiply** | Keep `source_com` (no `Restore` in source); runtime configs appear only inside `psteps` proofs |
| **`embed` vs `proj0` drift** | Never assume `S = embed s` mid-run; copy the `backward_sim` invariant discipline |
| **Track B blow-up on nested `Call`** | Slice 1B on flat examples; defer recursion to 2B |
| **Batch hangs on `auto elim!` for path predicates** | Bounded `simp only:` / named case lemmas (see `AGENTS.md` build timeout policy) |
| **Scope creep into array syntax** | Out of scope; array forward cases live in `ARRAY_SYNTAX_EXTENSION.md` |

---

## Non-goals (this migration)

- Redefining the analyzer spec or replaying `trace_ip_analysis_sound`.
- Forward simulation for **non-terminating** runs (big-step cannot express them).
- Per–program-point adequacy (`∀v. … ∈ cfg_collect g … v`) — exit-only slice first.
- Replacing `cfg_collect_trace` with small-step traces (separate M3.5 / trace handoff work).

---

## First slice (recommended start)

**Track A, Route A2, intraprocedural fragment:**

1. Define `pbig_step` for `SKIP` / `Assign` / `Seq` / `If` / `While` only (no
   `Scope`/`Call`).
2. Prove `pbig_step ↔ pruns_to` on the fragment (`source_com` restricted).
3. Prove `forward_sim` for the fragment (translation to IMP2).
4. Batch-gate `Voblint_IMP2`.

Then add `Scope`/`Call` (Track A Phase 2A) and begin Track B Phase 1B in
parallel.

Use I/Q on `IMP2_Bridge.thy` / `IMP2_Proc.thy`; batch only when file-clean.

---

## Doc / roadmap hooks (after completion)

- `docs/AFP_IMP2_REBASE_MIGRATION.md` — add "Phase 4 — forward (done)" pointer.
- `docs/PROOF_OVERVIEW.md` — bidirectional IMP2 agreement + adequacy link.
- `docs/GLOSSARY.md` — `forward_sim`, `pruns_to_cfg_runs_to` entries.
- `README.md` — update "Big-step is not the spec" paragraph to mention
  bidirectional agreement on terminating runs.

Do **not** add lemma name lists to `AGENTS.md` or `ROADMAP.md` (they drift).
