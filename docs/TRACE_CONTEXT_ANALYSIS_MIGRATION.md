# Migration — trace-context analysis (umbrella plan)

Status: **PLANNED.** Agent entry point for history-sensitive analysis. Two
**implementation tracks** share one **semantic foundation** (B0–B2) and one
**soundness target** (`context_analysis_sound`). Track-specific detail lives in
child docs — do not merge their solver steps.

| Child doc | Track | When to read |
| --- | --- | --- |
| `TRACE_CONTEXT_BRIDGE_MIGRATION.md` | shared B0–B2 | semantic defs, `lfp(trace)`, bridge lemmas |
| `TRACE_BASED_FORK_MIGRATION.md` | **A** digest / k-CFA | mono back-end, `(pp × d)` unknowns, R1–R6 |
| `SEMANTIC_CONTEXT_MIGRATION.md` | **B** entry-state | warrowing back-end, `(pp + g) × c`, S0–S4 |
| `CONTEXT_SENSITIVE_GLOBALS_MIGRATION.md` | thesis framing | PLDI §2 axis, reduced cardinal power |

KB: `wiki/research/trace-precision-direction.md`, `wiki/concepts/digests.md`.

---

## 1. Goal

```text
concrete trace semantics  →  finite context/digest abstraction  →  context-indexed solver
```

Recover precision lost at `α_last` by indexing the fixpoint with a finite history
key `c` (or digest `d`), not by storing concrete traces in the solver.

**Headline soundness shape** (both tracks):

```text
∀ v c.  cfg_collect_ctx dg cmp g S v c  ⊆  γ (env v c)
```

**Headline precision shape:** a non-trivial instance is *strictly tighter* than
the flat analyzer on a concrete program (`digest_beats_flat` / semantic analogue).

---

## 2. Core distinction (do not conflate)

| Statement | True? |
| --- | --- |
| `cfg_collect_trace` is more expressive than `cfg_collect` | **Yes** |
| Proving soundness w.r.t. traces makes the flat solver history-sensitive | **No** |
| `lfp(trace)` in the semantics improves solver precision | **No** |
| Unknowns `(pp, c)` or `envd v c` improve precision | **Yes** (when `c` is non-trivial) |

```text
Today (flat):
  cfg_collect_trace  ──α_last──▶  cfg_collect  ──γ──▶  env v

Target (context-sensitive):
  cfg_collect_trace  ──α_ctx/dg──▶  cfg_collect_ctx  ──γ──▶  env v c
```

The solver never stores traces. It stores a **finite abstraction of history**
updated incrementally (`enter_ctx` / digest push-pop).

---

## 2.1 Thesis spine — observables vs abstractions (read this)

Do **not** treat every `dg` as an arbitrary label. The clean story has **two
levels**:

### Level A — trace observables (new concrete semantics)

Properties of execution histories that are **not definable** from reachable
stores alone. Each observable induces a **trace-derived collecting semantics**
before any analyzer exists.

| Observable | Collecting semantics (sketch) | Definable from `cfg_collect`? |
| --- | --- | --- |
| **Last writer** | `last_write_collect(x,v) = { last_writer(tr,x) \| tr ∈ cfg_collect_trace(v) }` | **No** |
| Call history | `call_stack(tr)` | No |
| Lockset held | `lockset(tr)` | No |
| Taint origin | `source(tr,x)` | No |
| Branch/path taken | `path_sig(tr)` | No |

**Canonical motivating example (supervisor):** reading `g` should depend on
**which write to `g` reached this read on this trace**. At store level you only
get `g ∈ {1,2}`; at trace level you get `last_write_collect(g, read) = {w1, w2}`.
Properties like “execute `w1`-path only” are **literally unstatable** over
`cfg_collect`.

**Prerequisite for write-site identity:** action-labelled traces
`(edge_action × store) list` (M3.5 Slice 1). Until then, prove observables on
value-based surrogates (Ex0) or on hand-labelled traces.

**Semantic lemmas (prove before any solver):**

```isabelle
definition last_writer :: "trace ⇒ vname ⇒ pp"   (* needs action trace *)

definition last_write_collect ::
  "vname ⇒ cfg ⇒ store set ⇒ pp ⇒ pp set" where
  "last_write_collect x g S v =
     { last_writer tr x | tr. tr ∈ cfg_collect_trace g S v }"

lemma last_writer_sound:
  "tr ∈ cfg_collect_trace g S v ⟹ last_writer tr x ∈ last_write_collect x g S v"
```

`cfg_collect_ctx` with `dg = last_write_map` is then **projection of this
observable** onto `(v, c)`-indexed store sets — not a separate ad-hoc design.

### Level B — finite abstractions (what the solver approximates)

The TD solver cannot store infinite observables. It uses a **finite** digest
`dg_B : trace → 'd` that approximates a Level-A observable:

```text
exact last-writer map
        ↓  (join / bound / widen)
last-k writers / write generation / "was written?"
```

```text
full call history
        ↓  truncate
k-call-string
        ↓
caller-only
```

**Analyzer contract (unchanged):** `cfg_collect_ctx dg_B cmp … c ⊆ γ(env v c)`
approximates Level A **soundly** when `dg_B` refines the observable (B2 bridge).

Call strings and entry states are **implementation-friendly Level-B instances**.
**Last-writer is the canonical Level-A example for global precision**; k-CFA and
`enter#` are sibling instances at Level B.

### Proof story (full stack)

```text
Small-step / CFG operational semantics
        │
        ▼
cfg_collect_trace          (trace collecting — DONE)
        │
        ▼
Level A observables        (last_write_collect, … — PLANNED)
        │
        ▼
α_ctx / dg_B               (finite abstraction — B0, B2)
        │
        ▼
cfg_collect_ctx            (context collecting — B0)
        │
        ▼
context-indexed eqsystem   (Track A / B — B3)
        │
        ▼
TD-side solver
```

**Deepest contribution:** traces are the **canonical concrete semantics**;
history-sensitive analyses are **finite abstractions of trace observables** —
not unrelated “context features.”

---

## 3. What already exists (do not rebuild)

| Artifact | File |
| --- | --- |
| `trace_witness`, `cfg_collect_trace` | `src/CFG/Collecting/CFG_Collect_Trace.thy` |
| `trace_witness_d`, `reaching_compat` | same |
| `digest_env_sound`, `digest_read_sound`, `flat_env_is_digest_sound` | `src/Formalization/Pipeline/Trace_Analysis_Sound.thy` |
| Flat trace soundness | `trace_analysis_sound` (same file) |
| Precision toy witness | `src/Formalization/Examples/Example_Trace_Digest_Precision.thy` |
| Mixed-flow baseline (pre-context) | `mixed_flow_analysis_sound` |

`digest_env_sound` is already the analyzer contract; B0 names the intermediate
semantics it quantifies over.

---

## 4. Shared semantic layer (both tracks)

Detail: `TRACE_CONTEXT_BRIDGE_MIGRATION.md`.

### B0 — Context collecting semantics (**do first**)

**Files:** `CFG_Collect_Trace.thy` or `CFG_Collect_Context.thy`; corollary in
`Trace_Analysis_Sound.thy`.

**Add:**

```isabelle
definition alpha_ctx :: "(trace ⇒ 'c) ⇒ ('c ⇒ 'c ⇒ bool) ⇒ trace set ⇒ 'c ⇒ store set"
definition cfg_collect_ctx :: "… ⇒ pp ⇒ 'c ⇒ store set"
```

**Prove:**

```isabelle
lemma cfg_collect_ctx_reaching_compat:
  "cfg_collect_ctx dg cmp g S v c =
   alpha_last (reaching_compat dg cmp c g S v)"
```

Plus: monotonicity under trace refinement; flat collapse when `cmp = (λ_ _. True)`.

**Repackage:** `digest_env_sound` as `context_collect_sound` (definitional).

**Acceptance:** no `sorry`; no solver changes; `Voblint_CFG` + `Trace_Analysis_Sound` green.

### B1 — Optional `lfp(trace)` (proof interface only)

Add `cfg_collect_trace_F` + `cfg_collect_trace_lfp`; prove
`trace_witness_iff_lfp`. **Do not replace** `trace_witness`.

**Combine clause must match the inductive rule verbatim** (`CFG_Collect_Trace.thy`):

```isabelle
tau @ tl rho @ [<last tau|last rho>]   (* not tau @ rho *)
```

with `hd rho = enter_state (last tau)`.

**Skip B1** unless proving B3 via post-fixpoint induction or thesis needs
"trace-level AI" wording.

### B2 — Incremental context refines `dg` (**design crux, both tracks**)

Parametric locale: `dg`, `cmp`, `update_ctx` (edges), `combine_ctx` (IP return).

**Obligation (name TBD):** incremental solver context simulates whole-trace digest.

```text
cmp (update_ctx (dg trace) step) (dg (trace @ step))     -- edge
cmp (combine_ctx (dg tau) (dg rho)) (dg (tau @ tl rho @ [return]))  -- combine
```

**Track A specifics:** k-truncation agreement (fork R2), combine over-approx not
exact inverse (fork R3). **Track B specifics:** `enter_ctx` = Goblint `enter#`;
value-dependent routing → non-`mono_sides`.

**Acceptance:** `context_step_refines_dg` (or per-track names), no `sorry`.

```text
B0 ──▶ B3 (both tracks)
B1 (optional) ──▶ B3
B2 ──▶ B3
```

---

## 5. Track A — Digest / k-call-string fork

Detail: `TRACE_BASED_FORK_MIGRATION.md`. **Preferred first implementation** —
syntactic contexts keep `threefold_mono` where applicable.

| | |
| --- | --- |
| **Context** | bounded k-call-string (finite, value-independent) |
| **Unknowns** | `(pp × 'd) + 'g` |
| **Output** | `envd :: pp ⇒ 'd ⇒ abs_state` |
| **Back-end** | `TD_side_mono` where `mono_sides` holds |
| **First instance** | `CallString k` locale |

**Slices (fork naming):**

| Slice | Deliverable |
| --- | --- |
| A1 | `Digest` locale + `CallString` interpretation (`dg`, `cmp`) |
| A2 | incremental digest transfer + B2 bridge for call strings |
| A3 | digest-indexed `side_cfg_T_*` / `side_analyse_*_d` |
| A4 | `context_analysis_sound` ⇒ `digest_env_sound` for computed `envd` |
| A5 | executability + strict precision theorem (not just `value` printout) |

**Review obligations (blocking):**

| ID | Issue |
| --- | --- |
| R1 | `solve_dom` for partitioned unknowns — inherited or new hypothesis? |
| R2 | k-truncation: incremental digest = `dg` on whole trace |
| R3 | combine must over-approx compatible caller partitions (not exact pop) |
| R4 | confirm `digest_env_sound` is parametric in `(dg, cmp)` |
| R5 | precision = proved theorem, not evaluated inequality |
| R6 | lazy context discovery via demand-driven `TD_side` |
| S2.5 | `k = 0` reproduces flat analyzer (early conservativity gate) |

**Main risk:** unsound k-CFA return handling if combine pop is too precise.

---

## 6. Track B — Semantic entry-state contexts

Detail: `SEMANTIC_CONTEXT_MIGRATION.md`. Goblint-style `enter#`; enables
conditional routing (`flag_etf`).

| | |
| --- | --- |
| **Context** | abstract entry state (projection of store at call) |
| **Unknowns** | `(pp + 'g) × 'c` |
| **Encoding** | entries-as-sinks (encoding 1) |
| **Back-end** | **warrowing only** (`TD_side_upd_rule`) |
| **Given up** | `least_partial_post_solution` / `threefold_mono` for this instance |
| **Kept** | γ-soundness via shared `sound_effectful_transfer` |

**Stages (semantic naming):**

| Stage | Deliverable |
| --- | --- |
| B-S0 | warrowing interface + global widening instance |
| B-S1 | context-threaded `side_cfg_T_eff`, abstract `enter_ctx` |
| B-S2 | entry-state instance + `semantic_ctx_analysis_sound` |
| B-S3 | `semantic_ctx_strictly_more_precise` witness |
| B-S4 | runnable / `solve_dom` (future; Context Gas) |

**Main risk:** `mono_sides` breaks; per-context `gseed`; infinite context set
without bounding.

**Prerequisite for B track:** B-S0 (warrowing interface) can proceed in parallel
with Track A after B0.

---

## 7. Track comparison (do not collapse)

| | Track A (digest) | Track B (semantic) |
| --- | --- | --- |
| Back-end | mono `TD_side` (when monotone) | warrowing `TD_side_upd_rule` |
| Context kind | syntactic finite digest | abstract entry state |
| Unknown shape | `(pp × d) + g` | `(pp + g) × c` |
| Optimality | available when `threefold_mono` | **not** available |
| Goblint fidelity | call strings / locksets | `enter#` semantic contexts |
| Primary risk | truncation + combine soundness | mono loss + context explosion |

Both tracks prove the **same** semantic target (§1) with different `(dg, cmp)` and
solver encodings.

---

## 8. Shared solver target

After post-fixpoint of the context-indexed system:

```isabelle
theorem context_analysis_sound:
  fixes env :: "pp ⇒ 'c ⇒ 'a abs_state"
  assumes "… is_post_fixpoint … env"
  shows "cfg_collect_ctx dg cmp g S v c ⊆ γ (env v c)"
```

**Corollaries:** `digest_read_sound`, `reaching_global_read_sound` at refined
traces. Flat recovery: `c = unit` / constant digest ⇒ `trace_analysis_sound`.

---

## 9. Conservativity checks (required gates)

| Check | Meaning |
| --- | --- |
| `flat_env_is_digest_sound` | flat `env` satisfies digest contract |
| `k = 0` / `c = unit` | indexed system reproduces today's analyzer |
| `cfg_collect_ctx` with `cmp = (λ_ _. True)` | join over `c` = `α_last` of all traces |

Run **before** precision claims (fork S2.5; semantic `'c = unit` in S1).

---

## 10. Target theorems (ladder)

Status key: **DONE** = in repo; **B0** = needs `cfg_collect_ctx`; **TRACK** = needs solver
track; **PLANNED** = new example theory.

| # | Theorem (working name) | Meaning | Status | File / stage |
| --- | --- | --- | --- | --- |
| T1 | `context_analysis_sound` | `cfg_collect_ctx … c ⊆ γ(env v c)` | **PLANNED** | Track A4 / B-S2 |
| T2 | `context_collect_sound` | `digest_env_sound` via `cfg_collect_ctx` | **B0** | `Trace_Analysis_Sound.thy` |
| T3 | `flat_env_is_digest_sound` | flat `env` satisfies digest contract | **DONE** | `Trace_Analysis_Sound.thy` |
| T4 | `flat_is_context_sound` | `envd v c = env v` ⇒ context sound | **B0** | corollary of T3 + T2 |
| T5 | `context_k0_eq_flat` | `k = 0` analyzer = flat analyzer | **TRACK** | Track A, S2.5 |
| T6 | `digest_read_sound` | read uses only compatible-history values | **DONE** | `Trace_Analysis_Sound.thy` |
| T7 | `combine_ctx_sound` | IP `cmp` + combine preserves `cfg_collect_ctx` | **B2** | `CFG_Collect_Context.thy` |
| T8 | `context_step_refines_dg` | incremental ctx simulates `dg` on traces | **B2** | per-track instance |
| T9 | `digest_beats_flat` | strict precision, hand-built `envd` | **DONE** | `Example_Trace_Digest_Precision.thy` |
| T10 | `one_callstring_separates_callers` | k-CFA precision on real CFG | **TRACK** | `Example_CallString_Precision.thy` |
| T11 | `semantic_ctx_separates_entry_states` | entry-state beats call-string | **TRACK** | `Example_Semantic_Ctx_Precision.thy` |
| T12 | `history_sensitive_sound_and_precise` | sound + strict ⊃ flat (computed env) | **TRACK** | capstone per track |

### T1 — Main soundness (central)

```isabelle
theorem context_analysis_sound:
  assumes "is_post_fixpoint … env"
  shows "cfg_collect_ctx dg cmp g S v c ⊆ γ (env v c)"
```

> At every `(v, c)`, the analyzer covers exactly the last stores of traces reaching
> `v` whose history is compatible with `c`.

### T2–T4 — Conservativity

After B0, `digest_env_sound` unfolds to `context_collect_sound` via
`cfg_collect_ctx_reaching_compat`.

```isabelle
lemma flat_is_context_sound:
  assumes "envd v c = env v" for all v c
  assumes post_fp_flat
  shows "cfg_collect_ctx dg cmp g S v c ⊆ γ (envd v c)"
```

`flat_env_is_digest_sound` (**DONE**) is the instance `envd v d = env v`.

Track A early gate (**T5**):

```isabelle
lemma context_k0_sound_iff_flat:
  (* k = 0: partitioned unknowns collapse to flat post-fixpoint soundness *)
```

Executable equality `side_analyse_d k0 … = side_analyse …` is stronger; prove soundness
equivalence first if equality is hard.

### T6 — Digest read (thesis payoff)

**DONE** — plugs into T1/T2:

```isabelle
theorem digest_read_sound:
  assumes "digest_env_sound dg cmp g S envd"
  assumes "tr ∈ cfg_collect_trace g S v" "cmp (dg tr) d"
  shows "(last tr) x ∈ gamma (envd v d x)"
```

After B0: hypothesis is equivalently `context_collect_sound` on `envd`.

### T7–T8 — IP bridge (anti wrong-return)

Combine clause uses **compressed** traces (`tl rho`):

```isabelle
lemma combine_ctx_sound:
  assumes "tau ∈ cfg_collect_trace g S c"
  assumes "rho ∈ cfg_collect_trace g S ex"
  assumes "hd rho = enter_state (last tau)"
  assumes "cmp (dg tau) (dg rho)"
  shows "last (tau @ tl rho @ [<last tau|last rho>])
         ∈ cfg_collect_ctx dg cmp g S ret (combine_ctx (dg tau) (dg rho))"
```

Track A: `combine_ctx` may **join** compatible caller partitions (fork R3), not invert
`enter_ctx` exactly at depth ≥ k.

### B0 library lemmas (prove with T2)

```isabelle
lemma cfg_collect_ctx_mono_trace: …
lemma cfg_collect_ctx_subset_flat:
  "cfg_collect_ctx dg cmp g S v c ⊆ alpha_last (cfg_collect_trace g S v)"
lemma cfg_collect_ctx_mono_cmp: …
lemma cfg_collect_trace_d_ctx_subset: …
```

---

## 11. Example programs and proof targets

Examples are **staged**: semantics-only proofs (B0, no solver) → hand-built `envd`
(like today) → **computed** `envd` from `side_analyse_*_d` (Track A/B goal).

### Ex0 — Two histories, no procedures (**DONE**)

**Program (semantic sketch):** entry set `{x:=1, x:=-1}` at one program point; no edges.

**Flat:** `x ∈ ℤ` (sign: `⊤`). **Digest `d = x`:** reader at `d=1` sees `x>0` only.

| Target | Status |
| --- | --- |
| `digest_beats_flat`, `digest_env_sound_concrete` | **DONE** |

**File:** `src/Formalization/Examples/Example_Trace_Digest_Precision.thy`

**Agent:** extend with `cfg_collect_ctx` rewrites once B0 lands (should be
one-liners from `cfg_collect_ctx_reaching_compat`).

---

### Ex1 — Same call site, different globals (Track A priority)

**Program:**

```c
global Gg;

void main() {
  int x = 0; f();   // call A
  x = 1; f();       // call B
}

void f() {
  Gg = x;
  // read(Gg) at return pp
}
```

**Flat at read:** `Gg ∈ {0,1}`. **1-call-string at `f`:** caller `main` after first
`f`-call vs second call → separate contexts.

| Flat | Context-indexed |
| --- | --- |
| `Gg ∈ {0,1}` | ctx after `x=0` call: `Gg = 0` |
| | ctx after `x=1` call: `Gg = 1` |

**Target file:** `src/Formalization/Examples/Example_CallString_Precision.thy`

**Reuse:** `Example_Inc_Proc.thy` pattern (`imp_prog`, `compile_prog`, CFG lemmas).

**Theorems (staged):**

| Stage | Theorem |
| --- | --- |
| B0 semantics | `ex1_reaching_compat_separates` — two trace families, two digests |
| Hand `envd` | `ex1_digest_env_sound_manual` — like `digest_env_sound_concrete` |
| Precision | `ex1_digest_beats_flat` — `γ(envd read d0) ⊂ γ(env flat read)` |
| Track A5 | `one_callstring_separates_callers` — on **computed** `side_analyse_*_d` |

```isabelle
(* sign domain, names illustrative *)
lemma one_callstring_separates_callers:
  "gamma_sign (envd f_read_cs_main_a ''Gg'') ⊆ {0}"
  "gamma_sign (envd f_read_cs_main_b ''Gg'') ⊆ {1}"
```

---

### Ex2 — Different callers, same callee (call-string showcase)

**Program:**

```c
void main() { a(); b(); }
void a() { f(0); }
void b() { f(1); }
void f(int x) { Gg = x; /* read */ }
```

**1-call-string:** at `f`, digest `[main;a]` vs `[main;b]`.

| Flat `f` read | `envd f [main;a]` | `envd f [main;b]` |
| --- | --- | --- |
| `Gg ∈ {0,1}` | `Gg = 0` | `Gg = 1` |

**Target file:** same `Example_CallString_Precision.thy` (or `Example_Two_Callers.thy`)

**Theorem:** `two_callers_one_callstring_separates` (special case of T10).

---

### Ex3 — Semantic entry-state beats syntactic call-string (Track B)

**Program:**

```c
void main() {
  x = 0; f();
  x = 1; f();   // same call site, different abstract entry state
}
void f() { Gg = x; }
```

**Call-string 1-CFA:** both calls share digest `[main]` → **still joins** at `f`.

**Entry-state context:** `enter#(x↦0)` vs `enter#(x↦1)` → **separates**.

| Context kind | At `f` exit |
| --- | --- |
| Flat | `Gg ∈ {0,1}` |
| 1-call-string | `Gg ∈ {0,1}` (too coarse) |
| Semantic entry | `Gg = 0` vs `Gg = 1` |

**Target file:** `src/Formalization/Examples/Example_Semantic_Ctx_Precision.thy`

**Theorems:**

```isabelle
theorem semantic_ctx_separates_entry_states:
  "γ (env main_f_ctx0 ''Gg'') ⊆ {0}"
  "γ (env main_f_ctx1 ''Gg'') ⊆ {1}"

theorem semantic_beats_callstring_on_ex3:
  (* optional: 1-CFA envd strictly coarser on this program *)
```

**Track:** B-S3 (`semantic_ctx_strictly_more_precise`).

---

### Ex4 — Conditional routing (`flag_etf`, Track B bonus)

**Program:** abstract flag routes side-effect to different global slots (see
`Sign_Named_Global_Eff.thy` / `Mixed_Flow_Sound.thy`).

**Point:** value-dependent routing needs warrowing back-end; demonstrates B track
vs monotone Track A.

**Target:** extend `Example_Mixed_Flow_Sign.thy` with context-indexed read theorem
after B-S2.

---

### Ex5 — Last-writer observable (canonical Level-A example)

**Level:** A (semantic observable) + B (finite `last_write_map` digest for solver).

**Idea:** a global read depends on **which write reached it on this history** — a
trace property, not a store property. Defines **`last_write_collect`** (see §2.1),
which cannot be stated over `cfg_collect`.

**Program:**

```c
g = 0;
if (*) { g = 1; }   // write site w1
else   { g = 2; }   // write site w2
x = g;              // read
```

**Store collecting at read:** `g ∈ {1,2}` — no last-writer.

**With write-site digest** `dg(tr) = λg. last_write_site(tr, g)`:

```text
ctxA: g ↦ w1   →  read sees g = 1
ctxB: g ↦ w2   →  read sees g = 2
```

Strictly more precise than flat; also separates histories that **1-call-string can
miss** (intra-procedural branch, same call stack).

**Expressible in this framework?** **Yes** — another `(dg, cmp)` instance on the
same ladder (`cfg_collect_ctx`, `context_analysis_sound`, `digest_read_sound`).

**Repo gap:** `trace = store list` does not label *which edge wrote*. Prerequisite:
**M3.5 Slice 1** — action-labelled traces `(edge_action × store) list` (named in
`docs/SEIDL_TRACE_MIGRATION_HANDOFF.md`). Ex0's value-keyed digest is a weaker
stepping stone until Slice 1 lands.

**Target file:** `src/Formalization/Examples/Example_Last_Writer_Precision.thy`

**Theorems:** `last_writer_sound`, `last_write_collect` lemmas, then
`last_writer_beats_flat`, optional `last_writer_beats_callstring`.

**Thesis line:** last-writer is the **canonical Level-A motivating example**;
call strings and entry states are Level-B instances of the same stack (§2.1).

---

### Example → stage map

```text
Ex0  digest_beats_flat          DONE        B0: add cfg_collect_ctx aliases
Ex1  call-site history          PLANNED     B0 semantics → Track A5
Ex2  two callers                PLANNED     Track A5
Ex3  entry-state > call-string  PLANNED     Track B-S3
Ex4  flag_etf routing           PLANNED     Track B-S2 bonus
Ex5  last-writer digest         PLANNED     action traces (M3.5) + B2 instance
```

---

## 12. Thesis capstone (per track)

After computed analyzer exists:

```isabelle
theorem history_sensitive_global_read_sound_and_precise:
  assumes "context_analysis_sound … envd"
  assumes "digest_read_sound …"
  assumes "strictly_more_precise_than_flat envd env"
  shows "sound_global_read envd ∧ strict_precision_gain envd env"
```

**Track A instance:** `envd` from `side_analyse_d`; precision from Ex1/Ex2.

**Track B instance:** `env` from semantic context solver; precision from Ex3.

Must be a **proved** strict inclusion (`⊂`), not a `value` printout (fork R5).

---

## 13. Precision witnesses (summary)

| Witness | Example | Track | Status |
| --- | --- | --- | --- |
| `digest_beats_flat` | Ex0 | semantics | **DONE** (hand `envd`) |
| `one_callstring_separates_callers` | Ex1–Ex2 | A | **PLANNED** |
| `semantic_ctx_strictly_more_precise` | Ex3 | B | **PLANNED** |

---

## 14. Out of scope

- Literal trace-set domain in the solver (`gamma :: 'b ⇒ trace set`).
- Proving the flat solver is least abstraction of `cfg_collect_trace`.
- Full `solve_dom` proof for warrowing / partitioned systems (assumed, as today).
- Optimality for semantic-context instances.
- Choosing Track A vs B for the thesis — both may coexist; pick one for primary contribution.

---

## 15. Suggested agent execution order

```text
Phase 0 (semantic)
  B0  →  cfg_collect_ctx + cfg_collect_ctx_reaching_compat
  B0+ →  Ex0: rephrase digest_beats_flat via cfg_collect_ctx (optional)
  B1? →  only if B3 proof strategy needs lfp induction

Phase 0b (semantics examples, no solver)
  Ex1 reaching_compat / cfg_collect_ctx lemmas on compiled CFG

Phase 1 (pick one track)
  Track A: A1 → A2 → A3 → A4 → A5 + Ex1/Ex2 computed precision
  Track B: B-S0 → B-S1 + B2 instance → B-S2 → B-S3 + Ex3

Phase 2 (optional second track)
  Reuse B0–B2; swap unknown encoding + back-end per §7.

Always:
  - I/Q loop for .thy edits; batch build only at slice close
  - conservativity gate before precision theorem
  - ASCII-only .thy sources
```

---

## 16. See also

- `docs/ROADMAP.md` — stable direction pointers
- `docs/thesis/trace-pivot-and-history-sensitive-globals.md` — chapter narrative
- `docs/NON_GOALS.md` — no optimality, `solve_dom` assumed
- `src/CFG/Collecting/CFG_Collect_Trace.thy` — `trace_witness` combine uses `tl rho`
- `src/Formalization/Pipeline/Trace_Analysis_Sound.thy` — T3, T6 (**DONE**)
- `src/Formalization/Examples/Example_Trace_Digest_Precision.thy` — Ex0 (**DONE**)
- `src/Formalization/Examples/Example_Inc_Proc.thy` — compile pattern for Ex1+
