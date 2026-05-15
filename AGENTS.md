<!-- markdownlint-disable-file MD025 -->

# AGENTS.md

You are a formal proof engineer working with Isabelle/jEdit. Your work is surgical, structured, and well-documented. Continuously evaluate whether proofs can be simplified, accelerated, or decomposed into smaller lemmas.

When starting a proof:

* Simple: use `by ...` or short `apply` proofs.
* Complex: use structured Isar.

Apply-style proofs:

* Proceed incrementally.
* Add 1–2 tactics at a time.
* Inspect resulting goals carefully.
* Avoid repeatedly rewriting entire proof scripts.

For Isar proofs:

1. Build top-level structure first
2. Use temporary `sorry`
3. Fill gaps incrementally
4. Extract reusable lemmas when complexity grows

---

# Project goal

Verify:

```text
IMP AST
  -> (optional CFG)
  -> equation system
  -> Top_Down_Solver
  -> sound abstract result
  -> mapped back to program
```

Already verified:

* AFP `Top_Down_Solver`

Work to prove:

1. IMP semantics + collecting semantics
2. CFG layer (optional)
3. Equation system soundness
4. Abstract domains
5. Result mapping

---

# Locked decisions

| Topic            | Decision                                      |
| ---------------- | --------------------------------------------- |
| Proof assistant  | Isabelle/HOL                                  |
| Language         | HOL-IMP                                       |
| Solver           | AFP `Top_Down_Solver`                         |
| Solver interface | `rhs :: pp => (pp => abs_state) => abs_state` |
| First domain     | Sign                                          |
| Second domain    | Interval                                      |
| Stretch          | Octagon                                       |

---

# Open decisions

* Direct AST -> eqsys vs CFG layer (`Direct_Equations.thy` explores the direct route)
* `acom` annotations vs map-based results
* One global Galois connection vs staged soundness
* IMP vs IMP2
* Whether Interval is stretch-goal only

---

# Repository layout

```text
src/
  IMP2/          syntax + semantics + collecting semantics
  CFG/           CFG + paths + CFG collecting semantics
  Domains/       abstract domains
  Equations/     constraint systems + soundness + direct AST->eqsys alternative
  Examples/      executable sign analysis example
  Solver/        TD solver interface + total correctness (TD_Total.thy)
  Pipeline/      end-to-end results
  attempt2/      exploratory scratch (ignore)
```

---

# Solver architecture

We prove:

* `make_rhs` monotone
* post-fixpoint implies collecting-semantics overapproximation

AFP proves:

* solver returns post-fixpoint

---

# Important design constraints

| Decision                    | Reason                       |
| --------------------------- | ---------------------------- |
| `Finite_Set.fold` for joins | monotone + deterministic     |
| finite CFG edges            | required for folds           |
| `join_comm` + `join_assoc`  | needed for fold independence |
| `'a::ord`                   | pointwise order on states    |

---

# Current proof status

## Done

* `td_analyse_post_fixpoint`
* sign join laws (`join_sign_comm`, `join_sign_assoc`)
* `sign_le` lattice laws (`sign_le_refl`, `sign_le_antisym`, `sign_le_trans`)
* `gamma_sign_mono`
* `aval_sign_sound` (+ `sign_plus/minus/times_sound`)
* `big_step_determ`
* basic collecting semantics lemmas (`collect_SKIP/Assign/Seq/If`)
* `collect_pp_mono`

## Medium difficulty (sorry)

* `assume_sign_sound`, `assume_not_sign_sound`, `assign_sign_sound`
* Abstract_Domain lattice laws
* `compile_fresh`, `compile_finite`, `compile_entry_ne_exit`
* `collect_While`
* `make_rhs_mono`

## Hard (sorry)

* `post_fixpoint_sound`
* CFG path lemmas (`CFG_Path.thy`)

## Hardest (sorry)

* `cfg_collect_exit_eq_collect` — WHILE loops + back-edges + path reasoning

---

# Proof phases

Concrete execution plan with ordered working steps, exit criteria per
phase, and full `sorry` inventory: see [`docs/PROOF_PHASES.md`](docs/PROOF_PHASES.md).

Big-picture proof chain and result-mapping options: see
[`docs/PROOF_OVERVIEW.md`](docs/PROOF_OVERVIEW.md).

---

# CFG path infrastructure

Core predicate:

```isabelle
inductive cfg_path ::
  "cfg => pp => (edge_action * pp) list => pp => bool"
```

Paths record actions — needed for transfer-fn composition.

```isabelle
fun path_collect ::
  "(edge_action * pp) list => state set => state set"
```

---

# Isabelle workflow

## Batch build

```bash
isabelle build -D . Goblint_Formalization
```

## MCP (Isabelle/REPL — `isabelle-ir`)

The Isabelle MCP server (I/R) is the **primary** way to develop proofs. Do not
edit `.thy` files blind — drive Isar through MCP and verify each step.

### Preflight (every fresh session)

1. **Server config visible to Claude Code.** Project-scope MCP is declared in
   **`.mcp.json` at repo root** (not `.cursor/mcp.json` — that is Cursor only):

   ```json
   {
     "mcpServers": {
       "isabelle-ir": {
         "type": "http",
         "url": "http://localhost:9148/mcp",
         "headers": {
           "Authorization": "Bearer isabelle-local",
           "Accept": "application/json, text/event-stream"
         }
       }
     }
   }
   ```

   Also requires `.claude/settings.local.json` →
   `"enabledMcpjsonServers": ["isabelle-ir"]`.

2. **Server running.** Probe:

   ```bash
   curl -sS -m 2 -X POST \
     -H 'Authorization: Bearer isabelle-local' \
     -H 'Accept: application/json, text/event-stream' \
     -H 'Content-Type: application/json' \
     http://127.0.0.1:9148/mcp -d '{}'
   ```

   Non-empty JSON-RPC reply ⇒ up. If down: `./start-ir.sh` (user-run).

3. **Load tool schemas.** MCP tools are deferred. First Isabelle action:

   ```
   ToolSearch select:mcp__isabelle-ir__connect,
              mcp__isabelle-ir__step,
              mcp__isabelle-ir__sledgehammer,
              mcp__isabelle-ir__find_theorems,
              mcp__isabelle-ir__load_theory,
              mcp__isabelle-ir__init,
              mcp__isabelle-ir__theories,
              mcp__isabelle-ir__source
   ```

4. **Authenticate.** Call `mcp__isabelle-ir__connect` with `token=isabelle-local`
   (omit `port`; default 9147). All other tools fail until `connect` succeeded.

### Standing rules

* After editing a `.thy` on disk → `load_theory(<fully.qualified.name>)` to
  re-sync; the heap lags otherwise.
* `init` uses fully-qualified imports, e.g.
  `Goblint_Formalization.CFG_Collecting`.
* `step` — **one Isar line per call**. Newlines often rejected.
* Sledgehammer timeout ≤ 15s. Prefer reported `by blast/auto/meson` over `metis`
  /`smt` (faster batch rebuild, fewer surprise dependencies).
* `nitpick` is not a separate MCP tool — invoke it via `step` as
  `lemma … nitpick [timeout = 5] oops`.

Flow: build → server up → `connect` → `load_theory` → `init` → `step` /
`sledgehammer`. See `docs/ISABELLE_AGENT_NOTES.md` for traps.

---

## MCP (Isabelle/Q jEdit plugin — `isabelle-iq`)

**Optional / opportunistic.** I/Q is the AWS Labs Scala plugin for
Isabelle/jEdit that exposes the same I/R REPL **plus** document-aware tools
(diagnostics, sorry positions, structured edits, command-state inspection).
Vendored alongside I/R in `ir-repo/iq/`. Use I/Q when jEdit is open;
otherwise stay on I/R.

### One-time install

```bash
./setup-iq.sh      # builds ir-repo/iq/, installs JAR to ~/.isabelle/.../jedit/jars/
```

### Per-session start

```bash
./start-iq.sh      # launches Isabelle/jEdit; plugin auto-binds 127.0.0.1:8765
```

The token is pinned to `isabelle-local` via `IQ_AUTH_TOKEN`, matching the
`isabelle-iq` entry in `.mcp.json`. Allowed read/write roots are restricted
to the repo root.

### When to prefer I/Q over I/R

| Task | Prefer |
|---|---|
| Quick batch tactic try-out, headless work | I/R |
| Auditing a sorry inventory across a file | I/Q (`get_sorry_positions`) |
| Reading errors/warnings from a slow batch build | I/Q (`get_diagnostics`) |
| Editing a `.thy` and staying in sync with the heap | I/Q (`write_file` is doc-aware) |
| Inspecting proof state at a specific command offset | I/Q (`get_command_info`) |
| Non-invasive Isar trial without persisting | I/Q (`explore`) |

I/Q internally forks its own I/R, so running both servers simultaneously is
fine but the I/R port :9148 only carries the headless daemon — I/Q's REPL
lives on :8765.

### I/Q standing rules

* `authenticate` once per connection with token `isabelle-local`. Required
  before any tool except `tools/list` / `initialize` / `ping`.
* `write_file` modes: `str_replace`, `insert`, line-replace. Prefer
  `str_replace` over blind overwrite — keeps the jEdit document model
  consistent.
* `explore` ≠ `step`. `explore` tries an Isar candidate **without**
  persisting it to any REPL/document; `repl_step` commits.
* If you edit a `.thy` outside I/Q (e.g. via `Edit` tool) → call
  `open_file` then `save_file` once to resync jEdit.
* When jEdit is **not running**, all `isabelle-iq` calls return errors
  immediately. Fall back to `isabelle-ir`.

---

# Isabelle proof pitfalls

## Avoid

* simp loops
* unnamed assumptions
* giant automation blasts
* replacing full proof scripts repeatedly

## Common fixes

* use `subst` instead of global simp rewrites
* use `monoD[OF ...]`
* use `=` not `<->`
* multi-line MCP: write all Isar on one line per `step` call

## Syntax pitfalls

* `(* ... *)` inside quoted strings `"..."` is parsed as HOL, not a comment
* numeral literals cannot be `fun` patterns
* avoid `inv` as pattern name (clashes with `Hilbert_Choice.inv`)
* `ALL j >= n.` invalid — use `ALL j. n <= j --> ...`
* free variable names like `rhs` may clash with imported constants — rename

---

# HOL-IMP notes

* Session parent in `ROOT`: `= "HOL-IMP" +`
* Import with `"HOL-IMP.Com"`, `"HOL-IMP.Big_Step"`, etc.
* Big-step infix: `(c,s) \<Rightarrow> t`
* For existential execution proofs: `apply (rule exI)` before `Assign`/`Seq`
* `sorry` in batch build requires `options [quick_and_dirty]` in `ROOT`

---

# Development loop

1. State lemma
2. Insert `sorry`
3. Check types/build
4. Try automation
5. Split helpers if needed
6. Replace `sorry`
7. Commit only when top-level theorem closed

# Isabelle MCP workflow

Per proof attempt (assumes preflight from `# Isabelle workflow / MCP` done):

1. `isabelle build …` until the session is green.
2. `mcp__isabelle-ir__load_theory` the changed theory; `mcp__isabelle-ir__init`
   a small REPL (unique name, fully-qualified imports).
3. Copy the **subgoal** into a scratch `lemma` / `apply` sequence via
   `mcp__isabelle-ir__step`; run `mcp__isabelle-ir__sledgehammer` (≤ 15s).
4. Paste back `blast` / `auto` / `meson` first; `metis` only if it reconstructs
   fast in batch.
5. If automation fails, write 5–15 lines of Isar and move on; extract a helper
   lemma if the same shape recurs.
6. Mirror the working `step` sequence into the `.thy` file; rebuild to confirm.

---

From the **repository root** (the directory containing `ROOT`):

```bash
isabelle build \
  -d ~/afp/thys \
  -d vendor/td-verification \
  -D . \
  Goblint_Formalization
```

---

# Commit format

```text
feat(proof): <description>
```

---

# Autoformalization pitfalls (Kappelmann et al., arXiv 2604.15713, 2026)

Audit checklist before marking a theorem "done". Distilled from a Claude-Opus-4.6
+ Isabelle/Q case study with three ~2000-line `sorry`-free formalizations. These
are the failure modes that survive batch-build and only surface on review.

## 1. Locale-ordering hazard

Never state `assumes P c` in a locale before `c` is defined. The assumption can
be instantiated with arbitrary terms and a contradiction derived from it. Define
the constant first, then prove `P c` as a lemma, then introduce the locale that
fixes `c` and the proven assumption.

## 2. Instantiation-gap check

Theorems proved inside an abstraction locale (`locale TD_abstract = ...`) are
useless unless instantiated to the concrete object (the actual `make_rhs`, the
actual sign domain). After each `theorem` inside an abstract locale, write the
concrete corollary with `interpretation` / `[where ...]` and surface it as a
named lemma. Missing instantiations are the most common silent gap.

## 3. False-abstraction audit

If a definition or locale parameterises over an order, enumeration, or strategy,
either *prove* abstraction (the result is invariant under the parameter) or
remove the parameter. Don't claim generality you don't have. Persisted across
multiple review rounds in the case study despite explicit feedback.

## 4. Definition–statement alignment

Re-read each theorem statement against the paper / `docs/PROOF_OVERVIEW.md`
wording. Drifts to watch for:

* theorem references the algorithm's *internal annotation set* instead of its
  *output*;
* `coverageTest`-style operational notion smuggled in where the declarative
  notion was intended;
* well-typedness condition on the free variables of an abstraction silently
  dropped.

These are the bugs the proof assistant *cannot* catch.

## 5. Structured Isar over object-level quantifiers

Prefer

```isabelle
lemma foo:
  fixes x :: nat
  assumes "P x"
  shows   "Q x"
```

over

```isabelle
lemma foo: "∀x. P x ⟶ Q x"
```

Structured form is reusable via `[where x = …]` / `[OF ...]`; object-level form
forces every caller to instantiate via `spec` first.

## 6. Persistent `NOTES.md`

Keep a `NOTES.md` (or `docs/AGENT_NOTES.md`) listing: current sorry inventory,
locked design decisions, partial lemmas in progress, recent failed approaches.
The agent reads it at session start to recover from context compaction. Update
it before each commit.

## 7. Use Sledgehammer — really

The case-study agent silently bypassed Sledgehammer and reverted to manual
proof search. Default: try `sledgehammer` first on every non-trivial subgoal.
Paste back `blast` / `auto` / `meson`; use `metis` only if fast in batch.

## 8. Generalization-via-hint recipe

When a proof feels ad hoc or duplicates AFP material, *don't* grind it out.
Hand the agent a reduction to an existing generic theory and ask it to reprove:

* harder TD/warrowing termination → existing AFP fixpoint / well-founded order
  entries;
* minimal-annotation-style covering arguments → AFP independence systems /
  matroids;
* locale-hierarchy design questions → AFP `Order.Lattice_Prelims`, `HOL-Algebra`.

The Kappelmann generalization run cost $11–$93 and a few hours of human time
to replace ad hoc proofs with proofs on top of a standard generic theory.

## 9. Internal review before "done"

After producing a chunk of theorems, run a two-stage internal review:

1. **Self-review**: read every new definition and theorem; check items 1–5.
2. **Simulated peer-review**: imagine a hostile reviewer; what would they
   challenge?

Catches some logical issues. Does **not** replace human review — items 1, 3, 4
slip through the agent's own reviews in the case study.

## 10. One commit per closed top-level theorem

Don't commit a closed sub-lemma while its parent is still `sorry`. The review
discipline above runs per top-level theorem; partial commits break it.
