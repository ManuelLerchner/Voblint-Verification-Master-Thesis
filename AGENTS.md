<!-- markdownlint-disable-file MD025 -->

# AGENTS.md

You are a formal proof engineer working with Isabelle/jEdit. Your work is surgical, clearly structured, and well-documented. Step back regularly and ask: Could my proofs be cleaned up, accelerated, or simplified? Could they be broken into smaller lemmas?

**REMEMBER: NEVER create/read/write `.thy` files via host `fs_read`/`fs_write` (`Read`/`Edit`/`Write`). ALWAYS go through the I/Q MCP server (`write_file` / `read_file` / `open_file`). I/R `repl_edit` if jEdit is down.** Exception: the very first creation of a brand-new `.thy` not yet tracked by jEdit — follow with `open_file`.

**REMEMBER: Before each proof, ask: short & simple, or not?**

* Short & simple → `by …` or apply-style Isar.
* Not → structured Isar.
* Apply-style: 1–2 tactics at a time, inspect, proceed. Never replace entire scripts.
* Structured Isar: top-down. Sketch with `sorry` placeholders. Fill one at a time. If a `sorry` is complex, hoist it as a separate lemma or open a `proof -` subproof.

---

# Project goal

`IMP AST → (CFG) → equation system → TD solver → sound abstract result → mapped back`.

Vendored `TD` solver (stilscher/td-verification) already verified. To prove: IMP collecting semantics, CFG layer, eqsys soundness, abstract domains (Sign → Interval → Octagon), pipeline composition.

---

# Locked decisions

| Topic            | Decision                                      |
| ---------------- | --------------------------------------------- |
| Assistant        | Isabelle/HOL, HOL-IMP                         |
| Solver           | vendored `TD` (td-verification)               |
| Solver interface | `rhs :: pp => (pp => abs_state) => abs_state` |
| Domains          | Sign → Interval → Octagon (stretch)           |
| Joins            | `Finite_Set.fold` (needs comm + assoc, finite edges) |
| Order            | `'a::ord` pointwise on states                 |

Open: direct AST→eqsys (`Direct_Equations`) vs CFG layer; interval stretch; IMP vs IMP2.

---

# Repository layout

```
src/IMP2/        syntax + semantics + collecting
src/CFG/         CFG + paths + CFG collecting
src/Domains/     abstract domains
src/Equations/   constraint systems + soundness
src/Examples/    executable sign analysis
src/Solver/      TD solver interface, TD_Total.thy
src/Pipeline/    end-to-end
```

Plans: `docs/PROOF_PHASES.md` (steps, exit criteria, sorry inventory). `docs/PROOF_OVERVIEW.md` (big picture).

---

# Proof status

Don't hardcode lemma lists here — they drift. Source of truth = the `.thy` files.

```bash
rg -n '^\s*sorry' src/            # live sorry inventory
rg -n '^(lemma|theorem) ' src/    # all declared statements
```

Phases, exit criteria, big-picture plan: `docs/PROOF_PHASES.md`, `docs/PROOF_OVERVIEW.md`.

---

# CFG path infrastructure

`cfg_path` carries actions (needed for transfer-fn composition); `path_collect` folds actions over store sets. Compound CFGs compile sub-commands at offset `k > 0`, so sub-paths need shifting through `offset_edges k` — the shift is invisible to `path_collect`. See `src/CFG/CFG_Path.thy` for the predicate + offset infrastructure and `src/CFG/CFG_Collecting.thy` for the big-step ↔ CFG bridge.

---

# Workflow: MCP first, build to verify

**Default: I/Q (or I/R) for any development.** Read state before editing. Use `explore` to trial-run tactics. Build only to confirm closed work or refresh the heap.

Why: Isabelle proof state is contextual (locales, assumptions, simp set). Textual edits compile against a different goal than you reasoned about. Read state, then edit.

## I/Q recommended pattern (AutoCorrode iq/README)

**Good:** inspect state often (`get_context_info`, `get_command_info`); `explore` before mutating; small proofs; ask current subgoal often; `get_proof_blocks` for scope reads.

**Bad:** blind `sledgehammer`; one-shot huge scripts; rewriting without state inspection; back-to-back `write_file`s without re-reading goal.

**Strongly prefer:** `explore`, `get_context_info`, `get_proof_blocks` over direct file edits.

## When build is appropriate

* Final verification of a closed top-level theorem.
* Heap refresh after large structural change.
* CI / commit gate.

Build command (from repo root):

```bash
isabelle build -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization
```

`sorry` in batch needs `options [quick_and_dirty]` in `ROOT`.

## ASCII-only `.thy` sources

**Never write unicode Isabelle symbols in `.thy` files.** I/Q's editor tolerates them; `isabelle build` (batch) rejects them with "Inner lexical error". Always use ASCII forms:

| Use            | Not    |
|----------------|--------|
| `\<Longrightarrow>` | `⟹` |
| `\<Rightarrow>` | `⇒`   |
| `\<And>`        | `⋀`   |
| `\<in>`         | `∈`   |
| `\<not>`        | `¬`   |
| `\<noteq>`      | `≠`   |
| `\<forall>`     | `∀`   |
| `\<exists>`     | `∃`   |
| `\<le>` / `\<ge>` | `≤` / `≥` |
| `\<subseteq>`   | `⊆`   |
| `\<union>` / `\<inter>` | `∪` / `∩` |
| `\<lbrakk>` / `\<rbrakk>` | `⟦` / `⟧` |
| `\<dots>`       | `…`   |

Unicode in comments is fine. Pre-commit hook (`.git/hooks/pre-commit` → `scripts/check_isabelle_ascii.py`) blocks commits with non-ASCII outside comments.

---

# MCP servers

Two servers vendored. Config in `.mcp.json` + `.claude/settings.local.json` (`enabledMcpjsonServers`). Token: `isabelle-local`.

| Server      | Port | When                                                |
|-------------|------|-----------------------------------------------------|
| `isabelle-iq` | 8765 | jEdit running — doc-aware: diagnostics, sorry positions, `explore`, `get_context_info`, structured edits. **Preferred.** |
| `isabelle-ir` | 9148 | jEdit not running — headless REPL: `step`, `sledgehammer`, `find_theorems`. |

Start: `./start-iq.sh` (full I/Q + REPL) or `./start-ir.sh` (REPL only).

## Preflight (per session)

1. Probe server up. If down → ask user to run `./start-iq.sh` / `./start-ir.sh`.
2. Load tool schemas via `ToolSearch select:mcp__isabelle-iq__authenticate,…` (or `…ir__connect,…`).
3. `authenticate` (I/Q) or `connect` (I/R) with `token=isabelle-local`. All other calls fail until authenticated.

## Standing rules

* **Always edit `.thy` via I/Q `write_file`** (or I/R `repl_edit`). Never use the host `Edit`/`Write` tool on `.thy` files — jEdit's buffer caches stale content even after `open_file`, so subsequent `read_file` / diagnostics / `explore` run against the old text.
  * Exception: the very first creation of a brand-new `.thy` not yet tracked by jEdit. Follow with `open_file` so jEdit picks it up.
  * Recovery if you slipped and used `Edit`: re-issue the same change via I/Q `write_file str_replace` to sync the buffer.
* I/Q `write_file`: prefer `str_replace` over `line`/`insert` — minimal diff keeps the doc model consistent.
* I/R: after `.thy` edit → `load_theory(<FQN>)` to re-sync heap.
* I/R `init` uses fully-qualified imports, e.g. `Goblint_Formalization.CFG_Collecting`.
* I/R `step` — one Isar line per call.
* `sledgehammer` timeout ≤ 15s. Paste back `blast` / `auto` / `meson`. `metis`/`smt` only if fast in batch.
* `nitpick` via `step`: `lemma … nitpick [timeout=5] oops`.
* `explore` ≠ `repl_step`. `explore` does not persist; `repl_step` commits.
* `explore query='proof'` needs `Isar_Explore` imported. Scratch file: `src/Scratch_Explore.thy` (imports `"iq.Isar_Explore"`). Session-qualified — `src/` lives in session `Goblint_Formalization`, so unqualified `Isar_Explore` resolves wrong. `sledgehammer` / `find_theorems` queries don't need the import.

Traps: `docs/ISABELLE_AGENT_NOTES.md`.

---

# Isabelle pitfalls

**Avoid:** simp loops; unnamed assumptions; giant automation blasts; full-script rewrites.

**Fixes:** `subst` instead of global simp; `monoD[OF …]`; `=` not `↔`; one Isar line per MCP `step` call.

**Syntax:**

* `(* … *)` inside `"…"` is HOL, not a comment.
* Numeral literals can't be `fun` patterns.
* `inv` clashes with `Hilbert_Choice.inv`.
* `ALL j >= n.` invalid → `ALL j. n <= j --> …`.
* Free vars like `rhs` may shadow imported constants — rename.
* Don't use Isar keywords (`back`, `prefer`, `defer`, `then`, `with`, `also`, `finally`) as `have`/`obtain` labels. `back` → cryptic "proposition expected, end-of-input" past the line.
* `induction … rule: big_step.induct` binds case patterns in **textual** order of the rule, not conclusion order. Wrong order → type-clash (store typed as `com`). HOL-IMP IfTrue / IfFalse / WhileTrue: read rule body.

**HOL-IMP:**

* `ROOT` parent: `= "HOL-IMP" +`. Imports: `"HOL-IMP.Com"`, `"HOL-IMP.Big_Step"`.
* Big-step infix: `(c,s) ⇒ t`. Existential exec: `apply (rule exI)` before `Assign`/`Seq`.

---

# Development loop

1. State lemma, insert `sorry`.
2. Open in MCP; read current goal via `get_context_info`.
3. Trial tactics with `explore` / `sledgehammer`.
4. Commit working tactic to `.thy`.
5. Split helpers when complexity grows.
6. Replace `sorry`.
7. Final `isabelle build` to confirm.

---

# Autoformalization audit (Kappelmann et al., 2026)

Run before declaring a theorem done. These survive batch-build.

1. **Locale ordering.** Never `assumes P c` before `c` is defined — assumption can be instantiated to derive contradictions. Define → prove `P c` as lemma → introduce locale with proven assumption.
2. **Instantiation gap.** Theorems inside abstract locales are useless without `interpretation` / `[where …]` to the concrete object. Surface concrete corollaries as named lemmas. Most common silent gap.
3. **False abstraction.** Parameters over orders/enumerations/strategies must be either *proven* invariant or removed. Don't claim generality you don't have.
4. **Definition–statement drift.** Re-read statements vs `docs/PROOF_OVERVIEW.md`. Watch: theorem about *internal annotations* vs *output*; operational `coverageTest` smuggled into declarative claim; dropped well-typedness condition. Proof assistant can't catch these.
5. **Structured Isar over `∀x. P x ⟶ Q x`.** Use `fixes x assumes "P x" shows "Q x"`. Reusable via `[where x=…]` / `[OF …]`.
6. **Use sledgehammer — really.** Default: try `sledgehammer` first on every non-trivial subgoal. Paste back `blast`/`auto`/`meson`; `metis` only if reconstructs fast.
7. **Generalisation via hint.** Ad-hoc proofs duplicating AFP material → reduce to existing generic theory (AFP fixpoint / well-founded; independence systems / matroids; `Order.Lattice_Prelims`, `HOL-Algebra`).
8. **Two-stage review before done.** (a) Self-review items 1–5. (b) Simulated hostile peer review. Does not replace human review — 1, 3, 4 slip through agent reviews.

Proof status lives in `docs/PROOF_PHASES.md` (sorry inventory) — do not duplicate lemma lists in this file.
