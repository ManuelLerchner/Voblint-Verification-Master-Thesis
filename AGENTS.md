<!-- markdownlint-disable-file MD025 -->

# AGENTS.md

You are a formal proof engineer working with Isabelle/jEdit. Your work is surgical, clearly structured, and well-documented. Step back regularly and ask: Could my proofs be cleaned up, accelerated, or simplified? Could they be broken into smaller lemmas?

**REMEMBER: NEVER create/read/write `.thy` files via host `fs_read`/`fs_write` (`Read`/`Edit`/`Write`). ALWAYS go through the I/Q MCP server (`write_file` / `read_file` / `open_file`). I/R `repl_edit` if jEdit is down.** Exception: the very first creation of a brand-new `.thy` not yet tracked by jEdit follow with `open_file`.

**REMEMBER: Before each proof, ask: short & simple, or not?**

* Short & simple → `by …` or apply-style Isar.
* Not → structured Isar.
* Apply-style: 1–2 tactics at a time, inspect, proceed. Never replace entire scripts.
* Structured Isar: top-down. Sketch with `sorry` placeholders. Fill one at a time. If a `sorry` is complex, hoist it as a separate lemma or open a `proof -` subproof.

**REMEMBER: Comments describe the *current* theory, never its history.**

* No "Option-A/B", "Mirrors X", "IP analogue of X", "previously/formerly/used to", "no longer needs", or references to deleted/retired theories (e.g. `TD_Side_Interface`, `TD_IP_Soundness`, intra-spine names). State what the code does now.
* Comparing to a *still-existing* sibling is fine (`Mirrors cfg_collect_paths`); comparing to a removed one is rot — delete it.
* A "no longer / previously" that describes the *mathematics* (e.g. "after one write the array is no longer the constant array") stays; only project-history framing goes.
* Prefer Isabelle document structure over comment banners: file-header `(* … *)` → `section ‹…›` + `text ‹…›`; `(* -- X -- *)` separators → `subsection ‹X›`. Keep short why-comments as `(* … *)`. Use ASCII `\<open>`/`\<close>` for cartouches.

---

# Project goal

`IMP2 source → (CFG) → equation system → TD solver → sound abstract result → source bridge / mapped back`.

Vendored `TD` solver (stilscher/td-verification) already verified. Proved: CFG
collecting semantics (`cfg_collect`), CFG layer, eqsys soundness, abstract domains
(Sign → Interval → Octagon stretch), pipeline composition, source-to-analysis bridge.
Everything we formalize should stay Goblint-faithful and close to the actual
Goblint repository on GitHub.

---

# Locked decisions

| Topic            | Decision                                             |
| ---------------- | ---------------------------------------------------- |
| Assistant        | Isabelle/HOL, HOL-IMP                                |
| Solver           | vendored `TD` (td-verification)                      |
| Solver interface | `rhs :: pp => (pp => abs_state) => abs_state`        |
| Domains          | Sign → Interval → Octagon (stretch)                  |
| Joins            | `Finite_Set.fold` (needs comm + assoc, finite edges) |
| Order            | `'a::ord` pointwise on states                        |

Open: future IMP vs IMP2 scope only — current code is IMP2.

Decided since v0: CFG layer wins (`Direct_Equations` deleted as P10, off-path); interval instance is already in-tree, with remaining work on precision / termination engineering.

**Live roadmap and backlog: `docs/ROADMAP.md` + [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8).** Issues, dependencies, per-phase status, and Blazy-2013-inspired extensions live there, not in this file.

---

# Repository layout

```
src/IMP2/                  syntax + small-step (README)
src/CFG/                   CFG core (README); Collecting/ — cfg_collect (README); Compiler/ — source-to-CFG compiler correctness (Analysis-free)
src/Analysis/              Voblint_Analysis session
src/Analysis/Instances/    concrete domains and effectful transfer records (README)
src/Analysis/Equations/    constraint systems + soundness (README)
src/Analysis/Solver/       TD solver bridge (README)
src/Formalization/         Voblint_Formalization session
src/Formalization/Pipeline/ end-to-end soundness + source bridge (README)
src/Formalization/Examples/ executable demos (README)
vendor/td-verification/    TD solver (AFP session `TD`, submodule)
vendor/autocorrode/        I/Q + I/R MCP servers (submodule; scripts wire iq/, ir/)
```

`ROOTS` + scattered `ROOT` files define a 4-session DAG: `Voblint_IMP2` → `Voblint_CFG` → `Voblint_Analysis` → `Voblint_Formalization` (see `docs/SESSION_DAG_MIGRATION.md`). Cross-session imports use qualified names (`"Voblint_IMP2.IMP2_Syntax"` etc.). `Voblint_IMP2` adds `Deriving` (executable `linorder` for `aexp`/`bexp`/`edge_action`, so CFG edge enumeration code-generates without a list-built mirror); `Voblint_CFG` adds `Dijkstra_Shortest_Path`; `Voblint_Analysis` adds `TD`. The analysis rides **only** on the side-effecting solver (`TD.TD_side`); the plain top-down solver (`TD.TD_plain`) and its spine were retired (see `docs/TD_SIDE_ONLY_MIGRATION.md`). Top-level theories are the interprocedural side-effecting spine: `Trace_Analysis_Sound`, `Mixed_Flow_Sound`, `TD_Side_Eff_Soundness`, `Sign_Side_Soundness`, `Interval_Side_Soundness`, `Analysis_Sound`, `Compiler_Correctness`, plus `Example_*` witnesses (`Example_Inc_Proc`, `Example_Mixed_Flow_Sign`, `Example_Side_Proc_Global`, `Example_Proc_GraphViz`, `Example_Trace_Digest_Precision`, `Example_Digest_Pipeline_Showcase`, `Example_Interval_Recursion_Convergence`, `Example_Rdiv_Twfr_Sound`, `Example_Mixed_Sign_Interval_GraphViz`). The source-to-analysis bridge is the reusable IMP2-facing endpoint; the end-to-end example instantiations live in the digest showcase and recursive interval flagships. The retained context tower is `TD_Side_Eff_Ctx_Sound` → `TD_Side_Eff_Cmp_Sound` → `Clean_RRead_Sound` → `Seeded_Clean_Ctx_Collect` → `Seeded_Activation_Sound` → `Activation_Witness_From`. The intra-procedural (classical) spine — plain `TD_Soundness`, intra `Sign`/`Interval` analysis, `Pipeline`, the old `Voblint_Formalization` headline theory, intra examples — was extracted to the sibling repo `voblint-formalization-classical` and removed here (see `docs/CLASSICAL_SPINE_RETIREMENT.md`). The intra-only duplication (intra side soundness, the `to_cfg` cone, the intra solver fold, the intra `com` datatype) was then collapsed onto the single IP pipeline; the `com` datatype in `IMP2_Proc.thy` is the extended procedural language (Scope / Call / Restore) used throughout (see `docs/IP_ONLY_CONSOLIDATION.md`).

Docs:

* `docs/PROOF_PHASES.md` — steps, exit criteria, sorry inventory
* `docs/PROOF_OVERVIEW.md` — big picture
* `docs/ROADMAP.md` — live backlog (mirrors GitHub Project 8)
* `docs/NON_GOALS.md` — what the project deliberately does NOT do (each tied to a decision doc)
* `docs/GLOSSARY.md` — project terms with `file:line` references
* `docs/NEXT_STEPS.md`, `docs/OPEN_PROBLEMS.md` — short-horizon + open items
* `docs/HOL_IMP_COMPARISON.md`, `docs/IMP_SYNTAX_NIPKOW_EXTENSION.md`, `docs/cfg-representation.md` — design references
* `docs/ISABELLE_AGENT_NOTES.md` — MCP / Isabelle traps
* `docs/html/` — Isabelle browser info (generated by `make html`)

---

# Proof status

Don't hardcode lemma lists here they drift. Source of truth = the `.thy` files.

```bash
rg -n '^\s*sorry' src/            # live sorry inventory
rg -n '^(lemma|theorem) ' src/    # all declared statements
```

Phases, exit criteria, big-picture plan: `docs/PROOF_PHASES.md`, `docs/PROOF_OVERVIEW.md`.

---

# CFG path infrastructure

`cfg_path` carries actions (needed for transfer-fn composition); `edges_collect` folds actions over store sets. Compound CFGs compile sub-commands at offset `k > 0`, so sub-paths need shifting through `offset_edges k`; the shift is invisible to `edges_collect`. See `src/CFG/CFG_Path.thy` for the predicate + offset infrastructure and the IP collecting layer in `src/CFG/Collecting/`: `CFG_Collect` (`cfg_collect`), `CFG_Collect_Trace` (`cfg_collect_trace`, `alpha_last`), and `CFG_Collect_Runs` (`cfg_runs_to` plus generic collecting introduction lemmas).

**Thesis sentence:** Soundness is stated against interprocedural CFG collecting semantics at **every** program point (`cfg_collect` / `cfg_collect_trace`). The analyzer's post-fixpoint soundly over-approximates that semantics. Terminating IP runs correspond to exit reachability (`cfg_runs_to`); partial and non-terminating behaviour is covered by the trace-level theorem without a final store.

---

# Workflow: MCP first, build to verify

**Default: I/Q (or I/R) for any development.** Read state before editing. Use `explore` to trial-run tactics. **Do not run `isabelle build` while iterating** — build only when the user asks, or once at the end of the complete task or migration.

Why: Isabelle proof state is contextual (locales, assumptions, simp set). Textual edits compile against a different goal than you reasoned about. Read state, then edit. Full-session batch build is slow, hides which command failed, and tempts disk/buffer drift when used as a debug loop.

## Hard rules (agents)

| Do                                                                           | Don't                                                        |
| ---------------------------------------------------------------------------- | ------------------------------------------------------------ |
| `open_file` → `get_diagnostics` / `get_command_info` on the theory you touch | `isabelle build` after every edit or to “see if it compiles” |
| `explore` / `get_context_info` before non-trivial proof changes              | Host `Read`/`Edit`/`Write` on tracked `.thy` files           |
| `write_file` → `save_file` → `normalize_isabelle_ascii.py` → `open_file`     | Assume I/Q buffer == on-disk file without `save_file`        |
| One failing command at a time via I/Q diagnostics                            | Full rebuild to locate a failure I/Q already names by line   |
| Batch build once: user request, CI, or the **complete** task/migration is green in I/Q | Batch build between migration stages or as a substitute for `get_diagnostics` / `explore` |

**If I/Q is up:** debugging a proof or syntax error = I/Q only, until `get_diagnostics` (scope=file, severity=error) is empty on every file you changed.

**If I/Q is down:** say so and ask for `./scripts/start-both.sh` (or `./scripts/start-ir.sh`); use I/R `repl_edit` — still no full build as first resort.

## I/Q loop (per edit)

1. `open_file` (view the theory you edit).
2. `write_file` (`str_replace`, small diff).
3. `save_file` on that path.
4. `python3 scripts/normalize_isabelle_ascii.py <file>` then `open_file` again.
5. `get_diagnostics` (or `get_command_info` on the edited line range).
6. If proof work: `explore` on the failing command; repeat from step 2.

## I/Q recommended pattern (AutoCorrode iq/README)

**Good:** inspect state often (`get_context_info`, `get_command_info`); `explore` before mutating; small proofs; ask current subgoal often; `get_proof_blocks` for scope reads.

**Bad:** blind `sledgehammer`; one-shot huge scripts; rewriting without state inspection; back-to-back `write_file`s without re-reading goal; **`isabelle build` mid-task**.

**Strongly prefer:** `explore`, `get_context_info`, `get_proof_blocks` over direct file edits or batch build.

## When build is appropriate

* User explicitly asks for a build / CI check.
* Final verification after **all** edited theories report no errors in I/Q.
* Heap refresh after large structural change (imports, session `ROOT`, new theory entry).
* Commit gate (CI).

## Claiming work done

**Never claim a proof is fixed based on the I/Q interactive checker alone.** Interactive passes diverge from batch silently. The gate is a clean `isabelle build` output — show the user the green build log before declaring done.

After any `write_file`, re-read the file from disk (or re-run `get_diagnostics`) to confirm the edit persisted. Buffer-sync lag and `save_file` timeouts have caused phantom fixes; verify the disk state before proceeding.

Build command (from repo root, after bootstrap heaps exist):

```bash
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

Always pass `-v` so per-theory progress streams live. Pass `-N` to parallelise within each session. With warm heaps an incremental build touches only the changed session(s) + dependents.

**Bootstrap** (fresh clone, no heaps yet — run once in order):

```bash
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -d src/IMP2 Voblint_IMP2
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -d src/IMP2 -d src/CFG Voblint_CFG
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -d src/IMP2 -d src/CFG -d src/Analysis Voblint_Analysis
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

To build only a sub-layer (e.g., working only on CFG, after bootstrap):

```bash
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_CFG
```

`sorry` in batch needs `options [quick_and_dirty]` in the relevant `ROOT`.

### Build timeout policy

**If the build runs > 40s with warm heaps, assume an infinite loop or a slow `metis`/`smt` reconstruction, not slow compilation.** Top culprits, in order:

* **`metis` / `smt` blow-up** — sledgehammer-suggested `metis [...]` calls that run fast interactively but balloon in batch. Most common cause of build hangs in this repo.
* **`auto` + `elim!` on inductive case rules** — path predicates, grammars, and other large `inductive` libraries; often fine in I/Q, loops in batch.
* `simp` / `auto` / `fastforce` rewriting in both directions.
* A recursive `lemma [simp]` declaration.
* A freshly added congruence / `[intro]` rule that triggers nontermination.

Diagnosis:

1. Don't wait it out — kill the build.
2. Check the streaming `-v` output (or `Monitor` on the task file). The last `Running <Theory> ...` line names the file that hangs; the next silent gap is the stuck command.
3. If `-v` output is ambiguous, rerun with `isabelle build -v -v ...` (extra `-v` shows per-command timings) or open the theory in I/Q and step to the offending lemma.
4. Fix: bound the automation (`simp only:`, narrow `auto simp: ...` lemma set), undo the bad `[simp]`/`[intro]` attribute, or split the proof.

Never bump the build timeout to mask a hang — that hides a real regression and rots into a multi-minute baseline.

### Batch-friendly proof habits

Patterns that keep iteration in I/Q and batch as a one-shot gate:

**Workflow**

* **I/Q inner loop, batch outer gate.** Debug one failing command via `get_diagnostics` / `explore`. Run `isabelle build` once when the complete task or migration is file-clean — not between stages or after tactic changes.
* **I/Q is not completion.** Interactive checking can mark a step finished while subgoals remain, or accept bogus intro rules. Treat empty file diagnostics as “ready for batch”, not “proved”.
* **Batch is completion.** Show a green `-v` log before calling work done.

**Automation that batch tolerates**

* Prefer **small, named case-split or decomposition lemmas** + `by (rule …)` / `cases rule: …` over `auto elim!: …` on inductive predicates.
* Prefer **bounded** tactics: `simp only: …`, `auto simp: …` with an explicit lemma set — not unbounded `simp` / `auto` on large imported rule sets.
* Prefer **structured Isar** (`proof (rule …)` with explicit `show` subgoals) over long `[OF …]` chains when facts must line up exactly.
* When a subgoal resists one line of automation, **hoist a helper lemma** — do not widen `auto`/`simp` to force it.

**Locale and constant shapes**

* Theorems inside locales use locale-qualified constants; callers outside often need the **same global shape** the target lemma expects.
* Before `theorem_callee[OF …]`, check whether premises use **interpretation-local** names vs **fully applied global** names — mismatch fails `OF` even when the mathematics is the same.
* Surface **concrete corollaries** (global definitions, one-line expansion lemmas, or an `interpretation` block) at locale boundaries instead of repeating fragile unfolds at every use site.

**Sledgehammer in batch**

* Default paste-back: `blast`, `auto`, `meson`.
* `metis` / `smt` only after batch confirms they finish quickly — they are a leading hang source.

## ASCII-only `.thy` sources

**Never write unicode Isabelle symbols in `.thy` files.** I/Q's editor tolerates them; `isabelle build` (batch) rejects them with "Inner lexical error". Always use ASCII forms:

| Use                       | Not       |
| ------------------------- | --------- |
| `\<Longrightarrow>`       | `⟹`       |
| `\<Rightarrow>`           | `⇒`       |
| `\<And>`                  | `⋀`       |
| `\<in>`                   | `∈`       |
| `\<not>`                  | `¬`       |
| `\<noteq>`                | `≠`       |
| `\<forall>`               | `∀`       |
| `\<exists>`               | `∃`       |
| `\<le>` / `\<ge>`         | `≤` / `≥` |
| `\<subseteq>`             | `⊆`       |
| `\<union>` / `\<inter>`   | `∪` / `∩` |
| `\<lbrakk>` / `\<rbrakk>` | `⟦` / `⟧` |
| `\<dots>`                 | `…`       |

Unicode in comments is fine. Pre-commit hook (`.git/hooks/pre-commit` → `scripts/check_isabelle_ascii.py`) blocks commits with non-ASCII outside comments.

**I/Q normalises tokens to unicode on write.** Even when you pass ASCII forms (`\<lambda>`, `\<open>`) in `write_file`, I/Q's editor may serialise them back as `λ`, `‹`. After any `write_file` to a `.thy` source, normalise to ASCII and re-sync the buffer:

```bash
python3 scripts/normalize_isabelle_ascii.py <file>
```

then `open_file` again so jEdit picks up the normalised content. Skipping this step means the file looks fine in I/Q but fails the batch build.

---

# MCP servers

Two servers vendored. Config in `.mcp.json` + `.claude/settings.local.json` (`enabledMcpjsonServers`). Token: `isabelle-local`.

| Server        | Port | When                                                                                                                   |
| ------------- | ---- | ---------------------------------------------------------------------------------------------------------------------- |
| `isabelle-iq` | 8765 | jEdit running doc-aware: diagnostics, sorry positions, `explore`, `get_context_info`, structured edits. **Preferred.** |
| `isabelle-ir` | 9148 | jEdit not running headless REPL: `step`, `sledgehammer`, `find_theorems`.                                              |

Start: `./scripts/start-both.sh` (I/Q + I/R together preferred), `./scripts/start-iq.sh` (jEdit + I/Q only), or `./scripts/start-ir.sh` (headless REPL only).

## Standing rules

* Authenticate I/Q or connect I/R with `token=isabelle-local` before other server calls. Report a connection failure when an actual call fails; do not run a separate availability probe.
* **Always edit `.thy` via I/Q `write_file`** (or I/R `repl_edit`). Never use the host `Edit`/`Write` tool on `.thy` files jEdit's buffer caches stale content even after `open_file`, so subsequent `read_file` / diagnostics / `explore` run against the old text.
  * Exception: the very first creation of a brand-new `.thy` not yet tracked by jEdit. Follow with `open_file` so jEdit picks it up.
  * Recovery if you slipped and used `Edit`: re-issue the same change via I/Q `write_file str_replace` to sync the buffer.
* I/Q `write_file`: prefer `str_replace` over `line`/`insert` minimal diff keeps the doc model consistent.
* I/R: after `.thy` edit → `load_theory(<FQN>)` to re-sync heap.
* I/R `init` uses fully-qualified imports, e.g. `Voblint_CFG.CFG_Collect`.
* I/R `step` one Isar line per call.
* `sledgehammer` timeout ≤ 15s. Paste back `blast` / `auto` / `meson`. `metis`/`smt` only if fast in batch.
* `nitpick` via `step`: `lemma … nitpick [timeout=5] oops`.
* `explore` ≠ `repl_step`. `explore` does not persist; `repl_step` commits.
* `explore query='proof'` needs `Isar_Explore` imported. Session-qualified `src/` lives in session `Voblint_Formalization`, so unqualified `Isar_Explore` resolves wrong. `sledgehammer` / `find_theorems` queries don't need the import.

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
* Free vars may resolve to imported constants. `c` is especially risky because
  `Dijkstra_Shortest_Path` imports an edge-cost constant `c`; bind intended
  variables with `fixes` or rename them (`ctx`, `cmd`, `cost`) before debugging
  strange type errors.
* Don't use Isar keywords (`back`, `prefer`, `defer`, `then`, `with`, `also`, `finally`) as `have`/`obtain` labels. `back` → cryptic "proposition expected, end-of-input" past the line.
* `induction … rule: big_step.induct` binds case patterns in **textual** order of the rule, not conclusion order. Wrong order → type-clash (store typed as `com`). HOL-IMP IfTrue / IfFalse / WhileTrue: read rule body.

**HOL-IMP:**

* `ROOT` parent: `= "HOL-IMP" +`. Imports: `"HOL-IMP.Com"`, `"HOL-IMP.Big_Step"`.
* Big-step infix: `(c,s) ⇒ t`. Existential exec: `apply (rule exI)` before `Assign`/`Seq`.

---

# Searching (rg vs grep)

`rg` never rewrites matched text. If `rg` and `grep -R` disagree on hit counts, the cause is **default filtering**, not corruption: `rg` skips `.gitignore`d and hidden paths by default, `grep -R` searches everything. In this repo the gap is usually `.claude/worktrees/` (a git worktree, ignored) and `.git/`.

* Trust `rg`. Don't switch to `grep` because counts differ — widen `rg` instead.
* `rg --no-ignore PAT` — include `.gitignore`d files.
* `rg -uu PAT` — include ignored **and** hidden (matches `grep -R` coverage, plus `.git/`).
* `rg -uu --glob '!.git' PAT` — everything except `.git/`.

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

1. **Locale ordering.** Never `assumes P c` before `c` is defined assumption can be instantiated to derive contradictions. Define → prove `P c` as lemma → introduce locale with proven assumption.
2. **Instantiation gap.** Theorems inside abstract locales are useless without `interpretation` / `[where …]` to the concrete object. Surface concrete corollaries as named lemmas. Most common silent gap.
3. **False abstraction.** Parameters over orders/enumerations/strategies must be either *proven* invariant or removed. Don't claim generality you don't have.
4. **Definition–statement drift.** Re-read statements vs `docs/PROOF_OVERVIEW.md`. Watch: theorem about *internal annotations* vs *output*; operational `coverageTest` smuggled into declarative claim; dropped well-typedness condition. Proof assistant can't catch these.
5. **Structured Isar over `∀x. P x ⟶ Q x`.** Use `fixes x assumes "P x" shows "Q x"`. Reusable via `[where x=…]` / `[OF …]`.
6. **Use sledgehammer really.** Default: try `sledgehammer` first on every non-trivial subgoal. Paste back `blast`/`auto`/`meson`; `metis` only if reconstructs fast.
7. **Generalisation via hint.** Ad-hoc proofs duplicating AFP material → reduce to existing generic theory (AFP fixpoint / well-founded; independence systems / matroids; `Order.Lattice_Prelims`, `HOL-Algebra`).
8. **Two-stage review before done.** (a) Self-review items 1–5. (b) Simulated hostile peer review. Does not replace human review 1, 3, 4 slip through agent reviews.

Proof status lives in `docs/PROOF_PHASES.md` (sorry inventory) do not duplicate lemma lists in this file.

---

# Accuracy & Verification

**Never assert facts about analyzer behavior, paper contents, or proof correctness without first verifying against the repo or source.** Flag uncertainty explicitly ("I believe X — verify against `src/Y`") rather than stating it as fact.

Specific cases that require a source lookup before claiming:

* "inherits correctness" or "soundness follows from …"
* Quoted paper passages or attributed claims
* "Real analyzers also …" statements about VobLint behavior
* Whether a particular lemma or definition exists in a given theory
