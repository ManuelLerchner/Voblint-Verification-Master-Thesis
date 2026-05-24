# Isabelle / MCP notes

Companion to `AGENTS.md`. Project-specific traps only.

## Build

```bash
isabelle build -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization
```

- Solver session is **`TD`** from `vendor/td-verification` (not a separate AFP `Top_Down_Solver` path).
- `sorry` in batch needs `options [quick_and_dirty]` in `ROOT`.
- Run `make vendor` before the first build if `vendor/td-verification` is missing.

## MCP (I/R)

- HTTP MCP: `localhost:9148`; REPL `connect` uses TCP **`9147`** (not 9148).
- After disk edits: `load_theory` with fully qualified names (`Goblint_Formalization.CFG_Runs_To_Bridge`).
- `step`: one Isar line per call.
- Prefer `blast` / `auto` / `meson` from sledgehammer; verify `metis` with a full build.

## Sledgehammer

1. Shrink the goal first (`unfolding`, `monoI`, controlled `simp`) ATP rarely closes huge goals in one shot.
2. Prefer `by auto` / `blast` / `fastforce` / `simp` over `metis`/`smt` for batch speed and maintainability.
3. **`metis` caution:** reconstruction can be very slow in `isabelle build` and may pull surprising lemmas. Always run a full session build after pasting `metis`; fall back to Isar or `meson`/`blast` with explicit `simp`/`intro`/`dest` if stuck.
4. Keep timeout ≤ 15s unless debugging interactively.

## Isar traps

- Edit `.thy` via I/Q `write_file`, not host `Read`/`Write` (jEdit buffer drift).
- ASCII symbols in `.thy` only (`\<Longrightarrow>`, not `⟹`) batch rejects Unicode.
- **`obtain` + `show`:** if Isabelle reports “Result contains obtained parameters”, use `have` for intermediate facts; only the final case goal uses `show`.
- **`induction … arbitrary: S T` with named `assumes`:** the assumption may become a meta-implication not in the case context. Use an object implication `S ⊆ T ⟹ …` with `assume le: "S ⊆ T"` in cases, or derive `⋀u. rho1 u ⊆ rho2 u` from `rho1 ≤ rho2` via `le_fun_def`.
- Set comprehensions: `{s ∈ S. P s}` plus `fix s` can clash; prefer `fix x` in `subsetI` or `Collect (λs. s ∈ S ∧ P s)` with `mem_Collect_eq`.
- `path_collect` heads are `(edge_action * pp)` pairs `cases`/`obtain` before `simp`.
- `induction … rule: big_step.induct`: case order follows the rule text, not the conclusion.

## CFG-specific lemmas

- **`edge_collect_mono`:** monotonicity in the state-set argument; `subset_iff`, `mem_Collect_eq`, or `meson` after pointwise `rho1 u ⊆ rho2 u`.
- **`collect_pp_mono`:** unfold `collect_pp_def`, pointwise `cenv` order (`le_fun_def`), then `edge_collect_mono` and a Union step (`blast` once the `⋀u a.` helper is named).

## Workflow

1. `isabelle build …` until green (or expected sorries only).
2. MCP: `load_theory`, small REPL `init`.
3. Trial tactics in `step` / `explore`; paste `blast`/`auto`/`meson` first.
4. If automation fails, 5–15 lines of structured Isar; hoist hard subgoals as lemmas.

CFG maintenance: `docs/walkthrough/cfg/collecting/index.html` and `src/CFG/Collecting/README.md`.
