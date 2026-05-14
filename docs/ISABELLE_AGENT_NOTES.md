# Isabelle / MCP notes for agents

Practical findings from working on this repo (CFG collecting semantics, monotonicity lemmas, Cursor Isabelle MCP). Use together with `AGENTS.md` and `README.md`.

## Batch build

- Session **`TD`** comes from **`vendor/td-verification`** (see `start-ir.sh`). Build from the repo root with **both** `-d` paths, for example:
  - `isabelle build -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization`
- Do **not** point `-d` only at `.../Top_Down_Solver` unless your `ROOT` actually imports that session name; this project’s `ROOT` imports **`TD`** from the vendor tree.
- **`sorry`** requires `options [quick_and_dirty]` in `ROOT` (already set).

## Isabelle MCP (I/R)

- **Connect** first (`connect` with token, e.g. `isabelle-local` from `start-ir.sh`).
- After **editing theories on disk**, call **`load_theory`** on the changed theory so the REPL matches the file (the heap may lag otherwise).
- **`init`** creates a REPL with an explicit import list; use fully qualified theory names (e.g. `Goblint_Formalization.CFG_Collecting`).
- **`step`**: prefer **one line of Isar per call** if the server rejects newlines.
- **ASCII in `step` text**: the MCP server may normalize escapes; when in doubt, use Isabelle’s `\<...>` spellings consistent with your `.thy` files.

### Which tools exist

| Tool | Role |
|------|------|
| `sledgehammer` | ATP on **current** proof state; default timeout 15s is enough for most subgoals. |
| `find_theorems` | Search library / loaded theories. |
| `step` | Run Isar commands (including **`nitpick`** as an ordinary command in theory text). |

There is **no separate MCP tool named `nitpick`**. To run Nitpick, use **`step`** with something like `lemma ... nitpick [timeout = 5] oops` (or inside a proof).

## Sledgehammer: how to use it well

1. **Shrink the goal first**  
   `unfolding` definitions, `apply (rule monoI)`, `simp` (controlled) — Sledgehammer rarely closes huge first-order goals in one shot.

2. **Prefer light tactics from the menu**  
   When Sledgehammer reports `by auto`, `by blast`, `by fastforce`, or `by simp`, those are usually **better for the repo** than `metis`/`smt`: faster batch rebuilds, smaller proof terms, easier maintenance.

3. **`metis` caution**  
   A reported `metis` proof can (a) **reconstruct very slowly** in `isabelle build`, (b) pull in **surprising lemmas** that happen to unify. Always run a **full session build** after pasting a `metis` proof. If the build hangs or the proof looks unrelated, fall back to structured Isar or `meson`/`blast` with explicit `simp`/`intro`/`dest`.

4. **Timeouts**  
   Keep Sledgehammer at the recommended **≤ 15s** unless you are debugging interactively; long runs rarely beat “one more `unfold` + blast”.

5. **Induction + Sledgehammer**  
   For `induction … arbitrary: …`, Sledgehammer often finds `apply simp` **per subgoal**; you still need the right **induction rule** and sometimes a **manual `Cons` case** (e.g. product types in `fun` equations).

## Isar proof engineering (concrete traps)

### `obtain` and `show`

If Isabelle reports **“Result contains obtained parameters”**, you likely used **`show`** for an intermediate fact that still mentions the obtained locals. Use **`have`** for the intermediate step, then a **single** final `show` for the case goal.

### `induction` with `arbitrary: S T` and named `assumes`

With `proof (induction es arbitrary: S T)` and a lemma of the form `assumes "S ⊆ T" shows …`, the induction may turn the assumption into a **meta-implication** `S ⊆ T ⟹ …` where the outer `assumes` name is **not** in the case context. Fixes that work:

- State the strong lemma as an **object implication** `S ⊆ T ⟹ …` and use `assume le: "S ⊆ T"` inside the `Nil` case, or  
- Derive **`have ru: ⋀u. rho1 u ⊆ rho2 u`** from `rho1 ≤ rho2` via `le_fun_def` and reuse it (good for `mono` proofs).

### Set comprehension and bound variables

- `{s ∈ S. P s}` plus `fix s` in a proof can cause awkward parsing / clashes. Prefer **`fix x`** in `subsetI` proofs, or use **`Collect (λs. s ∈ S ∧ P s)`** and `mem_Collect_eq` / `auto simp: …` for stable automation.
- Mixing **`:`** and **`∈`** for membership: pretty-printing may show `∈` while your script uses `:``; if `simp` stalls, align with `Collect` + `mem_Collect_eq` or unfold the `fun` equation explicitly.

### `path_collect` and products

`path_collect` is defined on **`(edge_action * pp) # es`**, not on an arbitrary cons unless you know the head is a pair. Proofs often need **`obtain a p where e = (a, p)`** (or `cases e`) before `simp`/`auto` can apply the rewrite rule.

## Project-specific lemmas (memory)

- **`edge_collect_mono`**: monotonicity w.r.t. the **state set** argument; assume / Collect cases benefit from `subset_iff`, `mem_Collect_eq`, or `meson` after pointwise `rho1 u ⊆ rho2 u`.
- **`collect_pp_mono`**: `mono (λrho. collect_pp g rho v)` — unfold `collect_pp_def`, use pointwise order on `cenv` (`le_fun_def`), then `edge_collect_mono` and a **Union** / membership step (`blast` works well once the `⋀u a.` helper is named).

## Suggested workflow

1. `isabelle build …` until the session is green.  
2. Start MCP, `load_theory`, `init` a small REPL.  
3. Copy the **subgoal** into a scratch `lemma` / `apply` sequence in `step`; run **`sledgehammer`**.  
4. Paste back **`blast`/`auto`/`meson`** first; use **`metis`** only if checked and fast in batch.  
5. If automation fails, write 5–15 lines of Isar and move on.

These notes are **not** a substitute for the knowledge base (`~/goblint-formalization-kb/`) or AFP documentation; they record agent-time sinks we hit in this repository.
