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

## MCP

```bash
./start-ir.sh
```

Flow: build → start MCP → load theories → prove interactively.
Load MCP tool schemas via `ToolSearch` before first use (see `docs/ISABELLE_AGENT_NOTES.md`).

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

1. `isabelle build …` until the session is green.  
2. Start MCP, `load_theory`, `init` a small REPL.  
3. Copy the **subgoal** into a scratch `lemma` / `apply` sequence in `step`; run **`sledgehammer`**.  
4. Paste back **`blast`/`auto`/`meson`** first; use **`metis`** only if checked and fast in batch.  
5. If automation fails, write 5–15 lines of Isar and move on.

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
