# attempt2 — backward from the TD solver (small steps only)

This folder is a **sandbox**: prove tiny lemmas here first, then port winners into the main tree when stable.

## Direction

We walk **backward from the AFP top-down solver** toward the program. Each step below is meant to be **one file / one lemma cluster**, provable without the hardest bridge lemmas (`post_fixpoint_sound`, `cfg_collect_exit_eq_collect`, …).

## Where the solver actually is (and where Step 0 fits)

The **AFP connection** lives in `Solver/TD_Interface.thy`:

- `td_analyse` builds `make_rhs_tree`, calls `TD_plain_Interp_solve`, reads back an environment (`lookup_bot` / `env_map`).
- **`td_analyse_post_fixpoint`** is the lemma that says that environment satisfies your **`is_post_fixpoint`** from `Equations/Constraint_System.thy` (same shape the TD paper uses: stable / queried unknowns satisfy the equation w.r.t. the returned map).

So: **the solver does not use `lfp_lowerbound` directly.** It gives you a **post-fixpoint of your RHS**. The AFP proof is in `TD.TD_plain` once your RHS is packaged as their strategy tree and meets their hypotheses.

**`Attempt2_Step0.thy` is not wired to `TD_plain` yet.** It only records the *other* standard Knaster–Tarski move you will need **on the collecting-semantics side** (`CFG_Collecting.cfg_collect` as an `lfp`): “prefixed point ⇒ above least fixpoint.” That is the same inequality pattern as `lfp_lowerbound`, but applied later in `Constraint_System_Sound` / `CFG_Collecting`, not inside `TD_plain`.

**End-to-end picture:**

1. **Solver (AFP → your interface):** `make_rhs_tree` / `traverse_rhs` = `rhs` ⇒ `td_analyse_post_fixpoint` ⇒ `is_post_fixpoint … (td_analyse …)`.  
2. **Collecting semantics (your CFG):** `cfg_collect` as `lfp` ⇒ use Step-0-style reasoning to relate that `lfp` to `gamma_state ∘ env` (this becomes `post_fixpoint_sound` and friends).  
3. **Pipeline:** combine (1) + (2) + big-step / reachability lemmas.

Step 0 is preparation for **(2)**. Steps 1–4 in this plan are what connect **backward toward (1)**.

## Minimal function chain (what actually gets composed)

This is the **smallest** chain that matches `TD_Interface.thy` + `Constraint_System.thy` (names only; type parameters omitted where obvious).

### A. Build the CFG from the command

| Step | Function / def | Role |
|------|------------------|------|
| A1 | `to_cfg :: com => cfg` | AST → graph `g` with `cfg_edges g`, `cfg_entry g`, `cfg_exit g`. |

### B. One unknown’s right-hand side (functional style, what soundness talks about)

| Step | Function / def | Role |
|------|------------------|------|
| B1 | `rhs g tf join_abs bot_abs s0` — type `(pp => 'a abs_state) => pp => 'a abs_state` | Join of predecessor contributions + `s0` at entry (`Constraint_System.thy`). |
| B2 | `make_rhs g tf join_abs bot_abs s0 v env = rhs g tf join_abs bot_abs s0 env v` | Curried wrapper for TD / monotone statements (`TD_Interface.thy`). |

Post-fixpoint predicate (whole map):

- `is_post_fixpoint g tf join_abs bot_abs s0 env` means `forall v. rhs g tf join_abs bot_abs s0 env v <= env v` (`Constraint_System.thy`).

### C. Same RHS in AFP strategy-tree form (solver input)

| Step | Function / def | Role |
|------|------------------|------|
| C1 | `make_rhs_tree g tf join_abs bot_abs s0 :: pp => (pp, 'a abs_state) strategy_tree` | For each unknown `v`, a tree that queries predecessors and folds `join_abs` / `apply_tf` (`TD_Interface.thy`). |
| C2 | `env_map env` | Turns `pp => abs_state` into the partial map the traverser expects. |
| C3 | `traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) (env_map env)` | **Must equal** `make_rhs … v env` — lemma `make_rhs_tree_correspondence`. |

### D. Run the AFP top-down interpreter

| Step | Function / def | Role |
|------|------------------|------|
| D1 | `TD_plain_Interp_solve T v0` with `T = make_rhs_tree g tf join_abs bot_abs s0` and `v0 = cfg_entry g` | Produces partial map `sigma` (`TD_Interface.thy`; proof in `TD.TD_plain`). |
| D2 | `lookup_bot sigma v` | Read abstract state at `v`, default `bot` if unknown not in map. |

### E. Public “run analysis” API

| Step | Function / def | Role |
|------|------------------|------|
| E1 | `td_analyse c tf join_abs bot_abs s0 v = lookup_bot (TD_plain_Interp_solve (make_rhs_tree (to_cfg c) tf join_abs bot_abs s0) (cfg_entry (to_cfg c))) v` | Full chain (`TD_Interface.thy`). |
| E2 | `run_analysis cfg c` in `Pipeline.thy` | Instantiates `tf` / join / bot / init from a config record, then `td_analyse`. |

### F. Where collecting semantics and Step 0 enter (separate chain)

| Step | Function / def | Role |
|------|------------------|------|
| F1 | `cfg_collect g S` — type `pp => store set` | Least fixpoint of the **concrete** edge-collecting step (`CFG_Collecting.thy`). |
| F2 | `cfg_reach g S` = `cfg_collect g S` | Alias for stating “stores reachable at `v`”. |
| F3 | `post_fixpoint_sound` | Links `is_post_fixpoint` + transfer soundness to `cfg_reach g S v <= gamma_state (env v)` (`Constraint_System_Sound.thy`). |
| F4 | `Attempt2_Step0` | Reusable **lfp lower bound** pattern for (F1) once you have a suitable prefixed point on `λv. gamma_state (env v)`. |

**One-line dependency for “solver works”:** prove **C3** + AFP hypotheses, then **D1** gives a map whose `lookup_bot` satisfies the solver’s post-fixpoint notion; rewrite that to **B**’s `is_post_fixpoint` (**`td_analyse_post_fixpoint`**).

**One-line dependency for “result sound w.r.t. collecting”:** prove **F3** (and lemmas it needs), using **F4**-style reasoning on **F1**, *after* you already have `is_post_fixpoint` for `env = td_analyse …` from the solver chain.

## Step 0 — Knaster–Tarski template (`Attempt2_Step0.thy`)

**Status:** done in Isabelle (see theory).

**Point:** isolate the one-line `lfp_lowerbound` reasoning so later `cfg_collect` proofs reuse the same pattern without mixing in TD or CFG.

## Step 1 — `rhs` on empty predecessors

**Goal:** a lemma of the shape: if node `v` has no incoming edges (and is not the entry), then `rhs … v = bot_abs` (or your fold’s neutral element).

**Why:** pure `Finite_Set.fold` + `abs_join_set` algebra; no solver, no collecting semantics.

**Where to move later:** `Equations/Constraint_System.thy` (or stay here and `import` into main later).

## Step 2 — monotonicity slice for `rhs`

**Goal:** prove `rhs_mono` **or** a minimal special case (e.g. only `join_abs` monotone in the first argument + `apply_tf` monotone) that your AFP bridge actually needs.

**Why:** `TD_Interface.make_rhs_mono` depends on this; without it the solver connection stays on `sorry`.

**Where:** `Equations/Constraint_System.thy`.

## Step 3 — tree = fold = `rhs` (solver side, still no IMP soundness)

**Goals (in order):**

1. `rhs_tree_fold_traverse_env_map` in `TD_Interface.thy`  
2. `make_rhs_tree_preds_list` (finite edges ⇒ distinct list for the fold)  
3. `make_rhs_tree_correspondence`  

**Why:** this is exactly “AFP TD sees the same RHS as our functional `rhs`”.

**Where:** `Solver/TD_Interface.thy`.

## Step 4 — `td_analyse_post_fixpoint`

**Goal:** discharge `TD_Interface.td_analyse_post_fixpoint` using AFP `TD_plain` + Step 3.

**Where:** `Solver/TD_Interface.thy`.

## Step 5+ — soundness vs collecting / pipeline

**Only after Steps 1–4 are solid:** `Constraint_System_Sound`, `CFG_Collecting`, `TD_Soundness`, `Pipeline`.

Those steps stay **out of attempt2** until the solver chain is real; otherwise we repeat the old “big sorry wall”.

## Rules for this folder

- Prefer **one lemma per PR-sized change**.
- If a step needs a new definition, duplicate minimally in `attempt2` first; merge to `src/` only when the proof is closed.
- Keep every new theory building in session `Goblint_Formalization` (listed in `ROOT`).
