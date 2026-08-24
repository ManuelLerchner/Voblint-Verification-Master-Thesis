# From AST to solved abstract result

How a source program becomes a solved abstract state, end to end. Every stage
below names the real constant and its `file:line`, and the companion Python model
in `demo/voblint_pipeline/` reimplements each function so you can execute and
debug the same computation.

```
IMP2 com  ──compile──▶  CFG  ──side_cfg_T_eff──▶  equation system  ──solver──▶  post-fixpoint σ  ──side_env──▶  abstract state per point
   (AST)                (graph)   (strategy trees)   (T :: pp ⇒ tree)   (TD_side / any Kleene)   (σ: pp+g ⇒ 'd st)     γ over-approximates the real runs
```

The whole chain is generic in the abstract domain `'d` (a `sound_domain`); Sign is
the worked instance used throughout.

---

## 1. The AST — `com`

`src/VIMP/VIMP_Proc.thy:20`. Expressions are `aexp` / `bexp`
(`src/VIMP/VIMP_Syntax.thy:30,44`); a variable is **global** iff its name is empty
or starts with `G` (`is_global`, `src/VIMP/VIMP_Globals.thy:24`).

```
com = SKIP | Assign vname aexp | Seq com com | If bexp com com | While bexp com
    | Scope com | Call pname | Restore
```

`SKIP … While` are the intra core; `Scope`/`Call`/`Restore` are the interprocedural
extension (they produce `EA_Enter` edges and *combine* triples).

## 2. Compile to a CFG — `compile`

`src/CFG/VIMP_Proc_to_CFG.thy:19`. `compile Π lay c n` returns

```
(next_fresh_pp, entry_pp, exit_pp, edges, combines)
```

with `pp = nat` (`CFG_Def.thy:26`) allocated from `n`. Edges are labelled by an
`edge_action` (`CFG_Def.thy:38`): `EA_Nop`, `EA_Assign x a`, `EA_Assume b`,
`EA_AssumeNot b`, `EA_Enter`. The structured cases:

- `Assign x a`: `n ─EA_Assign x a─▶ n+1`
- `Seq c1 c2`: compile both, splice `ex1 ─EA_Nop─▶ en2`
- `If b c1 c2`: `en ─EA_Assume b─▶ c1`, `en ─EA_AssumeNot b─▶ c2`, both exits `─EA_Nop─▶` join
- `While b c`: `head ─EA_Assume b─▶ body`, `head ─EA_AssumeNot b─▶ exit`, `body_exit ─EA_Nop─▶ head`
- `Scope c`: `n ─EA_Enter─▶ body`, plus a **combine** `(n, body_exit, scope_exit)`

A `cfg` (`CFG_Def.thy:61`) is a graph of `edges` plus `cfg_entry`/`cfg_exit`, and a
set of **combine** triples `(caller, callee_exit, return)`. The solver reads two
derived lists per point `v`:

- `predecessor_list g v` (`CFG_Def.thy:147`) — the `(u, a)` incoming edges,
- `combine_predecessor_list g v` (`CFG_Def.thy:260`) — the `(caller, callee_exit)` returns.

## 3. The equation system — strategy trees

The analyzer never manipulates stores directly. Each program point `v` gets a
**strategy tree** `T v` (`side_cfg_T_eff g etf bot0 s0 gseed`,
`TD_Side_Tree.thy:61`), and the solver interprets trees against a candidate
solution `σ :: pp + 'g ⇒ 'd st`.

### 3.1 Strategy trees — `Basics_side.thy:94`

```
strategy_tree = Answer 'd | QueryL 'x (…) | QueryG 'g (…) | Side 'g 'd (…)
```

- `QueryL x k` — read the **local** unknown `Inl x`, continue with `k (σ (Inl x))`
- `QueryG g k` — read the **global** unknown `Inr g`, continue with `k (σ (Inr g))`
- `Side g d t` — **publish** `d` to global slot `Inr g`, then continue as `t`
- `Answer d` — the local result `d`

Three interpreters (`Basics_side.thy:289,297,101`):

- `traverse_rhs t σ` — the **local answer**: walks `QueryL`/`QueryG` reading σ,
  skips `Side`, returns the `Answer` value.
- `sides_of_rhs t σ k` — the **global writes**: `⊥` everywhere except that each
  `Side g d` accumulates `d` into slot `Inr g`.
- `dep_aux σ t` — the set of unknowns the tree reads (the dependency set the solver
  uses to schedule).

### 3.2 The per-point tree — `make_side_rhs_tree_eff` `TD_Side_Tree.thy:50`

```
T v = let acc0 = (if v = entry then bot0 ⊔ restrict_local s0 else bot0)
          t    = side_rhs_fold_eff etf acc0 (predecessor_list g v) (combine_predecessor_list g v)
      in if v = entry then Side gseed (restrict_global s0) t else t
```

`side_rhs_fold_eff` (`TD_Side_Tree.thy:36`) folds the incoming edges and combines
into a chain that joins each edge's transfer into `acc`:

```
fold acc [] []                     = Answer acc
fold acc ((u,a)#ps) cs             = seqcomp (apply_etf etf a u)  (λres. fold (acc ⊔ res) ps cs)
fold acc [] ((cc,ex)#cs)           = seqcomp (etf_combine etf cc ex) (λres. fold (acc ⊔ res) [] cs)
```

So `traverse_rhs (T v) σ` (its denotation, `side_acc_eff`, `TD_Side_Tree.thy:70`) is:

```
σ(Inl v) ⊒  acc0
          ⊔  ⨆ over edges (u,a)→v of  traverse_rhs (apply_etf etf a u) σ
          ⊔  ⨆ over combines (cc,ex)  of traverse_rhs (etf_combine etf cc ex) σ
```

and the entry point additionally seeds the global slot with `restrict_global s0`.

### 3.3 What one edge does — the transfer trees

`apply_etf etf a u` (`Constraint_System.thy:443`) dispatches the `edge_action` to
the domain's `effectful_domain_transfer` record (`:435`). A forward domain
transfer `domain_transfer` (`:36`, fields `tf_assign`/`tf_assume`/`tf_assume_not`/
`tf_enter`) is lifted to an etf by `unit_etf_of_transfer` (`TD_Side_CFG.thy:553`),
which wraps each action's state transformer `F = apply_tf tf a` (`:44`) in a
**unit-global edge tree** (`TD_Side_CFG.thy:128`):

```
unit_edge_tree f u = QueryL u (λsu. QueryG () (λg.
                       let res = f (su ⊔ g)
                       in Side () (restrict_global res) (Answer (restrict_local res))))
```

Read the predecessor local `su` and the global `g`, apply `f`, **publish the global
part** back to the (single, anonymous) global slot and **answer the local part**.
`restrict_local`/`restrict_global` (`TD_Side_CFG.thy:25,29`) keep the non-global /
global components (`is_global` decides). A purely-local action instead uses
`local_edge_tree` (`:369`) — no `QueryG`, no `Side` — to avoid a spurious
dependency on the global slot (see `LOCALES.md` / `docs` on the mixed generator).

`etf_combine` (procedure return) reassembles caller-locals with callee-globals via
`combine_abs` `⟨sc|se⟩` (`Constraint_System.thy:273`).

## 4. Solve — post-fixpoint of the equation system

A candidate `σ :: pp + 'g ⇒ 'd st` is a **post-solution** iff for every unknown it
over-approximates its right-hand side: `traverse_rhs (T v) σ ≤ σ(Inl v)` and
`sides_of_rhs (T v) σ k ≤ σ(k)` for every `k`. The project rides the **vendored,
verified top-down side solver** `TD.TD_side` (`vendor/td-verification/`), driven
through `td_cfg_side_solver_eff` (`TD_Side_Eff_Interface.thy:20`); its
`partial_correctness` gives such a post-solution when the system is monotone
(the `threefold_mono` obligation the RHS generator discharges — see `LOCALES.md`).

The important fact for understanding: **any** post-fixpoint is sound; `TD_side` is
just an *efficient* way to compute one, following `dep_aux` to re-evaluate only
what changed. A naïve ascending Kleene iteration reaches the same kind of
post-fixpoint — that is what the Python model does, so you can watch it converge.

## 5. Read back — `side_env`

The abstract state at point `v` is `side_env σ v = σ(Inl v) ⊔ glob_env σ`
(`TD_Side_CFG.thy:93`), i.e. the local slot joined with the join of all global
slots (`glob_env`, `Constraint_System.thy:525`).

## 6. Soundness (what it all buys)

Concretization `γ` maps an abstract state to the set of concrete stores it covers
(Sign: `gamma_sign`, `Sign_Domain.thy` — `SPos ↦ {n. n>0}`, `STop ↦ UNIV`, …). The
headline theorems state that the collecting semantics at every program point is
contained in `γ (side_env σ v)`: the analyzer's post-fixpoint **over-approximates
every real run**. See `PROOF_OVERVIEW.md`.

## 7. Context-sensitivity is a layer on top

Everything above is the base, single-global (`'g = unit`) system. A context- or
digest-sensitive analysis **reuses the same edge trees** and relabels their one
`()` global write to a keyed slot `Inr g` via `map_gtree (λ_. key)` (and locals to
`(pp, ctx)` via `map_ltree`), in generators like `side_cfg_T_eff_cmp`
(`TD_Side_Eff_Cmp_Gen.thy:53`) and the digest writer (`Digest_Keyed_Writer.thy`).
The domain stays keying-agnostic; the demo models the base system and notes the
hook.

---

## The runnable model

`demo/voblint_pipeline/` mirrors §1–§5 function-for-function (`strategy_tree.py`,
`state.py`, `trees.py`, `generator.py`, `sign.py`, `cfg.py`, `solver.py`). Run
`python -m voblint_pipeline.main` from `demo/` to compile a small program, print
its CFG, generate the strategy trees, Kleene-solve to a post-fixpoint, and show the
abstract state + `γ` at each point. Each module's docstring cites the `file:line`
it reimplements.
