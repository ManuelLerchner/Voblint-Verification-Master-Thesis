# CFG compiler redesign: continuation-passing fragments

Review of the `compile` / `compile_prog` pipeline in `src/CFG/`, with a
concrete migration plan. Written against the working tree at
`factorial-example-compilation-test` (`aa0f9d4d`).

Comparison target: Goblint-CIL `src/cfg.ml` at
`3ade66d089b5c31bb0dc7ed75bedda8370c2371e` and Goblint
`src/common/framework/cfgTools.ml` at
`aab8d97333fb93922cb9f06bd4604b1aab623db7`.

> **Names in this document are those of `aa0f9d4d` and have since changed.**
> The redesign was implemented and the compiler then moved out of `Voblint_CFG`
> into its own `Voblint_Compile` session, with every theory renamed after what
> it states:
>
> | here | now |
> | --- | --- |
> | `src/CFG/Compiler/Control_Residual.thy` | `src/Compile/Simulation/Residual_Location.thy` |
> | `src/CFG/Compiler/Control_Emit.thy` | `src/Compile/Simulation/Residual_Edges.thy` |
> | `src/CFG/Compiler/Control_Simulation.thy` | `src/Compile/Simulation/Simulation_Relation.thy` |
> | `src/CFG/Compiler/Control_Simulation_Forward.thy` | `src/Compile/Simulation/Simulation_Preservation.thy` |
> | `src/CFG/Compiler/Compile_Locality.thy` | `src/Compile/Procedure_Ownership.thy` |
> | `src/CFG/Compiler/Located_LTR.thy` | `src/Compile/Source_To_Trace.thy` |
> | `src/CFG/Compiler/Located_Exec.thy` | `src/CFG/CFG_Exec.thy` |
> | `src/CFG/Collecting/CFG_Local_Trace.thy` | `src/CFG/Collecting/LTR_Def.thy` |
> | `Compile_Certificate` | folded into `Simulation_Preservation` |
> | `Compile_Reaches` | folded into `Compile_Invariants` |
> | `procs_compiled` | `procs_embedded` |
> | `proc_activation` | folded into `compiled_at` |
> | `source_wf` | `return_safe :: com => bool` |
> | `source_global` | `gs` |
> | `mnm` | `main_name` |

---

## 1. Current architecture summary

### Layers

| Layer | File | Role |
| --- | --- | --- |
| Graph | `src/CFG/CFG_Def.thy` | `cfg_node`, `edge_action`, `call_action`, `cfg` record, `edge_step`, `wf_cfg` |
| Compiler | `src/Compile/VIMP_Proc_to_CFG.thy` | `compile`, `compile_proc`, `compile_procs`, `compile_prog`, range/finiteness/shape lemmas, `compile_prog_wf` |
| Reachability | `src/CFG/CFG_Prune.thy` | `cfg_succ_rel`, `cfg_reaches`, `cone`, `cfg_exit`, `compile_reaches` |
| Location | `src/Compile/Control_Residual.thy` | `control_at`, `compile_entry_node`, `compile_control_at_SKIP_exit_path` |
| Execution | `src/Compile/Located_Exec.thy` | `cstep`, `frames_match` |
| Simulation | `src/Compile/Control_Simulation.thy` | `intra_step`, `compiled_at`, `csim`, `csim_step`, `csim_star` |
| Locality | `src/Compile/Compile_Locality.thy` | `pfn`, edge shapes, per-procedure ownership, fragment bounds, `valid_ltr_frag_callers` |
| Invariants | `src/Compile/Compile_Invariants.thy`, `Compile_Certificate.thy` | `inv1`..`inv16`, `compiled_cfg_wf`, `procs_compiled` |
| Trace bridge | `src/Compile/Located_LTR.thy` | `ltr_repr`, `stack_repr` |
| Rendering | `src/Analysis/Reporting/Analysis_GraphViz.thy` | `raw_cfg_dot_lit`, `compiled_proc_owner`, `compiled_owner_of` |

### The fragment interface

```isabelle
compile :: "proc_table => pname => com => nat
   => nat * cfg_node * cfg_node
        * (cfg_node * edge_action * cfg_node) set
        * (cfg_node * call_action * cfg_node * cfg_node) set"
```

Returned as `(next_id, entry, normal_exit, intra_edges, call_edges)`.
`compile_proc` brackets a body between `FunctionEntry p` and `FunctionResult p`,
`compile_procs` folds the declared procedures, `compile_prog` appends `main`
under `mnm` and sets `cfg_entry = FunctionEntry mnm`.

Established facts about the interface:

- `compile_entry_node` / `compile_entry_is_start`: `en = Statement n` for every
  command. The entry is already fully determined by the base counter.
- `compile_entry_exit_stmt`: both `en` and `ex` are `Statement` nodes in
  `{n..<n'}`.
- `compile_counter_mono`: `n <= n'` (an inequality, not an equation).
- `compile_frag_stmts_range`: every statement index touched is in `{n..<n'}`.
- `compile_E_shape`: intra sources are `Statement`, targets are `Statement` or
  the own `FunctionResult p`.
- `compile_intra_pfn` / `compile_calls_pfn`: **both endpoints of every edge lie
  in `pfn p n n'`** — the fragment's own node set. This is the load-bearing
  locality invariant, and it is the one the redesign must generalize.

### Where the interface is consumed

`rg` over `src/` shows the 5-tuple is destructured in exactly nine theories:

```
src/Compile/VIMP_Proc_to_CFG.thy              37 references
src/Compile/Control_Simulation.thy   65
src/Compile/Compile_Locality.thy     40
src/Compile/Control_Residual.thy     15
src/Compile/Compile_Invariants.thy   11
src/CFG/CFG_Prune.thy                      6
src/Compile/Compile_Certificate.thy   2
src/Compile/Located_LTR.thy           2
src/Soundness/Source_Activation_Sound.thy   1 (line 191)
```

plus two example theories (`Example_Compile_Regression`,
`Example_Control_Simulation_Regression`).

Everything downstream — the equation system, the TD solver, the D/G framework,
the Sign/Interval/Mixed instances, the GraphViz renderer — consumes only
`compile_prog` / `compile_proc` and the `cfg` record. A grep for dense-index
assumptions (`{0..<n}`, `Statement `` ` ``, `upt`) over `src/Analysis` and
`src/Soundness` returns nothing: every consumer is edge-set driven.

**Consequence, stated precisely: no analysis *framework definition* appears to
require changes under any of the options below — but examples and
node-index-specific assertions will require regeneration.** The distinction
matters:

- Unchanged: the equation system, constraint soundness, the TD solver and its
  side-effecting variants, the DG framework, the domain type classes, the
  Sign/Interval/Mixed transfer functions and their soundness proofs, the
  GraphViz renderer's definitions.
- Regenerated: every `value`, `lemma`, or `theorem` in `src/Examples` that names
  a concrete `Statement k`. That is 14 files and roughly 285 index-bearing
  lines, the largest being `Example_LTR_Collect_Regression.thy` (69 references)
  and `Example_Proc_Call.thy` (30).
- Needs a read-through, not just renumbering: any example asserting an abstract
  value *at* a node whose identity merges with a neighbour under the redesign
  (see §12, question 6).

The cost is confined to the compiler, its proof stack, and example regeneration.

---

## 2. Root cause

### `exit` is an output when it should be an input

The problem is not "one exit per fragment". It is that the exit is *produced by*
the callee fragment instead of *supplied by* the surrounding construct. Two
consequences follow mechanically:

1. A construct that composes fragments must connect two nodes that denote the
   *same* program point, so it emits glue `EA_Nop` edges (`Seq`, both `If`
   joins, the `While` back-edge).
2. A construct with no normal exit must invent one to satisfy the type
   (`Return`).

### `exit` currently means at least four different things

| Command | What `ex` is |
| --- | --- |
| `Assign` | the genuine post-state program point |
| `Call` | the resume point |
| `If`, `While` | a freshly allocated merge / loop-false node |
| `Seq` | inherited from `c2` |
| `SKIP`, `Restore`, `Unwind` | *the entry node itself*, and the fragment emits **no edges at all** |
| `Return` | a fresh node with no incoming edge — filler |

So `ex` is simultaneously "post-state point", "merge target", "the entry", and
"a node that exists only because the tuple has a third slot". `SKIP` is the
quiet second anomaly: its fragment contributes zero edges, so its single node
exists only as an endpoint of its neighbours' glue edges.

### The type asserts something false about the source language

```isabelle
... => nat * cfg_node * cfg_node * ... set * ... set
```

reads as *every command has a normal exit*. `Return` does not. The dead nodes
`pp2`, `pp6`, `pp7` in the factorial CFG are the compiler paying for that false
claim, and `inv11_return_exit_unreached` in `Compile_Invariants.thy:303` is the
formalization *documenting* the artifact as an invariant rather than removing
it.

### Concrete cost, factorial

`factorial_program` in `src/Examples/Tooling/Example_Proc_GraphViz_Recursion.thy`
compiles as follows (hand-evaluated against the current `compile`):

```
fac body = If (n<2) (Return 1) (Seq (Call tmp fac [n-1]) (Return (n*tmp)))

Statement 0   if n < 2                       reachable
Statement 1   return 1                       reachable
Statement 2   exit of (Return 1) fragment    DEAD
Statement 3   call fac(n-1), resume at 4     reachable
Statement 4   resume point                   reachable
Statement 5   return n*tmp                   reachable
Statement 6   exit of (Return ...) fragment  DEAD
Statement 7   If merge node                  DEAD

dead edges:  2 -nop-> 7,  6 -nop-> 7,  7 -ret None-> FunctionResult fac
glue edge:   4 -nop-> 5    (reachable, but a pure pass-through)

main body = Seq (Assign N 8) (Call r fac [N])

Statement 8   N := 8                         reachable
Statement 9   post-assign point              reachable
Statement 10  call fac(N)                    reachable
Statement 11  resume point                   reachable

glue edge:   9 -nop-> 10   (reachable pass-through: 9 and 10 are the same point)
```

12 statement nodes, 3 dead (25%), 3 dead edges, 2 reachable-but-redundant
`EA_Nop` pass-throughs. The reader sees a `pp2 -> pp7 <- pp6` join and a
`pp7 -> exit_fac` return that no execution ever takes.

---

## 3. Goblint / Goblint-CIL findings

### Which repository owns CFG construction

Both, at different levels.

- **Goblint-CIL** (`goblint/cil`, `src/cfg.ml`) fills the mutable
  `stmt.succs` / `stmt.preds` fields on CIL statements.
- **Goblint** (`goblint/analyzer`, `src/common/framework/cfgTools.ml`,
  `createCFG`) builds its *own* labelled CFG (`MyCFG`) over
  `Node.t` by walking the CIL statement graph.

The second is the one the analysis consumes, and it is the direct analogue of
`compile_prog`.

### Goblint's node type matches this formalization

`src/common/framework/node0.ml`:

```ocaml
type t =
  | Statement of CilType.Stmt.t
  | FunctionEntry of CilType.Fundec.t
  | Function of CilType.Fundec.t
```

with the comment

> The stmt in a Statement node is misleading because nodes are program points
> between transfer functions (edges), which actually correspond to statement
> execution.

`Statement nat | FunctionEntry pname | FunctionResult pname` is a 1:1 match
(`Function` = `FunctionResult`). The parenthetical is exactly the design
principle the current `compile` violates: nodes are *program points between*
statements, so a statement's edge should target the next statement's node, not a
private "after" node bridged by a nop.

### Continuation passing, not fragment exits

`goblint/cil`, `src/cfg.ml:155`:

```ocaml
and cfgStmt (s: stmt) (next:stmt option) (break:stmt option) (cont:stmt option)
            (nodeList:stmt list ref) (rlabels: stmt list) =
```

with the file-level comment at line 65:

```
   Fill in the CFG info for the stmts in a block
   next = succ of the last stmt in this block
   break = succ of any Break in this block
   cont  = succ of any Continue in this block
   None means the succ is the function return.
```

`None` continuation = *function return*. That is precisely the epilogue /
`FunctionResult` role, expressed as the absence of a normal continuation.

Sequencing (`src/cfg.ml:136`) passes the next statement down instead of
patching an exit afterwards:

```ocaml
and cfgStmts (ss: stmt list) (next:stmt option) ... =
  match ss with
    [] -> ();
  | [s] -> cfgStmt s next break cont nodeList rlabels
  | hd::tl ->
      cfgStmt hd (Some (List.hd tl))  break cont nodeList rlabels;
      cfgStmts tl next break cont nodeList rlabels
```

### `return` has no successor

`src/cfg.ml:196`:

```ocaml
  | Return _  -> ()
```

The `next` argument is in scope and deliberately unused. Confirmed at the
Goblint level too, `cfgTools.ml:337`:

```ocaml
          | Return (exp, loc, eloc) ->
            addEdge (Statement stmt) (Cilfacade.eloc_fallback ~eloc ~loc, Ret (exp, fd)) (Function fd)
```

One edge, statement node to `Function fd`, no fall-through. This is
`(Statement k, EA_Ret e p, FunctionResult p)` with no synthetic exit.

### `if` gets no merge node

`src/cfg.ml:201`, plus `addBlockSucc` at line 175:

```ocaml
  | If (_, blk1, blk2, _, _) ->
      addBlockSucc blk2 next;
      addBlockSucc blk1 next;
      cfgBlock blk1 next break cont nodeList rlabels;
      cfgBlock blk2 next break cont nodeList rlabels
```

```ocaml
  let addBlockSucc (b: block) (n: stmt option) =
    (* Add the first statement in b as a successor to the current stmt.
       Or, if b is empty, add n as a successor *)
    match b.bstmts with
      [] -> addOptionSucc n
    | hd::_ -> addSucc hd
```

Both branches receive the same `next`. An empty branch wires the head straight
to `next`. No join node is allocated, and a branch ending in `return` simply
never uses `next`. Goblint's own layer does the same, `cfgTools.ml:310`:

```ocaml
            addEdge ~skippedStatements:true_skippedStatements (Statement stmt) (..., Test (exp, true )) (Statement true_stmt);
            addEdge ~skippedStatements:false_skippedStatements (Statement stmt) (..., Test (exp, false)) (Statement false_stmt)
```

### Loops

`src/cfg.ml:222`:

```ocaml
  | Loop(blk, loc, eloc, s1, s2) ->
      s.skind <- Loop(blk, loc, eloc, (Some s), next);
      addBlockSucc blk (Some s);
      cfgBlock blk (Some s) next (Some s) nodeList rlabels
      (* Since all loops have terminating condition true, we don't put
         any direct successor to stmt following the loop *)
```

Body continuation is the loop statement itself; `break = next`;
`continue = Some s`. The body's normal completion flows straight back to the
head — no back-edge nop node.

### Ordinary calls fall through to the next statement

`src/cfg.ml:182` and `:191`:

```ocaml
  let instrFallsThrough (i : instr) : bool = match i with
      Call (_, Lval (Var vf, NoOffset), _, _, _) ->
        not (hasAttribute "noreturn" vf.vattr)
    | Call (_, f, _, _, _) ->
        not (hasAttribute "noreturn" (typeAttrs (typeOf f)))
    | _ -> true
  in
  match s.skind with
    Instr il  ->
      if List.for_all instrFallsThrough il then
        addOptionSucc next
```

At Goblint's level (`cfgTools.ml:283-296`) a call instruction becomes a `Proc`
edge from the statement node **to the successor statement node**:

```ocaml
            let add_succ_node ?skippedStatements succ_node = addEdges ?skippedStatements (Statement stmt) edges succ_node in
            begin match real_succs () with
              | [] -> add_succ_node (Lazy.force pseudo_return)
              | [succ, skippedStatements] -> add_succ_node ~skippedStatements (Statement succ)
```

So Goblint does **not** put callee entry / resume into the CFG topology. The
callee identity and the resume transfer live in the analysis
(`enter` / `combine_env` / `combine_assign`). This formalization's four-place
`calls` relation is the *explicit* form of that: it makes the entry and resume
dependency visible in the graph rather than implicit in the framework. That is
a divergence in favour of the formalization; keep it. It is also unrelated to
the dead-node problem.

### The pseudo-return node: a lazily allocated epilogue

`cfgTools.ml:246-258`:

```ocaml
        (* Return node to be used for infinite loop connection to end of function
         * lazy, so it's only added when actually needed *)
        let pseudo_return = lazy (
          ...
          let newst = mkStmt (Return (None, fd_end_loc, locUnknown)) in
          newst.sid <- Cilfacade.get_pseudo_return_id fd;
          ...
          addEdge newst_node (fd_end_loc, Ret (None, fd)) (Function fd);
          newst_node
        )
```

used at `cfgTools.ml:293` when a statement has no real successor, and at
`:429` when an SCC cannot otherwise reach `Function fd`. This is the direct
precedent for a per-procedure epilogue node, allocated *only when needed*.

Note the entry bracket at `cfgTools.ml:245`, matching
`(FunctionEntry p, EA_Nop, ben)`:

```ocaml
        addEdge ~skippedStatements (FunctionEntry fd) (fd_loc, Entry fd) (Statement entrynode);
```

Goblint labels it `Entry fd` rather than a skip. Minor alignment observation:
the repo's `EA_Nop` bracket carries no information that `FunctionEntry` does not
already carry, so this is fine as is.

### Normalization is separate from CFG computation

`Cil.prepareCFG` lowers `switch` / `break` / `continue` into gotos and ifs
*before* CFG computation. `cfgTools.ml` then rejects anything unprepared
(`failwith "MyCFG.createCFG: unprepared stmt"` at `:216` and `:374`). The IMP2
language has no `break`/`continue`/`goto`/`switch`, so there is nothing to
normalize here — but the architectural split is worth keeping in mind if those
are ever added: lower first, then build edges.

### Unreachable statements and node elision

- CIL keeps unreachable statements in the AST with sids assigned; they simply
  have no `preds`. `src/cfg.ml` performs no dead-node removal.
- Goblint *does* elide nodes during construction: `find_real_stmt`
  (`cfgTools.ml:177`) skips `Goto`, `Instr []`, `Block`, and `Loop` container
  statements, and the elided statements are retained as **edge metadata**
  (`~skippedStatements`, returned as `skippedByEdge`). Source mapping survives
  even though the nodes do not appear in the CFG.
- `minimizeCFG` (`cfgTools.ml:471`) contracts every node with exactly one
  predecessor and one successor, again accumulating the elided statements into
  `skippedStmts`. A code search over `goblint/analyzer` finds no other file
  referencing it, so treat it as an optional utility rather than part of the
  analysis path.
- `find_backwards_reachable` (`cfgTools.ml:12`) and the connectivity check at
  `:458-461` (`raise (Not_connect fd)`) show Goblint requires
  `FunctionEntry fd` to reach `Function fd`, and adds `Test (one, false)` edges
  to force it.

**Two ideas worth importing.** (1) Pass the continuation down; let terminating
statements ignore it. (2) When a node is elided, keep its source identity as
edge metadata rather than keeping the node.

---

## 4. Design alternatives

Assessed against: semantic clarity, Isabelle definitional cost, executability
and code generation, termination, induction shape, proof burden, node
numbering, call continuations, migration cost.

### A. `normal_exit :: cfg_node option`

Honest about `Return`, and small: `None` for `Return`, `Some ex` otherwise.
Fixes the dead node after `Return`. But it does **not** fix the glue nops (the
exit is still an output, so `Seq` still bridges two nodes denoting one point),
and every composition site grows an `option` case split. `If` becomes:
allocate a merge node only if at least one branch is `Some` — an `if` on
options inside the compile clause, and a merge node whose existence is
data-dependent, which is worse to reason about than no merge node at all.
Verdict: a partial fix that adds case analysis without removing the cause.

### B. `normal_exits :: cfg_node set`

Strictly more general than A and strictly worse here. `Return` gives `{}`,
`If` gives the union of branch exits — which removes the merge node, good — but
now `Seq` emits one nop per exit in the set, and every lemma about "the" exit
becomes a lemma over a set. Finiteness of the exit set becomes an extra
obligation. The `pfn` locality lemmas would have to quantify over the set.
Verdict: no.

### C. `datatype completion = FallsThrough cfg_node | Terminates | MultipleExits "cfg_node set"`

Three constructors where the interesting distinction is binary, and
`MultipleExits` subsumes `FallsThrough`, so the type has redundant
representations — every consumer needs a normalization argument or risks
case-splitting on states that cannot arise. Verdict: no.

### D. Open-edge / patch-list construction

Return unresolved half-edges `(source, action)` to be closed by the enclosing
construct. This is essentially B with the label attached, and it is what LLVM
IRBuilder does with unterminated blocks. In HOL the patching operation is a set
map over the pending list, and every lemma about "the edges of a fragment" now
has to say "the edges after patching". Induction hypotheses become statements
about a function from continuation to edge set — which is exactly option E,
but reached indirectly and with an intermediate data structure. Verdict: E
directly.

### E. Continuation-passing compilation — **recommended**

`compile Pi p c k n` where `k :: cfg_node` is the normal continuation.
`Return` ignores `k`. `Seq` compiles `c1` with `entry c2` as its continuation.
`If` compiles both branches with the same `k`. `While` compiles the body with
the loop head as its continuation.

- Semantic clarity: high. The graph contains a node per program point and an
  edge per transfer, and nothing else.
- Definitional cost: needs an allocation-size function `csize :: com => nat` so
  `Seq` can name `entry c2` before compiling `c1` (see §5). One extra `fun` and
  one induction lemma.
- Executability, termination: unchanged. Still structurally recursive on `com`,
  still `fun`, still code-generates.
- Induction: unchanged shape — `com.induct` with the continuation and counter
  generalized. Every existing induction skeleton in `Compile_Locality` and
  `Control_Simulation` transfers.
- Numbering: forward and source-ordered, preserved (§5).
- Call continuations: the resume node becomes `k` instead of a private
  `Statement (Suc n)`. The four-place `calls` tuple is unchanged.
- Proof burden: one genuine generalization (`pfn` gains the continuation), and
  two catch-up lemmas get *easier* (see §11).

### F. Direct predecessor/successor construction over statement nodes

This is what Goblint-CIL does, and it is *the same algorithm* as E — the
difference is only that CIL mutates `succs`/`preds` in place while a HOL
function returns an edge set. There is no separate design here to adopt: E is F
written functionally. Adopting F literally (a state monad over a mutable node
table) would buy nothing and cost executability and proof simplicity.

### G. Basic blocks with terminators

Would change the node type from "program point" to "block", breaking the
`Statement | FunctionEntry | FunctionResult` correspondence with Goblint, and
requiring every analysis lemma to be restated over intra-block sequences.
Blocks matter when instruction scheduling or codegen matters; they do not help
a per-program-point abstract interpreter. Note that Goblint itself does *not*
use basic blocks. Verdict: no.

---

## 5. Recommended architecture

### The fragment type

```isabelle
fun csize :: "com => nat" where
  "csize SKIP = 1"
| "csize (Assign x a) = 1"
| "csize (Seq c1 c2) = csize c1 + csize c2"
| "csize (If b c1 c2) = 1 + csize c1 + csize c2"
| "csize (While b c) = 1 + csize c"
| "csize (Call dst q actuals) = 1"
| "csize (Return e) = 1"
| "csize Restore = 1"
| "csize Unwind = 1"

fun compile ::
  "proc_table => pname => com => cfg_node => nat
   => nat * cfg_node
        * (cfg_node * edge_action * cfg_node) set
        * (cfg_node * call_action * cfg_node * cfg_node) set"
```

Two changes to the interface for the migration:

1. The continuation `k` becomes an **input**.
2. `normal_exit` is **removed** from the result.

`entry` is **retained** through the migration, even though it is provably
`Statement n`. Removing it is interface cleanup, not part of the fix, and
bundling it with the continuation change concentrates avoidable churn in the
same files. It moves to Phase 7.

The counter-evidence is real and worth recording so the decision can be flipped
cheaply: `en1` is almost always rewritten to `Statement n` on the next line
after destructuring (`Control_Simulation.thy:174`, `:226`, `:318` all apply
`compile_entry_node[OF ...]` immediately), and under the new `If` clause the
assume-edge targets are named literally as `Statement m` / `Statement n1`, so
`en1` and `en2` disappear from the *statement* of `control_at_if_edges`
regardless of whether the tuple still carries them.

`next_id` is retained even though `compile_next_id` will prove
`fst (compile Pi p c k n) = n + csize c`, because every existing range and
ownership lemma is stated in terms of `n'` and keeping it makes those
statements transfer verbatim.

Argument order `compile Pi p c k n` mirrors `cfgStmt s next`.

### `csize` is a trade-off, not an implementation detail

`Seq` must name `c2`'s entry *before* compiling `c1`. There are two ways to get
it, and the choice is a design decision worth stating explicitly.

**Forward order with static sizing (recommended).** Introduce `csize` and use
`m = n + csize c1`. This retains forward, source-syntax-ordered statement
numbering — the property that makes the DOT output and the index-bearing
regression examples readable — and it upgrades `compile_counter_mono`'s
inequality to an equation, which *simplifies* the range and ownership lemmas.

The cost is real: **`csize` becomes part of the compiler's trusted arithmetic
structure.** Every clause must allocate exactly the number of nodes `csize`
claims, and any future language extension must extend both in step. Two
mitigations: a single lemma catches drift immediately — `compile_next_id` simply
fails to prove if the two disagree — and Phase 3 establishes that lemma against
the *current* compiler before it becomes load-bearing.

**Reverse structural order (rejected).** Compile `c2` first, read its entry,
then compile `c1` with that entry. No `csize`, no trusted arithmetic. But
indices are then allocated right-to-left, so a source-ordered program gets
descending node numbers, and `entry c = Statement n` no longer holds — a
fragment's entry becomes the *last* index it allocates. That breaks
`compile_entry_node`, which `Control_Residual` and `Control_Simulation` rely on
throughout, and it makes the `pfn` ownership ranges read backwards. The `csize`
obligation is the cheaper of the two, but it is an obligation, not a free
convenience.

### Two invariants that must hold by construction

- **Every fragment entry is a freshly allocated `Statement n`.** This is why
  `SKIP` keeps a node (emitting `Statement n -nop-> k`) rather than returning
  `k` as its entry. It preserves `compile_entry_node` and
  `control_at_node_stmt` unchanged, and the node is genuinely meaningful: an
  empty `else` branch gets a program point carrying the `¬b`-refined state.
- **Every edge into `FunctionResult p` is an `EA_Ret _ p` edge.** This is why
  procedures keep an epilogue node rather than passing `FunctionResult p` as
  the body continuation directly. Without it, a trailing `Assign` would emit
  `Statement k -EA_Assign-> FunctionResult p` and `compile_result_target` — used
  throughout `Compile_Locality` — would be lost. `edge_step (EA_Ret None p)` is
  semantically the identity, so the epilogue costs one node and one edge per
  procedure and buys a clean invariant. Goblint's `pseudo_return` is the same
  device.

### Is the result-node invariant worth one dead node?

The always-allocated epilogue leaves exactly one compiler-generated unreachable
node per always-returning procedure. That is the one artifact the redesign does
not remove in Phase 4, so the invariant it protects has to earn its keep. Two
alternatives, both rejected, and the reason is the same in both cases.

**Alternative 1: a distinguished implicit-return action, `EA_ReturnImplicit`.**
Let the final command's own edge target `FunctionResult p` directly, tagged with
a new action so the invariant survives in a weaker form. This looks cheap and is
not, because `edge_action` is not merely matched on — the transfer-function
interface has **one record field per action**. Adding a constructor means adding
a field to `tf` (`tf_assume_not`, …), `etf`, `etf_st`, and `dgs`, and then
extending every record literal that instantiates them:

```
src/Analysis/Generic/Equations/Constraint_System.thy   apply_tf, apply_etf, local_edge_action
src/Analysis/Generic/Solver/Exec/Exec_Bridge.thy       apply_etf_st
src/Analysis/Generic/Solver/Core/TD_Side_CFG.thy       two etf record literals
src/Analysis/Instances/Sign/Sign_Exec.thy              sign_tf_st + etf_st literal
src/Analysis/Instances/Interval/Interval_Exec.thy           ivl_tf_st + etf_st literal
src/Analysis/Instances/Product/Mixed_Sign_Interval.thy   dgs literal
src/Analysis/Instances/Product/Exec_DG_Bridge.thy        dgs literal
src/Analysis/Instances/NamedGlobalSign/…               etf literal
src/CFG/CFG_Def.thy, src/CFG/CFG_Transfer.thy          edge_step, edge_collect
src/Analysis/Reporting/Analysis_GraphViz.thy   string_of_action (two sites)
```

plus the exhaustive case analyses in `Constraint_System_Sound.thy:146` and
`Sign_Local_Effects.thy:484`. This is precisely the analysis-wide ripple the
whole plan exists to avoid — one dead node versus a new field in four record
types and eight instantiations is not a close call.

**Alternative 2: `datatype continuation = Normal cfg_node | ProcedureEnd pname`.**
Making the "no normal continuation" case explicit in the type is attractive, and
it is what CIL's `stmt option` does. But it does not by itself solve anything:
to emit an edge from the last statement to `FunctionResult p` you still need an
*action* for that edge, and reusing the command's own action puts us back at
`EA_Assign -> FunctionResult`. So this variant only pays off in combination with
Alternative 1, and inherits its cost. Its residual value — documenting in the
type that a continuation may be "the procedure end" — is obtainable for free by
naming the epilogue node in `compile_proc` and commenting it.

Conclusion: keep the epilogue. The result-node invariant is cheap to maintain
and load-bearing in `Compile_Locality`; the alternatives move the cost into the
domain instances. Phase 6's lazy epilogue removes the dead node without touching
`edge_action` at all, which makes it the right way to close this gap.

### Procedure layout

```isabelle
definition compile_proc ::
  "proc_table => pname => proc_decl => nat
   => nat * (cfg_node * edge_action * cfg_node) set
        * (cfg_node * call_action * cfg_node * cfg_node) set"
where
  "compile_proc Pi p decl n =
     (let r = n + csize (body decl);
          (n', ben, E, K) = compile Pi p (body decl) (Statement r) n
      in (Suc r,
          insert (FunctionEntry p, EA_Nop, ben)
            (insert (Statement r, EA_Ret None p, FunctionResult p) E),
          K))"
```

The epilogue `Statement r` is allocated *after* the body, so statement indices
stay in source order and the epilogue is the last node of the procedure
fragment. Two consequences worth noting:

- `r < n'` where `n' = Suc r`, so the epilogue is inside `pfn p n n'`. This is
  what makes the command-level `insert k (pfn ...)` generalization collapse back
  to the original statement at procedure level (§7).
- `compile_proc`'s own result type is unchanged from today
  (`nat * E set * K set`), so `compile_procs`, `compile_prog`, and
  `Analysis_GraphViz.compiled_proc_owner` change only where they thread the
  counter.

### Optional phase: lazy epilogue

A later refinement can suppress the epilogue when the body cannot fall through:

```isabelle
fun falls_through :: "com => bool" where
  "falls_through SKIP = True"
| "falls_through (Assign x a) = True"
| "falls_through (Seq c1 c2) = (falls_through c1 & falls_through c2)"
| "falls_through (If b c1 c2) = (falls_through c1 | falls_through c2)"
| "falls_through (While b c) = True"
| "falls_through (Call dst q actuals) = True"
| "falls_through (Return e) = False"
| "falls_through Restore = True"
| "falls_through Unwind = False"
```

`While b c = True` is correct and important: the guard may fail on the first
test. This buys the last dead node (the `fac` epilogue) but requires a new
lemma, `compile_continuation_unused`:

```isabelle
lemma compile_continuation_unused:
  assumes "compile Pi p c k n = (n', en, E, K)" and "~ falls_through c"
  shows "(u, a, k) ~: E" and "(u, act, ce, k) ~: K"
```

Recommendation: ship the always-allocated epilogue first (§8 Phase 4), add the
lazy variant afterwards as an isolated change gated on that lemma.

### Why not a post-pass

Strategy A ("keep `compile`, prune afterwards") and Strategy B ("never generate
the dead nodes") differ in one decisive way: a post-pass produces a *second*
graph, and the analysis is proved sound for whichever graph it consumes.

| | Post-pass | Compiler redesign |
| --- | --- | --- |
| Fixes dead nodes | Yes (for the pruned graph) | Yes |
| Fixes glue `EA_Nop` chains | Only with an additional contraction pass, which changes call continuations and needs its own correctness argument | Yes, they are never generated |
| Fixes the false claim in the type | No | Yes |
| Analysis changes | None if presentation-only; if the analysis consumes the pruned graph, needs `compile_prog_wf`, locality, `procs_compiled`, and `csim` re-established for the pruned graph | None |
| New proof obligations | Pruning preserves `wf_cfg`, preserves reachable traces, preserves node ownership, and — for nop contraction — preserves `calls` continuations | Generalize `pfn` with the continuation; restate `control_at` and `compiled_at` |
| Statement IDs | Unchanged | Change (densified) |
| Maintenance | Two graphs and a translation to keep in sync forever | One graph |
| Addresses the cause | No | Yes |

The post-pass is nevertheless worth doing *first*, in a presentation-only form,
because it is cheap, reversible, and gives the visual win immediately while the
compiler migration proceeds. `CFG_Prune.thy` already has `cfg_succ_rel`,
`cfg_reaches`, and `cone`; a forward-reachable filter rooted at every
`FunctionEntry` node is a handful of lines and touches no analysis theorem.

Do **not** ship nop-contraction, in either strategy, as a graph transformation.
Contracting a node that is a call continuation requires rewriting the fourth
component of `calls` tuples, and the abstract state at a contracted node
disappears from the analysis result — which is precisely what a reader of the
DOT output wants to see. Under the redesign the chains do not exist, so the
question does not arise.

### Should there be two graph representations?

No. Once compilation stops emitting artifacts there is nothing for a
presentation graph to hide. Keep one CFG, and if a purely cosmetic filter is
ever wanted (for example hiding the `FunctionEntry -nop->` bracket), apply it
inside the renderer as a rendering predicate, never as a graph-to-graph
function with its own correctness theory.

Source-point metadata is a separate concern and the answer is Goblint's: if a
node is elided, attach its source identity to the surviving edge. Under the
recommended design nothing is elided — every source command with a runtime
effect keeps its own node — so no metadata is needed yet.

---

## 6. Detailed compilation rules

Notation: `compile Pi p c k n = (n', en, E, K)` with `en = Statement n` in every
clause and `n' = n + csize c`. The `en` component is retained for the migration
(§5) and is redundant by construction; it is written out below so the clauses can
be transcribed directly.

### `SKIP`

```isabelle
"compile Pi p SKIP k n =
   (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})"
```

One node, one nop to the continuation. Interacts with neither `FunctionEntry`
nor `FunctionResult`. (Today: one node, *no* edges, and the caller bridges.)

### `Assign x a`

```isabelle
"compile Pi p (Assign x a) k n =
   (Suc n, Statement n, {(Statement n, EA_Assign x a, k)}, {})"
```

One node instead of two; the post-state point is the continuation. This is the
single change that removes most glue nops.

### `Seq c1 c2`

```isabelle
"compile Pi p (Seq c1 c2) k n =
   (let m = n + csize c1;
        (n1, en1, E1, K1) = compile Pi p c1 (Statement m) n;
        (n2, en2, E2, K2) = compile Pi p c2 k m
    in (n2, en1, E1 Un E2, K1 Un K2))"
```

`c1`'s continuation is `c2`'s entry, named ahead of time via `csize`. No glue
edge. Compilation order stays left-to-right, so indices stay in source order.
Note that `en2` is discarded: it is provably `Statement m`, which is what was
passed to `c1` — and the fact that this clause *has* to discard a component it
already knows is the argument for Phase 7.

### `If b c1 c2`

```isabelle
"compile Pi p (If b c1 c2) k n =
   (let m = Suc n;
        (n1, en1, E1, K1) = compile Pi p c1 k m;
        (n2, en2, E2, K2) = compile Pi p c2 k n1
    in (n2, Statement n,
        {(Statement n, EA_Assume b, en1),
         (Statement n, EA_AssumeNot b, en2)} Un E1 Un E2,
        K1 Un K2))"
```

One node — the test. **No merge node.** Both branches receive the same `k`, so
a falling-through branch flows into `k` on its own last edge and a returning
branch never mentions `k`. The join still happens, at `k`, which is the
program point after the conditional; it is not a separate node with two nops
into it. If both branches return, `k` receives nothing from this fragment —
exactly right.

### `While b c`

```isabelle
"compile Pi p (While b c) k n =
   (let m = Suc n;
        (n1, en1, E1, K1) = compile Pi p c (Statement n) m
    in (n1, Statement n,
        {(Statement n, EA_Assume b, en1),
         (Statement n, EA_AssumeNot b, k)} Un E1,
        K1))"
```

`Statement n` is the loop head. True edge to the body entry, false edge to the
continuation, body compiled with the head as *its* continuation — so the
back-edge is the body's own last edge, not a nop. A body that always returns
simply produces no edge back to the head, and the loop remains reachable and
exitable through the false edge. No loop-exit node is allocated.

### `Call dst q actuals`

```isabelle
"compile Pi p (Call dst q actuals) k n =
   (Suc n, Statement n, {},
    {(Statement n,
      CallEdge dst (case Pi q of Some decl => formals decl | None => []) actuals,
      FunctionEntry q, k)})"
```

One node — the call site. The resume node is the continuation. The four-place
tuple, the `CallEdge` payload, and `call_enter` are all unchanged; the call is
still absent from `intra`, so `wf_cfg` and `edge_step` are untouched.
Recursion needs no special case: a self-call names `FunctionEntry p`, whose
fragment is compiled once.

### `Return e`

```isabelle
"compile Pi p (Return e) k n =
   (Suc n, Statement n, {(Statement n, EA_Ret e p, FunctionResult p)}, {})"
```

`k` is in scope and ignored. This is the whole fix. `inv11_return_exit_unreached`
becomes unnecessary: there is no exit node to be unreached.

### `Restore` and `Unwind` — behaviour deliberately unchanged

```isabelle
"compile Pi p Restore k n = (Suc n, Statement n, {}, {})"
"compile Pi p Unwind  k n = (Suc n, Statement n, {}, {})"
```

Both are runtime-only markers, excluded by `source_com`, so these clauses are
never exercised for a source program. The translation above is the *faithful*
port of the current stubs: allocate one node, emit no edges, ignore `k`. The
only thing that changes is that the returned exit disappears, which for these
two clauses was the entry node anyway.

An earlier draft of this review proposed giving `Unwind` a real
`EA_Ret None p -> FunctionResult p` edge on the grounds that it is "closer to
its meaning". **That was reasoning from intuition, not from `pstep`.** `Unwind`
is a residual marker used while a return propagates outward through pending
statements up to the nearest activation frame (`VIMP_Proc.thy:28-34`), and
`pstep_Unwind_stuck` (`Control_Simulation.thy:693`) states that `Unwind` has no
`pstep` successor at all — the frame pop is performed by the `Seq Unwind Restore`
and bare `Restore` rules, not by `Unwind` itself. Giving it a graph edge would
assert a transition the source semantics does not have, and the residual-command
reasoning in `csim` (`unwinding`, `pop_ready`, `is_returning`,
`csim_returning_completion`) is where that mismatch would surface — the hardest
proofs in the repository, for zero observable benefit.

Rule: do not fold runtime-only residual cleanup into the continuation redesign.
If `Restore`/`Unwind` compilation is ever revisited, it should be a separate
change justified by `pstep` and `cstep` directly, with its own gate.

Note for Phase 6: `falls_through Restore = True` while the clause emits no
edges. That is consistent — `compile_continuation_unused` only claims
`~ falls_through c ==> k unused`, never the converse — and it is unreachable for
procedure bodies, which are `source_com`.

### `compile_proc`, `compile_procs`, `compile_prog`

`compile_proc` as in §5. `compile_procs` and `compile_prog` change only where
they thread the counter; `cfg_entry = FunctionEntry mnm` and the absence of a
global exit are unchanged.

### Answers to the specific questions

**§5 of the brief — how should `Seq` handle termination?** Compile `c2`
anyway, and reserve its indices. Do not special-case `Return e; c`. Reasons:
`csize` must stay a plain structural function or the `Seq` continuation
computation loses its footing; `control_at`'s `SeqRight` rule needs `c2`'s base
counter to exist; and the source-range and ownership lemmas are stated over
`{n..<n'}` with `n' = n + csize c`, which stays an equation only if allocation
is source-syntax-directed. The compiled `c2` is unreachable in the graph, which
is correct and is what CIL does (unreachable statements keep their sids and
have no preds). Nothing needs deleting, and source mapping is preserved for
free. Under the redesign the *only* structurally dead nodes in a program are
the ones the source itself makes unreachable — no compiler-invented ones.

**§6 — `if b then Return x else Return y`.** Two branch nodes plus the test,
three nodes, both branch edges into `FunctionResult p`, `k` untouched. And
`if b then Return x else Assign y a`: three nodes, the else edge into `k`, no
merge. A merge node is never allocated, so "only when needed" is automatic and
does not need a data-dependent `if` in the compile clause.

**§8 — calls and recursion.** Keep the four-place `calls` relation. It is
strictly more explicit than Goblint's `Proc` edge and is what makes
`cfg_succ_rel`'s ENTRY / COMB_CALLER / COMB_RESULT decomposition (and hence the
DG cone) work. The context-insensitive ambiguity — one `FunctionResult p` with
several possible resume continuations — is unchanged by this redesign: it is
resolved by `cstep`'s activation stack at runtime and by the context domain in
the analysis, and `CFG_Prune.thy` already models it as the COMB_RESULT
dependency `FunctionResult p -> k` for every call to `p`. This is orthogonal to
the dead-node problem and no part of the plan should touch it.

---

## 7. Proof impact matrix

Classification: **unchanged**, **local repair** (statement or proof adjusted
mechanically), **substantial** (structure of the proof changes), **new**.

### `src/Compile/VIMP_Proc_to_CFG.thy`

| Item | Class | Note |
| --- | --- | --- |
| `compile` | substantial | rewritten per §6 |
| `csize`, `compile_next_id` | new | `fst (compile Pi p c k n) = n + csize c`, by `com.induct` |
| `compile_counter_mono` | local repair | corollary of `compile_next_id` |
| `compile_entry_exit_stmt` | substantial | splits: entry is definitionally `Statement n`; the exit half disappears |
| `frag_stmts`, `frag_stmts_Un`, `frag_stmts_mono` | unchanged | |
| `compile_frag_stmts_range` | local repair | *easier*: exact range from `csize`, and the `Seq`/`If` cases lose the glue-edge sub-proofs. Statement must now read `frag_stmts E K <= insert_k`-style, i.e. continuation indices are excluded — see below |
| `compile_finite` and the `_proc`/`_procs`/`_prog` chain | unchanged | shape identical |
| `compile_call_ce_entry`, `compile_intra_tgt_not_entry`, `compile_ret_wf` | local repair | plus a new hypothesis that `k` is not a `FunctionEntry` node, discharged at `compile_proc` |
| `compile_prog_wf` | local repair | same three obligations, same skeleton |
| `compile_Call_calls`, `call_enter_*`, `return_publishes_ret_var`, `combine_collect_*` | unchanged | continuation-independent |

One statement genuinely weakens: `compile_frag_stmts_range` currently says
*every* statement index touched by the fragment is in `{n..<n'}`. Under CPS the
continuation is an endpoint outside that range, so the correct statement is

```isabelle
lemma compile_frag_stmts_range:
  "compile Pi p c k n = (n', en, E, K)
   ==> frag_stmts E K <= {n..<n'} Un (case k of Statement j => {j} | _ => {})"
```

or, more usably, keep the clean range for *sources* and handle targets through
the `pfn` lemma below.

### `src/Compile/Compile_Locality.thy` — the main cost

`pfn p n n'` is the fragment node set. Under CPS an edge target may be the
continuation, which is outside it. The generalization is uniform:

```isabelle
lemma compile_intra_pfn:
  assumes "compile Pi p c k n = (n', en, E, K)" and "(u, a, v) : E"
  shows "u : pfn p n n'" and "v : insert k (pfn p n n')"

lemma compile_calls_pfn:
  assumes "compile Pi p c k n = (n', en, E, K)" and "(u, ce, tgt, af) : K"
  shows "u : pfn p n n'" and "af : insert k (pfn p n n')"
```

Sources stay inside the fragment (they are always freshly allocated), targets
are inside or the continuation. At `compile_proc` the continuation is the
epilogue `Statement r` with `r < n'`, so `insert k (pfn p n n') = pfn p n n'`
and every *procedure-level* locality lemma keeps its current statement
verbatim. That is the key structural property: the generalization is confined
to the command level, and the procedure level is the interface everything else
uses.

| Item | Class | Note |
| --- | --- | --- |
| `pfn` | unchanged | |
| `compile_entry_is_start` | local repair | becomes definitional |
| `compile_E_shape`, `compile_K_shape` | local repair | targets gain the `k` alternative; the `Seq`/`If`/`While` glue-edge cases disappear from the proofs |
| `compile_result_target` | local repair | still true given the epilogue invariant |
| `compile_call_target_declared` | unchanged | |
| `compile_intra_pfn`, `compile_calls_pfn` | substantial | as above |
| `compile_proc_*` (entry target, intra pfn, result target, call declared, calls pfn, counter mono) | local repair | continuation instantiated to the epilogue |
| `compile_procs_*` (member, entry mem/unique, owner, tail/head disjointness, source ranges, fragment bounds) | local repair | list induction unchanged; ~20 lemmas, mechanical |
| `compile_prog_*` (intra split, entry out unique, result target, no result source, calls source stmt, call target declared, entry declared) | local repair | |
| `compiled_cfg_wf`, `compiled_cfg_wf_compile_prog` and the `D`-rules | local repair | |
| `frag_edge_intra`, `frag_edge_calls`, `frag_ok`, `valid_ltr_frag_callers`, `valid_ltr_entry_result_eq` | local repair | stated over the *procedure* fragment, so the continuation generalization does not reach them; only the `compile`-level premises they cite change |

This file is 1529 lines and roughly 40 `compile` references. Expect it to
dominate the migration effort. Nothing in it looks conceptually threatened.

### `src/Compile/Control_Residual.thy`

`control_at` gains the continuation as an index:
`control_at Pi p c k n residual v`.

| Item | Class | Note |
| --- | --- | --- |
| `compile_entry_node` | local repair | becomes trivial/definitional |
| `control_at` rules | substantial | `AssignDone` locates `SKIP` at `k` instead of `Statement (Suc n)`; `CallDone` likewise; `IfDone` and `WhileDone` collapse into "located at `k`" and no longer need to name a merge node; `SeqLeft`/`SeqRight`/`IfLeft`/`IfRight`/`WhileBody` thread the appropriate continuation |
| `control_at_initial` | unchanged shape | |
| `control_at_node_stmt` | unchanged **provided** every continuation reaching it is a `Statement` node — true with the always-allocated epilogue; needs an extra argument under the lazy-epilogue phase |
| `compile_control_at_SKIP_exit_path` | substantial, but *shrinks* | becomes "a located `SKIP` reaches `k`", which is `star.refl` in every case except source `SKIP`/`Restore` (one nop step). The `IfLeft`/`IfRight` join-hopping cases disappear |
| `control_at_source_com`, `source_com_no_Restore/Unwind` | unchanged | |

### `src/Compile/Control_Simulation.thy`

65 `compile` references, but the shape of the argument is preserved because
`cstep` is untouched.

| Item | Class | Note |
| --- | --- | --- |
| `control_at_assign_edge`, `control_at_call_edge` | local repair | conclusion becomes `(Statement j, EA_Assign x a, k') : E & control_at ... SKIP k'` where `k'` is the fragment's continuation — *simpler* than today's `Statement (Suc k)` |
| `control_at_return_edge` | local repair | unchanged conclusion |
| `control_at_if_edges` | local repair | the `WhileUnfolded` case no longer needs the loop-exit node |
| `control_at_skip_to_exit` | substantial, shrinks | mirrors `compile_control_at_SKIP_exit_path` |
| `control_at_seq_skip_reloc` | substantial, shrinks | `Seq SKIP c2` is already located at `entry c2`; the `WhileBody` case is already at the head. Most of the nop-stepping disappears |
| `intra_step` and its `inductive_cases` | unchanged | source-side only |
| `seq_after`, `unwinding`, `pop_ready`, `is_returning`, `head_call`, `head_return`, `ret_guarded`, `source_wf` | unchanged | source-side only |
| `compiled_at` | local repair | `(ex, EA_Ret None p, FunctionResult p)` becomes `(k, EA_Ret None p, FunctionResult p)` with `k` the epilogue — arguably clearer, since `k` is now an explicit parameter rather than a derived exit |
| `csim` | local repair | continuation threaded through `compiled_at` |
| `intra_step_simulation`, `csim_call_completion`, `csim_intra_completion`, `csim_return_init_completion`, `csim_returning_completion`, `csim_step`, `csim_run`, `csim_star` | substantial (mechanical) | premises re-shaped; the induction structure and the frame/stack reasoning are untouched. Risk concentrated here simply by volume |
| `frames_match_*`, `ret_store`, `pstep_*` | unchanged | |

### Other theories

| File | Class | Note |
| --- | --- | --- |
| `src/CFG/CFG_Def.thy` | unchanged | no compiler dependency |
| `src/CFG/CFG_Prune.thy` | local repair | `compile_reaches` becomes `cfg_reaches g (Statement n) k \| cfg_reaches g (Statement n) (FunctionResult p)`; the proof loses the nop hops. `compile_proc_reaches_result`, `compile_prog_entry_cfg_reaches_exit`, `cfg_exit_compile_prog` keep their statements |
| `src/Compile/Compile_Invariants.thy` | local repair | `has_call`, `returns_in`, `compile_return_edge`, `compile_no_call`, `compile_prog_flat`, range/disjointness lemmas adjust mechanically. `inv11_return_exit_unreached` is **deleted** and replaced by a statement that `Return` ignores its continuation. `inv13`, `inv14` restated with `k` |
| `src/Compile/Compile_Certificate.thy` | local repair | 2 references |
| `src/Compile/Located_Exec.thy` | unchanged | `cstep` is edge-driven |
| `src/Compile/Located_LTR.thy` | local repair | 2 references, both via `compiled_at` |
| `src/CFG/Collecting/*` (`CFG_Local_Trace`, `LTR_Abstract`, `LTR_Collect`) | unchanged | defined over `cfg`, not over `compile` |
| `src/Analysis/**` (equations, TD solver, DG, Sign, Interval, Mixed) | unchanged | consume `compile_prog` and the `cfg` record only; no dense-index assumptions found |
| `src/Analysis/Reporting/Analysis_GraphViz.thy` | unchanged | `compiled_proc_owner` recomputes `compile_proc` ranges; the shape of that recursion is preserved |
| `src/Soundness/Run_Analysis_Sound.thy`, `Mixed_Flow_Sound.thy`, `DG_Domain_Registration.thy` | unchanged | |
| `src/Soundness/Source_Activation_Sound.thy` | local repair | one `compiled_atE` destructuring at line 191; the `compile_control_at_SKIP_exit_path` + epilogue-edge composition still closes the same way |
| `src/Examples/Interprocedural/Example_Compile_Regression.thy` | local repair | `ex_nested_calls`, `compile_seq_call_edge`, `example_nested_call_preserves_outer`, `example_normal_fallthrough` hardcode `Statement (Suc n)`; regenerate |
| `src/Examples/Interprocedural/Example_Control_Simulation_Regression.thy` | local repair | |
| `src/Examples/Interprocedural/Example_Proc_Recursion_CFG.thy` | local repair | hardcoded indices 0–17; regenerate |
| Other examples (14 files reference `Statement`) | local repair | index-only churn; `Example_LTR_Collect_Regression` (69 references) is the largest |
| `src/Examples/Voblint.thy` | unchanged | prose |

### Unknown until attempted

- Whether `csim_step` and `csim_return_init_completion` reveal a place where the
  *old* exit node was doing hidden work. Reading `control_at` suggests not:
  there is no `ReturnDone` rule, so no residual is ever located at a return's
  exit, and `Restore`/`Unwind` are handled by `cstep` at `FunctionResult`
  rather than by a fragment node. But these are the two longest proofs in the
  repository and they are where a surprise would surface.
- Whether any `Interval`/`Sign` flagship example asserts an abstract value *at*
  a specific node index in a way that changes meaning rather than just index
  (e.g. an assertion at a post-assign node that is now shared with the next
  statement's pre-state — same abstract value, different name).

---

## 8. Migration plan

Every phase ends at a green `rtk make build`. Phases 1–3 are independently
useful and independently revertible.

### Phase 1 — pin down current behaviour (no semantic change)

- Add executable regression values for the 15 programs of §9 against the
  current compiler: node set, edge set, call set, and the forward-reachable
  node set.
- Add the `action_trace` / `observable` extractors of §11 and record the
  observable trace of one concrete run per program. These are the artifacts the
  old-versus-new comparison uses in Phase 4.
- Add a short `text` block in `VIMP_Proc_to_CFG.thy` recording the four
  meanings of `ex` from §2, so the ambiguity is documented before it is removed.
- Checkpoint: build green, dead nodes now *visible in the regression data*.

### Phase 2 — presentation-only pruning (reversible, no proof risk)

- In `CFG_Prune.thy`, add an executable forward-reachable node set rooted at
  every `FunctionEntry` node occurring in the graph (not only `cfg_entry`, so
  uncalled procedures still render).
- In `Analysis_GraphViz.thy`, filter rendered nodes and edges by that set.
- No analysis theorem changes; no `compile` change.
- Checkpoint: the factorial DOT loses `pp2`, `pp6`, `pp7` and their edges;
  build green. **This is the reversible first step, and it delivers the visual
  goal on its own.**

### Phase 3 — `csize` and its correspondence lemma

- Add `csize` and prove `compile_next_id : fst (compile Pi p c n) = n + csize c`
  for the *current* compiler. It holds today (`SKIP`/`Restore`/`Unwind` = 1,
  `Assign`/`Call`/`Return` = 2, `Seq` = sum, `If` = `1 + l + r + 1`,
  `While` = `1 + b + 1`).
- Derive `compile_counter_mono` from it.
- Checkpoint: build green. `csize` now exists and is trusted before it becomes
  load-bearing. If Phase 4 is abandoned, this lemma is still a strengthening.

### Phase 4 — the continuation-passing compiler

Single change to `compile` and `compile_proc` — continuation in, exit out,
`entry` retained, `Restore`/`Unwind` behaviour untouched — then repair in
dependency order:

1. `VIMP_Proc_to_CFG.thy` (ranges, finiteness, shapes, `compile_prog_wf`)
2. `CFG_Prune.thy` (`compile_reaches`)
3. `Compile_Invariants.thy`, `Compile_Certificate.thy`
4. `Control_Residual.thy` (`control_at`)
5. `Compile_Locality.thy` (the `pfn` generalization and the ownership chain)
6. `Control_Simulation.thy` (`compiled_at`, `csim`, the completion theorems)
7. `Located_LTR.thy`, `Source_Activation_Sound.thy`
8. Examples, then the old-versus-new observable-trace comparison of §11

Explicitly **out of scope for this phase**: removing the `entry` component
(Phase 7), lazy epilogues (Phase 6), any change to `Restore`/`Unwind` edges
(§6), any change to the four-place `calls` relation (never), and any new
`edge_action` constructor (§5).

Do not keep the old compiler alongside the new one as a permanent parallel
definition. A `compile_cps` plus a maintained correspondence theorem would cost
more than the repair itself (§11) and would leave two compilers in the tree —
the failure mode the project contract warns about ("generalize in place > new
API + old-API wrapper"). The compiler is one `fun` with nine clauses; widen its
definition. Keeping the *old regression data* from Phase 1 for comparison is a
different thing and is encouraged.

Interim checkpoints inside Phase 4 are per-file I/Q-clean states, not builds.
Run the batch build once at the end of each numbered step above, since each is
a session boundary in the dependency chain.

- Checkpoint after step 6: `csim_star` re-proved. **This is the semantics
  preservation gate** — the observable-trace comparison is a confidence check,
  not the gate.
- Checkpoint after step 8: full build green, regression data regenerated,
  observable traces equal to the Phase 1 baseline on all 15 programs.

### Phase 5 — retire the workarounds

- Delete `inv11_return_exit_unreached` and the "commands after the return sit
  behind a fresh unreachable exit node" sentence from the header comment of
  `VIMP_Proc_to_CFG.thy`.
- Delete the old-versus-new comparison theory. It has done its job; keeping it
  would mean maintaining a dead compiler to compare against.
- **Decide whether the Phase 2 pruning filter stays.** It is now optional and
  should be treated as such. After Phase 4 it hides only (a) one epilogue per
  always-returning procedure and (b) source-level dead code. Keeping it means
  the DOT output is not literally the graph the analysis sees, which should then
  be labelled in the output. Removing it means the rendered graph is exactly the
  compiled graph. Recommendation: keep it, labelled, until Phase 6 lands, then
  reduce it to a source-dead-code filter or drop it.
- Checkpoint: build green.

### Phase 6 — optional: lazy epilogue

Only after Phase 4 is green and the simulation proofs are stable.

- Add `falls_through` and `compile_continuation_unused`.
- Make `compile_proc` skip the epilogue when the body cannot fall through.
- Re-check `control_at_node_stmt` (the body continuation may now be
  `FunctionResult p`, so the "every located node is a `Statement`" argument needs
  the extra step that a non-falling-through body never locates a residual at its
  continuation) and `compile_result_target`.
- Checkpoint: zero compiler-generated dead nodes for factorial; build green.

### Phase 7 — optional: shrink the result tuple

Two independent cleanups, either or neither:

- Drop `entry`, which is provably `Statement n`. Deferred from Phase 4 to keep
  that phase's churn down; do it once the repaired proofs show whether `en` is
  still carried usefully or is immediately rewritten everywhere.
- Drop `next_id`, leaving `compile :: ... => cfg_node => nat => E * K` with all
  arithmetic in `csize`.

Both are cosmetic once Phase 3's lemma exists. Do them only if the range and
locality lemmas read better afterwards, and measure that on two or three lemmas
before committing to the sweep.

---

## 9. Regression-test plan

For each program record, before and after: statement node count, dead
(non-forward-reachable) node count, intra edge count, call edge count, count of
`EA_Nop` edges, and the reachable node sequence of one concrete run.

### Measured baseline (Phase 1, landed)

`src/Examples/Interprocedural/Example_Compile_Baseline.thy` records this
executably against the current compiler and is green in
`isabelle build Voblint_Examples`. Rows are `cfg_report`, i.e.
`(nodes, dead, intra, nops, calls)`.

**Counting convention.** These are *whole-program totals*: `nodes` includes
`FunctionEntry`/`FunctionResult` for every procedure, and `nops` includes the
per-procedure `FunctionEntry -nop->` bracket. Each shape below is the body of
`f` with `main` reduced to a single call, so `main`'s contribution is constant
across rows. The per-fragment figures quoted later in this section count
*statement* nodes and *non-bracket* nops only — both conventions appear, so
compare like with like.

| # | Program | nodes | dead | intra | nops | calls | dead nodes |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `skip` body | 7 | 0 | 4 | 2 | 1 | — |
| 2 | `x := 1` | 8 | 0 | 5 | 2 | 1 | — |
| 3 | `return 1` | 8 | **1** | 5 | 2 | 1 | `S1` |
| 4 | `return 1; x := 2` | 10 | **3** | 7 | 3 | 1 | `S1 S2 S3` |
| 5 | both branches return | 12 | **3** | 10 | 4 | 1 | `S2 S4 S5` |
| 6 | one branch returns | 12 | **1** | 10 | 4 | 1 | `S2` |
| 7 | loop body returns | 10 | **1** | 8 | 3 | 1 | `S2` |
| 8 | nested `if` | 16 | 0 | 15 | 6 | 1 | — |
| 9 | one call | 8 | 0 | 5 | 2 | 1 | — |
| 10 | recursive factorial | 16 | **3** | 13 | 6 | 2 | `S2 S6 S7` |
| 11 | nested calls | 12 | 0 | 7 | 3 | 2 | — |
| 12 | two call sites, one callee | 14 | 0 | 8 | 4 | 3 | — |
| 13 | statements after guaranteed return | 14 | **5** | 12 | 5 | 1 | `S2 S4 S5 S6 S7` |
| 14 | `main` only | 3 | 0 | 2 | 1 | 0 | — |
| 15 | `Restore` / `Unwind` | n/a | n/a | n/a | n/a | n/a | rejected by `wf_compile_input` |

**The measurement confirms the diagnosis exactly.** Dead nodes appear in
programs 3, 4, 5, 6, 7, 10, 13 — precisely the seven containing a `Return` — and
in no other program. Every `Return`-free program has zero dead nodes regardless
of nesting depth (see 8, 11, 12). The dead-node count is a function of `Return`
occurrences and their position, which is what §2 predicted from the type
signature alone.

Program 13 is the worst measured case: `if b then return 1 else return 2; z := 9`
yields **5** dead nodes out of 14 — two `Return` exits, the merge node, and the
two nodes of the unreachable `z := 9`. Note the mix: three are
compiler-invented, two are source-level dead code. Only the first kind is the
redesign's target.

Factorial's dead set is confirmed as exactly `{Statement 2, Statement 6,
Statement 7}` — the `pp2` / `pp6` / `pp7` of the original report — and its nop
edges as `S2->S7`, `S4->S5`, `S6->S7`, `S9->S10` plus the two entry brackets,
i.e. two dead joins and two reachable pass-throughs.

### Hand-evaluated per-fragment comparison

Statement nodes and non-bracket nops only:

| Program | Now: nodes / dead / nops | New: nodes / dead / nops |
| --- | --- | --- |
| `if b then Return x else Assign y a` | 6 / 1 / 2 | 3 / 0 / 0 |
| `while b do Return e` | 4 / 1 / 1 (dead back-edge) | 2 / 0 / 0 |
| factorial (`fac` + `main`) | 12 / 3 / 4 | 8 / 1 / 0 |

factorial after the redesign, with the always-allocated epilogue:

```
Statement 0   if n < 2                      reachable
Statement 1   return 1                      reachable
Statement 2   call fac(n-1), resume at 3    reachable
Statement 3   return n*tmp                  reachable
Statement 4   fac epilogue (ret None)       dead (removed in Phase 6)
Statement 5   N := 8                        reachable
Statement 6   call fac(N), resume at 7      reachable
Statement 7   main epilogue (ret None)      reachable
```

The `pp2 -> pp7 <- pp6` join is gone, the `4 -nop-> 5` and `9 -nop-> 10`
pass-throughs are gone, and `Statement 2`'s resume point *is* `Statement 3`,
the return statement — which is what the source says.

Full list to cover, with what each is for:

| # | Program | Checks |
| --- | --- | --- |
| 1 | `SKIP` | degenerate body; note this case gets *one node worse* (2 vs 1) because the epilogue is separate from the body node |
| 2 | `Assign x a` | the basic node-halving |
| 3 | `Return e` (as a procedure body) | no synthetic exit; epilogue dead |
| 4 | `Seq (Return e) (Assign x a)` | source dead code retained in the AST, absent from the graph, indices still reserved |
| 5 | `If b (Return x) (Return y)` | no merge node, `k` unreferenced |
| 6 | `If b (Return x) (Assign y a)` | merge-free join at `k` |
| 7 | `While b (Return e)` | no back-edge, false edge intact, loop still exitable |
| 8 | nested `If` | index ordering stays source-ordered |
| 9 | one procedure call | resume point identified with the next statement |
| 10 | recursive factorial | the flagship case above |
| 11 | nested calls (`Seq (Call ..) (Call ..)`) | two distinct continuations, `Example_Compile_Regression.ex_nested_calls` |
| 12 | two call sites to one procedure | one `FunctionResult`, two COMB_RESULT dependencies — unchanged behaviour, guard against regression |
| 13 | statements after a guaranteed return inside a branch | `Seq (If b (Return x) (Return y)) (Assign z a)` — nothing reaches `z := a` |
| 14 | empty procedure body | as #1, at procedure level |
| 15 | `Restore` / `Unwind` | unreachable by `source_com`; assert the clauses stay total and that `wf_compile_input` still rejects them at the source level |

Also worth asserting, as executable regressions rather than theorems:

- `EA_Nop` occurs only as the `FunctionEntry p -> Statement n` bracket (and for
  source `SKIP`/`Restore`). A count-based check catches accidental
  reintroduction of glue edges.
- Every node in the graph is forward-reachable from some `FunctionEntry`, except
  epilogues of non-falling-through procedures (empty after Phase 6) and nodes
  compiled from source-level dead code.

---

## 10. New invariants to prove

Statements in `fixes`/`assumes`/`shows` shape so callers can use `[where ...]`
and `[OF ...]`, per the autoformalization audit.

```isabelle
(* allocation is exactly the syntactic size *)
lemma compile_next_id:
  assumes "compile Pi p c k n = (n', en, E, K)"
  shows "n' = n + csize c"

(* the entry is the base counter, by construction *)
lemma compile_entry:
  "fst (snd (compile Pi p c k n)) = ..."   (* trivial once `entry` is dropped *)

(* sources are allocated; targets are allocated or the continuation *)
lemma compile_intra_endpoints:
  assumes "compile Pi p c k n = (n', en, E, K)" and "(u, a, v) : E"
  shows "u : Statement ` {n..<n'}"
    and "v : insert k (insert (FunctionResult p) (Statement ` {n..<n'}))"

lemma compile_calls_endpoints:
  assumes "compile Pi p c k n = (n', en, E, K)" and "(u, act, ce, af) : K"
  shows "u : Statement ` {n..<n'}"
    and "af : insert k (Statement ` {n..<n'})"
    and "EX q. ce = FunctionEntry q"

(* Return has no normal exit: the continuation is not mentioned *)
lemma compile_Return_ignores_continuation:
  "compile Pi p (Return e) k n = compile Pi p (Return e) k' n"

lemma compile_continuation_unused:
  assumes "compile Pi p c k n = (n', en, E, K)" and "~ falls_through c"
  shows "(u, a, k) ~: E" and "(u, act, ce, k) ~: K"

(* no fall-through leaves a return node *)
lemma compile_no_edge_from_return_node:
  assumes "compile Pi p c k n = (n', en, E, K)"
      and "(u, EA_Ret e p, FunctionResult p) : E"
  shows "ALL a v. (u, a, v) : E --> v = FunctionResult p"

(* FunctionResult is entered only by a matching return action *)
lemma compile_proc_result_only_ret:
  assumes "compile_proc Pi p decl n = (n', E, K)" and "(u, a, FunctionResult q) : E"
  shows "q = p & (EX e. a = EA_Ret e p)"

(* FunctionEntry ownership: only call edges enter, and the bracket is unique *)
lemma compile_proc_entry_unique:
  assumes "compile_proc Pi p decl n = (n', E, K)"
      and "(FunctionEntry p, a, v) : E" and "(FunctionEntry p, a', v') : E"
  shows "a = a' & v = v'"

(* the continuation is reachable from the entry exactly when the command can
   fall through *)
lemma compile_reaches_continuation:
  assumes "compile Pi p c k n = (n', en, E, K)" "E <= intra g" "K <= calls g"
      and "falls_through c"
  shows "cfg_reaches g (Statement n) k"

(* procedure-level: entry reaches result, unconditionally *)
theorem compile_proc_reaches_result:  (* already exists; must survive *)
  assumes "compile_proc Pi p decl n = (n', E, K)" "E <= intra g" "K <= calls g"
  shows "cfg_reaches g (FunctionEntry p) (FunctionResult p)"

(* every node in the compiled program is forward-reachable from some entry,
   modulo source-level dead code -- the invariant that makes the graph honest *)
theorem compile_prog_no_synthetic_dead_nodes:
  assumes "wf_compile_input Pi ps mnm main"
      and "ALL p decl. Pi p = Some decl --> reachable_com (body decl)"
  shows "cfg_nodes (compile_prog Pi ps mnm main)
           <= {v. EX q. cfg_reaches (compile_prog Pi ps mnm main) (FunctionEntry q) v}"
```

The last one is the theorem that actually states the goal of this redesign, and
it is worth stating even if `reachable_com` (no source-level dead code) has to
be assumed. Note it is *false* for the current compiler and *true* after
Phase 6 — which makes it the cleanest possible acceptance criterion.

Also keep, unchanged in statement: `compile_prog_wf`, `compiled_cfg_wf_compile_prog`,
`procs_compiled_compile_prog`, `compile_procs_head_disjoint`,
`compile_prog_entry_cfg_reaches_exit`.

---

## 11. How to state semantic preservation

Do **not** attempt a legacy-vs-new CFG equivalence theorem. Reasons:

- The two graphs have different node sets, different node counts, and different
  index assignments. Any relation would have to be a simulation modulo a
  node-renaming *and* modulo `EA_Nop` stuttering *and* modulo the removed merge
  nodes — three quotients at once, over a relation between two compilers only
  one of which will survive.
- The property that matters is not "the new CFG resembles the old one" but "the
  new CFG is a faithful compilation of the source". That property already has a
  name in this repository.

The correct anchors are the existing endpoints, re-proved for the new compiler:

1. `csim_star` (`Control_Simulation.thy:2241`) — the compiled execution
   simulates the source small-step semantics, with literal store equality.
   This *is* semantics preservation, and it is stated over `pstep`, so it is
   compiler-independent in statement and compiler-dependent only in proof.
2. `source_completes_ltr_collect_exit` and `ltr_collect_semantic_postfix` — the
   activation-local trace anchors named in the project contract.
3. `compile_prog_entry_cfg_reaches_exit` — connectivity, the analogue of
   Goblint's `Not_connect` check.
4. `compile_prog_wf`, `compiled_cfg_wf_compile_prog`, `procs_compiled_compile_prog`
   — the structural contracts the analysis layer consumes.

### The migration-time correspondence check

A lightweight old-versus-new comparison *is* worth having while both compilers
exist on the branch. Not as a theorem — as executable data, on the 15 programs
of §9. Concretely, add to the Phase 1 regression theory:

```isabelle
(* the actions along one concrete execution, glue nops removed *)
definition action_trace :: "cfg => cfg_node => store => nat => edge_action list"
  where "action_trace g v s bound = ..."   (* bounded deterministic-run extractor *)

definition observable :: "edge_action list => edge_action list"
  where "observable = filter (%a. a ~= EA_Nop)"
```

and compare, per program:

1. `observable (action_trace old ...) = observable (action_trace new ...)` — the
   sequence of *effectful* transfers is identical.
2. Final store and final activation-stack depth agree.
3. The reachable node count and the dead node count, as a regression table
   (§9) — this is what actually documents the improvement.

Check (1) is the honest content of "same behaviour modulo stuttering": both runs
perform the same assignments, guards, calls and returns in the same order, and
differ only in identity-labelled steps. It is cheap because `edge_step EA_Nop`
is `Some` and both runs are deterministic on these programs, so a bounded
executable extractor suffices — no coinduction, no relation, no maintenance
burden after Phase 4.

Deliberately *not* proposed: a `simulation old new` relation or a bisimulation
modulo node renaming. Those would need to survive the removal of the old
compiler, which is the point of the migration, and the effort is better spent
re-closing `csim_star`. Delete the comparison theory in Phase 5.

Concretely, the observation that makes this safe: `cstep` (`Located_Exec.thy`)
is defined purely over `intra` / `calls` membership and `edge_step`, and
`edge_step EA_Nop = Some`. Removing a glue nop edge `u -nop-> v` while
redirecting `u`'s real predecessor edges to `v` produces a `cstep` run that is
the old run with one identity step deleted. That is the informal stuttering
argument; `csim_star` is where it gets discharged formally, against the source
rather than against the old graph.

---

## 12. Open questions

1. ~~**`Unwind`'s compile clause.**~~ **Resolved: leave `Restore` and `Unwind`
   unchanged.** An earlier draft proposed an `EA_Ret None p` edge for `Unwind`;
   that was intuition rather than semantics. `pstep_Unwind_stuck` shows `Unwind`
   has no source successor at all, so a graph edge would assert a transition the
   source semantics lacks, and the fallout would land in the residual-command
   reasoning of `csim`. See §6. Any future change here needs its own
   justification from `pstep`/`cstep` and its own gate.
2. **`SKIP`'s node.** Keeping it preserves `compile_entry_node` and
   `control_at_node_stmt` at the cost of one nop node per source `SKIP`, and it
   costs the empty-procedure case one extra node versus today. The alternative
   (`csize SKIP = 0`, entry = `k`) is cheaper in the graph and more expensive in
   the proofs. Recommendation is to keep the node; worth confirming that no
   example depends on an empty procedure having exactly one statement node.
3. **Lazy versus always-allocated epilogue.** Phase 6 removes the last dead
   node but makes the body continuation possibly `FunctionResult p`, which
   requires relaxing or re-arguing `control_at_node_stmt`. Is one dead node per
   always-returning procedure acceptable indefinitely?
4. **Whether to keep the Phase 2 rendering filter after Phase 4.** It would
   then be hiding only source-level dead code — arguably still desirable, but it
   means the DOT output is not the graph the analysis sees. If kept, it should
   be visibly labelled in the output.
5. **`FunctionEntry` bracket label.** Goblint uses a distinct `Entry fd` edge
   action where this repo uses `EA_Nop`. Introducing `EA_Entry` would make the
   nop-count regression check in §9 exact ("`EA_Nop` should not occur at all in
   a program without source `SKIP`"). Cost measured, not guessed: it is the same
   cost as `EA_ReturnImplicit` in §5 — a new field in `tf`, `etf`, `etf_st` and
   `dgs`, eight record literals, and three exhaustive case analyses. Not worth it
   for a labelling improvement; recording the option so it is not rediscovered.
6. **Do any Interval/Sign flagship assertions read a post-assign node whose
   identity merges with the next statement's pre-state node?** Same abstract
   value either way, but the example's *phrasing* may need to change rather than
   just its index. Needs a pass over the 14 example files during Phase 4 step 8.

---

## Recommendation

Adopt option **E**, continuation-passing compilation, as the target
architecture: the continuation becomes an input, `Return` ignores it, `If` and
`While` allocate no join or exit nodes, `Seq` and `Assign` allocate no glue
nops, and each procedure gets one epilogue node standing for the implicit
return. This is the same algorithm Goblint-CIL uses (`cfgStmt s next break cont`,
`Return _ -> ()`), expressed functionally, and it lands the node type on
Goblint's own reading of it — program points between transfer functions.

Ship it in the phase order of §8, with Phase 2 (presentation-only pruning) first
so the visual goal is met immediately and reversibly, and Phase 3 (`csize`)
next so the arithmetic the redesign depends on is proved against the current
compiler before it becomes load-bearing.

Scope discipline, in one list — the redesign changes the continuation's
direction and nothing else:

| Change | Phase | Status |
| --- | --- | --- |
| Continuation becomes an input; `Return` ignores it | 4 | core |
| `exit` leaves the result tuple | 4 | core |
| `csize` for forward source-ordered numbering | 3 | prerequisite, trade-off stated (§5) |
| Four-place `calls` relation | — | **unchanged** |
| `Restore` / `Unwind` edges | — | **unchanged** (§6) |
| `edge_action` constructors | — | **unchanged** (§5) |
| Analysis framework definitions | — | **unchanged** |
| `entry` leaves the result tuple | 7 | deferred cleanup |
| Lazy epilogue | 6 | landed (`fe5e9733`): `IfDone`/`SeqRight` guarded by `falls_through`, epilogue edge conditional |
| Presentation pruning | 2 | rejected: hid the compiler-level issue instead of fixing it; removed |
| Old-vs-new observable-trace comparison | 1, 4, deleted in 5 | confidence check, not a gate |

No analysis framework definition requires changes; examples and node-index
assertions require regeneration (14 files, ~285 index-bearing lines). The proof
cost is concentrated in `Compile_Locality.thy` (generalizing `pfn` with the
continuation, ~20 mechanical lemma repairs) and `Control_Simulation.thy` (volume,
not difficulty), and two of the fiddliest existing lemmas —
`control_at_skip_to_exit` and `control_at_seq_skip_reloc` — get substantially
shorter because the nop hops they exist to traverse are no longer generated.

The risks are not in the continuation idea. They are in `control_at`, the
locality lemmas, the two long completion theorems in `Control_Simulation.thy`,
and the node-index-sensitive examples — which is where the phase boundaries and
the §7 impact matrix put the attention.

---

## Implementation status

### Landed

**Phase 1 — regression baseline.** `src/Examples/Interprocedural/Example_Compile_Baseline.thy`
(313 lines), registered in `src/Examples/ROOT`, green in
`isabelle build Voblint_Examples`. Contains:

- executable structural successors (`succ_list`), one clause per source of
  `cfg_succ_rel`: INTRA, ENTRY, COMB_CALLER, COMB_RESULT;
- node inventory, entry-rooted forward reachability (`reach_from`, `reach_list`),
  dead-node and nop-edge projections;
- `cfg_report` — the `(nodes, dead, intra, nops, calls)` row per program;
- all 15 regression programs of §9, with the measured table recorded there;
- the observable-trace machinery of §11: `step_label`, `step_exec`,
  `run_labels`, `observable`, `trace_from_entry`. Verified end to end — factorial
  from a zero store yields 8 nested `LCall ''fac''`, the base-case return, then 8
  `LRet ''fac''` unwinds.

**Phase 2 — reachability pruning for rendering, rejected.** An earlier draft
added a `prune_cfg` rendering filter (`src/Examples/Tooling/
Example_Pruned_GraphViz.thy`, now removed) that dropped entry-unreachable nodes
from the DOT output without touching the compiler. It reduced the factorial
render's dead-node count to zero, but issue #64's acceptance criteria are about
the compiled graph, not the rendered projection of it — approach 3 from the
issue, not the continuation-passing approach this document commits to. Phase 6
below removes the epilogue at the source instead.

**Phase 3 — `csize` and `compile_next_id`.** `src/Compile/Compile_Size.thy`,
registered in `src/CFG/ROOT`. Proves
`compile Pi p c n = (n', en, ex, E, K) ==> n' = n + csize c` for the current
compiler, plus `compile_fst_next_id` and `compile_counter_mono_via_csize`
(showing the existing inequality is a consequence).

Deviation from the plan, deliberate: `csize` lives in its own theory rather than
inside `VIMP_Proc_to_CFG.thy`. Reason is tooling, not design — see below. When
`VIMP_Proc_to_CFG.thy` becomes editable, `csize` should move into it directly
above `compile`, because Phase 4's `Seq` clause has to *call* `csize`, and a
definition cannot be used by a theory it imports. `Compile_Size.thy` then
collapses into that file and its ROOT entry is removed. Until then the split is
harmless: Phase 3's only consumer is Phase 4.

**Phase 4 prototype — design validated before the rewrite.**
`src/Examples/Interprocedural/Example_CPS_Prototype.thy`, registered in
`src/Examples/ROOT`. `compile_k` / `compile_proc_k` / `compile_procs_k` /
`compile_prog_k` implement §6 verbatim, beside the current compiler rather than
replacing it, purely to check the rules and the arithmetic against measured
graphs. It is deleted when `compile` is rewritten.

Proved:

- **`compile_k_next_id`** — `n' = n + ksize c`. This is the trusted-arithmetic
  obligation of §5, the one real risk in the forward-numbering choice, and it
  goes through by the same induction skeleton as the current
  `compile_counter_mono`.
- **`compile_k_entry`** — `en = Statement n` still holds for every command, so
  `compile_entry_node` survives the redesign unchanged.
- **`compile_k_E_shape`** — a target is an allocated `Statement`, the own
  `FunctionResult p`, or **the continuation**. §7 predicted exactly this extra
  disjunct, and it is what lets the "no intra edge enters a procedure entry"
  condition be proved without dragging a side condition through the induction.
  Note the proof needs explicit `consider`/`cases` per branch: `auto` cannot
  chain the two-premise IH, matching the existing `compile_E_shape` style.
- **`compile_prog_k_wf`** — `wf_cfg (compile_prog_k Pi ps mnm main)`. The
  continuation-passing output satisfies the same three structural conditions as
  today's, with the command-level continuation hypothesis discharged at
  procedure level by the epilogue being a `Statement` node, exactly as §7
  claimed.
- `compile_k_Return_ignores_continuation` — `Return`'s fragment is independent
  of `k`.

Measured, `(nodes, dead, intra, nops, calls)`, current then
continuation-passing:

| # | Program | current | CPS | dead |
| --- | --- | --- | --- | --- |
| 1 | `skip` body | (7, 0, 4, 2, 1) | (8, 0, 5, 3, 1) | 0 → 0 |
| 2 | `x := 1` | (8, 0, 5, 2, 1) | (8, 0, 5, 2, 1) | 0 → 0 |
| 3 | `return 1` | (8, 1, 5, 2, 1) | (8, 1, 5, 2, 1) | 1 → 1 |
| 4 | `return 1; x := 2` | (10, 3, 7, 3, 1) | (9, 2, 6, 2, 1) | 3 → 2 |
| 5 | both branches return | (12, 3, 10, 4, 1) | (10, 1, 8, 2, 1) | **3 → 1** |
| 6 | one branch returns | (12, 1, 10, 4, 1) | (10, 0, 8, 2, 1) | **1 → 0** |
| 7 | loop body returns | (10, 1, 8, 3, 1) | (9, 0, 7, 2, 1) | **1 → 0** |
| 8 | nested `if` | (16, 0, 15, 6, 1) | (12, 0, 11, 2, 1) | 0 → 0 |
| 9 | one call | (8, 0, 5, 2, 1) | (8, 0, 5, 2, 1) | 0 → 0 |
| 10 | recursive factorial | (16, 3, 13, 6, 2) | (12, 1, 9, 2, 2) | **3 → 1** |
| 11 | nested calls | (12, 0, 7, 3, 2) | (12, 0, 7, 3, 2) | 0 → 0 |
| 12 | two call sites | (14, 0, 8, 4, 3) | (13, 0, 7, 3, 3) | 0 → 0 |
| 13 | after guaranteed return | (14, 5, 12, 5, 1) | (11, 2, 9, 2, 1) | **5 → 2** |
| 14 | `main` only | (3, 0, 2, 1, 0) | (4, 0, 3, 2, 0) | 0 → 0 |

Confirmations:

- **Factorial lands exactly on the §9 prediction.** 8 statement nodes (12 total),
  `dead_list = [Statement 4]` — the single `fac` epilogue — and nop edges reduced
  to the two procedure-entry brackets. Zero glue nops.
- **The `calls` column is identical in every row.** The call relation is
  untouched, as required.
- **Glue nops are eliminated everywhere.** Every remaining `EA_Nop` is a
  procedure-entry bracket or a source `SKIP`; the nop count drops to the number
  of procedures in every program that has no source `SKIP`.
- **Observable traces are equal** for programs 2, 6 and 10 (factorial checked to
  200 steps, covering all 8 recursive activations and their unwinds). The
  redesign changes node identities, not behaviour.
- **The two predicted regressions are real.** Programs 1 and 14 gain one node,
  because a `skip` body and its epilogue are separate nodes where the current
  compiler collapses them. §12 question 2 flagged this; it is now measured rather
  than suspected.
- **Residual dead nodes are exactly the epilogues of non-falling-through
  procedures** (rows 3, 5, 10) plus genuine source-level dead code (rows 4, 13).
  This is what Phase 6's lazy epilogue removes, and it confirms that no
  compiler-invented dead node survives for any falling-through procedure.

### Editability, resolved

Phases 2, 4, and the `VIMP_Proc_to_CFG.thy` half of Phase 3 needed edits to
theories the PIDE MCP server treated as read-only (`Cannot edit base session
theory Voblint_CFG.VIMP_Proc_to_CFG`), because `.mcp.json` launched the server
with `-l Voblint_Soundness` and every repo theory sat inside the prebuilt
base heap.

Fix: base logic changed to `Voblint_VIMP`, which keeps the `Voblint_VIMP` heap
warm while making `src/CFG`, `src/Analysis`, `src/Soundness` and
`src/Examples` load dynamically. After the server restart the compiler theory is
editable and Phase 4 proceeds.

### Phase 4, landed

The continuation-passing `compile` / `compile_proc` are landed in
`VIMP_Proc_to_CFG.thy` together with the arithmetic and shape lemmas the
dependent files consume. Repair order followed §8; every file below is clean
and the batch build (`Voblint_Soundness` and `Voblint_Examples`) is green.

| File | State |
| --- | --- |
| `VIMP_Proc_to_CFG.thy` | clean: `csize`, `compile_next_id`, `compile_entry`, `kstmt`, `compile_frag_stmts_range`, `compile_E_shape`, `compile_SeqE`/`compile_IfE`/`compile_WhileE`/`compile_procE`, `compile_prog_wf` |
| `CFG_Prune.thy` | clean: `compile_reaches` now "entry reaches the continuation or the result" |
| `Compile_Invariants.thy` | clean: `inv11_return_exit_unreached` replaced by `inv11_return_ignores_continuation` |
| `Control_Residual.thy` | clean: `control_at` carries the continuation; `compile_control_at_SKIP_exit_path` lost its join hops |
| `Control_Simulation.thy` | clean: `compiled_at`, `csim`, `procs_compiled` carry the continuation |
| `Compile_Certificate.thy` | clean: destructuring replaced by `compile_procE` |
| `Compile_Locality.thy` | clean: fragments identified by `compile_proc \<Pi> r d m = (m', Ep, Kp)` plus the entry edge into `Statement m` |
| `Located_LTR.thy` | clean: `compile_prog_main_base` reads the epilogue node off `procs_compiled_proc` |
| `Source_Activation_Sound.thy` | clean: the completed-run path runs to the epilogue node, then the `EA_Ret` edge |
| examples | landed: index-bearing regressions regenerated |

Two decisions taken during the repair that the plan above did not anticipate:

**`csize` moved into `VIMP_Proc_to_CFG.thy` and `Compile_Size.thy` was deleted**
(with its `ROOT` entry), exactly as §"Landed" predicted would be needed once the
compiler theory became editable: the `Seq` clause has to *call* `csize`.

**`Restore` and `Unwind` emit a nop to their continuation, not nothing.** §6
proposed "allocate one node, emit no edges" as the faithful port of the current
stubs. That reading is wrong: the old clauses returned *entry = exit*, i.e. the
fragment was transparent and control flowed through it. Under continuation
passing, transparency is `Statement n --EA_Nop--> k`; emitting nothing makes the
node a dead end instead. The difference is observable in `compile_reaches`, and
through it in `compile_prog_entry_cfg_reaches_exit`. That theorem has no proof
consumer (the exit-cone coverage the D/G layer needs is discharged per node by
`DG_Coverage`, not by whole-program connectivity), but it is the connectivity
witness that pins the transparent encoding: emitting nothing would force a
`source_com` hypothesis onto it. Both clauses remain unreachable for source programs, so this is a choice
between two vacuous translations; the transparent one is the one that keeps the
downstream statements intact.

**Procedure fragments are identified by `compile_proc`, not by the body's
`compile` call.** Every locality lemma used to carry a hypothesis
`compile \<Pi> r (body d) m = (m', en, ex, Eb, Kb)` whose only job was to fix the
fragment's counter range and name its entry node. Under continuation passing the
fragment also contains the epilogue node, so the body's range `[m, m + csize)`
is one short: the right interval is `compile_proc`'s own `[m, Suc (m + csize))`.
Restating the hypothesis as `compile_proc \<Pi> r d m = (m', Ep, Kp)`, with the
entry edge written literally as `(FunctionEntry r, EA_Nop, Statement m)`, makes
the range correct by construction and drops the separate "the entry node is the
start counter" step from every proof that used it. `frag_ok` and
`compile_prog_proc_frag` follow the same shape.

Decisions unchanged: the four-place `calls` relation, `edge_action`, and every
analysis framework definition are untouched.

### New shapes worth knowing

- `compiled_at \<Pi> g p c0 k n` and `control_at \<Pi> p c0 k n r v` both carry
  the continuation, and `procs_compiled` existentially quantifies it. At
  procedure level the continuation is the epilogue node, so the fall-through
  return edge is stated from `k` — replacing the old `ex`.
- `compile_frag_stmts_range` reads
  `frag_stmts E K \<subseteq> {n..<n'} \<union> kstmt k`, with
  `kstmt` the continuation's index (empty unless it is a `Statement`).
- Command-level locality is `insert k (pfn p n n')` on both endpoints; at
  procedure level `k` is inside the range and the statement collapses to the
  original `pfn p n n'`.
- `compile_SeqE` / `compile_IfE` / `compile_WhileE` / `compile_procE` are the
  destructuring rules every dependent proof now uses instead of
  `(auto split: prod.splits)` over the compile clauses. They carry the entry
  equalities and the `csize` arithmetic, which is what removes the auxiliary
  `compile ... = (...)` premises the old `control_at` rules had to thread.

## 12. The unreachable epilogue, and how it was closed

The factorial example used to show `fac` with an epilogue node that nothing
targets: every path through the body ends in an explicit `return`. `main`'s
epilogue is reachable, because `main` falls off its end. Goblint allocates its
pseudo-return node lazily (§3); this section originally recorded why the same
move was blocked here, and then how commit `fe5e9733` closed it.

**Resolved.** `IfDone` in `Control_Residual.thy` is now guarded by
`falls_through (If b c1 c2)` and `SeqRight` by `falls_through c1`, which makes
`control_at_SKIP_imp_falls_through` provable — a located `SKIP` now witnesses
that its command can complete normally. `compile_proc` emits the
`(k, EA_Ret None p, FunctionResult p)` edge only when `falls_through (body
decl)`; otherwise it still reserves the counter slot without wiring it, so
`csize`/`pfn`/`frag_stmts` keep their statements unchanged. `procs_compiled`'s
two consumers take the conditional edge. `dead_list factorial_cfg` is `[]`.

### What is proved

`falls_through :: com => bool` (in `VIMP_Proc_to_CFG.thy`, beside `csize`) is
the syntactic over-approximation of "control can leave this fragment through its
continuation": `Seq` conjoins, `If` disjoins, `While` is `True` (the guard may
fail on the first test), `Return` is `False`.

Two lemmas in `CFG_Prune.thy` refine `compile_reaches` into its two disjuncts:

```isabelle
compile_reaches_falls_through:
  compile ... = (n', en, E, K) ==> E <= intra g ==> K <= calls g
    ==> falls_through c ==> cfg_reaches g en k
compile_reaches_returns:
  compile ... = (n', en, E, K) ==> E <= intra g ==> K <= calls g
    ==> ~ falls_through c ==> cfg_reaches g en (FunctionResult p)
```

**This settles the reachability question: a lazy epilogue would not put a side
condition on `compile_prog_entry_cfg_reaches_exit`.** A body that never falls
through still reaches `FunctionResult p` along its explicit `EA_Ret` edges, so
`compile_proc_reaches_result` splits on `falls_through` and the whole-program
theorem keeps its current unconditional statement. The enabling detail is that
`cfg_succ_rel` already relates a call site directly to its continuation
(`COMB_CALLER`), so no callee-termination fact is needed.

### What "do not allocate the epilogue" has to mean

Not "emit no edges mentioning the continuation". That is false:

```isabelle
compile \<Pi> p (Seq (Return e) (Assign x a)) k n
```

has `~ falls_through`, yet the dead `Assign` still emits
`Statement (Suc n) --EA_Assign x a--> k`. The continuation is referenced, from
an unreachable node. The usable invariant is reachability, not absence of
references --- which is what `compile_reaches_returns` gives.

So the change is to drop the `EA_Ret None p` edge, and to keep the counter:
`compile_proc` should still return `Suc (n + csize (body decl))`, reserving the
epilogue index without wiring it. Every `csize`, `pfn`, `frag_stmts` and
ownership lemma then keeps its exact current statement, and the node disappears
from the rendered CFG because no edge mentions it. Spending one `nat` is much
cheaper than making the counter arithmetic conditional.

### What blocked it, and how it closed

`procs_compiled` used to require, for every declared procedure,

```isabelle
(k, EA_Ret None p, FunctionResult p) \<in> intra g
```

unconditionally. Two places consumed it: the `Nested`/`inner = SKIP` case of
`csim_intra_completion`, where a completed callee runs to `k` and takes the
edge, and `source_completes_valid_ltr_result`. Both held only
`control_at \<Pi> p c0 k n SKIP v`, so conditioning the epilogue on
`falls_through` needed

```isabelle
control_at \<Pi> p c0 k n SKIP v ==> falls_through c0
```

which was false before the guard, on exactly the factorial shape:

```isabelle
control_at \<Pi> p (If b (Return e1) (Return e2)) k n SKIP k
  \<and> \<not> falls_through (If b (Return e1) (Return e2))
```

`IfDone` carried no premise and `SeqRight` did not require the left command to
have completed normally, so `control_at` said where a residual sits without
saying whether that location was reachable.

Commit `fe5e9733` closed it: `IfDone` is now guarded by
`falls_through (If b c1 c2)` and `SeqRight` by `falls_through c1` --- both true
of every reachable configuration --- and `control_at_SKIP_imp_falls_through`
goes through by induction on the strengthened relation. `control_at` is
strictly stronger and every theorem in this section keeps its statement.

The new premises are discharged at each construction site inside
`Control_Simulation.thy` (the `SeqRight` and `*Done` sites across
`intra_step_simulation`, `control_at_skip_to_exit`, and the four `csim_*`
completion theorems). The one non-local site, the `Seq SKIP c2 --> c2` step,
recovers `falls_through c1` from the `SeqLeft` sub-derivation rather than from
context, so the induction is well-founded rather than circular.
