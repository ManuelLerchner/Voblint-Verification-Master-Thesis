# IMP2 native parameters and return values — migration plan

Status: design agreed; source, CFG, and compiler-correctness layers implemented.
The `Voblint_Analysis` session is not yet migrated — see
`COMBINE_METADATA_MIGRATION.md` for current status and the remaining slices.

This document records the current migration plan for extending the procedural
IMP2 language with native call-by-value parameters and activation-local return
values while preserving the verified pipeline:

```text
IMP2 source semantics
-> CFG compilation
-> compiler simulation
-> interprocedural collecting semantics
-> D/G equation generation
-> verified solver
-> computed post-solution
-> source-level soundness
```

The immediate target example is:

```c
proc twice(p) {
    return p + p;
}

main() {
    x = twice(3);
    y = twice(10);
}
```

The computed result should distinguish the two calling contexts and certify the
returned values against source executions.

The recursive witness for this MVP must respect the "final result expression
only" restriction. A direct expression-level recursive return such as:

```c
return count(n - 1) + 1;
```

is out of scope for the first version because calls are commands, not
expressions. The compatible recursive shape is:

```c
proc count(n) result r {
  if (n == 0) {
    r := 0;
  } else {
    Call (Some r) count [n - 1];
    r := r + 1;
  }
}
```

This remains recursive, result-bearing, and activation-local, while staying
within the MVP command language.

## 1. Current state

The current source language has:

- parameterless procedures only;
- no return values;
- `Call p` as the only source-level call form;
- runtime-only `Restore`;
- caller-local restoration via `combine_states`.

The key theories are:

- `src/IMP2/IMP2_Proc.thy`
- `src/IMP2/IMP2_Notation.thy`
- `src/IMP2/IMP2_Bridge.thy`
- `src/CFG/IMP2_Proc_to_CFG.thy`
- `src/Formalization/Pipeline/Compiler_Correctness.thy`

Concrete call semantics today:

```text
Call p
-> Seq body Restore
-> enter_state caller
-> run callee body
-> Restore
-> <caller | callee_exit>
```

This is enough for global-channel communication, but not for native arguments or
return values.

## 2. Goblint alignment

Goblint's analysis interface already treats calls and returns as structured
operations:

```text
enter(caller, destination, callee, actuals)
return(callee, return_expr)
combine_env(caller_before, callee_exit)
combine_assign(destination, returned_value)
```

The relevant upstream implementation points are:

- `src/framework/analyses.ml`
- `src/framework/constraints.ml`

This matters because it shows that the clean design is not a single global
`ARG`/`RET` protocol. Arguments belong to call entry. Return values belong to the
callee exit and the return combine.

## 3. Core design decision

Use native actuals/formals and optional call destinations, with procedure-level
final return expressions.

Do not add arbitrary early returns in the first version.

This keeps the MVP semantically clean without introducing a large new control
effect through `Seq`, `If`, and `While`.

Calls remain commands. The MVP does not add expression-level calls.

## 4. Revised source datatypes

Planned source declaration shape:

```isabelle
record proc_decl =
  formals :: "vname list"
  body    :: com
  result  :: "aexp option"
```

Planned command shape:

```isabelle
datatype com =
    SKIP
  | Assign vname aexp
  | Seq com com
  | If bexp com com
  | While bexp com
  | Scope com
  | Call "vname option" pname "aexp list"
  | RestoreInternal "aexp option"
```

Notes:

- `RestoreInternal` is runtime-only, not source syntax.
- Existing `Call p` remains as sugar for `Call None p []`.
- Existing procedures become declarations with `formals = []` and `result = None`.

## 5. Revised runtime frame

Planned runtime frame:

```isabelle
datatype frame = Frame store "vname option"
```

The frame stores:

- the caller store;
- the optional destination variable.

It does not store the procedure name or declaration. The result expression stays
in the runtime control via `RestoreInternal`.

This avoids the semantic hole where nullary `Restore` no longer knows which
 procedure result expression to evaluate.

## 6. Concrete small-step plan

### Call entry

For:

```text
Call dst p actuals
```

and `Pi p = Some decl`:

1. evaluate actuals in the caller store;
2. build `enter_state caller`;
3. initialize formals in that callee store;
4. push `Frame caller dst`;
5. rewrite to `Seq (body decl) (RestoreInternal (result decl))`.

Conceptually:

```text
vals   = map (λe. aval e caller) actuals
callee = bind_formals (formals decl) vals (enter_state caller)
```

### Return / restore

At:

```text
(RestoreInternal result_expr, callee_exit, Frame caller dst # frs)
```

evaluate the result before caller locals are restored:

```text
ret      = map_option (λe. aval e callee_exit) result_expr
restored = combine_states caller callee_exit
after    = combine_assign dst ret restored
```

Correct order:

```text
evaluate result in callee exit state
-> restore caller locals / keep callee globals
-> assign optional return value in caller
```

Incorrect order:

```text
restore first
-> evaluate result in restored state
```

That would lose callee-local formal values.

## 7. Helper definitions

Planned:

```isabelle
bind_formals xs vs s =
  fold (λ(x, v) st. st(x := v)) (zip xs vs) s
```

```isabelle
combine_env caller callee = combine_states caller callee
```

```isabelle
combine_assign None _ s = s
combine_assign (Some x) (Some v) s = s(x := v)
```

No definition is planned for `combine_assign (Some x) None`. That case should be
ruled out by well-formedness, not assigned arbitrary semantics.

## 8. Well-formedness conditions

The MVP should reject malformed programs structurally.

Required conditions:

- callee exists in the procedure table;
- `length actuals = length (formals decl)`;
- `distinct (formals decl)`;
- `dst = Some _ ⟹ result decl = Some _`.

Allowed:

- `dst = None` with `result = None`;
- `dst = None` with `result = Some e` (ignored result).

Disallowed:

- `dst = Some x` with `result = None`.

This is intentional. A result-bearing call into a resultless procedure should
not silently behave like a no-op.

## 9. CFG plan

The current CFG carries only:

- `EA_Enter`;
- combine triples `(call_pp, exit_pp, ret_pp)`.

That is not enough for parameters and returns.

Planned call-entry action:

```isabelle
datatype edge_action =
    EA_Nop
  | EA_Assign vname aexp
  | EA_Assume bexp
  | EA_AssumeNot bexp
  | EA_Enter "vname list" "aexp list"
```

Planned combine metadata:

```isabelle
record combine_info =
  call_node   :: pp
  exit_node   :: pp
  return_node :: pp
  destination :: "vname option"
  result_expr :: "aexp option"
```

Concrete CFG semantics then becomes:

- `EA_Enter formals actuals` evaluates actuals in the caller state and binds them
  into the callee entry store;
- combine evaluates `result_expr` in the callee exit state, restores the caller,
  then assigns the destination.

## 10. Collecting-semantics plan

The current collecting semantics uses:

- `edge_collect EA_Enter S = enter_state \` S`;
- `collect_combine_pp` with plain `<caller | callee_exit>`.

This must be refined to match the new source semantics.

Planned shape:

- `edge_collect (EA_Enter formals actuals)`;
- destination-aware combine collection using `combine_info`.

The source/CFG agreement proof must use the same evaluation order as the source
restore rule:

```text
callee result evaluation
-> combine_env
-> combine_assign
```

## 11. D/G interface plan

Current generic interface:

```isabelle
dgs_enter   :: D -> G -> G × D
dgs_combine :: D -> D -> G -> G × D
```

Current conclusion:

- parameter initialization belongs semantically to `enter`;
- destination-aware return assignment belongs semantically to `combine`;
- plain metadata-free `dgs_combine` is too weak for the full new call shape.

Planned minimal extension:

```isabelle
dgs_enter   :: call_info => D => G => G × D
dgs_combine :: call_info => D => D => G => G × D
```

where `call_info` carries at least:

- formals;
- actuals;
- destination;
- result expression;
- callee identity if needed by an instance.

This decision still needs one explicit paper pass before implementation. The open
question is whether some metadata can be closed over by generated trees instead of
changing the abstract interface everywhere. The current bias is toward explicit
`call_info`.

## 12. Bridge and compiler-simulation impact

The highest proof risk is not syntax or CFG generation. It is the
source-to-CFG compiler simulation.

Main hotspots:

- `src/IMP2/IMP2_Bridge.thy`
- `src/Formalization/Pipeline/Compiler_Correctness.thy`

Reasons:

- `source_com` currently excludes only nullary runtime `Restore`;
- `to_imp2_com` currently maps `Call p` to `Syntax.PCall p`;
- `control_at`, `frames_match`, `concrete_program_match`, and `cstep` all encode
  the old parameterless call shape and plain `<caller | callee_exit>` return.
- AFP IMP2's core semantics remains parameterless `PCall`; parameters and
  return-variable plumbing live in its parser/specification layer, so the bridge
  can no longer stay a direct constructor-by-constructor translation once local
  native actuals and destinations exist.

The new runtime-only `RestoreInternal` must be threaded through the same source vs
runtime distinction currently used for `Restore`.

Plan adjustment:

- keep source semantics, CFG compilation, and collecting semantics independent
  of the AFP bridge work;
- recover AFP alignment via a bridge-level desugaring after the local semantics
  is stable;
- treat bridge adaptation as a follow-up proof phase, not a prerequisite for
  the core semantic refactor.

## 13. Staged migration plan

### Phase 1 — source semantics prototype

- add `proc_decl`;
- add `Call dst p actuals`;
- add runtime-only `RestoreInternal result_expr`;
- define `bind_formals`, `combine_env`, `combine_assign`;
- state and prove basic well-formedness lemmas;
- work concrete traces for:
  - `x = twice(3)`;
  - two calls with different arguments;
  - recursive countdown returning a value.

Exit criterion: source semantics stable, examples execute concretely.

### Phase 2 — CFG and compiler

- extend `edge_action`;
- replace raw combine triples with metadata-bearing combine information;
- compile actual/formal binding and result metadata;
- recover recursive call compilation;
- prove structural compiler invariants with the new metadata.

Exit criterion: compiled CFG matches the intended call-entry / return shape.

### Phase 3 — collecting semantics and compiler correctness

- extend `edge_collect`;
- extend combine collecting;
- update located CFG execution;
- update source-to-CFG matching relation;
- re-establish `source_reaches_cfg_collect`.

Exit criterion: source-level reachability lifts to CFG collecting again.

### Phase 4 — D/G and abstract instances

- finalize minimal `call_info` design;
- update D/G generator if required;
- extend Sign and Interval `enter` / `combine`;
- re-prove soundness instances;
- restore executable solver transport.

Exit criterion: verified solver result certifies the new call/return semantics.

### Phase 5 — flagship example

- implement `twice`;
- prove distinct results for `twice(3)` and `twice(10)`;
- produce the solver-computed witness;
- lift it to source-level soundness;
- add GraphViz rendering if useful.

Exit criterion: end-to-end certified mixed-flow interprocedural example.

## 14. Current recommendation

Proceed with:

> native actuals/formals and optional call destinations, with procedure-level
> final return expressions, runtime-only `RestoreInternal result_expr`, small
> frames carrying caller store and destination only, metadata-bearing call entry
> and combine in the CFG, and a minimal `call_info` extension to the D/G layer if
> the paper pass confirms it is necessary.

Do not implement global `ARG_c` / `RET_c` channels.

Do not add arbitrary early return yet.

Do not leave malformed result-bearing calls with silent semantics.

## 15. Immediate next step

Before code changes beyond documentation:

1. write the exact paper mini-spec;
2. fix the source small-step rules fully;
3. write the three worked traces;
4. settle the `call_info` question at the D/G boundary.

Only then start the Isabelle edits.

## 16. Mini-spec deltas

The current paper mini-spec refines this migration plan in four important ways.

### 16.1 Recursive trace shape

The recursive worked trace must use command-level recursive calls stored into a
local and then exposed through the final result expression:

```text
Call (Some r) count [n - 1];
r := r + 1
```

not expression-level recursive returns.

### 16.2 `RestoreInternal` is essential

The earlier draft idea of keeping a nullary restore and recovering the active
procedure declaration at return is rejected. At:

```text
(Restore, callee_exit, Frame caller dst # frs)
```

the procedure result expression is not recoverable from control or frame alone.

The accepted fix is:

```isabelle
RestoreInternal "aexp option"
```

and calls rewrite to:

```text
Seq (body decl) (RestoreInternal (result decl))
```

### 16.3 Scope uses `RestoreInternal None`

`Scope` should continue to behave like the old local-scope mechanism. Its
runtime expansion becomes:

```text
Seq body (RestoreInternal None)
```

with destination `None` in the pushed frame.

This preserves the old scope behavior and keeps one runtime restore mechanism.

### 16.4 D/G change is still open, but delayed

The likely end state remains metadata-aware call hooks:

```isabelle
dgs_enter   :: call_info => D => G => G × D
dgs_combine :: call_info => D => D => G => G × D
```

but this is now explicitly delayed until after:

1. source semantics;
2. concrete traces;
3. CFG metadata;
4. collecting semantics;
5. call/restore compiler simulation.

This staging is deliberate. The cheapest invalidation point is still the pure
source-and-CFG semantics, not the abstract-analysis interface.
