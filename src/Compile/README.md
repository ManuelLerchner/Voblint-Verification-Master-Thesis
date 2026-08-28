# Compile

This session compiles a VIMP program into the control-flow graphs of
`Voblint_CFG` and proves that running the source and running the graph agree.
The graph model and its semantics live in `Voblint_CFG`; nothing there depends
on anything here.

## Vocabulary

These five words appear throughout and are worth having straight first.

| word | meaning |
| --- | --- |
| **residual** | the part of a command still left to run. Running `x = 1; y = 2` one step leaves the residual `y = 2`. |
| **fragment** | the block of nodes the compiler allocated for one command. A fragment of procedure `p` over `[m, m')` is `FunctionEntry p`, `FunctionResult p`, and `Statement m … Statement (m'-1)`. |
| **located** | "the graph's program counter is at node `v`". `control_at` relates a residual to the node it is located at. |
| **activation** | one live call of a procedure: its own store and its own position. Recursion means several activations of the same procedure. |
| **local trace** | the history of *one* activation — its path through its own fragment, plus a link to the caller that spawned it. Defined in `Voblint_CFG`, not here. |

The one design choice that explains most of the code: **`compile` takes the
continuation as an input**, rather than returning an exit node. So a fragment
never has an exit of its own, `Seq` needs no connecting edge, `If` allocates no
merge node, and `While` needs no back-edge node. Wherever you see a `k`
argument, that is the continuation.

## One program, end to end

```c
void main() { x = 0; inc(); check(0 < x); }
void inc()  { x = x + 1; }
```

*Compiled* (`compile_prog`): `inc`'s body is one statement node bracketed by its
entry and result; `main`'s three commands get three consecutive nodes, and the
call becomes a `calls` edge rather than an `intra` one, recording where to
resume.

```text
  FunctionEntry inc ──Nop──► Statement 0 ──Ret──► FunctionResult inc
                                (x = x+1)

  FunctionEntry main ──Nop──► Statement 1 ──Assign──► Statement 2
                                (x = 0)                  │
                        calls: (Statement 2, CallEdge …, FunctionEntry inc, Statement 3)
                                                         ▼
                              Statement 3 ──Check──► FunctionResult main
```

*Executed* (`cstep`): at `Statement 2` the call edge pushes a frame recording
`Statement 3`, then execution continues at `FunctionEntry inc`. Reaching
`FunctionResult inc` pops that frame and resumes at `Statement 3`. Note the
return follows **no edge** — the stack supplied the continuation.

*As a trace* (`valid_ltr`): `main`'s activation is one trace, `inc`'s call is a
second trace linked to it as its caller. The store at `Statement 3` is what
`activation_collect` reports at that node, and what the analysis must
over-approximate.

## What is proved, in order

| File | Question it answers |
| --- | --- |
| `VIMP_Proc_to_CFG.thy` | How is a command turned into nodes and edges, and is the result a well-formed graph? |
| `Compile_Invariants.thy` | Which programs may be compiled, and what holds of the graph that comes out? |
| `Simulation/Residual_Location.thy` | After some steps, which node is the program counter at? |
| `Simulation/Residual_Edges.thy` | Is the edge the compiler emitted for that command really in the graph? |
| `Simulation/Simulation_Relation.thy` | What does it mean for a source state and a graph state to agree? (`csim`) |
| `Simulation/Simulation_Preservation.thy` | Does that agreement survive every step, and every run? (`csim_star`) |
| `Procedure_Ownership.thy` | Can an activation wander into another procedure's nodes? (no) |
| `Source_To_Trace.thy` | Is a source run a valid local trace? (yes — and this is what soundness consumes) |

## Shape of the session

Two branches that meet only at the end. `Simulation/` never mentions traces;
`Procedure_Ownership` never mentions the simulation. `Source_To_Trace` is the
only theory needing both.

```text
VIMP_Proc_to_CFG
 ├─► Compile_Invariants ──► Procedure_Ownership ─────────────┐
 └─► Simulation/Residual_Location ──► …Residual_Edges        │
        └─► …Simulation_Relation ──► …Simulation_Preservation ┤
                                                              ▼
                                                       Source_To_Trace
```
