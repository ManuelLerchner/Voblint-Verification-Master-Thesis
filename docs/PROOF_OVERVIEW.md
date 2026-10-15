# Proof overview

Voblint proves soundness for the result computed by an executable,
interprocedural abstract interpreter.

## Proof chain

```text
surface VIMP (src_exp, src_com), accepted by wf_program_compile_input_exec
  -> core VIMP by elaboration (elab_ptable), run by pstep
  -> compiled procedure-aware CFG (elab_cfg)
  -> located CFG execution
  -> valid activation trace
  -> node_collect / activation_collect
  -> abstract post-solution
  -> verified solver result
```

Each arrow has a separate responsibility.

## Language

The parser builds surface VIMP: `src_exp`, `src_com`, `imp_prog`. Elaboration
(`elaborate`, `elab_com`, `elab_ptable`) resolves every name to a variable
identity `var_id`, gives each expression its machine kind `ikind`, and makes
implicit conversions explicit. The result is core VIMP (`exp`, `com`), evaluated
by `eval` and executed by `pstep`, the canonical instance of the generic step
relation `vimp_sem.gpstep`; a call result is converted to its destination by
`kind_conv`. Surface VIMP has no semantics of its own: a surface program means
the core semantics of its elaboration. Every theorem below is about core runs;
that elaboration gives the intended meaning is part of the adequacy argument.
All of this lives in session `Voblint_VIMP`.

## Source contract

`wf_source_program` validates procedure declarations, call targets, arity,
formal parameters, reserved-variable exclusion, return behavior, and the
distinguished main declaration. Main contains no explicit return and completes
only by ordinary fall-through.

`wf_compile_input` adds the finite, duplicate-free procedure enumeration needed
by executable compilation. The executable check `wf_program_compile_input_exec`,
which `run_voblint` runs first, also rejects a literal outside `I64`
(`lits_fit`); `wf_program_compile_input_exec_sound` proves it implies
`wf_program_compile_input`.

## Compiler simulation

`compile_prog` builds one CFG with explicit procedure entries and results,
ordinary local edges, and a separate call relation. Compiler certificates and
locality lemmas expose node ownership, procedure ranges, call continuations, and
matching result boundaries. `elab_cfg p ds` is `compile_prog` of the
elaborated procedure table.

The simulation relation `csim` associates a source configuration, indexed by the
procedure of its outermost activation, with a CFG node, store, and activation stack. Control simulation shows that each source
step has a matching located CFG execution.

## Activation-trace semantics

`cstep` executes the CFG one located step at a time.
`valid_activation_trace` records one activation and its structural caller chain. Root, call,
and resume constructors preserve the correlation between a completed callee
and its immediate caller.

`node_collect` projects valid activation traces to stores at each node.
`activation_collect` groups those same stores by the context a context policy
admits for the activation (`vimp.gactivation_context_rel`), as context-sensitive
analyses require. Along valid activation traces of the elaborated graph every
store stays within its kinds (`node_collect_in_kinds`).

## Equation soundness

Every equation right-hand side joins three contribution families:

1. ordinary local-edge flow;
2. callee-entry flow;
3. caller/callee return combination.

The executable RHS and its mathematical characterization share the same source
definitions. Transfer soundness proves that each concrete trace constructor is
covered by its corresponding abstract contribution. A post-solution therefore
covers `node_collect`.

## Solver integration

Effectful transfers produce strategy programs, compiled by `sp_compile` into the
strategy trees the verified side-effecting
top-down solver. Executable finite-map states are related to function states by
representation morphisms. Solver correctness yields a partial post-solution;
the transport lemmas expose it as an abstract post-solution.

Demand-driven guarantees apply to nodes in the dependency cone of the query.
The equation semantics itself remains defined over the original CFG.

## D/G analyses

The D/G interface separates flow-sensitive local facts (`D`) from shared
side-effect information (`G`). A sound instance supplies local transfer,
callee-entry, return-combine, publication, and read obligations.

By default the shipped domains use the whole-state specification: the local
unknown carries the entire abstract state, VIMP globals included, and the global
channel stays inert. Under flow-insensitive program globals the keyed lifter
(`gkeyed_split_spec`) keeps each declared global at its own global unknown; the
contract is stated over an environment of global values, so an edge reads only
the globals it mentions and publishes only those it may assign
(`gkeyed_split_contract`). `Order_Analysis` (session `Voblint_Analysis_Order`)
instantiates the same interface at a relational carrier. Context-sensitive
instances index local facts by activation keys while routing shared information
through the analysis-defined global interface.

## Source-facing result

The source theorem composes:

- source/CFG simulation of a `pstep` run of the elaborated program, which names
  a node simulating the reached configuration (`source_reaches_node_collect`);
- construction of a valid activation trace;
- membership in the appropriate collector;
- collector coverage by the computed abstract solution.

The conclusion is soundness: every reached source store belongs to the
concretization of a computed abstract slot. The result may contain additional
stores; no completeness claim is made.
