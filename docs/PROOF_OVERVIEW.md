# Proof overview

Voblint proves soundness for the result computed by an executable,
interprocedural abstract interpreter.

## Proof chain

```text
well-formed VIMP source
  -> compiled procedure-aware CFG            (expressions elaborated to texp)
  -> located CFG execution
  -> valid activation-local trace
  -> ltr_collect / activation_collect
  -> abstract post-solution
  -> verified solver result
```

Each arrow has a separate responsibility.

## Source contract

`wf_source_program` validates procedure declarations, call targets, arity,
formal parameters, reserved-variable exclusion, return behavior, and the
distinguished main declaration. Main contains no explicit return and completes
only by ordinary fall-through.

`wf_compile_input` adds the finite, duplicate-free procedure enumeration needed
by executable compilation.

The source contract is static. The one *dynamic* contract the source-facing
theorems carry is `styped Gamma s0`: the initial store holds every variable
inside its declared machine-integer kind. It stays visible in the final
theorems rather than being discharged internally, because it is a genuine
obligation on the caller -- a store that already violates its own declarations
is outside the semantics the compiler was proved against. `rstyped` is its
during-unwinding relaxation, exempting the reserved `ret_var` channel.

## Elaboration

`compile_prog` takes the program's typing environment and elaborates every
expression once, at compile time, into a kind-annotated `texp`. The compiled
action carries that tree, so `edge_step`, every domain transfer, and the check
classifier all evaluate with `teval` and none of them takes a `tyenv`. The
conversion a write performs is explicit in the tree as `TCast`, emitted only
where the target kind differs from the kind the expression synthesizes.

On the abstract side the corresponding operation is the `cast_domain` class
operation `a_cast`, placed in the domain rather than in the analysis
specification -- the same position Goblint gives `IntDomain.S.cast_to`. Both an
ordinary assignment and a call-return write route through it, and its soundness
obligation `a_cast_sound` is discharged per domain against `ik_norm`.

## Compiler simulation

`compile_prog` builds one CFG with explicit procedure entries and results,
ordinary local edges, and a separate call relation. Compiler certificates and
locality lemmas expose node ownership, procedure ranges, call continuations, and
matching result boundaries.

The located execution relation associates a source configuration with a CFG
node, store, and activation stack. Control simulation shows that each source
step has a matching located CFG execution.

## Activation-local semantics

`valid_ltr` records one activation and its structural caller chain. Root, call,
and resume constructors preserve the correlation between a completed callee
and its immediate caller.

`ltr_collect` projects valid traces to stores at each node.
`activation_collect` groups those same stores by the structural activation
context required by context-sensitive analyses.

## Equation soundness

Every equation right-hand side joins three contribution families:

1. ordinary local-edge flow;
2. callee-entry flow;
3. caller/callee return combination.

The executable RHS and its mathematical characterization share the same source
definitions. Transfer soundness proves that each concrete trace constructor is
covered by its corresponding abstract contribution. A post-solution therefore
covers `ltr_collect`.

## Solver integration

Effectful transfers produce strategy trees for the verified side-effecting
top-down solver. Executable finite-map states are related to function states by
representation morphisms. Solver correctness yields a partial post-solution;
the transport lemmas expose it as an abstract post-solution.

Demand-driven guarantees apply to nodes in the dependency cone of the query.
The equation semantics itself remains defined over the original CFG.

## D/G analyses

The D/G interface separates flow-sensitive local facts (`D`) from shared
side-effect information (`G`). A sound instance supplies local transfer,
callee-entry, return-combine, publication, and read obligations.

Unit-context Sign and Interval analyses use the same carrier for `D` and `G`.
The mixed Sign/Interval instance uses distinct carriers. Context-sensitive
instances index local facts by activation keys while routing shared information
through the analysis-defined global interface.

## Source-facing result

The source theorem composes:

- source/CFG simulation;
- construction of a valid local trace;
- membership in the appropriate collector;
- collector coverage by the computed abstract solution.

The conclusion is soundness: every reached source store belongs to the
concretization of a computed abstract slot. The result may contain additional
stores; no completeness claim is made.
