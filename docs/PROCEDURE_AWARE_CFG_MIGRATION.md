# Procedure-aware CFG architecture

## Status

This document records the procedure-aware control-flow architecture implemented
by Voblint. It describes stable semantic and proof boundaries. Development
history belongs in version control.

## 1. Motivation

Interprocedural analysis needs more structure than a flat graph with synthetic
entry edges and detached return metadata. Calls create activations, arguments
initialize callee-local state, explicit returns may bypass source
continuations, and a completed callee resumes its immediate caller.

The framework represents those facts directly:

- procedure entries and results are typed CFG nodes;
- calls are separate from ordinary intra-procedural edges;
- local traces retain the activation stack;
- equation systems distinguish local flow, callee entry, and return
  combination;
- context-sensitive analyses route information through the generic D/G
  interface.

## 2. Source procedure contract

The source language contains structured commands, procedure calls, explicit
procedure returns, and internal restoration commands used by the small-step
semantics. A procedure declaration supplies its formal parameters and body.
Calls evaluate actual parameters in the caller, initialize a fresh callee
store, and save the caller state and optional destination in an activation
frame.

`wf_source_program` validates the semantic source contract.
`wf_compile_input` adds the finite, duplicate-free procedure enumeration used
by executable compilation:

- the distinguished main declaration exists, has no formals, and contains the
  supplied main body;
- procedure names are unique in the compiler enumeration;
- every call target exists;
- actual and formal arities agree;
- formal names are local, pairwise distinct, and not reserved;
- implementation-reserved variables cannot be used as ordinary source
  assignment destinations, expression variables, call destinations, or
  formals;
- a destination-bearing call targets a `value_providing` procedure body;
- a call without a destination may ignore a returned value;
- main contains no explicit return.

Procedures have no separate user-visible result declaration. Their accepted
return behavior is derived conservatively from syntax. `value_providing`
requires a source body with no syntactic fall-through, no void return, and at
least one value return. Falling off the end is a void completion. Calls without
a destination accept either behavior; destination-bearing calls require
`value_providing`.

## 3. Root completion

The root activation never executes `Return None` or `Return (Some e)`.
Successful execution of main reaches the end of its command by ordinary
fall-through with an empty frame stack. No root-unwind rule exists.

This restriction keeps `Return` activation-local: every accepted explicit
return discharges a real caller frame.

## 4. Procedure-aware CFG

CFG nodes distinguish:

- `Statement n`, an ordinary program point;
- `FunctionEntry p`, the unique entry of procedure `p`;
- `FunctionResult p`, the result boundary of procedure `p`.

The graph has two relations:

- `intra` contains ordinary local control flow and `EA_Ret` edges;
- `calls` contains call-site metadata, callee entry, and continuation nodes.

A compiled program has one flat node space partitioned into disjoint
procedure-owned ranges. Compiler certificates expose the ownership and
separation properties needed by semantic clients. In particular, ordinary
compiled edges do not enter a `FunctionResult`; only matching return flow does.

## 5. Call, return, unwind, and resume

A source call:

1. evaluates actual arguments in the caller store;
2. creates a callee store with inherited globals and fresh locals;
3. binds formals to the argument values;
4. pushes a frame containing the caller store and optional destination;
5. starts the callee body.

`Return (Some e)` evaluates `e`, publishes it through the reserved return
channel, and enters `Unwind`. `Return None` enters `Unwind` without publishing
a value. Unwinding discards pending commands inside the current activation
until the matching restoration command is reached. Restoration pops the frame,
keeps callee global effects, restores caller locals, and writes the published
value to the destination when one exists.

The compiler maps every explicit return and procedure fall-through to the
matching `FunctionResult p`. A local trace resumes the continuation recorded by
the call relation and combines the caller and callee stores with the same
operation used by the source semantics.

## 6. Activation-local trace semantics

`valid_ltr` is the concrete interprocedural reference semantics. Its trace
constructors represent:

- a root path beginning at the program entry;
- a called activation linked to its immediate caller;
- a resumed caller linked to the completed callee.

Each trace stores one activation-local CFG path. The caller relation remains
structural, so nested and recursive calls resume the nearest activation without
encoding an unbounded stack in CFG nodes.

## 7. Collecting semantics

`ltr_collect` forgets trace structure and collects sink stores at each CFG
node. `ltr_collect_keyed` additionally groups stores by an abstract activation
key. `activation_collect` retains the activation context required by
context-sensitive soundness results.

These collectors are the semantic targets of the analyzer. They cover partial
and non-terminating executions at every reachable program point. Terminating
source executions are related separately to result reachability.

## 8. Three RHS contribution sources

The equation system computes each local unknown from one shared representation
of three contribution families:

1. **intra contributions** apply an edge transfer to an ordinary predecessor;
2. **entry contributions** construct a callee entry state from a call site;
3. **combine contributions** merge a completed callee with its caller
   continuation.

Executable RHS construction and mathematical soundness characterization derive
from the same source-family definitions. This prevents the implementation and
proof model from independently restating interprocedural flow.

## 9. Generic D/G routing

The supported modular-analysis interface separates:

- `D`, flow-sensitive facts associated with local program-point unknowns;
- `G`, information published and consumed through global side effects.

The generic D/G generator routes local transfers, callee-entry effects, and
return combination through those carriers. Context keys select local
activation slots while shared global facts remain available through the
analysis-defined reader. Homogeneous analyses instantiate `D = G`; mixed
analyses may choose different carriers.

The architecture follows Goblint-style D/G routing. It does not claim semantic
equivalence to any removed analysis.

## 10. Verified solver integration

Executable D/G equations are represented as strategy trees and solved by the
vendored verified side-effecting top-down solver. Representation morphisms
connect executable finite maps and strategy trees to the abstract equation
system. The solver result is transported to a post-solution, then to collecting
soundness.

The plain solver interface is outside the supported pipeline. All executable
interprocedural analyses use the side-effecting solver.

## 11. Source-level soundness

Compiler simulation relates well-formed source configurations to located CFG
executions. Compiler certificates provide the node ownership and locality facts
used by the simulation.

The proof chain establishes:

1. solver output forms an abstract post-solution;
2. the post-solution covers activation-local collecting semantics;
3. compiler simulation maps accepted source executions into those traces;
4. source-level observations are contained in the analyzer result.

The headline theorems expose only the program well-formedness and
analysis-specific obligations that are not already consequences of the
canonical compiler-input predicate.

## 12. Intentionally absent components

The following components are not part of the live architecture:

- the Retain analysis;
- synthetic call-entry edge actions;
- detached call/exit combine relations;
- path-offset infrastructure tied to the flat command compiler;
- the AFP IMP2 bridge and VCG examples;
- the classical intra-procedural solver spine;
- trace-digest compatibility layers.

Retain used a routing discipline different from the supported D/G interface.
Native D/G analyses fill the intended modular-analysis role, but no semantic
equivalence with Retain is claimed.

## 13. Limitations and future work

- The language has no user-visible procedure return-kind declaration;
  `value_providing` is a conservative syntactic check rather than a semantic
  termination analysis.
- Context precision depends on the chosen finite key and analysis-specific
  global reader.
- Recursive solver examples remain sensitive to widening and context-domain
  design.
- The framework proves the implemented scalar IMP2 fragment; arrays and richer
  source types require separate language and compiler extensions.
- D/G supplies heterogeneous carriers and routing, not a generic reduced
  product constructor.
