# Handover: Deadcode / Reachability Representation in Voblint

## 1. Purpose

This document hands over an architectural issue discovered while aligning Voblint's branch transfer with Goblint.

The immediate question is:

> **How should Voblint represent an infeasible control-flow edge, especially in the presence of local/global side-effect separation?**

Do **not** treat this as a small Sign proof failure.

The current branch work exposed a deeper mismatch between:

* Goblint-style `Deadcode` / no-successor semantics;
* Voblint's current representation of an infeasible branch as `bot :: abs_state`;
* Voblint's existing local/global effect architecture.

The next task is an **architecture audit and design decision**, not immediate implementation.

---

## 2. Project goal

Voblint is intended to formalize a **Goblint-like analyzer**, including Goblint's architectural decomposition where practical.

The goal is therefore not merely:

> Find the smallest implementation which proves sound.

The stronger goal is:

> Mirror Goblint's information flow and abstraction boundaries where possible, and document explicit deviations where verification requires them.

This matters for the issue described below.

---

## 3. Relevant existing architecture

Voblint has a mathematical abstract state roughly of the form:

```isabelle
abs_state = vname => abstract_value
```

This state contains information associated with program variables.

The project also has a local/global effect architecture used by the TD-side solver.

Conceptually:

```text
                 program analysis
                /                \
         local flowing state    global effects
                |                   |
                v                   v
          local CFG flow       side publishing
```

Local CFG transfer is not supposed to directly rewrite arbitrary global information.

This is captured for Sign by the load-bearing theorem:

```text
sign_tf_local_edge_invariant
```

and downstream results including:

```text
sign_sound_etf
sign_etf_cone_compatible
sign_etf_threefold_mono
```

These are consumed by:

```text
Sign_Exec_Sound.thy
Sign_Named_Global_Eff.thy
Example_Side_Proc_Global.thy
Example_Sign_DG_CallString_K1.thy
Example_Mixed_Flow_Sign.thy
src/Examples/Voblint.thy
```

Therefore `sign_tf_local_edge_invariant` is not stale incidental proof infrastructure.

It is part of the soundness argument for the side-effect solver route.

---

## 4. What branch handling looked like before

Historically, branch transfer effectively used backward filtering:

```text
branch condition
      |
      v
   bfilter
      |
      v
refined abstract state
```

This was sufficient for many old expressions.

After unifying arithmetic and Boolean expressions, expressions such as:

```text
Less
Eq
Not
And
Or
```

became ordinary integer-valued expressions.

A falsification study found a real precision gap.

Example:

```c
if ((x < 0) == 1) {
    ...
}
```

with:

```text
x definitely positive
```

Forward evaluation gives:

```text
x < 0        = 0
0 == 1       = 0
to_bool      = Some False
```

so the true edge is impossible.

Old `bfilter`, however, could leave the state unchanged because the generic `afilter` fallback does not recursively handle all unified Boolean-valued expression constructors.

This established that Voblint needed Goblint-style forward feasibility reasoning.

---

## 5. New Goblint-style branch work

A generic branch combinator was introduced conceptually as:

```text
branch e expected sigma
    |
    v
forward aval
    |
    v
to_bool
    |
    +-------------------------+
    |                         |
definite contradiction     feasible/unknown
    |                         |
    v                         v
   bot                     bfilter
```

The following generic results were added/proved:

```text
branch_sound
branch_mono
branch_le_bfilter
```

and an executable mirror:

```text
branch_st
branch_st_commute
```

Domain wiring was migrated for Interval and the composite `int_dom` modes, and work was in progress for Sign.

---

## 6. The newly discovered conflict

Sign's migration to the new `branch` caused:

```text
sign_tf_local_edge_invariant
```

to become genuinely false.

This is not a missing proof automation issue.

The problem is the meaning of:

```isabelle
bot :: abs_state
```

for an infeasible branch.

Suppose before a local edge:

```text
local x  = Pos
global G = Pos
```

and the selected branch is impossible.

The new branch currently returns whole-state bottom:

```text
x = Bot
G = Bot
...
```

Extensionally, this represents no concrete state, so ordinary abstract-transfer soundness is fine.

But structurally, the local edge appears to have changed:

```text
G : Pos -> Bot
```

Therefore a theorem requiring local edges to preserve globals is false.

This exposes a distinction which the current representation conflates:

```text
NO SUCCESSOR
```

versus:

```text
A SUCCESSOR STORE WHOSE COORDINATES ARE BOTTOM
```

These may both have empty concrete semantics in simple state models, but they are not interchangeable for a local/global effect decomposition.

---

## 7. Why simply reverting Sign is not acceptable

One proposed fix was:

```text
Sign      -> bfilter only
Interval  -> branch
int_dom   -> branch
```

This would restore the old Sign proofs.

Do **not** assume that this is the desired final design.

The project goal is to model Goblint's architecture consistently.

Domain-specific CFG branch semantics would be undesirable unless justified by a genuine Goblint/domain distinction.

Similarly, do not delete the local-edge invariant simply to make `branch` fit.

---

## 8. Goblint reference architecture for Deadcode, branching, and side effects

This section records the relevant architecture of current Goblint which motivated this
investigation.

It is reference evidence, not an instruction to mechanically reproduce OCaml exceptions
in Isabelle. The Voblint design should reproduce the semantic/architectural distinction,
using the representation which fits the verified solver architecture best. Treat this
section as known reference points, not an immutable specification -- inspect Goblint
itself again if a question below is not settled by it.

### 8.1 Goblint distinguishes the analysis-local domain from dead control flow

Goblint defines a framework-level exception:

```text
exception Deadcode
```

and separately defines:

```text
Dom (D)
```

as a lifting of an analysis domain `D`. The source comment explicitly states:

```text
Dom (D) produces D lifted where bottom means dead code
```

Conceptually:

```text
                  Goblint analysis state

                      Dom(D)
                     /      \
                 Dead         Reachable
                               |
                               v
                               D
```

Thus dead control flow lives outside the analysis-specific local domain `D`. This
distinction is important for Voblint. Do not assume that `Deadcode` must be represented
by pointwise bottom inside `abs_state` merely because both ultimately have empty
concretization.

Relevant current Goblint source: `src/framework/analyses.ml` -- `exception Deadcode`,
`module Dom (LD)`, `Dom.unlift`.

### 8.2 Goblint's transfer manager separates local state and global effects

Goblint transfer functions receive a manager with, among other fields:

```text
local  : D
global : V -> G
sideg  : V -> G -> unit
```

Conceptually:

```text
                      transfer

              local flowing state D
                       |
                       +------ read ------> global V -> G
                       |
                       +------ publish ---> sideg V G
                       |
                       v
                 local result D'
```

The ordinary local analysis state and global side effects are therefore distinct
channels. This is directly relevant to Voblint's local/global restrictions, side-effect
publishing, and `local_edge_invariant`. The existence of `local_edge_invariant` should
therefore not automatically be regarded as legacy architecture which conflicts with
Goblint -- it expresses a separation that Goblint also has.

Relevant current Goblint source: `src/framework/analyses.ml` -- `type ('d,'g,'c,'v) man`
with fields `local`, `global`, `sideg`.

### 8.3 Goblint `Base.branch` uses forward feasibility first

Current Goblint `Base` implements branch roughly as:

```text
branch man exp tv =
  valu := eval_rv man.local exp

  if valu can be converted to a definite truth value:
    if value == tv:
      refine using invariant
    else:
      raise Deadcode

  otherwise:
    refine using invariant
```

For integer conditions, the decisive operation is `ID.to_bool value`. So the control
flow is:

```text
                         branch(exp, tv)
                               |
                               v
                           eval_rv
                               |
                               v
                           ID.to_bool
                               |
                  +------------+-------------+
                  |                          |
           definite opposite            compatible /
                  |                       unknown
                  v                          |
             raise Deadcode                  v
                                         invariant
                                             |
                                             v
                                      refined local D
```

This is the architecture Voblint's new `branch` work was trying to reproduce.

Relevant current Goblint source: `src/analyses/base.ml` -- `branch`, `eval_rv`,
`ID.to_bool`, `invariant`.

### 8.4 Backward refinement can independently discover Deadcode

Goblint does not use forward evaluation as a replacement for backward refinement. After
forward feasibility succeeds or is inconclusive, `branch` calls `invariant`. The source
explicitly notes that `invariant` may be more precise than forward `eval_rv` and may
itself make the path dead. The invariant machinery has a contradiction continuation
which raises `Deadcode`. Therefore the intended architecture is forward feasibility
*plus* backward refinement, not either phase by itself. This is why Voblint should
retain both forward `aval`/`tobool` and `bfilter`/backward reasoning, even if one
happens to subsume the other for a particular domain.

### 8.5 An infeasible branch does NOT return a modified local store

This is the critical difference behind the current Voblint issue. Goblint's
`Base.branch` has return type `store`, but when it discovers that the selected edge is
impossible it does not construct and return `D.bot ()`, and it certainly does not
construct a store in which all local/global coordinates have been overwritten with
bottom. Instead it aborts that transfer path with `raise Deadcode`. The framework's
outer lifted domain gives this control-flow deadness its lattice-level meaning.

```text
    WRONG mental model:

        impossible edge
             |
             v
        normal successor state
        where every coordinate = bottom


    GOBLINT model:

        impossible edge
             |
             v
          Deadcode
             |
             v
        no successor
```

This is the main reason to question Voblint's current experimental
`branch ... = bot :: abs_state` encoding.

### 8.6 Why this matters for global side effects

Suppose a local transfer starts with `local x = Pos`, `global G = Pos`, and the selected
branch is impossible. Goblint's conceptual result is `Deadcode` -- there is no ordinary
successor local state whose global portion needs to be compared with the predecessor.
By contrast, Voblint's current whole-state-bottom encoding produces something
extensionally like `x = Bot`, `G = Bot`, which is semantically empty but structurally
appears to mutate `G`. That is exactly why a local-edge frame theorem such as
`global_after = global_before` can fail even though ordinary collecting-semantics
soundness remains true. This is evidence that "no successor" and "whole abstract store
bottom" should be considered separate abstractions.

### 8.7 Do not copy the OCaml exception literally

The goal is not to reproduce `raise Deadcode` as an exception mechanism in Isabelle. The
semantic architecture is what matters. A natural Isabelle representation may be
`datatype 'a lifted = Bot | Lifted 'a`, or an existing equivalent already present in
Voblint:

```text
    Goblint                     possible Voblint formalization

    raise Deadcode              Bot
    return d                    Lifted d
```

The architecture audit must determine WHERE this lift belongs. Do not assume in advance
that it belongs directly in `apply_tf` or directly in the generic solver RHS type.

### 8.8 Key correspondence to target

The desired semantic correspondence is approximately:

```text
       Goblint                         Voblint

       local D                         abs_state / local state
       global V -> G                   global environment
       sideg                           side contribution
       Deadcode                        explicit no-successor representation

       branch:
         eval_rv                       branch:
         to_bool                         aval
         contradiction -> Deadcode       tobool
         otherwise invariant             contradiction -> Dead
                                          otherwise bfilter
```

The architecture audit should determine how to realize this without fighting Voblint's
existing verified solver decomposition.

### 8.9 Questions the audit must answer relative to Goblint

1. What Voblint object corresponds to Goblint's local `D`?
2. What corresponds to Goblint's `global` and `sideg` channels?
3. What should correspond to Goblint's framework-level `Deadcode`?
4. Does Voblint already have exactly that distinction in `'a lifted`, but introduce it
   too late?
5. Can branch deadness be propagated through the existing RHS/strategy-tree layer
   without changing the generic solver?
6. If the solver domain itself should be lifted, is that merely a different
   instantiation of the existing generic solver?
7. Can `local_edge_invariant` then be formulated only for reachable successors --
   `transfer sigma = Lifted sigma' ==> globals sigma' = globals sigma` -- matching the
   intended local/global separation?
8. Can the resulting executable mirror have the clean commute shape
   `map_lift resolve (branch ...) = branch_st ... (resolve sigma)`?

The preferred design should explain how it corresponds to the Goblint architecture
above.

---

## 9. Existing locked design decision

The repository documentation currently treats the following solver interface as locked:

```text
rhs :: pp => (pp => abs_state) => abs_state
```

Do not silently change this.

However, "locked" means that changing it requires an explicit architectural decision; it does **not** mean it can never be revised if the abstraction is shown to be wrong.

It is currently unknown whether solving the Deadcode problem actually requires changing this interface.

That must be established first.

---

## 10. Core research question

Determine:

> **Where should explicit reachability / Deadcode live in Voblint?**

The required properties are:

### Goblint-style control-flow behavior

A definitely contradictory branch means:

```text
no successor
```

### Local/global frame property

A local edge must not directly mutate globals.

For a reachable successor:

```text
tf edge sigma = Reach sigma'
```

we want something morally like:

```text
globals sigma' = globals sigma
```

If:

```text
tf edge sigma = Dead
```

there is no successor whose global part needs comparison.

### Soundness

Dead must denote the empty set of concrete successor states.

### Executability

The executable `resolved_st_q` layer must mirror the mathematical semantics with a commute/refinement theorem.

### Goblint fidelity

Prefer the architecture corresponding most closely to Goblint's distinction between local domain state, side effects, and `Deadcode`.

---

## 11. Do not assume the final type change

A tempting redesign is:

```isabelle
apply_tf :
  ... => abs_state => abs_state lifted
```

instead of:

```isabelle
apply_tf :
  ... => abs_state => abs_state
```

But this may be too early.

The first task is to reconstruct where the project already introduces:

```text
abs_state lifted
```

There may be a smaller correct solution.

---

## 12. Candidate architectures to evaluate

### A. Whole-state bottom

Current experimental design:

```text
branch : abs_state -> abs_state

contradiction -> bot
```

Advantages:

* simple;
* ordinary state soundness straightforward.

Known problem:

* breaks local-edge global preservation.

Likely not the desired final architecture.

---

### B. Poison only the local component

Example:

```text
locals  -> bottom
globals -> unchanged
```

This would preserve the global frame syntactically.

Audit carefully before considering it valid.

Potential problems:

* programs/procedures with no locals;
* global-only conditions;
* arbitrary choice of poisoned variable;
* future relational domains;
* conflates deadness with a store representation again.

Likely undesirable.

---

### C. Explicit Dead/Reach at the local transfer/effect boundary

Conceptually:

```text
local transfer
      |
      +-> Bot
      |
      +-> Lifted sigma'
```

A later adapter may possibly consume this result while retaining the existing solver RHS type.

This could avoid changing the generic solver interface.

Investigate whether the current effect/RHS infrastructure has a natural place for this.

---

### D. Lift the solver analysis domain

Instantiate the solver over:

```text
abs_state lifted
```

so RHS itself returns:

```text
abs_state lifted
```

Then:

```text
contradiction -> Bot
normal edge   -> Lifted sigma'
```

This may be the cleanest semantic model.

However, determine how large the actual migration is.

Important:

> Changing the lattice with which a generic polymorphic solver is instantiated is not necessarily the same thing as changing the generic solver implementation.

Do not conflate those.

---

### E. Hybrid

There may be an existing lifted RHS or strategy-tree layer which already represents reachability correctly.

The proper change could be to move the lift boundary inward without changing either:

* the generic TD solver;
* or every domain-facing transfer function.

Look for this explicitly.

---

## 13. Required audit: current type/data pipeline

Trace the current implementation from edge action to solver result.

Start with:

```text
apply_tf
tf_branch
branch
bfilter
```

and follow through:

```text
effectful transfer
local/global restriction
global side publishing
RHS generation
strategy-tree generation
TD-side RHS
solver domain/unknown
solver solution
executable mirror
```

Produce an explicit type pipeline.

Example format:

```text
edge_action
    |
    v
apply_tf
    : abs_state -> abs_state
    |
    v
???
    |
    v
abs_state lifted
    |
    v
strategy_tree
    |
    v
solver
```

Use actual repository types, not this guessed shape.

For every transition:

```text
abs_state -> abs_state lifted
```

or:

```text
abs_state lifted -> abs_state
```

record:

* definition;
* file;
* reason;
* associated correctness theorem.

---

## 14. Required audit: existing `lifted`

Inspect:

```isabelle
datatype 'a lifted = Bot | Lifted 'a
```

Determine:

* its intended semantics;
* whether `Bot` explicitly means unreachable/no value;
* lattice instances;
* `gamma`/concretization if defined;
* `is_bot`;
* `map_lift`;
* widening/narrowing;
* executable/code-generation support;
* every place `abs_state lifted` already appears.

Answer:

> Is the project already using this type as the control-flow reachability layer?

If yes:

> Why is branch infeasibility currently encoded below that layer as `bot :: abs_state`?

That may reveal the real misplaced abstraction boundary.

---

## 15. Required audit: solver interface

Investigate the locked:

```text
rhs :: pp => (pp => abs_state) => abs_state
```

Determine:

1. Where is this interface defined?
2. What earlier architecture decision motivated it?
3. Which Voblint proofs depend on `abs_state` specifically?
4. Which only require an arbitrary lattice `'d`?
5. Is the vendored solver actually polymorphic in `'d`?
6. Could Voblint instantiate `'d = abs_state lifted` without modifying the generic solver?
7. Would only Voblint's RHS/domain instance change?
8. Or does the generic solver architecture itself genuinely need modification?

This distinction is critical.

---

## 16. Required audit: Sign local-edge soundness chain

Trace:

```text
sign_tf_local_edge_invariant
        |
        +-> sign_sound_etf
        +-> sign_etf_cone_compatible
        +-> sign_etf_threefold_mono
                 |
                 v
          side solver soundness
```

Explain exactly what `local_edge_invariant` guarantees.

Determine the correct formulation if transfer results become explicit Dead/Reach values.

Likely something morally equivalent to:

```isabelle
tf edge sigma = Lifted sigma'
==> global_part sigma' = global_part sigma
```

rather than requiring a property of `Bot`.

---

## 17. Required audit: Goblint comparison

Section 8 already records the relevant Goblint source evidence (`Deadcode`,
`Dom (D)`, the `local`/`global`/`sideg` manager split, `Base.branch`). Treat it as a
starting point, not a substitute for this audit -- verify it against the actual current
Goblint source rather than treating the handover as an immutable specification, and
extend or correct it if the source disagrees.

Inspect current Goblint architecture sufficiently to establish:

* how local state is represented;
* how globals are read;
* how global side effects are published;
* how `Deadcode` is signaled;
* where `Deadcode` is caught;
* whether dead branches produce a lattice-bottom local store or absence of a successor;
* whether side effects produced before deadcode survive or are discarded;
* how this corresponds to Voblint's side-effect architecture.

Do not merely search for the word `Deadcode`.

Trace the relevant branch/effect path.

---

## 18. Soundness shape to aim for

If explicit lifting is chosen, a clean concretization would be:

```text
gamma_lift Bot
  = {}

gamma_lift (Lifted sigma)
  = gamma_state sigma
```

Then transfer soundness can be expressed as:

```text
concrete successors
    subseteq
gamma_lift (abstract_transfer sigma)
```

or equivalent existing Isabelle notation.

This cleanly distinguishes:

```text
abstract scalar bottom
```

from:

```text
empty abstract state
```

from:

```text
no CFG successor
```

Those should not be conflated without an explicit theorem.

---

## 19. Executable correspondence target

If branch becomes lifted, the desired commute square is conceptually:

```text
                         branch
       abs_state ----------------------> abs_state lifted
           |                                  |
           | resolve                          | map_lift resolve
           |                                  |
           v                                  v
     resolved_st_q ------------------> resolved_st_q lifted
                        branch_st
```

A theorem should state the actual equivalent of:

```isabelle
map_lift resolve (branch ...)
=
branch_st ... (resolve ...)
```

using repository definitions.

Determine whether existing `map_lift` infrastructure already makes this straightforward.

---

## 20. Current branch-alignment worktree

Do not assume the current tree represents a finished architecture.

The branch migration was in progress when the conflict was discovered.

Changes currently include work around:

```text
Abstract_Domain.thy
Exec_Backward.thy
Sign_Backward.thy
Sign_Transfer.thy
Sign_Exec.thy
Interval_Backward.thy
Interval_Transfer.thy
Ivl_Exec.thy
Int_Backward.thy
Int_Transfer.thy
Int_Exec.thy
Congruence_Backward.thy
Example_Interval_Loop_Coverage.thy
```

The exact current `git status` must be checked at the start.

Do not revert these changes as part of the audit.

Do not assume every intermediate theorem is intended to survive the final refactor.

---

## 21. Things explicitly NOT to do

Until the architecture audit is complete:

**Do not:**

* revert Sign permanently to `bfilter_sign`;
* delete `sign_tf_local_edge_invariant`;
* delete the Sign TD-side soundness chain;
* weaken the invariant merely to accommodate whole-state bottom;
* poison arbitrary local variables to encode unreachable;
* change the solver RHS type immediately;
* modify the vendored TD solver;
* update the locked CLAUDE.md decision;
* commit the current branch migration as final;
* make source changes during the audit.

The next pass is read-only.

---

## 22. Deliverables for the new agent

Produce a report with the following sections.

### Executive conclusion

Answer:

> Where should Deadcode/reachability live?

and:

> Does the locked solver RHS interface actually need to change?

Give a definite preferred design if the evidence supports one.

---

### Current type/data-flow diagram

Show the exact current path:

```text
edge
 -> transfer
 -> effect layer
 -> RHS
 -> solver
 -> result
```

with actual types.

---

### Existing reachability representation

Explain every use of:

```text
lifted
Bot
Lifted
abs_state lifted
```

relevant to analysis execution.

---

### Why the Sign theorem fails

Give a minimal mathematical counterexample to the current whole-state-bottom branch semantics.

---

### Meaning of `local_edge_invariant`

Explain why it exists and why it is load-bearing.

---

### Goblint architecture

Show:

```text
local state
global side effects
Deadcode
```

and where Voblint currently differs.

---

### Candidate comparison

Compare A/B/C/D/E in a table:

| Design | Sound | Local-safe | Goblint-like | Refactor size | Future-proof |
| ------ | ----: | ---------: | -----------: | ------------: | -----------: |

---

### Recommended target architecture

Include proposed type signatures.

For example, only if supported:

```isabelle
branch ::
  ... => abs_state => abs_state lifted
```

and/or:

```isabelle
rhs ::
  pp => (pp => abs_state lifted) => abs_state lifted
```

Do not guess.

---

### Solver impact

State explicitly:

```text
Vendored solver changes: YES/NO
Generic Voblint solver framework changes: ...
Domain instantiation changes: ...
```

---

### Proof migration

Identify changes to:

```text
branch_sound
branch_mono
branch_st_commute
transfer soundness
local_edge_invariant
effectful soundness
solver soundness
```

Classify each as:

```text
mechanical
moderate
fundamental redesign
```

---

### Executable migration

Explain the target `resolved_st_q` commute story.

---

### File impact map

Classify current theories:

```text
MUST CHANGE
PROOF-ONLY CHANGE
LIKELY UNCHANGED
EXECUTABLE MIRROR
EXAMPLES/REGRESSIONS
```

---

### Locked-decision recommendation

If the existing solver-interface decision should be superseded, draft:

1. old wording;
2. proposed replacement;
3. rationale.

Do not edit it.

---

### Migration phases

Give a staged implementation plan that maintains green checkpoints where possible.

For example:

```text
M1 introduce reachability result
M2 migrate generic branch
M3 migrate executable mirror
M4 migrate Sign
M5 migrate Interval/int_dom
M6 migrate RHS/effect layer
M7 restore end-to-end proofs
M8 full build + codegen
```

Use the architecture actually discovered.

---

### Acceptance criteria

The final design should satisfy all of:

```text
1. contradictory guard denotes no successor explicitly;
2. Sign local-edge invariant is true without special pleading;
3. all domains use the same branch architecture;
4. Goblint-style forward feasibility is retained;
5. backward filtering remains the second phase;
6. executable mirror provably commutes;
7. TD-side solver soundness chain remains intact;
8. no arbitrary local-variable poisoning;
9. no hidden state-bottom/deadcode conflation;
10. full build and executable regressions green.
```

---

## 23. Guiding principle

The key conceptual distinction for this task is:

```text
                 scalar bottom
                       |
             no concrete integer

                 state bottom
                       |
             no concrete store

                 Deadcode
                       |
              no CFG successor
```

These may be related by soundness/concretization theorems.

They should **not automatically be represented by the same object** merely because all eventually denote an empty set.

The Sign failure suggests this distinction has become observable in Voblint's local/global architecture.

---

## 24. Final instruction to the agent

Treat the current failure as evidence about the architecture, not as a proof obstacle to work around.

The desired outcome is:

> a representation of Goblint-style `Deadcode` which composes naturally with Voblint's verified local/global side-effect solver.

A larger refactor is acceptable if that is the clean architecture.

Do not optimize for the smallest diff.

Optimize for:

```text
semantic clarity
+ Goblint fidelity
+ proof compositionality
+ executable correspondence
```
