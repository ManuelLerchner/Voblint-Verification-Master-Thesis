# Migration: stabilize pipeline seams with explicit interfaces

Status: design study. Nothing implemented.

Goal: reduce proof blast radius when source, CFG, or solver-facing
representations evolve, without breaking downstream proofs during the migration.

This document audits the current pipeline seams, identifies where raw
representations leak across them, and proposes an additive migration strategy:

1. introduce owner interfaces first;
2. keep old constants and theorem shapes alive through compatibility lemmas;
3. move downstream theories to the new interfaces slice by slice;
4. only then consider deeper cleanup or finer-grained session splits.

The target is not "more abstraction" in the abstract. The target is
representation independence at the stage boundaries that already exist in the
project:

```text
IMP2 source
-> CFG compilation
-> collecting semantics
-> equation system
-> TD-side solver bridge
-> Goblint-facing context / DG overlays
-> end-to-end source-level soundness
```

## 1. Current stage map

The project already has a strong conceptual pipeline and a clean top-level
session DAG:

```text
Voblint_IMP2 -> Voblint_CFG -> Voblint_Analysis -> Voblint_Formalization
```

The theory ownership is mostly aligned with that split:

- `src/IMP2/` owns source syntax and concrete small-step semantics.
- `src/CFG/` owns CFG syntax, compilation, collecting semantics, and compiler
  simulation.
- `src/Analysis/Generic/` owns abstract-domain interfaces, equation systems,
  solver wiring, and Goblint-facing overlays.
- `src/Analysis/Instances/` owns concrete domains.
- `src/Formalization/` owns composed theorems and executable demonstrations.

The problem is not missing stages. The problem is that some stages expose raw
representations that downstream theories destructure directly.

## 2. Audit summary: where the seams leak

### 2.1 IMP2 -> CFG

Owner theories:

- `src/IMP2/IMP2_Proc.thy`
- `src/CFG/IMP2_Proc_to_CFG.thy`
- `src/CFG/CFG_Def.thy`

Current leak:

- downstream theories know the exact constructor shape of `Call`, `Restore`,
  `EA_Enter`, and `combines`;
- call/return metadata is re-pattern-matched in collecting, compiler
  simulation, equation generation, context routing, GraphViz, and examples.

Evidence:

- `EA_Enter` is matched across `CFG_Collect*`, `TD_Side_*`, context proofs,
  instances, tooling, and examples;
- combine tuples `(call, ex, ret, dst)` are destructured across CFG, Analysis,
  and Formalization.

Consequence:

- changing call metadata or return mechanics propagates through many theories,
  even where the mathematics only needs "entry edge" or "return edge".

### 2.2 CFG syntax -> collecting semantics

Owner theories:

- `src/CFG/CFG_Def.thy`
- `src/CFG/Collecting/CFG_Collect.thy`
- `src/CFG/Collecting/CFG_Collect_Trace.thy`
- `src/CFG/Collecting/CFG_Collect_Activation.thy`

Current leak:

- collecting theories expose the concrete implementation of call entry and
  return combine directly through `edge_collect`, `edge_step`, witness rules,
  and combine-set membership;
- downstream theories restate "an entry edge means ..." instead of importing one
  owner lemma.

Consequence:

- call semantics changes force proof replay not just in collecting, but in every
  later theory that quotes collecting introduction lemmas.

### 2.3 Collecting semantics -> equation system

Owner theories:

- `src/Analysis/Generic/Equations/Constraint_System.thy`
- `src/Analysis/Generic/Equations/Constraint_System_Sound.thy`

Current leak:

- `domain_transfer` and `effectful_domain_transfer` are partly stable
  interfaces, but they still expose CFG representation details directly;
- `tf_enter` is coupled to the exact payload carried by `EA_Enter`;
- combine reasoning is still phrased via raw CFG tuple membership in many
  soundness lemmas.

Consequence:

- a change in CFG metadata appears as a transfer-interface change for every
  domain, every executable mirror, and every soundness proof.

### 2.4 Generic solver core -> Goblint-facing context / DG overlays

Owner theories:

- `src/Analysis/Generic/Solver/Core/*`
- `src/Analysis/Generic/Solver/Context/Goblint/*`

Current leak:

- the base TD-side generator is a reasonable seam, but many Goblint-side
  overlays still depend on raw `EA_Enter` tests or direct combine tuple
  destructuring;
- the project already found one good repair here: `context_domain` packages a
  real interface instead of scattering routing assumptions.

Consequence:

- overlays that should depend on "frame entry" or "return predecessor" still
  depend on exact CFG constructor shapes.

### 2.5 Internal proofs -> examples and tooling

Owner theories:

- `src/CFG/CFG_GraphViz.thy`
- `src/Analysis/Instances/Tooling/Analysis_GraphViz.thy`
- `src/Formalization/Examples/*`

Current leak:

- examples and visualisation theories often assert exact edge tuples and exact
  combine tuples;
- some README and example text still describes older representations.

Consequence:

- example maintenance amplifies representation churn and obscures whether a
  change is semantic or cosmetic.

## 2.6 Healthy spread vs real leak

Not every high-fanout concept is a bad seam. Some concepts should appear across
many files because they are the intended interface of a layer. The distinction
is:

- **healthy spread**: downstream theories depend on a named owner-level concept;
- **real leak**: downstream theories depend on the owner layer's current
  representation.

Current rough fanout from the repository scan:

| Concept | Approx. files | Assessment |
| --- | ---: | --- |
| `EA_Enter` | 50 | **real leak** |
| combine tuple / selectors | 27 | **real leak** |
| `enter_state` | 30 | mostly healthy |
| `combine_states` | 31 | mostly healthy |
| `restrict_local` / `restrict_global` | 30 | healthy |
| `side_env` / `glob_env` | 34 | healthy |
| `sound_transfer` | 31 | healthy theorem-interface spread |
| `sound_effectful_transfer` | 18 | healthy theorem-interface spread |
| `part_post_solution` | 32 | healthy solver-interface spread |
| `threefold_mono` | 12 | healthy obligation spread |
| `context_domain` / `route` | 3 | good packaged seam |

### `EA_Enter` and combine metadata: real leak

These are still the clearest bad seams.

Why:

- they are not just widely mentioned;
- many downstream theories still reason by constructor shape or tuple shape;
- changing the source/CFG encoding forces work in solver, context, instance,
  tooling, and example layers.

This is the core reason parameter/return refactors spread so far.

### `enter_state`, `combine_states`, `is_global`: wide but mostly healthy

These appear broadly because they are the actual IMP2 local/global semantics,
owned by `IMP2_Globals.thy`.

Why this is not the same problem:

- downstream theories usually cite them as semantic concepts, not as accidental
  encodings;
- they form the meaning of call entry, local restoration, and global flow.

There is still room to improve ergonomics:

- owner lemmas such as `callee_entry_store` and `return_to_caller` would let
  later theories cite one semantic wrapper instead of rebuilding the expression
  from smaller pieces.

But this is secondary to the `EA_Enter` / combine leak.

### `restrict_local`, `restrict_global`, `side_env`, `glob_env`: healthy spread

These concepts are used broadly in the solver and pipeline layers, but they are
already functioning as named interfaces rather than raw representations.

Why this compares well:

- they are owned centrally (`TD_Side_CFG.thy`, `Constraint_System.thy`);
- downstream files usually consume the named interface directly;
- representation changes underneath them would be easier to absorb.

These are examples of a wide seam that is doing its job.

### `sound_transfer`, `sound_effectful_transfer`, `part_post_solution`, `threefold_mono`: theorem-interface spread

These also have significant fanout, but the spread is through abstract
contracts, not through constructor encodings.

The issue here is not representation leakage. The issue, when one exists, is:

- obligation bundling;
- ergonomics of interpretation;
- how many hypotheses must be threaded manually.

That is a different kind of cleanup from the call/return seam work.

### `context_domain`: the positive reference point

`context_domain` is the best current example of a leak that was successfully
turned into a stable interface.

Before:

- routing facts were split across kernel and generator code;
- the kernel proved soundness for a weaker routing shape than the generator
  actually used.

After:

- one locale owns the routing interface;
- the generator and soundness kernel both speak in terms of `route`;
- downstream proofs consume the packaged interface instead of reconstructing it.

This is the model to copy for the other volatile seams.

### Examples and tooling: secondary leak amplifier

Examples and GraphViz layers are not the root cause of the architectural leak,
but they amplify it.

Bad pattern:

- asserting exact edge tuples and combine tuples when the theorem only needs a
  view-level fact such as "this is an entry edge" or "this return node is a
  combine successor".

Guideline:

- only regression examples that deliberately pin graph shape should mention raw
  tuples;
- ordinary examples and visualisation support should consume the owner view API.

### Ranking

If the project wants to reduce future blast radius, the order is:

1. hide `EA_Enter` and combine metadata behind owner interfaces;
2. move examples and tooling away from exact raw tuples where possible;
3. add source-level semantic wrappers for call entry and return-to-caller store
   transformations;
4. leave `side_env` / `glob_env` and the transfer locales alone unless the goal
   is theorem-interface ergonomics rather than representation repair.

## 3. Principle: owner theory + stable interface + compatibility lemmas

For every volatile concept, one theory should own:

1. the representation;
2. the selectors / predicates / smart constructors;
3. the elimination and introduction lemmas other stages are supposed to use.

Downstream theories should prefer interface facts over constructor matching.

This is ordinary information hiding, applied to Isabelle theories.

## 4. Proposed owner interfaces

### 4.1 Source call/return interface

Owner:

- `IMP2_Proc.thy`

Should own:

- call decomposition;
- return publication;
- caller/callee frame behavior;
- source-level well-formedness facts for calls.

Suggested interface surface:

- predicates:
  - `is_call_com`
  - `is_restore_com`
- selectors:
  - `call_dst`
  - `call_proc`
  - `call_actuals`
  - `proc_formals`
  - `proc_body`
  - `proc_result`
- semantic wrappers:
  - `callee_entry_store`
  - `callee_result_store`
  - `return_to_caller`

The important point is not the exact names. The point is that later theories
should talk about "callee entry store" and "return to caller", not about how
`with_result`, `ret_var`, `Frame`, and `combine_assign` are assembled today.

Migration rule:

- add these as definitions and lemmas only;
- keep the existing constructors and proof scripts working;
- prove immediate simp lemmas that recover the current behavior.

### 4.2 CFG call/return metadata interface

Owner:

- `CFG_Def.thy`

This is the highest-value seam in the current branch.

Already present:

- `combine_call_node`
- `combine_exit_node`
- `combine_return_node`
- `combine_dst`
- `is_enter_action`

Missing discipline:

- many downstream theories still pattern-match on `(call, ex, ret, dst)` or on
  `EA_Enter xs es`.

Suggested interface surface:

- entry-edge predicates and selectors:
  - `is_enter_edge`
  - `enter_formals`
  - `enter_actuals`
  - `enter_target`
- combine-info selectors:
  - keep the existing `combine_*`;
  - add smart introduction / elimination lemmas so callers do not unpack tuples.
- predecessor views:
  - keep `enter_predecessor_list`, `non_enter_predecessor_list`,
    `combine_info_predecessor_list`;
  - treat these as the only sanctioned call/return predecessor API.

Suggested representation change:

- eventually turn `combine_info` from a tuple into a record.

Why not first:

- a direct tuple -> record switch would force proof churn immediately.
- first migrate downstream to the existing selectors.
- once tuple destructuring is gone, the representation can change underneath.

### 4.3 Collecting interface

Owner:

- `CFG_Collect.thy`
- `CFG_Collect_Trace.thy`

Should own:

- what entry edges mean concretely;
- what combine steps mean concretely;
- how those facts are introduced into collecting witnesses.

Suggested interface surface:

- lemmas:
  - `edge_collect_enterI`
  - `edge_collect_enterE`
  - `combine_collect_returnI`
  - `combine_collect_returnE`
  - `cfg_collect_from_enter_edge`
  - `cfg_collect_from_combine`
- witness-facing wrappers:
  - `is_proc_entry_pp`
  - `entry_edge_store`
  - `return_edge_store`

The goal is that solver and context theories cite owner lemmas about
entry/return flow, not restate `edge_collect (EA_Enter xs es)` or raw combine
membership over and over.

### 4.4 Abstract transfer interface

Owner:

- `Constraint_System.thy`
- `TD_Side_CFG.thy`
- `Exec_Bridge.thy`

Current interface:

- `tf_enter :: vname list => aexp list => abs_state => abs_state`

This is already better than a bare `EA_Enter`, but the interface still tracks
the CFG constructor payload too closely.

Suggested next interface:

- define a named "entry payload" concept in the owner layer and map both the
  concrete CFG edge and the abstract transfer interface through it.

Two compatible shapes:

1. keep the current curried arguments and add owner lemmas around them;
2. introduce a record such as `enter_info` and provide compatibility
   abbreviations.

Recommendation:

- do not force a record immediately;
- first add owner-level conversion lemmas:
  - `apply_tf_enter`
  - `apply_etf_enter`
  - `edge_collect_enter_sound`
  - executable mirrors for enter payload transport.

This preserves all current instance code while creating one place to absorb a
future entry-payload change.

### 4.5 Goblint-facing context interface

Owner:

- `Context_Domain.thy`
- one future locale for the repeated context-soundness obligation bundle

This is the best current example of the desired direction.

`context_domain` already packages:

- `start_context`
- `prep`
- `ctx_sel`
- `entdg`
- `cmp`
- derived `route`

Recommendation:

- extend this style instead of introducing more raw theorem-parameter bundles;
- fold the repeated `ENTRY` / `PROC_ENTRY` / `EDGE` / `ENTER_MONO` /
  `CMP_SOUND`-style bundles into one locale when the shared shape is real.

Important constraint:

- do not locale-ify every executable generator.
- keep executable generators as definitions when they need direct code
  generation and only have one production instance.

### 4.6 Example and tooling interface

Owners:

- `CFG_GraphViz.thy`
- `Analysis_GraphViz.thy`
- example theories

Recommendation:

- examples should prefer helper definitions like `cfg_edges_list`,
  `cfg_combines_list`, `combine_*`, `is_enter_action`;
- only a small number of regression examples should assert exact raw tuples.

This keeps examples useful as semantic witnesses instead of making them
representation snapshots.

## 5. Migration plan: additive and proof-preserving

### Phase 1: publish owner accessors and view lemmas

Additive only.

- add selectors, predicates, and view lemmas in owner theories;
- no theorem deletions;
- no representation changes;
- no consumer rewrites yet.

Exit criterion:

- all new interfaces exist and reduce by simp to current definitions.

### Phase 2: migrate generic downstream proofs to owner interfaces

Prioritize the broadest fan-out:

1. CFG collecting
2. Generic equations
3. Solver core
4. Goblint context overlays

Discipline:

- replace tuple destructuring with selector lemmas;
- replace `a = EA_Enter ...` reasoning with `is_enter_action` or
  owner-level entry-edge lemmas;
- preserve theorem statements when possible.

Exit criterion:

- generic layers stop pattern-matching on raw call/return metadata except in the
  owner theories.

### Phase 3: migrate domain instances and executable bridges

Why later:

- these are consumers of the generic interfaces, not the place to invent them.

Work:

- switch instance lemmas to owner facts;
- keep executable `value` behavior unchanged;
- add compatibility lemmas for any remaining constructor-specific instances.

Exit criterion:

- Sign, Interval, Mixed, and DG layers consume the same stable interfaces.

### Phase 4: migrate examples and docs

Work:

- update examples to use view APIs unless they are explicitly regression tests
  for graph shape;
- fix stale README language around parameterless procedures and combine triples.

Exit criterion:

- docs describe the current architecture and the intended seam owners.

### Phase 5: optional internal cleanup

Only after Phases 1-4:

- turn `combine_info` into a record;
- rename or internalize helper constructors;
- delete deprecated aliases after a full build-clean migration window.

## 5.1 Concrete execution plan

This section turns the architecture plan into an implementable migration route.
The bias is:

- additive first;
- generic layers before instances;
- mechanical edits before proof-shape edits;
- batch-build after each slice.

### Stage 0: preparation

Goal:

- freeze the migration surface before changing consumers.

Work:

1. create a short checklist issue or note for each slice below;
2. identify current failing local worktree changes and either finish or park
   them, so migration failures are attributable to the seam work;
3. update stale READMEs only after the code slices are stable.

No proof changes yet.

### Stage 1: owner-surface expansion in `IMP2` and `CFG`

Goal:

- publish stable view APIs while preserving all current representations.

Files:

- `src/IMP2/IMP2_Proc.thy`
- `src/CFG/CFG_Def.thy`
- optionally `src/CFG/IMP2_Proc_to_CFG.thy`

Work in `IMP2_Proc.thy`:

- add wrappers such as:
  - `callee_entry_store`
  - `return_to_caller`
  - `call_dst`
  - `call_proc`
  - `call_actuals`
- add simp lemmas reducing them to the current `bind_formals` /
  `with_result` / `combine_assign` behavior.

Work in `CFG_Def.thy`:

- add view helpers for entry edges:
  - `is_enter_edge`
  - `enter_edge_source`
  - `enter_edge_formals`
  - `enter_edge_actuals`
  - `enter_edge_target`
- add introduction / elimination lemmas for combine metadata:
  - from `(c, ex, ret, dst) \<in> combines g` to selector facts;
  - from selector facts back to membership where appropriate;
- add list/set bridge lemmas so consumers can avoid tuple destructuring through
  `predecessor_list`, `enter_predecessor_list`, `combine_info_predecessor_list`.

Build gate:

- `Voblint_CFG`

Risk:

- low. This is additive.

### Stage 2: mechanical consumer cleanup

Goal:

- eliminate the easiest raw-constructor dependencies first.

Files:

- broad sweep across `src/CFG/`, `src/Analysis/Generic/`, `src/Analysis/Instances/`,
  `src/Formalization/Examples/`, `src/Analysis/Instances/Tooling/`

Safe bulk replacements:

1. `a \<noteq> EA_Enter` -> `\<not> is_enter_action a`
2. `a = EA_Enter` style boolean tests -> `is_enter_action a`
   only where the code does **not** need `xs` / `es`
3. doc text:
   - "combine triples" -> "combine metadata" or the precise current term
   - stale "parameterless procedures" wording where no historical note is needed

Typical files for this slice:

- `src/Analysis/Instances/Sign/Sign_DG.thy`
- `src/Analysis/Instances/Interval/Interval_DG.thy`
- `src/Analysis/Instances/Mixed/Mixed_Sign_Interval.thy`
- `src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Seeded_Clean_Ctx_Collect.thy`
- `src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/*`
- executable examples with `no_enter` assumptions

Do **not** bulk-replace:

- pattern matches `EA_Enter xs es`;
- statements mentioning `(u, EA_Enter xs es, v)`;
- any theorem where the proof later uses `xs` or `es`;
- exact example graph-shape witnesses.

Implementation note:

- test each `sed` script on one file first;
- prefer search + targeted replace over repository-wide blind replacement.

Build gate:

- `Voblint_CFG`, then `Voblint_Analysis`, then `Voblint_Formalization`

Risk:

- low to medium. Mechanical, but proof scripts may rely on exact rewritten text.

### Stage 3: collecting owner-lemma migration

Goal:

- move generic proofs off raw `EA_Enter` / combine membership and onto owner
  collecting lemmas.

Files:

- `src/CFG/Collecting/CFG_Collect.thy`
- `src/CFG/Collecting/CFG_Collect_Trace.thy`
- `src/CFG/Collecting/CFG_Collect_Activation.thy`
- `src/CFG/Collecting/CFG_Collect_Runs.thy`
- selected CFG compiler-support theories that quote collecting facts

Work:

- add owner lemmas such as:
  - `edge_collect_enterI/E`
  - `cfg_collect_from_enter_edge`
  - `combine_collect_returnI/E`
  - `cfg_collect_from_combine`
- rewrite internal proofs to use those owner lemmas instead of restating the
  raw constructor facts.

Why this matters:

- later Analysis layers quote these files heavily;
- once this slice is done, downstream proofs can stop re-proving entry/return
  flow facts.

Build gate:

- `Voblint_CFG`

Risk:

- medium. Proof-local changes, but still inside the owner layer.

### Stage 4: generic equation-system migration

Goal:

- remove raw call/return metadata reasoning from the generic Analysis core.

Files:

- `src/Analysis/Generic/Equations/Constraint_System.thy`
- `src/Analysis/Generic/Equations/Constraint_System_Sound.thy`
- `src/Analysis/Generic/Solver/Core/TD_Side_CFG.thy`
- `src/Analysis/Generic/Solver/Core/TD_Side_Tree.thy`
- `src/Analysis/Generic/Solver/Core/TD_Side_Eff_Sound.thy`
- `src/Analysis/Generic/Solver/Core/TD_Side_Eff_Soundness.thy`

Work:

- rephrase combine-side assumptions via `combine_*` selectors and owner lemmas;
- rephrase entry-side assumptions via `is_enter_action` and collecting view
  lemmas;
- keep theorem statements stable where possible;
- add compatibility corollaries if an internal theorem needs a better-shaped
  statement.

This is the first slice that materially shrinks future blast radius.

Build gate:

- `Voblint_Analysis`

Risk:

- medium to high. These theories have many downstream consumers.

### Stage 5: Goblint context / DG overlay migration

Goal:

- make overlays consume the same stable views instead of raw edge and combine
  shapes.

Files:

- `src/Analysis/Generic/Solver/Context/Ctx_Collect_Backbone.thy`
- `src/Analysis/Generic/Solver/Context/Goblint/Read/*`
- `src/Analysis/Generic/Solver/Context/Goblint/Read/Support/*`
- `src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/*`
- `src/Analysis/Generic/Solver/Context/Goblint/DG/*`

Sub-slices:

1. replace bare `EA_Enter` boolean tests with `is_enter_action`;
2. replace entry-edge raw membership assumptions with owner view lemmas;
3. replace raw combine tuple destructuring with selector facts;
4. where repeated obligation bundles still rebuild entry facts manually,
   package them behind owner lemmas or, if justified, one locale.

This is where `context_domain` is the reference pattern:

- package a real interface once;
- reinterpret old proofs through it.

Build gate:

- `Voblint_Analysis`

Risk:

- high. Many theorem signatures and `OF` chains live here.

### Stage 6: instance and executable-bridge migration

Goal:

- align domain instances and executable transport with the generic interfaces.

Files:

- `src/Analysis/Instances/Sign/*`
- `src/Analysis/Instances/Interval/*`
- `src/Analysis/Instances/Mixed/*`
- `src/Analysis/Instances/NamedGlobalSign/*`
- `src/Analysis/Generic/Solver/Exec/Exec_Bridge.thy`

Work:

- switch instance-side no-enter assumptions and entry-side reasoning to
  owner-level predicates;
- keep executable `value` output behavior unchanged;
- avoid locale or representation changes in executable generators unless forced.

Build gate:

- `Voblint_Analysis`

Risk:

- medium. Mostly consumer adaptation.

### Stage 7: examples, tooling, and docs

Goal:

- stop non-regression examples from amplifying representation churn.

Files:

- `src/CFG/CFG_GraphViz.thy`
- `src/Analysis/Instances/Tooling/Analysis_GraphViz.thy`
- `src/Formalization/Examples/*`
- README and docs updates

Work:

- keep exact tuple assertions only in deliberate graph-layout regression
  examples;
- otherwise switch to owner view APIs;
- refresh stale README wording once the code is already migrated.

Build gate:

- `Voblint_Formalization`

Risk:

- low to medium.

### Stage 8: optional representation cleanup

Goal:

- cash in the indirection once consumers are off the raw shapes.

Possible work:

- `combine_info` tuple -> record;
- internal cleanup of call/return helper names;
- deletion of deprecated aliases and compatibility corollaries.

Prerequisite:

- previous stages build green;
- consumer grep confirms raw tuple destructuring is largely gone.

Build gate:

- full batch build

Risk:

- high if attempted early;
- moderate if attempted only after the previous slices are complete.

## 5.2 What can be automated

### Safe automation

Good candidates for `sed` / batch replace:

- boolean tests:
  - `a \<noteq> EA_Enter` -> `\<not> is_enter_action a`
  - `a = EA_Enter` -> `is_enter_action a`
    when no payload is used
- stale doc wording
- simple theorem assumptions of the form:
  - `\<(u, a, v) \<in> edges g \<Longrightarrow> a \<noteq> EA_Enter`
    where later proof steps only use the negative test

Workflow rule:

1. test on one file first;
2. inspect the diff;
3. only then apply to a narrow file set.

### Unsafe automation

Do not use blind `sed` for:

- `EA_Enter xs es` payload-bearing patterns;
- tuple binders like `(c, ex, ret, dst)` in theorem statements;
- `case` splits that bind tuple components;
- proof scripts using `cases`, `obtain`, or `induction` over those exact shapes;
- tuple -> record conversion.

These need proof-aware editing.

## 5.3 Suggested shell strategy

Use bulk replacement only for the mechanical stage.

Recommended pattern:

1. locate candidates with `rg`;
2. copy the candidate list into a temporary file;
3. apply the replacement to one representative file;
4. batch-apply only if the representative proof survives;
5. build the affected session immediately.

Examples of narrow searches:

```bash
rg -n 'a \\<noteq> EA_Enter|a = EA_Enter' src/Analysis src/Formalization
rg -n '\\(c, ex, ret, dst\\)|\\(c, ex, v, dst\\)' src/CFG src/Analysis src/Formalization
rg -n '\\(u, EA_Enter|\\(cfg_entry g, EA_Enter' src
```

Do not do repository-wide replacement in one shot.

## 5.4 Fast path

If the goal is fastest practical risk reduction, stop after Stage 4.

That yields:

- owner interfaces published;
- mechanical `EA_Enter` tests mostly cleaned up;
- collecting and generic solver/equation layers moved onto stable views;
- future call/return refactors much smaller.

At that point:

- the biggest architecture win is already captured;
- the `Voblint_CFG_Core` / `Voblint_CFG_Compiler` session split becomes easier;
- the remaining work is mostly overlay and example cleanup.

## 6. Compatibility policy

This migration should not break downstream proofs abruptly.

Rules:

1. New interfaces land before any representation cleanup.
2. Old theorem names stay alive as aliases during migration.
3. New owner lemmas should be proved in both directions when that helps old
   proof styles:
   - introduction form;
   - elimination form;
   - simp form.
4. If a theorem statement would widen from raw tuples to selectors, add a
   corollary with the old shape first and migrate callers gradually.
5. Treat examples and GraphViz output as compatibility clients too.

This is the same pattern that already worked well for `context_domain`: additive
interface first, then reinterpret the old route through it.

## 7. Candidate future session splits

The scan does identify plausible future session splits, but only some are worth
doing soon.

### 7.1 High-confidence split: `Voblint_CFG` core vs compiler simulation

Current `Voblint_CFG` mixes two concerns:

- CFG syntax + collecting + pruning
- compiler simulation support (`Compile_Invariants`, `Control_*`,
  `Located_*`)

Observation:

- `Voblint_Analysis` depends on CFG core and collecting, not on compiler
  simulation.
- `Compiler_Correctness.thy` in `Voblint_Formalization` is the main consumer of
  the compiler-simulation stack.

Candidate split:

```text
Voblint_IMP2
  -> Voblint_CFG_Core
  -> Voblint_Analysis

Voblint_CFG_Core
  -> Voblint_CFG_Compiler

Voblint_Analysis + Voblint_CFG_Compiler
  -> Voblint_Formalization
```

Why this is good:

- it matches a real seam;
- it reduces rebuild pressure on analysis work;
- it does not require new mathematics, only import and ROOT restructuring.

Prerequisite:

- keep compiler proofs from depending on raw CFG internals more than necessary;
- the interface work above helps.

Recommended order:

1. complete Stages 1-4 of the seam migration;
2. split `Voblint_CFG` into core vs compiler;
3. let that settle before attempting any further session change.

Concrete session sketch:

```isabelle
session Voblint_CFG_Core in "src/CFG" = "Voblint_IMP2" +
  description "CFG syntax, collecting semantics, and pruning"
  sessions
    "Dijkstra_Shortest_Path"
  directories
    "Collecting"
  theories
    CFG_Def
    CFG_Path
    CFG_GraphViz
    IMP2_Proc_to_CFG
    CFG_Collect
    CFG_Collect_Trace
    CFG_Prune
    CFG_Collect_Runs
    CFG_Collect_Activation

session Voblint_CFG_Compiler in "src/CFG" = "Voblint_CFG_Core" +
  description "Compiler simulation and located execution"
  directories
    "Compiler"
  theories
    Compile_Invariants
    Control_Residual
    Located_Exec
    Control_Simulation
    Located_Reaches
```

Why the folder constraint is satisfied:

- all core theories stay in `src/CFG` plus `src/CFG/Collecting`;
- all compiler theories stay in `src/CFG/Compiler`;
- the split follows the existing physical layout.

Import-header churn required:

- compiler theories currently import core theories by bare name because they are
  in the same session;
- after the split they must import them qualified from `Voblint_CFG_Core`.

First concrete edits:

- [Compile_Invariants.thy](/Users/manuellerchner/git/goblint-formalization/src/CFG/Compiler/Compile_Invariants.thy:1)
  - `CFG_Collect_Runs` -> `"Voblint_CFG_Core.CFG_Collect_Runs"`
  - `CFG_Collect_Trace` -> `"Voblint_CFG_Core.CFG_Collect_Trace"`
  - `CFG_Prune` -> `"Voblint_CFG_Core.CFG_Prune"`
- [Control_Residual.thy](/Users/manuellerchner/git/goblint-formalization/src/CFG/Compiler/Control_Residual.thy:1)
  - `Compile_Invariants` can stay bare inside `Voblint_CFG_Compiler`
- [Located_Exec.thy](/Users/manuellerchner/git/goblint-formalization/src/CFG/Compiler/Located_Exec.thy:1)
  - `Control_Residual` can stay bare
- [Control_Simulation.thy](/Users/manuellerchner/git/goblint-formalization/src/CFG/Compiler/Control_Simulation.thy:1)
  - `Located_Exec` can stay bare
- [Located_Reaches.thy](/Users/manuellerchner/git/goblint-formalization/src/CFG/Compiler/Located_Reaches.thy:1)
  - `Control_Simulation` can stay bare

Downstream session adjustments:

- `Voblint_Analysis` should depend on `Voblint_CFG_Core`, not `Voblint_CFG_Compiler`;
- `Voblint_Formalization` should depend on both `Voblint_Analysis` and
  `Voblint_CFG_Compiler`, because [Compiler_Correctness.thy](/Users/manuellerchner/git/goblint-formalization/src/Formalization/Pipeline/Compiler_Correctness.thy:1)
  uses the compiler simulation stack.

### 7.2 Medium-confidence split: `Voblint_Analysis` base vs Goblint overlays

Current `Voblint_Analysis` packs:

- generic domain + equations;
- TD-side core;
- Goblint context/read/routing/DG overlays;
- concrete instances;
- executable bridges.

There is a real conceptual seam:

- base solver soundness exists before the Goblint-facing overlays.

Candidate split after interface cleanup:

```text
Voblint_CFG_Core
  -> Voblint_Analysis_Base
  -> Voblint_Analysis_Goblint
  -> Voblint_Analysis_Instances
```

But this is not cheap today because:

- some instance soundness theories already depend on Goblint-side theories such
  as `Retain_Analysis`;
- raw `EA_Enter` and combine-shape dependencies blur the base/overlay seam.

Recommendation:

- do not split this yet;
- first migrate to owner interfaces;
- then re-audit whether Sign/Interval base soundness can sit below the Goblint
  overlays.

Candidate split after the seam cleanup:

```text
Voblint_CFG_Core
  -> Voblint_Analysis_Base
  -> Voblint_Analysis_Goblint
  -> Voblint_Analysis_Instances
```

Interpretation:

- `Voblint_Analysis_Base`
  - `Generic/Domain`
  - `Generic/Equations`
  - `Generic/Solver/Core`
  - `Generic/Solver/Exec`
- `Voblint_Analysis_Goblint`
  - `Generic/Solver/Context/Goblint/*`
  - `Ctx_Collect_Backbone`
- `Voblint_Analysis_Instances`
  - `Instances/Sign`
  - `Instances/Interval`
  - `Instances/Mixed`
  - `Instances/NamedGlobalSign`
  - `Instances/Tooling`

Why this is the second plausible split:

- it matches a real conceptual seam between the generic side-solver core and
  the Goblint-facing overlays;
- it would reduce rebuild scope for domain and base-solver work;
- it creates a cleaner dependency story for future non-Goblint solver or domain
  experiments.

Why it is not first:

- instance soundness still crosses into Goblint-side theories;
- raw `EA_Enter` and combine-shape dependencies still blur the seam;
- some current theory ordering in `src/Analysis/ROOT` suggests practical
  coupling that should be reduced before the split.

Readiness criteria:

1. generic Analysis core no longer destructures raw call/return metadata;
2. Goblint overlays consume owner-level CFG/collecting interfaces;
3. Sign/Interval base domain work can build without importing most Goblint
   routing/read machinery.

Migration order if pursued:

1. split `Voblint_CFG`;
2. re-check imports and build times;
3. only then prototype `Voblint_Analysis_Base` / `Voblint_Analysis_Goblint`;
4. keep `Voblint_Analysis_Instances` last, because it will reveal any remaining
   accidental cross-seam dependencies.

Concrete session sketch:

```isabelle
session Voblint_Analysis_Base in "src/Analysis" = "Voblint_CFG_Core" +
  description "Generic domains, equations, side-solver core, and exec bridge"
  sessions
    TD
  directories
    "Generic/Domain"
    "Generic/Equations"
    "Generic/Solver/Core"
    "Generic/Solver/Exec"
  theories
    Abstract_Domain
    Exec_St
    Split_State
    Constraint_System
    Constraint_System_Sound
    Analysis_Sound
    TD_Side_CFG
    Strategy_Tree_Monad
    TD_Side_Tree
    TD_Side_Eff_Sound
    TD_Side_Eff_Bounds
    TD_Side_Eff_Interface
    TD_Side_Eff_Pipeline
    TD_Side_RHS_Generator
    TD_Side_Eff_Soundness
    Exec_Bridge
    Solver_Side_RG
    Solver_Menu

session Voblint_Analysis_Goblint in "src/Analysis" = "Voblint_Analysis_Base" +
  description "Goblint-facing read, routing, activation, and DG overlays"
  directories
    "Generic/Solver/Context"
    "Generic/Solver/Context/Goblint/Read"
    "Generic/Solver/Context/Goblint/Read/Support"
    "Generic/Solver/Context/Goblint/Routing"
    "Generic/Solver/Context/Goblint/Routing/Support"
    "Generic/Solver/Context/Goblint/Routing/Support/Activation"
    "Generic/Solver/Context/Goblint/DG"
  theories
    Ctx_Collect_Backbone
    Global_Cmp_Read
    Context_Domain
    TD_Side_Eff_Cmp_Sound
    Clean_RRead_Sound
    Seed_EnterMono_Lift
    Seeded_Clean_Ctx_Collect
    Seeded_Activation_Sound
    Seeded_Activation_Reach
    Activation_Witness_From
    Digest_Global_Read
    Value_Digest_Reader
    TD_Side_Eff_Cmp_Pull
    TD_Side_Eff_Cmp_Gen
    DG_Framework
    DG_Soundness
    DG_Context_Soundness
    DG_Route_Soundness
    Local_DG
    Retain_Analysis

session Voblint_Analysis_Instances in "src/Analysis" = "Voblint_Analysis_Goblint" +
  description "Concrete domains and analysis tooling"
  directories
    "Instances/Sign"
    "Instances/Interval"
    "Instances/Mixed"
    "Instances/NamedGlobalSign"
    "Instances/Tooling"
  theories
    Sign_Lattice
    Sign_Arithmetic
    Sign_Backward
    Sign_Print
    Sign_Transfer
    Sign_Local_Effects
    Sign_Domain
    Sign_Side_Soundness
    Sign_Exec
    Sign_Exec_Sound
    Sign_DG
    Value_Digest_Read
    Interval_Bounds
    Interval_Lattice
    Interval_Warrowing
    Interval_Arithmetic
    Interval_Backward
    Interval_Transfer
    Interval_Print
    Interval_Domain
    Interval_Side_Soundness
    Ivl_Exec
    Interval_DG
    Mixed_Sign_Interval
    Exec_DG_Bridge
    Sign_Named_Global_Eff
    Activation_Domain_Instances
    Analysis_GraphViz
```

Why the folder constraint is satisfied:

- each proposed session owns complete existing subtrees;
- no theory would need to be moved physically to make the directories work;
- this is important because the current repository already uses directory
  boundaries as pseudo-seams.

Where feasibility is strongest:

- `Base` depends only on `Voblint_CFG_Core` and `TD`;
- `Goblint` depends on `Base`, not vice versa;
- `Instances` can sit above `Goblint`, because instance soundness already
  imports overlay theories such as `Retain_Analysis`.

Where import-header churn would land:

- any Goblint overlay importing a base theory by bare name would need
  qualification;
- any instance importing base or Goblint theories by bare name would need
  qualification once it crosses the new session boundary.

Representative first edits if prototyped:

- [Context_Domain.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/Read/Context_Domain.thy:1)
  - `TD_Side_CFG` -> `"Voblint_Analysis_Base.TD_Side_CFG"`
- [Global_Cmp_Read.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/Read/Global_Cmp_Read.thy:1)
  - `TD_Side_CFG` -> `"Voblint_Analysis_Base.TD_Side_CFG"`
- [TD_Side_Eff_Ctx_Shared.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/Read/Support/TD_Side_Eff_Ctx_Shared.thy:1)
  - `TD_Side_Tree` -> `"Voblint_Analysis_Base.TD_Side_Tree"`
- [DG_Framework.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Framework.thy:1)
  - `Exec_Bridge` -> `"Voblint_Analysis_Base.Exec_Bridge"`
  - `TD_Side_Eff_Cmp_Gen` can stay bare inside `Voblint_Analysis_Goblint`
- [Sign_Side_Soundness.thy](/Users/manuellerchner/git/goblint-formalization/src/Analysis/Instances/Sign/Sign_Side_Soundness.thy:1)
  - `TD_Side_Eff_Soundness` -> `"Voblint_Analysis_Base.TD_Side_Eff_Soundness"`
  - `Retain_Analysis` -> `"Voblint_Analysis_Goblint.Retain_Analysis"`

Top-level session consequence:

- `Voblint_Formalization` would depend on `Voblint_Analysis_Instances`;
- if it still needs compiler simulation, it would also depend on
  `Voblint_CFG_Compiler`.

### 7.3 Low-confidence split: executable/demo sub-session

A separate session for executable bridges and `by eval` examples is possible, but
it is less urgent.

Why low confidence:

- examples intentionally exercise the real pipeline;
- splitting them too early risks churn for little architectural gain.

Recommendation:

- keep executable examples under `Voblint_Formalization` for now.

## 8. Recommended first slice

If only one slice is done next, make it the CFG call/return interface.

Concrete first steps:

1. strengthen `CFG_Def.thy` as the sole owner of call/return metadata selectors
   and edge predicates;
2. add owner lemmas for `enter_predecessor_list` and combine-predecessor views;
3. migrate `CFG_Collect*`, `Constraint_System*`, and `TD_Side_CFG` to those
   views without changing theorem statements;
4. batch-build;
5. only then continue into context overlays and instances.

This is the highest-leverage move because it shrinks future source/CFG refactor
blast radius and unlocks the `Voblint_CFG_Core` / `Voblint_CFG_Compiler` split.

## 9. Non-goals

This migration does not propose:

- rewriting the generator hierarchy as a full locale tower;
- deleting executable definitions in favor of locale constants;
- changing the mathematics of collecting, solver correctness, or compiler
  correctness;
- forcing an immediate tuple-to-record rewrite;
- splitting sessions only for smaller heaps without a real seam.

## 10. Success criteria

The migration is successful when:

1. source/CFG call-return representation changes are absorbed mainly in
   `IMP2_Proc`, `CFG_Def`, `IMP2_Proc_to_CFG`, and collecting owner theories;
2. generic Analysis theories reason through selectors and owner lemmas instead
   of constructor shapes;
3. examples and tooling stop being major amplifiers of representation churn;
4. the `Voblint_CFG_Core` / `Voblint_CFG_Compiler` split becomes a mechanical
   follow-up, not a proof-design project;
5. downstream proofs survive the migration through additive aliases and
   compatibility corollaries rather than large theorem rewrites.
