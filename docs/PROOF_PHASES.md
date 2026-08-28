# Proof verification gates

Proof status is read from the theories and session builds. This file records the
stable gates for assessing a change.

## Source and CFG

- accepted programs satisfy `wf_compile_input`;
- main has no explicit return;
- compiler certificates expose procedure ownership and disjoint ranges;
- source steps are simulated by located CFG execution;
- reached source configurations have `valid_ltr` witnesses.

## Machine-integer typing

- every compiled action carries an elaborated `texp`, and both the concrete and
  the abstract semantics evaluate it with `teval` -- no evaluator inside the
  fixpoint consults a `tyenv`;
- `elaborate_to` emits a `TCast` only where the target kind differs from the
  kind the expression synthesizes, so a same-kind write costs no precision;
- `styped Gamma s` is a *public* premise of the source-facing theorems, not an
  internal side condition: it appears in `source_run_has_ltr`,
  `source_activation_sound`, `source_reaches_ltr_collect`,
  `source_completes_ltr_collect_exit`, and in the executable
  `run_source_sound` bundles;
- each domain instantiates `sound_cast_domain`, and its `a_cast` /
  `a_in_range` obligations are discharged against `ik_norm` / `ik_range`, not
  assumed.

## Collecting semantics

- `valid_ltr` handles root, call, local flow, procedure result, and resume;
- `ltr_collect` is characterized by its least fixpoint;
- keyed and activation collectors are projections of valid traces;
- abstract closure obligations imply collector coverage.

## Equation systems

- executable and mathematical RHS views share one contribution abstraction;
- local-edge, entry, and combine transfers are sound;
- post-solutions cover `ltr_collect`;
- finite enumerations agree with their set specifications.

## Solver

- executable state operations commute with function-state operations;
- strategy-tree generation refines the abstract equation system;
- solver success yields a partial post-solution;
- demand-cone restrictions are reflected only in the abstract guarantee.

## D/G instances

- the instance satisfies `sound_dg_spec`;
- executable transfers commute with abstract transfers;
- entry and combine routing use the same context discipline;
- the computed post-solution covers plain or activation-indexed collecting
  semantics as claimed.

## Source-facing theorem

- the compiler input satisfies the static source contract;
- the concrete initial store belongs to the abstract seed *and* is `styped`
  for the program's typing environment;
- every explicit coverage premise follows from the solver domain;
- the conclusion refers to the computed solution.

## Repository checks

```bash
rg -n '^\s*(sorry|oops)\b' src/
python3 scripts/check_isabelle_ascii.py
pixi run vendor
AFP=/path/to/afp/thys pixi run build
```

Completion requires all affected sessions and the example session to pass the
batch build without `sorry`.
