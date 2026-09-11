# Proof verification gates

Proof status is read from the theories and session builds. This file records the
stable gates for assessing a change.

## Source and CFG

- accepted programs satisfy `wf_compile_input`;
- main has no explicit return;
- compiler certificates expose procedure ownership and disjoint ranges;
- source steps are simulated by located CFG execution;
- reached source configurations have `valid_ltr` witnesses.

## Collecting semantics

- `valid_ltr` handles root, call, local flow, procedure result, and resume;
- `valid_ltr` is an inductive set, and `ltr_collect` projects it to stores
  (`ltr_collect_I`/`ltr_collect_E`);
- `activation_collect` groups the same stores by the context `trace_context`
  assigns;
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

- the instance satisfies `sound_dg_spec_core`;
- executable transfers commute with abstract transfers;
- entry and combine routing use the same context discipline;
- the computed post-solution covers plain or activation-indexed collecting
  semantics as claimed.

## Source-facing theorem

- the compiler input satisfies the static source contract;
- the concrete initial store belongs to the abstract seed;
- every explicit coverage premise follows from the solver domain;
- the conclusion refers to the computed solution;
- the conclusion names its collector: `ltr_collect` at the unit context, one
  `activation_collect` bucket at a routed one. A routed bound is not a
  source-facing theorem until a source run is placed in one of its buckets,
  as `sound_table_of_activation` and `sound_table.source_sound` do together.

## Repository checks

```bash
rg -n '^\s*(sorry|oops)\b' src/
python3 scripts/check_isabelle_ascii.py
pixi run vendor-init
AFP=/path/to/afp/thys pixi run isabelle-build
```

Completion requires all affected sessions and the example session to pass the
batch build without `sorry`.
