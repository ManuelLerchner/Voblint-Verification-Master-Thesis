# M4 semantic baseline

This baseline records observable behavior that the reduced M4 migration must
preserve for the existing classic-split policy. It is intentionally expressed
in theorem and executable-result form so later changes can distinguish an
intended storage-class change from an accidental analysis regression.

## Interval D/G flagship

Source: `Example_Interval_DG_Flagship.thy`.

- The executable solver terminates at `(cfg_exit flagship_cfg, ())`
  (`flagship_terminates_c`).
- The solved local-unknown set has cardinality `6`.
- The computed local interval for `x` is:

  | CFG node | Interval |
  | --- | --- |
  | `Statement 0` | `[-inf,+inf]` |
  | `Statement 1` | `[0,20]` |
  | `Statement 2` | `[0,19]` |
  | `Statement 3` | `[20,20]` |

- `flagship_head_computed`, `flagship_body_computed`, and
  `flagship_exit_computed` certify the three nontrivial bounds.
- `glob_x_at_head` certifies that the side component contains no local `x`
  information.
- `flagship_source_run_sound` is the source-level soundness endpoint.

The annotated DOT baseline has one `main / root context` cluster, nodes for
`entry_main`, `pp0` through `pp3`, and `exit_main`, with the interval labels
listed above and the six expected control-flow edges.

## Global-across-call witness

Source: `Example_Inc_Proc.thy`.

`pcompletes_inc_pcall_declared` proves that invoking `p` preserves a declared
global across entry and return while incrementing it:

```text
pcompletes (declared_global inc_program) inc_pi p() s
  (s(Gx := s Gx + 1))
```

This witness already uses the declaration-driven classifier. During reduced
M4 it remains the compatibility baseline for existing `Gx` programs; the thin
validation slice will add the same behavior for a declared global without a
`G` prefix and a `G`-named implicit local.

## Baseline gate

Before broad example migration, the classic-split interval slice must preserve
these computed values, the six-node solved coverage, the global-across-call
result, and the DOT node/edge/label structure.
