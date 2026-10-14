# Signed overflow

The concrete semantics wraps a signed overflow (the `-fwrapv` reading). How a
domain treats a *possible* signed overflow is a separate choice, Goblint's
`sem.int.signed_overflow`, selected with `--signed-overflow` (or
`--set sem.int.signed_overflow`):

- `assume_top` (default, as in Goblint): a signed `+`, `-` or `*` that may
  leave its kind's range gives the kind's top.
- `assume_wraparound`: the domain wraps as the concrete semantics does.

Both are proved sound. The same three overflowing operations run under each
policy and each domain: `precision/` holds the `assume_wraparound` runs, which
pin the wrapped value, and `known-imprecision/` the `assume_top` runs, which
lose it by design. `precision/04` shows the Int product's `no_ov`: where the
interval proves that the result fits, the congruence keeps its class under
`assume_top`.

The overflow diagnostics are the same under both policies: a signed `+`, `-`,
`*` or `/` raises an obligation that its mathematical result fits the kind, and
the report names every operation it cannot prove safe. An ERROR holds at every
store reaching the operation; a WARNING is a possible overflow. The policy
changes only how precisely the domain bounds a wrapped result, and with it how
many nested operations are decided: `precision/05` and
`known-imprecision/04` run one program under each. A remainder raises no
overflow obligation; C also leaves `INT_MIN % -1` undefined, which Voblint does
not report. Unsigned arithmetic wraps by definition and raises none; Goblint
warns about it as unsigned overflow.

Run with `pixi run python3 tests/run.py 27-signed-overflow`.
