# Site figures

Every case here backs a figure on the GitHub Pages site (`pages/index.html`) that quotes the analyzer's output: a verdict, an interval, a
node count, or a solve that never finishes. The figures carry those values in
their markup and scripts, so without these cases a change in the analyzer
would leave the site silently wrong. When one of these cases fails, the
figure it names needs the same update as its expected result.

Each case's header names its figure. Categories follow `tests/run.py`:
`precision/` for results the figure presents as exact, `known-imprecision/` for
the UNKNOWN answers a figure explains, and the group root for the solves a
figure reports as "no answer", pinned with `--timeout 5`. The `EXPECT-GRAPH`
blocks pin the per-node values the figures draw; the node and context counts in
"The price of precision" are the node and distinct-context counts of those
blocks.

## Coverage

| Figure | Program | Cases |
| --- | --- | --- |
| What a run is; The life of a call; The proof chain; strategy trees (call tabs) | factorial `a = f(2)` | `precision/01-factorial_entry_state`, `known-imprecision/01-factorial_no_context` |
| Four domains, one value: reduction | `x = 4 * n + 1` within `[0,10]` | `precision/02-int_reduction_int`, `known-imprecision/02`–`05-int_reduction_*` |
| From a graph to equations to values; widening stepper; solver step-through; zoom lens; compiler morph | counting loop | `precision/03-counting_loop` |
| A real bug, replayed (Voblint side) | goblint/analyzer #1161 regression test `37-congruence/14` | `precision/04-goblint_1161_congruence_mod` |
| The flagship theorems (explorer program) | `theorems` example | `precision/05-theorems_program` |
| Many runs in, one region per node out | `multiples-of-three` | `known-imprecision/06-multiples_of_three_interval`, `precision/06-multiples_of_three_int` |
| Which Globals setting should you pick? | two call sites, call inside a loop, growing and shrinking recursion | `precision/07`–`17`, `known-imprecision/07`–`09`, `01`–`02-recursion_grows_*_diverges` |
| A call that never stops calling | `recursion-bounded`, `recursion-grows` | `precision/18`–`30`, `03-recursion_grows_entry_state_diverges` |
| The price of precision | fan-out, `down(5)` | `precision/31`–`42`, `known-imprecision/10-down_call_string_4` |
| Context sensitivity: how many copies of a procedure; Reading a result | playground demo | `precision/43`–`44-demo_*`, `known-imprecision/11`–`12-demo_*` |

## What is not pinned

- "No answer within 12 s" (the Globals table) and "within 60 s" (the spiral) are
  pinned only as "does not finish within 5 s".
- The spiral's "Stops at 10" program is pinned for Join and Warrow in each
  context mode; Join per origin and Warrow per origin, which the figure reports
  as identical, are not.
- The spiral's Join and Join-per-origin rows under call strings, and Warrow per
  origin under entry state, report "no answer" without a case.
- Figures that transcribe a proof or a solver definition by hand (the solver
  step-through, the strategy trees' evaluation steps) are checked by reading,
  not by a case.
