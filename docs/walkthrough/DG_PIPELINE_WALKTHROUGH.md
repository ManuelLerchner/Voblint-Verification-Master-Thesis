# D/G pipeline walkthrough: the interval placement example

Worked example of the full pipeline, using
`src/Examples/Interval/Example_Interval_Placement.thy`. Every constant and
lemma name below exists in that theory; check there for full statements.

```text
VIMP source
  -> compiled CFG (compile_prog)
  -> D/G equation system (placed_dg_gen_of_strict / hook_gen)
  -> per-node strategy trees (edge / enter / combine)
  -> TD_side_warrowing_apinis_Interp_solve  (executable result)
  -> executable-to-abstract transport (dg_refines_on, se_constraint_holds)
  -> abstract post-solution (part_post_solution)
  -> ltr_collect coverage (hook_post_solution_collect_sound_ltr)
```

## The source program

```text
global balance, request_count;
void add(x) {
  tmp := balance + x;
  balance := tmp;
  request_count := request_count + 1;
  return balance
}
void main() { answer := add(3) }
```

Two declared globals get **independent placement policies**:

- `placement_keep_local (owner, Local_Location x) = True`
  `placement_keep_local (owner, Global_Location x) = (x = ''balance'')`
- `placement_publish_side (owner, Local_Location x) = False`
  `placement_publish_side (owner, Global_Location x) = (x = ''request_count'')`

`balance` is read and written like a local: it stays in the flow-sensitive `D`
component. `request_count` is routed through the shared `G` side channel
instead. Nothing else about the two globals differs -- the point of the
example is that this one placement choice is the entire difference between
them.

## CFG compilation

`placement_cfg = compile_prog (prog_table placement_prog) (prog_procs
placement_prog) prog_main_name (prog_main placement_prog)`.

`compile_prog` produces ten nodes for this program, reached through
`placement_hook_lists`:

| Node | Kind | Predecessor |
| --- | --- | --- |
| `FunctionEntry prog_main_name` (= `cfg_entry`) | entry (seed) | -- |
| `Statement 5` | edge (nop) | `FunctionEntry prog_main_name` |
| `Statement 6` | combine | caller `Statement 5`, callee result `FunctionResult ''add''` |
| `FunctionResult prog_main_name` | edge (`EA_Ret None`) | `Statement 6` |
| `FunctionEntry ''add''` | enter | `(Statement 5, CallEdge (Some ''answer'') [''x''] [N 3])` |
| `Statement 0` | edge (nop) | `FunctionEntry ''add''` |
| `Statement 1` | edge (assign `tmp`) | `Statement 0` |
| `Statement 2` | edge (assign `balance`) | `Statement 1` |
| `Statement 3` | edge (assign `request_count`) | `Statement 2` |
| `FunctionResult ''add''` | edge (`EA_Ret (Some balance)`) | `Statement 3` |

`calls placement_cfg` holds the single four-place relation `(Statement 5,
CallEdge (Some ''answer'') [''x''] [N 3], FunctionEntry ''add'', Statement
6)`: call site, action, callee entry, and caller **continuation** (where
control resumes after the call returns) -- the combine node itself. The
combine tree at `Statement 6` separately queries the caller's own state at
`Statement 5` and the callee's result at `FunctionResult ''add''`; the latter
is not part of the `calls` tuple. `intra`/`calls` are executable sets;
`placement_finI`/`placement_finC` get their finiteness from the generic
`compile_prog_finite`, not from `eval` (`cfg_node` is not a `finite` type).

Each generated node has one incoming generator case (edge, enter, combine,
or the entry seed); combine nodes are the one kind that queries two local
unknowns (caller and callee result) rather than one.

## D/G equation generation

`placement_sound_dg_hooks.hook_gen` (an interpretation of the generic
`sound_dg_hooks` locale) builds one `strategy_tree` per node, dispatching on
node kind exactly like the CFG table above:

- **edge** nodes fold a single incoming `placement_abs_edge_tree`, applying
  the interval transfer for that edge's `edge_action` to the predecessor's
  `D \<squnion> G`.
- **enter** nodes (`FunctionEntry ''add''`) use `placement_abs_enter_tree`,
  binding the call's actual argument (`N 3`) to the formal `x` under a fresh
  frame, again reading the caller's `D \<squnion> G`.
- **combine** nodes (`Statement 6`) use `placement_abs_combine_tree`, joining
  the caller's pre-call state with the callee exit's state through
  `combine_collect_abs`.
- the **entry** seed (`cfg_entry`) is not built from a tree fold at all: its
  own local/global answer is exactly the constant seed pair
  `placement_s0d_abs`/`placement_s0g_abs`
  (`placement_hook_gen_entry`).

Each tree still separates a **local answer** half (what this node
contributes to its own `D` unknown, always with a `bot` `G` component --
`placement_hook_gen_globs_bot`) from a **side** half (what it publishes to
the one shared `G` slot, always with a `bot` local component --
`sides_of_rhs_Inl_bot`). `placement_keep_local`/`placement_publish_side`
decide, per scoped location, which half a location's value lands in;
`placement_project_split_join` shows the split reconstructs the unsplit
abstract state exactly, since every location is either owner-independent
(`keep_local` on every local) or one of the two declared globals, each routed
to exactly one side.

`dep\<^sub>L` (the set of local unknowns a tree depends on) mirrors the same
per-kind case split: a singleton `{predecessor}` for edge/enter nodes, a pair
`{caller, callee_exit}` for the combine node, and the empty set for the entry
seed (`placement_hook_gen_single_edge_dep` / `_enter_dep` / `_combine_dep` /
`_entry_dep`).

## Solving

`placement_dg_eqs` is the *executable* mirror of the same equation system,
built by `placed_dg_gen_of_strict` over `ivl_tf_st_for`/`ivl_enter_st_for` and
the executable seed `cinit_ivl_st`. `placement_dg_td_sol` runs the vendored
`TD_side_warrowing_apinis_Interp_solve` solver on it once
(`placement_dg_td_terminates` confirms termination), and
`placement_dg_td_post_solution` records that the result is a
`part_post_solution` over exactly the ten computed nodes
(`placement_nodes_eq: fst placement_dg_td_sol = placement_nodes`).

Concrete solved values (`placement_dg_td_values`), each an interval `Ivl lo
hi`:

- `x` at `Statement 0`: `[3, 3]` (the actual argument, bound on entry).
- `balance` at `Statement 2`: `[3, 3]` -- exact, because `balance` stays in
  `D` and this program calls `add` exactly once.
- `request_count` in the shared side unknown `Inr ()`: `[0, +inf)` --
  widened, because the warrowing solver's global side channel accumulates
  across the whole run rather than following one call's straight-line flow.
- `answer` at `Statement 6`: `[3, 3]`, after the call's combine step joins
  the caller's pre-call state with `add`'s returned `balance`.

Nothing here isolates `balance`'s precision to a single mechanism in the
solver; it is simply what falls out of tracking `balance` in `D` while this
program only calls `add` once. Read `[0, +inf)` for `request_count` as the
price of routing a value through the shared `G` channel instead.

## Executable-to-abstract transport

Two different finite sets show up from here on, and they are not the same
thing: `placement_locations_of node` is one node's own executable *location*
scope (what `dg_refines_on`'s `universe` ranges over); `placement_nodes` is
the solved set of ten *CFG unknowns* (what `part_post_solution`'s `vars`
ranges over, and what `dep\<^sub>L`'s closure check lands in).

Each of the ten nodes gets a `dg_refines_on` fact
(`placement_dg_refines_statement0`, ..., `placement_dg_refines_function_entry_add`)
relating the executable solver's local/side pair, on that node's own
`placement_locations_of` scope, to the abstract hook's local/side pair, built
from the generic per-kind bridges
`placement_dg_refines_edge`/`_enter`/`_combine` plus a raw per-location
transfer-agreement fact.

`placement_local_bound` and `placement_side_bound` lift a `dg_refines_on`
fact plus an outside-scope bound into a genuine abstract inequality, using
`le_lift_if_dg_refines_on_and_le`'s `complete_abs_on` completion: known inside
the node's scope, `top` (`D`) or `bot` (`G`) everywhere else. The one-lemma
combinator `placement_se_constraint_holds` bundles both halves --
`traverse_rhs \<le>` the node's own abstract slot, and
`sides_of_rhs \<le>` the abstract state entirely (trivial off the single `Inr
()` key, via `sides_of_rhs_Inl_bot`) -- into the `se_constraint_holds` shape
that `part_post_solution` actually demands. `placement_se_edge`/`_enter`/
`_combine` package the generic per-kind proof once each; `placement_se_entry`
handles the seed directly from `placement_entry_local_le`/
`placement_entry_side_le`.

## Abstract post-solution and collecting soundness

`placement_dg_td_abs_post_solution` assembles the ten `se_constraint_holds`
facts, the `dep\<^sub>L` closure facts, and exit-node membership into one
`part_post_solution` over the abstract hook equations
(`part_post_solution_iff_se_constraint_holds`).

`placement_dg_td_collect_sound` is the endpoint: `hook_post_solution_collect_sound_ltr`
(from the `sound_dg_hooks_ltr` locale -- a re-packaging of `sound_dg_hooks`
with no extra obligations) turns that post-solution, plus finiteness of
`intra`/`calls`, coverage of every entry/edge/enter/combine target by
`placement_nodes`, and the concrete seed bound `placement_sound0`
(`cinit_stores \<subseteq> gamma_ownership_split placement_s0d_abs placement_s0g_abs`), into:

```text
ltr_collect (declared_global placement_prog) placement_cfg
  (cinit_stores (declared_global placement_prog)) v
    \<subseteq> dg_hook_gamma gamma_ownership_split placement_sigma_abs v
```

Every stack-faithful local trace starting from the concrete initial stores
is bounded, at every node `v`, by the abstract post-solution's
concretization -- the D/G hook route's collecting-soundness guarantee, for
this program, machine-checked end to end.
