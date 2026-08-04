# Completion vs. scoped abstract states: evidence from M4

The interval placement example (`Example_Interval_Placement.thy`) is the
first full D/G soundness chain proved through the hook route
(`hook_post_solution_collect_sound_ltr`), including the executable-to-abstract
transport step. This is an evaluation of where that transport's complexity
actually lived, prompted by finishing it -- not a proposal to migrate
anything. No line of the locked architecture changed.

## The two shapes being compared

**Completion (current, locked architecture).** `abs_state = vname => 'a`: a
total function over every variable name, unscoped and un-owned. The
executable side (`resolved_st_q`) is a sparse representation over unowned
executable `location`s (`Local_Location vname | Global_Location vname`);
procedure ownership is supplied separately, only at projection time, through
`scoped_location = pname \<times> location`. The strict placement trees
(`placed_dg_gen_of_strict`) project each generated executable result onto the
finite location universe declared for the write node -- that scoping is a
property of how those trees are built, not an invariant of `resolved_st_q`
itself. `dg_refines_on` states pointwise agreement between the executable and
abstract sides on a named finite `universe`; `complete_abs_on` pins
everything *outside* that universe to a fixed default (`top` for locals,
`bot` for the one shared global slot); `le_lift_if_dg_refines_on_and_le`
composes the two into a genuine `\<le>` between the executable value and the
total abstract state.

**Scoped abstract states (not built, not attempted here).** Each node's own
abstract value would be scoped to exactly its own locations -- a partial
map, or a state indexed per activation -- mirroring `resolved_st_q`'s own
finite shape directly, rather than being completed into a total function
after the fact.

## Where completion's cost actually showed up

- **The executable/abstract shape mismatch is the source of most of this
  session's proof work.** `placement_local_bound` and `placement_side_bound`
  exist for one reason: the strict placement trees only produce a value
  known on a finite scope, while the abstract side is asked to be a total
  function. Discharging that gap needed the `complete_abs_on` completion, an
  explicit outside-scope bound per node, and `placement_complete_bot_le` to
  discard the completion wrapper once inside it. None of that has anything
  to do with intervals, edges, or calls -- it is pure plumbing between
  "finite" and "total."
- **Owner-sensitive locals force a projection step that a scoped
  representation would not need.** `placement_keep_local`/
  `placement_publish_side` are keyed on `scoped_location = pname \<times>
  location`, not on `vname` alone, because a total `vname => 'a` state
  cannot otherwise distinguish one procedure's local from another's of the
  same name. `project_abs_on`/`project_resolved_on_strict` slice the total
  state down to one owner's view, and `placement_project_split_join` has to
  separately prove that the local/side split reconstructs the unsplit state
  exactly. Owner identity could become structural, eliminating this
  particular name-disambiguation projection -- but a scoped design would
  still need its own laws for scope transitions, split/recombination, joining
  states with different scopes, and caller/callee frame interaction, so this
  is not a lemma that simply disappears without replacement.
- **`bot` as "the other half" is safe only by a checked invariant, not by
  construction.** `placement_hook_gen_globs_bot` and `sides_of_rhs_Inl_bot`
  establish that a node's local answer always carries `bot` in its `G`
  slot and its side contribution always carries `bot` in its `D` slot. This
  is a structural invariant of the D/G encoding, not an incidental fact: a
  local result carries meaningful `D` and `bot` `G`, a side result carries
  `bot` `D` and meaningful `G`, and the semantic interpretation reconstructs
  the full state only by combining the two complementary halves before
  applying `gamma_state` (defined pointwise, `\<forall>x. s x \<in> \<gamma>(f x)`).
  `bot` is safe in the unused half only because it is never handed to
  `gamma_state` on its own -- interpreting either half as a complete state by
  itself would generally collapse to the empty concretization. A
  representation that does not carry an irrelevant half at all sidesteps
  the question rather than relying on that combination invariant to answer
  it.
- **Call/return scope transitions reuse the same completion machinery
  rather than a first-class "new scope" primitive.** `placement_abs_enter_tree`
  reads the caller's `D \<squnion> G`, and `placement_abs_combine_tree` reads
  both the caller's and the callee's, all through the same projection
  apparatus used for the plain per-node scope check.

## Where completion earned its keep

- **The bridging lemmas are exactly as generic as the framework needs them
  to be.** `dg_refines_on`, `complete_abs_on`, and
  `le_lift_if_dg_refines_on_and_le` know nothing about intervals, edges, or
  calls, or about `add` versus `main`. The same three lemmas, instantiated
  once per node kind (`placement_se_edge`/`_enter`/`_combine`), covered all
  nine non-entry nodes; each node needed only its own predecessor/call facts
  supplied, not new proof engineering. That is the batch-friendly shape this
  project asks for.
- **Totality keeps every semantic statement uniform.** `gamma_state`,
  `dg_hook_gamma`, and the soundness obligations they feed never carry a
  definedness or partiality side condition. Every lemma in this file, and
  every other D/G example in the repository (Sign, the CallString and Ctx
  instances, Mixed_Sign_Interval), shares this same total-function
  convention for exactly that reason.
- **The completion recipe, once established, is reusable across kinds with
  no per-node variation in shape.** `placement_local_bound`/
  `placement_side_bound` are stated once, generically over the node and the
  executable/abstract side values; every node's own proof is an
  instantiation, not a re-derivation.

## What this review does not establish

This is evidence about where complexity sits in the *current* design, not a
measurement of what a scoped-state redesign would cost. The core solver
interface (`strategy_tree`, `eqsT`), the `dg_spec`/`sound_dg_spec` locales,
and every existing analysis instance are built on total, unscoped
`abs_state`s as a locked decision; a scoped carrier would need to thread
through all of that, not just this one example, and nothing here measures
that cost. Whether the projection/completion tax paid here is smaller or
larger than what a scoped redesign would cost elsewhere in the framework is
an open question -- one this session's proof work supplies evidence for on
one side of the ledger only.
