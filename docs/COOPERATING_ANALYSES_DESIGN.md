# Cooperating analyses: design record

Status: **implemented**. Cooperating analyses run as components of Goblint's
`MCP` shape and reach `run_voblint`. This record reverses the earlier decision
against generic analysis composition with MCP-style queries (issue #70 closed
as not planned, and the "Domain composition" and "Cross-analysis query
composition" sections of `NEXT_STEPS.md` and `ROADMAP.md`). The non-goal "No
generic reduced-product constructor" (`NON_GOALS.md`) stands: `int_dom`
reduces numeric domains inside one value, whereas this composes independently
specified analyses that cooperate through queries.

## Goal

Independently verified analyses run as one combined state. During a transfer,
each may ask questions that the combined state answers. One generic theorem
turns the component proofs into an `analysis_contract` for the combination, so an analysis is added by proving obligations about itself and never
about its partners.

## Goblint reference model

Checked against `goblint/analyzer` at `5320a6b7` for MCP and at `0dc12d355`
for `queries.ml`.

| Goblint | Where | Voblint |
| --- | --- | --- |
| `man.ask` on every transfer's manager | `analyses.ml` | `man_ask :: query ⇒ (…, answer) strategy_program` in `DG_Manager` |
| `Spec.query`; `DefaultSpec.query` returns `Result.top` | `analyses.ml:369` | field `dgs_query`; the template answers `⊤` |
| `EvalInt : exp -> ID.t`, `ID = Lattice.Lift(IntDomTuple)` | `queries.ml:108`, `valueDomainQueries.ml:9–12` | `datatype query = EvalInt exp`, answers in `answer = int_dom query_lift` |
| former `MustBeEqual`, `MayBeLess` derived from `EvalInt` | `queries.ml:528–539` | comparisons answered by the exact integers `1` or `0` |
| `query'` meets the answers of all analyses from `Result.top` | `mCP.ml:290–293, 331` | `mcp_qry` meets the component handlers |
| manager built around the predecessor product state | `mCP.ml:395–397` (`outer_man`) | `outer_man` installs the spec's handler before the edge runs |
| queries may ask; a cycle answers `Result.top` | `mCP.ml:264–275` | `ask_with`: an already-asked query answers `⊤`; depth bound `query_depth = 1024` aborts generated code when exceeded |
| `enter` takes the Cartesian product of alternatives | `mCP.ml:539` | `mcp_en_from` |
| globals as a variant, `ask` at combine, events, spawn | `mCP.ml` | not modelled |

The query layer depends on the integer product lattice, as Goblint's query
layer depends on `IntDomain`. The value lattices therefore live under `Int/`
in `Voblint_Domain`, below the framework.

## Query semantics (`Analysis_Query.thy`)

`query_algebra` fixes `answer_holds :: 'q ⇒ 'r ⇒ store ⇒ bool` over a
`semilattice_inf` with top and asks two laws: `⊤` holds everywhere, and the meet
of two holding answers holds. `channel_holds A s` says every answer of `A` holds
at `s`.

The one interpretation is `eval_holds (EvalInt e) a s ⟷ ⟦e⟧ₑ s ∈ γ a` over
`answer = int_dom query_lift`, Goblint's `Lattice.Lift(IntDomTuple)`
(`Query_Lift.thy`). `QTop` claims nothing and is how an analysis declines a
query; `QBot` admits no value, so a sound handler returns it only for a state
that represents no store. The meet lifts the `int_dom` meet, which is exact
(`gamma_inf_int_dom`), so combining answers loses nothing.
`answer_of_int` is the exact answer for a known integer and `answer_const`
reads one back (Goblint's `of_int` and `to_int`); `eval_holds_constD` turns
`answer_const a = Some n` into `⟦e⟧ₑ s = n`. An interval-only handler answers
`answer_of_ivl`, the interval with every other component at top.

## Manager and specification (`DG_Manager.thy`, `DG_Spec.thy`)

`man_ask` is a program, so a handler may read globals and the dependency shows
up in the compiled equations. `dgs_query :: man ⇒ query ⇒ program` is the
spec's handler. `dg_spec_edge_program` runs the edge under
`outer_man (dgs_query S) m`, whose channel is `ask_with (dgs_query S)
query_depth {}`: a handler asking in turn gets the same construction one level
down, with the asked set growing. Exhausting the depth calls `Code.abort`,
whose logical value is `⊤`, so the bound plays no part in soundness.

`dg_spec_wf` asks well-formedness of an edge step and of a query handler under
every well-formed ask channel (`dg_spec_wf_step_ask`, `dg_spec_wf_query`);
`sp_wf_ask_with` then gives well-formedness of the installed channel.

## Components (`MCP_Spec.thy`)

An analysis that cooperates is an `local_spec`: a record with one field per
operation of Goblint's `Spec` (`ls_query`, `ls_skip`, `ls_assign`, `ls_special`,
`ls_branch`, `ls_body`, `ls_return`, `ls_event`, `ls_enter`,
`ls_combine_env`, `ls_combine_assign`). Every field receives a channel of type
`channel`, the counterpart of `man.ask`. `sound_local_spec 𝒢 γ c` states
each operation's obligation against every channel that holds at the store it
is asked about; the edge obligation splits into one named law per field
(`ls_step_sound_iff`), and `sound_local_spec_update` replaces one field
while re-proving only that field's law.

`mcp_combine` folds several components into one, meeting their handlers
(`mcp_qry`) and entering with the Cartesian product of alternatives
(`mcp_en_from`). `mcp_combine_sound` proves the combination sound for the
intersection of the concretizations when the components are pairwise framed
(`mcp_independent`). `dg_spec_of_contract` turns a sound component into an
`analysis_contract`. `lens_of` runs a component on one field of the combined
record; `analysis_product` (`Local_Spec_Product.thy`) is the componentwise
ordered pair the generated carrier nests.

## Components and wrappers

- `ask_assign` (`Channel_Wrappers.thy`): at `x = e`, if the channel answers
  `EvalInt e` with an exact integer `n`, assign `N n`; otherwise the
  component's own assignment. It replaces the assign field only, so its
  soundness is `assign_ask_sound` plus the update lemma.
- `order_spec` (`Rel_Order_Local.thy`): the order carrier `relc`. Its
  handler `relc_qry` answers comparisons between variables it has ordered with
  the exact integers `1` or `0`, everything else `⊤`. At `x = e` it asks the
  channel `e <= y` and `y <= e` for each tracked `y` and records a pair on the
  exact answer `1`. At calls it enters with the empty relation and combines to
  it, which is sound and imprecise by design; `Rel_Order_Domain` remains the
  example of relational call and global behaviour.

## Evidence

`coop_demo_needs_both` (`Example_Analysis_Dispatch_Regression.thy`, by
evaluation of `run_voblint`) runs
`if (x <= y) { if (y <= x) { z = (x == y); __voblint_check(z == 1); } }`:
Interval alone and Order alone leave the check `UNKNOWN`; both together prove
it. This is executable evidence for one program and supports no general
precision claim. Soundness of the combined run is the generic
`run_voblint` theorem over the MCP carrier.

## Open questions

- Whether a dead component makes the product dead inside the construction,
  as MCP's `map_deadcode` does. Soundness does not need it; precision and the
  `DEAD` verdict do.
- A demo for the relational-consumes-numeric direction.
- Whether the next step adds globals to the product or `ask` at `combine`.
- Thesis placement needs a recorded change to the frozen blueprint.
