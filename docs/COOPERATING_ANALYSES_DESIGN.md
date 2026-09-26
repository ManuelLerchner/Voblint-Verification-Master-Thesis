# Cooperating analyses: design record

Status: **implemented** on branch `cooperating-analyses`, checked in the
editor. The batch build, codegen regeneration and thesis checks have not been
rerun since the last changes. This record reverses the earlier decision
against generic analysis composition with MCP-style queries (issue #70 closed
as not planned, and the "Domain composition" and "Cross-analysis query
composition" sections of `NEXT_STEPS.md` and `ROADMAP.md`). The non-goal "No
generic reduced-product constructor" (`NON_GOALS.md`) stands: `int_dom`
reduces numeric domains inside one value, whereas this composes independently
specified analyses that cooperate through queries.

## Goal

Independently verified analyses run as one product. During a transfer, each
may ask questions that the product answers from the predecessor state. One
generic theorem turns the component proofs into an `analysis_contract` for the
product, so an analysis is added by proving obligations about itself and never
about its partners.

## Goblint reference model

Checked against `goblint/analyzer` at `5320a6b7` for MCP and at `0dc12d355`
for `queries.ml`.

| Goblint | Where | Voblint |
| --- | --- | --- |
| `man.ask` on every transfer's manager | `analyses.ml` | `man_ask :: query ⇒ (…, ivl) strategy_program` in `DG_Manager` |
| `Spec.query`; `DefaultSpec.query` returns `Result.top` | `analyses.ml:369` | field `dgs_query`; the template answers `⊤` |
| `EvalInt : exp -> ID.t` | `queries.ml:108` | `datatype query = EvalInt exp`, answers in `ivl` |
| former `MustBeEqual`, `MayBeLess` derived from `EvalInt` | `queries.ml:528–539` | comparisons answered by `[1,1]` or `[0,0]` |
| `query'` meets the answers of all analyses from `Result.top` | `mCP.ml:290–293, 331` | `qry_prod` meets the component handlers |
| manager built around the predecessor product state | `mCP.ml:395–397` (`outer_man`) | `outer_man` installs the spec's handler before the edge runs |
| queries may ask; a cycle answers `Result.top` | `mCP.ml:264–275` | `ask_with`: an already-asked query answers `⊤`; depth bound `query_depth = 1024` aborts generated code when exceeded |
| `enter` takes the Cartesian product of alternatives | `mCP.ml:539` | `prod_enter` |
| globals as a variant, `ask` at combine, events, spawn | `mCP.ml` | not modelled |

The query layer depends on the interval lattice, as Goblint's query layer
depends on `IntDomain`. `Interval_Bounds` and `Interval_Lattice` therefore live
in `Voblint_Domain`, below the framework.

## Query semantics (`Analysis_Query.thy`)

`query_algebra` fixes `answer_holds :: 'q ⇒ 'r ⇒ store ⇒ bool` over a
`semilattice_inf` with top and asks two laws: `⊤` holds everywhere, and the meet
of two holding answers holds. `oracle_holds A s` says every answer of `A` holds
at `s`.

The one interpretation is `eval_holds (EvalInt e) i s ⟷ ⟦e⟧ s ∈ γ i` over
`ivl`. The full interval claims nothing; the meet is `meet_ivl`, sound by
`meet_ivl_gamma`. An empty answer admits no value, so a sound handler returns
it only for a state that represents no store. `ivl_const` reads `[n,n]` back as
`Some n`, and `eval_holds_constD` turns that into `⟦e⟧ s = n`. Tests on answers
are datatype equality on `ivl`, which is executable.

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

## Local specifications that ask (`DG_Spec.thy`, `DG_Spec_Sound.thy`)

A local transfer names its questions up front, `qs :: edge_action ⇒ 'D ⇒ query
list`, and then runs a pure function of the answers (`asking_transfer`). A
question it did not name is answered `⊤`. `local_dg_spec qs qry sk asn …` takes
answer-relative intraprocedural transfers and a pure handler `qry`, installed
as `local_query qry`. Entry and combine take no answers.

`sound_local_dg_spec qry sk asn … gammaD 𝒢` proves each step against every
answer function that holds at the start store:

```text
edge_collect a (gammaD d ∩ {s. oracle_holds A s}) ⊆ gammaD (step A a d)
s ∈ gammaD d ⟹ eval_holds q (qry d q) s
```

`qs` is not a locale parameter: `local_spec_contract` gives `analysis_contract
(local_dg_spec qs qry …)` for every `qs`. A spec that never asks instantiates
`qs = λ_ _. []`, ignores the answers and answers `⊤`; every field then reduces
to the old `local_transfer`, so the Base, lifted and executable builders are
instances of the widened ones. `sound_local_dg_spec_with_qry` replaces the
handler of a sound spec by any other sound handler for the same states.

## Product (`Local_Spec_Product.thy`)

`analysis_product` is a datatype with componentwise order, join, bottom,
widening and narrowing (raw pairs carry `Product_Lexorder`). The product spec
applies both components' transfers to the same answer function, asks the
concatenation of both question lists (`qs_prod`), meets the handlers
(`qry_prod`), intersects the concretizations (`gamma_prod`), and enters with the
Cartesian product of alternatives.

```text
product_local_spec: sound_local_dg_spec A ⟹ sound_local_dg_spec B
                    ⟹ sound_local_dg_spec (A ⊗ B)
product_contract:   … ⟹ analysis_contract (local_dg_spec (qs_prod qs1 qs2) (qry_prod q1 q2) …)
```

Every component receives the answers of every other, and nesting gives n-ary
products, because the answers are fixed once per edge by the generator around
the whole product rather than inside a component.

## Components and wrappers

- `assign_ask` (`Oracle_Wrappers.thy`): at `x = e`, if the answer to `EvalInt e`
  is `[n,n]`, assign `N n`; otherwise the component's own assignment.
  `sound_local_assign_ask` preserves `sound_local_dg_spec`; `assign_ask_qs`
  adds the question.
- `rel_local_component` (`Rel_Order_Local.thy`): the order carrier `relc` as a
  local spec. Its handler `rel_qry` answers comparisons between variables it
  has ordered with `[1,1]` or `[0,0]`, everything else `⊤`. At `x = e` it asks
  `e <= y` and `y <= e` for each candidate `y` (`rel_qs`) and records a pair on
  `[1,1]`. At calls it enters with the empty relation and combines to it,
  which is sound and imprecise by design; `Rel_Order_Domain` remains the
  example of relational call and global behaviour.

## Demo (`Example_Cooperating_Demo.thy`)

Program: `if (x <= y) { if (y <= x) { z = (x == y); __voblint_check(z == 1); } }`.
The product is the executable Interval spec with `assign_ask` and the handler
`aval_ivl`, times `rel_local_component` over `x`, `y`, `z`.

- `coop_after_assignment` (by evaluation): right after the assignment the
  order component holds `(x, y)` and `(y, x)`, and Interval holds `z = [1,1]`.
- `coop_ivl_alone_after_assignment` (by evaluation): Interval alone holds
  `z = [0,1]` there.
- `coop_terminates` (by evaluation): the solver run terminates.
- `coop_contract` (proved): the product spec satisfies `analysis_contract`.

Evidence class: `coop_contract` is machine-checked; the two value lemmas are
executable evidence for one program and support no general precision claim.

## Boundary

The product is certified at the `analysis_contract` level and executed
through the verified solver. It does not reach `run_voblint`, the result
adapter or the CLI: `routed_dg_pipeline` is specialized to the pointwise
carrier. Reaching it means generalizing that pipeline over the carrier (spec
constructor, emptiness test for `DEAD`, readback, classifier); that step is
not claimed to be mechanical.

## Open questions

- Whether a dead component makes the product dead inside the construction,
  as MCP's `map_deadcode` does. Soundness does not need it; precision and the
  `DEAD` verdict do.
- A demo for the relational-consumes-numeric direction.
- Whether the next step adds globals to the product or `ask` at `combine`.
- Thesis placement needs a recorded change to the frozen blueprint.
