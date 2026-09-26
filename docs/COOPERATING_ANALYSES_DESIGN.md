# Cooperating analyses: design note

Status: **proposed**, not implemented. This note reverses the recorded
decision against generic analysis composition with MCP-style queries: the
closure of issue #70 as not planned, and the "Domain composition" and "Cross-analysis
query composition" sections of `NEXT_STEPS.md` and `ROADMAP.md`. It must be
accepted before any theory is written. The non-goal "No generic reduced-product
constructor" (`NON_GOALS.md`) can stay: `int_dom` reduces numeric domains
inside one value, whereas this note composes independently specified analyses
that cooperate through queries. Issue #70 and its comment record Goblint's
mechanism in detail; this note fixes the formalization shape it left open.

## Goal

Two independently verified analyses run as one product. During a transfer,
each may ask questions that the other answers from the predecessor state. One
generic theorem turns the component proofs into an `analysis_contract` for the
product, so a new analysis is added by proving obligations about itself and
never about its partners.

## Goblint reference model

Voblint follows Goblint's MCP at the semantic level: each component provides a
query function, transfers receive a manager-style `ask`, and the product asks
every component on the predecessor product state and meets the answers.
Version 1 specializes this to a statically typed binary product, one query
kind, pure non-recursive query handlers and no global channel. It copies the
semantics, not the dynamic OCaml encoding.

Checked against `goblint/analyzer` at `5320a6b7` (the revision the alignment
register uses):

| Goblint | Where | Voblint v1 |
| --- | --- | --- |
| activated analyses chosen at run time, state as `(int * Obj.t) list` | `mCP.ml` `spec_list` | two components in `analysis_product D₁ D₂`; nesting gives n-ary |
| `Queries.t`, a GADT whose constructor fixes the result lattice | `queries.ml` | `datatype query = EvalBool exp`, one flat Boolean answer lattice |
| `Spec.query`; `DefaultSpec.query` returns `Result.top` | `analyses.ml:369` | `qry :: D ⇒ query ⇒ answer`; the default answers `Unknown` |
| `query'` folds `Result.meet` from `Result.top` over all analyses | `mCP.ml:290–293, 331` | the handler of `A ⊗ B` meets the component answers; `close` turns it into the oracle |
| component transfers get a manager built from the predecessor product | `mCP.ml:395–397` (`outer_man`/`inner_man`) | `close` computes the oracle once per edge from the whole predecessor state |
| `enter` takes the Cartesian product of the component alternatives | `mCP.ml:539` | same |
| one dead component makes the product dead | `mCP.ml` `map_deadcode` | open (see below) |
| queries may ask; answers cached; a cycle answers `Result.top` | `mCP.ml:264–275` | omitted: handlers do not ask |
| `ask` at every transfer, `f_ask` into `combine_env`/`combine_assign` | `mCP.ml:570` | intraprocedural edges only |
| globals as a variant, `sideg`, events, spawn, split | `mCP.ml` | omitted |

## Non-goals for version 1

- **No recursive queries.** A query handler reads its own component state
  only; transfers may ask, handlers may not. Goblint's query cache and its
  cycle-breaking `top` are not modelled.
- **No global state in queries or in the product.** Components are local
  specifications (see "Where it attaches"). Goblint composes globals as a
  variant (`DomVariantLattice`); that is left for version 2.
- **No `ask` at `enter`/`combine`.** Goblint threads `f_ask` into
  `combine_env`/`combine_assign`. Version 1 offers the oracle on
  intraprocedural edges only.
- **No `run_voblint` integration.** The product is certified at the contract
  level and executed through the verified solver, as `Rel_Order_Domain` is
  today. It does not reach the public result adapter, the soundness tables or
  the CLI (see "Path to the full pipeline").
- **No change to the numeric domain hierarchy.** `sound_evaluator`,
  `backward_domain` and the expression builders stay oracle-free.

## Where it attaches

Three candidate layers exist.

| Layer | Carrier | Why (not) here |
| --- | --- | --- |
| `routed_dg_pipeline` (`Routed_DG_Analysis.thy:132`) | fixed to `'a exec_dg_st lifted`, classifier over `'a abs_state` | pointwise only; `relc` cannot enter |
| `analysis_contract` (`DG_Spec_Sound.thy:318`) | arbitrary `'D`, `'G`, `γDG` | transfers are CPS `strategy_program`s over the packed `('dl,'dg) dg_state`; a product must embed each component's program into the product state and prove `traverse_program`/`sides_of_program` commute with the embedding |
| `sound_local_dg_spec` (`DG_Spec_Sound.thy:373`) | arbitrary `'D` with `gammaD` | ten pure functions over `'D`; `local_spec_contract` already yields `analysis_contract` |

Version 1 attaches at `sound_local_dg_spec`. Its transfers are pure, so the
product combines them componentwise, and its existing theorem carries the
product down to `analysis_contract`, the equation generator and the solver
without touching anything below. The pointwise numeric analyses already reach
this layer, both unlifted (`sound_transfer_for`'s sublocale `base`) and lifted
(`local_state_dg_spec_for_lifted_contract`, `DG_Local_State_Spec.thy:251`).
Both are over the mathematical state `'a abs_state`. The solver runs the
finite executable state `'a exec_dg_st lifted`; `analysis_contract_st`
(`DG_Local_State_Exec_Refinement.thy:262`) proves that carrier's contract
through `sound_local_dg_spec`, but only inside its proof. A product that the
solver can run needs that executable instance exposed as a component (work
item 4).

`relc` does not reach this layer: it reads and publishes the global channel on
its transfers (`Rel_Order_Domain.thy:318`). The demo therefore needs a
local-only `relc` instance. To keep this from becoming a study of relational
call boundaries, version 1 makes it deliberately coarse at calls: `enter`
yields the caller's relation as continuation and the empty relation as callee
entry, and `combine` returns the empty relation. The empty relation
concretizes to every store, so both obligations hold trivially. The demos need
no precision across calls; the D/G-aware `relc` stays the example of relational
call and global behaviour.

## Query semantics

Version 1 has one query kind, the truth of an expression, because it covers
both demo directions and already has a proved-sound numeric answerer. It is a
constructor, not a bare `exp`, so later kinds extend the datatype. Answers
form a four-element lattice ordered by the truth values they admit; `Unknown`
is Goblint's `Result.top` and `Inconsistent` its bottom:

```text
            Unknown                 admits {True, False}
           /       \
        True       False            admits {True} / {False}
           \       /
          Inconsistent              admits {}

datatype query = EvalBool exp
answer_holds (EvalBool e) a s  ⟷  truthy (⟦e⟧ s) ∈ admits a
```

A handler `qry :: 'D ⇒ query ⇒ answer` is sound when
`s ∈ gammaD d ⟹ answer_holds q (qry d q) s`. For a pointwise numeric state
`check_query` answers with `bool option`, mapped as `None ↦ Unknown` and
`Some b ↦ b`. Its soundness is exactly `check_query_sound`
(`Abstract_Checks.thy`), so the numeric side answers at no new proof cost. `relc` holds pairs
`(x, y)` meaning `s x ≤ s y` (`gamma_rel`, `Rel_Order_Domain.thy:115`), so it
answers `x <= y` true when `(x, y)` is present, `y < x` false for the same
pair, and `x == y` true when both `(x, y)` and `(y, x)` are present.

**Combining answers.** The product meets the two answers. The meet admits
the intersection of what the operands admit, so `True ⊓ False = Inconsistent`
and `Unknown ⊓ True = True`. Because it is associative and commutative,
query aggregation does not depend on the order or nesting of components. It
is Goblint's `Queries.Result.meet` restricted to this one query. Soundness of
the meet is one lemma: if a store satisfies both answers, it satisfies their
meet.

**Extending the vocabulary.** The product theorem is stated over a query
algebra rather than over `EvalBool`:

```text
locale query_algebra =
  fixes answer_holds :: 'q ⇒ 'r::{semilattice_inf, order_top} ⇒ store ⇒ bool
  assumes top_sound: answer_holds q ⊤ s
      and inf_sound: answer_holds q a s ⟹ answer_holds q b s
                       ⟹ answer_holds q (a ⊓ b) s
```

The answers form a meet-semilattice with top, so "no information" is `⊤` and
combining is `⊓`, as in Goblint, and associativity, commutativity and
idempotence come from the class rather than from separate assumptions.

Version 1 interprets it once, at `EvalBool` and the four-element lattice. A
later vocabulary reuses the theorem wherever it fits that interface. Queries with different answer
types (Goblint's `EvalInt` answers an integer abstraction, `MayPointTo` an
address set) need an encoding such as a tagged universal answer type; that
choice is deferred.

## The oracle-relative contract

A component supplies a carrier with its concretization, a query handler, and
transfers that take the oracle, mirroring Goblint's `Spec.query` beside
transfers that receive `man`. Its proof splits into two families: handler
soundness (`s ∈ gammaD d ⟹ answer_holds q (qry d q) s`) and transfer
soundness assuming a sound oracle. The transfers are those of
`sound_local_dg_spec` with an extra first argument on the intraprocedural
ones:

```text
asn :: ask ⇒ vname ⇒ exp ⇒ 'D ⇒ 'D        (likewise sk, sp, br, bd, rt, ev)
ask  = query ⇒ answer
```

and one obligation per operation, weakened by the oracle:

```text
oracle_holds ask s  ≡  ∀q. answer_holds q (ask q) s

s ∈ gammaD d ⟹ oracle_holds ask s ⟹ successor s ∈ gammaD (asn ask x e d)
```

The oracle is quantified in the obligation, never fixed, so a component proof
cannot depend on who answers. An existing `sound_local_dg_spec` becomes a
component by ignoring `ask` and answering `Unknown` to every query, the
analogue of inheriting `DefaultSpec.query`.

**Predecessor-state invariant.** Following MCP's manager model, the oracle is
computed once per edge from the whole predecessor state and passed to every
component. No component sees a partially updated product, so the successor
does not depend on the order in which the component transfers are evaluated.
This matches Goblint, where `man.ask` answers from the state the transfer
starts in.

## Composition and closure

Two operations, kept separate. Composing two components yields a component,
still open in its oracle. Closing a component supplies its own query handler
as the oracle, exactly once, at the outside.

```text
datatype ('a, 'b) analysis_product = Product 'a 'b
                        (componentwise ≤, ⊔, ⊥, widen, narrow)

A ⊗ B:
  gammaD (Product a b)       = gammaD_A a ∩ gammaD_B b
  qry    (Product a b) q     = qry_A a q ⊓ qry_B b q
  step   ask act (Product a b) = Product (step_A ask act a) (step_B ask act b)
  enter  = all pairs of the two alternative lists
  combine = componentwise

close C:
  step' act d = step_C (qry_C d) act d
```

Closing too early breaks n-ary cooperation. Were `A ⊗ B` to close itself with
`qry_A ⊓ qry_B`, then in `(A ⊗ B) ⊗ C` the inner transfers would never see
`qry_C`. With the split, `close ((A ⊗ B) ⊗ C)` hands
`qry_A ⊓ qry_B ⊓ qry_C` to all three transfers, however the product is
parenthesized.

The carrier is a datatype, not `'a × 'b`. This repository loads
`HOL-Library.Product_Lexorder`, so raw pairs already carry the lexicographic
order and cannot take a componentwise instance; `dg_state` wraps its pair
for the same reason (`DG_State.thy:22`).

`enter` takes the Cartesian product because each component's alternatives
cover every concrete entry on their own, as `MCP.enter` does
(`mCP.ml:539`).

**Theorems.** Three, one per construction:

```text
product_component:    component A ⟹ component B ⟹ component (A ⊗ B)
product_query_sound:  qry_A sound ⟹ qry_B sound ⟹ qry_(A ⊗ B) sound
close_component:      component C ⟹ qry_C sound ⟹ sound_local_dg_spec (close C)
```

The headline result is their composition: two components with sound handlers
give `sound_local_dg_spec (close (A ⊗ B))`, and hence `analysis_contract` by
`local_spec_contract`. Closure is the only place an oracle is built, and its
result is an ordinary pure specification, so nothing below it becomes
oracle-aware.

`product_component` is one step per operation: a store in
`gammaD_A a ∩ gammaD_B b` satisfying the oracle meets both components'
premises, so its successor lies in both concretizations. `close_component`
instantiates the oracle with `qry_C d`, which holds at every store of
`gammaD_C d` because the handler is sound.

## Demo

Components: the pointwise Interval analysis and the local `relc` variant.
Each program must yield a check that the product proves and that each
component alone leaves `UNKNOWN`. The comparison is established by evaluation
inside Isabelle and registered as a thesis claim.

- **Numeric consumes relational.** An oracle wrapper around any local
  specification: at `z = e` with `e` Boolean-valued, if `ask (EvalBool e)` is
  `True` or
  `False`, assign the literal `1` or `0`; otherwise fall back to the
  component's own assignment. An answer fixes only the truthiness of `e`, so
  the wrapper is restricted to the comparisons and logical operators, which
  evaluate to `0` or `1` (`VIMP_Expr.thy:122–130`); for `z = x` with `x = 5`,
  `True` would wrongly give `z = 1`. Its soundness follows from that lemma, the
  fallback's soundness and `oracle_holds`. On `Inconsistent` the state is
  unreachable and any result is sound; the wrapper falls back.
  `relc` forgets every assigned variable and learns only at branches, so the
  program builds the equality from two guards:
  `if (x <= y) { if (y <= x) { z = (x == y); check(z == 1) } }`. Interval
  alone keeps `z ∈ [0, 1]`; `relc` alone knows nothing about `z`.
- **Relational consumes numeric.** At `x = e`, the `relc` wrapper asks
  `EvalBool (LessEq e (V y))` and `EvalBool (LessEq (V y) e)` for each tracked
  `y ≠ x` and records every pair answered `True`. The answers are about the predecessor state, and there `e`
  evaluates to the new value of `x` while `y` is unchanged, so the recorded
  relation holds afterwards. Program to be chosen so that the relation must
  survive a point where the numeric bounds are lost.

Neither wrapper touches `aval_abs`, `sound_evaluator` or `backward_domain`.
Generalizing the pattern into an oracle-aware evaluator is later work.

## Isabelle work items

1. `Query.thy` (`Voblint_Framework`): `query_algebra`, the `query` datatype,
   the four-element answer lattice, `answer_holds`, `oracle_holds`, and the
   `query_algebra` interpretation.
2. `Oracle_Local_Spec.thy`: the component locale, the lift of a plain
   `sound_local_dg_spec` (ignore `ask`, answer `⊤`), `close`, and
   `close_component`.
3. `Local_Spec_Product.thy`: the `analysis_product` datatype with a
   componentwise `bounded_semilattice_sup_bot` instance, `⊗`,
   `product_component` and `product_query_sound`.
4. Executable component bridge: expose the Base operations on
   `'a exec_dg_st lifted` as a component, reusing the obligations
   `analysis_contract_st` already discharges.
5. Solver carrier: componentwise `widening`/`narrowing`/`warrowing` on
   `analysis_product`, so the vendored TD solver can run the product.
6. The local `relc` instance and its component contract.
7. The two wrappers, the demo programs, and a certificate per program that the
   product proves the check and each component does not.

Items 1–3 carry the research result. Items 4–7 make it executable and
observable. Gate for each item: the batch build is green.

## Path to the full pipeline

Reaching `run_voblint` means generalizing `routed_dg_pipeline` and the result
adapter over the carrier: its spec constructor, the emptiness test that yields
`DEAD`, readback and the check classifier. The product and query interfaces
above are chosen so that this step does not change them. It may still raise
proof obligations of its own around readback and canonical `Bot` for product
states, so it is not claimed to be mechanical.

## Thesis impact

The structure in `THESIS_BLUEPRINT.md` is frozen, so this needs a recorded
change: a section in the analysis-interface chapter (the oracle-relative
contract and the product theorem) and an evaluation entry (the two demo
programs). The claim must carry its boundary: the product is certified at the
contract level and executed through the verified solver; the public
`run_voblint` path remains specialized to the pointwise family.

## Open questions

- Whether a dead component makes the product dead inside the product
  construction, as `map_deadcode` does in MCP, or only in the pipeline step.
  Soundness does not need it: a component with empty concretization already
  makes `γ₁ ∩ γ₂` empty. Precision and the `DEAD` verdict do.
- Which program demonstrates the relational-consumes-numeric direction
  convincingly.
- Whether version 2 adds globals first or `ask` at `combine` first.
