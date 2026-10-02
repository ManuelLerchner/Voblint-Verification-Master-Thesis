# Analyses / Int

`Voblint_Analysis_Int` is `int_dom`: the reduced product of Sign, Interval, Parity and
Congruence. It is the only domain here whose components can talk to each other, and
that exchange — refinement — is what this session is about.

It is parented on `Voblint_Nonrelational` and lists the four component sessions, so it
is the one analysis session that sees more than its own domain, by construction.

## Vocabulary

| Term | Meaning |
| --- | --- |
| reduced product | a product lattice where components may sharpen one another. Without that exchange it would be a plain product and no more precise than its parts run separately. |
| reduction step | a function on `int_dom` that is *exact* — `int_reduction_step` requires it to preserve the concretization while descending the order, so a sharpened component never drops a concrete state |
| `Refine_Never` | disable cross-component reduction. Native component filters remain active; Congruence alone has nontrivial arithmetic inverses for addition, subtraction, and multiplication. |
| `Refine_Once` | one reduction round per composite operation |
| `Refine_Fixpoint` | iterate reduction to a fixpoint. The production default. |
| distributed information | a fact no single component holds: Congruence's `6 (mod 0)` plus Interval's `[0,10]` pin a value neither pins alone |

## The layer chain

```text
Int_Lattice             (Voblint_Domain) the four-component record and its concretization
Int_Warrowing           componentwise widen/narrow and the numeric_domain instance
Int_Refinement          exactness of reduction steps; one refinement round
Int_Refinement_Control  the three refine modes
  -> Int_Arithmetic / Int_Backward                   mode-aware forward and backward
  -> Int_Transfer                                    the bundle int_dom_ops mode and its
                                                     one interpretation, parametric in mode
  -> Int_Exec                                        executable transfer and entry, and
                                                     their commutation, at every mode
  -> Int_Classify                                    check discharge
  -> Int_Sound                                       initial-state facts
  -> generated/Int_Fixpoint_Analyses                 the unit-context registrations at
     generated/Int_Once_Analyses                     Refine_Fixpoint, Refine_Once and
     generated/Int_Never_Analyses                    Refine_Never (generated; see below)
```

Like Interval, Int has a component with infinite ascending chains, so the global
update rule matters: every registration takes it as a parameter, and the CLI
defaults to Apinis warrowing (`Globals_Warrow`).

Each mode is registered as an analysis of its own, `Int_Analysis Refine_Fixpoint`,
`Int_Analysis Refine_Once` and `Int_Analysis Refine_Never`, each with its own
field of the combined state. The CLI's `--int-refinement` picks one (default
`fixpoint`); the facts behind all three are the same mode-generic ones.

On programs, `once` and `fixpoint` give the same results in every case we know
of. A refinement chain is at most two rounds long (Congruence never learns from
Interval, and Parity learns from it only at singletons), every guard already
refines twice, and an arithmetic result's bounds already agree with its
congruence. The difference `refinement_round_is_progressive` witnesses needs
operands no stored state has. `never` differs visibly: see the regression
fixtures `16-composite-domain/precision/12`–`15`.

Checks do not refine. As in Goblint's `IntDomTuple`, a comparison is decided
when one component decides it on its own value (`int_less_true` and its
siblings in `Int_Backward`), so the mode reaches a check only through the
values the transfers stored and the evaluator computed. Under `never`, a fact
only the combined components know, such as a remainder that is `[0,5]` in
Interval and `1 (mod 6)` in Congruence, does not prove `r == 1` (fixture 15).

## Worked example: `if (y + 1 == 3) { x := 1 } else { x := 0 }`

The guard gives `y + 1 = 3`. Backward filtering inverts `+` and hands the leaf `y` a
candidate. What each mode then does with it:

- `Refine_Never` — Congruence narrows `y` to `2 (mod 0)` and Parity to `PEven`, each through
  its own inverse of `+`; Sign and Interval learn nothing, so `y` stays `STop`/`top` there.
- `Refine_Once` — one round pushes the congruence singleton into the other three, and
  `y` becomes `SPos`/`[2,2]`/`PEven`/`2 (mod 0)`: exact.
- `Refine_Fixpoint` — the same, here. One round already sufficed *for this guard*.

`Exec_Int_DG_Run` (Examples/Int) proves the `Refine_Never` and `Refine_Once` results by
real solver runs and closes with `dgExI_never_ne_once`; the CLI regression pins all
three modes. That `Once` equals `Fixpoint` here
is not a general fact: `refinement_round_is_progressive` in `Example_Int_Domain` is a
witness where a further round still makes progress.

## Division and reduction

Exact division benefits from the existing reduction steps: Congruence keeps
`(6*n)/3` in `0 (mod 2)`, and reduction transfers that fact to Parity as even.
With `Refine_Never`, Congruence retains the class but Parity remains top.
Division by `1` or `-1` also preserves unbounded interval endpoints, such as
`[7,+inf] / -1 = [-inf,-7]`.

The division/remainder fixture
`tests/regression/16-composite-domain/precision/11-division_remainder_reduction.vimp`
combines bounded division with modular information to prove a singleton
remainder. The individual components cannot prove that check.
`int_division_remainder_progressive` compares the modes: one round obtains
`[1,1]` but leaves Sign nonnegative; fixpoint refinement reads the tightened
interval on its next round and makes Sign positive.

## Widening

`Int_Warrowing` is exactly componentwise — Interval's own accelerating widen and narrow
surface through and no reduction runs afterwards. That is deliberate: a concrete
counterexample there shows that running `refine` after `narrow` (which is Goblint's own
choice) would break the solver's `narrow_ge` bracket.

## Int in the entry-state and call-string runs

`generated/Int_Fixpoint_Analyses.thy` and its two siblings are machine-written from `manifests/analyses.yaml`,
so the orientation a reader needs lives here rather than in a header the
generator owns.

Int's own generated file registers only the context-insensitive run,
`int_fixpoint_rule`. The entry-state and call-string runs are the CLI's combined
registrations, `mcp_es_rule` and `mcp_cs_rule` (`Voblint_CLI.MCP_Analyses`),
which run every active analysis as fields of one state; Int is one of those
fields whenever an `Int_Analysis mode` is in the activation list. Neither policy has
a pipeline of its own. Both are interpretations of `dg_analysis`, which
owns the equation system, the solve, the covered keys, the reader, the result
table, the contextual report and the activation-indexed soundness endpoint —
for every active combination at every policy.

Int is the domain where two axes meet, and they stay independent in every run
that includes it.

`mode` is Int's refinement axis. Every obligation asked of Int's field is
discharged by one of Int's own mode-generic facts — `int_tf.is_sound_nonrelational_transfer`,
`int_tf.tf_st_for_commute`, `int_tf.enter_st_for_commute`, `int_cinit_gamma`, the
two classifier laws — so each would hold at an arbitrary `refine_mode`. The
manifest registers one analysis per mode by naming the bundle at that mode
(`ops: {const: int_dom_ops, args: [Refine_Fixpoint]}`, and likewise at
`Refine_Once` and `Refine_Never`) and the mode-taking abstract operations as applied
roles, because each field needs one concrete choice;
the facts it cites are the same at every mode.

The global update rule is the second axis. `int_fixpoint_rule` leaves it free as `r`,
and so do the combined `mcp_es_rule` and `mcp_cs_rule` runs, alongside the
activation list.

A call string is the last `k` call sites on the stack. `cs_route` never reads
the state it is handed, which makes `fun_route_activation_collect_sound` the
applicable endpoint. The entry-state run keys a callee on the abstract values
its formals hold on entry, and `exec_formals_route` does read that state, so
`entry_state_activation_collect_sound` applies there instead — its
admitted-context relation is the one the entry answer induces rather than the
graph of a function on stores.

`int_fixpoint_rule` is a `global_interpretation` with its runtime data left free
through `for` — `r` at the unit context. `mcp_es_rule` and `mcp_cs_rule` leave
the activation list free the same way — `as r`, and `as k r` at the call
string — and none renames the pipeline through `defines`: a caller applies
`mcp_cs_rule.result as k r gs p` directly, with `Int_Analysis Refine_Fixpoint` in `as`.

Int carries no emptiness predicate of its own. The shared assembly pins the
bottom test to the program's declaration predicate and proves it agrees with
the semantic emptiness test.
