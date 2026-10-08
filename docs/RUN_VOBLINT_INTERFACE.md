# `run_voblint`: one verified function, one semantic report, one projection

## Principle

Isabelle exports the semantic information the soundness contract needs, plus
domain-owned observations of abstract values. Presentation derived from that
information lives outside the theorems.

Domain knowledge stays with the domain: how `Ivl (Fin 0) (Fin 1)` reads as `[0,1]`
is Interval's business. If OCaml printed it, the renderer would pattern-match every
domain's representation (Congruence is a typedef OCaml cannot look inside) and every
new domain would touch OCaml.

## The boundary

```text
run_voblint   : analysis_config => imp_prog => analysis_report analysis_answer
                                                       (Analysis_Run.thy, verified)
render_report : (abstract_value => 'v) => analysis_report => 'v run_result
                                                       (Analysis_Render.thy, display only)

datatype analysis_config = Analysis_Config
  (config_analyses: analysis_domain list) (config_rule: globals_rule)
  (config_context: context_mode) (config_globals: program_globals)

datatype 'r analysis_answer =
  Invalid_Activation | Malformed_Program | No_Answer | Analysed 'r

valid_config config <-> config_analyses config ~= [] /\ distinct (config_analyses config)
```

The activation list names the analyses that run together, in the order their values
are displayed. `run_voblint` checks it before anything else; an empty list or one
that names an analysis twice answers `Invalid_Activation`. A malformed program
answers `Malformed_Program`. Otherwise the configuration is solved with the
executable solver `solve_c`. `No_Answer` represents the logical `None` branch of
`solve_c`. Where the solve genuinely diverges, the generated code does not return at
all, so `No_Answer` is not an operational timeout result.

The adapters call `run_voblint`, then map `render_report` over the answer with the
value printer they want (`string_of_abstract_value` composed with the CLI's symbol
decoding).

The report is an opaque token to OCaml. Its selectors are not exported; the only
reader is `render_report`, so no OCaml code depends on the report's representation.
`run_voblint_config` and `run_voblint_cfg` state that an analysed report carries the
configuration it was asked for and the compiled graph of the program.

## The report

```text
record analysis_report =
  report_config      :: analysis_config
  report_vars        :: vname list
  report_cfg         :: cfg
  report_contexts    :: report_context list        index = identity and order
  report_states      :: mcp_val result_state list
  report_routes      :: call_route list
  report_checks      :: result_check list
  report_globals     :: mcp_val result_global list
  report_diagnostics :: arithmetic_diagnostic list

datatype report_context =
  Report_Unit | Report_Entry mcp_ctx | Report_Call_String "pp list"
```

The states are semantic (`mcp_val`, the combined state the solver computed), and a
context keeps the policy's own value. No rendered value is part of the report.
`render_report` maps states through `mcp_render` and the printer, and contexts
through `render_context`, into the displayed `'v run_result`; it changes neither
checks, diagnostics, routes nor the graph.

`consistent_report` is about verdicts only. `well_formed_report` states what a
reader of the rows relies on: every context index (of a state, a route and a route
target) is below `length (report_contexts res)`, each `(point, context)` has one row,
each row's `state_checks` lists exactly the report's checks at its point, and its
`state_diagnostics` exactly the graph's arithmetic obligations there
(`obligations_at`), each with the verdict of its own `state_value`. With a consistent report, a check's aggregate verdict is then the
aggregate of the rows' verdicts for it (`well_formed_check_verdict`).
`report_of_well_formed` proves it for every report `report_of` builds, so
`run_voblint_well_formed` holds for every analysed answer. No soundness theorem
needs it.

Checks and diagnostics come twice, and both are load-bearing: `report_checks` and
`report_diagnostics` join every context of a point, which is what a source-level
report states; `state_checks` and `state_diagnostics` keep each context's own
verdict, which is what a drawing of one context shows.

## Semantic spine

The collecting semantics `𝒞 v` is not a starting point: it is the projection of
valid activation traces. A finite source run is represented by a valid activation
trace `t` that ends at some node `v` with the run's store `s`
(`activation_trace_repr`, from `source_run_has_activation_trace`). The policy assigns
`t` a context `c` (`activation_context_rel`), so `s ∈ 𝒜(v, c)`
(`source_store_in_activation_collect`). Under each policy the activation buckets
together are the collecting semantics (`node_collect_eq_Union_activation_collect`
and its per-policy instances). Then:

```text
s ∈ 𝒜(v, c) ⊆ ⋃c'. 𝒜(v, c') = 𝒞 v ⊆ ⟦res⟧⇘v⇙ ⊆ 𝒱⇘res⇙ v
```

`run_voblint_spine` states the chain once, for any context relation `R` and root
context, given what a policy owes: every valid activation trace carries some context,
and the buckets together are the collecting semantics.
`run_voblint_unit_chain`, `run_voblint_entry_state_chain` and
`run_voblint_call_string_chain` (`Analysis_Certified.thy`) state this chain for a
source run, one per policy, since the context type is the policy's own. Each keeps
the witness: the conclusion names the trace `t`, its representation of the run's
configuration, and the context the policy relates it to. Under call strings and the
unit policy every valid trace has its context outright; under entry-state routing
the admitted context exists because the solve returned
(`run_voblint_entry_state_terminates`), read off the registration the placement of
program globals selects (`mcp_es_admitted`). All three chains hold for both
placements. `run_voblint_source_sound` is the context-erased form.

## Public contract

`Analysis_Report.thy` reads a report through two store sets at a point `v`:

```text
⟦res⟧⇘v⇙   (report_sem)      the stores some state at v describes
𝒱⇘res⇙ v  (verdict_stores)  the stores in which every definite verdict at v holds
DEAD res v                   every state at v is Bot
HAS_VERDICT res v e r        some check at v on e has the definite verdict r
```

`PROVED`, `REFUTED` and `UNKNOWN` abbreviate `HAS_VERDICT` at `Check_Proved`,
`Check_Refuted` and `Check_Unknown`. What a verdict claims of a store is
`verdict_holds r e s`: the condition is true, false, or nothing is claimed; `𝒱⇘res⇙ v`
is the stores in which `verdict_holds` holds for every definite verdict at `v`.

A report is `consistent_report` when every check's verdict is the aggregate of its
classifier over its own states at the check's point. From that alone:

| Theorem | Claim |
| --- | --- |
| `analysis_report_verdicts_sound` | `⟦res⟧⇘v⇙ ⊆ 𝒱⇘res⇙ v` |
| `analysis_report_proved`, `analysis_report_refuted` | a definite verdict holds in every store of `⟦res⟧⇘v⇙` |
| `analysis_report_dead`, `sound_emptiness_DEAD` | `DEAD res v ⟹ ⟦res⟧⇘v⇙ = {}`: `DEAD` is a sound emptiness test on points; the converse does not hold: `DEAD_not_exact` gives a report whose point describes no store and is not `DEAD`, its one state being the combined state `mcp_contradiction` that no store satisfies (`mcp_empty_v_not_exact`) |
| `analysis_report_check_dead` | a `Dead` check row's point is `DEAD` |
| `analysis_report_unknown` | an `UNKNOWN` check's point is not `DEAD` |

`analysis_report_of_sound` is the one proof that splits on the context policy: a
report the run builds is consistent, covers the collecting semantics, makes the
arithmetic diagnostics sound, and lists one row per compiled check. It rests on
`report_states_at_report_of`: the report's states at a point are exactly the table's
entries there. That needs the context listing to be complete, which
`ordered_by_key_set` proves for an injective key; the entry-state key breaks ties by
`mcp_ctx_key`, which is injective on every context.

The endpoints, all in `Analysis_Certified.thy`, have no termination premise:

| Theorem | Claim |
| --- | --- |
| `run_voblint_report_contract` | an analysed report answers a valid configuration and a well-formed program, is for exactly that configuration and `prog_cfg p`, is `well_formed_report` and `sound_report`; the theorems below are its consequences |
| `run_voblint_covers` | `𝒞 v ⊆ ⟦res⟧⇘v⇙` |
| `run_voblint_collect_sound` | `𝒞 v ⊆ 𝒱⇘res⇙ v` |
| `run_voblint_source_sound` | a source run stopped anywhere sits at a node `v` (`csim`) with its store in `𝒞 v`, `⟦res⟧⇘v⇙` and `𝒱⇘res⇙ v` |
| `run_voblint_check_sound` | a run about to execute `Check e` finds a listed check for `e` at a node it reaches, not `Dead`, whose verdict holds |
| `run_voblint_proved`, `run_voblint_refuted` | a definite verdict holds at every collected store |
| `run_voblint_dead_unreached`, `run_voblint_dead_check_unreached` | a `DEAD` point collects no store |
| `run_voblint_arithmetic_safe`, `run_voblint_arithmetic_intra_safe` | no diagnostic at `v` means no collected store at `v` divides by zero |
| `run_voblint_well_formed` | the report is `well_formed_report`: indices in range, one row per `(point, context)`, row verdicts are their own state's |
| `run_voblint_check_sites` | `report_checks` lists one check per compiled `EA_Check` edge, in graph order: the rows the verdict theorems speak about are all of the program's checks |
| `run_voblint_unit_chain`, `run_voblint_entry_state_chain`, `run_voblint_call_string_chain` | the semantic spine above, per policy |

```text
                  source
                    |  unverified parser
                    v
                 imp_prog
                    |  run_voblint                verified semantic contract
                    v
             analysis_report
                    |  render_report             deliberately unverified projection
                    v
         'v run_result (strings)
                    |  unverified presentation
                    v
         graph / DOT / HTML / JSON
```

The soundness contract does not speak about `report_routes` or `report_globals`;
`well_formed_report` bounds their context indices and nothing more. It does not state
that routes sit at call edges or that seeds name entered contexts.

## What the theorem does not cover

The theorem is about the semantics of the `imp_prog` Isabelle received. It does not
cover:

- **parser correctness**: source text to `imp_prog`
- **`string_of_abstract_value` and `render_report`**: abstract value to text, report
  to displayed rows
- **presentation correctness**: OCaml cannot alter the verified payload, but a bug
  can misattribute it (for example a state shown at the wrong node)
- **termination**: where the solve does not return, there is no answer and no claim

## One dispatcher

`analysis_report_of` is the one function that reads the context policy.
`scripts/gen_analysis_assembly.py` emits one combined state from
`manifests/analyses.yaml` (`generated/MCP_Carrier.thy`): a nested product with one
lifted field per listed analysis. `MCP_Analyses.thy` registers this state once per
context policy: `mcp_rule` and `mcp_es_rule` for `as r`, `mcp_cs_rule` for
`as k r`. Each branch solves its registration's equations with `solve_c` and builds
the report from the `solved_run` that answer gives (`DG_Analysis.thy`). The
activation list, the rule and the call-string bound are parameters, so no
combination has an instance of its own.

A transfer asks the combined state through the query channel. Every active
analysis answers from its own field, and the answers are met. A handler may ask
through the same channel while it answers: `ask_rec` answers a query already being
asked with `⊤` and bounds the depth, as Goblint's `MCP.query'` does. Inactive fields
start at their bottom and stay there. A step whose result makes any active field
`Bot` makes the whole state `Bot`. A check reads the met answer of every active
analysis to `EvalInt` of the check's expression, and `answer_check` classifies that
one answer (`Check_Answer.thy`).

## Enumerating contexts

`covered_keys` is a set, and a domain's value type already spends its `ord`
instance on the abstraction order. The abstraction order and the listing order are
unrelated structures; `order_key` exists only to enumerate finite context sets
deterministically. `Dispatch_Carrier.thy` supplies `order_key`
(`Key_Int | Key_Node | Key_List`) with a derived `linorder`, and every abstract value
has an injective key (`inj_abstract_value_key`). `report_of` lists contexts with
`ordered_by_key`: unit contexts by `Key_List []`, call strings by
`Key_List (map Key_Node ...)`, entry-state contexts by `entry_ctx_key`, whose first
component is the active analyses' formal values (the display order) and whose
second, `mcp_ctx_key`, separates contexts those values do not.
