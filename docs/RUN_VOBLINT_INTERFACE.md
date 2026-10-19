# `run_voblint`: one verified function, one semantic report, one projection

The analysis generator (`scripts/gen_analysis_assembly.py`, `manifests/analyses.yaml`)
is gone; the combined carrier is the hand-written `MCP_Carrier.thy` in `Voblint_CLI`.

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

The adapters call `run_voblint`, then map `prog_render_report` over the answer with
the value printer they want (`string_of_report_value` composed with the CLI's symbol
decoding).

The report is an opaque token to OCaml. Its selectors are not exported; the only
reader is `render_report`, so no OCaml code depends on the report's representation.
`run_voblint_report_contract` states that an analysed report carries the
configuration it was asked for and the elaborated graph of the program.

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
`prog_render_report` maps states through each analysis's `render` and the printer, and contexts
through `render_context`, into the displayed `'v run_result`; it changes neither
checks, diagnostics, routes nor the graph.

Each row's `state_checks` and `state_diagnostics` give that row's own verdicts for
the checks and arithmetic obligations (`obligations_at`) at its point.

Checks and diagnostics come twice, and both are load-bearing: `report_checks` and
`report_diagnostics` join every context of a point, which is what a source-level
report states; `state_checks` and `state_diagnostics` keep each context's own
verdict, which is what a drawing of one context shows.

## Semantic spine

The collecting semantics `𝒞 v` is not a starting point: it is the projection of
valid activation traces. A finite source run is represented by a valid activation
trace `t` that ends at some node `v` with the run's store `s`
(`gactivation_trace_repr`, from `source_run_has_activation_trace`). The policy assigns
`t` a context `c` (`activation_context_rel`), so `s ∈ 𝒜(v, c)`
(`source_store_in_activation_collect`). Under each policy the activation buckets
together are the collecting semantics (`node_collect_eq_Union_activation_collect`
and its per-policy instances). Then:

```text
s ∈ 𝒜(v, c) ⊆ ⋃c'. 𝒜(v, c') = 𝒞 v = reaching ds p v,  and every s there lies in a listed state
```

`run_voblint_spine` states the chain once, for any context relation `R` and root
context, given what a policy owes: every valid activation trace carries some context,
and the buckets together are the collecting semantics.
`run_voblint_call_string_chain` and `run_voblint_entry_state_chain`
(`Run_Voblint.thy`) state this chain for a source run, one per policy, since the
context type is the policy's own; call strings of bound 0 are the context-insensitive
case. Each keeps the witness: the conclusion names the trace `t`, its representation
of the run's configuration, and the context the policy relates it to. Under call
strings every valid trace has its context outright; under entry-state routing the
admitted context exists because the solve returned. Both chains hold for both
placements. `run_voblint_source_sound` is the context-erased form.

## Public contract

`Analysis_Report.thy` reads a report at a point `v` through its states
(`report_states_at res v`) and its check rows. `PROVED res v c`, `REFUTED res v c`
and `UNKNOWN res v c` say that some check at `v` on `c` has that verdict, `DEAD res v`
that every state at `v` is `Bot`, and `SAFE res v` that no arithmetic diagnostic
names `v`. `report_states_at_report_of` shows that the states a run's report lists at
a point are exactly the solved table's entries there; it needs a complete context
listing, which `ordered_by_key_set` gives for an injective context key.

`report_sound conf ds p res` (`Run_Report.thy`) collects everything a report
guarantees: a row for every check edge, and at every store `s ∈ reaching ds p v` a
listed state containing `s`, no `DEAD` check, correct `PROVED` and `REFUTED` rows,
every obligation of `obligations_at ds p v` met when `SAFE res v`, and a refuted
obligation failing. `report_run_sound` is the one proof that splits on context policy
and placement.

The endpoints, in `Run_Voblint.thy`, have no termination premise; an `Analysed`
answer exists only when the solve returned:

| Theorem | Claim |
| --- | --- |
| `run_voblint_report_contract` | an analysed report answers a valid configuration and a well-formed program, for exactly that configuration and `elab_cfg p ds` |
| `run_voblint_sound` | every reaching store lies in a listed state, no check there is dead, `DEAD` points collect nothing |
| `run_voblint_report_sound` (`run_voblint_PROVED`, `run_voblint_REFUTED`, `run_voblint_SAFE`) | definite verdicts and `SAFE` hold at every reaching store |
| `run_voblint_arithmetic_safe` (`_intra`, `_call`, `_return`, `_min`, `_max`), `run_voblint_arithmetic_refuted`, `run_voblint_no_signed_overflow`, `run_voblint_no_remainder_overflow`, `run_voblint_no_conversion_overflow` | what `SAFE` and a refuted diagnostic say about each arithmetic obligation |
| `run_voblint_dead_unreached` | a `DEAD` point collects no store |
| `run_voblint_source_sound` | every core run of `elab_ptable p ds` from `init_stores (kenv_of ds)` is simulated at some node where the report covers it and its verdicts hold |
| `run_voblint_check_sound`, `run_voblint_labelled_check_sound` | a run about to execute a check finds its listed row, not `Dead`, whose verdict holds |
| `run_voblint_spine`, `run_voblint_call_string_chain`, `run_voblint_entry_state_chain` | the semantic spine above, per context policy |

[`THEOREM_MAP.md`](THEOREM_MAP.md) gives each statement with its premises.

```text
                  source
                    |  unverified parser
                    v
          imp_prog, kind_decls
                    |  run_voblint                verified semantic contract
                    v
                 report
                    |  render_report             deliberately unverified projection
                    v
         'v run_result (strings)
                    |  unverified presentation
                    v
         graph / DOT / HTML / JSON
```

The soundness contract (`report_sound`) does not speak about `report_routes`,
`report_globals` or the per-row lists: it does not state that context indices are in
range, that routes sit at call edges or that seeds name entered contexts.

## What the theorem does not cover

The theorem is about the semantics of the `imp_prog` Isabelle received. It does not
cover:

- **parser correctness**: source text to `imp_prog`
- **`string_of_report_value` and `prog_render_report`**: abstract value to text, report
  to displayed rows
- **presentation correctness**: OCaml cannot alter the verified payload, but a bug
  can misattribute it (for example a state shown at the wrong node)
- **termination**: where the solve does not return, there is no answer and no claim

## One dispatcher

`report_run` (`Run_Report.thy`) is the one function that reads the context policy:
`Call_String k` goes to `cs_run`, `Entry_State` to `es_run`. Each of these reads the
program-globals placement and picks one of four registrations of the combined
state `mcp_st` (`MCP_Carrier.thy`): `mcp_cs` and `mcp_es` (`MCP.thy`) for
flow-sensitive program globals, `mcp_split` and `mcp_split_es` (`MCP_Split.thy`)
for flow-insensitive ones. Each branch solves its registration's equations with
`TD_side_rule_Interp_solve_c` and builds the report with `prog_report_of` from the
`solved_run_of` that answer gives. The activation list, the update rule and the
call-string bound are parameters, so no combination has an instance of its own.
`report_run_sound` is the one proof that splits on context policy and placement.

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
(`Key_Int | Key_Node | Key_List`). `report_of` lists contexts with `ordered_by_key`:
call strings by `Key_List (map Key_Node ...)` (unit contexts are call strings of
bound `0`), entry-state contexts by `mcp_ctx_key` (`Run_Report.thy`), which lists
each active field's formal values and is injective (`inj_mcp_ctx_key`).
