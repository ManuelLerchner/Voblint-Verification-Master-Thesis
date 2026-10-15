# CLI

`Voblint_CLI` is where the analyses meet again. Every analysis session below is
blind to its siblings; `run_voblint` cannot be, so this session is parented on
`Voblint_Analysis_Int` and lists `Voblint_Analysis_Order`, `Voblint_Analysis_Sign`
and `Voblint_Analysis_Parity` (Interval and Congruence arrive through Int).

Anything importing it sees every analysis, so what lives here is only what needs
all of them: the combined state, the run of the activated analyses through the
shared D/G pipeline, the report, and the public theorems about `run_voblint`.

## Vocabulary

| Term | Meaning |
| --- | --- |
| analysis | a constructor of `analysis`: `Interval`, `Congruence`, `Ana_Int m` for each refinement mode `m`, `Order`, `Sign`, `Parity` |
| activation | the `analysis list` a caller activates, as Goblint's `ana.activated`. `valid_activation` asks for a nonempty list naming no analysis twice; any other activation answers `Invalid_Activation`. |
| configuration | a `voblint_conf`: the activation (`conf_analyses`), a `context_policy` (`Call_String k` or `Entry_State`), a `globals_rule`, a `program_globals` placement and the `sem_conf` the domains read (the signed-overflow policy, `Assume_Top` by default or `Assume_Wraparound`) |
| global update rule | how the solver merges a value side-effected into a global unknown (`globals_rule`): joined, joined per origin, warrowed, warrowed per origin, or with bounded narrowing. Local unknowns are warrowed at widening points under every rule. |
| program globals placement | where a program's declared globals live (`program_globals`): flow-sensitively in each point's own state, or flow-insensitively, each at its own global unknown, read only by the edges that mention it (`MCP_Split`) |
| combined state | `mcp_st`: one field per analysis, as in Goblint's MCP; Int has one field per refinement mode |
| report | what `run_voblint` answers (`report`, an instance of `analysis_report`): the configuration, the variables, the elaborated graph, the contexts, one state per covered (point, context), the routes calls take, the check column, the program globals' states and the arithmetic diagnostics |
| check label | the `check_label` a source `Check l e` carries onto its `EA_Check l e` edge and its report row. The parser sets it to the line and column of the check's keyword, so a renderer prints a row at its own label. |
| arithmetic diagnostic | an obligation of an evaluated expression (division by zero, signed overflow, a conversion that may not fit) that the report does not decide safe, with its point |

## What is here

| File | What |
| --- | --- |
| `Analysis_Config.thy` | `analysis`, `context_policy`, `program_globals`, `voblint_conf`, and `reaching ds p v`: the stores that reach a node of `elab_cfg p ds` from `init_stores`, which every public theorem is stated over |
| `MCP_Carrier.thy` | the combined state `mcp_st` and its fields, each analysis on its own field (`field`, `val_gamma`, `answer`), and the `mcp` interpretation of `mcp_registry` over core VIMP |
| `MCP.thy` | `activation_of`, the initial state `mcp_init`, and the pipeline instances `mcp_cs` (call-string contexts) and `mcp_es` (entry-state contexts) of `gdg_analysis`, with `mcp_cs_verdict_sound` and `mcp_es_verdict_sound` |
| `Dispatch_Carrier.thy` | each domain's injective ordering key for listing contexts, and how a field's state is shown |
| `MCP_Split.thy` | the carrier laws that let the combined state split by global name, field by field, and the flow-insensitive instances `mcp_split` and `mcp_split_es` |
| `Arithmetic_Diagnostics.thy` | arithmetic obligations and structured diagnostics, independent of the language |
| `Analysis_Run.thy` | the report rows, `analysis_report`, its builder `report_of` for every context policy, and `analysis_answer` (`Invalid_Activation`, `Malformed_Program`, `No_Answer`, `Analysed`) |
| `Analysis_Render.thy` | the analysis graph and `render_report`, the displayed `run_result` the adapters read; no theorem reads it |
| `Analysis_Report.thy` | what a report claims: `report_states_at`, `PROVED`, `REFUTED`, `UNKNOWN`, `DEAD`, `SAFE` |
| `Run_Report.thy` | the report of a typed run: `arith_obligations`, `obligation_holds` (`s ⊨ ob`), `obligations_at`, `prog_report_of`, `cs_run`, `es_run`, `report_run`, and the soundness of a run's report (`report_sound`, `report_run_sound`, `report_state_sound`, `report_check_sound`) |
| `Run_Voblint.thy` | `run_voblint` and its public theorems |
| `Trace_Run.thy` | the solver trace in the exported code: traced code equations for routing and the runs, the readers a run hands the tracer, and the OCaml mapping of `trace_event` |

`run_voblint conf ds p` answers `Invalid_Activation` for an invalid activation,
`Malformed_Program` when `wf_program_compile_input_exec p` fails, `No_Answer`
when the executable solve returns nothing, and otherwise `Analysed res`.

## The public theorems

All are in `Run_Voblint.thy` and assume only `run_voblint conf ds p = Analysed res`;
termination of the solve is not a premise, because the executable solve answers only
when it has terminated.

| Theorem | Statement |
| --- | --- |
| `run_voblint_sound` | every store in `reaching ds p v` lies in the concretization of a state the report lists at `v`; a proved check holds at every reaching store, a refuted one fails |
| `run_voblint_report_contract` | the activation was valid, the program well formed, and the report records `conf` and `elab_cfg p ds` |
| `run_voblint_report_sound` | the same guarantees read through `PROVED`, `REFUTED`, `DEAD` and `SAFE` |
| `run_voblint_dead_unreached` | a `DEAD` point has no reaching store |
| `run_voblint_arithmetic_safe` | at a point no diagnostic names, every obligation of every expression an edge or call there evaluates holds, and every returned value fits the kind a caller converts it to |
| `run_voblint_arithmetic_refuted` | a refuted diagnostic's obligation fails at every store reaching its point |
| `run_voblint_no_signed_overflow`, `run_voblint_no_conversion_overflow` | the two arithmetic corollaries for signed operations and narrowing conversions |
| `run_voblint_source_sound` | a `pstep` run of `elab_ptable p ds` from `init_stores` is simulated at a node `v` of `elab_cfg p ds`; its store reaches `v`, lies in a reported state, and satisfies every verdict at `v` |
| `run_voblint_check_sound`, `run_voblint_labelled_check_sound` | a run about to execute `Check l e` finds a row for it whose verdict holds of the store; with distinct labels, the row labelled `l` is that row |
| `run_voblint_spine`, `run_voblint_call_string_chain`, `run_voblint_entry_state_chain` | the whole chain through activation traces and `activation_collect`, for any context policy that owes the spine's two facts, and for each shipped policy |

None of the verdicts says that its point is reached. Every statement is about the
core program `elab_ptable p ds`: what a surface program means is the core semantics of
its elaboration, a definition rather than a proved transformation.

## Arithmetic diagnostics

`Run_Report` decides the obligations `arith_obligations` lists for every expression
an edge or call evaluates: division by zero, signed overflow of `+ - * /`, and
conversions to a narrower kind, including a returned value converted to its
destination's kind. `run_voblint_obligations_cover` shows `obligations_at` covers
them all. Obligations under `&&` and `||` are not guarded by short-circuit
evaluation. The concrete semantics wraps every result. On a possible signed overflow
the domains answer the kind's top under `Assume_Top` (the default) and wrap under
`Assume_Wraparound`; the theorems hold under both.

The CLI renders `Check_Refuted` as `error` and `Check_Unknown` as `warning`, with
the containing statement's source position and the domain name. Neither verdict
establishes concrete reachability. `run_voblint_arithmetic_safe` is stated at a CFG
node; pairing a diagnostic with its source position is OCaml outside the proof.

## Nothing here draws a picture

`run_voblint` stops at its structured report. The text report, DOT, graph snapshots
and HTML come from `cli/result/` and `cli/render/`, outside any theory and outside any
soundness claim; graph shape is pinned by the golden fixtures under
`tests/regression/11-graph-snapshot/`.

## Worked example

`voblint --analysis interval --context entry-state FILE.vimp` names no `--globals`, so
`cli/entry/voblint_main.ml` picks `warrow` and calls `Voblint.run_voblint conf
kind_decls prog` with `conf_analyses = [Interval]`, `conf_context = Entry_State` and
`conf_globals = Globals_Warrow`. For a well-formed program and a valid activation,
`report_run` dispatches to `es_run`, which solves `mcp_es.equations` with the
executable solver and builds the report with `prog_report_of`. Its guarantees are
`run_voblint_sound` and `run_voblint_entry_state_chain`. `--globals join` changes only
the rule, and activating more analyses changes only the activation list.
