# `run_voblint`: one verified function, one display wrapper, one public contract

Status: **in progress** on branch `structured-run-voblint` (stacked on PR #190).

## Principle

Isabelle exports the semantic information the soundness contract needs, plus
domain-owned observations of abstract values. Presentation derived from that
information lives outside Isabelle.

Domain knowledge stays with the domain: how `Ivl (Fin 0) (Fin 1)` reads as `[0,1]`
is Interval's business. If OCaml printed it, the renderer would pattern-match every
domain's representation (Congruence is a typedef OCaml cannot look inside) and every
new domain would touch OCaml.

## The boundary

All names below are defined in `src/Executable_Surface/CLI/Analysis_Run.thy`.

```text
analyse_program : analysis_domain => globals_rule => context_mode => imp_prog
               => abstract_value analysis_answer            (typed, verified)

run_voblint     = map_analysis_answer string_of_abstract_value o analyse_program
                                                             (exported, display only)

datatype 'v analysis_answer = Malformed_Program | Analysed "'v run_result"
```

`map_run_result` is an explicit definition rather than a derived BNF map (plain
`record`s are not BNFs), so the boundary itself spells out what presentation may
transform: every occurrence of domain data -- state values, global values and the
abstract values inside entry-state contexts -- and nothing else. Context identity
stays a `nat`; OCaml never infers identity from displayed text.
`map_run_result_structure` records that `res_cfg`, the context count, routes,
checks, diagnostics and the `(point, context)` of every state pass through
unchanged.

## Result shape (records, not tuples, at the permanent boundary)

```text
record 'v run_result =
  res_cfg         :: cfg
  res_contexts    :: "'v analysis_context list"   index = identity and order
  res_states      :: "'v result_state list"
  res_routes      :: "call_route list"
  res_checks      :: "result_check list"
  res_globals     :: "'v result_global list"
  res_diagnostics :: "arithmetic_diagnostic list"

datatype 'v analysis_context =
  Context_Unit | Context_Entry "'v list" | Context_Call_String "pp list"

record 'v result_state   = state_point :: pp, state_context :: nat,
                           state_value :: "(vname * 'v) list lifted"   (Bot = unreachable)
                           state_checks :: "(exp * contextual_verdict) list"
                           state_diagnostics :: "(arithmetic_obligation * contextual_verdict) list"
record call_route        = route_point :: pp, route_context :: nat,
                           route_callee :: pname, route_targets :: "nat list"
                           ([] = no callee context entered; several = overlapping
                            enter alternatives)
record result_check      = check_point :: pp, check_exp :: exp,
                           check_verdict :: contextual_verdict
record 'v result_global  = global_key :: result_global_key,
                           global_state :: "(vname * 'v) list lifted"
datatype result_global_key = Global_Shared | Global_Seed pname "nat option"
                           (None = a procedure no solved context enters)
datatype arithmetic_diagnostic = Arithmetic_Diagnostic (diagnostic_point :: pp)
                           (diagnostic_occurrence :: nat)
                           (diagnostic_obligation :: arithmetic_obligation)
                           (diagnostic_verdict :: check_result)
```

`contextual_verdict` is `check_result lifted`, with `Dead = Bot` and
`Decided r = Lifted r` (`Contextual_Check_Report.thy`). `arithmetic_diagnostic`
lives in `Arithmetic_Diagnostics.thy`.

Checks and diagnostics come twice, and both are load-bearing: `res_checks` and
`res_diagnostics` join every context of a point, which is what a source-level
report states; `state_checks` and `state_diagnostics` keep each context's own
verdict, which is what a drawing of one context shows. A diagnostic reaches
OCaml as its operation and verdict; the sentence a reader sees is written there.

## Public contract

The proved contract lives in `Analysis_Run_Sound.thy` and
`Analysis_Certified.thy`. Both claims are stated for any value type, so the typed
result and its displayed form make the same claim (`map_run_result_sound_at`):

```text
definition checks_sound_at :: "'v run_result => pp => store => bool" where
  checks_sound_at res v s <->
    (ALL chk : set (res_checks res). check_point chk = v -->
         check_verdict chk ~= Dead
      /\ (check_verdict chk = Decided Check_Proved --> truthy (aval (check_exp chk) s))
      /\ (check_verdict chk = Decided Check_Refuted --> ~ truthy (aval (check_exp chk) s)))

definition diagnostics_sound_at :: "'v run_result => imp_prog => pp => store => bool" where
  diagnostics_sound_at res p v s <->
    ((ALL d : set (res_diagnostics res). diagnostic_point d ~= v)
       --> arithmetic_safe_at (prog_cfg p) v s)

lemma run_voblint_sound_at:
  assumes "config_terminates D rule ctx p"
      and "run_voblint D rule ctx p = Analysed res"
      and "s : ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v"
  shows "analysis_result_covers D rule ctx p v s
         /\ checks_sound_at res v s /\ diagnostics_sound_at res p v s"
```

`analysis_result_covers` is `table_covers` of the table the configuration's
registration solved: the store lies in the entry filed at `v` under some context.
Each configuration discharges the `sound_table` locale (finitely many contexts
per point, coverage, classifier soundness in both directions) through its
`<d>_rule_table`, `<d>_es_rule_table` or `<d>_cs_rule_table` lemma, and
`analysis_result_sound` does the case split once. Well-formedness is not a
premise: `run_voblint` answers `Analysed` only for a program that passes
`wf_program_compile_input_exec`.

The endpoints built on it, all in `Analysis_Certified.thy`:

| Theorem | Claim |
| --- | --- |
| `run_voblint_certified_source_sound` | a source run stopped anywhere sits at a node (`csim`) whose collected store the table covers and whose listed checks hold |
| `run_voblint_check_sound` | a run about to execute `Check e` finds a listed check for `e` at a node it reaches, and its verdict holds |
| `run_voblint_dead_check_unreached` | a `Dead` check's point collects no store |
| `run_voblint_arithmetic_safe`, `run_voblint_arithmetic_intra_safe` | no diagnostic at `v` means no collected store at `v` divides by zero |
| `run_voblint_check_sites` | `res_checks` lists one check per compiled `EA_Check` edge, in graph order |

```text
                  source
                    |  unverified parser
                    v
                 imp_prog
                    |  analyse_program                          verified semantic contract
                    v
    abstract_value run_result
                    |  map_run_result string_of_abstract_value  deliberately unverified
                    v
    String.literal run_result                                   run_voblint
                    |  unverified presentation
                    v
         graph / DOT / HTML / JSON
```

The contract does not yet speak about `res_states`, `res_routes` or
`res_globals`. These conjuncts are planned and not stated:

| Conjunct | Meaning |
| --- | --- |
| `result_wf` | every context id in states, routes and targets is `< length res_contexts`; `res_contexts` distinct; states unique per `(point, context)`; routes unique per `(point, caller context)`; every route sits at a call edge of `res_cfg` whose callee is `route_callee`; `route_targets` distinct; every state, check and diagnostic point is a node of `res_cfg` |
| `states_cover` | a store collected at `v` is concretized by the `res_states` entry at some context `v` was solved at |
| `globals_cover` | each `res_globals` entry concretizes the global unknown its key names |
| `routes_sound` | `set (route_targets r)` is exactly the set of callee keys the solved equation system uses for that call and caller context -- the routed `dgs_enter` alternatives **after** context selection, not the raw alternatives; target order is serialization only |

`analysis_result_covers` states coverage of the solver's table; `states_cover`
is the step from that table to the `res_states` list OCaml reads.

## Enumerating contexts without a presentation key

`result_keys` is a set, and a domain's value type already spends its `ord`
instance on the abstraction order, so there is no linear order to list an
entry-state context set by. `Dispatch_Carrier.thy` supplies a structural
encoding instead: `order_key` (`Key_Int | Key_Node | Key_List`) derives
`linorder`, and `abstract_value_key` maps every abstract value into it, proved
injective once (`inj_abstract_value_key`). `run_result_of` lists contexts with
`ordered_by_key`: unit contexts by `Key_List []`, entry-state contexts by
`Key_List` of their values' keys, call strings by `Key_List (map Key_Node ...)`.
`string_of_abstract_value` stays out of enumeration and out of
`analyse_program`. No lemma yet states that `ordered_by_key` lists every
context of an injectively keyed set; `states_cover` needs it.

## What the theorem does not cover

The theorem is about the semantics of the `imp_prog` Isabelle received. It does not
cover:

- **parser correctness**: source text to `imp_prog`; a parser bug makes Isabelle
  verify a different program than the one the user wrote
- **`string_of_abstract_value` correctness**: abstract value to text
- **presentation correctness**: structured result to what is displayed; OCaml
  cannot alter the verified payload, but a bug can misattribute it (for example
  a state shown at the wrong node)

## What moves to OCaml

- graph construction (`cli/result/context_graph.ml`): clusters per
  `(procedure, context)`, nodes per `(point, context)`, intra/enter/combine/
  call-to-return edges from `res_cfg` plus `res_routes`, procedure-scope filtering
- printing (`cli/result/result_text.ml`, generated `cli/frontend/vimp_printer.ml`):
  `exp`, `edge_action`, verdicts, diagnostic messages, global rows, and context
  labels built from rendered context contents
- rendering (`cli/render/`): text report, DOT, the regression snapshot, HTML node
  documents and report directory, browser JSON

## One dispatcher

`analyse_program` is the only dispatcher. Its `analysis_result` reads one
rule-parametric registration per domain and context policy, which
`scripts/gen_analysis_assembly.py` emits from `manifests/analyses.yaml`:
`<d>_rule` and `<d>_es_rule` for `r`, `<d>_cs_rule` for `k r`, each read through
its `result_with_globals`. These are the only registrations a domain carries:
the rule is a parameter, so no discipline has an instance of its own.

## Steps

1. Records and `'v run_result`; explicit `map_run_result`;
   `string_of_abstract_value`; injective context encodings (`order_key`,
   `abstract_value_key`); `analyse_program` via the one builder `run_result_of`;
   list-valued routes from `entered_targets` (done).
2. Soundness over `run_voblint`'s result. Done: `checks_sound_at`,
   `diagnostics_sound_at`, `run_voblint_sound_at` and the endpoints above.
   Remaining: `result_wf`, `states_cover`, `globals_cover`, `routes_sound`, and
   the completeness lemma for `ordered_by_key`.
3. Fold every dispatcher into `analyse_program`; update the generator (done).
4. OCaml access over `Generated`: grammar-generated `exp`/program printer
   (`Vimp_printer`), verdict/diagnostic names (`Result_text`), node status and
   `is_dead` (`Context_graph`, `Render_xml`) (done).
5. OCaml graph builder `Context_graph` from `res_cfg`, `res_states`,
   `res_routes` (done). Remaining: structural tests of the builder; the
   `.vimp` regression fixtures (`EXPECT-GRAPH` snapshots, DOT output) are its
   only check.
6. OCaml layout: `cli/frontend` (parser, printer), `cli/result` (`result_text`,
   `context_graph`, `value_symbols`), `cli/render` (`render_text`, `render_dot`,
   `render_snapshot`, `render_json`, `render_xml`, `report_dir`), `cli/entry`
   (`voblint`, `voblint_web`) (done). Remaining: entry points reduced to
   argument handling and I/O; `cli/entry/voblint.ml` still assembles the HTML
   report's check and diagnostic rows.
7. Delete the Isabelle presentation layer (done). The endpoint theorems quantify
   over `run_voblint`'s structured result.
8. Regenerate every `EXPECT-GRAPH` oracle in the snapshot format (done).
9. Select the side-effect update rule with `--globals` (`globals_rule`, done): it
   chooses only how a global unknown is updated; loop heads are always widened and
   narrowed (the `is_point` branch of `TD_side_upd_rule.thy`).
10. Single-route audit over every domain x globals rule x context.
11. Website: introduction, domain/globals/context explainers, globals placement,
    inline editor annotations.
