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

```text
analyse_program : analysis_domain => globals_rule => context_mode => imp_prog
               => abstract_value analysis_answer            (typed, verified)

run_voblint     = map_analysis_answer show_abstract_value o analyse_program
                                                             (exported, display only)
```

`map_analysis_result` is an explicit definition rather than a derived BNF map (plain
`record`s are not BNFs), so the boundary itself spells out what presentation may
transform: every occurrence of domain data -- state values, global values and the
abstract values inside entry-state contexts -- and nothing else. Context identity
stays a `nat`; OCaml never infers identity from displayed text.

## Result shape (records, not tuples, at the permanent boundary)

```text
record 'a analysis_result =
  res_cfg         :: cfg
  res_contexts    :: "'a analysis_context list"   index = identity and order
  res_states      :: "'a result_state list"
  res_routes      :: "call_route list"
  res_checks      :: "result_check list"
  res_globals     :: "'a result_global list"
  res_diagnostics :: "arithmetic_diagnostic list"

datatype 'a analysis_context =
  Unit_Context | Entry_Context "'a list" | Call_String_Context "pp list"

record 'a result_state   = state_point :: pp, state_context :: nat,
                           state_value :: "(vname * 'a) list lifted"   (Bot = unreachable)
                           state_checks :: "(exp * contextual_verdict) list"
                           state_diagnostics :: "(arithmetic_obligation * contextual_verdict) list"
record call_route        = route_point :: pp, route_context :: nat,
                           route_callee :: pname, route_targets :: "nat list"
                           ([] = no callee context entered; several = overlapping
                            enter alternatives)
record result_check      = check_point :: pp, check_exp :: exp,
                           check_verdict :: contextual_verdict
record 'a result_global  = global_key :: result_global_key,
                           global_state :: "(vname * 'a) list lifted"
datatype result_global_key = Global_Shared | Global_Seed pname "nat option"
                           (None = a procedure no solved context enters)
datatype arithmetic_diagnostic = Arithmetic_Diagnostic (diagnostic_point :: pp)
                           (diagnostic_occurrence :: nat)
                           (diagnostic_obligation :: arithmetic_obligation)
                           (diagnostic_verdict :: check_result)
```

Checks and diagnostics come twice, and both are load-bearing: `res_checks` and
`res_diagnostics` join every context of a point, which is what a source-level
report states; `state_checks` and `state_diagnostics` keep each context's own
verdict, which is what a drawing of one context shows. A diagnostic reaches
OCaml as its operation and verdict; the sentence a reader sees is written there.

## Public contract

```text
definition sound_analysis_result_at where
  sound_analysis_result_at p res v s <->
       result_wf res
    /\ res_cfg res = prog_cfg p
    /\ routes_sound p res
    /\ states_cover res v s
    /\ globals_cover res s
    /\ checks_sound_at res v s
    /\ diagnostics_safe_at res v s

theorem analyse_program_sound:
  assumes "analyse_program D r c p = Analysed res"
      and "config_terminates D r c p"
      and "s : ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v"
  shows "sound_analysis_result_at p res v s"
```

Proved from component lemmas (`analyse_program_wf`, `..._routes_sound`,
`..._states_cover`, `..._globals_cover`, `..._checks_sound`,
`..._diagnostics_safe`), so one field changing touches one proof.

`show` is not trusted for semantic soundness, so the displayed result carries no
`γ`-claim of its own. Its theorem is existential:

```text
theorem run_voblint_sound:
  assumes "run_voblint D r c p = Analysed shown"
      and "config_terminates D r c p"
  shows "EX res. analyse_program D r c p = Analysed res
               /\ shown = map_analysis_result show_abstract_value res
               /\ (ALL v s. s : ltr_collect ... v --> sound_analysis_result_at p res v s)"
```

Structural conjuncts (`result_wf`, `res_cfg`, routes, checks, diagnostics) are
preserved by `map_analysis_result` and hold of `shown` directly.

```text
                  source
                    |  unverified parser
                    v
                 imp_prog
                    |  analyse_program            verified semantic contract
                    v
    abstract_value analysis_result
                    |  map_analysis_result show   deliberately unverified
                    v
    String.literal analysis_result                run_voblint
                    |  unverified presentation
                    v
         graph / DOT / HTML / JSON
```

| Conjunct | Meaning |
| --- | --- |
| `result_wf` | every context id in states, routes and targets is `< length res_contexts`; `res_contexts` distinct; states unique per `(point, context)`; routes unique per `(point, caller context)`; every route sits at a call edge of `res_cfg` whose callee is `route_callee`; `route_targets` distinct; every state, check and diagnostic point is a node of `res_cfg` |
| `states_cover` | a store collected at `v` is concretized by the state at some context `v` was solved at |
| `globals_cover` | each declared global's value concretizes that global in every collected store |
| `checks_sound_at` | `Proved`/`Refuted` hold of every collected store at the point; `Dead` only where none is collected |
| `diagnostics_safe_at` | **absence** of a diagnostic at `v` implies no collected store at `v` divides by zero; a diagnostic is not claimed to be a real error |
| `routes_sound` | `set (route_targets r)` is exactly the set of callee keys the solved equation system uses for that call and caller context -- the routed `dgs_enter` alternatives **after** context selection, not the raw alternatives; target order is serialization only |

## Enumerating contexts without a presentation key

`result_keys` is a set, and a domain's value type already spends its `ord`
instance on the abstraction order, so there is no linear order to list an
entry-state context set by. Today's code sorts by `ctx_key_of`, a key built from
`string_of_abstract_value`: presentation deciding enumeration, and complete only
if that key is injective (`set_ordered_by_key`), which no domain proves -- two
entry-state contexts that render alike would silently lose a state.

Instead each domain supplies a structural encoding of its values into a
linearly ordered type, separate from `show`, proved injective once. Enumeration
then needs no premise, `states_cover` is unconditional, and `show` stays out of
`analyse_program`. Call-string contexts need nothing: `cfg_node` derives
`linorder`.

## What the theorem does not cover

The theorem is about the semantics of the `imp_prog` Isabelle received. It does not
cover:

- **parser correctness**: source text to `imp_prog`; a parser bug makes Isabelle
  verify a different program than the one the user wrote
- **`show` correctness**: abstract value to text
- **presentation correctness**: structured result to what is displayed; OCaml
  cannot alter the verified payload, but a bug can misattribute it (for example
  a state shown at the wrong node)

## What moves to OCaml

- graph construction: clusters, nodes per `(point, context)`, intra/enter/combine/
  call-to-return edges from `res_cfg` plus `res_routes`, procedure-scope filtering
- printing `exp`, `edge_action`, verdicts, diagnostic kinds, node status, source
  text, and context labels built from `show`n context contents
- DOT, the regression snapshot (new format), HTML node documents, browser JSON,
  report-vs-graph selection

## One dispatcher

`analyse_program` is the only dispatcher. Its `analysis_result` reads one
rule-parametric registration per domain and context policy, which the generator
emits from `manifests/analyses.yaml`: `<d>_rule` and `<d>_es_rule` for `r`,
`<d>_cs_rule` for `k r`. The per-discipline registrations (`sign_join`,
`interval_es_po`, ...) remain in the domain theories for their `*_Checks` and
`*_Entry` consumers; `run_voblint` does not reach them.

## Steps

1. Records and `'a analysis_result`; explicit `map_analysis_result`;
   `show_abstract_value`; injective per-domain context encodings;
   `analyse_program` via one generic builder over any sound table (replacing
   `flat_output_of`, `entry_state_output_of`, `cs_output_of`); list-valued
   routes from the routed enter results.
2. Component lemmas, `sound_analysis_result_at`, `analyse_program_sound`, and
   the existential `run_voblint_sound`.
3. Fold every dispatcher into `analyse_program`; update the generator (done).
4. OCaml `Voblint_api` over `Generated`: grammar-generated `exp`/program printer,
   verdict/status/diagnostic names, `is_dead`.
5. OCaml `Graph` builder from `res_cfg`, `res_states`, `res_routes`, with
   structural tests replacing `build_analysis_graph_wf`.
6. OCaml layout: `cli/frontend` (parser, printer), `cli/result` (`result_text`,
   `context_graph`), `cli/render` (`render_text`, `render_dot`, `render_snapshot`,
   `render_json`, `render_xml`, `report_dir`), `cli/entry` (`voblint`, `voblint_web`),
   entry points reduced to
   argument handling and I/O.
7. Delete the Isabelle presentation layer (done): `Analysis_Graph*`,
   `State_Report_*`, `VIMP_Source_Print`, the old `run_voblint` views,
   `analysis_output` and `check_row`. The endpoint theorems quantify over
   `run_voblint`'s structured result.
8. Regenerate every `EXPECT-GRAPH` oracle in the new format.
9. Select the side-effect update rule with `--globals` (`globals_rule`, done): it
   chooses only how a global unknown is updated; loop heads are always widened and
   narrowed (the `is_point` branch of `TD_side_upd_rule.thy`).
10. Single-route audit over every domain x globals rule x context, including the
    manifest's `legacy:` spellings.
11. Website: introduction, domain/globals/context explainers, globals placement,
    inline editor annotations.
