# Verification chain and trust boundary

The reference map from the parsed VIMP program through the proved abstract
analyzer to the generated OCaml CLI: what is proved, what is inherited from
Isabelle's code-generation infrastructure, and what is unverified adapter code.
`docs/THEOREM_MAP.md` lists the checked statements; this page says where each
one sits in the chain.

## Architecture

```text
 OCaml lexer, parser, scope resolution, kind declarations      trusted
   v
 surface VIMP (imp_prog over src_exp/src_com) + kind_decls ds
   |  wf_program_compile_input_exec p          gate inside run_voblint
   |  elaborate / elab_com / elab_ptable       Voblint_VIMP (definitions)
   v
 core VIMP (exp/com over var_id), pstep        Voblint_VIMP
   |  elab_cfg = compile_prog (elab_ptable p ds) Voblint_Compile (forward simulation)
   v
 procedure-aware CFG, cstep, valid_activation_trace,
 activation_collect, node_collect               Voblint_CFG
   v
 D/G equation system over the analyses' combined state
                                               Voblint_Framework, Voblint_Result, Voblint_CLI
   v
 vendored TD solver, solve_c                   TD_side_upd_rule (vendor/td-verification)
   v
 report: states, checks, diagnostics           Voblint_CLI (Run_Report, Run_Voblint)
   |  export_code ... module_name Generated    Voblint_Codegen
   v
 codegen/generated/ml/Voblint_Generated.ml
   |  hand-written OCaml, outside the proof
   v
 cli/entry/voblint_main.ml -> Voblint.run_voblint -> cli/render -> output
```

## 0. The language and what a surface program means

The parser builds a surface VIMP program (`imp_prog`, expressions `src_exp`,
commands `src_com`) together with kind declarations `ds :: kind_decls`, which give
each variable identity (`var_id`) a machine-integer kind (`ikind`). The parser
rejects a program that leaves a global, formal or local undeclared, so every
identity the program names has a declaration; `kenv_of ds` still totalizes the
list by giving any other identity `I32`. Elaboration (`elaborate` in
`Core_Exp.thy`, `elab_com` in `Core_Com.thy`, `elab_ptable` in
`VIMP_Semantics.thy`) resolves names to identities and makes every implicit
conversion and the kind of every operation explicit, producing core VIMP (`exp`,
`com`). `eval` (`Core_Exp.thy`) evaluates a core expression, and `kind_conv`
converts a value written to a variable to that variable's kind. The canonical
small-step relation is `pstep` (`VIMP_Semantics.thy`), which evaluates with
`eval` and converts every write with `kind_conv`; runs start from
`init_stores`, where globals are zero at their kinds.

Surface VIMP has no step relation of its own. A surface program means the core
semantics of its elaboration. `eval_elaborate` relates `eval` of an elaborated
expression to `src_eval`, a reading of the surface expression in the shape of
the C standard's arithmetic conversions, but whether elaboration, `eval`,
`kind_conv`, `pstep` and the well-formedness conditions model the intended C
subset is a definitional-adequacy question, argued and not proved. Everything in
`Voblint_VIMP` is in that argument.

`wf_program_compile_input_exec` (`Compile_Invariants.thy`), checked inside
`run_voblint`, rejects among others a program with a literal outside `I64`
(`lits_fit`).

## 1. Abstract transfer soundness

What a component owes is `sound_local_spec` (`MCP_Spec.thy`): every
transfer of a `local_spec` over-approximates the corresponding concrete step
(`edge_collect`, `call_enter`, `combine_collect`) under the component's
concretization. The non-relational
component is generic in its value domain, any instance of the class
`kind_int_domain` (`Nonrelational_Domain.thy`). `nonrel_spec_sound`
(`Nonrelational_Transfer.thy`) proves `nonrel_spec` sound over the function
states `'a tabs = var_id => 'a kd`, and `nonrel_exec_spec_sound`
(`Nonrelational_Exec.thy`) proves the executable component `nonrel_exec_spec`
sound over the dictionary carrier. Sign, Interval, Parity and Congruence
instantiate `kind_int_domain` in their `*_Kind` theories; Int is the reduced
product `int_tuple` of Interval and Congruence (`Int_Tuple_Kind.thy`), one
instance per refinement mode. The relational Order component is proved sound by
`ord_spec_sound` (`Order_Analysis.thy`).

The analyses a caller activates run as one component through the registry
`mcp_registry` (`MCP_Registry.thy`), interpreted as `mcp` in
`MCP_Carrier.thy`: each analysis owns one field of `mcp_st`, `field_sound`
lifts each field's soundness, and `mcp_comp_sound` composes them.
`dg_analysis_whole_stateI` and, for flow-insensitive program globals,
`dg_analysis_keyedI` (`DG_Analysis.thy`) turn a sound component and its side
conditions into a `dg_analysis` registration; `mcp_cs_routed` (`MCP.thy`) and
`mcp_cs_keyed` (`MCP_Split.thy`) are the CLI's. Under flow-insensitive program
globals the state is wrapped in the keyed lifter `keyed_split_spec`, one
global unknown per declared global, whose contract is `keyed_split_contract`
(`DG_Keyed_Split_Spec.thy`).

Guards go through `nonrel_branch` (`Nonrelational_Transfer.thy`): a forward
truth test of the guard ahead of backward refinement by `nonrel_refine`, with a
definite contradiction denoting bottom. `nonrel_branch_sound` holds either way;
the gate is a precision choice (`docs/GOBLINT_ALIGNMENT_REGISTER.md`, "Branch
transfer").

## 2. Two representations

The proof-level non-relational state is `'a tabs = var_id => 'a kd`
(`Nonrelational_Domain.thy`), a function over an infinite domain with no finite
representation. The executable state is `'a tst = (var_id, 'a kd) gdefault_st`
(`Nonrelational_Exec.thy` over `Default_St_Base.thy`), a `quotient_type` over one
default dictionary (a default plus finitely many entries) per partition,
quotiented by observable lookup so that `=`, `<=` and `bot` are well-defined.

The link is a total function, `default_st_to_fun is_global`
(`Default_St_Transfer.thy`, abbreviated `nonrel_rd`), which reads each identity
at the location the classifier `is_global` selects. It is not injective: a
quotient value carries a local and a global dictionary, each able to answer for
every identity, and the conversion reads one per identity. That is why
`st_rep_is_bot` (`Nonrelational_Exec.thy`) consults `is_global` for each
dictionary entry.

## 3. Commute theorems

Every executable operation agrees with its function-level counterpart through
that conversion: `nonrel_rd_assign_st`, `nonrel_rd_special_st`,
`nonrel_rd_branch_st`, `nonrel_rd_return_st`, `nonrel_rd_enter_st` and
`nonrel_rd_combine_assign_st` (`Nonrelational_Exec.thy`), and
`nonrel_rd_init_st` for the initial state (`Nonrelational_Analysis.thy`). They
are stated once for every `kind_int_domain`, so each domain inherits them by
instantiation; `nonrel_exec_spec_sound` uses them to carry `nonrel_spec_sound`
to the carrier.

## 4. Solver

`Voblint_Solver` depends on the externally authored, vendored session `TD`.
The locale `TD_side_upd_rule` (`vendor/td-verification/TD_side_upd_rule.thy:18`)
fixes two constants:

- `solve`, the non-executable specification, sound by `partial_post_solution`
  (`:1787`);
- `solve_c`, the option-valued version that is code-generated; executing it
  outside `solve`'s domain does not return.

`term_equivalence` (`:2362`) and `value_equivalence` (`:2370`) prove the two
agree on `solve`'s domain, and `solve_code_equation [code]` (`:2387`) installs
`solve_c` as `solve`'s code equation. `solve_dom_of_solve_c` (`:2406`) turns a
successful `solve_c` into `solve_dom`. The locale `certified_solver`
(`TD_Solver_Bridge.thy`) states the four facts the pipeline uses (partial
post-solution, finite solved key set, domain of a `solve_c` answer, and that
answer being the solve) as one solver contract; `dg_analysis` extends it, and
every registration discharges it with `td_certified_solver` (`Globals_Rule.thy`),
proved once for every `globals_rule`. The certificate is solver-independent:
`activation_collect_dg_sound` (`Routed_Context.thy`) proves collecting
soundness from any valuation satisfying it, without asking how it was computed.

The five update rules of `globals_rule` (`Globals_Join`, `Globals_Per_Origin`,
`Globals_Warrow`, `Globals_Warrow_Per_Origin`, `Globals_Bounded_Narrowing`) are
vendored rules, selected through one `TD_side_rule_Interp` interpretation
(`Globals_Rule.thy`). The first four run on the contribution part of the
bounded-narrowing rule's update state (`lift_basic_rule`, proved to keep the
update-rule interface), and widening is a type-class instance of the vendored
`widening` class, so there is no refinement gap at the solver layer beyond
ordinary code-generation trust.

## 5. Soundness endpoints

The public theorems are about `run_voblint` itself (`Run_Voblint.thy`) and
hold for every configuration: every activation list, update rule, context
policy, placement of program globals and signed-overflow policy. Their stores
are `reaching ds p v`, the stores `node_collect` collects at node `v` of
`elab_cfg p ds` from `init_stores`.

- `run_voblint_sound`: if `run_voblint conf ds p = Analysed res`, every store
  reaching `v` lies in the concretization of some state the report lists at `v`,
  a `PROVED` check holds at it and a `REFUTED` check fails at it.
- `run_voblint_report_sound` restates this through `PROVED`, `REFUTED`, `DEAD`
  and `SAFE`; `run_voblint_dead_unreached` concludes `reaching ds p v = {}` for a
  dead point.
- `run_voblint_arithmetic_safe` (with `_intra`, `_call` and `_return` parts),
  `run_voblint_no_signed_overflow`, `run_voblint_no_remainder_overflow` and
  `run_voblint_no_conversion_overflow`: at a point no diagnostic names, no
  divisor is zero, no signed operation leaves its kind, no signed remainder has
  a quotient outside its kind and no narrowing conversion changes its value, at
  every reaching store. `run_voblint_arithmetic_refuted`: a refuted diagnostic's obligation
  fails at every reaching store.
- `run_voblint_source_sound`: a `pstep` run of `elab_ptable p ds` from
  `init_stores` is simulated at some node `v` of `elab_cfg p ds`, its store
  reaches `v`, `v` is not dead, and every decided verdict at `v` holds of the
  store. `run_voblint_check_sound` and `run_voblint_labelled_check_sound` read
  this at a `Check l e` about to execute.
- `run_voblint_spine`, `run_voblint_call_string_chain` and
  `run_voblint_entry_state_chain` expose the intermediate layers: the
  activation trace, its context, and the context-indexed `activation_collect`
  whose union over contexts is `reaching ds p v`.

The bridge from source runs to the graph is `source_reaches_node_collect`
(`Source_To_Trace.thy`), the forward simulation at the elaborated program. The caller owes nothing about termination: `run_voblint` solves
with the executable `solve_c`, and an analysed answer exists only where it
returned (`solve_c_run`, `DG_Analysis.thy`). Nothing proves the solve returns
in general. That the run solved enough keys is no premise either:
`live_unknowns_cover` (`DG_Live_Unknowns.thy`) proves it from termination.

### Arithmetic obligations compared with C

`SAFE` at a point means every obligation `obligations_at` lists there holds for every
covered execution (`run_voblint_SAFE`). The obligations are defined in `Run_Report.thy`
(`arith_obligations`, `return_sites`, `special_sites`); they are a deliberate policy,
not a model of C's undefined behaviour:

| Operation | Obligation | C (ISO/IEC 9899) |
| --- | --- | --- |
| `/`, `%` with divisor 0 | raised | undefined (6.5.5p5) |
| signed `+`, `-`, `*`, `/` outside the kind | raised (`-x` is `0 - x`; `/` only for minimum / -1) | undefined (6.5p5) |
| signed `%` whose truncated quotient does not fit (`INT_MIN % -1`) | raised, although the remainder 0 fits | undefined, because the quotient does not fit (6.5.5p6) |
| unsigned arithmetic | not raised: wraps by definition | defined wraparound (6.2.5p9) |
| conversion to an unsigned kind that does not fit | raised | defined wraparound (6.3.1.3p2) |
| conversion to a signed kind that does not fit | raised | implementation-defined (6.3.1.3p3) |
| conversion that widens into its target | not raised | value preserved |
| `min`/`max` arguments of different kinds | both converted to their common kind (usual arithmetic conversions), each conversion raised as above | the `(a) < (b) ? (a) : (b)` macro converts both operands (6.3.1.8, 6.5.15p5) |
| `min`/`max` result written to a kind that does not hold the arguments' common kind | raised, exactly when the result does not fit (`min(300, 1)` into `u8` holds) | library result converted on assignment (6.3.1.3) |
| `__voblint_nondet_int()` result | not raised: any value of the destination's kind | (declaration without initializer) |
| operands under `&&`, `\|\|` | raised for both operands | second operand evaluated only if needed (6.5.13p4, 6.5.14p4) |

So a warning is not a proof of undefined behaviour, and `SAFE` is stronger than C requires
for conversions and short-circuit operands. The concrete
semantics wraps signed overflow under both `signed_overflow_policy` settings; the policy only
changes how the analysis abstracts a result that may overflow.

## 6. `export_code` and the code-generation trust boundary

One `export_code` declaration (`Voblint_Codegen.thy`) targets OCaml with
`module_name Generated file_prefix "Voblint_Generated"`, landing at
`codegen/generated/ml/Voblint_Generated.ml`. Its operation is `run_voblint`; the
other roots are the constructors and selectors a caller needs to build a
program, ask for a configuration and read the answer. Every analysis (Interval,
Congruence, Int at three refinement modes, Order, Sign, Parity), the five global
update rules, both context policies (`Call_String k`, `Entry_State`), both
placements of program globals and both signed-overflow policies are reachable
through `run_voblint`. `codegen-regression` and `cli-build` compile and link the
output through Dune.

One `code_printing` declaration appears in `src/`: `Trace_Run.thy` maps
`trace_event`, which is `()` in the logic, to the OCaml hook
`Solver_trace_hook.emit`. It is trusted to return, raise nothing and leave the
solver's values alone. No `code_datatype`, `code_reserved` or `code_abbrev`
appears in `src/`. HOL-Library's own target mappings still apply, and they are
what makes the exported integers Zarith's `Z.t`: `Code_Target_Numeral` and
`Code_Abstract_Char` are imported by `Analysis_Run.thy`. The `[code]`
attributes that do appear sit on proved lemmas or on a definition's own
equations.

What a successful `export_code` establishes rests on Isabelle's code-generation
metatheory, trusted and not re-proved here: the emitted OCaml is computationally
faithful to the exported functions' code equations. It says nothing about what
those functions mean (that is the chain in sections 0 to 5) and nothing about
code that is not an exported constant.

## 7. Parser and hand-written CLI

The lexer and parser (`cli/frontend/vimp_lexer.mll`,
`cli/frontend/vimp_parser.mly`, generated from `manifests/vimp-grammar.yaml`)
carry no soundness theorem; the proved chain starts at an already-constructed
`imp_prog` and its `kind_decls`. `cli/frontend/vimp_typing.ml` turns the kinds
written in the source into those declarations and rejects a program with an
undeclared variable or a value-returning procedure without a return kind; that
the declarations are the kinds the source declares is trusted. `cli/entry/voblint_main.ml` calls
`Voblint.run_voblint` and reads its answer through the exported selectors. A
malformed program answers `Malformed_Program`, which the CLI reports with exit
code 4.

Zarith, the OCaml and `wasm_of_ocaml` toolchains and the browser are trusted the
same way, and so is the hand-written OCaml between `Voblint.run_voblint` and the
output: `cli/entry/voblint_main.ml`, `cli/entry/voblint_web.ml`, `cli/render/`,
`cli/result/` and `cli/trace/`.

A check's verdict is a `contextual_verdict = check_result lifted`
(`Contextual_Check_Report.thy`) computed in HOL; `Dead`, an abbreviation of
`Bot`, is the dead marker, and the CLI only matches on it. Rendering (text
layout, JSON, the GraphViz graph, the snapshot and globals strings) is
presentation with no theorem about it.

Each source check carries a label, `Check l e`. Execution ignores it,
compilation copies it onto the check's `EA_Check l e` edge, and every report
check carries it as `check_label`. `run_voblint_check_sound` concludes that a
run about to execute `Check l e` finds a check labelled `l` for `e` whose
verdict holds of its store, and `run_voblint_labelled_check_sound` adds that,
when the labels are distinct, every check labelled `l` is that one. The
renderers check distinctness on the report and fail otherwise, and print each
check at its own label. Two steps stay trusted: the parser writes the line and
column of each check's `__voblint_check` keyword into its label, and the
renderer prints the label it reads.

A local declared without an initializer reaches the proved chain as the library
call `x = __voblint_nondet_int()` at the declaration's position; the parser
performs this rewriting (`cli/frontend/vimp_parser.mly`), and it is trusted.
`pstep_declare` (`VIMP_Semantics.thy`) proves that this call may leave any value
of `x`'s kind in `x` and changes nothing else, and `pstep_declare_forgets` that
its outcomes do not depend on what `x` held before: the `0` a call entry
writes, or an earlier iteration's or activation's value. Since every local is
declared and every path to a use passes its declaration, the value a local
holds on entry is never read. Block scoping is
resolved in the parser (`cli/frontend/vimp_scope.ml`): a declaration that
shadows a name gets a fresh identity `x#2`, `x#3`, ..., and every use names the
innermost declaration in scope. That this resolution follows C's scoping, and
that every use of a local follows its declaration, is trusted; the parser
rejects a use before the declaration or outside its scope, and no theorem
covers it.

Arithmetic diagnostics are placed by position lookup outside the proof.
`run_voblint_arithmetic_safe` is stated at a CFG node; the CLI finds a
diagnostic's source line through the statement positions the parser records in
post-order and `prog_stmt_post_order` (`cli/frontend/vimp_frontend.ml`), and
nothing proves that pairing.

## 8. What may be claimed

Proved, for every configuration `run_voblint` answers (`docs/THEOREM_MAP.md`):
if `run_voblint conf ds p = Analysed res`, every `pstep` execution of the
elaborated program from `init_stores` is simulated at a CFG node whose store the
report over-approximates there; every `PROVED` or `REFUTED` verdict at that node
is correct for the execution; a `DEAD` point is reached by no such execution;
and at a point no arithmetic diagnostic names, no division or remainder by
zero, signed overflow, signed remainder with an out-of-range quotient, or
value-changing narrowing conversion (including a returned value or a `min`/`max`
result written to its destination) occurs in the expressions evaluated there. None of these says that a point is reached.

Argued, not proved (definitional adequacy): that `Voblint_VIMP` (elaboration,
`eval`, kind normalization and implicit conversions, `kind_conv`, declarations,
`pstep`, and the well-formedness conditions) gives a surface program the meaning
of the intended C subset.

Not proved:

- solver termination for an arbitrary program;
- anything about the rendered output (text, JSON, graph, snapshot or globals
  strings);
- the lexer and parser, including the kind declarations, block-scope
  resolution, the rewriting of a declaration without initializer, that each
  check's label is its own source position, and that every use of a local
  follows its declaration;
- the source position printed for an arithmetic diagnostic;
- Isabelle's code generator, the `trace_event` mapping, the OCaml compiler and
  its runtime.

## Adding an executable analysis

"One generator, six layers" in `src/Abstract_Interpreter/Framework/README.md`
describes the layers. A new non-relational domain instantiates
`kind_int_domain` and inherits `nonrel_exec_spec_sound`. Making it selectable
touches the `analysis` datatype (`Analysis_Config.thy`), the combined state
`mcp_st` and the registry proofs that case on `analysis` (`MCP_Carrier.thy`,
`MCP.thy`, `MCP_Split.thy`). Re-run the
full batch build (`docs/ISABELLE_AGENT_NOTES.md`) and `pixi run codegen` before
claiming the new analysis is connected end to end.
