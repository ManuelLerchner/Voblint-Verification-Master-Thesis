# Verification chain and trust boundary

The reference map from concrete VIMP semantics through the proved abstract
analyzer to the generated OCaml CLI: what is proved, what is inherited from
Isabelle's code-generation infrastructure, and what is unverified adapter code.
`docs/THEOREM_MAP.md` lists the checked statements; this page says where each
one sits in the chain.

## Architecture

```text
 VIMP AST (imp_prog)
   |  wf_program_compile_input_exec p          gate inside run_voblint
   v
 compile_prog -> procedure-aware CFG           Voblint_Compile (forward simulation)
   v
 D/G equation system (routed_node_rhs)         Voblint_Framework
   v
 vendored TD solver, solve_c                   TD_side_upd_rule (vendor/td-verification)
   v
 solved table, classified check rows           Voblint_Result, Voblint_CLI
   |  export_code ... module_name Generated    Voblint_Codegen
   v
 codegen/generated/ml/Voblint_CLI.ml
   |  hand-written OCaml, outside the proof
   v
 cli/entry/voblint.ml -> lexer/parser -> Generated.run_voblint -> render_report -> output
```

## 1. Abstract transfer soundness

A domain proves one fact per operation and interprets `sound_transfer_for`
(`DG_Local_State_Spec.thy`) once: the non-relational domains through
`is_sound_transfer_for` (`Nonrelational_Transfer.thy`), the `int_dom` product
through `int_is_sound_transfer_for` (`Int_Transfer.thy`).
`local_state_dg_spec_for_core_sound` turns that into `sound_dg_spec_core` for
the whole-state specification every shipped domain uses.

Guards go through `branch_lifted` (`Backward_Domain.thy`): a forward feasibility
gate ahead of backward narrowing by `bfilter`, with a definite contradiction
denoting `Bot`. `branch_sound` holds either way; the gate is a precision change
(`docs/GOBLINT_ALIGNMENT_REGISTER.md`, "Branch transfer").

## 2. Two representations

The mathematical layer works over `'a abs_state = vname => 'a`
(`Nonrelational_State.thy`), a function over an infinite domain with no finite
representation. The executable layer works over `'a resolved_st_q`
(`Exec_St_Base.thy`), a `quotient_type` of a default-value-plus-finite-override
encoding, quotiented by observable lookup so that `=`, `<=` and `bot` are
well-defined.

The link is a total function, `fun_of_resolved_st_q_for gs`
(`Exec_St_Transfer.thy`), which reads each name at the location the classifier
`gs` selects. It is not injective: a quotient value carries both a local and a
global location per name and the conversion reads one. That is why
`resolved_st_is_bot` filters through `canonical_location`
(`Exec_St_Reachability.thy`).

## 3. Commute theorems

Every executable operation commutes with its abstract counterpart through that
conversion. `afilter_st`, `bfilter_st` and `branch_st` with `branch_st_commute`
are proved once for every `backward_domain` (`Exec_Backward.thy`). The per-edge
transfer is `generic_tf_st_for_commute` (`Numeric_Ops.thy`), instantiated per
domain (`sign_tf_st_for_commute` in `Sign_Exec.thy`,
`congruence_tf_st_for_commute` in `Congruence_Exec.thy`, `int_dom`'s three
refinement modes as `int_tf_st_never_for_commute`/`_once_`/`_fixpoint_`, ...).

## 4. Solver

`Voblint_Solver` depends on the externally authored, vendored session `TD`.
The locale `TD_side_upd_rule` (`vendor/td-verification/TD_side_upd_rule.thy:18`)
fixes two constants:

- `solve`, the non-executable specification, sound by `partial_post_solution`
  (`:1787`);
- `solve_c`, the terminating, code-generated version.

`term_equivalence` (`:2362`) and `value_equivalence` (`:2370`) prove the two
agree on `solve`'s domain, and `solve_code_equation [code]` (`:2387`) installs
`solve_c` as `solve`'s code equation, so the equality between them is proved.
`part_post_solution_of_solve_c` (`TD_Solver_Bridge.thy`) turns a successful
`solve_c` into the vendored certificate `part_post_solution`
(`Basics_side.thy`). That certificate is solver-independent:
`activation_collect_dg_sound` (`Routed_Context.thy`) proves collecting
soundness from any valuation satisfying it, without asking how it was computed.

The four update rules of `globals_rule` (always-join, per-origin, Apinis
warrowing, warrowing-per-origin) are vendored rules, selected through one
`TD_side_rule_Interp` interpretation (`Globals_Rule.thy`), and widening is a type-class
instance of the vendored `widening` class, so there is no refinement gap at the
solver layer beyond ordinary code-generation trust.

## 5. Soundness endpoints

The chain ends at `run_voblint_certified_source_sound` (`Analysis_Certified.thy`):
for every domain, global update rule and context policy, a source run's
store lies in the analysis result at a genuinely reachable node, and every
definite verdict listed there holds for that store.
`run_voblint_dead_check_unreached`, beside it, states separately that a dead check's
point is unreachable, at every configuration. The caller owes `config_terminates D rule ctx p` -- the
solver run completed -- and nothing proves that in general; it is established per
program by evaluation. That the run solved enough keys is no premise:
`live_keys_cover` (`Routed_Live_Keys.thy`) proves it from termination. The
root `README.md` states the theorem in full.

## 6. `export_code` and the code-generation trust boundary

One `export_code` declaration (`Voblint_Codegen.thy`) targets OCaml with
`module_name Generated file_prefix "Voblint_CLI"`, landing at
`codegen/generated/ml/Voblint_CLI.ml`. Its operation is `run_voblint`; the other
roots are the constructors and selectors a caller needs to build a program, ask
for a configuration and read the answer. All five domains, the four global
update rules and the three context modes are reachable through `run_voblint`.
`codegen-regression` and `cli-build` compile and link the output through Dune.

No `code_printing`, `code_datatype`, `code_reserved` or `code_abbrev` appears in
`src/`. HOL-Library's own target mappings still apply, and they are what makes the
exported integers Zarith's `Z.t`: `Code_Target_Numeral` and `Code_Abstract_Char`
are imported by `Analysis_Run.thy`. The `[code]` attributes that do appear sit on proved lemmas or on a
definition's own equations, and `[code_unfold]` rewrites named `dg_spec`
definitions away before serialization.

What a successful `export_code` establishes rests on Isabelle's code-generation
metatheory, trusted and not re-proved here: the emitted OCaml is computationally
faithful to the exported functions' code equations. It says nothing about what
those functions mean -- that is the chain in sections 1 to 5 -- and nothing
about code that is not an exported constant.

## 7. Parser and hand-written CLI

The lexer and parser (`cli/frontend/vimp_lexer.mll`, `cli/frontend/vimp_parser.mly`, generated
from `manifests/vimp-grammar.yaml`) carry no soundness theorem; the proved chain starts at
an already-constructed `imp_prog`. `cli/entry/voblint.ml` calls `Generated.run_voblint`
and reads its answer through the exported selectors. A malformed program answers
`Malformed_Program`, which the CLI reports with exit code 4.

Zarith, the OCaml and `wasm_of_ocaml` toolchains and the browser are trusted the same
way, and so is the hand-written OCaml between `Generated.run_voblint` and the output:
`cli/entry/voblint.ml`, `cli/entry/voblint_web.ml`, `cli/render/` and `cli/result/`.

A row's verdict is a `contextual_verdict = check_result lifted`
(`Contextual_Check_Report.thy`) computed in HOL; `Bot` is the dead marker, and
`cli/entry/voblint.ml` only matches on it. Rendering -- text layout, the GraphViz graph,
the snapshot and globals strings -- is presentation with no theorem about it.

## 8. What may be claimed

Proved, for every configuration `run_voblint` answers (every domain, rule and
context policy, `docs/THEOREM_MAP.md`):
if `config_terminates` holds for the program, every modeled source
execution is over-approximated at a reachable node, and every `PROVED` or
`REFUTED` row printed there is correct for that execution.

Not proved:

- solver termination for an arbitrary program (key coverage is checked at run
  time rather than proved);
- anything about the rendered graph, snapshot or globals strings;
- the lexer and parser;
- Isabelle's code generator, the OCaml compiler and its runtime.

## Adding an executable analysis

"One generator, six layers" in `src/Abstract_Interpreter/Framework/README.md` is
the procedure and
`docs/ANALYSIS_ASSEMBLY_GENERATION.md` the registration format. Re-run the full
batch build (`docs/ISABELLE_AGENT_NOTES.md`) and `pixi run codegen` before
claiming the new analysis is connected end to end.
