# Glossary

The source theories are authoritative. File references identify the defining
layer without embedding line numbers that drift.

## Source language

| Term | Meaning | Source |
| --- | --- | --- |
| `com` | Procedural command language: structured commands, calls, explicit returns, and internal restoration commands. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `proc_decl` | Procedure declaration containing formal parameters and a body. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `proc_table` | Partial map from procedure names to declarations. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `frame` | Saved caller store and optional return destination. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `pstep` / `psteps` | Small-step execution over a command, store, and activation-frame stack. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `pcompletes` | Terminating source execution with an empty frame stack. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `source_com` | Syntactic source-command restriction excluding runtime-only commands. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `wf_source_com` | Whole-program-aware command check for declared calls, arity, and reserved-variable exclusion. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `value_providing` | Conservative syntactic predicate: no fall-through or void return and at least one value return. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `wf_source_program` | Source contract for declarations, calls, returns, reserved variables, and a fall-through-only main. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `ret_var` | Reserved internal channel carrying an explicit return value during unwinding. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `enter_state` | Callee store: the caller's globals kept, every other name reset to `0` (formals are bound afterwards). C leaves such locals indeterminate; VIMP defines them, as it defines `/ 0`. | `src/Program_Model/VIMP/VIMP_Globals.thy` |
| `cinit_stores` | Initial stores of a program run: every global `0`, `main`'s locals unconstrained. Constrains only the initial store; callee locals come from `enter_state`. | `src/Program_Model/VIMP/VIMP_Globals.thy` |
| `combine_env` | Restored caller locals combined with callee globals; Goblint's `combine_env`, split from the separate destination write (`combine_assign`). | `src/Program_Model/VIMP/VIMP_Globals.thy` |

## Procedure-aware CFG

| Term | Meaning | Source |
| --- | --- | --- |
| `cfg_node` | `Statement n`, `FunctionEntry p`, or `FunctionResult p`. | `src/Program_Model/CFG/CFG_Def.thy` |
| `edge_action` | Local CFG transfer, including assignments, assumptions, no-op flow, and matching procedure returns. | `src/Program_Model/CFG/CFG_Def.thy` |
| `intra` | Ordinary procedure-local CFG edges. | `src/Program_Model/CFG/CFG_Def.thy` |
| `calls` | Call-site relation containing the call action, callee entry, and continuation. | `src/Program_Model/CFG/CFG_Def.thy` |
| `wf_cfg` | Generic structural well-formedness conditions for a CFG. | `src/Program_Model/CFG/CFG_Def.thy` |
| `compile` | Compiles one source command into local edges and calls over a node interval. | `src/Program_Model/Compile/VIMP_Proc_to_CFG.thy` |
| `compile_proc` | Adds a procedure entry, result boundary, and fall-through return to a compiled body. | `src/Program_Model/Compile/VIMP_Proc_to_CFG.thy` |
| `compile_prog` | Compiles the procedure table and distinguished main command into one CFG. | `src/Program_Model/Compile/VIMP_Proc_to_CFG.thy` |
| `wf_compile_input` | Canonical static contract for accepted source programs. | `src/Program_Model/Compile/Compile_Invariants.thy` |

## Activation-trace semantics

| Term | Meaning | Source |
| --- | --- | --- |
| `activation_path` | One activation's own path: a list of `(cfg_node, store)` pairs, read by `path_of`. | `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy` |
| `activation_trace` | One procedure activation of a sequential run: its own `activation_path`, its frozen caller ancestry, and its completed callee subtrees (root, called activation, or resumed caller). Distinct from the local traces of Schwarz et al., which are per-thread traces of a multithreaded semantics. | `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy` |
| `valid_activation_trace` | Inductive concrete semantics over activation traces. | `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy` |
| `caller_of` | Immediate caller stored structurally in a called or resumed trace. | `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy` |
| `node_collect` | Node-indexed collecting semantics: reachable sink stores at each CFG node, forgetting activation structure and context. `activation_collect` is its context-indexed refinement. | `src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy` |
| `activation_collect` | `activation_collect gs R c\<^sub>0 g S v c`: reachable sink stores at `v` in context `c`, the `activation_context_rel`-grouped view of `node_collect`. `R` is the `call_context_rel`. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `activation_coverage` | The five obligations (`INIT`, `INTRA`, `CALL`, `RETURN`, `TOTAL`) under which a per-node, per-context store-set claim covers every valid activation trace. | `src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy` |
| `activation_context_rel` | Inductive `activation_context_rel gs R c\<^sub>0 g t c`: the context a valid activation trace carries. Its Call rule picks an edge in `calls g` at the call node that reproduces the entered store, so no compiler uniqueness invariant is needed. The relational form of the paper's `beta`. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `call_context_rel` | `'c call_context_rel = cfg_node => 'c => call_info => store => store => 'c => bool`: the admissible callee contexts of one concrete call, from call site, caller context, call info, caller store and entered store. Several contexts per call are allowed. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `call_context_rel_of_fun` | Embeds a functional policy (`unit`, call strings) as the relation admitting exactly the function's value. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `call_context_total_on` | `call_context_total_on cover R gs g`: conditional totality -- an empty relation is rejected only where a covered call exists. It is what makes the context-insensitive collection exactly the union of the buckets (`node_collect_eq_Union_activation_collect`). Buckets form a cover, not a partition. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `c\<^sub>0` | Context of the root activation (locale parameter, formerly `startcontext`), Goblint's `Spec.startcontext`. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |

## Abstract interpretation

| Term | Meaning | Source |
| --- | --- | --- |
| `abs_state` | Pointwise abstract variable environment. | `src/Abstract_Interpreter/Domain/State/Nonrelational_State.thy` |
| `default_st_to_fun` | The function a carrier state represents, written `ρ⇘𝒢⇙ s` in bundle `default_st_syntax` ("its function", "the represented function"). It plays the role of `fun_rep` in HOL-IMP's `Abs_State.thy` (Concrete Semantics) for the executable `default_st`, with the classifier `𝒢` choosing the local or global slot of each name. | `src/Abstract_Interpreter/Exec/State/Default_St_Transfer.thy` |
| `readback` | The abstract state an executable state represents, written `ρ⇘𝒢⇙ x` in bundle `default_st_syntax`. One overloaded constant with three instances chosen by the type of `x`: `default_st_to_fun` for a carrier state, `map_lift (default_st_to_fun 𝒢)` for a lifted one, and `dg_state_to_fun` for a D/G state. The concretization of an executable state is `⟦ρ⇘𝒢⇙ x⟧`. | `src/Abstract_Interpreter/Domain/State/State_Concretization.thy` |
| `exact_emptiness`, `sound_emptiness` | Whether an emptiness test `e` holds of exactly the values a concretization `γ` maps to `{}` (`e x ⟷ γ x = {}`) or only of some of them (`e x ⟹ γ x = {}`). Exact: a domain's `is_empty`, `is_empty_state`, `default_st_is_bot_for`, the order domain. Sound only: the D/G locale's `empty⇩V` (its contract asks only soundness; an instance may be exact), the combined state's `mcp_empty_v` (not exact: `mcp_empty_v_not_exact`), and `DEAD` on report points (not exact: `DEAD_not_exact`). | `src/Abstract_Interpreter/Domain/Lattice/Abstract_Domain.thy` |
| `numeric_domain` | Abstract carrier, order, and concretization obligations. | `src/Abstract_Interpreter/Domain/Lattice/Abstract_Domain.thy` |
| `part_post_solution` | Certificate with a query-membership condition and three conditions per unknown in the vars set (dependency closure, local-result bound, every side contribution bounded) an equation-system valuation must satisfy; generic over the unknown/value types, so it is the shared interface between solver correctness and D/G collecting soundness, not tied to any one solver. | `vendor/td-verification/Basics_side.thy` |
| `TD_side_upd_rule` | Vendored verified side-effecting top-down solver, parametric in the global update rule, that the analyses instantiate (`TD_side_rule_Interp`, `Globals_Rule.thy`). It warrows every local unknown at a widening point. Its leastness theorem belongs to the separate `TD_side_mono` locale, which Voblint does not instantiate. | `vendor/td-verification/TD_side_upd_rule.thy` |
| `solve_dom_of_solve_c` | `solve_c x ≠ None` implies `solve_dom x`. With the vendored `partial_post_solution` (`solve_dom` implies `part_post_solution`) and `finite_stabl_solve` it discharges `certified_solver`. | `src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy` |
| `certified_solver` | The solver contract the analysis pipeline assumes, over any equation system: in the solver's domain a solve answers a `part_post_solution` over a finite key set, and `solve_c` succeeding implies `solve_dom` (assumptions `solve_pp`, `solve_fin`, `dom_of_solve_c`). `dg_analysis` and `dg_analysis_exec` extend it; `td_certified_solver` (`Globals_Rule.thy`) proves it for the vendored solver at every `globals_rule`. | `src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy` |

## D/G framework

| Term | Meaning | Source |
| --- | --- | --- |
| `D` | Analysis-chosen flow-sensitive fact associated with a local unknown. | `src/Abstract_Interpreter/Framework/Spec/DG_State.thy` |
| `G` | Analysis-chosen shared fact routed through global side effects. | `src/Abstract_Interpreter/Framework/Spec/DG_State.thy` |
| `dg_spec` | D/G transfer, entry, combine, read, and publication interface. | `src/Abstract_Interpreter/Framework/Spec/DG_Spec.thy` |
| `analysis_contract` | Concrete-soundness obligations for a D/G instance. | `src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy` |
| resume value (`cont`) | First component `q` of an entry pair `(q, e)` that `enter#` returns: the caller-side value the callee's result is combined with. The theories name it `cont` (`entry_pairs_cover`: `(cont, entry) ∈ set pairs`); the thesis calls it the resume value. One pair must cover both the caller store (by `cont`) and the entered store (by `entry`). | `src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy` |
| `routed_node_rhs` | D/G equation generator: one right-hand side per node and context, joining the local-edge programs, one program per call site, and the extra contribution programs (`routed_contribution_programs`; in the routed instance these are the framework's seed-reading programs, `routed_entry_seed_programs`). | `src/Abstract_Interpreter/Framework/Constraints/DG_Indexed_Generator.thy` |

### Correspondence to Goblint's `Spec` interface

Goblint's `Spec` module signature (`analyses.ml`) fixes four type components:
`D` (local abstract value), `G` (global abstract value), `C` (context), and
`V` (the analysis's own global-variable-name type, indexing `G`). The table
below states the current Voblint type or locale parameter realizing each,
and where the correspondence is inexact.

| `Spec` component | Voblint realization | Note |
| --- | --- | --- |
| `D` | Opaque `'D` carrier (`dg_state.dg_local`) | Chosen by each `dg_spec`. Base analyses use a non-relational or executable state carrier; `Rel_Order_Domain` demonstrates a relational carrier. |
| `G` | Opaque `'G` carrier (`dg_state.dg_global`) | Chosen independently by each `dg_spec`; homogeneous analyses may use the same type for `D` and `G`. See "Local/global payloads" in `docs/GOBLINT_ALIGNMENT_REGISTER.md`. |
| `C` | `'c` (type parameter of `dg_context_activation`/`routed_context`, `DG_Ctx_Activation.thy`, `Routed_Context.thy`) | Instantiated per analysis instance (`unit`, call-string, entry-state, ...). |
| `V` | `'v` (the `dg_spec` record's global-name parameter, `DG_Spec.thy`) | An analysis reaches shared state only through `man_global`/`man_sideg` at a `'v`; `mk_dg_man` embeds it into the solver's global-key type `'k` (`DG_Manager.thy`). Not the combined unknown space -- see below. |

**The combined unknown space is not `V`.** The vendored solver's equation type
(`vendor/td-verification/Basics_side.thy`) is generic over `'x` (local key)
and `'g` (global key): `('x, 'g, 'd) eqsT = 'x => ('x, 'g, 'd) strategy_tree`,
with unknowns typed `'x + 'g`. `DG_Ctx_Activation.thy` instantiates
`'x = pp \<times> 'c` and, deliberately, `'g = 'k` rather than reusing the bare
letter `'g` -- `DG_State.thy`'s `dg_state` datatype already fixes `'g` as
the global *value* type (the `dg_global` field, i.e. Goblint's `G.t`), one layer
up. Reusing `'g` for the global *key* at the activation layer would silently
overload one letter for two different `Spec` components (`G` and `V`) across
two adjacent files. `'k` names the vendor solver's global-key slot without
that collision; the unknown space `pp \<times> 'c + 'k` corresponds to Goblint's
combined local/global unknown (`LVar.t + GVar.t` in `constraints.ml`'s
terms), built from `C` and `V` respectively, not to `V` alone.

### `#`-notated abstract operations

Inline mixfix notation naming the abstract-operation-layer counterpart of a
paper/Goblint concept, applied to the stable Isabelle identifier that already
carries the soundness proof -- notation does not rename the identifier.

| Notation | Identifier | Layer |
| --- | --- | --- |
| `enter#` | `dgs_enter` (`dg_spec` field) | Specification, `DG_Spec.thy` |
| `context#` | `route` (locale parameter of `dg_context_activation`, carrying the notation in `routed_context`) | Generator, `Routed_Context.thy` |
| `combine_env#` | `dgs_combine_env` (`dg_spec` field) | Specification, `DG_Spec.thy` |
| `combine_assign#` | `dgs_combine_assign` (`dg_spec` field) | Specification, `DG_Spec.thy` |
| `combine#` | `combine_collect_abs` (the fixed whole-state return merge) | Abstract-state algebra, `Transfer_Algebra.thy` |

`route`'s semantic counterpart is the relation `call_context_rel`
(`Activation_Trace_Context.thy`), which consumes **concrete** stores rather than
an abstract state and is left unnotated, matching `call_enter` -- the concrete
counterpart of `enter#` -- staying unnotated. `routed_entry_cover` is the
per-instance locale obligation: at a real call edge, some `(cont, entry)`
alternative of the spec's own `enter#` run covers the caller and entered
stores, and `route` on that entry yields a context `routed_entry_context_rel`
admits. Goblint's `Spec.context` is a function applied per `enter`
alternative; since `enter` returns a list, one concrete call can land in
several contexts, and Voblint's proof relation models exactly that whole-call
nondeterminism (`enter` alternatives x `context`). `context` itself is an Isar
outer keyword, hence `route` -- see `docs/GOBLINT_ALIGNMENT_REGISTER.md`.

### `sigma` / `sg`

Both fixed in `dg_context_activation` (`DG_Ctx_Activation.thy`) and genuinely
different objects, not naming duplication:

| Term | Meaning |
| --- | --- |
| `sigma` | Raw `dg_state` reader over the unknown space `pp \<times> 'c + 'k` -- the vendored solver's own solution shape (`sigma :: pp \<times> 'c + 'k => ('D, 'G) dg_state`). |
| `sg` | The reader an analysis publishes over the same unknowns (`sg :: pp \<times> 'c + 'k => 'M`), read as stores through `gammaM`. |

The locale assumption `sg_cov` ties them: at a covered key,
`gammaM (sg (Inl (v, c)))` is `gammaDG` of `sigma`'s local slot against its one
shared global slot `Inr analysis_global`, and `sg_uncov` makes it empty off the solved keys.
Unifying the two names would make a proof step that needs both
indistinguishable.

### Notation and locale-local abbreviations

The notation the theories declare (global symbols such as `\<C>`, `\<T>`,
`\<rightarrow>\<^sub>p`) and the locale-local abbreviations over a locale's
fixed arguments (`\<C>`, `\<T>`, `\<A>`, `carries`, `admits`, `gamma_at`,
`man_at`, `cover`) are listed once, in the table generated from their
declarations: the [README's Notation section](../README.md#notation), appendix B
of the thesis, and `thesis/shared/generated/notation.json`
(`pixi run thesis-notation-write`). Edit `thesis/shared/notation.toml` for a
reading or meaning; everything else comes from the theories.

Locale abbreviations unfold at parse time, so every exported theorem is the same
term as without them. A printing abbreviation also folds goals and facts,
including those of every interpretation of its locale, which then print as
`X.cover v c`. `activation_coverage` is only interpreted inside proofs, so printing
mode is safe there. The other locales have theory-level interpretations, so
their abbreviations are input-only and interpreted facts keep the explicit
terms. The anonymous context fixing `p` in `DG_Analysis.thy` adds the
input-only `pgs` for `declared_global p`; it is not a locale and stays out of
the table.

## Source-facing endpoints

| Term | Meaning | Source |
| --- | --- | --- |
| `analysis_report` | What `run_voblint` returns for an analysed program: the semantic states per point and context, the check column and the diagnostics. Read through `⟦res⟧⇘v⇙` (`report_sem`), `𝒱⇘res⇙ v` (`verdict_stores`) and `DEAD`. Termination is not a premise of its theorems: `run_voblint` solves with the executable `solve_c`, and an answer exists only where it returned (`solve_c_run`). | `src/Executable_Surface/CLI/Analysis_Report.thy` |
| `source_activation_sound` | Compiler and activation-collecting bridge for accepted source executions. | `src/Analyses/Shared/Result/Source_Activation_Sound.thy` |
| `fun_route_source_sound` | The routed endpoints for a route that is a function of the call site, the unit route among them: a terminating solve bounds every store a source run reaches by the state published at its point under one of its contexts (`fun_route_source_sound`, `fun_route_result_node_sound`, `fun_route_report_proved_sound`). Every domain's unit registration is an instance. | `src/Analyses/Shared/Result/DG_Live_Unknowns.thy` |
