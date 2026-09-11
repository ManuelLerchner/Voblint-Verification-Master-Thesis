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
| `enter_state` | Callee store with caller globals and fresh local variables. | `src/Program_Model/VIMP/VIMP_Globals.thy` |
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

## Activation-local semantics

| Term | Meaning | Source |
| --- | --- | --- |
| `ltr` | Activation-local trace: root, called activation, or resumed caller. | `src/Program_Model/CFG/Collecting/LTR_Def.thy` |
| `valid_ltr` | Inductive concrete semantics over activation-local traces. | `src/Program_Model/CFG/Collecting/LTR_Def.thy` |
| `caller_of` | Immediate caller stored structurally in a called or resumed trace. | `src/Program_Model/CFG/Collecting/LTR_Def.thy` |
| `ltr_collect` | Reachable sink stores at each CFG node, forgetting trace structure. | `src/Program_Model/CFG/Collecting/LTR_Collect.thy` |
| `activation_collect` | `activation_collect gs R startcontext g S v c`: reachable sink stores at `v` in context `c`, the `trace_context`-grouped view of `ltr_collect`. `R` is the `call_context_rel`. | `src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy` |
| `ltr_coverage` | The five obligations (`INIT`, `INTRA`, `CALL`, `RETURN`, `TOTAL`) under which a per-node, per-context store-set claim covers every valid trace. | `src/Program_Model/CFG/Collecting/LTR_Abstract.thy` |
| `trace_context` | Inductive `trace_context gs R startcontext g t c`: the context a valid trace carries. Its Call rule picks an edge in `calls g` at the call node that reproduces the entered store, so no compiler uniqueness invariant is needed. The relational form of the paper's `beta`. | `src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy` |
| `call_context_rel` | `'c call_context_rel = cfg_node => 'c => call_info => store => store => 'c => bool`: the admissible callee contexts of one concrete call, from call site, caller context, call info, caller store and entered store. Several contexts per call are allowed. | `src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy` |
| `call_context_rel_of_fun` | Embeds a functional policy (`unit`, call strings) as the relation admitting exactly the function's value. | `src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy` |
| `call_context_total_on` | `call_context_total_on cover R gs g`: conditional totality -- an empty relation is rejected only where a covered call exists. It is what makes the context-insensitive collection exactly the union of the buckets (`ltr_collect_eq_Union_activation_collect`). Buckets form a cover, not a partition. | `src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy` |
| `startcontext` | Context of the root activation, Goblint's `Spec.startcontext`. | `src/Program_Model/CFG/Collecting/LTR_Activation_Context.thy` |

## Abstract interpretation

| Term | Meaning | Source |
| --- | --- | --- |
| `abs_state` | Pointwise abstract variable environment. | `src/Abstract_Interpreter/Domain/Nonrelational_State.thy` |
| `sound_domain` | Abstract carrier, order, and concretization obligations. | `src/Abstract_Interpreter/Domain/Abstract_Domain.thy` |
| `part_post_solution` | Two-part certificate (local-result bound plus every side contribution) an equation-system valuation must satisfy; generic over the unknown/value types, so it is the shared interface between solver correctness and D/G collecting soundness, not tied to any one solver. | `vendor/td-verification/Basics_side.thy` |
| `TD_side` | Vendored verified side-effecting top-down solver used by executable analyses. | `vendor/td-verification` |

## D/G framework

| Term | Meaning | Source |
| --- | --- | --- |
| `D` | Analysis-chosen flow-sensitive fact associated with a local unknown. | `src/Abstract_Interpreter/Framework/Spec/DG_State.thy` |
| `G` | Analysis-chosen shared fact routed through global side effects. | `src/Abstract_Interpreter/Framework/Spec/DG_State.thy` |
| `dg_spec` | D/G transfer, entry, combine, read, and publication interface. | `src/Abstract_Interpreter/Framework/Spec/DG_Spec.thy` |
| `sound_dg_spec_core` | Concrete-soundness obligations for a D/G instance. | `src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy` |
| `routed_node_rhs` | D/G equation generator: one right-hand side per node and context, joining the local-edge trees, one tree per call site, and the analysis's extra trees (`routed_contribution_trees`). | `src/Abstract_Interpreter/Framework/Constraints/DG_Keyed_Generator.thy` |

### Correspondence to Goblint's `Spec` interface

Goblint's `Spec` module signature (`analyses.ml`) fixes four type components:
`D` (local abstract value), `G` (global abstract value), `C` (context), and
`V` (the analysis's own global-variable-name type, indexing `G`). The table
below states the current Voblint type or locale parameter realizing each,
and where the correspondence is inexact.

| `Spec` component | Voblint realization | Note |
| --- | --- | --- |
| `D` | Opaque `'D` carrier (`dg_state.locals`) | Chosen by each `dg_spec`. Base analyses use a non-relational or executable state carrier; `Rel_Order_Domain` demonstrates a relational carrier. |
| `G` | Opaque `'G` carrier (`dg_state.globs`) | Chosen independently by each `dg_spec`; homogeneous analyses may use the same type for `D` and `G`. See "Local/global payloads" in `docs/GOBLINT_ALIGNMENT_REGISTER.md`. |
| `C` | `'c` (type parameter of `dg_ctx_activation_base`/`routed_context_base_hetero`, `DG_Ctx_Activation.thy`, `Routed_Context.thy`) | Instantiated per analysis instance (`unit`, call-string, entry-state, ...). |
| `V` | `'v` (the `dg_spec` record's global-name parameter, `DG_Spec.thy`) | An analysis reaches shared state only through `man_global`/`man_sideg` at a `'v`; `mk_dg_man` embeds it into the solver's global-key type `'k` (`DG_Manager.thy`). Not the combined unknown space -- see below. |

**The combined unknown space is not `V`.** The vendored solver's equation type
(`vendor/td-verification/Basics_side.thy`) is generic over `'x` (local key)
and `'g` (global key): `('x, 'g, 'd) eqsT = 'x => ('x, 'g, 'd) strategy_tree`,
with unknowns typed `'x + 'g`. `DG_Ctx_Activation.thy` instantiates
`'x = pp \<times> 'c` and, deliberately, `'g = 'k` rather than reusing the bare
letter `'g` -- `DG_State.thy`'s `dg_state` datatype already fixes `'g` as
the global *value* type (the `globs` field, i.e. Goblint's `G.t`), one layer
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
| `context#` | `route` (locale parameter of `dg_ctx_activation_base`, carrying the notation in `routed_context_base_hetero`) | Generator, `Routed_Context.thy` |
| `combine_env#` | `dgs_combine_env` (`dg_spec` field) | Specification, `DG_Spec.thy` |
| `combine_assign#` | `dgs_combine_assign` (`dg_spec` field) | Specification, `DG_Spec.thy` |
| `combine#` | `combine_collect_abs` (the fixed whole-state return merge) | Abstract-state algebra, `Transfer_Algebra.thy` |

`route`'s semantic counterpart is the relation `call_context_rel`
(`LTR_Activation_Context.thy`), which consumes **concrete** stores rather than
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

Both fixed in `dg_ctx_activation_base` (`DG_Ctx_Activation.thy`) and genuinely
different objects, not naming duplication:

| Term | Meaning |
| --- | --- |
| `sigma` | Raw `dg_state` reader over the unknown space `pp \<times> 'c + 'k` -- the vendored solver's own solution shape (`sigma :: pp \<times> 'c + 'k => ('D, 'G) dg_state`). |
| `sg` | The reader an analysis publishes over the same unknowns (`sg :: pp \<times> 'c + 'k => 'M`), read as stores through `gammaM`. |

The locale assumption `sg_cov` ties them: at a covered key,
`gammaM (sg (Inl (v, c)))` is `gammaDG` of `sigma`'s local slot against its one
shared global slot `Inr gk0`, and `sg_uncov` makes it empty off the solved keys.
Unifying the two names would make a proof step that needs both
indistinguishable.

## Source-facing endpoints

| Term | Meaning | Source |
| --- | --- | --- |
| `source_activation_sound` | Compiler and activation-collecting bridge for accepted source executions. | `src/Analyses/Shared/Result/Source_Activation_Sound.thy` |
| `unit_dg_analysis` | The context-insensitive analysis: `routed_dg_analysis` at the unit context, with the published `state_at`/`report` and the endpoints connecting a computed solve to source execution (`source_sound`, `completed_run_sound`, `result_node_sound`). Every domain's unit route interprets it. | `src/Analyses/Shared/Result/Unit_DG_Analysis.thy` |
