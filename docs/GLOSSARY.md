# Glossary

The source theories are authoritative. File references identify the defining
layer without embedding line numbers that drift.

## Source language

| Term | Meaning | Source |
| --- | --- | --- |
| `com` | Procedural command language: structured commands, calls, explicit returns, and internal restoration commands. | `src/VIMP/VIMP_Proc.thy` |
| `proc_decl` | Procedure declaration containing formal parameters and a body. | `src/VIMP/VIMP_Proc.thy` |
| `proc_table` | Partial map from procedure names to declarations. | `src/VIMP/VIMP_Proc.thy` |
| `frame` | Saved caller store and optional return destination. | `src/VIMP/VIMP_Proc.thy` |
| `pstep` / `psteps` | Small-step execution over a command, store, and activation-frame stack. | `src/VIMP/VIMP_Proc.thy` |
| `pcompletes` | Terminating source execution with an empty frame stack. | `src/VIMP/VIMP_Proc.thy` |
| `source_com` | Syntactic source-command restriction excluding runtime-only commands. | `src/VIMP/VIMP_Proc.thy` |
| `wf_source_com` | Whole-program-aware command check for declared calls, arity, and reserved-variable exclusion. | `src/VIMP/VIMP_Proc.thy` |
| `value_providing` | Conservative syntactic predicate: no fall-through or void return and at least one value return. | `src/VIMP/VIMP_Proc.thy` |
| `wf_source_program` | Source contract for declarations, calls, returns, reserved variables, and a fall-through-only main. | `src/VIMP/VIMP_Proc.thy` |
| `ret_var` | Reserved internal channel carrying an explicit return value during unwinding. | `src/VIMP/VIMP_Proc.thy` |
| `enter_state` | Callee store with caller globals and fresh local variables. | `src/VIMP/VIMP_Globals.thy` |
| `combine_env` | Restored caller locals combined with callee globals; Goblint's `combine_env`, split from the separate destination write (`combine_assign`). | `src/VIMP/VIMP_Globals.thy` |

## Procedure-aware CFG

| Term | Meaning | Source |
| --- | --- | --- |
| `cfg_node` | `Statement n`, `FunctionEntry p`, or `FunctionResult p`. | `src/CFG/CFG_Def.thy` |
| `edge_action` | Local CFG transfer, including assignments, assumptions, no-op flow, and matching procedure returns. | `src/CFG/CFG_Def.thy` |
| `intra` | Ordinary procedure-local CFG edges. | `src/CFG/CFG_Def.thy` |
| `calls` | Call-site relation containing the call action, callee entry, and continuation. | `src/CFG/CFG_Def.thy` |
| `wf_cfg` | Generic structural well-formedness conditions for a CFG. | `src/CFG/CFG_Def.thy` |
| `compile` | Compiles one source command into local edges and calls over a node interval. | `src/Compile/VIMP_Proc_to_CFG.thy` |
| `compile_proc` | Adds a procedure entry, result boundary, and fall-through return to a compiled body. | `src/Compile/VIMP_Proc_to_CFG.thy` |
| `compile_prog` | Compiles the procedure table and distinguished main command into one CFG. | `src/Compile/VIMP_Proc_to_CFG.thy` |
| `wf_compile_input` | Canonical static contract for accepted source programs. | `src/Compile/Compile_Invariants.thy` |

## Activation-local semantics

| Term | Meaning | Source |
| --- | --- | --- |
| `ltr` | Activation-local trace: root, called activation, or resumed caller. | `src/CFG/Collecting/LTR_Def.thy` |
| `valid_ltr` | Inductive concrete semantics over activation-local traces. | `src/CFG/Collecting/LTR_Def.thy` |
| `caller_of` | Immediate caller stored structurally in a called or resumed trace. | `src/CFG/Collecting/LTR_Def.thy` |
| `ltr_collect` | Reachable sink stores at each CFG node, forgetting trace structure. | `src/CFG/Collecting/LTR_Collect.thy` |
| `activation_collect` | `activation_collect gs R startcontext g S v c`: reachable sink stores at `v` in context `c`, the `trace_context`-grouped view of `ltr_collect`. `R` is the `call_context_rel`. | `src/CFG/Collecting/LTR_Activation_Context.thy` |
| `ltr_gamma` | Concretization interface relating abstract states to local-trace collecting semantics. | `src/CFG/Collecting/LTR_Abstract.thy` |
| `trace_context` | Inductive `trace_context gs R startcontext g t c`: the context a valid trace carries. Its Call rule picks an edge in `calls g` at the call node that reproduces the entered store, so no compiler uniqueness invariant is needed. The relational form of the paper's `beta`. | `src/CFG/Collecting/LTR_Activation_Context.thy` |
| `call_context_rel` | `'c call_context_rel = cfg_node => 'c => call_info => store => store => 'c => bool`: the admissible callee contexts of one concrete call, from call site, caller context, call info, caller store and entered store. Several contexts per call are allowed. | `src/CFG/Collecting/LTR_Activation_Context.thy` |
| `call_context_rel_of_fun` | Embeds a functional policy (`unit`, call strings) as the relation admitting exactly the function's value. | `src/CFG/Collecting/LTR_Activation_Context.thy` |
| `call_context_total_on` | `call_context_total_on cover R gs g`: conditional totality -- an empty relation is rejected only where a covered call exists. `activation_bucket_sound` (one bucket) needs no totality; `activation_collect_sound` (whole program) does. Buckets form a cover, not a partition. | `src/CFG/Collecting/LTR_Activation_Context.thy` |
| `startcontext` | Context of the root activation, Goblint's `Spec.startcontext`. | `src/CFG/Collecting/LTR_Activation_Context.thy` |

## Abstract interpretation

| Term | Meaning | Source |
| --- | --- | --- |
| `abs_state` | Pointwise abstract variable environment. | `src/Domain/Nonrelational_State.thy` |
| `sound_domain` | Abstract carrier, order, and concretization obligations. | `src/Domain/Abstract_Domain.thy` |
| `part_post_solution` | Two-part certificate (local-result bound plus every side contribution) an equation-system valuation must satisfy; generic over the unknown/value types, so it is the shared interface between solver correctness and D/G collecting soundness, not tied to any one solver. | `vendor/td-verification/Basics_side.thy` |
| `TD_side` | Vendored verified side-effecting top-down solver used by executable analyses. | `vendor/td-verification` |

## D/G framework

| Term | Meaning | Source |
| --- | --- | --- |
| `D` | Analysis-chosen flow-sensitive fact associated with a local unknown. | `src/Framework/Spec/DG_State.thy` |
| `G` | Analysis-chosen shared fact routed through global side effects. | `src/Framework/Spec/DG_State.thy` |
| `dg_spec` | D/G transfer, entry, combine, read, and publication interface. | `src/Framework/Spec/DG_Spec.thy` |
| `sound_dg_spec_core` | Concrete-soundness obligations for a D/G instance. | `src/Framework/Spec/DG_Spec_Sound.thy` |
| `dg_gen_of` | Executable D/G equation generator. | `src/Exec/Exec_DG_Generator.thy` |

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
| `C` | `'c` (locale parameter of `dg_ctx_activation`/`routed_context`, `DG_Ctx_Activation.thy`) | Instantiated per analysis instance (`unit`, call-string, entry-state, ...). |
| `V` | `'k` (locale parameter of `dg_ctx_activation`, `DG_Ctx_Activation.thy`) | The type of global-variable identities, matching Goblint's `S.V` (see `M1_CALLSTRING_CONTEXT_MIGRATION.md`'s `GVar = GVarF (S.V)` citation). Not the combined unknown space -- see below. |

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
| `context#` | `route` (locale parameter of `routed_context_base_hetero`) | Generator, `Routed_Context.thy` |
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

Both fixed in `dg_ctx_activation` (`DG_Ctx_Activation.thy`) and genuinely
different objects, not naming duplication:

| Term | Meaning |
| --- | --- |
| `sigma` | Raw `dg_state` reader over the unknown space `pp \<times> 'c + 'k` -- the vendored solver's own solution shape (`sigma :: pp \<times> 'c + 'k => (D, G) dg_state`). |
| `sg` | Concretization-facing reader over the same unknowns, one flat `'a abs_state` per point (`sg :: pp \<times> 'c + 'k => 'a abs_state`), satisfying `ENTRY_G`/`EDGE`/`CALL`/`COMB`. |

`sg_cov` derives `sg` from `sigma` via `combine_env_abs` (`sg` at a covered
point is `sigma`'s locals and globals combined through the local/global
classifier `gs`); unifying the two names would make a proof step that needs
both indistinguishable.

## Source-facing endpoints

| Term | Meaning | Source |
| --- | --- | --- |
| `source_activation_sound` | Compiler and activation-collecting bridge for accepted source executions. | `src/Soundness/Source_Activation_Sound.thy` |
| `dg_exec_run_source_sound_for` | Reusable bundle connecting a computed D/G solver result to source execution. | `src/Soundness/Run_Analysis_Sound.thy` |
