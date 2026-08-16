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
| `source_location` | Resolved source storage location: `GlobalVar` or an implicitly procedure-local `LocalVar`. | `src/VIMP/VIMP_Proc.thy` |
| `storage_of` | Program declaration-driven source-location resolver. A non-declared identifier is implicitly local to the supplied procedure. | `src/VIMP/VIMP_Notation.thy` |
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
| `compile` | Compiles one source command into local edges and calls over a node interval. | `src/CFG/VIMP_Proc_to_CFG.thy` |
| `compile_proc` | Adds a procedure entry, result boundary, and fall-through return to a compiled body. | `src/CFG/VIMP_Proc_to_CFG.thy` |
| `compile_prog` | Compiles the procedure table and distinguished main command into one CFG. | `src/CFG/VIMP_Proc_to_CFG.thy` |
| `wf_compile_input` | Canonical static contract for accepted source programs. | `src/CFG/Compiler/Compile_Invariants.thy` |

## Activation-local semantics

| Term | Meaning | Source |
| --- | --- | --- |
| `ltr` | Activation-local trace: root, called activation, or resumed caller. | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `valid_ltr` | Inductive concrete semantics over activation-local traces. | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `caller_of` | Immediate caller stored structurally in a called or resumed trace. | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `ltr_collect` | Reachable sink stores at each CFG node, forgetting trace structure. | `src/CFG/Collecting/LTR_Collect.thy` |
| `activation_collect` | Reachable sink stores indexed by activation context (the key-grouped view of `ltr_collect`). | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `ltr_gamma` | Concretization interface relating abstract states to local-trace collecting semantics. | `src/CFG/Collecting/LTR_Abstract.thy` |
| `key` | Functional describing-function reading a trace's admissible context, one context per position -- the paper's `beta` one-for-one. | `src/CFG/Collecting/CFG_Local_Trace.thy` |
| `admiss` / `ctx_key` | `admiss` is a locale-fixed relation admitting possibly several target contexts per step; `ctx_key` lifts it over a trace. The *relational* generalization of `beta`, not `beta` itself -- needed where an instance may pick a context nondeterministically. `admiss_exact` is the functional (single-admissible-target) instance. | `src/CFG/Collecting/CFG_Local_Trace.thy` |

## Abstract interpretation

| Term | Meaning | Source |
| --- | --- | --- |
| `abs_state` | Pointwise abstract variable environment. | `src/Core/Equations/Constraint_System.thy` |
| `sound_domain` | Abstract carrier, order, and concretization obligations. | `src/Core/Domain/Abstract_Domain.thy` |
| `domain_transfer` | Pure abstract transfers for CFG actions, entry, and return combination. | `src/Core/Equations/Constraint_System.thy` |
| `effectful_domain_transfer` | Strategy-tree-producing transfers used by the side-effecting solver. | `src/Core/Equations/Constraint_System.thy` |
| `part_post_solution` | Two-part certificate (local-result bound plus every side contribution) an equation-system valuation must satisfy; generic over the unknown/value types, so it is the shared interface between solver correctness and D/G collecting soundness, not tied to any one solver. | `vendor/td-verification/Basics_side.thy` |
| `TD_side` | Vendored verified side-effecting top-down solver used by executable analyses. | `vendor/td-verification` |

## D/G framework

| Term | Meaning | Source |
| --- | --- | --- |
| `D` | Analysis-chosen flow-sensitive fact associated with a local unknown. | `src/Core/Solver/Context/DG/DG_Framework.thy` |
| `G` | Analysis-chosen shared fact routed through global side effects. | `src/Core/Solver/Context/DG/DG_Framework.thy` |
| `dg_spec` | D/G transfer, entry, combine, read, and publication interface. | `src/Core/Solver/Context/DG/DG_Framework.thy` |
| `sound_dg_spec` | Concrete-soundness obligations for a D/G instance. | `src/Core/Solver/Context/DG/DG_Soundness.thy` |
| `dg_gen_of` | Executable D/G equation generator. | `src/Analysis/Instances/Mixed/Exec_DG_Bridge.thy` |
| `dg_postfix` | Mathematical post-solution property for D/G equations. | `src/Core/Solver/Context/DG/DG_Soundness.thy` |

### Correspondence to Goblint's `Spec` interface

Goblint's `Spec` module signature (`analyses.ml`) fixes four type components:
`D` (local abstract value), `G` (global abstract value), `C` (context), and
`V` (the analysis's own global-variable-name type, indexing `G`). The table
below states the current Voblint type or locale parameter realizing each,
and where the correspondence is inexact.

| `Spec` component | Voblint realization | Note |
| --- | --- | --- |
| `D` | `'a abs_state` (`dg_state.locals`) | Flat `vname => 'a` today; Goblint's `D.t` can be any lattice. |
| `G` | `'a abs_state` (`dg_state.globs`) | Same flat type as `D` in every current instance -- Goblint's `G.t` is a separate, analysis-chosen lattice. See "Local/global payloads" in `docs/GOBLINT_ALIGNMENT_REGISTER.md`. |
| `C` | `'c` (locale parameter of `dg_ctx_activation`/`routed_context`, `DG_Ctx_Activation.thy`) | Instantiated per analysis instance (`unit`, call-string, entry-state, ...). |
| `V` | `'k` (locale parameter of `dg_ctx_activation`, `DG_Ctx_Activation.thy`) | The type of global-variable identities, matching Goblint's `S.V` (see `M1_CALLSTRING_CONTEXT_MIGRATION.md`'s `GVar = GVarF (S.V)` citation). Not the combined unknown space -- see below. |

**The combined unknown space is not `V`.** The vendored solver's equation type
(`vendor/td-verification/Basics_side.thy`) is generic over `'x` (local key)
and `'g` (global key): `('x, 'g, 'd) eqsT = 'x => ('x, 'g, 'd) strategy_tree`,
with unknowns typed `'x + 'g`. `DG_Ctx_Activation.thy` instantiates
`'x = pp \<times> 'c` and, deliberately, `'g = 'k` rather than reusing the bare
letter `'g` -- `DG_Framework.thy`'s `dg_state` datatype already fixes `'g` as
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
| `enter#` | `tf_enter` (`domain_transfer` field) | Flat/abstract, `Constraint_System.thy` |
| `context#` | `route` (locale parameter of `routed_context`) | Generator, `Routed_Context.thy` |
| `combine_env#` | `combine_env_abs` | Flat/abstract, `Constraint_System.thy` |
| `combine_assign#` | `combine_assign_abs` | Flat/abstract, `Constraint_System.thy` |
| `combine#` | `combine_collect_abs` (`combine_env#` then `combine_assign#`) | Flat/abstract, `Constraint_System.thy` |

`route`'s semantic ground truth is `enterc` (`Routed_Context.thy`), which
consumes a **concrete** `store` rather than an abstract state and is left
unnotated, matching `call_enter`/`dgs_enter` staying unnotated below
`enter#`. `route_enterc_agree` is the per-instance locale obligation proving
the two agree on real call edges, not a blanket theorem. `context#`'s
signature is currently stronger than Goblint's `Spec.context` -- see
`docs/GOBLINT_ALIGNMENT_REGISTER.md` and issue #114.

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

## Strategy-tree equation combinators

Named, zero-cost (`abbreviation`) readings of the verified solver's four
`strategy_tree` constructors (`QueryL`, `QueryG`, `Side`, `Answer`,
`vendor/td-verification/Basics_side.thy`). Full design and rationale in
`docs/DG_COMBINATOR_MIGRATION.md`.

| Term | Meaning | Source |
| --- | --- | --- |
| `read_local` | Read a local unknown, continue with its value. | `src/Core/Solver/Strategy_Tree/Strategy_Tree_Combinators.thy` |
| `read_global` | Read a global unknown, continue with its value. | `src/Core/Solver/Strategy_Tree/Strategy_Tree_Combinators.thy` |
| `depend_on` | Publish a side value under a global key, continue. | `src/Core/Solver/Strategy_Tree/Strategy_Tree_Combinators.thy` |
| `answer` | Yield the equation's local result. | `src/Core/Solver/Strategy_Tree/Strategy_Tree_Combinators.thy` |
| `enter_global` / `enter_local` | The global side effect / local answer half of `dgs_enter`. | `src/Core/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `combine_global` / `combine_local` | The global side effect / local answer half of `dgs_combine`. | `src/Core/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `publish_global` | `depend_on` to the one shared global slot, wrapping the payload as `DG bot x`. | `src/Core/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `publish_seed` | `depend_on` to a routed per-context seed slot -- same primitive as `publish_global`, named for the role. | `src/Core/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `return_local` | Yield the equation's own local contribution, wrapping it as `DG x bot`. | `src/Core/Solver/Context/DG/DG_Transfer_Combinators.thy` |
| `with_call` | Destructure a `call_action`'s single constructor once per call site instead of once per `dgs_enter`/`dgs_combine` call. | `src/Core/Solver/Context/DG/DG_Transfer_Combinators.thy` |

## Source-facing endpoints

| Term | Meaning | Source |
| --- | --- | --- |
| `source_activation_sound` | Compiler and activation-collecting bridge for accepted source executions. | `src/Formalization/Pipeline/Source_Activation_Sound.thy` |
| `dg_exec_run_source_sound_for` | Reusable bundle connecting a computed D/G solver result to source execution. | `src/Formalization/Pipeline/Run_Analysis_Sound.thy` |
| `mixed_flow_analysis_sound` | Mixed local/global analysis soundness. | `src/Formalization/Pipeline/Mixed_Flow_Sound.thy` |
