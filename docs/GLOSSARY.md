# Glossary

The source theories are authoritative. File references identify the defining
layer without embedding line numbers that drift.

## Canonical thesis terminology

One term per concept in thesis prose. Distinct formal objects keep distinct
names.

| Term | Use for | Not |
| --- | --- | --- |
| valuation `σ` | a map from unknowns to domain elements (`#sol`) | an abstract state (write `d`) |
| domain element | an element of a carrier where the definition is generic in it | |
| abstract value | a domain element describing the values of one variable (an interval) | a D element |
| abstract state | a domain element describing stores; D elements of the D/G framework | |
| entry / resume / exit state | `e`, `q` (`cont` in the theories), `r` of one call; `r` is the callee's state at `FunctionResult` | entry/resume/exit value, `t♯` |
| entered store | the concrete store a procedure call produces for the callee | |
| initial store | a store at the start of a program run (`init_stores κ`) | entered store |
| entry store | generic: the first store of any activation (root, callee or resumed caller), when neither term above fits | |
| execution configuration | a source configuration `(c, s, frs)` or a graph configuration `(v, s, stk)` | |
| analysis configuration | the `voblint_conf` argument of `run_voblint` | |
| analysis settings | informal: the selected domain, context policy and update rule | bare "configuration" |
| side-effecting constraint system | the literature formalism (Apinis et al.) | |
| equation system `T` | Voblint's generated system as the TD solver receives it | |
| side effect / contribution / publish | the mechanism / the published domain element / the verb | side contribution, contribute |
| stable set | the solver's `stabl`, returned by a terminating solve | |
| solved set `V` | the set `vars` on which `part_post_solution` holds; a solve instantiates it with its stable set | `S` (initial stores) |
| loop head | the CFG node where a loop is entered and left | |
| widening point | an unknown in the solver's `point` set, where TD warrows; the TD papers' widening/narrowing point | loop point |
| non-relational state | a state that describes each variable independently (precision) | |
| pointwise | the representation `var_id ⇒ 'a kd` of a non-relational state (`tabs`) | a synonym of non-relational |
| frame stack | the stack of frames in a source or graph configuration | call stack (intuition only) |
| context policy | the choice between call strings of bound `k` (`k = 0` is context-insensitive) and entry states (`context_policy` in `Analysis_Config.thy`); formally, the relation `gcontext_policy` | calling-context / routing policy |
| source contract | `wf_source_program`, `wf_compile_input`, `wf_program_compile_input` | bare "the contract" |
| coverage contract | `gactivation_coverage` | |
| analysis contract | `ganalysis_contract` | analysis soundness contract |
| `Int` | the analysis `Ana_Int`: the reduced product of Interval and Congruence at machine kinds (`int_tuple`), introduced once as such | Int product, product Int |
| `+∞` | the positive interval endpoint | bare `∞` |
| `≤` | every carrier order (`lle`) | `⊑` |
| `Unk`, `Unk_G` | local and global unknowns in Chapter 2 | `G` (clashes with the global classifier) |

## Source language

VIMP has one semantics. The parser builds surface VIMP; elaboration, an Isabelle
definition, turns it into core VIMP, which `pstep` executes. A surface program
means the core semantics of its elaboration. All of the following is in session
`Voblint_VIMP`.

| Term | Meaning | Source |
| --- | --- | --- |
| surface VIMP: `src_exp`, `src_com`, `imp_prog` | What the parser builds: expressions over names `vname`, commands `src_com = unit acom`, and a program record. Has no step relation of its own. | `src/Program_Model/VIMP/VIMP_Syntax.thy`, `VIMP_Proc.thy`, `VIMP_Program.thy` |
| `lits_fit` | Every literal of a surface expression fits `I64`. Part of the executable well-formedness check `wf_program_compile_input_exec`. | `src/Program_Model/VIMP/VIMP_Expr.thy` |
| `ikind` | Machine integer kind: `I8`, `U8`, `I16`, `U16`, `I32`, `U32`, `I64`, `U64`. | `src/Program_Model/VIMP/Machine_Kind.thy` |
| `var_id` | Variable identity: `GlobalId x`, `ScopedId p x`, `ReturnId p`, or `ReturnVar`. `kenv = var_id ⇒ ikind` assigns each a kind; `kind_decls` lists declared kinds, read by `kenv_of`. | `src/Program_Model/VIMP/Var_Id.thy`, `Core_Com.thy` |
| core VIMP: `exp`, `com` | Elaborated expressions over `var_id`, every node carrying its kind (`TArith`, `TCast`, ...), and commands `'a com = ('a, var_id, exp) gcom`. | `src/Program_Model/VIMP/Core_Exp.thy`, `Core_Com.thy` |
| `eval` | Core evaluation `exp ⇒ store ⇒ int`, `store = var_id ⇒ int`; each operation normalizes its result to its kind. | `src/Program_Model/VIMP/Core_Exp.thy` |
| `elaborate` / `elab_com` / `elab_ptable` | Elaboration of a surface expression, command and procedure table: name resolution to identities, kind assignment, explicit conversions. `eval_elaborate` relates `eval` of an elaborated expression to the kind-indexed surface evaluator `src_eval`. | `src/Program_Model/VIMP/Core_Exp.thy`, `Core_Com.thy`, `VIMP_Semantics.thy` |
| `kind_conv` | `kind_conv κ (Some x) n = ik_norm (κ x) n`: the conversion applied when a value is written to `x`; `None` leaves it unchanged. | `src/Program_Model/VIMP/VIMP_Semantics.thy` |
| `gcom` / `acom` | Generic procedural command language: structured commands, calls, explicit returns, and internal restoration commands. Every constructor except `Seq` carries an annotation that the semantics never reads. `acom` fixes surface names and expressions; `com` fixes core ones. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `gproc_decl` / `proc_decl` | Procedure declaration containing formal parameters and a body. `proc_decl` is the surface instance. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `gptable` / `ptable` / `proc_table` | Partial map from procedure names to declarations. `elab_ptable p ds` is the core table of a program. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `csim` | Simulation relation `Π, g, p ⊢ (c, s, frs) ≈ (v, s, stk)` between a source configuration and a graph configuration, where `p` is the procedure of the outermost activation (`main` for a run of the program). | `src/Program_Model/Compile/Simulation/Simulation_Relation.thy` |
| `frame` | Saved caller store and optional return destination. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `gpstep` | Generic small-step execution over a command, store and activation-frame stack, in locale `vimp_sem`, parametric in evaluator, globals, return slot and write conversion. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `pstep` / `psteps` | The canonical instance `vimp_sem.gpstep eval is_global ReturnVar (kind_conv κ)`. `pstep_declare` describes the `__voblint_nondet_int` call the parser emits for a declaration without initializer. | `src/Program_Model/VIMP/VIMP_Semantics.thy` |
| `source_com` | Syntactic source-command restriction excluding runtime-only commands. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `wf_source_com` | Whole-program-aware command check for declared calls, arity, and reserved-variable exclusion. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `value_providing` | Conservative syntactic predicate: no fall-through or void return and at least one value return. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `wf_source_program` | Source contract for declarations, calls, returns, reserved variables, and a fall-through-only main. | `src/Program_Model/VIMP/VIMP_Proc.thy` |
| `ret_var` / `ReturnVar` | Reserved internal channel carrying an explicit return value during unwinding: `ret_var` on surface names, `ReturnVar` among identities. | `src/Program_Model/VIMP/VIMP_Proc.thy`, `Var_Id.thy` |
| `enter_state` | Callee store: the caller's globals kept, every other name reset to `0` (formals are bound afterwards). C leaves such locals indeterminate; VIMP defines them, as it defines `/ 0`. | `src/Program_Model/VIMP/VIMP_Globals.thy` |
| `init_stores` | Initial stores of a program run: every global `0`, every other identity some value of its kind (`all_in_kinds`). Constrains only the initial store; callee locals come from `enter_state`. | `src/Program_Model/VIMP/VIMP_Semantics.thy` |
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
| `elab_cfg` | `elab_cfg p ds`: the graph of the elaborated program, `compile_prog (elab_ptable p ds) (prog_procs p)`. | `src/Program_Model/Compile/VIMP_Proc_to_CFG.thy` |
| `cstep` | Located small-step execution of a CFG, the canonical instance of the generic CFG step. | `src/Program_Model/CFG/CFG_Exec.thy` |
| `wf_compile_input` | Canonical static contract for accepted source programs. | `src/Program_Model/Compile/Compile_Invariants.thy` |

## Activation-trace semantics

| Term | Meaning | Source |
| --- | --- | --- |
| `gactivation_path` | One activation's own path: a list of `(cfg_node, store)` pairs, read by `path_of`. | `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy` |
| `gactivation_trace` | One procedure activation of a sequential run: its own path, its frozen caller ancestry, and its completed callee subtrees (root, called activation, or resumed caller). Distinct from the local traces of Schwarz et al., which are per-thread traces of a multithreaded semantics. | `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy` |
| `valid_activation_trace` | Inductive concrete semantics over activation traces: `valid_activation_trace κ g S`, the canonical instance of `gvalid_activation_trace` (written `𝒯`). | `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy` |
| `caller_of` | Immediate caller stored structurally in a called or resumed trace. | `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy` |
| `node_collect` | Node-indexed collecting semantics: reachable sink stores at each CFG node, forgetting activation structure and context (written `𝒞`). `node_collect κ g S v` is the canonical instance of `collect_sem.gnode_collect`; `activation_collect` is its context-indexed refinement. | `src/Program_Model/CFG/Collecting/Activation_Trace_Collect.thy` |
| `activation_collect` | `activation_collect κ adm c\<^sub>0 g S v c`: reachable sink stores at `v` in context `c` (written `𝒜`), the `gactivation_context_rel`-grouped view of `node_collect`. `adm` is the context policy. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `gactivation_coverage` | The five obligations (`INIT`, `INTRA`, `CALL`, `RETURN`, `TOTAL`) under which a per-node, per-context store-set claim covers every valid activation trace. | `src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy` |
| `gactivation_context_rel` | Inductive `gactivation_context_rel adm c\<^sub>0 g t c` (canonical instance `vimp.gactivation_context_rel κ ...`): a context that a valid activation trace may carry (none, one or several). Its Call rule picks an edge in `calls g` at the call node that reproduces the entered store, so no compiler uniqueness invariant is needed. The relational form of the paper's `beta`. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `gcontext_policy` | `('v, 'e, 'c) gcontext_policy`, a function `cfg_node => 'c => call_info => store => store => 'c set`: the set of callee contexts admitted for one concrete call, from call site, caller context, call info, caller store and entered store. The set may be empty or have several elements; `gcall_context_total_on` requires it non-empty for covered calls. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `context_policy_of_fun` | Embeds a functional policy (call strings) as the singleton set of the function's value. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `gcall_context_total_on` | `gcall_context_total_on cover adm g`: conditional totality -- an empty relation is rejected only where a covered call exists. It is what makes the context-insensitive collection exactly the union of the buckets (`node_collect_eq_Union_activation_collect`). Buckets form a cover, not a partition. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |
| `c\<^sub>0` | Context of the root activation (locale parameter, formerly `startcontext`), Goblint's `Spec.startcontext`. | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy` |

## Abstract interpretation

| Term | Meaning | Source |
| --- | --- | --- |
| `gabs_state` | Pointwise abstract variable environment `'k ⇒ 'a`. The analyses at machine kinds use `tabs = var_id ⇒ 'a kd` (`Nonrelational_Domain.thy`). | `src/Abstract_Interpreter/Domain/State/Nonrelational_State.thy` |
| `default_st_to_fun` | The function a carrier state represents, written `ρ⇘𝒢⇙ s` in bundle `default_st_syntax` ("its function", "the represented function"). It plays the role of `fun_rep` in HOL-IMP's `Abs_State.thy` (Concrete Semantics) for the executable `gdefault_st`, with the classifier `𝒢` choosing the local or global slot of each name. | `src/Abstract_Interpreter/Exec/State/Default_St_Transfer.thy` |
| `readback` | The abstract state an executable state represents, written `ρ⇘𝒢⇙ x` in bundle `default_st_syntax`. One overloaded constant with two instances chosen by the type of `x`: `default_st_to_fun` for a carrier state and `map_lift (default_st_to_fun 𝒢)` for a lifted one (`Default_St_Reachability.thy`). The concretization of an executable state is `γ (ρ⇘𝒢⇙ x)`. | `src/Abstract_Interpreter/Domain/State/State_Concretization.thy` |
| `exact_emptiness`, `sound_emptiness` | Whether an emptiness test `e` holds of exactly the values a concretization `γ` maps to `{}` (`e x ⟷ γ x = {}`) or only of some of them (`e x ⟹ γ x = {}`). Exact: a domain's `is_empty` (`exact_emptiness_is_empty`) and `is_empty_state` (`exact_emptiness_is_empty_state`). Sound: the D/G locale's `empty⇩V` (its contract asks only soundness; an instance may be exact), the combined state's `mcp_empty_v` (`sound_emptiness_mcp`), and `DEAD` on report points. | `src/Abstract_Interpreter/Domain/Lattice/Abstract_Domain.thy` |
| `numeric_domain` | Abstract carrier, order, and concretization obligations. | `src/Abstract_Interpreter/Domain/Lattice/Abstract_Domain.thy` |
| `part_post_solution` | Certificate with a query-membership condition and three conditions per unknown in the vars set (dependency closure, local-result bound, every contribution bounded) an equation-system valuation must satisfy; generic over the unknown/value types, so it is the shared interface between solver correctness and D/G collecting soundness, not tied to any one solver. | `vendor/td-verification/Basics_side.thy` |
| `rhs_pair` | A strategy tree's evaluation as a pair: `rhs_sides`, the contributions it publishes as a partial map (`sides_of_rhs` restricted to the keys `side_path` visits), and its value `traverse_rhs`. `part_post_solution_iff_rhs_pair` states the certificate's local and side bounds on this pair, the side-effecting constraint form of Saan's thesis. | `src/Abstract_Interpreter/Solver/Strategy_Tree_Pair.thy` |
| `TD_side_upd_rule` | Vendored verified side-effecting top-down solver, parametric in the global update rule, that the analyses instantiate (`TD_side_rule_Interp`, `Globals_Rule.thy`). It warrows every local unknown at a widening point. Its leastness theorem belongs to the separate `TD_side_mono` locale, which Voblint does not instantiate. | `vendor/td-verification/TD_side_upd_rule.thy` |
| `solve_dom_of_solve_c` | `solve_c x ≠ None` implies `solve_dom x`. With the vendored `partial_post_solution` (`solve_dom` implies `part_post_solution`) and `finite_stabl_solve` it discharges `certified_solver`. | `vendor/td-verification/TD_side_upd_rule.thy` |
| `certified_solver` | The solver contract the analysis pipeline assumes, over any equation system: in the solver's domain a solve answers a `part_post_solution` over a finite key set, and `solve_c` succeeding implies `solve_dom` (assumptions `solve_pp`, `solve_fin`, `dom_of_solve_c`). `gdg_analysis` extends it; `td_certified_solver` (`Globals_Rule.thy`) proves it for the vendored solver at every `globals_rule`. | `src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy` |

## D/G framework

| Term | Meaning | Source |
| --- | --- | --- |
| `D` | Analysis-chosen flow-sensitive fact associated with a local unknown. | `src/Abstract_Interpreter/Framework/Spec/DG_State.thy` |
| `G` | Analysis-chosen shared fact routed through global side effects. | `src/Abstract_Interpreter/Framework/Spec/DG_State.thy` |
| `gdg_spec` | D/G transfer, entry, combine, read, and publication interface. | `src/Abstract_Interpreter/Framework/Spec/DG_Spec.thy` |
| `ganalysis_contract` | Concrete-soundness obligations for a D/G instance. | `src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy` |
| resume state (`cont`) | First component `q` of an entry pair `(q, e)` that `enter♯` returns: the caller-side value the callee's result is combined with. The theories name it `cont` (`entry_pairs_cover`: `(cont, entry) ∈ set pairs`); the thesis calls it the resume state. One pair must cover both the caller store (by `cont`) and the entered store (by `entry`). | `src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy` |
| `routed_node_rhs` | D/G equation generator: one right-hand side per node and context, joining the local-edge programs, one program per call site, and the extra contribution programs (`routed_contribution_programs`; in the routed instance these are the framework's seed-reading programs, `routed_entry_seed_programs`). | `src/Abstract_Interpreter/Framework/Constraints/DG_Indexed_Generator.thy` |

### Correspondence to Goblint's `Spec` interface

Goblint's `Spec` module signature (`analyses.ml`) fixes four type components:
`D` (local abstract value), `G` (global abstract value), `C` (context), and
`V` (the analysis's own global-variable-name type, indexing `G`). The table
below states the current Voblint type or locale parameter realizing each,
and where the correspondence is inexact.

| `Spec` component | Voblint realization | Note |
| --- | --- | --- |
| `D` | Opaque `'D` carrier (`dg_state.dg_local`) | Chosen by each `gdg_spec`. The non-relational analyses use an executable state carrier; `Order_Analysis` uses a relational one. |
| `G` | Opaque `'G` carrier (`dg_state.dg_global`) | Chosen independently by each `gdg_spec`; homogeneous analyses may use the same type for `D` and `G`. See "Local/global payloads" in `docs/GOBLINT_ALIGNMENT_REGISTER.md`. |
| `C` | `'c` (type parameter of `gdg_context_activation`/`grouted_context`, `DG_Ctx_Activation.thy`, `Routed_Context.thy`) | Instantiated per context policy (call strings, entry states). |
| `V` | `'v` (the `gdg_spec` record's global-name parameter, `DG_Spec.thy`) | An analysis reaches shared state only through `man_global`/`man_sideg` at a `'v`; `mk_dg_man` embeds it into the solver's global-key type `'k` (`DG_Manager.thy`). Not the combined unknown space -- see below. |

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
| `enter♯` | `dgs_enter` (`gdg_spec` field) | Specification, `DG_Spec.thy` |
| `context♯` | `route` (locale parameter of `gdg_context_activation`, carrying the notation in `grouted_context`) | Generator, `Routed_Context.thy` |
| `combine_env♯` | `dgs_combine_env` (`gdg_spec` field) | Specification, `DG_Spec.thy` |
| `combine_assign♯` | `dgs_combine_assign` (`gdg_spec` field) | Specification, `DG_Spec.thy` |

`route`'s semantic counterpart is the relation `context_policy`
(`Activation_Trace_Context.thy`), which consumes **concrete** stores rather than
an abstract state and is left unnotated, matching `gcall_enter` -- the concrete
counterpart of `enter♯` -- staying unnotated. `grouting_adequate` is the
per-instance locale obligation: at a real call edge, some `(cont, entry)`
alternative of the spec's own `enter♯` run covers the caller and entered
stores, and `route` on that entry yields a context `routed_entry_context_rel`
admits. Goblint's `Spec.context` is a function applied per `enter`
alternative; since `enter` returns a list, one concrete call can land in
several contexts, and Voblint's proof relation models exactly that whole-call
nondeterminism (`enter` alternatives x `context`). `context` itself is an Isar
outer keyword, hence `route` -- see `docs/GOBLINT_ALIGNMENT_REGISTER.md`.

### `sigma` / `sg`

Both fixed in `gdg_context_activation` (`DG_Ctx_Activation.thy`) and genuinely
different objects, not naming duplication:

| Term | Meaning |
| --- | --- |
| `sigma` | Raw `dg_state` reader over the unknown space `pp \<times> 'c + 'k` -- the vendored solver's own solution shape (`sigma :: pp \<times> 'c + 'k => ('D, 'G) dg_state`). |
| `sg` | The reader an analysis publishes over the same unknowns (`sg :: pp \<times> 'c + 'k => 'M`), read as stores through `γ⇩M`. |

The locale assumption `sg_cov` ties them: at a covered key,
`γ⇩M (sg (Inl (v, c)))` is `γ⇩D⇩G` of `sigma`'s local slot against the global
environment `genv global_of sigma`, and `sg_uncov` makes it empty off the solved keys.
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
`X.cover v c`. `gactivation_coverage` is only interpreted inside proofs, so printing
mode is safe there. The other locales have theory-level interpretations, so
their abbreviations are input-only and interpreted facts keep the explicit
terms. The anonymous context fixing `p` in `DG_Analysis.thy` adds the
input-only `pgs` for `pglob p`; it is not a locale and stays out of
the table.

## Source-facing endpoints

| Term | Meaning | Source |
| --- | --- | --- |
| `reaching` | `reaching ds p v = node_collect (kenv_of ds) (elab_cfg p ds) (init_stores (kenv_of ds)) v`: the stores every public theorem is stated over. | `src/Executable_Surface/CLI/Analysis_Config.thy` |
| `report` | What `run_voblint` returns inside `Analysed`: the states per point and context, the check rows and the arithmetic diagnostics, an instance of `analysis_report`. Read through `report_states_at`, `PROVED`, `REFUTED`, `DEAD` and `SAFE`. Termination is not a premise of its theorems: an answer exists only where the executable solve returned. | `src/Executable_Surface/CLI/Run_Report.thy`, `Analysis_Report.thy` |
| `report_sound` | Every guarantee a report gives, as one predicate; `report_run_sound` proves it for every answered run. | `src/Executable_Surface/CLI/Run_Report.thy` |
| `source_reaches_node_collect` | Compiler and activation-collecting bridge: a `pstep` run of an accepted program is simulated at a node whose `node_collect` holds its store. | `src/Program_Model/Compile/Source_To_Trace.thy`, `src/Analyses/Shared/Result/Source_Activation_Sound.thy` |
| `gfun_route_result_node_sound` | The endpoint for a route that is a function of the call site: a terminating solve bounds `node_collect` at every node by the union over contexts of the published states (with `gfun_route_activation_collect_sound_of_terminates` and `gfun_route_report_proved_sound`). | `src/Analyses/Shared/Result/DG_Live_Unknowns.thy` |
