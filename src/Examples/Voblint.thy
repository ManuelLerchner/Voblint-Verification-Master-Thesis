(* SPDX-License-Identifier: MIT *)

section \<open>Voblint: a verified abstract interpreter for VIMP\<close>

theory Voblint
  imports
    "Voblint_VIMP.VIMP_Syntax"
    "Voblint_VIMP.VIMP_Expr"
    "Voblint_VIMP.VIMP_Globals"
    "Voblint_VIMP.VIMP_Proc"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_CFG.CFG_Def"
    "Voblint_CFG.VIMP_Proc_to_CFG"
    "Voblint_CFG.CFG_Local_Trace"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Core.Abstract_Domain"
    "Voblint_Core.Constraint_System"
    "Voblint_Core.Constraint_System_Sound"
    "Voblint_Core.Abstract_Numeric_Queries"
    "Voblint_Core.Abstract_Checks"
    "Voblint_Analysis.Sign_Domain"
    "Voblint_Analysis.Sign_Ctx_None_Sound"
    "Voblint_Analysis.Sign_Checks"
    "Voblint_Analysis.Interval_Domain"
    "Voblint_Analysis.Interval_Ctx_None_Sound"
    "Voblint_Analysis.Interval_Checks"
    "Voblint_Analysis.Interval_Exec_Sound"
    "Voblint_Core.DG_Framework"
    "Voblint_Core.DG_Soundness"
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.DG_Ctx_Activation"
    "Voblint_Core.Exec_St"
    "Voblint_Core.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_Exec_Sound"
    Exec_Sign_DG_Run
    Example_Checks_Store_Only
    Example_Interval_Checks_Store_Only
    Example_Parity_Checks_Store_Only
    Example_Interval_DG_Flagship
    "Voblint_Soundness.Source_Activation_Sound"
    Example_Interval_DG_Ctx_Collect
    Example_Interval_DG_EntryState_Collect
    Example_Interval_DG_CallString_K1
    Example_Interval_DG_CallString_K2
    Example_Sign_DG_CallString_K1
    Example_Sign_DG_CallString_K2
    Call_String_Solver_Refinement_Seeded
    Example_Interval_Source_Ctx
    Example_Inc_Proc
    Example_Side_Execute
    Example_Side_Branch_Calls
    Example_Side_Proc_Global
    Example_Proc_Call
    Example_Interval_Loop_Coverage
    Example_Guard_Refinement
    Example_Random_Sign_Showcase
    Example_Relational_DG_Demo
    Example_Strategy_Tree_Demo
    "Voblint_CLI.Sign_Entry"
    "Voblint_CLI.Analyse_Dispatch"
    "Voblint_CLI.State_Report_GraphViz"
begin

text \<open>
  \<^verbatim>\<open>
____   ____   ___.   .__  .__        __
\   \ /   /___\_ |__ |  | |__| _____/  |_
 \   Y   /  _ \| __ \|  | |  |/    \   __\
  \     (  <_> ) \_\ \  |_|  |   |  \  |
   \___/ \____/|___  /____/__|___|  /__|
                   \/             \/
  \<close>
\<close>

section \<open>Certified pipeline\<close>

text \<open>
  \<^bold>\<open>What this development proves.\<close>  An end-to-end soundness proof for a Goblint-style abstract
  interpreter for VIMP, machine-checked from the source operational semantics to the
  \<^emph>\<open>computed\<close> analysis result.  The whole pipeline, each arrow a theorem:

  \<^verbatim>\<open>
    source execution
      -> procedure-aware CFG execution
      -> activation-local trace
      -> collecting semantics
      -> D/G equation system
      -> verified side-effecting solver
      -> abstract post-solution
      -> source-level soundness
  \<close>

  Each arrow is justified independently.  Compiler simulation preserves source
  behavior.  Forgetful trace projections introduce no abstract states.  Transfer,
  join, routing, and widening occur only on the abstract side and are justified by
  containment in the corresponding concretization.
\<close>

section \<open>Complete end-to-end analyses\<close>

text \<open>
  Every theory below compiles a source program, generates its D/G equation system,
  \<^emph>\<open>computes\<close> a solution with the verified solver (\<open>by eval\<close>), and closes with a soundness
  theorem over that computed result --- no step is a precision demo, a raw execution
  witness, or left as an unclosed obligation.  \<^bold>\<open>7. Examples and witnesses\<close> below holds
  everything else: parallel-capability checks, precision witnesses, tooling, and research
  demonstrations. Two capability axes, each with its own flagships.
\<close>

subsection \<open>Basic capability: one domain, the whole pipeline, monovariant\<close>

text \<open>
  \<^item> \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_Flagship}\<close> --- the Interval flagship: a
    counting loop, compiled, solved, and certified. \<^verbatim>\<open>flagship_source_run_sound\<close> bounds
    \<^emph>\<open>actual source runs\<close>.
  \<^item> \<^bold>\<open>@{theory Voblint_Examples.Exec_Sign_DG_Run}\<close> --- the Sign flagship, same pipeline, same
    always-join solver. \<^verbatim>\<open>dgEx_source_run_sound\<close> is the same source-run bound.
\<close>

subsection \<open>Context sensitivity: the axis issue \<open>#66\<close> is about\<close>

text \<open>
  Three storage policies, each certified against the same activation-indexed semantics
  and by the same soundness shape --- \<^const>\<open>activation_collect\<close> bounded at every
  \<open>(node, context)\<close> pair.  They differ only in what a context \<^emph>\<open>is\<close>.

  \<^item> \<^bold>\<open>Monovariant\<close> --- no context: one abstract state per program point.
    \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_IP_Flagship}\<close> analyses \<open>twice\<close>, whose
    single procedure is called from two sites with different arguments, under one shared
    entry state, and \<^verbatim>\<open>twice_collect_sound\<close> bounds the result.  This is the baseline the
    two policies below sharpen.
  \<^item> \<^bold>\<open>Entry state\<close> --- the context is the entered abstract value of the callee's declared
    formals (partial tabulation, \<^cite>\<open>SeidlEtAl2026\<close> Example 8).
    \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_Ctx_Collect}\<close> instantiates the production
    entry-state analysis on that same \<open>twice\<close> program: the two calls route to the distinct
    contexts \<open>[3,3]\<close> and \<open>[10,10]\<close> and keep their entry and return values apart, where the
    monovariant baseline joins them.  \<^verbatim>\<open>twice_activation_collect_sound\<close> is the bound.
    \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_EntryState_Collect}\<close> is the complementary
    witness on an unconstrained argument, where one wide context covers infinitely many
    concrete entries rather than separating two.
  \<^item> \<^bold>\<open>Call string\<close> --- the context is a bounded record of the call sites traversed to reach
    the activation (\<^cite>\<open>SeidlEtAl2026\<close> Example 7 at \<open>k = 1\<close>).
    \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_CallString_K1}\<close> and
    \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_CallString_K2}\<close> run one \<open>nest\<close> program at
    \<open>k = 1\<close> and \<open>k = 2\<close>, so the pair also measures what raising the bound buys.  This policy
    needed \<open>enterc\<close> widened to see the call site (issue \<open>#66\<close>, G1) to be expressible at all.

  \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_Source_Ctx}\<close> is the sharpest statement of the
  entry-state route: bound against \<^emph>\<open>actual source runs\<close> at each activation's own context,
  not just the collecting semantics.
\<close>

subsection \<open>Activation-local concrete semantics\<close>

text \<open>
  \<^const>\<open>valid_ltr\<close> represents one procedure activation and its ancestry.
  \<^const>\<open>Root\<close> starts main, \<^const>\<open>Call\<close> records an immediate caller, and
  \<^const>\<open>Resume\<close> continues that caller after its callee reaches the matching
  result node.  Structural caller links distinguish nested and recursive activations
  without placing an unbounded stack in CFG nodes.

  \<^const>\<open>ltr_collect\<close> forgets the activation structure and collects stores by
  node, while \<^const>\<open>activation_collect\<close> keys the same collection by the
  structural activation context.  Both contain only stores from valid local traces.
\<close>
 
subsection \<open>Procedure-aware source and CFG\<close>

text \<open>
  Procedures receive fresh local state and inherited globals.  A call frame stores
  the caller state and optional destination.  Explicit return enters unwinding,
  which skips the remaining commands in that activation and resumes the immediate
  caller.  Main has no caller and accepted programs therefore require it to terminate
  by ordinary fall-through.

  CFGs use explicit \<^const>\<open>FunctionEntry\<close> and \<^const>\<open>FunctionResult\<close> nodes.
  The \<^const>\<open>intra\<close> relation carries local transfers and matching returns.  The
  \<^const>\<open>calls\<close> relation carries call-site, callee-entry, and continuation data.
  Compiler certificates expose the node ownership and range separation needed by
  the source/CFG simulation.
\<close>

subsection \<open>Equations, D/G routing, and solver\<close>

text \<open>
  Every node equation joins ordinary predecessor flow, callee-entry flow, and
  caller/callee combination.  Executable equations and their soundness proof use
  the same contribution families.

  The D/G interface separates local flow-sensitive facts from information published
  through global side effects.  Analyses choose the two carriers, routing operations,
  and context keys.  Sign, Interval, and mixed Sign/Interval instances share the
  verified side-effecting top-down solver and the collecting-soundness infrastructure.
\<close>

subsection \<open>Executable witnesses\<close>

text \<open>
  The interval and Sign flagships compile source programs, generate their D/G
  equations, execute the verified solver, and certify the computed post-solutions.
  The \<open>twice\<close> program calls one procedure from two sites; its activation-sensitive
  interval analysis keeps the two call contexts separate.  Recursive examples test
  structural activation nesting independently of that repeated-call witness.

  GraphViz exporters present procedure entries, results, calls, resumes, and computed
  abstract states without changing the certified equation system.

  The proof is layered across the six-session dependency chain. A separate
  downstream codegen session owns executable exports. The index below separates
  the proof spine from executable frontends, DOT exporters, and research witnesses.

  \<^bold>\<open>1. Language.\<close> VIMP syntax, small-step semantics, and the procedural extension
  (scopes, calls, restores).
    \<^item> @{theory Voblint_VIMP.VIMP_Syntax} --- AST, variable names, countability.
    \<^item> @{theory Voblint_VIMP.VIMP_Expr} --- expression evaluation and small-step semantics.
    \<^item> @{theory Voblint_VIMP.VIMP_Globals} --- global variable names and initial store.
    \<^item> @{theory Voblint_VIMP.VIMP_Proc} --- procedural extension: \<^verbatim>\<open>Scope\<close>, \<^verbatim>\<open>Call\<close>, \<^verbatim>\<open>Restore\<close>.
    \<^item> @{theory Voblint_VIMP.VIMP_Notation} --- \<^verbatim>\<open>\<lbrakk> ... \<rbrakk>\<close> quotation bracket for examples.
    \<^item> @{theory Voblint_VIMP.VIMP_Source_Print} --- source rendering used by the GraphViz tooling.

  \<^bold>\<open>2. Control-flow graph and concrete semantics.\<close> CFG construction, transfer primitives, and
  the activation-local trace semantics it carries.
    \<^item> @{theory Voblint_CFG.CFG_Def} --- CFG node/edge types, predecessor enumeration, finite code lists.
    \<^item> @{theory Voblint_CFG.VIMP_Proc_to_CFG} --- \<^verbatim>\<open>compile_prog\<close>: VIMP programs to interprocedural CFGs.
    \<^item> @{theory Voblint_CFG.CFG_Transfer} --- the concrete store transformers shared by the semantics: \<^verbatim>\<open>edge_step\<close>, \<^verbatim>\<open>edge_collect\<close>, \<^verbatim>\<open>edges_collect\<close>, \<^verbatim>\<open>combine_collect\<close>, \<^verbatim>\<open>call_enter_store\<close>.
    \<^item> @{theory Voblint_CFG.CFG_Local_Trace} --- the call-structured activation-local trace \<^const>\<open>valid_ltr\<close> (\<^verbatim>\<open>Root\<close>/\<^verbatim>\<open>Call\<close>/\<^verbatim>\<open>Resume\<close>), the projections \<^const>\<open>ltr_collect\<close> / \<^const>\<open>activation_collect\<close>, and the correlation-preserving interface \<^locale>\<open>ltr_gamma\<close> (with the keystone \<^verbatim>\<open>ltr_collect_semantic_postfix\<close>).
    \<^item> @{theory Voblint_CFG.CFG_Prune} --- interprocedural graph reachability (\<^const>\<open>cfg_reaches\<close>) and the backward exit cone (\<^const>\<open>cone\<close>); these feed the cone guard.  No graph is pruned: the cone restriction lives in the abstract concretization, not in a semantics-altering transformation.

  \<^bold>\<open>3. Analysis spine.\<close> Abstract domains, equation systems, and the TD_side solver bridge; every
  generic endpoint concludes over the trace projections.
    \<^item> @{theory Voblint_Core.Abstract_Domain} --- \<^verbatim>\<open>sound_domain\<close>, lifted state concretization, display support.
    \<^item> @{theory Voblint_Core.Constraint_System} --- the transfer interface \<^verbatim>\<open>domain_transfer\<close>, its soundness locale \<^verbatim>\<open>sound_transfer\<close>, and the per-unknown side-effecting constraint \<^verbatim>\<open>se_constraint_holds\<close>.
    \<^item> @{theory Voblint_Core.Constraint_System_Sound} --- per-edge transfer soundness (\<^verbatim>\<open>edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a \<sigma>\<rbrakk>\<close>) and its \<^verbatim>\<open>EA_Check\<close> companion, the dispatch-point facts \<^theory>\<open>Voblint_Core.DG_Soundness\<close>'s \<^verbatim>\<open>step_sound\<close>/\<^verbatim>\<open>combine_sound\<close> obligations are discharged against.
    \<^item> @{theory Voblint_Core.State_Restriction} --- the local/global restriction algebra the routed spine reassembles states with.
    \<^item> @{theory Voblint_Core.Solver_Mono} --- \<^verbatim>\<open>threefold_mono\<close>: the monotonicity obligation the vendored solver's post-solution theorem takes.

  \<^bold>\<open>3b. Check discharge.\<close> A domain-generic, sound (incomplete) decision
    procedure for compiled \<^verbatim>\<open>__voblint_check(...)\<close> conditions, discharged
    against the computed abstract solver environment at each check's own
    node --- no store is forwarded between check nodes or to the procedure
    exit.
    \<^item> @{theory Voblint_Core.Abstract_Numeric_Queries} --- the generic
      \<^locale>\<open>abstract_numeric_queries\<close> interface (entailment/refutation of
      \<open><\<close>/\<open>=\<close> over an abstract numeric value) and its derivation from any
      \<^locale>\<open>backward_domain\<close> instance's own narrowing operators
      (\<^locale>\<open>derived_less_queries\<close>, \<^locale>\<open>derived_eq_true_from_less\<close>,
      \<^locale>\<open>derived_eq_false_from_intersection\<close>) --- a sound default a concrete
      domain may override with sharper, hand-tuned predicates.
    \<^item> @{theory Voblint_Core.Abstract_Checks} --- \<^locale>\<open>abstract_expression_domain\<close>
      and \<^locale>\<open>abstract_check_domain\<close>: mutually recursive
      \<^verbatim>\<open>check_true\<close>/\<^verbatim>\<open>check_false\<close> over \<^typ>\<open>exp\<close>, the three-way
      \<^verbatim>\<open>check_result\<close> classification (\<^verbatim>\<open>Check_Proved\<close>/\<^verbatim>\<open>Check_Refuted\<close>/
      \<^verbatim>\<open>Check_Unknown\<close>), and the node-indexed bridge to
      \<^const>\<open>checks_proven\<close>.
    \<^item> @{theory Voblint_Analysis.Sign_Checks} --- the Sign instance: derived
      numeric queries (read off \<^const>\<open>inv_less_sign\<close>/\<^const>\<open>inv_eq_sign\<close>/
      \<^const>\<open>meet_sign\<close>), no hand-built comparison tables.
    \<^item> @{theory Voblint_Analysis.Interval_Checks} --- the Interval instance:
      specialized bound-comparison queries (\<^const>\<open>interval_less_true\<close> and
      siblings, \<open>Interval_Numeric_Queries\<close>). The backward-domain default derives
      equality refutation through \<^const>\<open>intersect_ivl\<close>, whose canonical empty
      result is independent of the raw lattice \<^const>\<open>inf\<close>.

  \<^bold>\<open>4. Concrete domains.\<close> Domain instances used by the proof spine and examples.
    \<^item> @{theory Voblint_Analysis.Sign_Domain} --- Sign lattice, transfer functions, soundness, monotonicity, display instance.
    \<^item> @{theory Voblint_Analysis.Sign_Ctx_None_Sound} --- Sign at the routed D/G spine, over \<^const>\<open>ltr_collect\<close>.
    \<^item> @{theory Voblint_Analysis.Interval_Domain} --- interval lattice, widening, transfer functions, soundness, monotonicity.
    \<^item> @{theory Voblint_Analysis.Interval_Ctx_None_Sound} --- Interval at the routed D/G spine, over \<^const>\<open>ltr_collect\<close>.

  \<^bold>\<open>4b. The D/G interface spine.\<close> The native, carrier-opaque Goblint-\<^verbatim>\<open>Spec\<close> interface
    (independent flow-sensitive local domain \<^verbatim>\<open>D\<close> and flow-insensitive global domain \<^verbatim>\<open>G\<close>),
    the canonical context-sensitive backbone.
    \<^item> @{theory Voblint_Core.DG_Framework} --- the \<^verbatim>\<open>dg_spec\<close> record (\<^verbatim>\<open>step : D => G => G x D\<close>), the \<^verbatim>\<open>dg_state\<close> copy lattice, the seeded keyed generator.
    \<^item> @{theory Voblint_Core.DG_Soundness} --- native heterogeneous soundness over opaque carriers (\<^verbatim>\<open>sound_dg_spec\<close>); the shared closure obligations \<^verbatim>\<open>dg_postfix_gamma_{entry,edge,combine}\<close> feed the trace endpoint \<^verbatim>\<open>dg_post_solution_collect_sound_ltr\<close>.
    \<^item> @{theory Voblint_Analysis.Sign_DG} --- Sign as a diagonal \<^verbatim>\<open>sound_dg_spec\<close> instance.
    \<^item> @{theory Voblint_Analysis.Interval_DG} --- Interval as a diagonal instance (\<^verbatim>\<open>ivl_dg_post_solution_collect_sound\<close>, over \<^const>\<open>ltr_collect\<close>).

  \<^bold>\<open>4c. Activation-local certification.\<close> The concrete object the context-sensitive soundness
    rides: one trace per activation, with a stable call-only context.
    \<^item> @{theory Voblint_Core.Activation_Backbone} --- the generic \<^verbatim>\<open>activation_collect_sound\<close>: over \<^const>\<open>valid_ltr\<close>, four obligations \<^verbatim>\<open>ENTRY_G\<close>/\<^verbatim>\<open>EDGE\<close>/\<^verbatim>\<open>SEED_G\<close>/\<^verbatim>\<open>COMB\<close> (\<^verbatim>\<open>COMB\<close> at the caller context) bound \<^const>\<open>activation_collect\<close> at every \<^verbatim>\<open>(node, context)\<close>.
    \<^item> @{theory Voblint_Core.DG_Ctx_Activation} --- DG-native discharge of those four obligations from a \<^verbatim>\<open>sound_dg_spec\<close> post-solution, so a computed D/G solution certifies the activation collecting.

  \<^bold>\<open>5. Executable frontend.\<close> Finite-map state representation and certified execution.
    \<^item> @{theory Voblint_Core.Exec_St} --- executable abstract-state maps for code generation.
    \<^item> @{theory Voblint_Core.Exec_Refinement} --- commutation bridge from executable states to function states.
    \<^item> @{theory Voblint_Core.Exec_DG_Bridge} --- executable transport for the D/G spine (\<^verbatim>\<open>fun_of_dg_st\<close>, \<^verbatim>\<open>dg_gen_of\<close>, \<^verbatim>\<open>part_post_solution_dg_st_to_abs\<close>): the verified solver \<^emph>\<open>runs\<close> on D/G equations.
    \<^item> @{theory Voblint_Analysis.Sign_Exec} --- executable Sign transfer functions.
    \<^item> @{theory Voblint_Analysis.Sign_Exec_Sound} --- the native D/G runtime API for Sign: \<open>analyse_sign_eqs\<close>, \<open>analyse_sign\<close>, \<open>analyse_sign_env\<close>.
    \<^item> @{theory Voblint_Analysis.Interval_Exec_Sound} --- the Interval counterpart:
      \<open>analyse_interval_dg_eqs_for\<close>/\<open>analyse_interval_dg_for\<close>/\<open>analyse_interval_dg_env_for\<close>,
      plus the join and per-origin solver-choice siblings.

  \<^bold>\<open>6. End-to-end theorems.\<close> Headline soundness and the source bridge.
    \<^item> @{theory Voblint_Soundness.Source_Activation_Sound} --- the source-adequacy bridge: a reachable VIMP source configuration produces a \<^const>\<open>valid_ltr\<close> trace (\<^verbatim>\<open>source_run_has_ltr\<close>), bounded at its activation context (\<^verbatim>\<open>source_activation_sound\<close>) and monovariantly (\<^verbatim>\<open>source_reaches_ltr_collect\<close>).

  \<^bold>\<open>7. Examples and witnesses.\<close> Executable demos, precision witnesses, tooling --- the
    complete end-to-end analyses (\<open>Example_Interval_DG_Flagship\<close>, \<open>Exec_Sign_DG_Run\<close>,
    \<open>Example_Interval_DG_Ctx_Collect\<close>, \<open>Example_Interval_DG_EntryState_Collect\<close>,
    \<open>Example_Interval_Source_Ctx\<close>) are indexed separately, above.
    \<^item> @{theory Voblint_Examples.Example_Checks_Store_Only} --- \<open>__voblint_check(...)\<close>
      discharged against a computed Sign post-solution, node-locally: one check
      proved, one refuted (a genuine bug, not merely unproven), one unknown.
    \<^item> @{theory Voblint_Examples.Example_Parity_Checks_Store_Only} --- the same
      program, but with a parity domain instead of Sign.
    \<^item> @{theory Voblint_Examples.Example_Interval_Checks_Store_Only} --- the Interval
      counterpart, inside a two-sided bound guard (\<open>0 < x \<and> x < 10\<close>) so the
      checks exercise Interval's numeric bounds, not just its sign; includes a
      precision comparison showing a bound Interval proves outright that Sign's
      \<^term>\<open>SPos\<close> alone classifies \<^term>\<open>Check_Unknown\<close>.
    \<^item> @{theory Voblint_Examples.Example_Inc_Proc} --- shared global-increment procedure witness.
    \<^item> @{theory Voblint_Examples.Example_Side_Execute} --- minimal certified Sign IP example with annotated CFG DOT.
    \<^item> @{theory Voblint_Examples.Example_Side_Branch_Calls} --- branching procedure called twice; flow-sensitive locals, flow-insensitive globals.
    \<^item> @{theory Voblint_Examples.Example_Side_Proc_Global} --- Sign IP analysis on the shared global-increment call.
    \<^item> @{theory Voblint_Examples.Example_Proc_Call} --- concrete-semantics witness for \<^verbatim>\<open>inc\<close> and \<^verbatim>\<open>sqr\<close> procedures communicating through a global, and their compiled interprocedural CFG; a certified Sign analysis of a shared-global increment call is @{theory Voblint_Examples.Example_Side_Proc_Global}.
    \<^item> @{theory Voblint_Examples.Example_Interval_Loop_Coverage} --- backward guard-refinement precision witness for a bounded loop's body entry; the certified computed bound at the loop head is @{text "Exec_Ivl_Run"}'s.
    \<^item> @{theory Voblint_Examples.Example_Guard_Refinement} --- backward guard refinement precision witness.
    \<^item> @{theory Voblint_Examples.Example_Random_Sign_Showcase} --- issue \<open>#43\<close>'s nondeterministic
      \<open>x := __voblint_nondet_int()\<close>, closed end to end: \<^const>\<open>special_sign\<close> forgets \<open>x\<close> to \<^term>\<open>STop\<close>, a
      guard on \<open>x\<close> narrows each branch, and the branches join to \<^term>\<open>SNonNeg\<close> rather than
      \<^term>\<open>STop\<close>. Computed by \<^const>\<open>analyse_sign_result_for\<close> and the vendored TD solver, not asserted
      by hand; \<open>random_guard_exit_sound\<close> over-approximates every reachable exit state and
      \<open>random_guard_exit_y_nonneg\<close> closes the issue's \<open>y \<ge> 0\<close> claim there.
      \<open>random_guard_run_42\<close> is a non-vacuity witness at the source semantics: fixing the
      random draw at \<open>v = 42\<close>, \<^const>\<open>pcompletes\<close> derives an actual terminating run
      reaching \<open>y = 42\<close>.
    \<^item> @{theory Voblint_Examples.Example_Interval_DG_CallString_K1} --- the \<open>nest\<close> program,
      computed and certified at a 1-call-string context
      (\<^verbatim>\<open>nest_1_activation_collect_sound\<close>): \<open>main\<close> calls \<open>f\<close> from two sites and \<open>f\<close>
      calls \<open>g\<close> from one, so a 1-call-string cannot separate \<open>g\<close>'s two activations.
    \<^item> @{theory Voblint_Examples.Example_Interval_DG_CallString_K2} --- the same program at a
      2-call-string context (\<^verbatim>\<open>nest_2_activation_collect_sound\<close>), which does separate them.
    \<^item> @{theory Voblint_Examples.Example_Sign_DG_CallString_K1} --- the Sign counterpart of the
      \<open>nest\<close> pair, computed by the plain-join solver (\<^verbatim>\<open>TD_side_always_join_Interp\<close>) rather
      than warrowing: Sign is finite, so no widening is needed and the computed solution is
      exact. \<^verbatim>\<open>sign_nest_1_activation_collect_sound\<close> is the same soundness shape at a
      1-call-string context, where \<open>g\<close>'s two activations (entered with \<open>SPos\<close> and \<open>SNeg\<close>)
      collapse and join to \<open>STop\<close>.
    \<^item> @{theory Voblint_Examples.Example_Sign_DG_CallString_K2} --- the 2-call-string sibling
      (\<^verbatim>\<open>sign_nest_2_activation_collect_sound\<close>), which keeps \<open>g\<close>'s two activations separate
      at \<open>SPos\<close> and \<open>SNeg\<close>. Because Sign is a finite lattice with an exact computed solution,
      this pair supports a genuine strict-precision witness that
      \<open>Call_String_Solver_Refinement_Seeded\<close>'s refinement argument does not state:
      \<^verbatim>\<open>sign_k2_strictly_more_precise_than_k1_at_g\<close> proves
      the 2-call-string value at \<open>g\<close>'s entry is strictly below the 1-call-string \<open>STop\<close> merge in
      the Sign order, for both activations, \<^emph>\<open>computed and compared\<close> rather than argued
      abstractly.
    \<^item> @{theory Voblint_Examples.Call_String_Solver_Refinement_Seeded} --- a solver-level
      refinement witness, not a source-level soundness theorem: truncates and joins the
      computed 2-call-string solution down to a finite 1-call-string lower bound
      (\<^verbatim>\<open>proj_P\<close>), seeds the 1-call-string equations with it (\<^verbatim>\<open>seed_rhs\<close>), and runs the
      same unmodified verified solver. The generic seeded-solve theorem
      (\<^verbatim>\<open>post_solution_of_seeded\<close>) then gives, with no per-node case analysis, both that the
      seeded solution is a \<^verbatim>\<open>part_post_solution\<close> of the plain 1-call-string equations and
      that it dominates the projected 2-call-string information on every local and
      global/seed key (\<^verbatim>\<open>nest_1_seeded_refinement\<close>).
    \<^item> @{theory Voblint_Examples.Example_Relational_DG_Demo} --- an execution
      witness, not a soundness-certified result: a compiled full-program
      `if (x < y) { z := 1 } else { z := 0 }` runs through the *same*
      \<^verbatim>\<open>dg_gen_of\<close>/vendored-solver pipeline as Sign/Interval, this time
      over \<^verbatim>\<open>Voblint_Analysis.Rel_Order_Domain\<close>'s non-\<^verbatim>\<open>abs_state\<close>
      relational carrier; the computed result is compared against
      Interval's on the identical program and rendered, raw and
      analysis-annotated, via GraphViz.

  \<^bold>\<open>8. Tooling.\<close> Theories outside the core proof spine.
    \<^item> \<^bold>\<open>Named global unknowns\<close> --- a keyed global family is the routed D/G
      context's own \<open>gkey\<close>, and \<^const>\<open>dep_aux\<close> pins what a per-edge tree reads:
      @{thm dep_aux_dg_edge_tree} names the source local unknown and the one
      global slot, nothing else.
    \<^item> \<^bold>\<open>DOT rendering\<close> --- \<^const>\<open>raw_cfg_dot_lit\<close> and \<^const>\<open>state_report_dot\<close>
      (@{theory Voblint_CLI.State_Report_GraphViz}) have no Isabelle-side witness of
      their own: rendering asserts nothing that a \<^verbatim>\<open>writeln\<close> could check, so the
      fixtures under \<^verbatim>\<open>tests/regression/\<close> carry it instead --- \<^verbatim>\<open>08-tooling\<close> for
      \<^verbatim>\<open>--dot\<close>, \<^verbatim>\<open>13-full-state-dot\<close> for the per-node state labels, and
      \<^verbatim>\<open>11-graph-snapshot\<close> for golden cluster/node/edge snapshots including a
      recursive procedure. Those compare output; a build-time render only proves
      it did not crash.
    \<^item> \<^bold>\<open>Related demo:\<close> @{theory Voblint_Examples.Example_Strategy_Tree_Demo} ---
      \<^type>\<open>strategy_tree\<close> as a small dependency/effect language on its own,
      independent of any abstract domain: a Fibonacci equation tree built with
      \<^const>\<open>answer\<close> and \<^const>\<open>seqcomp_tree\<close>, run with \<open>traverse_rhs\<close>.

  \<^bold>\<open>9. Executable code generation.\<close> A runtime-program entry point per domain,
    reusing the exact native D/G pipeline behind \<open>4b\<close>/\<open>5\<close> above rather than a
    parallel one, exported to OCaml.
    \<^item> @{theory Voblint_CLI.Sign_Entry} --- \<^verbatim>\<open>analyse_sign\<close>
      takes an arbitrary \<^typ>\<open>imp_prog\<close> at runtime (not a fixed example
      program) and reuses \<^verbatim>\<open>unit_dg_exec_analysis\<close>'s own \<^verbatim>\<open>run_source_sound\<close>
      and \<^verbatim>\<open>collect_sound\<close> (@{theory Voblint_Soundness.Run_Analysis_Sound})
      for its soundness theorems. \<^verbatim>\<open>analyse_sign_report\<close> classifies every
      compiled \<^verbatim>\<open>__voblint_check(...)\<close> against that same computed
      post-solution via \<^locale>\<open>abstract_check_domain\<close>'s
      \<^verbatim>\<open>classify_checks\<close>, so the report and the soundness theorem share one
      computation, not two.
    \<^item> @{theory Voblint_CLI.Interval_Entry} --- \<^verbatim>\<open>analyse_interval_dg\<close>/
      \<^verbatim>\<open>analyse_interval_td_report\<close>, the Interval counterpart production \<^verbatim>\<open>analyse\<close> actually
      dispatches to, built the same way on \<^verbatim>\<open>base_dg_exec_analysis\<close>'s own \<^verbatim>\<open>run_source_sound\<close>/
      \<^verbatim>\<open>collect_sound\<close>. \<^verbatim>\<open>Interval_Checks\<close> additionally carries \<^verbatim>\<open>analyse_interval_report\<close>/
      \<^verbatim>\<open>analyse_interval_report_per_origin\<close>, the always-join and per-origin update-rule siblings
      \<^verbatim>\<open>analyse_with_solver\<close> (@{theory Voblint_CLI.Analyse_Dispatch}) compares against this
      same production default on the identical equation system, each with its own soundness
      theorems proved the same way, in @{theory
      Voblint_CLI.Interval_Entry}.
    \<^item> @{theory Voblint_CLI.Analyse_Dispatch} --- \<^verbatim>\<open>analyse\<close>
      dispatches on \<^verbatim>\<open>analysis_domain\<close> (\<^verbatim>\<open>Sign_Analysis\<close>/\<^verbatim>\<open>Interval_Analysis\<close>)
      to the two domains' report functions; both already share the observable
      \<^verbatim>\<open>check_report_entry list\<close> result type
      (@{theory Voblint_Core.Abstract_Checks}), so the dispatcher adds no new
      proof. \<^verbatim>\<open>dispatch_demo_interval_precise\<close> computes
      (\<^verbatim>\<open>by eval\<close>) that program's report, and the executable corpus under
      \<^verbatim>\<open>tests/regression/\<close> runs the same analysis through the generated CLI
      for both domains, each settling both checks precisely --- Interval at
      numeric-bound granularity, Sign at sign granularity. \<^verbatim>\<open>Interval_Analysis_TD\<close>
      (warrowing) is deliberately not a
      branch here: it has no soundness theorem yet
      (@{theory Voblint_Analysis.Interval_Exec_Sound}).

      A downstream \<open>Voblint_Codegen\<close> session exports \<open>analyse\<close>, the AST
      constructors, and \<open>imp_prog.make\<close> to OCaml, so external code can build a
      fresh \<open>imp_prog\<close> and call \<open>analyse\<close> without touching Isabelle. The
      generated source is tracked under \<open>codegen/generated/\<close> (regenerated
      by \<open>pixi run codegen\<close>; \<open>pixi run codegen-check\<close> fails if it has
      drifted from the export declarations). A hand-written OCaml driver under
      \<open>codegen/regression/\<close> (\<open>pixi run codegen-regression\<close>) constructs
      that same program purely through the exported constructors, calls
      \<open>analyse\<close>, and checks the result against the values
      \<open>dispatch_demo_interval_precise\<close> already proves --- so the generated
      OCaml is checked against the same theorem as the Isabelle source, not
      merely assumed to match it. That driver additionally pins the Sign
      verdict and several call/global shapes for which no Isabelle-side
      \<open>eval\<close> witness is kept, since the executable corpus under
      \<open>tests/regression/\<close> covers the same programs far more cheaply.


      \<^bold>\<open>What the proof attaches to.\<close> \<^verbatim>\<open>export_code\<close> translates the executable
      equations of the HOL constant \<^verbatim>\<open>analyse\<close> and everything it transitively
      calls --- \<^verbatim>\<open>analyse_sign_report\<close>/\<^verbatim>\<open>analyse_interval_td_report\<close> down to
      the warrowing solver itself. It is not proving one function and exporting
      a different, hand-written one: the generated \<^verbatim>\<open>analyse\<close> is a translation
      of the same equations \<^verbatim>\<open>analyse_sign_report_sound_proved\<close>/\<^verbatim>\<open>_refuted\<close>
      and \<^verbatim>\<open>analyse_interval_td_report_sound_proved\<close>/\<^verbatim>\<open>_refuted\<close> are proved
      about. The proof term itself is erased by code generation, as for any
      \<^verbatim>\<open>export_code\<close> use --- what survives is that the exported constant
      \<^emph>\<open>is\<close> the proved one, not an assumed match to it.
      \<^verbatim>\<open>analyse_interval_proved_sound\<close>/\<^verbatim>\<open>analyse_interval_refuted_sound\<close> and
      \<^verbatim>\<open>analyse_sign_proved_sound\<close>/\<^verbatim>\<open>analyse_sign_refuted_sound\<close> restate those
      theorems directly over \<^verbatim>\<open>analyse\<close>, so this connection does not require
      unfolding the dispatcher's \<^verbatim>\<open>fun\<close> equations by hand.

      These soundness theorems are conditional, not automatic: a
      \<^verbatim>\<open>Check_Proved\<close>/\<^verbatim>\<open>Check_Refuted\<close> value \<^verbatim>\<open>analyse\<close> returns at runtime is
      not itself a discharged certificate. Beyond report membership, applying
      the theorem to a concrete program additionally needs a solver-termination
      witness for that program --- nothing here proves that either solver
      terminates on every input, so termination is a genuine per-program fact,
      typically discharged \<^verbatim>\<open>by eval\<close> via
      \<^verbatim>\<open>analyse_interval_td_terminates_via_solve_c\<close> --- and a proof that the
      checked node reaches \<^verbatim>\<open>cfg_exit\<close>, a real structural fact about the
      compiled CFG, not a formality. \<^verbatim>\<open>dispatch_demo_first_check_certified\<close>
      is one complete instance of the whole chain with every hypothesis
      actually discharged: a concrete \<^verbatim>\<open>Check_Proved\<close> value \<^verbatim>\<open>analyse\<close> returns
      for \<^verbatim>\<open>dispatch_demo_prog\<close>, proved semantically correct with no assumption
      left open.
\<close>

text \<open>
  \<^bold>\<open>The D/G execution pipeline (headline).\<close> The flagship threads a single chain,
  every step machine-checked, from source to a soundness theorem over the
  \<^emph>\<open>computed\<close> analysis result:

    \<^item> VIMP source \<^verbatim>\<open>compile_prog\<close> to a CFG;
    \<^item> the generic D/G generator \<^verbatim>\<open>dg_gen_of\<close> emits the equation system;
    \<^item> the verified solver \<^emph>\<open>computes\<close> a solution (\<^verbatim>\<open>solve_c ... = Some sigma\<close>, \<^verbatim>\<open>by eval\<close>);
    \<^item> the registered endpoint \<open>flagship_ex_reg.run_source_sound\<close>
      (@{theory Voblint_Soundness.Run_Analysis_Sound}'s \<^verbatim>\<open>unit_dg_exec_analysis\<close>
      locale) bundles solver correctness, executable/pure commutation,
      post-solution transport, and D/G collecting soundness into one
      application, bounding \<open>ltr_collect g S v\<close> at every program point.

  \<^bold>\<open>Soundness spine.\<close> The context-sensitive analyses converge on one native
  interface, the carrier-opaque \<^verbatim>\<open>sound_dg_spec\<close>; Sign, Interval, and
  the mixed flagship are its instances, and context slicing is factored through
  the functional activation spine and its per-context keyed slots. There is one
  such spine: every domain reaches \<^const>\<open>ltr_collect\<close> through
  \<^verbatim>\<open>dg_post_solution_collect_sound_ltr\<close>, and the routed instances
  through \<^verbatim>\<open>activation_collect_sound\<close> above it.
\<close>

end
