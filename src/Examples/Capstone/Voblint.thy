section \<open>Voblint: a verified abstract interpreter for VIMP\<close>

theory Voblint
  imports
    "Voblint_VIMP.VIMP_Syntax"
    "Voblint_VIMP.VIMP_Expr"
    "Voblint_VIMP.VIMP_Globals"
    "Voblint_VIMP.VIMP_Proc"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_CFG.CFG_Def"
    "Voblint_Compile.VIMP_Proc_to_CFG"
    "Voblint_CFG.LTR_Def"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Domain.Abstract_Domain"
    "Voblint_Framework.Transfer_Algebra"
    "Voblint_Domain.Abstract_Numeric_Queries"
    "Voblint_Framework.Check_Result"
    "Voblint_Framework.Abstract_Checks"
    "Voblint_Framework.Check_Report"
    "Voblint_Analysis_Sign.Sign_Classify"
    "Voblint_Analysis_Sign.Sign_Analyses"
    "Voblint_Analysis_Interval.Interval_Domain"
    "Voblint_Analysis_Interval.Interval_Classify"
    "Voblint_Analysis_Interval.Interval_Analyses"
    "Voblint_Analysis_Parity.Parity_Analyses"
    "Voblint_Analysis_Congruence.Congruence_Analyses"
    "Voblint_Analysis_Int.Int_Analyses"
    "Voblint_CLI.Analysis_Run_Ctx_Sound"
    "Voblint_Framework.DG_Constraint_Programs"
    "Voblint_Framework.DG_Spec_Sound"
    "Voblint_Framework.CFG_Enumeration"
    "Voblint_Analysis_Sign.Sign_Transfer"
    "Voblint_Analysis_Interval.Interval_Transfer"
    "Voblint_Framework.Activation_Backbone"
    "Voblint_Framework.DG_Ctx_Activation"
    "Voblint_Exec.Exec_St_Reachability"
    "Voblint_Analysis_Sign.Sign_Exec"
    "Voblint_Examples_Sign.Exec_Sign_DG_Run"
    "Voblint_Examples_CLI.Example_Checks_Store_Only"
    "Voblint_Examples_CLI.Example_Interval_Checks_Store_Only"
    "Voblint_Examples_CLI.Example_Parity_Checks_Store_Only"
    "Voblint_Examples_Interval.Exec_Interval_Run"
    "Voblint_Examples_CLI.Example_Int_Refinement_Mode_Regression"
    "Voblint_Examples_CLI.Example_Analysis_Result_Regression"
    "Voblint_Examples_CLI.Example_Arithmetic_Diagnostics_Regression"
    Example_End_To_End_Certificate
    "Voblint_Examples_Interval.Example_Interval_DG_Flagship"
    "Voblint_Result.Source_Activation_Sound"
    "Voblint_Examples_Interval.Example_Interval_DG_Ctx_Collect"
    "Voblint_Examples_Interval.Example_Interval_DG_EntryState_Collect"
    "Voblint_Examples_Interval.Example_Interval_DG_CallString_K1"
    "Voblint_Examples_Interval.Example_Interval_DG_CallString_K2"
    "Voblint_Examples_Sign.Example_Sign_DG_CallString_K1"
    "Voblint_Examples_Sign.Example_Sign_DG_CallString_K2"
    "Voblint_Examples_Interval.Example_Interval_Source_Ctx"
    "Voblint_Examples_CFG.Example_Inc_Proc"
    "Voblint_Examples_Sign.Example_Side_Execute"
    "Voblint_Examples_Interval.Example_Proc_Call"
    "Voblint_Examples_Interval.Example_Interval_Loop_Coverage"
    "Voblint_Examples_Interval.Example_Guard_Refinement"
    "Voblint_Examples_Relational.Example_Relational_DG_Demo"
    "Voblint_Examples_Tooling.Example_Strategy_Tree"
    "Voblint_Examples_Tooling.Example_TD_Side_Program"
    "Voblint_Examples_Tooling.Example_TD_Plain_Program"
    "Voblint_Examples_Parity.Example_Parity_DG_Flagship"
    "Voblint_Examples_Int.Exec_Int_DG_Run"
    "Voblint_Examples_Congruence.Example_Congruence_Arithmetic"
    "Voblint_Examples_Congruence.Example_Congruence_Backward"
    "Voblint_Examples_Congruence.Example_Congruence_DG_Run"
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

  \<^bold>\<open>Where the chain ends.\<close>  At the operation the CLI actually calls and code
  generation actually exports, not at an internal solved system.
  @{thm [source] run_voblint_certified_source_sound}, in
  \<^theory>\<open>Voblint_CLI.Analysis_Certified\<close>, says: run the source program, stop
  wherever you like, and ask any configuration --- a domain, a global update rule and a
  context policy --- for a result. There is a graph node and frame stack for where you
  stopped, the abstract state filed for that node contains your store, and every check
  listed there holds of that store, with none there marked unreachable.

  Under a context policy the table has one entry per point \<^emph>\<open>and\<close> context.  A
  store reaching a point then sits in the entry filed under at least one context its
  own call history is admitted at --- exactly one for a call string, possibly several
  under entry-state routing; quantifying over every covered context would be false,
  since another activation's entry need not describe this store.

  What a caller owes is \<open>config_terminates D rule ctx p\<close>: the solve completed.
  Neither coverage nor well-formedness is a premise, because a terminating solve is
  closed along its live dependencies and a malformed program answers
  \<open>Malformed_Program\<close>.  The case split lives in that predicate and in
  \<open>analysis_result_covers\<close> rather than in the statement, because an abstract state's
  type is the domain's own carrier.

  \<^theory>\<open>Voblint_Examples.Example_End_To_End_Certificate\<close> is that theorem
  with nothing left to assume.  It fixes one program at the product domain, a
  call-string context of length one and always-join globals, evaluates
  the solve's termination and the answer, builds the source run step by step,
  and reads the listed \<^const>\<open>Check_Proved\<close> check off the conclusion.
\<close>

section \<open>Flagship theorems\<close>

text \<open>
  Each theory cited here compiles a source program, generates its D/G equation system,
  \<^emph>\<open>computes\<close> a solution with the verified solver (\<open>by eval\<close>), and proves a soundness
  theorem about that computed result.  The session READMEs carry each family's full witness
  inventory; this index names only the headline results along three axes: which domain, which
  context policy, and how far the product domain's components refine each other.
\<close>

subsection \<open>One domain, the whole pipeline, monovariant\<close>

text \<open>
  One flagship per selectable domain, all on the same generator and vendored solver.  Only
  the lattice differs.

  \<^item> @{thm [source] flagship_source_run_sound}
    (\<^theory>\<open>Voblint_Examples_Interval.Example_Interval_DG_Flagship\<close>) bounds actual source
    runs of an interval counting loop.
  \<^item> @{thm [source] dgEx_source_run_sound}
    (\<^theory>\<open>Voblint_Examples_Sign.Exec_Sign_DG_Run\<close>) is the same bound for Sign, solved
    with the always-join update rule.
  \<^item> @{thm [source] parity_source_run_sound}
    (\<^theory>\<open>Voblint_Examples_Parity.Example_Parity_DG_Flagship\<close>) is the Parity instance on
    an even-step loop.
  \<^item> \<^theory>\<open>Voblint_Examples_Congruence.Example_Congruence_DG_Run\<close> computes exact residue
    classes at the exit of a straight-line program.
  \<^item> \<^theory>\<open>Voblint_Examples_Int.Exec_Int_DG_Run\<close> runs the reduced product of Sign,
    Interval, Parity and Congruence.  @{thm [source] dgExI_never_ne_once} separates
    \<^const>\<open>Refine_Never\<close>, which narrows only the Congruence component, from
    \<^const>\<open>Refine_Once\<close>, whose one reduction round reaches the exact singleton.  Refinement
    is legal because \<^const>\<open>int_reduction_step\<close> preserves the concretization while
    descending the order.
\<close>

subsection \<open>Context sensitivity: three storage policies for one axis\<close>

text \<open>
  All three are certified against the same activation-indexed semantics, bounding
  \<^const>\<open>activation_collect\<close> at every \<open>(node, context)\<close> pair.  They differ only in what a
  context \<^emph>\<open>is\<close>.

  \<^item> \<^bold>\<open>Monovariant.\<close> @{thm [source] twice_source_run_sound} analyses \<open>twice\<close>, whose single
    procedure is called from two sites with different arguments, under one shared entry state.
  \<^item> \<^bold>\<open>Entry state\<close>, the entered abstract value of the callee's formals (Seidl et al.,
    \<^emph>\<open>Mixed Flow-Sensitive Static Analysis\<close>, FM 2026, Example 8).
    @{thm [source] twice_activation_collect_sound} keeps the two calls of \<open>twice\<close> in the
    distinct contexts \<open>[3,3]\<close> and \<open>[10,10]\<close>, where the monovariant baseline joins them;
    \<^theory>\<open>Voblint_Examples_Interval.Example_Interval_Source_Ctx\<close> lifts that bound to
    source runs at each activation's own context.
  \<^item> \<^bold>\<open>Call string\<close>, a bounded record of the call sites that led to the activation
    (FM 2026, Example 7).  @{thm [source] nest_1_activation_collect_sound} and
    @{thm [source] nest_2_activation_collect_sound} run one \<open>nest\<close> program at \<open>k = 1\<close> and
    \<open>k = 2\<close>; on Sign, whose computed solution is exact,
    @{thm [source] sign_k2_strictly_more_precise_than_k1_at_g} shows the longer string
    strictly more precise at \<open>g\<close>'s entry.
\<close>

subsection \<open>Checks\<close>

text \<open>
  \<^theory>\<open>Voblint_Examples_CLI.Example_Checks_Store_Only\<close> discharges compiled
  \<open>__voblint_check(...)\<close> conditions against a computed Sign post-solution at each check's own
  node: one proved, one refuted, one unknown.  Its Interval and Parity siblings reuse the
  shape; @{thm [source] checks_ivl_ex_precision_over_sign} is a bound Interval proves and Sign
  cannot.
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
  and context keys.  Every domain instance --- Sign, Interval, Parity, the \<^verbatim>\<open>int_dom\<close>
  product, and the relational carrier --- shares the one verified side-effecting top-down
  solver and the one collecting-soundness infrastructure.
\<close>

subsection \<open>Executable witnesses\<close>

text \<open>
  The interval and Sign flagships compile source programs, generate their D/G
  equations, execute the verified solver, and certify the computed post-solutions.
  The \<open>twice\<close> program calls one procedure from two sites; its activation-sensitive
  interval analysis keeps the two call contexts separate.  Recursive examples test
  structural activation nesting independently of that repeated-call witness.

  The exported analyser returns its solved result as data; the text report, GraphViz
  drawings and report pages are built from that data outside this development, so no
  rendering is part of any soundness claim.

  \<^bold>\<open>How the development is laid out.\<close>  One Isabelle session per architectural
  layer, and the ROOT graph is what keeps the layering honest: a theory cannot reach
  past its session's declared ancestors, so a boundary claimed in prose is also
  enforced by the build.  \<^verbatim>\<open>Voblint_CFG\<close> never sees the compiler, which is why every
  D/G soundness endpoint below holds for an arbitrary CFG rather than only for a
  compiled one; \<^verbatim>\<open>Voblint_Solver\<close> never sees a CFG; \<^verbatim>\<open>Voblint_Framework\<close> never sees a
  concrete domain.

  Two layers are families rather than single sessions.  Every abstract domain has its
  own analysis session over the shared \<^verbatim>\<open>Analyses/Shared/\<close> chain --- Sign, Interval,
  Parity, Congruence, the \<^verbatim>\<open>int_dom\<close> product, and the relational carrier --- and its
  own example session over that, so a domain's witnesses cannot quietly depend on a
  sibling domain.  \<^verbatim>\<open>Voblint_CLI\<close> is where they meet again, because the dispatcher has
  to see all of them, and a downstream codegen session exports it.  This theory is the
  most downstream file in the development: it imports the CLI and every flagship, so
  anything it names has actually been built.

  The index below separates the proof spine from executable frontends and research
  witnesses.

  \<^bold>\<open>1. Language.\<close> VIMP syntax, small-step semantics, and the procedural extension
  (scopes, calls, restores).
    \<^item> @{theory Voblint_VIMP.VIMP_Syntax} --- AST, variable names, countability.
    \<^item> @{theory Voblint_VIMP.VIMP_Expr} --- expression evaluation and small-step semantics.
    \<^item> @{theory Voblint_VIMP.VIMP_Globals} --- global variable names and initial store.
    \<^item> @{theory Voblint_VIMP.VIMP_Proc} --- procedural extension: \<^verbatim>\<open>Scope\<close>, \<^verbatim>\<open>Call\<close>, \<^verbatim>\<open>Restore\<close>.
    \<^item> @{theory Voblint_VIMP.VIMP_Notation} --- \<^verbatim>\<open>\<lbrakk> ... \<rbrakk>\<close> quotation bracket for examples.

  \<^bold>\<open>2. Control-flow graph and concrete semantics.\<close> CFG construction, transfer primitives, and
  the activation-local trace semantics it carries.
    \<^item> @{theory Voblint_CFG.CFG_Def} --- CFG node and edge types,
      predecessor enumeration, and finite code lists.
    \<^item> @{theory Voblint_Compile.VIMP_Proc_to_CFG} ---
      \<^verbatim>\<open>compile_prog\<close>, from VIMP programs to
      interprocedural CFGs.
    \<^item> @{theory Voblint_CFG.CFG_Transfer} --- concrete store
      transformers shared by the semantics:
      \<^verbatim>\<open>edge_step\<close>, \<^verbatim>\<open>edge_collect\<close>,
      \<^verbatim>\<open>edges_collect\<close>,
      \<^verbatim>\<open>combine_collect\<close>, and
      \<^verbatim>\<open>call_enter_store\<close>.
    \<^item> @{theory Voblint_CFG.LTR_Def} --- the call-structured
      activation-local trace \<^const>\<open>valid_ltr\<close>
      (\<^verbatim>\<open>Root\<close>/\<^verbatim>\<open>Call\<close>/
      \<^verbatim>\<open>Resume\<close>), the \<^const>\<open>ltr_collect\<close> and
      \<^const>\<open>activation_collect\<close> projections, and the
      \<^locale>\<open>ltr_coverage\<close> interface with
      \<^verbatim>\<open>ltr_collect_semantic_postfix\<close>.
    \<^item> @{theory Voblint_CFG.CFG_Prune} --- interprocedural graph
      reachability (\<^const>\<open>cfg_reaches\<close>), which feeds the cone
      guard. The graph itself is unchanged; the cone restriction belongs to the
      abstract concretization.

  \<^bold>\<open>3. Analysis spine.\<close> Abstract domains, equation systems, and the TD_side solver bridge; every
  generic endpoint concludes over the trace projections.
    \<^item> @{theory Voblint_Domain.Abstract_Domain} ---
      \<^verbatim>\<open>sound_domain\<close>, lifted state concretization, and
      display support.
    \<^item> @{theory Voblint_Framework.Transfer_Algebra} --- the pure
      abstract-state algebra: call-entry frame reset, formal binding, structural
      return combination, and their soundness against
      \<^verbatim>\<open>gamma_state\<close>.
    \<^item> @{theory Voblint_Framework.DG_Local_State_Spec} --- the
      \<^verbatim>\<open>sound_transfer_for\<close> contract and two Base
      constructions. Their edge and \<^verbatim>\<open>EA_Check\<close> soundness
      facts discharge \<^theory>\<open>Voblint_Framework.DG_Spec_Sound\<close>'s
      \<^verbatim>\<open>step_sound\<close> and
      \<^verbatim>\<open>combine_sound\<close> obligations.
    \<^item> @{theory Voblint_Framework.State_Restriction} --- the
      local/global restriction algebra used to reassemble routed states.
    \<^item> @{theory Voblint_Framework.DG_Keyed_Generator} ---
      \<^verbatim>\<open>routed_node_rhs_mono_eq\<close>/
      \<^verbatim>\<open>routed_node_rhs_mono_sides\<close>/
      \<^verbatim>\<open>routed_node_rhs_mono_deps\<close> discharge the vendored
      solver's \<^verbatim>\<open>TD_side_mono\<close> precondition once for an
      arbitrary generator instance.

  \<^bold>\<open>3b. Check discharge.\<close> A domain-generic, sound (incomplete) decision
    procedure for compiled \<^verbatim>\<open>__voblint_check(...)\<close> conditions, discharged
    against the computed abstract solver environment at each check's own
    node --- no store is forwarded between check nodes or to the procedure
    exit.
    \<^item> @{theory Voblint_Domain.Abstract_Numeric_Queries} --- the generic
      \<^locale>\<open>abstract_numeric_queries\<close> interface (entailment/refutation of
      \<open><\<close>/\<open>=\<close> over an abstract numeric value) and its derivation, defined
      directly in any \<^locale>\<open>backward_domain\<close> instance's own context, from
      that instance's own narrowing operators --- a sound default a concrete
      domain may override with sharper, hand-tuned predicates.
    \<^item> @{theory Voblint_Framework.Abstract_Checks} --- \<^locale>\<open>abstract_expression_domain\<close>
      and \<^locale>\<open>abstract_check_domain\<close>: the single \<^verbatim>\<open>check_query\<close> decision
      procedure into \<^typ>\<open>bool option\<close> over \<^typ>\<open>exp\<close>, the three-way
      \<^verbatim>\<open>check_result\<close> classification (\<^verbatim>\<open>Check_Proved\<close>/\<^verbatim>\<open>Check_Refuted\<close>/
      \<^verbatim>\<open>Check_Unknown\<close>), and the node-indexed bridge to
      \<^const>\<open>checks_proven\<close>.
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Classify} --- the Sign instance: derived
      numeric queries (read off \<^const>\<open>inv_less_sign\<close>/\<^const>\<open>inv_eq_sign\<close>/
      \<^const>\<open>meet_sign\<close>), no hand-built comparison tables.
    \<^item> @{theory Voblint_Analysis_Interval.Interval_Classify} --- the Interval instance:
      specialized bound-comparison queries (\<^const>\<open>interval_less_true\<close> and
      siblings, \<open>Interval_Numeric_Queries\<close>). The backward-domain default derives
      equality refutation through \<^const>\<open>intersect_ivl\<close>, whose canonical empty
      result is independent of the raw lattice \<^const>\<open>inf\<close>.

  \<^bold>\<open>4. Concrete domains.\<close> One analysis session per domain, all over the shared
    \<^verbatim>\<open>Analyses/Shared/\<close> chain, all reaching the same spine.  Each pairs a lattice theory
    (order, transfers, soundness, monotonicity) with one generated \<^verbatim>\<open>_Analyses\<close> theory
    that registers it at the routed D/G spine three times: at the unit context, keyed by
    entry state, and keyed by a bounded call string --- for Sign, \<^verbatim>\<open>sign_rule\<close>,
    \<^verbatim>\<open>sign_es_rule\<close> and \<^verbatim>\<open>sign_cs_rule\<close>.  Every registration takes the global
    update rule \<open>r\<close> as a parameter, and the call-string one also its bound \<open>k\<close>, so
    one registration per context policy serves every rule and every bound.
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Transfer} /
      @{theory Voblint_Analysis_Sign.Sign_Analyses} --- the seven-element Sign
      lattice. It is finite, so the plain-join solver needs no widening.
    \<^item> @{theory Voblint_Analysis_Interval.Interval_Domain} /
      @{theory Voblint_Analysis_Interval.Interval_Analyses} --- intervals over
      the extended integers. Their infinite height requires widening and
      narrowing, making solver choice relevant.
    \<^item> @{theory Voblint_Analysis_Parity.Parity_Domain} --- even/odd.
      Finite like Sign, and expressive about values neither Sign nor Interval
      constrains: \<^verbatim>\<open>y := x * 2\<close> is even for every
      \<^verbatim>\<open>x\<close>.
    \<^item> @{theory Voblint_Analysis_Congruence.Congruence_Domain} ---
      normalized residue classes. Congruence is selectable on its own and is
      also the fourth component of \<^verbatim>\<open>int_dom\<close>.
    \<^item> @{theory Voblint_Analysis_Int.Int_Domain} /
      @{theory Voblint_Analysis_Int.Int_Refinement} ---
      \<^verbatim>\<open>int_dom\<close>, the reduced product of the four scalar
      domains, with exact reduction steps and three refinement modes.
    \<^item> @{theory Voblint_Analysis_Relational.Rel_Order_Domain} --- an
      order carrier that is \<^emph>\<open>not\<close> a pointwise abstract state,
      showing that the generator and solver do not assume one.

  \<^bold>\<open>4b. The D/G interface spine.\<close> The native, carrier-opaque Goblint-\<^verbatim>\<open>Spec\<close> interface
    (independent flow-sensitive local domain \<^verbatim>\<open>D\<close> and flow-insensitive global domain \<^verbatim>\<open>G\<close>),
    the canonical context-sensitive backbone.
    \<^item> @{theory Voblint_Framework.DG_Spec} --- the
      \<^verbatim>\<open>dg_spec\<close> record, with one manager-native transfer
      per edge action, plus the \<^verbatim>\<open>dg_state\<close> copy lattice and
      seeded keyed generator in
      @{theory Voblint_Framework.DG_Constraint_Programs}.
    \<^item> @{theory Voblint_Framework.DG_Spec_Sound} --- native
      heterogeneous soundness over opaque carriers
      (\<^verbatim>\<open>sound_dg_spec_core\<close>). The routed context locales in
      @{theory Voblint_Framework.Routed_Context} feed those obligations into
      \<^const>\<open>activation_collect\<close>. The unit-context instance reaches
      \<^const>\<open>ltr_collect\<close> through
      \<^verbatim>\<open>ltr_collect_eq_Union_activation_of_fun\<close>
      (@{theory Voblint_Framework.Routed_Context_Unit}).
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Analyses} and its four siblings --- each
      domain as a \<^locale>\<open>routed_dg_analysis\<close> instance at entry state and call
      string and a \<^locale>\<open>unit_dg_analysis\<close> instance at the unit context, so each
      reaches \<^const>\<open>activation_collect\<close>, and at the unit context
      \<^const>\<open>ltr_collect\<close>, through the locale's generic node-soundness bridge.

  \<^bold>\<open>4c. Activation-local certification.\<close> The concrete object the context-sensitive soundness
    rides: one trace per activation, with a stable call-only context.
    \<^item> @{theory Voblint_Framework.Activation_Backbone} --- the generic
      \<^verbatim>\<open>activation_collect_sound\<close>. Over
      \<^const>\<open>valid_ltr\<close>, the five obligations
      \<^verbatim>\<open>INIT\<close>/\<^verbatim>\<open>INTRA\<close>/
      \<^verbatim>\<open>CALL\<close>/\<^verbatim>\<open>RETURN\<close>/
      \<^verbatim>\<open>TOTAL\<close> on a \<^verbatim>\<open>cover\<close> map bound
      \<^const>\<open>activation_collect\<close> at every
      \<^verbatim>\<open>(node, context)\<close>.
    \<^item> @{theory Voblint_Framework.DG_Ctx_Activation} --- discharges
      those five obligations from a
      \<^verbatim>\<open>sound_dg_spec_core\<close> post-solution, so a computed D/G
      solution certifies the activation collecting semantics.

  \<^bold>\<open>5. Executable frontend.\<close> Finite-map state representation and certified execution.
    \<^item> @{theory Voblint_Exec.Exec_St_Base} --- executable abstract-state maps for code
      generation, layered as representation, algebra
      (@{theory Voblint_Exec.Exec_St_Algebra}), refinement to variable-indexed states
      (@{theory Voblint_Exec.Exec_St_Transfer}) and dead-code detection
      (@{theory Voblint_Exec.Exec_St_Reachability}).
    \<^item> @{theory Voblint_Exec.Exec_St_Restriction_Refinement} ---
      commutation from executable states to function states.
    \<^item> @{theory Voblint_Routing.Compiled_Routed_Equations} --- the D/G
      equation generator (\<^const>\<open>compiled_routed_eqs_for\<close>) every analysis,
      context-insensitive or not, is solved over; the verified solver \<^emph>\<open>runs\<close> on it.
    \<^item> @{theory Voblint_Framework.DG_Reader_Transport} --- reads a
      whole equation system through carrier-generic readers
      (\<^const>\<open>fun_of_dg_st_gen\<close>), letting the executable run answer
      for the mathematical system.
    \<^item> @{theory Voblint_Exec.DG_Local_State_Exec_Refinement} ---
      \<^locale>\<open>routed_dg_domain_exec\<close> proves a registered domain's
      D/G spec sound directly at the executable carrier, without a separate
      abstract-carrier transport step.
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Exec} --- executable Sign transfer functions.
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Analyses} --- the routed
      D/G runtime for Sign: each registration's equation system, solved table,
      and termination hypothesis \<^verbatim>\<open>sign_rule.terminates r\<close>, stated once for every
      update rule \<open>r\<close>.
    \<^item> @{theory Voblint_Analysis_Interval.Interval_Analyses},
      @{theory Voblint_Analysis_Parity.Parity_Analyses},
      @{theory Voblint_Analysis_Congruence.Congruence_Analyses} and
      @{theory Voblint_Analysis_Int.Int_Analyses} --- the same runtime for the other
      four domains, generated from the same template.

  \<^bold>\<open>5b. Solved results and reports.\<close> What a finished analysis \<^emph>\<open>is\<close>, before anyone
    renders or dispatches it.
    \<^item> @{theory Voblint_Framework.Analysis_Result} --- the
      domain-generic table: a covered key set of
      \<^typ>\<open>pp \<times> 'ctx\<close> pairs plus a total lookup.
      \<^verbatim>\<open>wf_analysis_result\<close> requires finitely many keys and
      canonical payloads. Publishing adapters guarantee canonicality;
      finiteness is unconditional only for context spaces bounded in advance.
    \<^item> @{theory Voblint_Framework.Check_Report} and
      @{theory Voblint_Framework.Contextual_Check_Report} --- the flat and
      per-context readings of that table. A check can be
      \<^const>\<open>Dead\<close> in one context and decided in another, which a
      flat \<^typ>\<open>check_result\<close> cannot express. The contextual report
      therefore has a separate type.
    \<^item> @{theory Voblint_CLI.Analysis_Config} --- the selection surface:
      \<^typ>\<open>analysis_domain\<close>, \<^typ>\<open>globals_rule\<close> and \<^typ>\<open>context_mode\<close>, all
      plain values. Every combination is analysed, so there is no legality table and no
      default a caller inherits.

  \<^bold>\<open>6. End-to-end theorems.\<close> Headline soundness and the source bridge.
    \<^item> @{theory Voblint_Result.Source_Activation_Sound} --- the
      source-adequacy bridge. A reachable VIMP source configuration produces a
      \<^const>\<open>valid_ltr\<close> trace
      (\<^verbatim>\<open>source_run_has_ltr\<close>), bounded at its activation
      context (\<^verbatim>\<open>source_activation_sound\<close>) and monovariantly
      (\<^verbatim>\<open>source_reaches_ltr_collect\<close>).
    \<^item> @{theory Voblint_Result.Unit_DG_Analysis} --- the context-insensitive
      analysis as the routed one at the unit context; its endpoints are what every
      flagship and codegen entry point applies: one
      \<^verbatim>\<open>solve_c ... \<noteq> None\<close> fact in, source-level soundness out.
      Solver correctness, executable-to-pure commutation, post-solution
      transport, and D/G collecting soundness are discharged inside. It is
      partial correctness: the caller supplies that the solver
      \<^emph>\<open>returns\<close>, typically \<^theory_text>\<open>by eval\<close>.
    \<^item> @{theory Voblint_CLI.Analysis_Certified} --- one soundness statement for
      every configuration the dispatcher answers with check rows
      (@{thm [source] run_voblint_certified_source_sound}), and the dead-check
      guarantee at the same entry point
      (@{thm [source] run_voblint_dead_check_unreached}).
    \<^item> @{theory Voblint_Examples.Example_End_To_End_Certificate} --- that
      statement instantiated at one program, with every premise discharged.

  \<^bold>\<open>7. Examples and witnesses.\<close> Executable demos, precision
    witnesses, and tooling. The five domain flagships
    (\<open>Example_Interval_DG_Flagship\<close>, \<open>Exec_Sign_DG_Run\<close>,
    \<open>Example_Parity_DG_Flagship\<close>, \<open>Example_Congruence_DG_Run\<close>,
    and \<open>Exec_Int_DG_Run\<close>) are indexed above, together with the
    context-sensitive \<open>Example_Interval_DG_Ctx_Collect\<close>,
    \<open>Example_Interval_DG_EntryState_Collect\<close>, and
    \<open>Example_Interval_Source_Ctx\<close>.
    \<^item> @{theory Voblint_Examples_CLI.Example_Checks_Store_Only} --- \<open>__voblint_check(...)\<close>
      discharged against a computed Sign post-solution, node-locally: one check
      proved, one refuted (a genuine bug, not merely unproven), one unknown.
    \<^item> @{theory Voblint_Examples_CLI.Example_Parity_Checks_Store_Only} --- the same
      program, but with a parity domain instead of Sign.
    \<^item> @{theory Voblint_Examples_CLI.Example_Interval_Checks_Store_Only} --- the Interval
      counterpart, inside a two-sided bound guard (\<open>0 < x \<and> x < 10\<close>) so the
      checks exercise Interval's numeric bounds, not just its sign; includes a
      precision comparison showing a bound Interval proves outright that Sign's
      \<^term>\<open>SPos\<close> alone classifies \<^term>\<open>Check_Unknown\<close>.
    \<^item> @{theory Voblint_Examples_Congruence.Example_Congruence_Arithmetic}
      and @{theory Voblint_Examples_Congruence.Example_Congruence_Backward} ---
      standalone modular arithmetic and backward filtering, which supplies
      Congruence's precise inverse.
    \<^item> @{theory
      Voblint_Examples_CLI.Example_Int_Refinement_Mode_Regression} --- all three
      refinement modes pinned at a composite operation. This complements
      @{theory Voblint_Examples_Int.Exec_Int_DG_Run}, whose two non-CLI modes
      run through the compiled solver pipeline. In the direct-operation
      witness, \<^const>\<open>Refine_Once\<close> has not reached the fixpoint.
    \<^item> @{theory Voblint_Examples_Interval.Exec_Interval_Run} --- the same
      bounded loop under Kleene iteration, warrowing TD, and every update rule.
      Interval narrowing and the backward guard filter recover \<open>[0,20]\<close>;
      the update rule does not affect that bound.
    \<^item> @{theory Voblint_Examples_CLI.Example_Analysis_Result_Regression} --- the published result
      table and its per-context lookup surface.
    \<^item> @{theory Voblint_Examples_CLI.Example_Arithmetic_Diagnostics_Regression} ---
      arithmetic findings through the public CLI operation: one finding per guard,
      silence in dead branches, conservative context aggregation, and total Boolean operands.
    \<^item> @{theory Voblint_Examples_CFG.Example_Inc_Proc} --- shared global-increment procedure witness.
    \<^item> @{theory Voblint_Examples_Sign.Example_Side_Execute} ---
      minimal certified Sign interprocedural example with annotated CFG DOT.
    \<^item> @{theory Voblint_Examples_Interval.Example_Proc_Call} ---
      concrete-semantics witness for \<^verbatim>\<open>inc\<close> and
      \<^verbatim>\<open>sqr\<close> communicating through a global, plus their
      compiled interprocedural CFG. The executable corpus carries the Sign
      analysis of the same shared-global increment call.
    \<^item> @{theory
      Voblint_Examples_Interval.Example_Interval_Loop_Coverage} --- backward
      guard-refinement precision at a bounded loop's body entry. The certified
      loop-head bound is carried by @{text "Exec_Interval_Run"}.
    \<^item> @{theory Voblint_Examples_Interval.Example_Guard_Refinement} ---
      backward guard-refinement precision witness.
    \<^item> @{theory Voblint_Examples_Interval.Example_Interval_DG_CallString_K1} --- the \<open>nest\<close> program,
      computed and certified at a 1-call-string context
      (\<^verbatim>\<open>nest_1_activation_collect_sound\<close>): \<open>main\<close> calls \<open>f\<close> from two sites and \<open>f\<close>
      calls \<open>g\<close> from one, so a 1-call-string cannot separate \<open>g\<close>'s two activations.
    \<^item> @{theory
      Voblint_Examples_Interval.Example_Interval_DG_CallString_K2} --- the
      same program at a
      2-call-string context (\<^verbatim>\<open>nest_2_activation_collect_sound\<close>), which does separate them.
    \<^item> @{theory Voblint_Examples_Sign.Example_Sign_DG_CallString_K1} --- the Sign counterpart of the
      \<open>nest\<close> pair, computed by the plain-join solver (\<^verbatim>\<open>TD_side_always_join_Interp\<close>) rather
      than warrowing: Sign is finite, so no widening is needed and the computed solution is
      exact. \<^verbatim>\<open>sign_nest_1_activation_collect_sound\<close> is the same soundness shape at a
      1-call-string context, where \<open>g\<close>'s two activations (entered with \<open>SPos\<close> and \<open>SNeg\<close>)
      collapse and join to \<open>STop\<close>.
    \<^item> @{theory Voblint_Examples_Sign.Example_Sign_DG_CallString_K2} --- the 2-call-string sibling
      (\<^verbatim>\<open>sign_nest_2_activation_collect_sound\<close>), which keeps \<open>g\<close>'s two activations separate
      at \<open>SPos\<close> and \<open>SNeg\<close>. Because Sign is a finite lattice with an exact computed solution,
      this pair supports a genuine strict-precision witness:
      \<^verbatim>\<open>sign_k2_strictly_more_precise_than_k1_at_g\<close> proves
      the 2-call-string value at \<open>g\<close>'s entry is strictly below the 1-call-string \<open>STop\<close> merge in
      the Sign order, for both activations, \<^emph>\<open>computed and compared\<close> rather than argued
      abstractly.
    \<^item> @{theory Voblint_Examples_Relational.Example_Relational_DG_Demo} --- an execution
      witness, not a soundness-certified result: a compiled full-program
      `if (x < y) { z := 1 } else { z := 0 }` runs through the *same*
      \<^verbatim>\<open>compiled_routed_eqs_for\<close>/vendored-solver pipeline as Sign/Interval, this time
      over \<^verbatim>\<open>Voblint_Analysis_Relational.Rel_Order_Domain\<close>'s non-\<^verbatim>\<open>abs_state\<close>
      relational carrier; the computed result is compared against
      Interval's on the identical program and rendered, raw and
      analysis-annotated, via GraphViz.

  \<^bold>\<open>8. Tooling.\<close> Theories outside the core proof spine.
    \<^item> \<^bold>\<open>Named global unknowns\<close> --- a keyed global family is the routed D/G
      context's own \<open>gkey\<close>, and \<^const>\<open>dep_aux\<close> pins what a per-edge
      program reads: @{thm dep_dg_edge_program_at} names the source address and the
      one global slot, nothing else.
    \<^item> \<^bold>\<open>Rendering\<close> --- the text report, DOT and HTML are produced by the OCaml
      renderers from \<^const>\<open>run_voblint\<close>'s structured result, outside any theory.
      A rendering asserts nothing that a \<^verbatim>\<open>writeln\<close> could check, so the
      fixtures under \<^verbatim>\<open>tests/regression/\<close> carry it instead --- \<^verbatim>\<open>08-tooling\<close> for
      \<^verbatim>\<open>--dot\<close>, \<^verbatim>\<open>13-full-state-dot\<close> for the per-node states, and
      \<^verbatim>\<open>11-graph-snapshot\<close> for golden cluster/node/edge snapshots including a
      recursive procedure.
    \<^item> \<^bold>\<open>Related demo:\<close> @{theory Voblint_Examples_Tooling.Example_Strategy_Tree} ---
      \<^type>\<open>strategy_tree\<close> as a small dependency/effect language on its own,
      independent of any abstract domain, built directly from \<^const>\<open>QueryL\<close>/
      \<^const>\<open>Side\<close>/\<^const>\<open>Answer\<close>.
    \<^item> \<^bold>\<open>The vendored solver on its own terms:\<close>
      @{theory Voblint_Examples_Tooling.Example_TD_Side_Program} and
      @{theory Voblint_Examples_Tooling.Example_TD_Plain_Program} run Tilscher's own
      running examples --- the lock-set analysis with side effects, and
      must-be-initialized without them --- through the typed \<^verbatim>\<open>strategy_program\<close>
      frontend, with no CFG and no abstract domain in play.  They are what shows the
      solver interface this development builds on is the vendored one, not a
      reimplementation shaped to fit.

  \<^bold>\<open>9. The CLI: configuration and code generation.\<close>
    One public operation over every domain, update rule and context policy, applying
    the registrations of \<open>4\<close>/\<open>5\<close> above rather than a parallel pipeline, and
    exported to OCaml.
    \<^item> @{theory Voblint_Solver.Globals_Rule} --- the rule that merges contributions to a
      side-effected global, as a value: one solver interpretation serves all four, and
      every domain registers each context policy once over it.
    \<^item> @{theory Voblint_CLI.Analysis_Run} --- \<^const>\<open>run_voblint\<close>, the one operation
      code generation exports: a domain, a global update rule and a context policy, all
      plain values, and a program. Every combination is analysed; the answer is the
      solved result as data, and every rendering of it is built outside this
      development. \<^verbatim>\<open>dispatch_demo_interval_precise\<close> pins one program's answer
      \<^verbatim>\<open>by eval\<close>, and a hand-written OCaml driver under \<open>codegen/regression/\<close>
      checks the generated module against the same values.
    \<^item> @{theory Voblint_CLI.Analysis_Run_Sound} and
      @{theory Voblint_CLI.Analysis_Run_Ctx_Sound} --- one soundness table per domain
      and context policy (@{thm [source] sign_rule_table},
      @{thm [source] interval_es_rule_table}, @{thm [source] int_cs_rule_table}, and
      their siblings), each stated for an arbitrary update rule.  The unit tables are
      built from the registration's own \<^verbatim>\<open>result_node_sound_of_terminates\<close>
      (\<^theory>\<open>Voblint_Result.Unit_DG_Analysis\<close>).
      @{theory Voblint_CLI.Analysis_Certified} dispatches over the tables to state
      @{thm [source] run_voblint_certified_source_sound} and
      @{thm [source] run_voblint_check_sound} once for every configuration.

      \<^bold>\<open>What the proof attaches to.\<close> \<^verbatim>\<open>export_code\<close> translates the executable
      equations of \<^const>\<open>run_voblint\<close> and everything it transitively calls, down to the
      solver itself. It is not proving one function and exporting a different,
      hand-written one: the generated operation is a translation of the same equations
      @{thm [source] run_voblint_certified_source_sound} is proved about. That theorem is
      conditional: applying it to a concrete program needs the solve's termination on
      that program, a genuine per-program fact typically discharged \<^verbatim>\<open>by eval\<close>.
      \<^theory>\<open>Voblint_Examples.Example_End_To_End_Certificate\<close> discharges it for one
      program, with no assumption left open.
\<close>

text \<open>
  \<^bold>\<open>The D/G execution pipeline (headline).\<close> The flagship threads a single chain,
  every step machine-checked, from source to a soundness theorem over the
  \<^emph>\<open>computed\<close> analysis result:

    \<^item> VIMP source \<^verbatim>\<open>compile_prog\<close> to a CFG;
    \<^item> the generic D/G generator \<^verbatim>\<open>compiled_routed_eqs_for\<close> emits the equation system;
    \<^item> the verified solver \<^emph>\<open>computes\<close> a solution (\<^verbatim>\<open>solve_c ... = Some sigma\<close>, \<^verbatim>\<open>by eval\<close>);
    \<^item> the endpoint \<open>interval_seed_join.source_sound\<close>
      (@{theory Voblint_Result.Unit_DG_Analysis}'s \<^verbatim>\<open>unit_dg_analysis\<close> locale, the
      routed analysis at the unit context) bundles solver correctness,
      executable/pure commutation,
      post-solution transport, and D/G collecting soundness into one
      application, bounding \<open>\<C>\<^bsub>\<G>,g,S\<^esub> v\<close> at every program point.

  \<^bold>\<open>Soundness spine.\<close> The context-sensitive analyses converge on one native
  interface, the carrier-opaque \<^verbatim>\<open>sound_dg_spec_core\<close>; every domain is one of its
  instances, and context slicing is factored through
  the relational activation spine and its per-context admitted slots --- the unit
  and call-string routings stay functional (\<^const>\<open>call_context_rel_of_fun\<close>), while
  entry-state routing genuinely admits several contexts per call. There is one
  such spine: every domain reaches \<^const>\<open>ltr_collect\<close> through the routed
  unit-context instance's \<^verbatim>\<open>ltr_collect_eq_Union_activation_of_fun\<close>, and the routed
  instances through \<^verbatim>\<open>activation_collect_sound\<close> above it.
\<close>

end
