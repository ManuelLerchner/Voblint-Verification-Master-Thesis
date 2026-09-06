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
    "Voblint_Analysis_Sign.Sign_Domain"
    "Voblint_Analysis_Sign.Sign_Analyses"
    "Voblint_Analysis_Sign.Sign_Checks"
    "Voblint_Analysis_Interval.Interval_Domain"
    "Voblint_Analysis_Interval.Interval_Analyses"
    "Voblint_Analysis_Interval.Interval_Checks"
    "Voblint_Analysis_Interval.Interval_Exec_Sound"
    "Voblint_Framework.DG_Constraint_Trees"
    "Voblint_Framework.DG_Spec_Sound"
    "Voblint_Framework.CFG_Enumeration"
    "Voblint_Analysis_Sign.Sign_Transfer"
    "Voblint_Analysis_Interval.Interval_Transfer"
    "Voblint_Framework.Activation_Backbone"
    "Voblint_Framework.DG_Ctx_Activation"
    "Voblint_Exec.Exec_St"
    "Voblint_Analysis_Sign.Sign_Exec"
    "Voblint_Examples_Sign.Exec_Sign_DG_Run"
    "Voblint_Examples_CLI.Example_Checks_Store_Only"
    "Voblint_Examples_CLI.Example_Interval_Checks_Store_Only"
    "Voblint_Examples_CLI.Example_Parity_Checks_Store_Only"
    "Voblint_Examples_CLI.Exec_Interval_Run"
    "Voblint_Examples_CLI.Example_Int_Refinement_Mode_Regression"
    "Voblint_Examples_CLI.Example_Analysis_Result_Regression"
    "Voblint_Examples_Interval.Example_Interval_DG_Flagship"
    "Voblint_Soundness.Source_Activation_Sound"
    "Voblint_Examples_Interval.Example_Interval_DG_Ctx_Collect"
    "Voblint_Examples_Interval.Example_Interval_DG_EntryState_Collect"
    "Voblint_Examples_Interval.Example_Interval_DG_CallString_K1"
    "Voblint_Examples_Interval.Example_Interval_DG_CallString_K2"
    "Voblint_Examples_Sign.Example_Sign_DG_CallString_K1"
    "Voblint_Examples_Sign.Example_Sign_DG_CallString_K2"
    "Voblint_Examples_Interval.Example_Interval_Source_Ctx"
    "Voblint_Examples_CFG.Example_Inc_Proc"
    "Voblint_Examples_CLI.Example_Side_Execute"
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
  demonstrations. Three capability axes, each with its own flagships: which domain, which
  context policy, and --- for the product domain only --- how far its components refine
  each other.
\<close>

subsection \<open>Basic capability: one domain, the whole pipeline, monovariant\<close>

text \<open>
  One flagship per domain, all four on the same generator, the same vendored solver, and
  the same soundness shape.  What differs is only which lattice is plugged in.

  \<^item> \<^bold>\<open>@{theory Voblint_Examples_Interval.Example_Interval_DG_Flagship}\<close> --- the Interval flagship: a
    counting loop, compiled, solved, and certified. \<^verbatim>\<open>flagship_source_run_sound\<close> bounds
    \<^emph>\<open>actual source runs\<close>.
  \<^item> \<^bold>\<open>@{theory Voblint_Examples_Sign.Exec_Sign_DG_Run}\<close> --- the Sign flagship, same pipeline, same
    always-join solver. \<^verbatim>\<open>dgEx_source_run_sound\<close> is the same source-run bound.
  \<^item> \<^bold>\<open>@{theory Voblint_Examples_Parity.Example_Parity_DG_Flagship}\<close> --- the Parity flagship on an
    even-step loop, \<^verbatim>\<open>parity_source_run_sound\<close> again that bound.  Its point is what it did
    \<^emph>\<open>not\<close> need: registering a third domain copied no step or combine proof.
  \<^item> \<^bold>\<open>@{theory Voblint_Examples_Int.Exec_Int_DG_Run}\<close> --- the \<^verbatim>\<open>int_dom\<close> product, the
    reduced product of Sign, Interval, Parity and Congruence, on
    \<^verbatim>\<open>if (y + 1 == 3) { x := 1 } else { x := 0 }\<close>.  See the refinement subsection below for
    what this one settles.
\<close>

subsection \<open>Context sensitivity: three storage policies for one axis\<close>

text \<open>
  Three storage policies, each certified against the same activation-indexed semantics
  and by the same soundness shape --- \<^const>\<open>activation_collect\<close> bounded at every
  \<open>(node, context)\<close> pair.  They differ only in what a context \<^emph>\<open>is\<close>.

  \<^item> \<^bold>\<open>Monovariant\<close> --- no context: one abstract state per program point.
    \<^bold>\<open>@{theory Voblint_Examples_Interval.Example_Interval_DG_IP_Flagship}\<close> analyses \<open>twice\<close>, whose
    single procedure is called from two sites with different arguments, under one shared
    entry state, and \<^verbatim>\<open>twice_source_run_sound\<close> bounds the result.  This is the baseline
    the two policies below sharpen.
  \<^item> \<^bold>\<open>Entry state\<close> --- the context is the entered abstract value of the callee's declared
    formals (partial tabulation, \<^cite>\<open>SeidlEtAl2026\<close> Example 8).
    \<^bold>\<open>@{theory Voblint_Examples_Interval.Example_Interval_DG_Ctx_Collect}\<close> instantiates the production
    entry-state analysis on that same \<open>twice\<close> program: the two calls route to the distinct
    contexts \<open>[3,3]\<close> and \<open>[10,10]\<close> and keep their entry and return values apart, where the
    monovariant baseline joins them.  \<^verbatim>\<open>twice_activation_collect_sound\<close> is the bound.
    \<^bold>\<open>@{theory Voblint_Examples_Interval.Example_Interval_DG_EntryState_Collect}\<close> is the complementary
    witness on an unconstrained argument, where one wide context covers infinitely many
    concrete entries rather than separating two.
  \<^item> \<^bold>\<open>Call string\<close> --- the context is a bounded record of the call sites traversed to reach
    the activation (\<^cite>\<open>SeidlEtAl2026\<close> Example 7 at \<open>k = 1\<close>).
    \<^bold>\<open>@{theory Voblint_Examples_Interval.Example_Interval_DG_CallString_K1}\<close> and
    \<^bold>\<open>@{theory Voblint_Examples_Interval.Example_Interval_DG_CallString_K2}\<close> run one \<open>nest\<close> program at
    \<open>k = 1\<close> and \<open>k = 2\<close>, so the pair also measures what raising the bound buys.  This policy
    needed \<open>enterc\<close> widened to see the call site to be expressible at all.

  \<^bold>\<open>@{theory Voblint_Examples_Interval.Example_Interval_Source_Ctx}\<close> is the sharpest statement of the
  entry-state route: bound against \<^emph>\<open>actual source runs\<close> at each activation's own context,
  not just the collecting semantics.
\<close>

subsection \<open>Reduced product: what refinement between components buys\<close>

text \<open>
  \<^verbatim>\<open>int_dom\<close> is a reduced product, so it has a dimension the single-lattice flagships do
  not: components may exchange facts.  \<^const>\<open>Refine_Never\<close> forbids that exchange,
  \<^const>\<open>Refine_Once\<close> runs one reduction round per composite operation, and
  \<^const>\<open>Refine_Fixpoint\<close> iterates to a fixpoint
  (@{theory Voblint_Analysis_Int.Int_Refinement}).  Refinement is only legal because each
  step is exact: \<^const>\<open>int_reduction_step\<close> requires it to preserve the concretization
  while descending the order, so a sharper component value never loses a concrete state.

  @{theory Voblint_Examples_Int.Exec_Int_DG_Run} settles the modes by three real solver
  runs on one compiled program, not by three direct transfer calls:
  \<^verbatim>\<open>dgExI_never_ne_once\<close> shows \<^const>\<open>Refine_Never\<close> stops at what Congruence alone can
  invert, while \<^verbatim>\<open>dgExI_once_eq_fixpoint\<close> shows the exact singleton is already reached
  after one round \<^emph>\<open>on this guard\<close> --- not in general, which
  \<^verbatim>\<open>refinement_round_is_progressive\<close> witnesses in the other direction.
  Congruence is not selectable on its own: it exists as the fourth component here, and
  @{theory Voblint_Examples_Congruence.Example_Congruence_Arithmetic} and
  @{theory Voblint_Examples_Congruence.Example_Congruence_Backward} exercise it directly.
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

  GraphViz exporters present procedure entries, results, calls, resumes, and computed
  abstract states without changing the certified equation system.

  \<^bold>\<open>How the development is laid out.\<close>  One Isabelle session per architectural
  layer, and the ROOT graph is what keeps the layering honest: a theory cannot reach
  past its session's declared ancestors, so a boundary claimed in prose is also
  enforced by the build.  \<^verbatim>\<open>Voblint_CFG\<close> never sees the compiler, which is why every
  D/G soundness endpoint below holds for an arbitrary CFG rather than only for a
  compiled one; \<^verbatim>\<open>Voblint_Solver\<close> never sees a CFG; \<^verbatim>\<open>Voblint_Framework\<close> never sees a
  concrete domain.

  Two layers are families rather than single sessions.  Every abstract domain has its
  own analysis session over the shared \<^verbatim>\<open>Voblint_Analysis_Base\<close> --- Sign, Interval,
  Parity, Congruence, the \<^verbatim>\<open>int_dom\<close> product, and the relational carrier --- and its
  own example session over that, so a domain's witnesses cannot quietly depend on a
  sibling domain.  \<^verbatim>\<open>Voblint_CLI\<close> is where they meet again, because the dispatcher has
  to see all of them, and a downstream codegen session exports it.  This theory is the
  most downstream file in the development: it imports the CLI and every flagship, so
  anything it names has actually been built.

  The index below separates the proof spine from executable frontends, DOT exporters,
  and research witnesses.

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
    \<^item> @{theory Voblint_Compile.VIMP_Proc_to_CFG} --- \<^verbatim>\<open>compile_prog\<close>: VIMP programs to interprocedural CFGs.
    \<^item> @{theory Voblint_CFG.CFG_Transfer} --- the concrete store transformers shared by the semantics: \<^verbatim>\<open>edge_step\<close>, \<^verbatim>\<open>edge_collect\<close>, \<^verbatim>\<open>edges_collect\<close>, \<^verbatim>\<open>combine_collect\<close>, \<^verbatim>\<open>call_enter_store\<close>.
    \<^item> @{theory Voblint_CFG.LTR_Def} --- the call-structured activation-local trace \<^const>\<open>valid_ltr\<close> (\<^verbatim>\<open>Root\<close>/\<^verbatim>\<open>Call\<close>/\<^verbatim>\<open>Resume\<close>), the projections \<^const>\<open>ltr_collect\<close> / \<^const>\<open>activation_collect\<close>, and the correlation-preserving interface \<^locale>\<open>ltr_coverage\<close> (with the keystone \<^verbatim>\<open>ltr_collect_semantic_postfix\<close>).
    \<^item> @{theory Voblint_CFG.CFG_Prune} --- interprocedural graph reachability (\<^const>\<open>cfg_reaches\<close>), which feeds the cone guard.  No graph is pruned: the cone restriction lives in the abstract concretization, not in a semantics-altering transformation.

  \<^bold>\<open>3. Analysis spine.\<close> Abstract domains, equation systems, and the TD_side solver bridge; every
  generic endpoint concludes over the trace projections.
    \<^item> @{theory Voblint_Domain.Abstract_Domain} --- \<^verbatim>\<open>sound_domain\<close>, lifted state concretization, display support.
    \<^item> @{theory Voblint_Framework.Transfer_Algebra} --- the pure abstract-state algebra a whole-state transfer computes in: the call-entry frame reset and formal binding, the structural return combine, and their soundness against \<^verbatim>\<open>gamma_state\<close>.
    \<^item> @{theory Voblint_Framework.DG_Local_State_Spec} --- the contract those operations owe (\<^verbatim>\<open>sound_transfer_for\<close>) and the two Base constructions built from them, with per-edge transfer soundness (\<^verbatim>\<open>edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>local_spec_step \<dots> a \<sigma>\<rbrakk>\<close>) and its \<^verbatim>\<open>EA_Check\<close> companion, the dispatch-point facts \<^theory>\<open>Voblint_Framework.DG_Spec_Sound\<close>'s \<^verbatim>\<open>step_sound\<close>/\<^verbatim>\<open>combine_sound\<close> obligations are discharged against.
    \<^item> @{theory Voblint_Framework.State_Restriction} --- the local/global restriction algebra the routed spine reassembles states with.
    \<^item> @{theory Voblint_Framework.DG_Keyed_Generator} --- \<^verbatim>\<open>routed_node_rhs_mono_eq\<close>/\<^verbatim>\<open>_mono_sides\<close>/\<^verbatim>\<open>_mono_deps\<close>: the vendored solver's \<^verbatim>\<open>TD_side_mono\<close> precondition, discharged once for an arbitrary generator instance.

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
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Checks} --- the Sign instance: derived
      numeric queries (read off \<^const>\<open>inv_less_sign\<close>/\<^const>\<open>inv_eq_sign\<close>/
      \<^const>\<open>meet_sign\<close>), no hand-built comparison tables.
    \<^item> @{theory Voblint_Analysis_Interval.Interval_Checks} --- the Interval instance:
      specialized bound-comparison queries (\<^const>\<open>interval_less_true\<close> and
      siblings, \<open>Interval_Numeric_Queries\<close>). The backward-domain default derives
      equality refutation through \<^const>\<open>intersect_ivl\<close>, whose canonical empty
      result is independent of the raw lattice \<^const>\<open>inf\<close>.

  \<^bold>\<open>4. Concrete domains.\<close> One analysis session per domain, all over the shared
    \<^verbatim>\<open>Voblint_Analysis_Base\<close>, all reaching the same spine.  Each pairs a lattice theory
    (order, transfers, soundness, monotonicity) with an \<^verbatim>\<open>_Analyses\<close> theory placing it at
    the routed D/G spine over \<^const>\<open>ltr_collect\<close>.
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Domain} / @{theory Voblint_Analysis_Sign.Sign_Analyses} --- the seven-element sign lattice.  Finite, so the plain-join solver computes an exact solution and no widening is needed.
    \<^item> @{theory Voblint_Analysis_Interval.Interval_Domain} / @{theory Voblint_Analysis_Interval.Interval_Analyses} --- intervals over the extended integers.  Infinite height, so this is the domain that needs widening and narrowing, and the one whose solver choice matters.
    \<^item> @{theory Voblint_Analysis_Parity.Parity_Domain} --- even/odd.  Finite like Sign, and expressible about values neither Sign nor Interval constrains: \<^verbatim>\<open>y := x * 2\<close> is even whatever \<^verbatim>\<open>x\<close> is.
    \<^item> @{theory Voblint_Analysis_Congruence.Congruence_Domain} --- residue classes, the one component with no analysis of its own: it is the fourth member of the product below, not a selectable analysis.
    \<^item> @{theory Voblint_Analysis_Int.Int_Domain} / @{theory Voblint_Analysis_Int.Int_Refinement} --- \<^verbatim>\<open>int_dom\<close>, the reduced product of the four above, with the exactness contract on reduction steps and the three refinement modes.
    \<^item> @{theory Voblint_Analysis_Relational.Rel_Order_Domain} --- an order carrier that is \<^emph>\<open>not\<close> a pointwise abstract state, kept to show the generator and solver never assumed one.

  \<^bold>\<open>4b. The D/G interface spine.\<close> The native, carrier-opaque Goblint-\<^verbatim>\<open>Spec\<close> interface
    (independent flow-sensitive local domain \<^verbatim>\<open>D\<close> and flow-insensitive global domain \<^verbatim>\<open>G\<close>),
    the canonical context-sensitive backbone.
    \<^item> @{theory Voblint_Framework.DG_Spec} --- the \<^verbatim>\<open>dg_spec\<close> record, one manager-native transfer per edge action, plus the \<^verbatim>\<open>dg_state\<close> copy lattice and the seeded keyed generator in @{theory Voblint_Framework.DG_Constraint_Trees}.
    \<^item> @{theory Voblint_Framework.DG_Spec_Sound} --- native heterogeneous soundness over opaque carriers (\<^verbatim>\<open>sound_dg_spec_core\<close>); the routed context locales in @{theory Voblint_Framework.Routed_Context} feed those obligations directly into \<^const>\<open>activation_collect\<close>, so the routed unit-context instance reaches \<^const>\<open>ltr_collect\<close> through \<^verbatim>\<open>ltr_collect_eq_Union_activation_of_fun\<close> (@{theory Voblint_Framework.Routed_Context_Unit}).
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Analyses} and
      @{theory Voblint_Analysis_Interval.Interval_Analyses} --- Sign and Interval as
      routed \<^verbatim>\<open>sound_dg_spec_core\<close> instances, each reaching \<^const>\<open>ltr_collect\<close>
      through the adapter's generic node-soundness bridge.

  \<^bold>\<open>4c. Activation-local certification.\<close> The concrete object the context-sensitive soundness
    rides: one trace per activation, with a stable call-only context.
    \<^item> @{theory Voblint_Framework.Activation_Backbone} --- the generic \<^verbatim>\<open>activation_collect_sound\<close>: over \<^const>\<open>valid_ltr\<close>, five obligations \<^verbatim>\<open>INIT\<close>/\<^verbatim>\<open>INTRA\<close>/\<^verbatim>\<open>CALL\<close>/\<^verbatim>\<open>RETURN\<close>/\<^verbatim>\<open>TOTAL\<close> (\<^verbatim>\<open>RETURN\<close> at the caller context, \<^verbatim>\<open>TOTAL\<close> on the context relation itself) on an arbitrary \<^verbatim>\<open>cover\<close> map bound \<^const>\<open>activation_collect\<close> at every \<^verbatim>\<open>(node, context)\<close>.
    \<^item> @{theory Voblint_Framework.DG_Ctx_Activation} --- DG-native discharge of those five obligations from a \<^verbatim>\<open>sound_dg_spec_core\<close> post-solution, so a computed D/G solution certifies the activation collecting.

  \<^bold>\<open>5. Executable frontend.\<close> Finite-map state representation and certified execution.
    \<^item> @{theory Voblint_Exec.Exec_St} --- executable abstract-state maps for code generation.
    \<^item> @{theory Voblint_Exec.Exec_Refinement} --- commutation bridge from executable states to function states.
    \<^item> @{theory Voblint_Exec.Exec_DG_Generator} --- the executable D/G equation generator (\<^const>\<open>unit_routed_eqs\<close>, \<^const>\<open>fun_of_dg_st_gen\<close>): the verified solver \<^emph>\<open>runs\<close> on D/G equations.
    \<^item> @{theory Voblint_Exec.DG_Local_State_Exec} --- \<^locale>\<open>routed_dg_domain_exec\<close> proves a registered domain's D/G spec sound directly at this executable carrier, with no separate abstract-carrier transport step.
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Exec} --- executable Sign transfer functions.
    \<^item> @{theory Voblint_Analysis_Sign.Sign_Analyses} --- the routed D/G runtime for Sign: the equation system, its solved table, and the termination hypothesis each solver discipline turns on.
    \<^item> @{theory Voblint_Analysis_Interval.Interval_Analyses} --- the Interval counterpart, with the join, per-origin and warrowing solver-choice siblings.

  \<^bold>\<open>5b. Solved results and reports.\<close> What a finished analysis \<^emph>\<open>is\<close>, before anyone
    renders or dispatches it.
    \<^item> @{theory Voblint_Framework.Analysis_Result} --- the domain-generic table: a covered key set of \<^typ>\<open>pp \<times> 'ctx\<close> pairs plus a total lookup.  \<^verbatim>\<open>wf_analysis_result\<close> asks for finitely many keys and canonical payloads; canonicality is unconditional because every publishing adapter canonicalizes, finiteness holds outright only where the context space is bounded in advance and is a hypothesis elsewhere.
    \<^item> @{theory Voblint_Framework.Check_Report} and @{theory Voblint_Framework.Contextual_Check_Report} --- the flat and per-context readings of that table.  They are genuinely different: a check can be \<^const>\<open>Dead\<close> in one context and decided in another, which a flat \<^typ>\<open>check_result\<close> cannot express, which is why the contextual report exists rather than a degraded flat view.
    \<^item> @{theory Voblint_Analysis_Base.Analysis_Config} --- the selection surface: \<^typ>\<open>analysis_domain\<close>, \<^typ>\<open>solver_choice\<close>, \<^typ>\<open>context_mode\<close>, and \<^const>\<open>resolve_analysis_config\<close>, which decides once and centrally which combinations are legal.  Unsupported pairings answer \<^const>\<open>None\<close> rather than degrading silently.

  \<^bold>\<open>6. End-to-end theorems.\<close> Headline soundness and the source bridge.
    \<^item> @{theory Voblint_Soundness.Source_Activation_Sound} --- the source-adequacy bridge: a reachable VIMP source configuration produces a \<^const>\<open>valid_ltr\<close> trace (\<^verbatim>\<open>source_run_has_ltr\<close>), bounded at its activation context (\<^verbatim>\<open>source_activation_sound\<close>) and monovariantly (\<^verbatim>\<open>source_reaches_ltr_collect\<close>).
    \<^item> @{theory Voblint_Soundness.Run_Analysis_Sound} --- the bundle every flagship and every codegen entry point applies: one \<^verbatim>\<open>solve_c ... \<noteq> None\<close> fact in, source-level soundness out, with solver correctness, executable-to-pure commutation, post-solution transport and D/G collecting soundness discharged inside.  It bundles partial correctness only --- that the solver \<^emph>\<open>returns\<close> is supplied by the caller, typically \<^theory_text>\<open>by eval\<close>, and is not a theorem of this development.

  \<^bold>\<open>7. Examples and witnesses.\<close> Executable demos, precision witnesses, tooling --- the
    complete end-to-end analyses (the four domain flagships \<open>Example_Interval_DG_Flagship\<close>,
    \<open>Exec_Sign_DG_Run\<close>, \<open>Example_Parity_DG_Flagship\<close> and \<open>Exec_Int_DG_Run\<close>, and the
    context-sensitive \<open>Example_Interval_DG_Ctx_Collect\<close>,
    \<open>Example_Interval_DG_EntryState_Collect\<close>, \<open>Example_Interval_Source_Ctx\<close>) are indexed
    separately, above.
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
    \<^item> @{theory Voblint_Examples_Congruence.Example_Congruence_Arithmetic} and
      @{theory Voblint_Examples_Congruence.Example_Congruence_Backward} --- the fourth
      product component exercised on its own: modular arithmetic, and the backward
      filtering that makes it the one component with a real inverse.
    \<^item> @{theory Voblint_Examples_CLI.Example_Int_Refinement_Mode_Regression} --- the mode ladder
      pinned at the composite operation itself (\<^const>\<open>plus_int_dom\<close> under each of the
      three modes), the complement to @{theory Voblint_Examples_Int.Exec_Int_DG_Run}, which
      settles the same ladder through real solver runs.  Here \<^const>\<open>Refine_Once\<close> is
      \<^emph>\<open>not\<close> yet the fixpoint, which is why one witness of each kind is kept.
    \<^item> @{theory Voblint_Examples_CLI.Exec_Interval_Run} --- the same bounded loop under bounded
      Kleene iteration, warrowing TD, and every update rule at once: interval narrowing and
      the backward guard filter, not the update rule, are what recover \<open>[0,20]\<close>.
    \<^item> @{theory Voblint_Examples_CLI.Example_Analysis_Result_Regression} --- the published result
      table and its per-context lookup surface.
    \<^item> @{theory Voblint_Examples_CFG.Example_Inc_Proc} --- shared global-increment procedure witness.
    \<^item> @{theory Voblint_Examples_CLI.Example_Side_Execute} --- minimal certified Sign IP example with annotated CFG DOT.
    \<^item> @{theory Voblint_Examples_Interval.Example_Proc_Call} --- concrete-semantics witness for \<^verbatim>\<open>inc\<close> and \<^verbatim>\<open>sqr\<close> procedures communicating through a global, and their compiled interprocedural CFG; a Sign analysis of the same shared-global increment call is \<^verbatim>\<open>tests/regression/07-sign-precision/precision/10-single_call_global_increment.vimp\<close>.
    \<^item> @{theory Voblint_Examples_Interval.Example_Interval_Loop_Coverage} --- backward guard-refinement precision witness for a bounded loop's body entry; the certified computed bound at the loop head is @{text "Exec_Interval_Run"}'s.
    \<^item> @{theory Voblint_Examples_Interval.Example_Guard_Refinement} --- backward guard refinement precision witness.
    \<^item> @{theory Voblint_Examples_Interval.Example_Interval_DG_CallString_K1} --- the \<open>nest\<close> program,
      computed and certified at a 1-call-string context
      (\<^verbatim>\<open>nest_1_activation_collect_sound\<close>): \<open>main\<close> calls \<open>f\<close> from two sites and \<open>f\<close>
      calls \<open>g\<close> from one, so a 1-call-string cannot separate \<open>g\<close>'s two activations.
    \<^item> @{theory Voblint_Examples_Interval.Example_Interval_DG_CallString_K2} --- the same program at a
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
      \<^verbatim>\<open>unit_routed_eqs\<close>/vendored-solver pipeline as Sign/Interval, this time
      over \<^verbatim>\<open>Voblint_Analysis_Relational.Rel_Order_Domain\<close>'s non-\<^verbatim>\<open>abs_state\<close>
      relational carrier; the computed result is compared against
      Interval's on the identical program and rendered, raw and
      analysis-annotated, via GraphViz.

  \<^bold>\<open>8. Tooling.\<close> Theories outside the core proof spine.
    \<^item> \<^bold>\<open>Named global unknowns\<close> --- a keyed global family is the routed D/G
      context's own \<open>gkey\<close>, and \<^const>\<open>dep_aux\<close> pins what a per-edge tree reads:
      @{thm dep_aux_dg_edge_tree_at} names the source address and the one
      global slot, nothing else.
    \<^item> \<^bold>\<open>Rendering\<close> --- \<^const>\<open>raw_cfg_dot_lit\<close> and the \<open>_graph_snapshot_auto\<close> /
      \<open>_export_auto\<close> family (@{theory Voblint_CLI.State_Report_GraphViz}) have no
      Isabelle-side witness of
      their own: rendering asserts nothing that a \<^verbatim>\<open>writeln\<close> could check, so the
      fixtures under \<^verbatim>\<open>tests/regression/\<close> carry it instead --- \<^verbatim>\<open>08-tooling\<close> for
      \<^verbatim>\<open>--dot\<close>, \<^verbatim>\<open>13-full-state-dot\<close> for the per-node state labels, and
      \<^verbatim>\<open>11-graph-snapshot\<close> for golden cluster/node/edge snapshots including a
      recursive procedure. Those compare output; a build-time render only proves
      it did not crash.
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

  \<^bold>\<open>9. The CLI: configuration, dispatch, and code generation.\<close> A runtime-program entry point per domain,
    reusing the exact native D/G pipeline behind \<open>4b\<close>/\<open>5\<close> above rather than a
    parallel one, exported to OCaml.
    \<^item> @{theory Voblint_CLI.Sign_Entry} --- \<^verbatim>\<open>analyse_sign\<close>
      takes an arbitrary \<^typ>\<open>imp_prog\<close> at runtime (not a fixed example
      program) and reuses \<^verbatim>\<open>ownership_split_dg_exec_analysis\<close>'s own \<^verbatim>\<open>run_source_sound\<close>
      and \<^verbatim>\<open>collect_sound\<close> (@{theory Voblint_Soundness.Run_Analysis_Sound})
      for its soundness theorems. \<^verbatim>\<open>analyse_sign_report\<close> classifies every
      compiled \<^verbatim>\<open>__voblint_check(...)\<close> against that same computed
      post-solution via \<^locale>\<open>abstract_check_domain\<close>'s
      \<^verbatim>\<open>classify_checks\<close>, so the report and the soundness theorem share one
      computation, not two.
    \<^item> @{theory Voblint_CLI.Interval_Entry} --- \<^verbatim>\<open>analyse_interval_dg\<close>/
      \<^verbatim>\<open>analyse_interval_td_report\<close>, the Interval counterpart production \<^verbatim>\<open>analyse\<close> actually
      dispatches to, built the same way on \<^verbatim>\<open>local_state_dg_exec_analysis\<close>'s own \<^verbatim>\<open>run_source_sound\<close>/
      \<^verbatim>\<open>collect_sound\<close>. \<^verbatim>\<open>Interval_Checks\<close> additionally carries \<^verbatim>\<open>analyse_interval_report\<close>/
      \<^verbatim>\<open>analyse_interval_report_per_origin\<close>, the always-join and per-origin update-rule siblings
      \<^verbatim>\<open>analyse_with_solver\<close> (@{theory Voblint_CLI.Analyse_Dispatch}) compares against this
      same production default on the identical equation system, each with its own soundness
      theorems proved the same way, in @{theory
      Voblint_CLI.Interval_Entry}.
    \<^item> @{theory Voblint_CLI.Int_Entry} --- the \<^verbatim>\<open>int_dom\<close> counterpart,
      \<^verbatim>\<open>analyse_int_report\<close>, built the same way; the product's refinement mode is fixed
      inside the entry point, not exposed as a CLI axis.
    \<^item> @{theory Voblint_CLI.Parity_Entry} --- \<^verbatim>\<open>analyse_parity_report\<close>, the fourth
      selectable analysis, again on the same locale's \<^verbatim>\<open>run_source_sound\<close>/\<^verbatim>\<open>collect_sound\<close>.
    \<^item> @{theory Voblint_CLI.Analyse_Dispatch} --- \<^const>\<open>analyse\<close> dispatches
      \<^typ>\<open>analysis_domain\<close> to the four domains' report functions, all sharing the
      observable \<^typ>\<open>check_report_entry list\<close> result type
      (@{theory Voblint_Framework.Abstract_Checks}), so the dispatcher adds no new proof.
      Interval's branch is the warrowing report \<^const>\<open>analyse_interval_td_report\<close>: that
      is the production default, carrying its own soundness theorems, not an unproved
      alternative parked outside the dispatcher.

      Above \<^const>\<open>analyse\<close> sit the two configuration-driven entry points.
      \<^const>\<open>analyse_config\<close> answers a flat report and \<^const>\<open>analyse_config_ctx\<close> a
      per-context one; both route through \<^const>\<open>resolve_analysis_config\<close>, so which
      (domain, solver, context) triples are legal is decided in exactly one place.  The
      split is not cosmetic: entry-state and call-string routing have no honest flat
      report, because a check can be \<^const>\<open>Dead\<close> in one context and decided in another,
      so \<^const>\<open>analyse_config\<close> answers \<^const>\<open>None\<close> there rather than flattening.
      \<^verbatim>\<open>dispatch_demo_interval_precise\<close> computes (\<^verbatim>\<open>by eval\<close>) one program's report, and
      the executable corpus under \<^verbatim>\<open>tests/regression/\<close> runs the same analyses through the
      generated CLI.

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
      typically discharged \<^verbatim>\<open>by eval\<close> through the domain's own
      \<^verbatim>\<open>*_terminates_prog_via_solve_c\<close> --- and a proof that the
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
    \<^item> the generic D/G generator \<^verbatim>\<open>unit_routed_eqs\<close> emits the equation system;
    \<^item> the verified solver \<^emph>\<open>computes\<close> a solution (\<^verbatim>\<open>solve_c ... = Some sigma\<close>, \<^verbatim>\<open>by eval\<close>);
    \<^item> the registered endpoint \<open>flagship_ex_reg.run_source_sound\<close>
      (@{theory Voblint_Soundness.Run_Analysis_Sound}'s \<^verbatim>\<open>ownership_split_dg_exec_analysis\<close>
      locale) bundles solver correctness, executable/pure commutation,
      post-solution transport, and D/G collecting soundness into one
      application, bounding \<open>ltr_collect g S v\<close> at every program point.

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
