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
    "Voblint_Core.TD_Side_CFG"
    "Voblint_Core.TD_Side_Eff_Cone_Lemmas"
    "Voblint_Analysis.Sign_Domain"
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_Analysis.Interval_Domain"
    "Voblint_Analysis.Interval_Side_Soundness"
    "Voblint_Core.DG_Framework"
    "Voblint_Core.DG_Soundness"
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Mixed_Sign_Interval"
    "Voblint_Core.Activation_Backbone"
    "Voblint_Core.DG_Ctx_Activation"
    "Voblint_Core.Exec_St"
    "Voblint_Core.Exec_Bridge"
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Sign_Named_Global_Eff"
    Exec_Sign_Run
    Exec_Sign_DG_Run
    Example_Interval_DG_Flagship
    "Voblint_Formalization.Mixed_Flow_Sound"
    "Voblint_Formalization.Source_Activation_Sound"
    Example_Interval_DG_Ctx_Collect
    Example_Interval_DG_CallString
    Example_Interval_DG_CallString_K1
    Example_Interval_DG_CallString_K2
    Example_Sign_DG_CallString_K1
    Example_Sign_DG_CallString_K2
    Call_String_Solver_Refinement
    Example_Interval_Source_Ctx
    Example_Inc_Proc
    Example_Side_Execute
    Example_Side_Branch_Calls
    Example_Side_Proc_Global
    Example_Interval_Side_Proc_Global
    Example_Mixed_Flow_Sign
    Example_Proc_Call
    Example_Interval_Loop_Coverage
    Example_Guard_Refinement
    Example_Proc_GraphViz
    Example_Relational_DG_Demo
    Example_Strategy_Tree_Demo
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
  Three routing policies for the same \<open>twice\<close> program (called from two sites), each
  certified against the same activation-indexed semantics.

  \<^item> \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_Ctx_Collect}\<close> --- context routed by
    \<open>ivl_enterc\<close>: the entered formal's point abstraction (partial tabulation,
    \<^cite>\<open>SeidlEtAl2026\<close> Example 8). \<^verbatim>\<open>twice_activation_collect_sound\<close> bounds
    \<^const>\<open>activation_collect\<close> at every \<open>(node, context)\<close>.
  \<^item> \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_CallString}\<close> --- context routed by
    \<open>route_cs\<close>: the call site itself (1-call-string, \<^cite>\<open>SeidlEtAl2026\<close> Example 7).
    \<^verbatim>\<open>twice_cs_activation_collect_sound\<close> is the same soundness shape as \<open>Ctx_Collect\<close>, for a
    routing policy that needed \<open>enterc\<close> widened to see the call site (issue \<open>#66\<close>, G1) to be
    expressible at all.
  \<^item> \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_Source_Ctx}\<close> --- the sharpest of the three:
    bound against \<^emph>\<open>actual source runs\<close> at each activation's own context, not just the
    collecting semantics, so it is the source-level counterpart of \<open>Ctx_Collect\<close>.
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

  The proof is layered into four Isabelle sessions.  The index below separates the proof spine from
  executable frontends, DOT exporters, and research witnesses.

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
    \<^item> @{theory Voblint_Core.Constraint_System} --- pure and effectful transfer interfaces, \<^verbatim>\<open>glob_env\<close>, \<^verbatim>\<open>sound_transfer\<close>, \<^verbatim>\<open>sound_effectful_transfer\<close>.
    \<^item> @{theory Voblint_Core.Constraint_System_Sound} --- per-edge / per-combine transfer soundness (\<^verbatim>\<open>edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a \<sigma>\<rbrakk>\<close>), the building blocks of the monovariant trace endpoint \<^verbatim>\<open>unified_ltr_post_fixpoint_sound\<close> (in \<^verbatim>\<open>LTR_Analysis_Sound\<close>, over \<^const>\<open>ltr_collect\<close>).
    \<^item> @{theory Voblint_Core.TD_Side_CFG} --- mixed local/global abstraction: \<^verbatim>\<open>side_env\<close>, local/global restrictions, unit-global effectful tree constructors.
    \<^item> @{theory Voblint_Core.TD_Side_Eff_Cone_Lemmas} --- query-cone soundness for the
      effectful TD_side solver over \<^const>\<open>ltr_collect\<close>
      (\<^verbatim>\<open>side_collect_sound_in_eff_cone\<close>), with the exit corollary
      \<^verbatim>\<open>side_collect_sound_exit_eff_ltr_cone\<close>, \<^verbatim>\<open>threefold_mono\<close>, and
      \<^verbatim>\<open>cone_compatible_etf\<close>.

  \<^bold>\<open>4. Concrete domains.\<close> Domain instances used by the proof spine and examples.
    \<^item> @{theory Voblint_Analysis.Sign_Domain} --- Sign lattice, transfer functions, soundness, monotonicity, display instance.
    \<^item> @{theory Voblint_Analysis.Sign_Side_Soundness} --- Sign at the effectful side IP solver, over \<^const>\<open>ltr_collect\<close>.
    \<^item> @{theory Voblint_Analysis.Interval_Domain} --- interval lattice, widening, transfer functions, soundness, monotonicity.
    \<^item> @{theory Voblint_Analysis.Interval_Side_Soundness} --- Interval at the effectful side IP solver, over \<^const>\<open>ltr_collect\<close>.

  \<^bold>\<open>4b. The D/G interface spine.\<close> The native, carrier-opaque Goblint-\<^verbatim>\<open>Spec\<close> interface
    (independent flow-sensitive local domain \<^verbatim>\<open>D\<close> and flow-insensitive global domain \<^verbatim>\<open>G\<close>),
    the canonical context-sensitive backbone.
    \<^item> @{theory Voblint_Core.DG_Framework} --- the \<^verbatim>\<open>dg_spec\<close> record (\<^verbatim>\<open>step : D => G => G x D\<close>), the \<^verbatim>\<open>dg_state\<close> copy lattice, the seeded keyed generator.
    \<^item> @{theory Voblint_Core.DG_Soundness} --- native heterogeneous soundness over opaque carriers (\<^verbatim>\<open>sound_dg_spec\<close>); the shared closure obligations \<^verbatim>\<open>dg_postfix_gamma_{entry,edge,combine}\<close> feed the trace endpoint \<^verbatim>\<open>dg_post_solution_collect_sound_ltr\<close>.
    \<^item> @{theory Voblint_Analysis.Sign_DG} --- Sign as a diagonal \<^verbatim>\<open>sound_dg_spec\<close> instance.
    \<^item> @{theory Voblint_Analysis.Interval_DG} --- Interval as a diagonal instance (\<^verbatim>\<open>ivl_dg_post_solution_collect_sound\<close>, over \<^const>\<open>ltr_collect\<close>).
    \<^item> @{theory Voblint_Analysis.Mixed_Sign_Interval} --- the mixed flagship: Sign locals with Interval globals, both mixed-domain and context-sensitive.

  \<^bold>\<open>4c. Activation-local certification.\<close> The concrete object the context-sensitive soundness
    rides: one trace per activation, with a stable call-only context.
    \<^item> @{theory Voblint_Core.Activation_Backbone} --- the generic \<^verbatim>\<open>activation_collect_sound\<close>: over \<^const>\<open>valid_ltr\<close>, four obligations \<^verbatim>\<open>ENTRY_G\<close>/\<^verbatim>\<open>EDGE\<close>/\<^verbatim>\<open>SEED_G\<close>/\<^verbatim>\<open>COMB\<close> (\<^verbatim>\<open>COMB\<close> at the caller context) bound \<^const>\<open>activation_collect\<close> at every \<^verbatim>\<open>(node, context)\<close>.
    \<^item> @{theory Voblint_Core.DG_Ctx_Activation} --- DG-native discharge of those four obligations from a \<^verbatim>\<open>sound_dg_spec\<close> post-solution, so a computed D/G solution certifies the activation collecting.

  \<^bold>\<open>5. Executable frontend.\<close> Finite-map state representation and certified execution.
    \<^item> @{theory Voblint_Core.Exec_St} --- executable abstract-state maps for code generation.
    \<^item> @{theory Voblint_Core.Exec_Bridge} --- commutation bridge from executable states to function states.
    \<^item> @{theory Voblint_Analysis.Exec_DG_Bridge} --- executable transport for the D/G spine (\<^verbatim>\<open>fun_of_dg_st\<close>, \<^verbatim>\<open>dg_gen_of\<close>, \<^verbatim>\<open>part_post_solution_dg_st_to_abs\<close>): the verified solver \<^emph>\<open>runs\<close> on D/G equations.
    \<^item> @{theory Voblint_Analysis.Sign_Exec} --- executable Sign transfer functions.
    \<^item> @{theory Voblint_Analysis.Sign_Exec_Sound} --- executable Sign IP solver, trace soundness, annotated DOT entry points.

  \<^bold>\<open>6. End-to-end theorems.\<close> Headline soundness and the source bridge.
    \<^item> @{theory Voblint_Formalization.Mixed_Flow_Sound} --- mixed flow-sensitive soundness and optimality over \<^const>\<open>ltr_collect\<close> (\<^verbatim>\<open>mixed_flow_analysis_sound\<close> / \<^verbatim>\<open>mixed_flow_analysis_optimal\<close>).
    \<^item> @{theory Voblint_Formalization.Source_Activation_Sound} --- the source-adequacy bridge: a reachable VIMP source configuration produces a \<^const>\<open>valid_ltr\<close> trace (\<^verbatim>\<open>source_run_has_ltr\<close>), bounded at its activation context (\<^verbatim>\<open>source_activation_sound\<close>) and monovariantly (\<^verbatim>\<open>source_reaches_ltr_collect\<close>).

  \<^bold>\<open>7. Examples and witnesses.\<close> Executable demos, precision witnesses, tooling --- the
    complete end-to-end analyses (\<open>Example_Interval_DG_Flagship\<close>, \<open>Exec_Sign_DG_Run\<close>,
    \<open>Example_Interval_DG_Ctx_Collect\<close>, \<open>Example_Interval_DG_CallString\<close>,
    \<open>Example_Interval_Source_Ctx\<close>) are indexed separately, above.
    \<^item> @{theory Voblint_Examples.Example_Inc_Proc} --- shared global-increment procedure witness.
    \<^item> @{theory Voblint_Examples.Example_Side_Execute} --- minimal certified Sign IP example with annotated CFG DOT.
    \<^item> @{theory Voblint_Examples.Example_Side_Branch_Calls} --- branching procedure called twice; flow-sensitive locals, flow-insensitive globals.
    \<^item> @{theory Voblint_Examples.Example_Side_Proc_Global} --- Sign IP analysis on the shared global-increment call.
    \<^item> @{theory Voblint_Examples.Example_Interval_Side_Proc_Global} --- Interval IP analysis on the same.
    \<^item> @{theory Voblint_Examples.Example_Mixed_Flow_Sign} --- the mixed-flow soundness/optimality theorem applied to Sign.
    \<^item> @{theory Voblint_Examples.Example_Proc_Call} --- Interval analysis of \<^verbatim>\<open>inc\<close> and \<^verbatim>\<open>sqr\<close> procedures communicating through a global.
    \<^item> @{theory Voblint_Examples.Example_Interval_Loop_Coverage} --- Interval analysis of a bounded loop.
    \<^item> @{theory Voblint_Examples.Example_Guard_Refinement} --- backward guard refinement precision witness.
    \<^item> @{theory Voblint_Examples.Example_Interval_DG_CallString_K1} --- the same \<open>nest\<close>
      program as \<open>Example_Interval_DG_CallString\<close>, computed and certified at a 1-call-string
      context (\<^verbatim>\<open>nest_1_activation_collect_sound\<close>): \<open>main\<close> calls \<open>f\<close> from two sites and \<open>f\<close>
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
      this pair supports a genuine strict-precision witness that \<open>Call_String_Solver_Refinement\<close>'s
      projection argument does not state: \<^verbatim>\<open>sign_k2_strictly_more_precise_than_k1_at_g\<close> proves
      the 2-call-string value at \<open>g\<close>'s entry is strictly below the 1-call-string \<open>STop\<close> merge in
      the Sign order, for both activations, \<^emph>\<open>computed and compared\<close> rather than argued
      abstractly.
    \<^item> @{theory Voblint_Examples.Call_String_Solver_Refinement} --- a solver-level refinement
      witness, not a source-level soundness theorem: projects the computed 2-call-string
      solution onto the 1-call-string dependency cone (\<^verbatim>\<open>project_sigma\<close>) and proves the
      projection is itself a \<^verbatim>\<open>part_post_solution\<close> of the 1-call-string equations
      (\<^verbatim>\<open>project_sigma_part_post_solution\<close>).
    \<^item> @{theory Voblint_Examples.Example_Proc_GraphViz} --- plain procedural CFG DOT export examples.
    \<^item> @{theory Voblint_Examples.Example_Relational_DG_Demo} --- an execution
      witness, not a soundness-certified result: a compiled full-program
      `if (x < y) { z := 1 } else { z := 0 }` runs through the *same*
      \<^verbatim>\<open>dg_gen_of\<close>/vendored-solver pipeline as Sign/Interval, this time
      over \<^verbatim>\<open>Voblint_Analysis.Rel_Order_Domain\<close>'s non-\<^verbatim>\<open>abs_state\<close>
      relational carrier; the computed result is compared against
      Interval's on the identical program and rendered, raw and
      analysis-annotated, via GraphViz.

  \<^bold>\<open>8. Tooling.\<close> Theories outside the core proof spine.
    \<^item> @{theory Voblint_Examples.Exec_Sign_Run} --- code-generation probe on a hand-written Sign equation system.
    \<^item> @{theory Voblint_Analysis.Sign_Named_Global_Eff} --- named-global routing witness; the solver-compatible constant route and the conditional-route monotonicity boundary.
    \<^item> \<^bold>\<open>Related demo:\<close> @{theory Voblint_Examples.Example_Strategy_Tree_Demo} ---
      \<^type>\<open>strategy_tree\<close> as a small dependency/effect language on its own,
      independent of any abstract domain: a Fibonacci equation tree built with
      \<^const>\<open>answer\<close> and \<^const>\<open>seqcomp_tree\<close>, run with \<open>traverse_rhs\<close>.
\<close>

text \<open>
  \<^bold>\<open>The D/G execution pipeline (headline).\<close> The flagship threads a single chain,
  every step machine-checked, from source to a soundness theorem over the
  \<^emph>\<open>computed\<close> analysis result:

    \<^item> VIMP source \<^verbatim>\<open>compile_prog\<close> to a CFG;
    \<^item> the generic D/G generator \<^verbatim>\<open>dg_gen_of\<close> emits the equation system;
    \<^item> the verified solver \<^emph>\<open>computes\<close> a solution (\<^verbatim>\<open>solve_c ... = Some sigma\<close>, \<^verbatim>\<open>by eval\<close>);
    \<^item> the solver's own correctness theorem certifies \<^verbatim>\<open>part_post_solution sigma\<close> --- no re-checking;
    \<^item> the native endpoint \<open>ivl_dg_post_solution_collect_sound\<close> bounds
      \<open>ltr_collect g S v\<close> at every program point.

  \<^bold>\<open>Soundness spine.\<close> The context-sensitive analyses converge on one native
  interface, the carrier-opaque \<^verbatim>\<open>sound_dg_spec\<close>; Sign, Interval, and
  the mixed flagship are its instances, and context slicing is factored through
  the functional activation spine and its per-context keyed slots. The base
  flow-sensitive spine is the query-cone endpoint
  \<^verbatim>\<open>side_collect_sound_in_eff_cone\<close>, instantiated for Sign and Interval over
  \<^const>\<open>ltr_collect\<close> on the original CFG. Its exit corollary
  \<^verbatim>\<open>side_collect_sound_exit_eff_ltr_cone\<close> uses \<open>q = cfg_exit g\<close>. The cone
  restriction lives in the abstract concretization guard, not in a graph
  transformation.
\<close>

end
