(* SPDX-License-Identifier: MIT *)

section \<open>Voblint: a verified abstract interpreter for IMP2\<close>

theory Voblint
  imports
    "Voblint_IMP2.IMP2_Syntax"
    "Voblint_IMP2.IMP2_Expr"
    "Voblint_IMP2.IMP2_Globals"
    "Voblint_IMP2.IMP2_Proc"
    "Voblint_IMP2.IMP2_Notation"
    "Voblint_IMP2.IMP2_Bridge"
    "Voblint_CFG.CFG_Def"
    "Voblint_CFG.CFG_Path"
    "Voblint_CFG.IMP2_Proc_to_CFG"


    "Voblint_CFG.CFG_Local_Trace"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Analysis.Abstract_Domain"
    "Voblint_Analysis.Constraint_System"
    "Voblint_Analysis.Constraint_System_Sound"
    "Voblint_Analysis.TD_Side_CFG"
    "Voblint_Analysis.TD_Side_Eff_Soundness"
    "Voblint_Analysis.Sign_Domain"
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_Analysis.Interval_Domain"
    "Voblint_Analysis.Interval_Side_Soundness"

    "Voblint_Analysis.DG_Framework"
    "Voblint_Analysis.DG_Soundness"
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Mixed_Sign_Interval"
    "Voblint_Analysis.Activation_Backbone"
    "Voblint_Analysis.DG_Ctx_Activation"
    "Voblint_Analysis.Exec_St"
    "Voblint_Analysis.Exec_Bridge"
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
    Example_Interval_Source_Ctx
    Example_Inc_Proc
    Example_IMP2_Coverage
    Example_Side_Execute
    Example_Side_Branch_Calls
    Example_Side_Proc_Global
    Example_Interval_Side_Proc_Global
    Example_Mixed_Flow_Sign
    Example_Proc_Call
    Example_Interval_Loop_Coverage
    Example_Guard_Refinement
    Example_Proc_GraphViz
begin

text \<open>
  \<^bold>\<open>What this development proves.\<close>  An end-to-end soundness proof for a Goblint-style abstract
  interpreter for IMP2, machine-checked from the source operational semantics to the
  \<^emph>\<open>computed\<close> analysis result.  The whole pipeline, each arrow a theorem:

  \<^verbatim>\<open>
    IMP2 source program          (pstep: small-step operational semantics)
         |
         |  compile_prog                          [ FORWARD-SIMULATES ]
         |     control_step_simulation            every source step is matched
         |     concrete_program_step_match        by a run of CFG steps
         v
    compiled CFG  +  located run  (cstep) ------------------------+
         |                                                        |  dg_gen_of
         |  source_run_has_ltr          [ WITNESS ]               v
         |     ltr_repr / stack_repr                       equation system
         |     (source run has a valid_ltr witness)              |
         v                                                        |  TD_side solve_c
    valid_ltr                                                     |  (verified solver,
      == THE SOLE CONCRETE CFG SEMANTICS ==                       |   computes by eval)
      activation-local traces: Root / Call / Resume,              v
      each return matched to its own caller by caller_of    solution  sigma
         |                                                        |
         |  sink / key projection    [ CONCRETE PROJECTION ]     |  part_post_solution
         |     (forgetful; no abstract stores introduced)        |  (solver-certified)
         v                                                        v
    ltr_collect / ltr_collect_keyed /                     abstract post-solution
    activation_collect                                            |
         |                                                        |
         +----------------------< SOUNDNESS >--------------------+
                                     |
                                     v
       [ ABSTRACT OVER-APPROXIMATION -- the abstract side may lose precision;
         soundness proves the final inclusion ]
       all-node:   C v            \<subseteq>  gamma (sigma v)
          unified_ltr_post_fixpoint_sound      (monovariant)
          dg_post_solution_collect_sound_ltr   (D/G)
          activation_collect_sound             (per calling context)
       exit only:  C (cfg_exit g) \<subseteq>  gamma (sigma (cfg_exit g))
          side_collect_sound_exit_eff_ltr_cone (effectful, cone-guarded)
  \<close>

  \<^bold>\<open>Reading the diagram.\<close>  The left column is the \<^emph>\<open>concrete\<close> spine, the right column the
  \<^emph>\<open>abstract\<close> computation; they meet at the soundness inclusion.  Two kinds of arrow:

    \<^item> \<^bold>\<open>[ FORWARD-SIMULATES / PROJECTS ]\<close> --- no abstract-domain approximation occurs here.
      Compilation is a proved \<^emph>\<open>forward\<close> simulation (\<^verbatim>\<open>control_step_simulation\<close> /
      \<^verbatim>\<open>concrete_program_step_match\<close>, \<^theory>\<open>Voblint_CFG.Control_Simulation\<close>): every source
      run has a matching CFG run --- only the source-to-CFG direction is claimed, \<^bold>\<open>not\<close>
      equivalence, a backward simulation, or absence of extra CFG runs.  A source run then has a
      \<^const>\<open>valid_ltr\<close> \<^emph>\<open>witness\<close> (\<^verbatim>\<open>source_run_has_ltr\<close>,
      \<^theory>\<open>Voblint_CFG.Located_LTR\<close>) --- \<^bold>\<open>no adequacy is assumed\<close>.  The collectors are
      \<^emph>\<open>forgetful\<close> projections: a non-injective key may group several activations under one slot,
      but every collected store still comes from an actual \<^const>\<open>valid_ltr\<close> --- no abstract stores
      are introduced.
    \<^item> \<^bold>\<open>[ ABSTRACT OVER-APPROXIMATION ]\<close> --- the only \<^emph>\<open>semantic\<close> relaxation.  The abstract
      side may lose precision at several operations (abstract transfer, join, widening, context
      merging, finite keys); soundness justifies them together by one inclusion,
      \<open>C v \<subseteq> gamma (sigma v)\<close> --- every concrete store reaching \<open>v\<close> is admitted by the abstract
      slot: at \<^emph>\<open>every\<close> program point for the plain / keyed / D/G endpoints, and at
      \<open>cfg_exit g\<close> for the cone-guarded effectful endpoint.  Under threefold monotonicity the solver
      result is also the \<^emph>\<open>least\<close> partial post-solution (\<^verbatim>\<open>mixed_flow_analysis_optimal\<close>).

  No abstract-domain approximation occurs before the final inclusion: the source-to-CFG connection
  is a proved forward simulation and the collectors are projections of valid traces; only \<open>gamma\<close>
  abstracts.  So a proof of the concrete side (source through \<^const>\<open>valid_ltr\<close>) plus one soundness
  endpoint discharges the whole chain.

  \<^bold>\<open>The base semantics: activation-local traces.\<close>  Everything rests on \<^emph>\<open>one\<close> concrete
  semantics, \<^const>\<open>valid_ltr\<close> --- the \<^emph>\<open>activation-local trace semantics\<close> of a compiled,
  stack-disciplined CFG.  A trace value is one procedure activation together with its ancestry:

    \<^item> \<^verbatim>\<open>Root path\<close> --- the \<open>main\<close> activation;
    \<^item> \<^verbatim>\<open>Call caller path\<close> --- a callee, its caller frozen at the call node, the path starting
      at the parameter-bound entry store;
    \<^item> \<^verbatim>\<open>Resume caller callee path\<close> --- a caller continued past a completed call.

  Calls and returns are correlated by these constructors: \<^verbatim>\<open>caller_of\<close> recovers the creating
  caller \<^emph>\<open>structurally\<close> (descending a \<^verbatim>\<open>Resume\<close>), so each return composes with its \<^bold>\<open>own\<close>
  caller and recursion is first-class.  The analyser is therefore proved sound against the semantics
  that actually matches returns, not a broad graph-store closure.  Soundness is read off three
  forgetful projections of \<^const>\<open>valid_ltr\<close>:

    \<^item> \<^const>\<open>ltr_collect\<close> --- the monovariant set of stores reaching a program point;
    \<^item> \<^const>\<open>ltr_collect_keyed\<close> --- that set filtered by an arbitrary trace key;
    \<^item> \<^const>\<open>activation_collect\<close> --- the activation-keyed projection, definitionally
      \<^const>\<open>ltr_collect_keyed\<close> at the structural activation key (per calling context).

  The CFG layer contributes only graph structure (edges, paths, reachability, pruning) and the
  concrete store-transfer primitives in \<^theory>\<open>Voblint_CFG.CFG_Transfer\<close>; the abstract
  endpoints, domains, and the source bridge all read the analyser back through these projections.

  \<^bold>\<open>The semantic hierarchy (one concrete semantics).\<close>  After the single-semantics
  convergence there is exactly one concrete CFG execution semantics; everything else is a projection
  or an abstraction of it --- there is no parallel graph-store collecting semantics:

  \<^verbatim>\<open>
    valid_ltr                       concrete interprocedural execution (activation traces)
      |                             -- the only place caller/callee correlation lives --
      +-- ltr_collect               forgetful node-indexed projection
      +-- ltr_collect_keyed         forgetful key-indexed projection (a non-injective key may
      |     = activation_collect     merge activations; no concrete store invented)
      |                              at the structural activation key (per calling context)
      |
      ltr_gamma                     generic interface for proving over-approximation
        |
        domain / solver endpoints   its instantiations (Sign, Interval, mixed, D/G)
  \<close>

  \<^bold>\<open>Canonical theorem map.\<close>  The load-bearing theorems on the chain, and what each gives.
  The first block is concrete --- a forward simulation and forgetful projections, with no
  abstract-domain approximation; the second is over-approximation
  (\<open>concrete \<subseteq> gamma (abstract)\<close>).  Scope matters: the effectful row holds at the program
  \<^emph>\<open>exit\<close> only, the others at \<^emph>\<open>every\<close> program point.

  \<^verbatim>\<open>
   -- concrete: forward simulation + forgetful projection (no abstraction) --
   IMP2 source -> CFG run   control_step_simulation             a source step is forward-simulated
                            concrete_program_step_match          by a run of CFG steps
   CFG run -> local trace   source_run_has_ltr                  every reachable source config has
                                                                a valid_ltr witness
   source -> plain coll.    source_reaches_ltr_collect          reached store is in ltr_collect
   source -> keyed coll.    source_store_in_activation_collect  reached store is in activation_collect
                                                                at its calling context

   -- over-approximating (concrete stores subset of gamma(abstract)) --
   generic set-valued       ltr_collect_semantic_postfix        closure premises bound ltr_collect
                                                                by B, at every node
   plain abstract           unified_ltr_post_fixpoint_sound     a post-fixpoint env covers
                                                                ltr_collect, at every node
   keyed abstract           activation_collect_sound            keyed slots cover activation
                                                                traces, every node and context
   D/G endpoint             dg_post_solution_collect_sound_ltr  a computed D/G post-solution covers
                                                                ltr_collect, at every node
   effectful EXIT           side_collect_sound_exit_eff_ltr_cone  the demand-driven solver result
                                                                covers ltr_collect at the EXIT only
   source -> abstract       source_activation_sound             composes the keyed bridge with
   (composed)                                                   activation_collect_sound: a reached
                                                                source store lies in gamma of the slot
  \<close>

  \<^bold>\<open>The complete argument, in one sentence.\<close>  For a well-formed compiled IMP2 program
  (\<^verbatim>\<open>wf_compile_input\<close>, \<^verbatim>\<open>source_com\<close>) and any source execution, the compiler
  simulation constructs a \<^const>\<open>valid_ltr\<close> execution in the compiled CFG whose reached store lies
  in the corresponding plain (\<^const>\<open>ltr_collect\<close>) or keyed (\<^const>\<open>activation_collect\<close>) trace
  collection, and a generic solver-soundness theorem places that collection inside the
  concretization of the computed abstract result.  Hence every concrete source state the execution
  reaches is \<^emph>\<open>covered\<close> by the analysis --- soundness, not completeness: the abstract result may
  admit more, and need not equal the concrete collecting semantics.

  \<^bold>\<open>The cone guard (demand-driven path).\<close>  The effectful solver computes bounds only for
  nodes that can reach the queried exit.  The concrete semantics still ranges over the
  \<^emph>\<open>original\<close> CFG; the \<^locale>\<open>ltr_gamma\<close> interpretation reads the real abstract slot on the
  exit cone and \<^const>\<open>UNIV\<close> off it.  So the cone restriction lives in the abstract guarantee ---
  no graph-pruning transformation is part of the semantic pipeline.

  The proof is layered into four Isabelle sessions.  The index below separates the proof spine from
  executable frontends, DOT exporters, and research witnesses.

  \<^bold>\<open>1. Language.\<close> IMP2 syntax, small-step semantics, and the procedural extension
  (scopes, calls, restores).
    \<^item> @{theory Voblint_IMP2.IMP2_Syntax} --- AST, variable names, countability.
    \<^item> @{theory Voblint_IMP2.IMP2_Expr} --- expression evaluation and small-step semantics.
    \<^item> @{theory Voblint_IMP2.IMP2_Globals} --- global variable names and initial store.
    \<^item> @{theory Voblint_IMP2.IMP2_Proc} --- procedural extension: \<^verbatim>\<open>Scope\<close>, \<^verbatim>\<open>Call\<close>, \<^verbatim>\<open>Restore\<close>.
    \<^item> @{theory Voblint_IMP2.IMP2_Notation} --- \<^verbatim>\<open>\<lbrakk> ... \<rbrakk>\<close> quotation bracket for examples.
    \<^item> @{theory Voblint_IMP2.IMP2_Bridge} --- backward simulation from AFP IMP2 big-step to \<^verbatim>\<open>pcompletes\<close>.

  \<^bold>\<open>2. Control-flow graph and concrete semantics.\<close> CFG construction, transfer primitives, and
  the activation-local trace semantics it carries.
    \<^item> @{theory Voblint_CFG.CFG_Def} --- CFG node/edge types, predecessor enumeration, finite code lists.
    \<^item> @{theory Voblint_CFG.CFG_Path} --- inductive path predicate and offset infrastructure.
    \<^item> @{theory Voblint_CFG.IMP2_Proc_to_CFG} --- \<^verbatim>\<open>compile_prog\<close>: IMP2 programs to interprocedural CFGs.
    \<^item> @{theory Voblint_CFG.CFG_Transfer} --- the concrete store transformers shared by the semantics: \<^verbatim>\<open>edge_step\<close>, \<^verbatim>\<open>edge_collect\<close>, \<^verbatim>\<open>edges_collect\<close>, \<^verbatim>\<open>combine_collect\<close>, \<^verbatim>\<open>call_enter_store\<close>.
    \<^item> @{theory Voblint_CFG.CFG_Local_Trace} --- the call-structured activation-local trace \<^const>\<open>valid_ltr\<close> (\<^verbatim>\<open>Root\<close>/\<^verbatim>\<open>Call\<close>/\<^verbatim>\<open>Resume\<close>), the projections \<^const>\<open>ltr_collect\<close> / \<^const>\<open>ltr_collect_keyed\<close> / \<^const>\<open>activation_collect\<close>, and the correlation-preserving interface \<^locale>\<open>ltr_gamma\<close> (with the keystone \<^verbatim>\<open>ltr_collect_semantic_postfix\<close>).
    \<^item> @{theory Voblint_CFG.CFG_Prune} --- graph-level dead-procedure pruning utilities and reachability-cone lemmas (\<^const>\<open>cfg_reaches\<close>, \<^const>\<open>cone\<close>); pruning is \<^emph>\<open>not\<close> part of the concrete semantics or the primary LTR soundness path --- only the reachability lemmas feed the cone guard.

  \<^bold>\<open>3. Analysis spine.\<close> Abstract domains, equation systems, and the TD_side solver bridge; every
  generic endpoint concludes over the trace projections.
    \<^item> @{theory Voblint_Analysis.Abstract_Domain} --- \<^verbatim>\<open>sound_domain\<close>, lifted state concretization, display support.
    \<^item> @{theory Voblint_Analysis.Constraint_System} --- pure and effectful transfer interfaces, \<^verbatim>\<open>glob_env\<close>, \<^verbatim>\<open>sound_transfer\<close>, \<^verbatim>\<open>sound_effectful_transfer\<close>.
    \<^item> @{theory Voblint_Analysis.Constraint_System_Sound} --- per-edge / per-combine transfer soundness (\<^verbatim>\<open>edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a \<sigma>\<rbrakk>\<close>), the building blocks of the monovariant trace endpoint \<^verbatim>\<open>unified_ltr_post_fixpoint_sound\<close> (in \<^verbatim>\<open>LTR_Analysis_Sound\<close>, over \<^const>\<open>ltr_collect\<close>).
    \<^item> @{theory Voblint_Analysis.TD_Side_CFG} --- mixed local/global abstraction: \<^verbatim>\<open>side_env\<close>, local/global restrictions, unit-global effectful tree constructors.
    \<^item> @{theory Voblint_Analysis.TD_Side_Eff_Soundness} --- effectful TD_side soundness at the exit cone over \<^const>\<open>ltr_collect\<close> (\<^verbatim>\<open>side_collect_sound_exit_eff_ltr_cone\<close>), \<^verbatim>\<open>threefold_mono\<close>, \<^verbatim>\<open>cone_compatible_etf\<close>.

  \<^bold>\<open>4. Concrete domains.\<close> Domain instances used by the proof spine and examples.
    \<^item> @{theory Voblint_Analysis.Sign_Domain} --- Sign lattice, transfer functions, soundness, monotonicity, display instance.
    \<^item> @{theory Voblint_Analysis.Sign_Side_Soundness} --- Sign at the effectful side IP solver, over \<^const>\<open>ltr_collect\<close>.
    \<^item> @{theory Voblint_Analysis.Interval_Domain} --- interval lattice, widening, transfer functions, soundness, monotonicity.
    \<^item> @{theory Voblint_Analysis.Interval_Side_Soundness} --- Interval at the effectful side IP solver, over \<^const>\<open>ltr_collect\<close>.

  \<^bold>\<open>4b. The D/G interface spine.\<close> The native, carrier-opaque Goblint-\<^verbatim>\<open>Spec\<close> interface
    (independent flow-sensitive local domain \<^verbatim>\<open>D\<close> and flow-insensitive global domain \<^verbatim>\<open>G\<close>),
    the canonical context-sensitive backbone.
    \<^item> @{theory Voblint_Analysis.DG_Framework} --- the \<^verbatim>\<open>dg_spec\<close> record (\<^verbatim>\<open>step : D => G => G x D\<close>), the \<^verbatim>\<open>dg_state\<close> copy lattice, the seeded keyed generator.
    \<^item> @{theory Voblint_Analysis.DG_Soundness} --- native heterogeneous soundness over opaque carriers (\<^verbatim>\<open>sound_dg_spec\<close>); the shared closure obligations \<^verbatim>\<open>dg_postfix_gamma_{entry,edge,combine}\<close> feed the trace endpoint \<^verbatim>\<open>dg_post_solution_collect_sound_ltr\<close>.
    \<^item> @{theory Voblint_Analysis.Sign_DG} --- Sign as a diagonal \<^verbatim>\<open>sound_dg_spec\<close> instance.
    \<^item> @{theory Voblint_Analysis.Interval_DG} --- Interval as a diagonal instance (\<^verbatim>\<open>ivl_dg_post_solution_collect_sound\<close>, over \<^const>\<open>ltr_collect\<close>).
    \<^item> @{theory Voblint_Analysis.Mixed_Sign_Interval} --- the mixed flagship: Sign locals with Interval globals, both mixed-domain and context-sensitive.

  \<^bold>\<open>4c. Activation-local certification.\<close> The concrete object the context-sensitive soundness
    rides: one trace per activation, with a stable call-only context.
    \<^item> @{theory Voblint_Analysis.Activation_Backbone} --- the generic \<^verbatim>\<open>activation_collect_sound\<close>: over \<^const>\<open>valid_ltr\<close>, four obligations \<^verbatim>\<open>ENTRY_G\<close>/\<^verbatim>\<open>EDGE\<close>/\<^verbatim>\<open>SEED_G\<close>/\<^verbatim>\<open>COMB\<close> (\<^verbatim>\<open>COMB\<close> at the caller context) bound \<^const>\<open>activation_collect\<close> at every \<^verbatim>\<open>(node, context)\<close>.
    \<^item> @{theory Voblint_Analysis.DG_Ctx_Activation} --- DG-native discharge of those four obligations from a \<^verbatim>\<open>sound_dg_spec\<close> post-solution, so a computed D/G solution certifies the activation collecting.

  \<^bold>\<open>5. Executable frontend.\<close> Finite-map state representation and certified execution.
    \<^item> @{theory Voblint_Analysis.Exec_St} --- executable abstract-state maps for code generation.
    \<^item> @{theory Voblint_Analysis.Exec_Bridge} --- commutation bridge from executable states to function states.
    \<^item> @{theory Voblint_Analysis.Exec_DG_Bridge} --- executable transport for the D/G spine (\<^verbatim>\<open>fun_of_dg_st\<close>, \<^verbatim>\<open>dg_gen_of\<close>, \<^verbatim>\<open>part_post_solution_dg_st_to_abs\<close>): the verified solver \<^emph>\<open>runs\<close> on D/G equations.
    \<^item> @{theory Voblint_Analysis.Sign_Exec} --- executable Sign transfer functions.
    \<^item> @{theory Voblint_Analysis.Sign_Exec_Sound} --- executable Sign IP solver, trace soundness, annotated DOT entry points.

  \<^bold>\<open>6. End-to-end theorems.\<close> Headline soundness and the source bridge.
    \<^item> @{theory Voblint_Formalization.Mixed_Flow_Sound} --- mixed flow-sensitive soundness and optimality over \<^const>\<open>ltr_collect\<close> (\<^verbatim>\<open>mixed_flow_analysis_sound\<close> / \<^verbatim>\<open>mixed_flow_analysis_optimal\<close>).
    \<^item> @{theory Voblint_Formalization.Source_Activation_Sound} --- the source-adequacy bridge: a reachable IMP2 source configuration produces a \<^const>\<open>valid_ltr\<close> trace (\<^verbatim>\<open>source_run_has_ltr\<close>), bounded at its activation context (\<^verbatim>\<open>source_activation_sound\<close>) and monovariantly (\<^verbatim>\<open>source_reaches_ltr_collect\<close>).

  \<^bold>\<open>7. Examples and witnesses.\<close> Executable demos, precision witnesses, tooling.
    \<^item> \<^bold>\<open>@{theory Voblint_Examples.Example_Interval_DG_Flagship} --- the flagship end-to-end example.\<close> An inline IMP2 counting loop is compiled, its D/G interval equations generated, the verified warrowing solver \<^emph>\<open>computes\<close> the solution (\<^verbatim>\<open>by eval\<close>), the result certified a post-solution and transported to the abstract semantics; \<^verbatim>\<open>flagship_collect_sound\<close> proves it over-approximates \<^const>\<open>ltr_collect\<close> --- discovering \<^verbatim>\<open>x in [0,20]\<close> --- and the compiler simulation lifts this to \<^emph>\<open>actual source runs\<close> (\<^verbatim>\<open>flagship_source_run_sound\<close>).
    \<^item> @{theory Voblint_Examples.Exec_Sign_DG_Run} --- the Sign analogue on the always-join solver.
    \<^item> @{theory Voblint_Examples.Example_Interval_DG_Ctx_Collect} --- the recursive \<^verbatim>\<open>twice\<close> program certified against \<^const>\<open>activation_collect\<close> at every \<^verbatim>\<open>(node, context)\<close> (\<^verbatim>\<open>twice_activation_collect_sound\<close>).
    \<^item> @{theory Voblint_Examples.Example_Interval_Source_Ctx} --- \<^verbatim>\<open>twice\<close> certified against \<^emph>\<open>actual source runs\<close> at each activation's own context, strictly sharper than the monovariant capstone.
    \<^item> @{theory Voblint_Examples.Example_Inc_Proc} --- shared global-increment procedure witness.
    \<^item> @{theory Voblint_Examples.Example_IMP2_Coverage} --- Sign analysis on a non-terminating loop.
    \<^item> @{theory Voblint_Examples.Example_Side_Execute} --- minimal certified Sign IP example with annotated CFG DOT.
    \<^item> @{theory Voblint_Examples.Example_Side_Branch_Calls} --- branching procedure called twice; flow-sensitive locals, flow-insensitive globals.
    \<^item> @{theory Voblint_Examples.Example_Side_Proc_Global} --- Sign IP analysis on the shared global-increment call.
    \<^item> @{theory Voblint_Examples.Example_Interval_Side_Proc_Global} --- Interval IP analysis on the same.
    \<^item> @{theory Voblint_Examples.Example_Mixed_Flow_Sign} --- the mixed-flow soundness/optimality theorem applied to Sign.
    \<^item> @{theory Voblint_Examples.Example_Proc_Call} --- Interval analysis of \<^verbatim>\<open>inc\<close> and \<^verbatim>\<open>sqr\<close> procedures communicating through a global.
    \<^item> @{theory Voblint_Examples.Example_Interval_Loop_Coverage} --- Interval analysis of a bounded loop.
    \<^item> @{theory Voblint_Examples.Example_Guard_Refinement} --- backward guard refinement precision witness.
    \<^item> @{theory Voblint_Examples.Example_Proc_GraphViz} --- plain procedural CFG DOT export examples.

  \<^bold>\<open>8. Tooling.\<close> Theories outside the core proof spine.
    \<^item> @{theory Voblint_Examples.Exec_Sign_Run} --- code-generation probe on a hand-written Sign equation system.
    \<^item> @{theory Voblint_Analysis.Sign_Named_Global_Eff} --- named-global routing witness; the solver-compatible constant route and the conditional-route monotonicity boundary.
\<close>

text \<open>
  \<^bold>\<open>The D/G execution pipeline (headline).\<close> The flagship threads a single chain,
  every step machine-checked, from source to a soundness theorem over the
  \<^emph>\<open>computed\<close> analysis result:

    \<^item> IMP2 source \<^verbatim>\<open>compile_prog\<close> to a CFG;
    \<^item> the generic D/G generator \<^verbatim>\<open>dg_gen_of\<close> emits the equation system;
    \<^item> the verified solver \<^emph>\<open>computes\<close> a solution (\<^verbatim>\<open>solve_c ... = Some sigma\<close>, \<^verbatim>\<open>by eval\<close>);
    \<^item> the solver's own correctness theorem certifies \<^verbatim>\<open>part_post_solution sigma\<close> --- no re-checking;
    \<^item> the native endpoint \<open>ivl_dg_post_solution_collect_sound\<close> bounds
      \<open>ltr_collect g S v\<close> at every program point.

  \<^bold>\<open>Soundness spine.\<close> The context-sensitive analyses converge on one native
  interface, the carrier-opaque \<^verbatim>\<open>sound_dg_spec\<close>; Sign, Interval, Retain and
  the mixed flagship are its instances, and context slicing is factored through
  the functional activation spine and its per-context keyed slots. The base
  flow-sensitive spine is the cone-guarded exit endpoint
  \<^verbatim>\<open>side_collect_sound_exit_eff_ltr_cone\<close>, instantiated for Sign and Interval and stated over
  \<^const>\<open>ltr_collect\<close> on the original CFG --- the cone restriction lives in the abstract
  concretization guard, not in a graph transformation.
\<close>

end
