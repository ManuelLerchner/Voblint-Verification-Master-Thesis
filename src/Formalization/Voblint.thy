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
    "Voblint_CFG.CFG_Collect"
    "Voblint_CFG.CFG_Collect_Trace"
    "Voblint_CFG.CFG_Collect_Runs"
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
    "Voblint_Analysis.Analysis_Sound"
    "Voblint_Analysis.DG_Framework"
    "Voblint_Analysis.DG_Soundness"
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Mixed_Sign_Interval"
    "Voblint_Analysis.Exec_St"
    "Voblint_Analysis.Exec_Bridge"
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Sign_Named_Global_Eff"
    Exec_Sign_Run
    Exec_Sign_DG_Run
    Example_Interval_DG_Flagship
    Trace_Analysis_Sound
    Mixed_Flow_Sound
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
    Example_Trace_Digest_Precision
    Example_Trace_Digest_Combine
    Example_Trace_Digest_ReachingCompat
    Example_Proc_GraphViz
begin

text \<open>
  This development formalises an end-to-end soundness proof for an abstract
  interpreter in the style of Goblint.  An IMP2 program is compiled to a
  control-flow graph; the graph induces an effectful equation system; the
  verified TD_side solver computes a partial post-solution; and the resulting
  mixed flow-sensitive abstract state over-approximates the interprocedural
  trace collecting semantics at every program point.  When the generated
  equation system satisfies threefold monotonicity, the solver result is also
  the least partial post-solution.

  The proof is layered into four Isabelle sessions.  The list below separates
  the proof spine from executable frontends, DOT exporters, and research
  witnesses.

  \<^bold>\<open>1. Language.\<close> IMP2 syntax, small-step semantics, and the procedural
  extension (scopes, calls, restores).
    \<^item> @{theory Voblint_IMP2.IMP2_Syntax} --- AST, variable names, countability.
    \<^item> @{theory Voblint_IMP2.IMP2_Expr} --- expression evaluation and small-step semantics.
    \<^item> @{theory Voblint_IMP2.IMP2_Globals} --- global variable names and initial store.
    \<^item> @{theory Voblint_IMP2.IMP2_Proc} --- procedural extension: \<^verbatim>\<open>Scope\<close>, \<^verbatim>\<open>Call\<close>, \<^verbatim>\<open>Restore\<close>.
    \<^item> @{theory Voblint_IMP2.IMP2_Notation} --- \<^verbatim>\<open>\<lbrakk> ... \<rbrakk>\<close> quotation bracket for examples.
    \<^item> @{theory Voblint_IMP2.IMP2_Bridge} --- backward simulation from AFP IMP2 big-step to \<^verbatim>\<open>pcompletes\<close>.

  \<^bold>\<open>2. Control-flow graph.\<close> CFG construction and the collecting semantics it carries.
    \<^item> @{theory Voblint_CFG.CFG_Def} --- CFG node and edge types, predecessor enumeration, finite code lists.
    \<^item> @{theory Voblint_CFG.CFG_Path} --- inductive path predicate and offset infrastructure.
    \<^item> @{theory Voblint_CFG.IMP2_Proc_to_CFG} --- \<^verbatim>\<open>compile_prog\<close>: IMP2 programs to interprocedural CFGs.
    \<^item> @{theory Voblint_CFG.CFG_Collect} --- edge/path transfer functions, pointwise \<^verbatim>\<open>cfg_collect\<close>, and path-to-lfp bridge.
    \<^item> @{theory Voblint_CFG.CFG_Collect_Trace} --- trace-valued and digest-refined collecting semantics.
    \<^item> @{theory Voblint_CFG.CFG_Collect_Runs} --- generic run-to-exit projection into \<^verbatim>\<open>cfg_collect\<close>.
    \<^item> @{theory Voblint_CFG.CFG_Prune} --- dead-procedure pruning and the reachability cone used by the solver proof.

  \<^bold>\<open>3. Analysis spine.\<close> Abstract domains, equation systems, and the TD_side solver bridge.
    \<^item> @{theory Voblint_Analysis.Abstract_Domain} --- \<^verbatim>\<open>sound_domain\<close>, \<^verbatim>\<open>abstract_domain\<close>, lifted state concretization, and display support.
    \<^item> @{theory Voblint_Analysis.Constraint_System} --- pure and effectful transfer interfaces, \<^verbatim>\<open>glob_env\<close>, \<^verbatim>\<open>sound_transfer\<close>, and \<^verbatim>\<open>sound_effectful_transfer\<close>.
    \<^item> @{theory Voblint_Analysis.Constraint_System_Sound} --- pure post-fixpoint soundness against \<^verbatim>\<open>cfg_collect\<close>.
    \<^item> @{theory Voblint_Analysis.TD_Side_CFG} --- mixed local/global abstraction: \<^verbatim>\<open>side_env\<close>, local/global restrictions, and unit-global effectful tree constructors.
    \<^item> @{theory Voblint_Analysis.TD_Side_Eff_Soundness} --- effectful TD_side collecting soundness with pruning, \<^verbatim>\<open>threefold_mono\<close>, and \<^verbatim>\<open>cone_compatible_etf\<close>.
    \<^item> @{theory Voblint_Analysis.Analysis_Sound} --- small post-fixpoint bridge lemmas for \<^verbatim>\<open>cfg_collect\<close>.

  \<^bold>\<open>4. Concrete domains.\<close> Domain instances used by the proof spine and examples.
    \<^item> @{theory Voblint_Analysis.Sign_Domain} --- Sign lattice, transfer functions, soundness, monotonicity, and display instance.
    \<^item> @{theory Voblint_Analysis.Sign_Side_Soundness} --- Sign instantiated at the effectful side IP solver.
    \<^item> @{theory Voblint_Analysis.Interval_Domain} --- interval lattice, widening, transfer functions, soundness, and monotonicity.
    \<^item> @{theory Voblint_Analysis.Interval_Side_Soundness} --- Interval instantiated at the effectful side IP solver.

  \<^bold>\<open>4b. The D/G interface spine.\<close> The native, carrier-opaque Goblint-\<^verbatim>\<open>Spec\<close> interface
    (independent flow-sensitive local domain \<^verbatim>\<open>D\<close> and flow-insensitive global domain
    \<^verbatim>\<open>G\<close>), which is the canonical context-sensitive backbone.
    \<^item> @{theory Voblint_Analysis.DG_Framework} --- the \<^verbatim>\<open>dg_spec\<close> analysis record (\<^verbatim>\<open>step : D => G => G x D\<close>), the \<^verbatim>\<open>dg_state\<close> componentwise copy lattice, and the seeded CMP generator \<^verbatim>\<open>side_cfg_T_eff_cmp_seed_dg\<close>.
    \<^item> @{theory Voblint_Analysis.DG_Soundness} --- native heterogeneous soundness over opaque carriers (\<^verbatim>\<open>sound_dg_spec\<close>, \<^verbatim>\<open>dg_post_solution_collect_sound\<close>).
    \<^item> @{theory Voblint_Analysis.Sign_DG} --- Sign as a diagonal \<^verbatim>\<open>sound_dg_spec\<close> instance (\<^verbatim>\<open>sign_dg_post_solution_collect_sound\<close>).
    \<^item> @{theory Voblint_Analysis.Interval_DG} --- Interval as a diagonal instance (\<^verbatim>\<open>ivl_dg_post_solution_collect_sound\<close>).
    \<^item> @{theory Voblint_Analysis.Mixed_Sign_Interval} --- the mixed flagship: Sign locals with Interval globals, both mixed-domain and context-sensitive (\<^verbatim>\<open>mixed_si_post_solution_collect_sound\<close>).

  \<^bold>\<open>5. Executable frontend.\<close> Finite-map state representation and certified execution.
    \<^item> @{theory Voblint_Analysis.Exec_St} --- executable abstract-state maps for code generation.
    \<^item> @{theory Voblint_Analysis.Exec_Bridge} --- commutation bridge from executable states to function states.
    \<^item> @{theory Voblint_Analysis.Exec_DG_Bridge} --- executable transport for the D/G spine: the product carrier \<^verbatim>\<open>(D st, G st) dg_state\<close>, the refinement morphism \<^verbatim>\<open>fun_of_dg_st\<close>, the executable generator \<^verbatim>\<open>dg_gen_of\<close>, and the post-solution transport \<^verbatim>\<open>part_post_solution_dg_st_to_abs\<close>. Lets the verified solver \<^emph>\<open>run\<close> on D/G equations and certify the computed result.
    \<^item> @{theory Voblint_Analysis.Sign_Exec} --- executable Sign transfer functions.
    \<^item> @{theory Voblint_Analysis.Sign_Exec_Sound} --- executable Sign IP solver, trace soundness, and annotated DOT entry points.

  \<^bold>\<open>6. End-to-end theorems.\<close> Headline soundness and optimality statements.
    \<^item> @{theory Voblint_Formalization.Trace_Analysis_Sound} --- trace-level post-fixpoint soundness and digest-indexed trace reading.
    \<^item> @{theory Voblint_Formalization.Mixed_Flow_Sound} --- mixed flow-sensitive soundness and optimality:
      @{thm [source] mixed_flow_analysis_sound} and @{thm [source] mixed_flow_analysis_optimal}.

  \<^bold>\<open>7. Examples and witnesses.\<close> Executable demos, precision witnesses, and tooling.
    \<^item> \<^bold>\<open>@{theory Voblint_Formalization.Example_Interval_DG_Flagship} --- the flagship end-to-end example.\<close> An inline IMP2 counting loop is compiled, its D/G interval equations are generated, the verified warrowing solver \<^emph>\<open>computes\<close> the solution (\<^verbatim>\<open>by eval\<close>), the result is certified a post-solution and transported to the abstract semantics, and \<^verbatim>\<open>flagship_collect_sound\<close> proves it over-approximates the collecting semantics --- discovering the invariant \<^verbatim>\<open>x in [0,20]\<close>. The compiler-correctness simulation then lifts this to \<^emph>\<open>actual IMP2 source runs\<close> (\<^verbatim>\<open>flagship_source_run_sound\<close>). Ends with an analysis-annotated GraphViz rendering.
    \<^item> @{theory Voblint_Formalization.Exec_Sign_DG_Run} --- the Sign analogue on the always-join solver (\<^verbatim>\<open>dgEx_collect_sound\<close>).
    \<^item> @{theory Voblint_Formalization.Example_Inc_Proc} --- shared global-increment procedure witness used by sign, interval, and mixed-flow examples.
    \<^item> @{theory Voblint_Formalization.Example_IMP2_Coverage} --- Sign analysis on a non-terminating loop.
    \<^item> @{theory Voblint_Formalization.Example_Side_Execute} --- minimal certified Sign IP example with annotated CFG DOT.
    \<^item> @{theory Voblint_Formalization.Example_Side_Branch_Calls} --- branching procedure called twice; flow-sensitive locals and flow-insensitive globals.
    \<^item> @{theory Voblint_Formalization.Example_Side_Proc_Global} --- Sign IP analysis on the shared global-increment procedure call.
    \<^item> @{theory Voblint_Formalization.Example_Interval_Side_Proc_Global} --- Interval IP analysis on the shared global-increment procedure call.
    \<^item> @{theory Voblint_Formalization.Example_Mixed_Flow_Sign} --- application of the mixed-flow soundness and optimality theorem to Sign.
    \<^item> @{theory Voblint_Formalization.Example_Proc_Call} --- Interval analysis of \<^verbatim>\<open>inc\<close> and \<^verbatim>\<open>sqr\<close> procedures communicating through a global.
    \<^item> @{theory Voblint_Formalization.Example_Interval_Loop_Coverage} --- Interval analysis of a bounded loop.
    \<^item> @{theory Voblint_Formalization.Example_Guard_Refinement} --- backward guard refinement precision witness.
    \<^item> @{theory Voblint_Formalization.Example_Trace_Digest_Precision} --- trace digest precision witness.
    \<^item> @{theory Voblint_Formalization.Example_Trace_Digest_Combine} --- combine-side digest filtering: @{const cmp_pair} at the return junction.
    \<^item> @{theory Voblint_Formalization.Example_Trace_Digest_ReachingCompat} --- reader-side @{const reaching_compat}: lockset ghost filters the global read.
    \<^item> @{theory Voblint_Formalization.Example_Proc_GraphViz} --- plain procedural CFG DOT export examples.

  \<^bold>\<open>8. Tooling and research witnesses.\<close> Useful theories outside the core proof spine.
    \<^item> @{theory Voblint_CFG.CFG_GraphViz} --- plain CFG rendering as GraphViz DOT.
    \<^item> @{theory Voblint_Analysis.Analysis_GraphViz} --- domain-parameterised annotated CFG DOT export.
    \<^item> @{theory Voblint_Formalization.Exec_Sign_Run} --- code-generation probe on a hand-written Sign equation system.
    \<^item> @{theory Voblint_Analysis.Sign_Named_Global_Eff} --- named-global routing witness; documents the solver-compatible constant route and the conditional-route monotonicity boundary.
\<close>

text \<open>
  \<^bold>\<open>The D/G execution pipeline (headline).\<close> The flagship threads a single chain,
  every step machine-checked, from source to a soundness theorem over the
  \<^emph>\<open>computed\<close> analysis result:

    \<^item> IMP2 source \<^verbatim>\<open>compile_prog\<close> to a CFG;
    \<^item> the generic D/G generator \<^verbatim>\<open>dg_gen_of\<close> emits the equation system;
    \<^item> the verified solver \<^emph>\<open>computes\<close> a solution (\<^verbatim>\<open>solve_c ... = Some sigma\<close>, \<^verbatim>\<open>by eval\<close>);
    \<^item> the solver's own correctness theorem certifies \<^verbatim>\<open>part_post_solution sigma\<close> --- no re-checking;
    \<^item> \<^verbatim>\<open>part_post_solution_dg_st_to_abs\<close> transports it to the abstract \<^verbatim>\<open>dg_gen\<close>;
    \<^item> the native endpoint (\<^verbatim>\<open>ivl_dg_post_solution_collect_sound\<close>) concludes
      \<^verbatim>\<open>cfg_collect g S v <= gamma(sigma) v\<close> at every program point.

  \<^bold>\<open>Soundness spine.\<close> The context-sensitive analyses converge on one native
  interface, the carrier-opaque \<^verbatim>\<open>sound_dg_spec\<close>; Sign, Interval, Retain, Clean and
  the mixed flagship are its instances, and context slicing is factored through
  \<^verbatim>\<open>Ctx_Collect_Backbone\<close>. The base flow-sensitive spine remains
  \<^verbatim>\<open>side_analyse_eff_collect_sound_exit_pruned\<close> (Sign \<^verbatim>\<open>side_sign_analysis_sound\<close>,
  Interval \<^verbatim>\<open>side_ivl_analysis_sound\<close>).
\<close>

end
