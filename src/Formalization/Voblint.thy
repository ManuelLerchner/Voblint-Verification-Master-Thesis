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
    "Voblint_Analysis.Exec_St"
    "Voblint_Analysis.Exec_Bridge"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Sign_Named_Global_Eff"
    "Voblint_Analysis.Exec_Sign_Run"
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

  \<^bold>\<open>5. Executable frontend.\<close> Finite-map state representation and certified sign execution.
    \<^item> @{theory Voblint_Analysis.Exec_St} --- executable abstract-state maps for code generation.
    \<^item> @{theory Voblint_Analysis.Exec_Bridge} --- commutation bridge from executable states to function states.
    \<^item> @{theory Voblint_Analysis.Sign_Exec} --- executable Sign transfer functions.
    \<^item> @{theory Voblint_Analysis.Sign_Exec_Sound} --- executable Sign IP solver, trace soundness, and annotated DOT entry points.

  \<^bold>\<open>6. End-to-end theorems.\<close> Headline soundness and optimality statements.
    \<^item> @{theory Voblint_Formalization.Trace_Analysis_Sound} --- trace-level post-fixpoint soundness and digest-indexed trace reading.
    \<^item> @{theory Voblint_Formalization.Mixed_Flow_Sound} --- mixed flow-sensitive soundness and optimality:
      @{thm [source] mixed_flow_analysis_sound} and @{thm [source] mixed_flow_analysis_optimal}.

  \<^bold>\<open>7. Examples and witnesses.\<close> Executable demos, precision witnesses, and tooling.
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
    \<^item> @{theory Voblint_Analysis.Exec_Sign_Run} --- code-generation probe on a hand-written Sign equation system.
    \<^item> @{theory Voblint_Analysis.Sign_Named_Global_Eff} --- named-global routing witness; documents the solver-compatible constant route and the conditional-route monotonicity boundary.
\<close>

end

