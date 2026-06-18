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
    "Voblint_CFG.CFG_Collect_Edges"
    "Voblint_CFG.CFG_Collect_Core"
    "Voblint_CFG.CFG_Collect_IP"
    "Voblint_CFG.CFG_Collect_IP_Adeq"
    "Voblint_CFG.CFG_Collect_Trace"
    "Voblint_CFG.CFG_Collect_Trace_IP"
    "Voblint_CFG.CFG_Collect_Unified"
    "Voblint_CFG.CFG_Prune"
    "Voblint_CFG.CFG_GraphViz"
    "Voblint_Analysis.Abstract_Domain"
    "Voblint_Analysis.Constraint_System"
    "Voblint_Analysis.Constraint_System_Sound"
    "Voblint_Analysis.Constraint_System_IP_Sound"
    "Voblint_Analysis.TD_Side_CFG"
    "Voblint_Analysis.TD_Side_IP_Eff_Soundness"
    "Voblint_Analysis.Sign_Domain"
    "Voblint_Analysis.Sign_Side_IP_Soundness"
    "Voblint_Analysis.Interval_Domain"
    "Voblint_Analysis.Interval_Side_IP_Soundness"
    "Voblint_Analysis.Analysis_Sound"
    "Voblint_Analysis.Exec_St"
    "Voblint_Analysis.Exec_Bridge"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Analysis_GraphViz"
    Trace_IP_Analysis_Sound
    Example_IMP2_Coverage
    Example_Side_Execute
    Example_Side_Branch_Calls
    Example_Side_Proc_Global
    Example_Interval_Side_Proc_Global
    Example_Proc_Call
    Example_Interval_Loop_Coverage
    Example_Trace_Digest_Precision
    Example_Proc_GraphViz
begin

text \<open>
  This development formalises an end-to-end soundness proof for an abstract
  interpreter in the style of Goblint. An IMP2 program is compiled to a
  control-flow graph; the graph induces a constraint system; a verified
  top-down solver computes a post-fixpoint; and that post-fixpoint soundly
  over-approximates the interprocedural collecting semantics at every program
  point.

  The proof is layered into four Isabelle sessions. Read them in order; every
  theory name below links into its formal text.

  \<^bold>\<open>1. Language.\<close> IMP2 syntax, small-step semantics, and the
  procedural extension (scopes, calls, restores).
    \<^item> @{theory Voblint_IMP2.IMP2_Syntax} --- AST, variable names, countability.
    \<^item> @{theory Voblint_IMP2.IMP2_Expr} --- expression evaluation and small-step semantics.
    \<^item> @{theory Voblint_IMP2.IMP2_Globals} --- global variable names and initial store.
    \<^item> @{theory Voblint_IMP2.IMP2_Proc} --- procedural extension: \<^verbatim>\<open>Scope\<close>, \<^verbatim>\<open>Call\<close>, \<^verbatim>\<open>Restore\<close>.
    \<^item> @{theory Voblint_IMP2.IMP2_Notation} --- \<^verbatim>\<open>\<lbrakk> ... \<rbrakk>\<close> quotation bracket for writing commands and whole programs.
    \<^item> @{theory Voblint_IMP2.IMP2_Bridge} --- backward simulation from AFP IMP2 big-step to \<^verbatim>\<open>pruns_to\<close>; transfers analyzer soundness to AFP IMP2's concrete semantics.

  \<^bold>\<open>2. Control-flow graph.\<close> CFG construction and the interprocedural
  collecting semantics it carries.
    \<^item> @{theory Voblint_CFG.CFG_Def} --- CFG node and edge types.
    \<^item> @{theory Voblint_CFG.CFG_Path} --- inductive path predicate and offset infrastructure.
    \<^item> @{theory Voblint_CFG.IMP2_Proc_to_CFG} --- \<^verbatim>\<open>compile_prog\<close>: IMP2 programs to interprocedural CFGs.
    \<^item> @{theory Voblint_CFG.CFG_Collect_Edges} --- per-edge transfer functions on store sets.
    \<^item> @{theory Voblint_CFG.CFG_Collect_Core} --- \<^verbatim>\<open>edges_collect\<close>: path fold and path-to-lfp bridge.
    \<^item> @{theory Voblint_CFG.CFG_Collect_IP} --- interprocedural collecting semantics (\<^verbatim>\<open>cfg_collect_ip\<close>).
    \<^item> @{theory Voblint_CFG.CFG_Collect_IP_Adeq} --- operational adequacy: big-step runs reach \<^verbatim>\<open>cfg_collect_ip\<close>.
    \<^item> @{theory Voblint_CFG.CFG_Collect_Trace} --- trace-valued collecting semantics.
    \<^item> @{theory Voblint_CFG.CFG_Collect_Trace_IP} --- interprocedural trace collecting and the projection lemma.
    \<^item> @{theory Voblint_CFG.CFG_Collect_Unified} --- unified locale combining both collecting views.
    \<^item> @{theory Voblint_CFG.CFG_Prune} --- dead-procedure pruning: restrict to reachable sub-CFG.
    \<^item> @{theory Voblint_CFG.CFG_GraphViz} --- plain CFG rendering as GraphViz DOT.

  \<^bold>\<open>3. Analysis.\<close> Abstract domains, the constraint system, and the TD
  solver bridge --- from local equation to global post-fixpoint.
    \<^item> @{theory Voblint_Analysis.Abstract_Domain} --- \<^verbatim>\<open>abstract_domain\<close> locale, lifted state concretization, and @{class show_val}.
    \<^item> @{theory Voblint_Analysis.Constraint_System} --- equation system over a CFG.
    \<^item> @{theory Voblint_Analysis.Constraint_System_Sound} --- each constraint RHS soundly over-approximates the collecting step.
    \<^item> @{theory Voblint_Analysis.Constraint_System_IP_Sound} --- interprocedural constraint soundness.
    \<^item> @{theory Voblint_Analysis.TD_Side_CFG} --- wires the constraint system into the side-effecting TD solver.
    \<^item> @{theory Voblint_Analysis.TD_Side_IP_Eff_Soundness} --- collecting soundness of the standalone effectful side-effecting IP solver.
    \<^item> @{theory Voblint_Analysis.Sign_Domain} --- Sign lattice: concrete domain instantiation.
    \<^item> @{theory Voblint_Analysis.Sign_Side_IP_Soundness} --- Sign domain instantiated at the side IP solver.
    \<^item> @{theory Voblint_Analysis.Interval_Domain} --- interval domain instantiation.
    \<^item> @{theory Voblint_Analysis.Interval_Side_IP_Soundness} --- Interval domain instantiated at the side IP solver.
    \<^item> @{theory Voblint_Analysis.Analysis_Sound} --- unified soundness: one engine over both collecting views.
    \<^item> @{theory Voblint_Analysis.Exec_St} --- executable abstract-state maps for code generation.
    \<^item> @{theory Voblint_Analysis.Exec_Bridge} --- generic executable transfer mirror and S4 commutation.
    \<^item> @{theory Voblint_Analysis.Sign_Exec} --- sign-domain executable transfer functions.
    \<^item> @{theory Voblint_Analysis.Sign_Exec_Sound} --- executable sign IP solver and certified program queries.
    \<^item> @{theory Voblint_Analysis.Analysis_GraphViz} --- domain-parameterised annotated CFG DOT export.

  \<^bold>\<open>4. End-to-end soundness.\<close> The headline theorem and executable examples.
    \<^item> @{theory Voblint_Formalization.Trace_IP_Analysis_Sound} --- the main
      result, @{thm [source] sound_transfer.trace_ip_analysis_sound}.
    \<^item> @{theory Voblint_Formalization.Example_IMP2_Coverage} --- Sign analysis on a non-terminating loop:
      soundness where big-step has no final state.
    \<^item> @{theory Voblint_Formalization.Example_Side_Execute} --- minimal certified sign IP example with annotated CFG DOT.
    \<^item> @{theory Voblint_Formalization.Example_Side_Branch_Calls} --- branching procedure called twice;
      flow-sensitive locals and flow-insensitive globals in GraphViz.
    \<^item> @{theory Voblint_Formalization.Example_Side_Proc_Global} --- Sign IP analysis on a single
      global-increment procedure call; executable @{const sign_exec_prog} and annotated DOT.
    \<^item> @{theory Voblint_Formalization.Example_Interval_Side_Proc_Global} --- Interval IP analysis
      on the same program; demonstrates domain-generic soundness scaffold.
    \<^item> @{theory Voblint_Formalization.Example_Proc_Call} --- Interval analysis of \<^verbatim>\<open>inc\<close> and \<^verbatim>\<open>sqr\<close>
      procedures communicating through a global; terminates with \<^verbatim>\<open>Gx = 25\<close>.
    \<^item> @{theory Voblint_Formalization.Example_Interval_Loop_Coverage} --- Interval analysis of
      a bounded loop; proves \<^verbatim>\<open>x \<in> [0, 20]\<close> at the loop head without widening.
    \<^item> @{theory Voblint_Formalization.Example_Trace_Digest_Precision} --- precision of the
      trace-IP collecting semantics.
    \<^item> @{theory Voblint_Formalization.Example_Proc_GraphViz} --- interprocedural CFG rendered
      as plain GraphViz DOT (structural witness; sign examples carry annotated DOT).
\<close>

end

