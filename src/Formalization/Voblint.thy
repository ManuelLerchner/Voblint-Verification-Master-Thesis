(* SPDX-License-Identifier: MIT *)

section \<open>Voblint: a verified abstract interpreter for IMP2\<close>

theory Voblint
  imports
    "Voblint_IMP2.IMP2_Syntax"
    "Voblint_IMP2.IMP2_Expr"
    "Voblint_IMP2.IMP2_Proc"
    "Voblint_CFG.CFG_Def"
    "Voblint_CFG.IMP2_Proc_to_CFG"
    "Voblint_CFG.CFG_Collect_IP"
    "Voblint_CFG.CFG_Collect_Trace_IP"
    "Voblint_CFG.CFG_Collect_Unified"
    "Voblint_Analysis.Abstract_Domain"
    "Voblint_Analysis.Sign_Domain"
    "Voblint_Analysis.Constraint_System"
    "Voblint_Analysis.TD_Side_IP_Soundness"
    "Voblint_Analysis.Analysis_Sound"
    Trace_IP_Analysis_Sound
    Example_Side_Proc_Global
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
    \<^item> @{theory Voblint_IMP2.IMP2_Syntax}
    \<^item> @{theory Voblint_IMP2.IMP2_Expr}
    \<^item> @{theory Voblint_IMP2.IMP2_Proc}

  \<^bold>\<open>2. Control-flow graph.\<close> CFG construction and the interprocedural
  collecting semantics it carries.
    \<^item> @{theory Voblint_CFG.CFG_Def}
    \<^item> @{theory Voblint_CFG.IMP2_Proc_to_CFG}
    \<^item> @{theory Voblint_CFG.CFG_Collect_IP}
    \<^item> @{theory Voblint_CFG.CFG_Collect_Trace_IP}
    \<^item> @{theory Voblint_CFG.CFG_Collect_Unified}

  \<^bold>\<open>3. Analysis.\<close> Abstract domains, the constraint system, and the
  TD solver bridge.
    \<^item> @{theory Voblint_Analysis.Abstract_Domain}
    \<^item> @{theory Voblint_Analysis.Sign_Domain}
    \<^item> @{theory Voblint_Analysis.Constraint_System}
    \<^item> @{theory Voblint_Analysis.TD_Side_IP_Soundness}
    \<^item> @{theory Voblint_Analysis.Analysis_Sound}

  \<^bold>\<open>4. End-to-end soundness.\<close> The headline theorem and executable
  examples.
    \<^item> @{theory Voblint_Formalization.Trace_IP_Analysis_Sound} --- the main
      result, @{thm [source] sound_transfer.trace_ip_analysis_sound}.
    \<^item> @{theory Voblint_Formalization.Example_Side_Proc_Global}
    \<^item> @{theory Voblint_Formalization.Example_Trace_Digest_Precision}
    \<^item> @{theory Voblint_Formalization.Example_Proc_GraphViz}
\<close>

end
