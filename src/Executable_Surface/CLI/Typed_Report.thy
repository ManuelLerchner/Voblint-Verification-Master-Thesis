theory Typed_Report
  imports Analysis_Report "Voblint_Typed_CLI.Typed_MCP"
begin

section \<open>The report of a typed run\<close>

text \<open>
  A typed run is reported by the builder a VIMP run uses (\<^const>\<open>report_of\<close>): the typed
  graph, the declared variables, no global name kept at its own unknown, since the typed
  analyses keep every variable in a point's own state, the division obligations of the
  typed expressions, and the program's procedures.
\<close>

fun tarith_obligations :: "texp \<Rightarrow> texp arithmetic_obligation list" where
  "tarith_obligations (TN _ _) = []"
| "tarith_obligations (TVar _ _) = []"
| "tarith_obligations (TArith k op a b) =
     tarith_obligations a @ tarith_obligations b
     @ (if op = ADiv \<or> op = AMod then [Arithmetic_Obligation (TArith k op a b) b] else [])"
| "tarith_obligations (TCast _ a) = tarith_obligations a"
| "tarith_obligations (TCmp _ a b) = tarith_obligations a @ tarith_obligations b"
| "tarith_obligations (TNot a) = tarith_obligations a"
| "tarith_obligations (TAnd a b) = tarith_obligations a @ tarith_obligations b"
| "tarith_obligations (TOr a b) = tarith_obligations a @ tarith_obligations b"

text \<open>An obligation is safe when its divisor is not zero, compared at the divisor's kind.\<close>

definition tarith_condition :: "texp arithmetic_obligation \<Rightarrow> texp" where
  "tarith_condition ob =
     TCmp CNe (arithmetic_divisor ob) (TN (texp_kind (arithmetic_divisor ob)) 0)"

type_synonym typed_report =
  "(typed_domain list \<times> globals_rule \<times> typed_context, tmcp_ctx report_context,
    var_id, texp, unit, tmcp_val) analysis_report"

definition typed_cs_report ::
    "typed_domain list \<Rightarrow> globals_rule \<Rightarrow> nat \<Rightarrow> kind_decls \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> cfg_node list) set
          \<times> (pp \<times> cfg_node list + (unit, cfg_node list) global_unknown
              \<Rightarrow> (tmcp_st lifted, tmcp_st lifted) dg_state)
       \<Rightarrow> typed_report" where
  "typed_cs_report as r k ds p sol =
     report_of (as, r, Typed_Call_String k) (map fst ds) (typed_cfg p ds) []
       (obligation_sites tarith_obligations (typed_cfg p ds)) tarith_condition
       (prog_main_name # prog_procs p) (\<lambda>ctx. Key_List (map Key_Node ctx)) Report_Call_String
       (tmcp_classify ds (tactivation as)) (typed_mcp.solved_run_of ds as k tglobal p sol)"

definition typed_report_run ::
    "typed_domain list \<Rightarrow> globals_rule \<Rightarrow> nat \<Rightarrow> kind_decls \<Rightarrow> imp_prog
       \<Rightarrow> typed_report option" where
  "typed_report_run as r k ds p =
     map_option (typed_cs_report as r k ds p)
       (TD_side_rule_Interp_solve_c r (typed_mcp.equations ds as k tglobal p)
          (cfg_exit (typed_cfg p ds), []))"

end
