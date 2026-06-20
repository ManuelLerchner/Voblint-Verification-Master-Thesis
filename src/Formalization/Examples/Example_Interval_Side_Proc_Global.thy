section \<open>Example: TD\_side Interval Analysis on a Single Global Increment Call\<close>

theory Example_Interval_Side_Proc_Global
  imports "Voblint_Analysis.Interval_Side_Soundness" "Voblint_CFG.CFG_Collect_Adeq"
begin

text \<open>
  Interval instance of the side-effecting interprocedural witness: the same
  @{const inc_pi} program (a single call to procedure p incrementing the global
  @{term \<open>''Gx''\<close>}) carried through the @{const side_analyse_eff} solver at the
  interval domain.  Demonstrates the soundness scaffold is domain-generic by
  reusing it on a second, infinite-height numeric domain.
\<close>

text \<open>
  Initial state: every variable -- including the globals -- starts at the full
  interval @{term \<open>Ivl MinInf PlusInf\<close>} (top), the interval analogue of sign top.
\<close>
definition side_proc_global_ivl_s0 :: "ivl abs_state" where
  "side_proc_global_ivl_s0 = (\<lambda>_. Ivl MinInf PlusInf)"

theorem proc_global_side_ivl_analysis:
  fixes s t :: store
  assumes s_sound: "s \<in> ivl_domain.gamma_state side_proc_global_ivl_s0"
  assumes runs: "cfg_runs_to inc_pi [''p''] (Call ''p'') s t"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog inc_pi [''p''] (Call ''p'')) ivl_etf bot
       side_proc_global_ivl_s0
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
  shows "t \<in> ivl_domain.gamma_state
       (side_analyse_eff inc_pi [''p''] (Call ''p'') ivl_etf bot side_proc_global_ivl_s0
         (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))))"
proof -
  have collect_exit:
    "t \<in> cfg_collect (compile_prog inc_pi [''p''] (Call ''p'')) {s}
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
    using runs unfolding cfg_runs_to_def
    by (metis singleton_store_def)
  show ?thesis
    by (rule side_ivl_analysis_sound[OF s_sound collect_exit side_solve_dom])
qed

end
