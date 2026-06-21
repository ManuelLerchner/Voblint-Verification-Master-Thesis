section \<open>Example: TD\_side Sign Analysis on a Single Global Increment Call\<close>

theory Example_Side_Proc_Global
  imports
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_CFG.CFG_Collect_Adeq"
begin

text \<open>
  Side-effecting interprocedural witness: @{const inc_pi} with a single call to
  procedure p.  Operational semantics via @{const cfg_runs_to}; soundness via
  @{const side_analyse_eff} (the effectful side TD solver).
\<close>

(* A non-trivial initial state: every variable -- including the globals --
   starts at STop, not bot.  The entry seeds the initial globals into the
   single global unknown, so soundness holds for an arbitrary s0 (no
   restrict_global s0 = bot precondition). *)
definition side_proc_global_s0 :: "sign abs_state" where
  "side_proc_global_s0 = (\<lambda>_. STop)"

theorem proc_global_side_sign_analysis:
  fixes s t :: store
  assumes s_sound: "s \<in> sign_domain.gamma_state side_proc_global_s0"
  assumes runs: "cfg_runs_to inc_pi [''p''] (Call ''p'') s t"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog inc_pi [''p''] (Call ''p'')) sign_etf bot
       side_proc_global_s0 ()
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse_eff inc_pi [''p''] (Call ''p'') sign_etf bot side_proc_global_s0 ()
         (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))))"
proof -
  have collect_exit:
    "t \<in> cfg_collect (compile_prog inc_pi [''p''] (Call ''p'')) {s}
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
    using runs unfolding cfg_runs_to_def
    by (metis singleton_store_def)
  show ?thesis
    by (rule side_sign_analysis_sound[OF s_sound collect_exit side_solve_dom])
qed

subsection \<open>Executable sign analysis\<close>

definition inc_procs :: "pname list" where
  "inc_procs = [''p'']"

definition inc_main :: com where
  "inc_main = Call ''p''"

definition inc_prog :: imp_prog where
  "inc_prog = (inc_procs, inc_pi, inc_main)"


value "sign_exec_prog inc_prog ''Gx''"

lemma inc_gx_nonneg:
  "sign_exec_prog inc_prog ''Gx'' = SNonNeg"
  by eval

lemma inc_terminates: "sign_terminates_prog inc_prog"
  by (rule sign_terminates_prog_via_solve_c) eval

corollary inc_certified_sound:
  "cfg_collect (prog_cfg inc_prog) cinit_stores (cfg_exit (prog_cfg inc_prog))
   \<le> sign_domain.gamma_state (sign_exec_prog inc_prog)"
  by (rule sign_exec_prog_sound_collecting[OF inc_terminates])

subsection \<open>Annotated CFG visualisation\<close>

text \<open>
  @{const sign_annotated_dot_prog_lit} on the same witness: CFG nodes labelled
  with sign abstract states from @{const sign_exec_raw} (exit @{thm [source] inc_gx_nonneg}).
\<close>


ML_val \<open>
  writeln (@{code sign_annotated_dot_prog_lit} @{code inc_prog})
\<close>

end
