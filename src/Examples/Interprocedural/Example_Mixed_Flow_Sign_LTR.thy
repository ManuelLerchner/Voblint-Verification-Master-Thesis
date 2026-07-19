section \<open>Example: effectful recursive analysis over the stack-faithful semantics\<close>

theory Example_Mixed_Flow_Sign_LTR
  imports
    Example_Mixed_Flow_Sign
    "Voblint_Analysis.LTR_TD_Side_Eff_Exit"
begin

text \<open>
  Effectful validation for the local-trace solver soundness path.  It reuses the recursive sign
  analysis of \<^theory>\<open>Voblint_Examples.Example_Mixed_Flow_Sign\<close> --- the self-recursive procedure
  @{term \<open>''p''\<close>} (\<open>inc\<close>) compiled by @{const compile_prog} --- and restates its effectful exit
  soundness against the stack-faithful local-trace collecting @{const ltr_collect}, stated directly
  over the ORIGINAL compiled graph, via @{thm [source] side_collect_sound_exit_eff_ltr_cone}.

  The theorem has NO pruning bridge: no \<open>call_return_reaches\<close>, no graph transformation, no
  compiled-CFG well-bracketing hypothesis.  The cone restriction lives in the concretization guard
  of @{thm [source] ltr_post_fixpoint_sound_at_eff_cone}, not in a graph transformation, so a dead
  procedure's call site is simply off the exit cone and imposes no obligation.  The R5d
  counterexample (a well-formed program with an uncalled procedure whose call continuation cannot
  reach the exit) is therefore subsumed automatically: the recursive \<open>inc\<close> program's exit trace
  survives with no side condition.

  The proof reuses exactly the effectful post-solution hypotheses of the raw-CFG corollary
  @{thm [source] sign_mixed_flow_sound_from_pp}.  Soundness flows through
  @{const valid_ltr}'s matched return rule inside the trace-native endpoint.
  callers with all callee exits.  It changes no solver equation.

  This theory is a separate leaf because importing the trace stack brings @{const ltr.Call} into
  scope, shadowing the bare \<open>Call\<close> constructor that
  @{theory Voblint_Examples.Example_Mixed_Flow_Sign} uses in its compiled-program terms; the
  statement below qualifies @{const com.Call}.
\<close>

corollary sign_mixed_flow_sound_ltr_from_pp:
  fixes \<sigma> :: "pp + unit \<Rightarrow> sign abs_state" and S :: "store set"
  assumes pp:
    "part_post_solution
       (side_cfg_T_eff (compile_prog inc_pi [''p''] (com.Call None ''p'' []))
          sign_etf bot sign_init_s0 ())
       (cfg_exit (compile_prog inc_pi [''p''] (com.Call None ''p'' []))) \<sigma> vars"
  assumes entry:
    "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry (compile_prog inc_pi [''p''] (com.Call None ''p'' [])))\<rbrakk>"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  shows
    "ltr_collect (compile_prog inc_pi [''p''] (com.Call None ''p'' [])) S
       (cfg_exit (compile_prog inc_pi [''p''] (com.Call None ''p'' [])))
     \<subseteq> \<lbrakk>side_env \<sigma> (cfg_exit (compile_prog inc_pi [''p''] (com.Call None ''p'' [])))\<rbrakk>"
  by (rule side_collect_sound_exit_eff_ltr_cone
        [OF sign_sound_etf pp
            compile_prog_finite[THEN conjunct1]
            compile_prog_finite[THEN conjunct2]
            entry sign_etf_cone_compatible inr])

end
