section \<open>Example: mixed_flow_analysis_optimal applied to the sign domain\<close>

theory Example_Mixed_Flow_Sign
  imports
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.Mixed_Flow_Sound"
    Example_Inc_Proc
begin

text \<open>
  Demonstrates the top-level collecting-semantics theorem applied to the sign
  domain on the \<open>inc_pi\<close> program (procedure p increments the global Gx).

  The effectful transfer record is the domain interface here.  Its soundness,
  cone compatibility, and threefold monotonicity are discharged by the Sign
  domain theory.  Two obligations remain program- or run-specific:

    dom: solver termination         -- no static proof from the equation system
    S_sound: S <= gamma(s0)         -- caller's initial stores must fit the abstract entry
\<close>

definition sign_init_s0 :: "sign abs_state" where
  "sign_init_s0 = (\<lambda>_. STop)"


corollary sign_mixed_flow_sound_and_optimal:
  fixes S :: "store set"
  assumes dom:
    "side_cfg_solve_dom_eff (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))
       sign_etf bot sign_init_s0 ()
       (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))"
  assumes S_sound: "S \<le> \<lbrakk>sign_init_s0\<rbrakk>"
  shows
    "ltr_collect is_global (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)) S
       (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))
     \<le> \<lbrakk>side_analyse_eff inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>) sign_etf
          bot sign_init_s0 ()
          (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))\<rbrakk>"
    and
    "least_part_post_solution
       (side_cfg_T_eff (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))
          sign_etf bot sign_init_s0 ())
       (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))
       (td_cfg_side_solver_eff.nu_at
          (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))
          sign_etf bot sign_init_s0 ()
          (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))))
       (td_cfg_side_solver_eff.stabl_at
          (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))
          sign_etf bot sign_init_s0 ()
          (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))))"
proof -
  note result = mixed_flow_analysis_optimal
    [OF refl refl sign_sound_etf sign_etf_threefold_mono sign_etf_cone_compatible
        dom S_sound]
  show "ltr_collect is_global (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)) S
          (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))
        \<le> \<lbrakk>side_analyse_eff inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>) sign_etf
             bot sign_init_s0 ()
             (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))\<rbrakk>"
    using result(1) .
  show "least_part_post_solution
         (side_cfg_T_eff (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))
            sign_etf bot sign_init_s0 ())
         (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))
         (td_cfg_side_solver_eff.nu_at
            (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))
            sign_etf bot sign_init_s0 ()
            (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))))
         (td_cfg_side_solver_eff.stabl_at
            (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))
            sign_etf bot sign_init_s0 ()
            (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))))"
    using result(2) .
qed
text \<open>
  The post-solution corollary needs finite local-edge and call relations.  The
  compiler supplies both properties independently of the chosen analysis.
\<close>

corollary sign_mixed_flow_sound_from_pp:
  fixes \<sigma> :: "pp + unit \<Rightarrow> sign abs_state" and S :: "store set"
  assumes pp:
    "part_post_solution
       (side_cfg_T_eff (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))
          sign_etf bot sign_init_s0 ()) (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>))) \<sigma> vars"
  assumes entry:
    "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))\<rbrakk>"
  assumes inr: "inr_slot_locals_bot is_global \<sigma>"
  shows
    "ltr_collect is_global (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)) S
       (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))
     \<le> \<lbrakk>side_env \<sigma> (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))\<rbrakk>"
  by (rule mixed_flow_analysis_sound
        [OF sign_sound_etf pp entry sign_etf_cone_compatible
            compile_prog_finite[THEN conjunct1]
            compile_prog_finite[THEN conjunct2]
            compile_prog_wf inr])

end



