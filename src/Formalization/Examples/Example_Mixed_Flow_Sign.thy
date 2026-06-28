section \<open>Example: mixed_flow_analysis_optimal applied to the sign domain\<close>

theory Example_Mixed_Flow_Sign
  imports
    "Voblint_Analysis.Sign_Side_Soundness"
    Example_Inc_Proc
    Mixed_Flow_Sound
begin

text \<open>
  Demonstrates the top-level trace-level theorem applied to the sign domain
  on the @{const inc_pi} program (procedure p increments the global Gx).

  The effectful transfer record is the domain interface here.  Its soundness,
  cone compatibility, and threefold monotonicity are discharged by the Sign
  domain theory.  Three obligations remain program- or run-specific:

    dom: solver termination         -- no static proof from the equation system
    S_sound: S <= gamma(s0)         -- caller's initial stores must fit the abstract entry
    tr_in: tr a reaching trace      -- the trace we are proving pointwise soundness for
\<close>

definition sign_init_s0 :: "sign abs_state" where
  "sign_init_s0 = (\<lambda>_. STop)"

corollary sign_mixed_flow_sound_and_optimal:
  fixes S :: "store set" and tr :: "store list"
  assumes dom:
    "side_cfg_solve_dom_eff (compile_prog inc_pi [''p''] (Call ''p''))
       sign_etf bot sign_init_s0 ()
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
  assumes S_sound: "S \<le> \<lbrakk>sign_init_s0\<rbrakk>"
  assumes tr_in:
    "tr \<in> cfg_collect_trace (compile_prog inc_pi [''p''] (Call ''p'')) S
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
  shows
    "\<forall>x. (last tr) x \<in> gamma
       (side_analyse_eff inc_pi [''p''] (Call ''p'') sign_etf
          bot sign_init_s0 ()
          (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))) x)"
    and
    "least_part_post_solution
       (side_cfg_T_eff (compile_prog inc_pi [''p''] (Call ''p''))
          sign_etf bot sign_init_s0 ())
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))
       (td_cfg_side_solver_eff.nu_at
          (compile_prog inc_pi [''p''] (Call ''p''))
          sign_etf bot sign_init_s0 ()
          (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))))
       (td_cfg_side_solver_eff.stabl_at
          (compile_prog inc_pi [''p''] (Call ''p''))
          sign_etf bot sign_init_s0 ()
          (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))))"
proof -
  note result = mixed_flow_analysis_optimal
    [OF refl refl sign_sound_etf sign_etf_threefold_mono sign_etf_cone_compatible
        dom S_sound tr_in]
  show "\<forall>x. (last tr) x \<in> gamma
         (side_analyse_eff inc_pi [''p''] (Call ''p'') sign_etf
            bot sign_init_s0 ()
            (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))) x)"
    using result(1) .
  show "least_part_post_solution
         (side_cfg_T_eff (compile_prog inc_pi [''p''] (Call ''p''))
            sign_etf bot sign_init_s0 ())
         (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))
         (td_cfg_side_solver_eff.nu_at
            (compile_prog inc_pi [''p''] (Call ''p''))
            sign_etf bot sign_init_s0 ()
            (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))))
         (td_cfg_side_solver_eff.stabl_at
            (compile_prog inc_pi [''p''] (Call ''p''))
            sign_etf bot sign_init_s0 ()
            (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))))"
    using result(2) .
qed

text \<open>
  The post-solution corollary also needs finite (edges g) and finite (combines g).
  Both follow from compile_prog_finite when g is a compiled program -- a
  structural property of the CFG construction, not the analysis.
\<close>

corollary sign_mixed_flow_sound_from_pp:
  fixes \<sigma> :: "pp + unit \<Rightarrow> sign abs_state" and S :: "store set" and tr :: "store list"
  assumes pp:
    "part_post_solution
       (side_cfg_T_eff (compile_prog inc_pi [''p''] (Call ''p''))
          sign_etf bot sign_init_s0 ())
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))) \<sigma> vars"
  assumes entry:
    "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry (compile_prog inc_pi [''p''] (Call ''p'')))\<rbrakk>"
  assumes tr_in:
    "tr \<in> cfg_collect_trace (compile_prog inc_pi [''p''] (Call ''p'')) S
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
  shows
    "\<forall>x. (last tr) x \<in> gamma
       (side_env \<sigma> (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))) x)"
  by (rule mixed_flow_analysis_sound
        [OF sign_sound_etf pp entry sign_etf_cone_compatible
            compile_prog_finite[THEN conjunct1]
            compile_prog_finite[THEN conjunct2]
            tr_in])

end

