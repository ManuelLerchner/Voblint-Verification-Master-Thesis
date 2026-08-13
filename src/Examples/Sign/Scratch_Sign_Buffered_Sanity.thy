theory Scratch_Sign_Buffered_Sanity
  imports "Voblint_Analysis.Sign_Exec" "Voblint_Analysis.Sign_Exec_Sound" "Voblint_VIMP.VIMP_Notation"
begin

text \<open>
  Sanity check for the Voblint issue #121 generator-layer buffering fix,
  mirrored from \<open>Interval\<close>'s \<open>Scratch_Reachability_Regression_Repro\<close>: a
  merge node (an \<open>if\<close>/\<open>else\<close> writing a shared global on both branches, then a
  read after the join) exercises the buffered generator's per-predecessor
  folding. The buffered \<open>sign_exec_eqs\<close> must terminate under the unmodified
  vendored always-join solver and agree with the original unbuffered
  \<open>side_cfg_T_eff_st\<close> generator's stable sigma.
\<close>

definition merge_prog :: imp_prog where
  "merge_prog = program {
     global g;
     void main() {
       if (0 < x) { g := 1 } else { g := 2 };
       y := g
     }
   }"

lemma merge_prog_declared_global_vars [simp]:
  "declared_global_vars merge_prog = [STR ''g'']"
  by (simp add: merge_prog_def)

abbreviation merge_gs :: "vname \<Rightarrow> bool" where
  "merge_gs \<equiv> declared_global merge_prog"

definition merge_is_bot_pred :: "sign resolved_st_q \<Rightarrow> bool" where
  "merge_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars merge_prog)"

definition merge_cfg :: cfg where
  "merge_cfg = compile_prog (prog_table merge_prog) (prog_procs merge_prog)
                  prog_main_name (prog_main merge_prog)"

definition merge_eqs_unbuffered :: "(pp, unit, sign resolved_st_q lifted) eqsT" where
  "merge_eqs_unbuffered = side_cfg_T_eff_st merge_cfg (sign_etf_st_for merge_is_bot_pred merge_gs)
                 bot cinit_sign_st ()"

value "merge_cfg"

value "TD_side_always_join_Interp_solve_c merge_eqs_unbuffered (cfg_exit merge_cfg) \<noteq> None"

text \<open>The production, buffered generator on the same program.\<close>

value "sign_exec_eqs merge_is_bot_pred merge_gs (prog_table merge_prog) (prog_procs merge_prog)
         prog_main_name (prog_main merge_prog)"

value "TD_side_always_join_Interp_solve_c
         (sign_exec_eqs merge_is_bot_pred merge_gs (prog_table merge_prog) (prog_procs merge_prog)
            prog_main_name (prog_main merge_prog))
         (cfg_exit merge_cfg) \<noteq> None"

definition merge_unbuffered_sigma where
  "merge_unbuffered_sigma = snd (the (TD_side_always_join_Interp_solve_c merge_eqs_unbuffered (cfg_exit merge_cfg)))"

definition merge_buffered_sigma where
  "merge_buffered_sigma = snd (the (TD_side_always_join_Interp_solve_c
      (sign_exec_eqs merge_is_bot_pred merge_gs (prog_table merge_prog) (prog_procs merge_prog)
         prog_main_name (prog_main merge_prog))
      (cfg_exit merge_cfg)))"

value "merge_unbuffered_sigma (Inr ())"
value "merge_buffered_sigma (Inr ())"

text \<open>Agreement check: the buffered generator's stable global slot matches the
  original unbuffered generator's, at both the exit local slot and the shared
  global slot.\<close>

value "merge_buffered_sigma (Inr ()) = merge_unbuffered_sigma (Inr ())"
value "merge_buffered_sigma (Inl (cfg_exit merge_cfg)) = merge_unbuffered_sigma (Inl (cfg_exit merge_cfg))"

end
