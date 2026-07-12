theory Exec_Sign_Cmp_Keyed_Solve
  imports Exec_Sign_Cmp_Keyed_Run Exec_Sign_Run
begin

section \<open>Keyed-global context precision: executable solver run (sign)\<close>

text \<open>\<^bold>\<open>Role: executable precision regression.\<close> An \<open>eval\<close>-only witness that keyed context
  slots stay separate.  The proved keyed/combine soundness endpoint is
  \<open>context_analysis_soundness.collect_sound\<close>.\<close>
text \<open>
  The executable counterpart to \<open>Exec_Sign_Cmp_Keyed_Run\<close>.  There the keyed
  post-solution \<open>kw_sig\<close> is exhibited by hand and the combine obligations of
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close> are discharged against it.  Here
  the same two-call abstraction is written as a genuine side-effecting equation
  system over keyed global slots and handed to the vendored
  \<^const>\<open>TD_side_always_join_Interp_solve\<close>: the solver itself computes the
  per-context global routing, and the separated slots are read back by the code
  generator.

  Context \<open>kctx\<close> is the caller's surviving global-input class (\<open>KF\<close>: \<open>G = 0\<close>,
  \<open>KT\<close>: \<open>G = 1\<close>).  The callee \<open>f\<close> propagates its context's input to the global
  through the real \<^const>\<open>aval_sign\<close> transfer and side-effects the result to the
  keyed slot \<^term>\<open>Inr ctx\<close>.  Distinct contexts land in distinct slots, so the
  solved environment keeps \<^const>\<open>SZero\<close> and \<^const>\<open>SPos\<close> apart where the
  context-blind join-all read merges them to \<^const>\<open>SNonNeg\<close> --- exactly the
  precision the keying recovers, now sealed by the solver rather than asserted.
\<close>

subsection \<open>The keyed side-effecting equation system\<close>

text \<open>Context: the caller's global-input class at the call to \<open>f\<close>.\<close>
datatype kctx = KF | KT

text \<open>Program points of the two-call abstraction: \<open>main\<close> and \<open>f\<close>'s body per context.\<close>
datatype ppk = PMain | PF kctx

text \<open>
  \<open>f\<close> under context \<open>ctx\<close> reads the caller input local \<open>x\<close> (\<^const>\<open>SZero\<close> /
  \<^const>\<open>SPos\<close>), runs the assignment transfer \<open>G := x\<close>, and side-effects the
  global-only result to its keyed slot \<^term>\<open>Inr ctx\<close>.  \<open>main\<close> forces both
  activations, so the solver materialises both slots.
\<close>
fun keyed_eqs :: "ppk \<Rightarrow> (ppk, kctx, sign st) strategy_tree" where
  "keyed_eqs (PF ctx) =
     (let xin = update_st (bot :: sign st) ''x'' (case ctx of KF \<Rightarrow> SZero | KT \<Rightarrow> SPos);
          gv  = update_st bot ''G'' (aval_sign (BaseN (AExp.V ''x'')) (lookup_st xin))
      in Side ctx gv (Answer gv))"
| "keyed_eqs PMain =
     QueryL (PF KF) (\<lambda>_. QueryL (PF KT) (\<lambda>_. Answer bot))"

definition keyed_solution :: "ppk set \<times> (ppk + kctx \<Rightarrow> sign st)" where
  "keyed_solution = TD_side_always_join_Interp_solve keyed_eqs PMain"

subsection \<open>The solver computes separated keyed slots\<close>

text \<open>
  Each callee activation's global effect lands in its own slot; the solved
  environment reads \<^const>\<open>SZero\<close> at \<^term>\<open>Inr KF\<close> and \<^const>\<open>SPos\<close> at
  \<^term>\<open>Inr KT\<close>.  Both are produced by the code generator from the running
  solver, not asserted.
\<close>

lemma slot_KF: "lookup_st (snd keyed_solution (Inr KF)) ''G'' = SZero"
  unfolding keyed_solution_def by eval

lemma slot_KT: "lookup_st (snd keyed_solution (Inr KT)) ''G'' = SPos"
  unfolding keyed_solution_def by eval

text \<open>
  The context-blind read --- the join over all keyed slots, the monovariant
  global view --- merges the two to \<^const>\<open>SNonNeg\<close>.  This is the abstract
  \<^const>\<open>glob_env\<close> read that the \<open>cmp\<close>-filtered \<^const>\<open>glob_env_cmp\<close> refines; the
  precision separation is proved at the read layer in \<open>Exec_Sign_Cmp_Keyed_Run\<close>
  (\<open>read_False\<close> / \<open>read_True\<close> / \<open>merge_join_all\<close>).
\<close>

lemma slot_join_all:
  "lookup_st (snd keyed_solution (Inr KF) \<squnion> snd keyed_solution (Inr KT)) ''G'' = SNonNeg"
  unfolding keyed_solution_def by eval

subsection \<open>The precision payoff, sealed by the solver\<close>

theorem keyed_slots_strictly_separate:
  "lookup_st (snd keyed_solution (Inr KF)) ''G'' = SZero
   \<and> lookup_st (snd keyed_solution (Inr KT)) ''G'' = SPos
   \<and> lookup_st (snd keyed_solution (Inr KF) \<squnion> snd keyed_solution (Inr KT)) ''G'' = SNonNeg
   \<and> lookup_st (snd keyed_solution (Inr KF)) ''G''
       < lookup_st (snd keyed_solution (Inr KF) \<squnion> snd keyed_solution (Inr KT)) ''G''
   \<and> lookup_st (snd keyed_solution (Inr KT)) ''G''
       < lookup_st (snd keyed_solution (Inr KF) \<squnion> snd keyed_solution (Inr KT)) ''G''"
  unfolding keyed_solution_def by eval

text \<open>
  The soundness of reading these slots per context --- that a call under context
  \<open>ctx\<close> may consult only slot \<^term>\<open>Inr ctx\<close> --- is the \<open>CMP_SOUND\<close> obligation of
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>, discharged for this abstraction
  in \<open>Exec_Sign_Cmp_Keyed_Run\<close>.  This theory adds the executable half: the keyed
  routing and the join-all merge are computed by the verified TD side solver.
\<close>

end
