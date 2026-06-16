theory Example_Side_Execute_Proc
  imports "Voblint_Analysis.Sign_Exec_Sound" "Voblint_CFG.CFG_Collect_Trace_IP"
begin

section \<open>Certified sign analyzer on a two-procedure-call program\<close>

text \<open>
  \<open>main = (x := 1; call p; call q)\<close> with two procedures, \<open>p\<close> setting global
  \<open>Gx := 1\<close> and \<open>q\<close> setting \<open>Gy := 1\<close>.  This is a multi-edge interprocedural CFG
  (two \<open>EA_Enter\<close> edges, two combine triples), so -- unlike the single-edge
  \<open>Example_Side_Execute\<close> -- the sorted enumeration does not code-generate.  The
  certified soundness nonetheless follows by simply instantiating the
  program-parametric theorems of @{theory Voblint_Analysis.Sign_Exec_Sound}: the
  set-invariance transfer underneath them handles the multi-edge case.
\<close>

definition pq_pt :: proc_table where
  "pq_pt = ((\<lambda>_. None)
              (''p'' := Some (Assign ''Gx'' (BaseN (AExp.N 1))),
               ''q'' := Some (Assign ''Gy'' (BaseN (AExp.N 1)))))"

abbreviation pq_main :: com where
  "pq_main \<equiv> Seq (Assign ''x'' (BaseN (AExp.N 1))) (Seq (Call ''p'') (Call ''q''))"

abbreviation pq_exit :: pp where
  "pq_exit \<equiv> cfg_exit (compile_prog pq_pt [''p'', ''q''] pq_main)"

text \<open>
  The solver computes \<open>x \<mapsto> SPos\<close> at the exit -- precise, and surviving both
  procedure calls (locals are saved on entry and restored by the combine at each
  return).  The globals \<open>Gx\<close> / \<open>Gy\<close> come out \<open>STop\<close>: the single global unknown is
  flow-insensitive and joins the \<open>STop\<close> input seed, so it is sound but imprecise.
\<close>

value "sign_exec pq_pt [''p'', ''q''] pq_main ''x''"
value "sign_exec pq_pt [''p'', ''q''] pq_main ''Gx''"

lemma pq_computes_x_pos:
  "sign_exec pq_pt [''p'', ''q''] pq_main ''x'' = SPos"
  by eval

corollary pq_certified_sound:
  assumes "sign_exec_terminates pq_pt [''p'', ''q''] pq_main"
  shows "cfg_collect_ip (compile_prog pq_pt [''p'', ''q''] pq_main) UNIV pq_exit
         \<le> sign_domain.gamma_state (sign_exec pq_pt [''p'', ''q''] pq_main)"
  using assms by (rule sign_exec_sound_collecting)

subsection \<open>Soundness against the underlying trace semantics\<close>

text \<open>
  The state-level bound above is the last-store projection (\<open>alpha_last\<close>) of the
  interprocedural \<open>trace\<close> semantics @{const cfg_collect_trace_ip} -- the
  underlying semantics against which the whole development states soundness.  So
  the last store of \<^emph>\<open>any\<close> interprocedural trace reaching the exit is
  over-approximated by the computed result.

  The trace semantics connects further to AFP IMP2's standard big-step semantics
  via \<open>IMP2_Bridge.backward_sim\<close>
  (\<open>Semantics.big_step (to_imp2_pi \<Pi>) (to_imp2_com c, S) T \<Longrightarrow> pruns_to \<Pi> c (proj0 S) (proj0 T)\<close>),
  which lands in the procedural small-step run \<open>pruns_to\<close>.  Closing that onto
  \<open>cfg_collect_ip\<close> for an arbitrary program needs the operational adequacy
  \<open>pruns_to \<Longrightarrow> cfg_collect_ip\<close>, currently established per program rather than as a
  single general lemma; lifting it would extend the chain below to the genuine
  IMP2 big-step.
\<close>

corollary pq_certified_sound_trace:
  assumes "sign_exec_terminates pq_pt [''p'', ''q''] pq_main"
      and "tr \<in> cfg_collect_trace_ip (compile_prog pq_pt [''p'', ''q''] pq_main) UNIV pq_exit"
  shows "last tr \<in> sign_domain.gamma_state (sign_exec pq_pt [''p'', ''q''] pq_main)"
  using assms by (rule sign_exec_sound_trace)

end

