theory Congruence_Transfer
  imports
    Congruence_Backward
    Congruence_Special
    "Voblint_Nonrelational.Nonrelational_Transfer"
begin

section \<open>What each kind of edge does to a map from variables to residue classes\<close>

text \<open>
  One operation per edge the framework can hand a domain: an assignment writes the
  evaluated right-hand side, a guard runs the backward branch, a call binds the
  actuals into a fresh frame, a return publishes its expression into the return
  variable, and skip, body entry and check observation leave the map alone. None
  of that is about modular arithmetic, so none of it is stated here: it is
  \<^locale>\<open>sound_nonrelational_ops\<close>, proved sound and monotone once for every
  domain that gives one abstract value per variable.

  What is Congruence's own are the primitive choices. \<open>congruence_ops\<close> collects
  the evaluator, the comparison tables, \<^const>\<open>congruence_refine_ops\<close> --- whose
  inverses make \<open>x + 1 == 3\<close> narrow \<open>x\<close> to a single integer --- the special calls,
  and \<^const>\<open>top\<close>. The one interpretation below derives the guard filters, the
  branch, the check classifier and the transfer from that bundle, and rewrites the
  locale's special-call dispatch to \<^const>\<open>special_congruence\<close>, Congruence's own
  \<open>fun\<close>, rather than introducing a second name for it.
\<close>

lemma congruence_check_domain:
  "sound_check_query congruence_lt congruence_eqb gamma_state aval_congruence"
  by unfold_locales (rule congruence_arith.aval_abs_sound)

definition congruence_ops :: "congruence nonrelational_ops" where
  "congruence_ops =
     \<lparr> n_aval = aval_congruence, n_query = \<lparr>q_less = congruence_lt, q_eq = congruence_eqb\<rparr>,
       n_refine = congruence_refine_ops, n_special = congruence_special_ops \<rparr>"

lemma congruence_ops_simps [simp]:
  "n_aval congruence_ops = aval_congruence"
  "q_less (n_query congruence_ops) = congruence_lt"
  "q_eq (n_query congruence_ops) = congruence_eqb"
  "n_refine congruence_ops = congruence_refine_ops"
  "n_special congruence_ops = congruence_special_ops"
  by (simp_all add: congruence_ops_def)

global_interpretation congruence_tf: mono_nonrelational_ops congruence_ops
  rewrites "sound_minmax_ops.special_transfer (n_special congruence_ops) (n_aval congruence_ops)
           = special_congruence"
  defines assign_congruence = congruence_tf.assign
    and skip_congruence = congruence_tf.skip
    and body_congruence = congruence_tf.body
    and event_congruence = congruence_tf.event
    and return_congruence = congruence_tf.ret
    and enter_frame_congruence_for = congruence_tf.enter_frame_for
    and enter_congruence_for = congruence_tf.enter_for
    and enter_congruence_ci_for = congruence_tf.enter_ci_for
    and congruence_tf_abs = congruence_tf.tf_abs
    and afilter_congruence = congruence_tf.backward.afilter
    and feasible_congruence = congruence_tf.backward.feasible
    and bfilter_congruence = congruence_tf.backward.bfilter
    and branch_congruence = congruence_tf.backward.branch
    and congruence_truthy_query = congruence_tf.check.truthy_query
    and congruence_check_query = congruence_tf.check.check_query
    and congruence_classify_check = congruence_tf.check.classify_check
    and congruence_eval_answer = congruence_tf.check.eval_answer
    and congruence_checks_proven = congruence_tf.check.abstract_checks_proven
proof -
  show "mono_nonrelational_ops congruence_ops"
  proof (rule mono_nonrelational_opsI,
         unfold congruence_ops_simps congruence_refine_ops_simps)
    show "mono_minmax_ops congruence_special_ops aval_congruence"
      by (rule congruence_special.mono_minmax_ops_axioms)
    show "mono_refinement inf aval_congruence congruence_tobool
            inv_less_congruence inv_eq_congruence
            inv_plus_congruence inv_minus_congruence inv_times_congruence"
      by (rule congruence_backward_domain)
    show "sound_check_query congruence_lt congruence_eqb gamma_state aval_congruence"
      by (rule congruence_check_domain)
  qed
qed (simp_all add: special_congruence_eq_transfer fun_eq_iff)

text \<open>
  No fact is renamed. The transfer functions get Congruence-prefixed names above
  because they are constants a caller applies, exported to OCaml and named in
  registration data; the theorems about them stay under \<open>congruence_tf.\<close>, which is
  where a reader looks to find out that they are the generic ones rather than
  Congruence's own. \<^const>\<open>skip_congruence\<close>'s soundness is
  \<open>congruence_tf.skip_sound\<close>, the branch's is \<open>congruence_tf.backward.branch_sound\<close>, and the
  framework's transfer contract at Congruence is
  \<open>congruence_tf.is_sound_nonrelational_transfer\<close>.
\<close>

end
