theory Sign_Transfer
  imports
    Sign_Backward
    Sign_Special
    Sign_Numeric_Queries
    "Voblint_Nonrelational.Nonrelational_Transfer"
begin

section \<open>What each kind of CFG edge does to a sign store\<close>

text \<open>
  A sign store maps every variable to one of the seven signs. How an edge of a
  compiled graph moves such a store is not a Sign question: an assignment
  re-evaluates its right-hand side and overwrites the target, a guard runs the
  backward branch, a return writes into the return variable, procedure entry
  resets the callee frame and binds the formals, and skip, body entry and check
  observation leave the store alone. That is \<^locale>\<open>sound_nonrelational_ops\<close>,
  proved sound and monotone once for any domain that gives one abstract value per
  variable.

  So this theory only states Sign's bundle of primitive choices and certifies it.
  \<open>sign_ops\<close> collects \<^const>\<open>aval_sign\<close>, the comparison queries
  \<^const>\<open>sign_less\<close>/\<^const>\<open>sign_eq\<close>, \<^const>\<open>sign_refine_ops\<close>,
  \<^const>\<open>sign_special_ops\<close> and \<^const>\<open>STop\<close>; each capability is already
  certified in the theory that introduces it. The guard filters, the branch, the
  check classifier and every transfer function are derived from the bundle by the
  one interpretation below, which names the results Sign's callers apply.
  \<open>Sign_Exec\<close>'s executable mirror runs on the same bundle.

  \<^const>\<open>special_sign\<close> is the one name that does not come from the interpretation.
  It is Sign's own \<open>fun\<close> in \<^theory>\<open>Voblint_Analysis_Sign.Sign_Special\<close>, written
  out case by case because a reader wants to see the three special calls, so the
  interpretation rewrites the locale's dispatch to it rather than introducing a
  second name for the same function.
\<close>

definition sign_ops :: "sign nonrelational_ops" where
  "sign_ops = \<lparr> n_aval = aval_sign, n_query = \<lparr>q_less = sign_less, q_eq = sign_eq\<rparr>,
                n_refine = sign_refine_ops, n_special = sign_special_ops, n_top = STop \<rparr>"

lemma sign_ops_simps [simp]:
  "n_aval sign_ops = aval_sign"
  "q_less (n_query sign_ops) = sign_less"
  "q_eq (n_query sign_ops) = sign_eq"
  "n_refine sign_ops = sign_refine_ops"
  "n_special sign_ops = sign_special_ops"
  "n_top sign_ops = STop"
  by (simp_all add: sign_ops_def)

global_interpretation sign_tf: mono_nonrelational_ops sign_ops
  rewrites "n_top sign_ops = STop"
    and "sound_special_ops.special_transfer (n_special sign_ops) (n_aval sign_ops) = special_sign"
  defines assign_sign = sign_tf.assign
    and skip_sign = sign_tf.skip
    and body_sign = sign_tf.body
    and event_sign = sign_tf.event
    and return_sign = sign_tf.ret
    and enter_frame_sign_for = sign_tf.enter_frame_for
    and enter_sign_for = sign_tf.enter_for
    and enter_sign_ci_for = sign_tf.enter_ci_for
    and sign_tf_abs = sign_tf.tf_abs
    and afilter_sign = sign_tf.backward.afilter
    and feasible_sign = sign_tf.backward.feasible
    and bfilter_sign = sign_tf.backward.bfilter
    and branch_sign = sign_tf.backward.branch
    and bfilter_lifted_sign = sign_tf.backward.bfilter_lifted
    and branch_lifted_sign = sign_tf.backward.branch_lifted
    and bfilter_sign_st_lift = sign_tf.backward.bfilter_st_lift
    and sign_truthy_query = sign_tf.check.truthy_query
    and sign_check_query = sign_tf.check.check_query
    and sign_classify_check = sign_tf.check.classify_check
    and sign_eval_answer = sign_tf.check.eval_answer
    and sign_checks_proven = sign_tf.check.abstract_checks_proven
proof -
  show "mono_nonrelational_ops sign_ops"
  proof (rule mono_nonrelational_opsI, unfold sign_ops_simps sign_refine_ops_simps)
    show "mono_special_ops sign_special_ops aval_sign"
      by (rule sign_special.mono_special_ops_axioms)
    show "backward_domain_mono inf aval_sign sign_tobool
            inv_less_sign inv_eq_sign inv_conservative inv_conservative inv_conservative"
      by (rule sign_backward_domain)
    show "abstract_check_domain sign_less sign_eq gamma_state aval_sign"
      by unfold_locales (rule sign_arith.aval_abs_sound)
    show "STop = top"
      by (simp add: top_sign_def)
  qed
qed (simp_all add: special_sign_eq_transfer fun_eq_iff)

text \<open>
  No fact is renamed here. The transfer functions get Sign-prefixed names above
  because they are constants a caller applies, exported to OCaml and named in
  registration data; the theorems about them stay under \<open>sign_tf.\<close>, which is where
  a reader looks to find out that they are the generic ones rather than Sign's
  own. \<^const>\<open>skip_sign\<close>'s soundness is \<open>sign_tf.skip_sound\<close>, the branch's is
  \<open>sign_tf.br_sound\<close>, and the framework's transfer contract at Sign is
  \<open>sign_tf.is_sound_nonrelational_transfer\<close>.
\<close>

thm sign_tf.backward.bfilter.simps(1) sign_tf.backward.afilter.simps(1)

subsection \<open>Executable end-to-end @{const bfilter_sign} tests\<close>

definition test_env_nonneg_eq :: "sign abs_state" where
  "test_env_nonneg_eq = (\<lambda>_. STop)((STR ''x'') := SNonNeg)"

text \<open>@{text \<open>x = 0\<close>} known true meets \<open>x\<close>'s bound with @{term SZero}.\<close>
lemma bfilter_sign_eq_true_narrows:
  "bfilter_sign (Eq (V (STR ''x'')) (N 0)) True test_env_nonneg_eq (STR ''x'') = SZero"
  unfolding test_env_nonneg_eq_def by eval

text \<open>@{text \<open>x != 0\<close>} known true (i.e. the guard @{text \<open>x = 0\<close>} is false) on
  @{term SNonNeg} narrows to @{term SPos}: the disequality narrowing
  @{const inv_eq_sign} supplies.\<close>
lemma bfilter_sign_eq_false_narrows_to_pos:
  "bfilter_sign (Eq (V (STR ''x'')) (N 0)) False test_env_nonneg_eq (STR ''x'') = SPos"
  unfolding test_env_nonneg_eq_def by eval

end
