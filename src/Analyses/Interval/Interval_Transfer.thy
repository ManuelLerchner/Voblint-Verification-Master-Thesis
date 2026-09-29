theory Interval_Transfer
  imports
    Interval_Backward
    Interval_Special
    "Voblint_Nonrelational.Nonrelational_Transfer"
begin

section \<open>What each kind of CFG edge does to an interval store\<close>

text \<open>
  An interval store gives every variable a lower and an upper bound. How an edge
  of a compiled graph moves such a store is not an Interval question --- an
  assignment re-evaluates its right-hand side and overwrites the target, a guard
  runs the backward branch, a return writes into the return variable, procedure
  entry resets the callee frame to \<^const>\<open>ivl_top\<close> and binds the formals, and skip,
  body entry and check observation leave the store alone. That is
  \<^locale>\<open>sound_nonrelational_ops\<close>, proved sound and monotone once for every
  domain that gives one abstract value per variable.

  What is Interval's own are the primitive choices. \<open>ivl_ops\<close> collects the
  evaluator, the bound-comparison queries, \<^const>\<open>ivl_refine_ops\<close> --- whose
  comparison inverses make \<open>x < 8\<close> tighten \<open>x\<close>'s upper bound --- the special
  calls, and \<^const>\<open>ivl_top\<close>. The one interpretation below derives the guard
  filters, the branch, the check classifier and the transfer from that bundle,
  and rewrites the locale's special-call dispatch to \<^const>\<open>special_ivl\<close>,
  Interval's own \<open>fun\<close>, rather than introducing a second name for it.
\<close>

lemma interval_check_domain:
  "sound_check_query interval_less interval_eq gamma_state aval_ivl"
  by unfold_locales (rule ivl_arith.aval_abs_sound)

definition ivl_ops :: "ivl nonrelational_ops" where
  "ivl_ops = \<lparr> n_aval = aval_ivl, n_query = \<lparr>q_less = interval_less, q_eq = interval_eq\<rparr>,
               n_refine = ivl_refine_ops, n_special = ivl_special_ops \<rparr>"

lemma ivl_ops_simps [simp]:
  "n_aval ivl_ops = aval_ivl"
  "q_less (n_query ivl_ops) = interval_less"
  "q_eq (n_query ivl_ops) = interval_eq"
  "n_refine ivl_ops = ivl_refine_ops"
  "n_special ivl_ops = ivl_special_ops"
  by (simp_all add: ivl_ops_def)

global_interpretation ivl_tf: mono_nonrelational_ops ivl_ops
  rewrites "(top :: ivl) = ivl_top"
    and "sound_minmax_ops.special_transfer (n_special ivl_ops) (n_aval ivl_ops) = special_ivl"
  defines assign_ivl = ivl_tf.assign
    and skip_ivl = ivl_tf.skip
    and body_ivl = ivl_tf.body
    and event_ivl = ivl_tf.event
    and return_ivl = ivl_tf.ret
    and enter_frame_ivl_for = ivl_tf.enter_frame_for
    and enter_ivl_for = ivl_tf.enter_for
    and enter_ivl_ci_for = ivl_tf.enter_ci_for
    and ivl_tf_abs = ivl_tf.tf_abs
    and afilter_ivl = ivl_tf.backward.afilter
    and feasible_ivl = ivl_tf.backward.feasible
    and bfilter_ivl = ivl_tf.backward.bfilter
    and branch_ivl = ivl_tf.backward.branch
    and bfilter_lifted_ivl = ivl_tf.backward.bfilter_lifted
    and branch_lifted_ivl = ivl_tf.backward.branch_lifted
    and interval_truthy_query = ivl_tf.check.truthy_query
    and interval_check_query = ivl_tf.check.check_query
    and interval_classify_check = ivl_tf.check.classify_check
    and interval_eval_answer = ivl_tf.check.eval_answer
    and interval_checks_proven = ivl_tf.check.abstract_checks_proven
proof -
  show "mono_nonrelational_ops ivl_ops"
  proof (rule mono_nonrelational_opsI, unfold ivl_ops_simps ivl_refine_ops_simps)
    show "mono_minmax_ops ivl_special_ops aval_ivl"
      by (rule ivl_special.mono_minmax_ops_axioms)
    show "mono_refinement intersect_ivl aval_ivl interval_tobool
            inv_less_ivl inv_eq_ivl inv_conservative inv_conservative inv_conservative"
      by (rule ivl_backward_domain)
    show "sound_check_query interval_less interval_eq gamma_state aval_ivl"
      by (rule interval_check_domain)
  qed
qed (simp_all add: special_ivl_eq_transfer fun_eq_iff top_ivl_def)

text \<open>
  No fact is renamed. The transfer functions get Interval-prefixed names above
  because they are constants a caller applies, exported to OCaml and named in
  registration data; the theorems about them stay under \<open>ivl_tf.\<close>, which is where
  a reader looks to find out that they are the generic ones rather than
  Interval's own. \<^const>\<open>skip_ivl\<close>'s soundness is \<open>ivl_tf.skip_sound\<close>, the
  branch's is \<open>ivl_tf.backward.branch_sound\<close>, and the framework's transfer contract at
  Interval is \<open>ivl_tf.is_sound_nonrelational_transfer\<close>.
\<close>

text \<open>
  Reusable simp bundle for post-fixpoint proofs over the interval domain, covering
  the core evaluation rules every interval example shares. Examples with
  multiplication also need \<open>times_ivl_def\<close> and \<open>ivl_times_core.simps\<close>; ones with branch
  edges also need \<open>ivl_tf.backward.bfilter.simps\<close>; examples with procedure
  calls also need \<open>ivl_tf.op_defs\<close> and \<^const>\<open>combine_env\<close>'s definition.
\<close>

lemmas ivl_eval_simps =
  ivl_tf.tf_abs_def ivl_tf.assign_def
  aval_ivl.simps
  plus_ivl.simps plus_eint.simps
  less_eq_ivl_def le_fun_def

end
