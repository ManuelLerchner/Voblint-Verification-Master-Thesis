theory Parity_Transfer
  imports
    Parity_Backward
    Parity_Special
    Parity_Numeric_Queries
    "Voblint_Nonrelational.Nonrelational_Transfer"
begin

section \<open>What each kind of CFG edge does to a parity store\<close>

text \<open>
  A parity store records, for each variable, whether it is even, odd, either
  (\<^const>\<open>PTop\<close>) or unreachable (\<^const>\<open>PBot\<close>). How an edge of a compiled graph
  moves such a store is not a Parity question --- an assignment re-evaluates its
  right-hand side and overwrites the target, a guard runs the backward branch, a
  return writes into the return variable, procedure entry resets the callee frame
  and binds the formals --- so it is \<^locale>\<open>sound_nonrelational_ops\<close> that says
  it, once, for every domain that gives one abstract value per variable.

  What is Parity's own are the primitive choices. \<open>parity_ops\<close> collects the
  evaluator, the comparison queries, \<^const>\<open>parity_refine_ops\<close> --- whose
  inverses let \<open>x + 1 == y\<close> with \<open>y\<close> even make \<open>x\<close> odd --- the special calls, and
  \<^const>\<open>PTop\<close>. The one interpretation below derives the guard filters, the
  branch, the check classifier and the transfer from that bundle, and rewrites the
  locale's special-call dispatch to \<^const>\<open>special_parity\<close>, Parity's own \<open>fun\<close>,
  rather than introducing a second name for it.
\<close>

lemma parity_check_domain: "sound_check_query parity_less parity_eq gamma_state aval_parity"
  by unfold_locales (rule parity_arith.aval_abs_sound)

definition parity_ops :: "parity nonrelational_ops" where
  "parity_ops = \<lparr> n_aval = aval_parity, n_query = \<lparr>q_less = parity_less, q_eq = parity_eq\<rparr>,
                  n_refine = parity_refine_ops, n_special = parity_special_ops \<rparr>"

lemma parity_ops_simps [simp]:
  "n_aval parity_ops = aval_parity"
  "q_less (n_query parity_ops) = parity_less"
  "q_eq (n_query parity_ops) = parity_eq"
  "n_refine parity_ops = parity_refine_ops"
  "n_special parity_ops = parity_special_ops"
  by (simp_all add: parity_ops_def)

global_interpretation parity_tf: mono_nonrelational_ops parity_ops
  rewrites "(top :: parity) = PTop"
    and "sound_minmax_ops.special_transfer (n_special parity_ops) (n_aval parity_ops)
           = special_parity"
  defines assign_parity = parity_tf.assign
    and skip_parity = parity_tf.skip
    and body_parity = parity_tf.body
    and event_parity = parity_tf.event
    and return_parity = parity_tf.ret
    and enter_frame_parity_for = parity_tf.enter_frame_for
    and enter_parity_for = parity_tf.enter_for
    and enter_parity_ci_for = parity_tf.enter_ci_for
    and parity_tf_abs = parity_tf.tf_abs
    and afilter_parity = parity_tf.backward.afilter
    and feasible_parity = parity_tf.backward.feasible
    and bfilter_parity = parity_tf.backward.bfilter
    and branch_parity = parity_tf.backward.branch
    and parity_truthy_query = parity_tf.check.truthy_query
    and parity_check_query = parity_tf.check.check_query
    and parity_classify_check = parity_tf.check.classify_check
    and parity_eval_answer = parity_tf.check.eval_answer
    and parity_checks_proven = parity_tf.check.abstract_checks_proven
proof -
  show "mono_nonrelational_ops parity_ops"
  proof (rule mono_nonrelational_opsI, unfold parity_ops_simps parity_refine_ops_simps)
    show "mono_minmax_ops parity_special_ops aval_parity"
      by (rule parity_special.mono_minmax_ops_axioms)
    show "mono_refinement inf aval_parity parity_tobool
            inv_conservative inv_eq_parity inv_plus_parity inv_minus_parity inv_times_parity"
      by (rule parity_backward_domain)
    show "sound_check_query parity_less parity_eq gamma_state aval_parity"
      by (rule parity_check_domain)
  qed
qed (simp_all add: special_parity_eq_transfer fun_eq_iff top_parity_def)

text \<open>
  No fact is renamed. The transfer functions get Parity-prefixed names above
  because they are constants a caller applies, exported to OCaml and named in
  registration data; the theorems about them stay under \<open>parity_tf.\<close>, which is
  where a reader looks to find out that they are the generic ones rather than
  Parity's own. \<^const>\<open>skip_parity\<close>'s soundness is \<open>parity_tf.skip_sound\<close>, the
  branch's is \<open>parity_tf.backward.branch_sound\<close>, and the framework's transfer contract at
  Parity is \<open>parity_tf.is_sound_nonrelational_transfer\<close>.
\<close>

subsection \<open>Executable refinement tests\<close>

definition test_env_parity :: "parity abs_state" where
  "test_env_parity = (\<lambda>_. PTop)((STR ''y'') := PEven)"

text \<open>\<open>x + 1 == y\<close> with \<open>y\<close> even makes \<open>x\<close> odd.\<close>
lemma bfilter_parity_plus_narrows:
  "bfilter_parity (Eq (Plus (V (STR ''x'')) (N 1)) (V (STR ''y''))) True test_env_parity
     (STR ''x'') = POdd"
  unfolding test_env_parity_def by eval

text \<open>An order guard says nothing about parity.\<close>
lemma bfilter_parity_less_identity:
  "bfilter_parity (Less (V (STR ''x'')) (N 3)) True test_env_parity (STR ''x'') = PTop"
  unfolding test_env_parity_def by eval

end
