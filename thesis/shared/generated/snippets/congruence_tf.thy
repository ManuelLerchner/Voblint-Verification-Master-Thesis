(* src/Analyses/Congruence/Congruence_Transfer.thy *)
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
