(* src/Analyses/Interval/Interval_Transfer.thy *)
global_interpretation ivl_tf: mono_nonrelational_ops ivl_ops
  rewrites "n_top ivl_ops = ivl_top"
    and "sound_special_ops.special_transfer (n_special ivl_ops) (n_aval ivl_ops) = special_ivl"
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
