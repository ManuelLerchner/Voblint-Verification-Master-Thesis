(* src/Analyses/Parity/Parity_Transfer.thy *)
global_interpretation parity_tf: mono_nonrelational_ops parity_ops
  rewrites "n_top parity_ops = PTop"
    and "sound_special_ops.special_transfer (n_special parity_ops) (n_aval parity_ops)
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
