(* src/Analyses/Sign/Sign_Transfer.thy *)
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
