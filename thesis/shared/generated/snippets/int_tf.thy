(* src/Analyses/Int/Int_Transfer.thy *)
global_interpretation int_tf: sound_nonrelational_ops "int_dom_ops mode"
  rewrites "n_top (int_dom_ops mode) = top"
    and "sound_special_ops.special_transfer (n_special (int_dom_ops mode)) (n_aval (int_dom_ops mode))
           = special_int_dom mode"
  defines assign_int_dom = int_tf.assign
    and skip_int_dom = int_tf.skip
    and body_int_dom = int_tf.body
    and event_int_dom = int_tf.event
    and return_int_dom = int_tf.ret
    and enter_frame_int_dom_for = int_tf.enter_frame_for
    and enter_int_dom_for = int_tf.enter_for
    and enter_int_dom_ci_for = int_tf.enter_ci_for
    and int_tf_abs = int_tf.tf_abs
    and afilter_int_dom = int_tf.backward.afilter
    and feasible_int_dom = int_tf.backward.feasible
    and bfilter_int_dom = int_tf.backward.bfilter
    and branch_int_dom_for = int_tf.backward.branch
    and bfilter_lifted_int_dom = int_tf.backward.bfilter_lifted
    and branch_lifted_int_dom = int_tf.backward.branch_lifted
    and int_truthy_query = int_tf.check.truthy_query
    and int_check_query = int_tf.check.check_query
    and int_classify_check = int_tf.check.classify_check
    and int_eval_answer = int_tf.check.eval_answer
    and int_checks_proven = int_tf.check.abstract_checks_proven
