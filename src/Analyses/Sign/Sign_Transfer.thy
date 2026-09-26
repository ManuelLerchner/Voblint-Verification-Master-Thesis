theory Sign_Transfer
  imports
    Sign_Backward
    Sign_Special
    "Voblint_Nonrelational.Nonrelational_Transfer"
begin

section \<open>What each kind of CFG edge does to a sign store\<close>

text \<open>
  A sign store maps every variable to one of the seven signs. How an edge of a
  compiled graph moves such a store is not a Sign question: an assignment
  re-evaluates its right-hand side and overwrites the target, a return writes the
  same into the return variable, procedure entry resets the callee frame and binds
  the formals, and skip, body entry and check observation leave the store alone.
  That is \<^locale>\<open>nonrelational_transfer\<close>, proved sound and monotone once for any
  domain that gives one abstract value per variable.

  So this theory only names Sign's instance of it. \<open>sign_ops\<close> is the primitive
  bundle the locale reads --- \<^const>\<open>aval_sign\<close>, \<^const>\<open>sign_special_ops\<close>,
  \<^const>\<open>branch_sign_st\<close> and \<^const>\<open>STop\<close> --- and \<^const>\<open>branch_sign\<close> travels
  beside it; each is already sound and monotone in the theory that introduces it.
  \<open>Sign_Exec\<close>'s executable mirror runs on that same bundle, so Sign's evaluator
  and its top element are written here once rather than once per layer. The
  interpretation carries every transfer function, every soundness and
  monotonicity fact, and the framework's transfer contract over to a
  Sign-prefixed name. Nothing about signs is restated.

  \<^const>\<open>special_sign\<close> is the one name that does not come from the interpretation.
  It is Sign's own \<open>fun\<close> in \<^theory>\<open>Voblint_Analysis_Sign.Sign_Special\<close>, written
  out case by case because a reader wants to see the three special calls, so the
  interpretation rewrites the locale's dispatch to it rather than introducing a
  second name for the same function.
\<close>

definition sign_ops :: "sign nonrelational_ops" where
  "sign_ops = \<lparr> n_aval = aval_sign, n_special = sign_special_ops,
                n_bfilter = branch_sign_st, n_top = STop \<rparr>"

lemma sign_ops_simps [simp]:
  "n_aval sign_ops = aval_sign"
  "n_special sign_ops = sign_special_ops"
  "n_bfilter sign_ops = branch_sign_st"
  "n_top sign_ops = STop"
  by (simp_all add: sign_ops_def)

global_interpretation sign_tf:
  nonrelational_transfer sign_ops branch_sign
  rewrites "n_aval sign_ops = aval_sign"
    and "n_special sign_ops = sign_special_ops"
    and "n_top sign_ops = STop"
    and "sound_special_ops.special_transfer sign_special_ops aval_sign = special_sign"
  defines assign_sign = sign_tf.assign
    and skip_sign = sign_tf.skip
    and body_sign = sign_tf.body
    and event_sign = sign_tf.event
    and return_sign = sign_tf.ret
    and enter_frame_sign_for = sign_tf.enter_frame_for
    and enter_sign_for = sign_tf.enter_for
    and enter_sign_ci_for = sign_tf.enter_ci_for
    and sign_tf_abs = sign_tf.tf_abs
proof -
  show "nonrelational_transfer sign_ops branch_sign"
    by unfold_locales
       (auto simp: top_sign_def
             intro: sign_min_sound sign_max_sound sign_min_combine_mono
                    sign_max_combine_mono sign_arith.aval_abs_sound[unfolded gamma_abs_sign]
                    branch_sign_sound branch_sign_mono)
  show "n_aval sign_ops = aval_sign" by simp
  show "n_special sign_ops = sign_special_ops" by simp
  show "n_top sign_ops = STop" by simp
  show "sound_special_ops.special_transfer sign_special_ops aval_sign = special_sign"
    by (intro ext) (simp add: special_sign_eq_transfer)
qed

text \<open>
  No fact is renamed here. The transfer functions get Sign-prefixed names above
  because they are constants a caller applies, exported to OCaml and named in
  registration data; the theorems about them stay under \<open>sign_tf.\<close>, which is where
  a reader looks to find out that they are the generic ones rather than Sign's
  own. \<^const>\<open>skip_sign\<close>'s soundness is \<open>sign_tf.skip_sound\<close>, and the framework's
  transfer contract at Sign is \<open>sign_tf.is_sound_transfer_for\<close>.
\<close>

end
