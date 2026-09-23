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
  assignment re-evaluates its right-hand side and overwrites the target, a return
  writes the same into the return variable, procedure entry resets the callee
  frame to \<^const>\<open>ivl_top\<close> and binds the formals, and skip, body entry and check
  observation leave the store alone. That is \<^locale>\<open>nonrelational_transfer\<close>,
  proved sound and monotone once for every domain that gives one abstract value
  per variable.

  What is Interval's own is the guard. \<^const>\<open>branch_ivl\<close> narrows on the branch
  its polarity argument selects, so \<open>x < 8\<close> tightens \<open>x\<close>'s upper bound instead of
  leaving it alone; it and \<^const>\<open>bfilter_ivl\<close> come from the
  \<^locale>\<open>backward_domain\<close> interpretation in
  \<^theory>\<open>Voblint_Analysis_Interval.Interval_Backward\<close>, and the two soundness
  readings below are all this theory proves. The interpretation then rewrites the
  locale's special-call dispatch to \<^const>\<open>special_ivl\<close>, Interval's own \<open>fun\<close>,
  rather than introducing a second name for it.
\<close>

subsection \<open>Abstract branch\<close>

text \<open>
  Guard refinement delegates to the generic \<open>bfilter\<close> proved sound in
  \<^locale>\<open>backward_domain\<close>. \<^const>\<open>bfilter_ivl\<close> narrows on the branch selected by
  its boolean polarity argument (\<^const>\<open>True\<close> for \<open>truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)\<close>,
  \<^const>\<open>False\<close> for its negation) --- this is Interval's branch operation directly,
  matching Goblint's single polarity-parametrized \<open>Spec.branch\<close>.
\<close>

lemma bfilter_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_ivl b res \<sigma>\<rbrakk>"
  using ivl_backward_domain.bfilter_sound by simp

text \<open>
  \<^const>\<open>branch_ivl\<close> is Interval's registered branch operation: a forward
  \<^const>\<open>interval_tobool\<close> feasibility check ahead of \<^const>\<open>bfilter_ivl\<close>, matching
  Goblint's \<open>Base.branch\<close> structure.
\<close>

lemma branch_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_ivl b res \<sigma>\<rbrakk>"
  using ivl_backward_domain.branch_sound by simp

subsection \<open>Interval's instance of the generic transfer\<close>

text \<open>
  \<open>ivl_ops\<close> is the primitive bundle both layers read: the locale below takes it,
  and so does the executable mirror in \<open>Interval_Exec\<close>, so Interval's evaluator
  and its top element are written once rather than once per layer.
  \<^const>\<open>branch_ivl\<close> travels beside it, since an abstract branch is the one
  primitive a bundle cannot carry through code generation.
\<close>

definition ivl_ops :: "ivl numeric_ops" where
  "ivl_ops = \<lparr> n_aval = aval_ivl, n_special = ivl_special_ops,
               n_bfilter = branch_ivl_st, n_top = ivl_top \<rparr>"

lemma ivl_ops_simps [simp]:
  "n_aval ivl_ops = aval_ivl"
  "n_special ivl_ops = ivl_special_ops"
  "n_bfilter ivl_ops = branch_ivl_st"
  "n_top ivl_ops = ivl_top"
  by (simp_all add: ivl_ops_def)

global_interpretation ivl_tf:
  nonrelational_transfer ivl_ops branch_ivl
  rewrites "n_aval ivl_ops = aval_ivl"
    and "n_special ivl_ops = ivl_special_ops"
    and "n_top ivl_ops = ivl_top"
    and "sound_special_ops.special_transfer ivl_special_ops aval_ivl = special_ivl"
  defines assign_ivl = ivl_tf.assign
    and skip_ivl = ivl_tf.skip
    and body_ivl = ivl_tf.body
    and event_ivl = ivl_tf.event
    and return_ivl = ivl_tf.ret
    and enter_frame_ivl_for = ivl_tf.enter_frame_for
    and enter_ivl_for = ivl_tf.enter_for
    and enter_ivl_ci_for = ivl_tf.enter_ci_for
    and ivl_tf_abs = ivl_tf.tf_abs
proof -
  show "nonrelational_transfer ivl_ops branch_ivl"
    by unfold_locales
       (auto simp: top_ivl_def
             intro: ivl_min_sound ivl_max_sound ivl_min_combine_mono ivl_max_combine_mono
                    aval_ivl_sound ivl_arith.aval_dom_mono branch_ivl_sound
                    ivl_backward_domain.branch_mono)
  show "n_aval ivl_ops = aval_ivl" by simp
  show "n_special ivl_ops = ivl_special_ops" by simp
  show "n_top ivl_ops = ivl_top" by simp
  show "sound_special_ops.special_transfer ivl_special_ops aval_ivl = special_ivl"
    by (intro ext) (simp add: special_ivl_eq_transfer)
qed

text \<open>
  No fact is renamed. The transfer functions get Interval-prefixed names above
  because they are constants a caller applies, exported to OCaml and named in
  registration data; the theorems about them stay under \<open>ivl_tf.\<close>, which is where
  a reader looks to find out that they are the generic ones rather than
  Interval's own. \<^const>\<open>skip_ivl\<close>'s soundness is \<open>ivl_tf.skip_sound\<close>, and the
  framework's transfer contract at Interval is \<open>ivl_tf.is_sound_transfer_for\<close>.
\<close>

text \<open>
  Reusable simp bundle for post-fixpoint proofs over the interval domain, covering
  the core evaluation rules every interval example shares. Examples with
  multiplication also need \<open>times_ivl_def\<close> and \<open>ivl_times_core.simps\<close>; ones with branch
  edges also need \<open>ivl_backward_domain.bfilter.simps\<close>; examples with procedure
  calls also need \<open>ivl_tf.op_defs\<close> and \<^const>\<open>combine_env\<close>'s definition.
\<close>

lemmas ivl_eval_simps =
  ivl_tf.tf_abs_def ivl_tf.assign_def
  aval_ivl.simps
  plus_ivl.simps plus_eint.simps
  less_eq_ivl_def le_fun_def

end
