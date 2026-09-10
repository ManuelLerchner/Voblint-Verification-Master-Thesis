theory Congruence_Transfer
  imports
    Congruence_Backward
    Congruence_Special
    "Voblint_Nonrelational.Nonrelational_Transfer"
begin

section \<open>What each kind of edge does to a map from variables to residue classes\<close>

text \<open>
  One operation per edge the framework can hand a domain: an assignment writes the
  evaluated right-hand side, a call binds the actuals into a fresh frame, a return
  publishes its expression into the return variable, and skip, body entry and
  check observation leave the map alone. None of that is about modular arithmetic,
  so none of it is stated here: it is \<^locale>\<open>nonrelational_transfer\<close>, proved
  sound and monotone once for every domain that gives one abstract value per
  variable, and this theory names Congruence's instance of it.

  What is Congruence's own is the guard. \<^const>\<open>branch_congruence\<close> runs the
  domain's backward filter, so \<open>x + 1 == 3\<close> narrows \<open>x\<close> to a single integer rather
  than leaving it alone; it and \<^const>\<open>bfilter_congruence\<close> come from the
  \<^locale>\<open>backward_domain\<close> interpretation in
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Backward\<close>, and the two soundness
  readings below are all this theory proves. The interpretation then rewrites the
  locale's special-call dispatch to \<^const>\<open>special_congruence\<close>, Congruence's own
  \<open>fun\<close>, rather than introducing a second name for it.
\<close>

subsection \<open>Guards, through the backward filter\<close>

text \<open>
  \<^const>\<open>branch_congruence\<close> is \<^locale>\<open>backward_domain\<close>'s own branch: a forward
  \<^const>\<open>congruence_tobool\<close> feasibility test ahead of \<^const>\<open>bfilter_congruence\<close>,
  matching Goblint's \<open>Base.branch\<close> structure.
\<close>

lemma bfilter_congruence_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_congruence b res \<sigma>\<rbrakk>"
  using congruence_backward_domain.bfilter_sound by simp

lemma branch_congruence_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_congruence b res \<sigma>\<rbrakk>"
  using congruence_backward_domain.branch_sound by simp

lemma branch_congruence_mono:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> branch_congruence b res \<sigma>1 \<le> branch_congruence b res \<sigma>2"
  using congruence_backward_domain.branch_mono by (simp add: branch_congruence_def)

subsection \<open>Congruence's instance of the generic transfer\<close>

text \<open>
  \<open>congruence_ops\<close> is the primitive bundle both layers read: the locale below
  takes it, and so does the executable mirror in \<open>Congruence_Exec\<close>, so
  Congruence's evaluator and its top element are written once rather than once
  per layer. \<^const>\<open>branch_congruence\<close> travels beside it, since an abstract
  branch is the one primitive a bundle cannot carry through code generation.
\<close>

definition congruence_ops :: "congruence numeric_ops" where
  "congruence_ops = \<lparr> n_aval = aval_congruence, n_special = congruence_special_ops,
                      n_bfilter = branch_congruence_st, n_top = top \<rparr>"

lemma congruence_ops_simps [simp]:
  "n_aval congruence_ops = aval_congruence"
  "n_special congruence_ops = congruence_special_ops"
  "n_bfilter congruence_ops = branch_congruence_st"
  "n_top congruence_ops = top"
  by (simp_all add: congruence_ops_def)

global_interpretation congruence_tf:
  nonrelational_transfer congruence_ops branch_congruence
  rewrites "n_aval congruence_ops = aval_congruence"
    and "n_special congruence_ops = congruence_special_ops"
    and "n_top congruence_ops = top"
    and "sound_special_ops.special_transfer congruence_special_ops aval_congruence
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
proof -
  show "nonrelational_transfer congruence_ops branch_congruence"
    by unfold_locales
       (auto simp: congruence_min_mono congruence_max_mono
             intro: congruence_min_sound congruence_max_sound
                    congruence_arith.aval_dom_sound[unfolded gamma_abs_congruence]
                    congruence_arith.aval_dom_mono
                    branch_congruence_sound branch_congruence_mono)
  show "n_aval congruence_ops = aval_congruence" by simp
  show "n_special congruence_ops = congruence_special_ops" by simp
  show "n_top congruence_ops = top" by simp
  show "sound_special_ops.special_transfer congruence_special_ops aval_congruence
          = special_congruence"
    by (intro ext) (simp add: special_congruence_eq_transfer)
qed

text \<open>
  No fact is renamed. The transfer functions get Congruence-prefixed names above
  because they are constants a caller applies, exported to OCaml and named in
  registration data; the theorems about them stay under \<open>congruence_tf.\<close>, which is
  where a reader looks to find out that they are the generic ones rather than
  Congruence's own. \<^const>\<open>skip_congruence\<close>'s soundness is
  \<open>congruence_tf.skip_sound\<close>, and the framework's transfer contract at Congruence
  is \<open>congruence_tf.is_sound_transfer_for\<close>.
\<close>

end
