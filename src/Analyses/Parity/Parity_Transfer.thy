theory Parity_Transfer
  imports
    Parity_Domain
    Parity_Special
    "Voblint_Nonrelational.Nonrelational_Transfer"
begin

section \<open>What each kind of CFG edge does to a parity store\<close>

text \<open>
  A parity store records, for each variable, whether it is even, odd, either
  (\<^const>\<open>PTop\<close>) or unreachable (\<^const>\<open>PBot\<close>). How an edge of a compiled graph
  moves such a store is not a Parity question --- an assignment re-evaluates its
  right-hand side and overwrites the target, a return writes the same into the
  return variable, procedure entry resets the callee frame and binds the formals
  --- so it is \<^locale>\<open>nonrelational_transfer\<close> that says it, once, for every
  domain that gives one abstract value per variable.

  Two things here are Parity's own. \<open>branch_parity\<close>, defined below, is the identity: a
  guard that held or failed says nothing about anyone's parity, so the domain has
  no backward filter to install and supplies the trivial one, which the locale
  accepts like any other. And the interpretation rewrites the locale's
  special-call dispatch to \<^const>\<open>special_parity\<close>, Parity's own \<open>fun\<close> in
  \<^theory>\<open>Voblint_Analysis_Parity.Parity_Special\<close>, rather than introducing a
  second name for it. Everything else is named and nothing else is proved.
\<close>

subsection \<open>Branch: no backward parity refinement\<close>

text \<open>
  The current parity analysis leaves guards unchanged. This is sound but loses
  facts an equality or arithmetic guard could establish, such as \<open>x = 1\<close> implying
  odd \<open>x\<close>. The polarity-parametrized operation stays explicit so a future backward
  filter can improve precision without changing the framework interface.
\<close>

definition branch_parity :: "exp \<Rightarrow> bool \<Rightarrow> parity abs_state \<Rightarrow> parity abs_state" where
  "branch_parity b pol \<sigma> = \<sigma>"

lemma branch_parity_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = pol \<Longrightarrow> s \<in> \<lbrakk>branch_parity b pol \<sigma>\<rbrakk>"
  by (simp add: branch_parity_def)

lemma branch_parity_mono:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> branch_parity b pol \<sigma>1 \<le> branch_parity b pol \<sigma>2"
  by (simp add: branch_parity_def)

subsection \<open>Parity's instance of the generic transfer\<close>

text \<open>
  \<open>parity_ops\<close> is the primitive bundle both layers read: the locale below takes
  it, and so does the executable mirror in \<open>Parity_Exec\<close>. Its executable filter
  is the identity, matching \<^const>\<open>branch_parity\<close>, which travels beside the
  bundle.
\<close>

definition parity_ops :: "parity nonrelational_ops" where
  "parity_ops = \<lparr> n_aval = aval_parity, n_special = parity_special_ops,
                  n_bfilter = (\<lambda>_ _ _ s. s), n_top = PTop \<rparr>"

lemma parity_ops_simps [simp]:
  "n_aval parity_ops = aval_parity"
  "n_special parity_ops = parity_special_ops"
  "n_bfilter parity_ops = (\<lambda>_ _ _ s. s)"
  "n_top parity_ops = PTop"
  by (simp_all add: parity_ops_def)

global_interpretation parity_tf:
  nonrelational_transfer parity_ops branch_parity
  rewrites "n_aval parity_ops = aval_parity"
    and "n_special parity_ops = parity_special_ops"
    and "n_top parity_ops = PTop"
    and "sound_special_ops.special_transfer parity_special_ops aval_parity = special_parity"
  defines assign_parity = parity_tf.assign
    and skip_parity = parity_tf.skip
    and body_parity = parity_tf.body
    and event_parity = parity_tf.event
    and return_parity = parity_tf.ret
    and enter_frame_parity_for = parity_tf.enter_frame_for
    and enter_parity_for = parity_tf.enter_for
    and enter_parity_ci_for = parity_tf.enter_ci_for
    and parity_tf_abs = parity_tf.tf_abs
proof -
  show "nonrelational_transfer parity_ops branch_parity"
    by unfold_locales
       (auto simp: top_parity_def
             intro: parity_min_sound parity_max_sound parity_min_combine_mono
                    parity_max_combine_mono parity_arith.aval_abs_sound[unfolded gamma_abs_parity]
                    branch_parity_sound branch_parity_mono)
  show "n_aval parity_ops = aval_parity" by simp
  show "n_special parity_ops = parity_special_ops" by simp
  show "n_top parity_ops = PTop" by simp
  show "sound_special_ops.special_transfer parity_special_ops aval_parity = special_parity"
    by (intro ext) (simp add: special_parity_eq_transfer)
qed

text \<open>
  No fact is renamed. The transfer functions get Parity-prefixed names above
  because they are constants a caller applies, exported to OCaml and named in
  registration data; the theorems about them stay under \<open>parity_tf.\<close>, which is
  where a reader looks to find out that they are the generic ones rather than
  Parity's own. \<^const>\<open>skip_parity\<close>'s soundness is \<open>parity_tf.skip_sound\<close>, and
  the framework's transfer contract at Parity is
  \<open>parity_tf.is_sound_transfer_for\<close>.
\<close>

end
