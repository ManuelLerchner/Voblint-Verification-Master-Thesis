theory DG_Base
  imports DG_Soundness
begin

section \<open>Base-style whole-state DG construction\<close>

text \<open>
  A Base-style D/G specification never routes program state through a separate
  local/global reconstruction: the local unknown \<open>'a abs_state lifted\<close> already
  carries every VIMP variable, so an ordinary transfer runs on it directly. The
  global carrier \<open>'g\<close> stays a free \<open>bounded_semilattice_sup_bot\<close> type that
  every field threads through unchanged -- this construction never publishes to
  it and never reads from it. \<open>gs\<close> appears only inside \<open>tf\<close>'s own
  \<open>tf_enter\<close>/\<open>tf_combine_env\<close> fields, i.e. only for the VIMP call-boundary
  scoping rule (globals persist, locals reset/bind formals) that
  \<^const>\<open>combine_env_abs\<close> and \<^const>\<open>enter_frame_D\<close> already implement; no
  \<^const>\<open>restrict_local_for\<close>, \<^const>\<open>restrict_global_for\<close>, or
  \<^const>\<open>combine_env_abs\<close>-style reconstruction against \<open>'g\<close> occurs anywhere
  in this record.

  \<open>dgs_caller_cont\<close> is the identity: the Base carrier holds no relation between
  the caller's locals and anything the callee could invalidate, so there is
  nothing for the caller half of \<open>enter\<close> to drop, and the value \<open>combine\<close>
  receives is the raw call-site one.  \<open>dgs_combine_env\<close> is likewise the identity
  on that value: with no separate global accumulator to reconcile \<open>dc\<close> against,
  the two-stage \<^const>\<open>dgs_combine\<close> split degenerates to passing \<open>dc\<close> through
  unchanged and letting \<open>dgs_combine_assign\<close> do the entire combine once \<open>de\<close> is
  available.  Only \<open>ci_dst\<close> of the call metadata is consumed, by the return
  assignment.
\<close>

definition base_dg_spec_for_lifted ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::sound_domain abs_state \<Rightarrow> bool)
   \<Rightarrow> 'a domain_transfer
   \<Rightarrow> ('a abs_state lifted, 'g::bounded_semilattice_sup_bot) dg_spec"
where
  "base_dg_spec_for_lifted gs is_bot_pred tf = (|
    dgs_skip       = (\<lambda>d g. (g, transfer_lift is_bot_pred (skip\<^sup># tf) d)),
    dgs_assign     = (\<lambda>x e d g. (g, transfer_lift is_bot_pred (assign\<^sup># tf x e) d)),
    dgs_special    = (\<lambda>sc x d g. (g, transfer_lift is_bot_pred (special\<^sup># tf sc x) d)),
    dgs_branch     = (\<lambda>b pol d g. (g, transfer_lift is_bot_pred (branch\<^sup># tf b pol) d)),
    dgs_body       = (\<lambda>p d g. (g, transfer_lift is_bot_pred (body\<^sup># tf p) d)),
    dgs_return     = (\<lambda>e p d g. (g, transfer_lift is_bot_pred (return\<^sup># tf e p) d)),
    dgs_enter      = (\<lambda>xs es d g. (g, transfer_lift is_bot_pred (enter\<^sup># tf xs es) d)),
    dgs_event      = (\<lambda>ev d g. (g, transfer_lift is_bot_pred (event\<^sup># tf ev) d)),
    dgs_caller_cont    = (\<lambda>ci dc g. dc),
    dgs_combine_env    = (\<lambda>ci dc de g. (g, dc)),
    dgs_combine_assign = (\<lambda>ci de g merged.
      (g, transfer_lift2 is_bot_pred (combine\<^sup># gs (ci_dst ci)) (snd merged) de))
  |)"

subsection \<open>Basic equations\<close>

text \<open>
  Record-level type sanity: the generic \<^const>\<open>dg_spec_step\<close>/\<^const>\<open>dgs_combine\<close>
  machinery dispatches to \<^const>\<open>transfer_lift\<close>/\<^const>\<open>transfer_lift2\<close> directly on the
  whole-state carrier, with no further reasoning about \<open>gs\<close> beyond what \<open>tf\<close> itself
  already bakes in.
\<close>

lemma dg_spec_step_base_for_lifted:
  "dg_spec_step (base_dg_spec_for_lifted gs is_bot_pred tf) a d g =
     (g, transfer_lift is_bot_pred (apply_tf tf a) d)"
  unfolding base_dg_spec_for_lifted_def
  by (cases a) simp_all

lemma dgs_enter_base_for_lifted:
  "dgs_enter (base_dg_spec_for_lifted gs is_bot_pred tf) xs es d g =
     (g, transfer_lift is_bot_pred (enter\<^sup># tf xs es) d)"
  unfolding base_dg_spec_for_lifted_def by simp

text \<open>The caller half of \<open>enter\<close> hands \<open>combine\<close> the raw call-site value, so
  every Base equation below reads exactly as it did before the call/return
  protocol split the two halves apart.\<close>

lemma dgs_caller_cont_base_for_lifted [simp]:
  "dgs_caller_cont (base_dg_spec_for_lifted gs is_bot_pred tf) ci dc g = dc"
  unfolding base_dg_spec_for_lifted_def by simp

lemma dgs_combine_base_for_lifted:
  "dgs_combine (base_dg_spec_for_lifted gs is_bot_pred tf) ci dc de g =
     (g, transfer_lift2 is_bot_pred (combine\<^sup># gs (ci_dst ci)) dc de)"
  unfolding dgs_combine_def base_dg_spec_for_lifted_def by simp

subsection \<open>Bot propagation\<close>

text \<open>
  A dead local unknown dominates every ordinary field before \<open>tf\<close> ever runs --
  \<^const>\<open>transfer_lift\<close>'s own \<^const>\<open>bind_lift\<close> short-circuit, with no
  \<^const>\<open>combine_env_abs\<close>/\<^const>\<open>assemble_env_abs\<close> reconstruction step to reason
  about first.
\<close>

lemma dg_spec_step_base_for_lifted_Bot:
  "dg_spec_step (base_dg_spec_for_lifted gs is_bot_pred tf) a Bot g = (g, Bot)"
  unfolding dg_spec_step_base_for_lifted by simp

lemma dgs_enter_base_for_lifted_Bot:
  "dgs_enter (base_dg_spec_for_lifted gs is_bot_pred tf) xs es Bot g = (g, Bot)"
  unfolding dgs_enter_base_for_lifted by simp

lemma dgs_combine_base_for_lifted_dc_bot:
  "dgs_combine (base_dg_spec_for_lifted gs is_bot_pred tf) dst Bot de g = (g, Bot)"
  unfolding dgs_combine_base_for_lifted by (cases de) (simp_all add: transfer_lift2_def)

lemma dgs_combine_base_for_lifted_de_bot:
  "dgs_combine (base_dg_spec_for_lifted gs is_bot_pred tf) dst dc Bot g = (g, Bot)"
  unfolding dgs_combine_base_for_lifted by (cases dc) (simp_all add: transfer_lift2_def)

subsection \<open>Packaging correspondence\<close>

text \<open>
  Generic executable/mathematical commute for \<^const>\<open>transfer_lift\<close>/
  \<^const>\<open>transfer_lift2\<close> themselves, independent of any executable state
  representation: this is the one fact an executable Base mirror needs per
  field, proved once here rather than once per domain.
\<close>

lemma transfer_lift_commute:
  assumes commute: "\<And>s. phi (f s) = F (phi s)"
    and exact: "\<And>s. is_bot_pred s = is_bot_pred' (phi s)"
  shows "map_lift phi (transfer_lift is_bot_pred f d) = transfer_lift is_bot_pred' F (map_lift phi d)"
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def commute exact)

lemma transfer_lift2_commute:
  assumes commute: "\<And>s t. phi (f s t) = F (phi s) (phi t)"
    and exact: "\<And>s. is_bot_pred s = is_bot_pred' (phi s)"
  shows "map_lift phi (transfer_lift2 is_bot_pred f d1 d2) =
           transfer_lift2 is_bot_pred' F (map_lift phi d1) (map_lift phi d2)"
  by (cases d1; cases d2) (simp_all add: transfer_lift2_def normalize_lift_def commute exact)

subsection \<open>Soundness\<close>

text \<open>
  The meaning of a Base-style Answer/Side pair never depends on \<open>g\<close>: nothing in
  \<^const>\<open>base_dg_spec_for_lifted\<close> ever publishes to or reads from it.
\<close>

definition gamma_dg_base ::
  "'a::sound_domain abs_state lifted \<Rightarrow> 'g::bounded_semilattice_sup_bot \<Rightarrow> store set"
where
  "gamma_dg_base d g = gamma_state_lift d"

lemma gamma_dg_base_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_dg_base d g \<subseteq> gamma_dg_base d' g'"
  unfolding gamma_dg_base_def
proof (cases d)
  case Bot
  then show "gamma_state_lift d \<subseteq> gamma_state_lift d'" by simp
next
  case (Lifted sigma)
  then obtain sigma' where d'_eq: "d' = Lifted sigma'" and le: "sigma \<le> sigma'"
    using assms(1) by (cases d') auto
  show "gamma_state_lift d \<subseteq> gamma_state_lift d'"
    unfolding Lifted d'_eq using gamma_state_mono[OF le] by simp
qed

lemma gamma_dg_base_step_sound:
  assumes tf_sound: "sound_transfer_for gs tf"
    and is_bot_pred_sound: "\<And>sigma. is_bot_pred sigma \<Longrightarrow> \<lbrakk>sigma\<rbrakk> = {}"
  shows "edge_collect a (gamma_dg_base d g) \<subseteq>
           (case dg_spec_step (base_dg_spec_for_lifted gs is_bot_pred tf) a d g of
              (g', d') \<Rightarrow> gamma_dg_base d' g')"
proof (cases d)
  case Bot
  then show ?thesis by (simp add: gamma_dg_base_def)
next
  case (Lifted sigma)
  have base: "edge_collect a (gamma_state sigma) \<subseteq> \<lbrakk>apply_tf tf a sigma\<rbrakk>"
    by (rule sound_transfer_for.edge_collect_apply_tf_sound_for[OF tf_sound])
  show ?thesis
  proof (cases "is_bot_pred (apply_tf tf a sigma)")
    case True
    then have "\<lbrakk>apply_tf tf a sigma\<rbrakk> = {}"
      by (rule is_bot_pred_sound)
    with base Lifted show ?thesis by (simp add: gamma_dg_base_def)
  next
    case False
    then show ?thesis
      using base Lifted
      unfolding dg_spec_step_base_for_lifted gamma_dg_base_def
      by (simp add: transfer_lift_def normalize_lift_def)
  qed
qed

lemma gamma_dg_base_combine_sound:
  assumes tf_sound: "sound_transfer_for gs tf"
    and is_bot_pred_sound: "\<And>sigma. is_bot_pred sigma \<Longrightarrow> \<lbrakk>sigma\<rbrakk> = {}"
    and sc: "s \<in> gamma_dg_base dc g" and tc: "t \<in> gamma_dg_base de g"
  shows "combine_collect gs (ci_dst ci) s t \<in>
           (case dgs_combine (base_dg_spec_for_lifted gs is_bot_pred tf) ci dc de g of
              (g', d') \<Rightarrow> gamma_dg_base d' g')"
proof -
  obtain sigma_c where dc_eq: "dc = Lifted sigma_c" and sc': "s \<in> \<lbrakk>sigma_c\<rbrakk>"
    using sc unfolding gamma_dg_base_def by (cases dc) auto
  obtain sigma_e where de_eq: "de = Lifted sigma_e" and tc': "t \<in> \<lbrakk>sigma_e\<rbrakk>"
    using tc unfolding gamma_dg_base_def by (cases de) auto
  have base: "combine_collect gs (ci_dst ci) s t
                \<in> \<lbrakk>combine\<^sup># gs (ci_dst ci) sigma_c sigma_e\<rbrakk>"
    by (rule combine_collect_sound[OF sc' tc'])
  show ?thesis
  proof (cases "is_bot_pred (combine\<^sup># gs (ci_dst ci) sigma_c sigma_e)")
    case True
    then have "\<lbrakk>combine\<^sup># gs (ci_dst ci) sigma_c sigma_e\<rbrakk> = {}"
      by (rule is_bot_pred_sound)
    with base show ?thesis by simp
  next
    case False
    then show ?thesis
      using base dc_eq de_eq
      unfolding dgs_combine_base_for_lifted gamma_dg_base_def
      by (simp add: transfer_lift2_def normalize_lift_def)
  qed
qed

lemma gamma_dg_base_enter_sound:
  assumes tf_sound: "sound_transfer_for gs tf"
    and is_bot_pred_sound: "\<And>sigma. is_bot_pred sigma \<Longrightarrow> \<lbrakk>sigma\<rbrakk> = {}"
    and sc: "s \<in> gamma_dg_base dc g"
  shows "call_enter gs (CallEdge dst pars args) s \<in>
           (case dgs_enter (base_dg_spec_for_lifted gs is_bot_pred tf) pars args dc g of
              (g', d') \<Rightarrow> gamma_dg_base d' g')"
proof -
  obtain sigma_c where dc_eq: "dc = Lifted sigma_c" and sc': "s \<in> \<lbrakk>sigma_c\<rbrakk>"
    using sc unfolding gamma_dg_base_def by (cases dc) auto
  have base: "call_enter gs (CallEdge dst pars args) s \<in> \<lbrakk>enter\<^sup># tf pars args sigma_c\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_forD[OF tf_sound sc']
    by (simp add: call_enter_CallEdge)
  show ?thesis
  proof (cases "is_bot_pred (enter\<^sup># tf pars args sigma_c)")
    case True
    then have "\<lbrakk>enter\<^sup># tf pars args sigma_c\<rbrakk> = {}"
      by (rule is_bot_pred_sound)
    with base show ?thesis by simp
  next
    case False
    then show ?thesis
      using base dc_eq
      unfolding dgs_enter_base_for_lifted gamma_dg_base_def
      by (simp add: transfer_lift_def normalize_lift_def)
  qed
qed

text \<open>
  No reference to any concrete domain: instantiating \<open>tf\<close> with a domain's own
  \<^const>\<open>sound_transfer_for\<close> interpretation and \<open>is_bot_pred\<close> with its
  \<^const>\<open>is_bot_state\<close> (via \<open>is_bot_state_gamma_state_empty\<close>) is the entire
  per-domain obligation.
\<close>

theorem base_dg_spec_sound:
  assumes tf_sound: "sound_transfer_for gs tf"
    and is_bot_pred_sound: "\<And>sigma. is_bot_pred sigma \<Longrightarrow> \<lbrakk>sigma\<rbrakk> = {}"
  shows "sound_dg_spec (base_dg_spec_for_lifted gs is_bot_pred tf) gamma_dg_base gs"
  apply unfold_locales
  subgoal for d d' g g' by (rule gamma_dg_base_mono)
  subgoal for a d g by (rule gamma_dg_base_step_sound[OF tf_sound is_bot_pred_sound])
  subgoal premises prems using prems by simp
  subgoal premises prems by (rule gamma_dg_base_combine_sound[OF tf_sound is_bot_pred_sound prems])
  subgoal premises prems by (rule gamma_dg_base_enter_sound[OF tf_sound is_bot_pred_sound prems])
  done

end
