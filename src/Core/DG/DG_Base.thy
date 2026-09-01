theory DG_Base
  imports DG_Spec_Sound
begin

section \<open>Base-style whole-state DG construction\<close>

text \<open>
  A Base-style D/G specification is local-only: the local unknown already
  carries every VIMP variable, so an ordinary transfer runs on it directly
  and touches no global at all -- no \<open>man_global\<close> read, no \<open>man_sideg\<close>
  publication, so its compiled equations have no \<open>QueryG\<close> and no \<open>Side\<close>.
  Both constructions below are \<^const>\<open>local_dg_spec\<close> instances: the raw
  transfer on \<open>'a abs_state\<close>, and its reachability-lifted mirror where
  every field additionally routes through \<^const>\<open>transfer_lift\<close> so a dead
  local collapses to \<^const>\<open>Bot\<close> before the transfer ever runs.

  \<open>dgs_caller_cont\<close> is the identity: the Base carrier holds no relation
  between the caller's locals and anything the callee could invalidate, so
  there is nothing for the caller half of \<open>enter\<close> to drop, and the value
  \<open>combine\<close> receives is the raw call-site one. \<open>dgs_combine_env\<close> is
  likewise the identity on that value: the two-stage combine degenerates
  to passing the continuation through and letting \<open>dgs_combine_assign\<close> do
  the entire combine once the callee exit is available. Only \<open>ci_dst\<close> of
  the call metadata is consumed, by the return assignment.
\<close>

subsection \<open>The unlifted core\<close>

definition base_dg_spec_for ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> 'a::sound_domain domain_transfer
   \<Rightarrow> ('x,'k,'a abs_state,'g::bounded_semilattice_sup_bot) dg_spec"
where
  "base_dg_spec_for gs tf = local_dg_spec
     (skip\<^sup># tf) (assign\<^sup># tf) (special\<^sup># tf) (branch\<^sup># tf) (body\<^sup># tf) (return\<^sup># tf)
     (\<lambda>ci. snd o enter\<^sup># tf ci) (event\<^sup># tf)
     (\<lambda>ci d. d) (\<lambda>ci dc de. dc)
     (\<lambda>ci dcM de. combine\<^sup># gs (ci_dst ci) dcM de)"

lemma local_spec_step_apply_tf:
  "local_spec_step (skip\<^sup># tf) (assign\<^sup># tf) (special\<^sup># tf) (branch\<^sup># tf) (return\<^sup># tf)
     (event\<^sup># tf) a
     = apply_tf tf a"
  by (cases a) simp_all

lemma dg_spec_step_base_for:
  "dg_spec_step (base_dg_spec_for gs tf) a = local_transfer (apply_tf tf a)"
  by (simp add: base_dg_spec_for_def dg_spec_step_local_dg_spec local_spec_step_apply_tf)

theorem base_dg_spec_for_sound:
  assumes tf_sound: "sound_transfer_for gs tf"
  shows "sound_dg_spec (base_dg_spec_for gs tf) (\<lambda>d g. \<lbrakk>d\<rbrakk>) gs"
  unfolding base_dg_spec_for_def
proof (rule sound_local_dg_spec.local_spec_sound, unfold_locales, goal_cases)
  case 1
  then show ?case by (meson gamma_state_mono)
next
  case 2
  then show ?case
    by (simp add: local_spec_step_apply_tf
        sound_transfer_for.edge_collect_apply_tf_sound_for[OF tf_sound])
next
  case 3
  then show ?case
    by (simp add: call_enter_CallEdge
        sound_transfer_for.tf_sound_enter_entry_for[OF tf_sound])
next
  case 4
  then show ?case by (simp add: combine_collect_sound)
qed

subsection \<open>Transporting soundness through the reachability lift\<close>

text \<open>
  A pure transfer's soundness fact carries over the \<^const>\<open>transfer_lift\<close>
  wrapper by one case split: \<^const>\<open>Bot\<close>'s concretization is empty, and a
  \<^const>\<open>normalize_lift\<close> collapse to \<^const>\<open>Bot\<close> only ever fires when
  \<open>empty_pred\<close> holds, whose concretization is empty by assumption.
\<close>

lemma transfer_lift_sound_collect:
  assumes step: "\<And>\<sigma>. C \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>f \<sigma>\<rbrakk>"
    and Cempty: "C {} = {}"
    and empty_pred_sound: "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
  shows "C (gamma_state_lift d) \<subseteq> gamma_state_lift (transfer_lift empty_pred f d)"
proof (cases d)
  case Bot
  then show ?thesis by (simp add: Cempty)
next
  case (Lifted \<sigma>)
  have "C \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>f \<sigma>\<rbrakk>" by (rule step)
  then show ?thesis
    using Lifted empty_pred_sound[of "f \<sigma>"] by (auto simp: normalize_lift_def)
qed

lemma transfer_lift_sound_mem:
  assumes step: "\<And>\<sigma>. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> h s \<in> \<lbrakk>f \<sigma>\<rbrakk>"
    and empty_pred_sound: "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
    and s: "s \<in> gamma_state_lift d"
  shows "h s \<in> gamma_state_lift (transfer_lift empty_pred f d)"
proof (cases d)
  case Bot
  then show ?thesis using s by simp
next
  case (Lifted \<sigma>)
  with s have "s \<in> \<lbrakk>\<sigma>\<rbrakk>" by simp
  then have hs: "h s \<in> \<lbrakk>f \<sigma>\<rbrakk>" by (rule step)
  then have "\<not> empty_pred (f \<sigma>)" using empty_pred_sound by auto
  with Lifted hs show ?thesis by simp
qed

lemma transfer_lift2_sound_mem:
  assumes step: "\<And>\<sigma>1 \<sigma>2. s \<in> \<lbrakk>\<sigma>1\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>2\<rbrakk> \<Longrightarrow> h s t \<in> \<lbrakk>f \<sigma>1 \<sigma>2\<rbrakk>"
    and empty_pred_sound: "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
    and s: "s \<in> gamma_state_lift d1"
    and t: "t \<in> gamma_state_lift d2"
  shows "h s t \<in> gamma_state_lift (transfer_lift2 empty_pred f d1 d2)"
proof (cases d1)
  case Bot
  then show ?thesis using s by simp
next
  case (Lifted \<sigma>1)
  show ?thesis
  proof (cases d2)
    case Bot
    then show ?thesis using t by simp
  next
    case (Lifted \<sigma>2)
    with \<open>d1 = Lifted \<sigma>1\<close> s t have "s \<in> \<lbrakk>\<sigma>1\<rbrakk>" "t \<in> \<lbrakk>\<sigma>2\<rbrakk>" by simp_all
    then have hst: "h s t \<in> \<lbrakk>f \<sigma>1 \<sigma>2\<rbrakk>" by (rule step)
    then have "\<not> empty_pred (f \<sigma>1 \<sigma>2)" using empty_pred_sound by auto
    with \<open>d1 = Lifted \<sigma>1\<close> Lifted hst show ?thesis by simp
  qed
qed

subsection \<open>The reachability-lifted construction\<close>

definition base_dg_spec_for_lifted ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a abs_state \<Rightarrow> bool)
   \<Rightarrow> 'a::sound_domain domain_transfer
   \<Rightarrow> ('x,'k,'a abs_state lifted,'g::bounded_semilattice_sup_bot) dg_spec"
where
  "base_dg_spec_for_lifted gs empty_pred tf = local_dg_spec
     (transfer_lift empty_pred (skip\<^sup># tf))
     (\<lambda>x e. transfer_lift empty_pred (assign\<^sup># tf x e))
     (\<lambda>sc x. transfer_lift empty_pred (special\<^sup># tf sc x))
     (\<lambda>b pol. transfer_lift empty_pred (branch\<^sup># tf b pol))
     (\<lambda>p. transfer_lift empty_pred (body\<^sup># tf p))
     (\<lambda>e p. transfer_lift empty_pred (return\<^sup># tf e p))
     (\<lambda>ci. transfer_lift empty_pred (snd o enter\<^sup># tf ci))
     (\<lambda>ev. transfer_lift empty_pred (event\<^sup># tf ev))
     (\<lambda>ci d. d) (\<lambda>ci dc de. dc)
     (\<lambda>ci dcM de. transfer_lift2 empty_pred (combine\<^sup># gs (ci_dst ci)) dcM de)"

lemma local_spec_step_transfer_lift_apply_tf:
  "local_spec_step (transfer_lift empty_pred (skip\<^sup># tf))
     (\<lambda>x e. transfer_lift empty_pred (assign\<^sup># tf x e))
     (\<lambda>sc x. transfer_lift empty_pred (special\<^sup># tf sc x))
     (\<lambda>b pol. transfer_lift empty_pred (branch\<^sup># tf b pol))
     (\<lambda>e p. transfer_lift empty_pred (return\<^sup># tf e p))
     (\<lambda>ev. transfer_lift empty_pred (event\<^sup># tf ev)) a
     = transfer_lift empty_pred (apply_tf tf a)"
  by (cases a) simp_all

lemma dg_spec_step_base_for_lifted:
  "dg_spec_step (base_dg_spec_for_lifted gs empty_pred tf) a
     = local_transfer (transfer_lift empty_pred (apply_tf tf a))"
  by (simp add: base_dg_spec_for_lifted_def dg_spec_step_local_dg_spec
      local_spec_step_transfer_lift_apply_tf)

lemma dgs_enter_base_for_lifted:
  "dgs_enter (base_dg_spec_for_lifted gs empty_pred tf) ci
     = local_transfer (transfer_lift empty_pred (snd o enter\<^sup># tf ci))"
  by (simp add: base_dg_spec_for_lifted_def)

text \<open>The caller half of \<open>enter\<close> and the env stage are both identities, so the
  whole return pipeline is the return assignment applied to the raw call-site
  value and the callee exit.\<close>

lemma dg_spec_combine_transfer_base_for_lifted:
  "dg_spec_combine_transfer (base_dg_spec_for_lifted gs empty_pred tf) ci
     = local_combine_transfer
         (\<lambda>dc de. transfer_lift2 empty_pred (combine\<^sup># gs (ci_dst ci)) dc de)"
  by (simp add: base_dg_spec_for_lifted_def dg_spec_combine_transfer_local_dg_spec)
subsection \<open>Packaging correspondence\<close>

text \<open>
  Generic executable/mathematical commute for \<^const>\<open>transfer_lift\<close>/
  \<^const>\<open>transfer_lift2\<close> themselves, independent of any executable state
  representation: this is the one fact an executable Base mirror needs per
  field, proved once here rather than once per domain.
\<close>

lemma transfer_lift_commute:
  assumes commute: "\<And>s. phi (f s) = F (phi s)"
    and exact: "\<And>s. empty_pred s = empty_pred' (phi s)"
  shows "map_lift phi (transfer_lift empty_pred f d) = transfer_lift empty_pred' F (map_lift phi d)"
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def commute exact)

lemma transfer_lift2_commute:
  assumes commute: "\<And>s t. phi (f s t) = F (phi s) (phi t)"
    and exact: "\<And>s. empty_pred s = empty_pred' (phi s)"
  shows "map_lift phi (transfer_lift2 empty_pred f d1 d2) =
           transfer_lift2 empty_pred' F (map_lift phi d1) (map_lift phi d2)"
  by (cases d1; cases d2) (simp_all add: transfer_lift2_def normalize_lift_def commute exact)

subsection \<open>Soundness of the lifted construction\<close>

text \<open>
  The meaning of a Base-style equation never depends on the global slot:
  nothing in \<^const>\<open>base_dg_spec_for_lifted\<close> ever publishes to or reads
  from it, so \<open>gamma_dg_base\<close> ignores its global argument entirely and the
  \<^const>\<open>sound_local_dg_spec\<close> obligations are the transported pure facts.
\<close>

definition gamma_dg_base ::
  "'a::sound_domain abs_state lifted \<Rightarrow> 'g::bounded_semilattice_sup_bot \<Rightarrow> store set"
where
  "gamma_dg_base d g = gamma_state_lift d"

theorem base_dg_spec_sound:
  assumes tf_sound: "sound_transfer_for gs tf"
    and empty_pred_sound: "\<And>sigma. empty_pred sigma \<Longrightarrow> \<lbrakk>sigma\<rbrakk> = {}"
  shows "sound_dg_spec (base_dg_spec_for_lifted gs empty_pred tf) gamma_dg_base gs"
proof -
  have geq: "gamma_dg_base = (\<lambda>d g. gamma_state_lift d)"
    by (simp add: fun_eq_iff gamma_dg_base_def)
  show ?thesis
    unfolding base_dg_spec_for_lifted_def geq
  proof (rule sound_local_dg_spec.local_spec_sound, unfold_locales, goal_cases)
    case 1
    then show ?case by (meson gamma_lift_mono gamma_state_mono)
  next
    case (2 a d)
    show ?case
      by (simp add: local_spec_step_transfer_lift_apply_tf)
         (rule transfer_lift_sound_collect
            [OF sound_transfer_for.edge_collect_apply_tf_sound_for[OF tf_sound]
                edge_collect_empty_set empty_pred_sound])
  next
    case (3 s d ci)
    show ?case
    proof (rule transfer_lift_sound_mem
          [where h = "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci))"])
      show "\<And>\<sigma>. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
          call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
            \<in> \<lbrakk>(snd o enter\<^sup># tf ci) \<sigma>\<rbrakk>"
        by (simp add: call_enter_CallEdge
            sound_transfer_for.tf_sound_enter_entry_for[OF tf_sound])
      show "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}" by (rule empty_pred_sound)
      show "s \<in> gamma_state_lift d" by (rule 3)
    qed
  next
    case (4 s dc t de ci)
    show ?case
    proof (rule transfer_lift2_sound_mem[where h = "combine_collect gs (ci_dst ci)"])
      show "\<And>\<sigma>1 \<sigma>2. s \<in> \<lbrakk>\<sigma>1\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>2\<rbrakk> \<Longrightarrow>
          combine_collect gs (ci_dst ci) s t \<in> \<lbrakk>combine\<^sup># gs (ci_dst ci) \<sigma>1 \<sigma>2\<rbrakk>"
        by (rule combine_collect_sound)
      show "\<And>\<sigma>. empty_pred \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}" by (rule empty_pred_sound)
      show "s \<in> gamma_state_lift dc" by (rule 4(1))
      show "t \<in> gamma_state_lift de" by (rule 4(2))
    qed
  qed
qed

end

