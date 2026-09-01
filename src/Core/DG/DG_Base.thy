theory DG_Base
  imports DG_Dead_Code_Lift
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
  \<^const>\<open>combine_env\<close> and \<^const>\<open>enter_frame\<close> already implement; no
  \<^const>\<open>restrict_local_for\<close>, \<^const>\<open>restrict_global_for\<close>, or
  \<^const>\<open>combine_env\<close>-style reconstruction against \<open>'g\<close> occurs anywhere
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
  "base_dg_spec_for_lifted gs empty_pred tf = (|
    dgs_skip       = (\<lambda>d g. (g, transfer_lift empty_pred (skip\<^sup># tf) d)),
    dgs_assign     = (\<lambda>x e d g. (g, transfer_lift empty_pred (assign\<^sup># tf x e) d)),
    dgs_special    = (\<lambda>sc x d g. (g, transfer_lift empty_pred (special\<^sup># tf sc x) d)),
    dgs_branch     = (\<lambda>b pol d g. (g, transfer_lift empty_pred (branch\<^sup># tf b pol) d)),
    dgs_body       = (\<lambda>p d g. (g, transfer_lift empty_pred (body\<^sup># tf p) d)),
    dgs_return     = (\<lambda>e p d g. (g, transfer_lift empty_pred (return\<^sup># tf e p) d)),
    dgs_enter      = (\<lambda>ci d g. (g, transfer_lift empty_pred (snd o enter\<^sup># tf ci) d)),
    dgs_event      = (\<lambda>ev d g. (g, transfer_lift empty_pred (event\<^sup># tf ev) d)),
    dgs_caller_cont    = (\<lambda>ci dc g. dc),
    dgs_combine_env    = (\<lambda>ci dc de g. (g, dc)),
    dgs_combine_assign = (\<lambda>ci de g merged.
      (g, transfer_lift2 empty_pred (combine\<^sup># gs (ci_dst ci)) (snd merged) de))
  |)"

subsection \<open>Basic equations\<close>

text \<open>
  Record-level type sanity: the generic \<^const>\<open>dg_spec_step\<close>/\<^const>\<open>dgs_combine\<close>
  machinery dispatches to \<^const>\<open>transfer_lift\<close>/\<^const>\<open>transfer_lift2\<close> directly on the
  whole-state carrier, with no further reasoning about \<open>gs\<close> beyond what \<open>tf\<close> itself
  already bakes in.
\<close>

lemma dg_spec_step_base_for_lifted:
  "dg_spec_step (base_dg_spec_for_lifted gs empty_pred tf) a d g =
     (g, transfer_lift empty_pred (apply_tf tf a) d)"
  unfolding base_dg_spec_for_lifted_def
  by (cases a) simp_all

lemma dgs_enter_base_for_lifted:
  "dgs_enter (base_dg_spec_for_lifted gs empty_pred tf) ci d g =
     (g, transfer_lift empty_pred (snd o enter\<^sup># tf ci) d)"
  unfolding base_dg_spec_for_lifted_def by simp

text \<open>The caller half of \<open>enter\<close> hands \<open>combine\<close> the raw call-site value, so
  every Base equation below reads exactly as it did before the call/return
  protocol split the two halves apart.\<close>

lemma dgs_caller_cont_base_for_lifted [simp]:
  "dgs_caller_cont (base_dg_spec_for_lifted gs empty_pred tf) ci dc g = dc"
  unfolding base_dg_spec_for_lifted_def by simp

lemma dgs_combine_base_for_lifted:
  "dgs_combine (base_dg_spec_for_lifted gs empty_pred tf) ci dc de g =
     (g, transfer_lift2 empty_pred (combine\<^sup># gs (ci_dst ci)) dc de)"
  unfolding dgs_combine_def base_dg_spec_for_lifted_def by simp

subsection \<open>Bot propagation\<close>

text \<open>
  A dead local unknown dominates every ordinary field before \<open>tf\<close> ever runs --
  \<^const>\<open>transfer_lift\<close>'s own \<^const>\<open>bind_lift\<close> short-circuit, with no
  \<^const>\<open>combine_env\<close> reconstruction step to reason
  about first.
\<close>

lemma dg_spec_step_base_for_lifted_Bot:
  "dg_spec_step (base_dg_spec_for_lifted gs empty_pred tf) a Bot g = (g, Bot)"
  unfolding dg_spec_step_base_for_lifted by simp

lemma dgs_enter_base_for_lifted_Bot:
  "dgs_enter (base_dg_spec_for_lifted gs empty_pred tf) ci Bot g = (g, Bot)"
  unfolding dgs_enter_base_for_lifted by simp

lemma dgs_combine_base_for_lifted_dc_bot:
  "dgs_combine (base_dg_spec_for_lifted gs empty_pred tf) dst Bot de g = (g, Bot)"
  unfolding dgs_combine_base_for_lifted by (cases de) (simp_all add: transfer_lift2_def)

lemma dgs_combine_base_for_lifted_de_bot:
  "dgs_combine (base_dg_spec_for_lifted gs empty_pred tf) dst dc Bot g = (g, Bot)"
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
    and exact: "\<And>s. empty_pred s = empty_pred' (phi s)"
  shows "map_lift phi (transfer_lift empty_pred f d) = transfer_lift empty_pred' F (map_lift phi d)"
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def commute exact)

lemma transfer_lift2_commute:
  assumes commute: "\<And>s t. phi (f s t) = F (phi s) (phi t)"
    and exact: "\<And>s. empty_pred s = empty_pred' (phi s)"
  shows "map_lift phi (transfer_lift2 empty_pred f d1 d2) =
           transfer_lift2 empty_pred' F (map_lift phi d1) (map_lift phi d2)"
  by (cases d1; cases d2) (simp_all add: transfer_lift2_def normalize_lift_def commute exact)

subsection \<open>The unlifted core\<close>

text \<open>
  \<open>base_dg_spec_for\<close> is the same construction with neither reachability
  tracking nor normalization: the raw transfer runs on \<open>'a abs_state\<close>
  directly.  The frozen \<^const>\<open>base_dg_spec_for_lifted\<close> agrees with
  \<open>dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_for gs tf))\<close>
  on every composed operation; only the raw \<open>dgs_combine_env\<close> stage differs
  (the generic lifter's is strict in the callee value, this record's
  passthrough is not), which the composed \<^const>\<open>dgs_combine\<close> erases.
\<close>

definition base_dg_spec_for ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> 'a::sound_domain domain_transfer
   \<Rightarrow> ('a abs_state, 'g::bounded_semilattice_sup_bot) dg_spec"
where
  "base_dg_spec_for gs tf = (|
    dgs_skip       = (\<lambda>d g. (g, skip\<^sup># tf d)),
    dgs_assign     = (\<lambda>x e d g. (g, assign\<^sup># tf x e d)),
    dgs_special    = (\<lambda>sc x d g. (g, special\<^sup># tf sc x d)),
    dgs_branch     = (\<lambda>b pol d g. (g, branch\<^sup># tf b pol d)),
    dgs_body       = (\<lambda>p d g. (g, body\<^sup># tf p d)),
    dgs_return     = (\<lambda>e p d g. (g, return\<^sup># tf e p d)),
    dgs_enter      = (\<lambda>ci d g. (g, snd (enter\<^sup># tf ci d))),
    dgs_event      = (\<lambda>ev d g. (g, event\<^sup># tf ev d)),
    dgs_caller_cont    = (\<lambda>ci dc g. dc),
    dgs_combine_env    = (\<lambda>ci dc de g. (g, dc)),
    dgs_combine_assign = (\<lambda>ci de g merged.
      (g, combine\<^sup># gs (ci_dst ci) (snd merged) de))
  |)"

lemma dg_spec_step_base_for:
  "dg_spec_step (base_dg_spec_for gs tf) a d g = (g, apply_tf tf a d)"
  by (cases a) (simp_all add: base_dg_spec_for_def)

lemma dgs_enter_base_for:
  "dgs_enter (base_dg_spec_for gs tf) ci d g = (g, snd (enter\<^sup># tf ci d))"
  by (simp add: base_dg_spec_for_def)

lemma dgs_caller_cont_base_for [simp]:
  "dgs_caller_cont (base_dg_spec_for gs tf) ci dc g = dc"
  by (simp add: base_dg_spec_for_def)

lemma dgs_combine_base_for:
  "dgs_combine (base_dg_spec_for gs tf) ci dc de g =
     (g, combine\<^sup># gs (ci_dst ci) dc de)"
  by (simp add: dgs_combine_def base_dg_spec_for_def)

subsection \<open>Soundness\<close>

text \<open>
  The meaning of a Base-style Answer/Side pair never depends on \<open>g\<close>: nothing in
  \<^const>\<open>base_dg_spec_for_lifted\<close> ever publishes to or reads from it.
\<close>

definition gamma_dg_base ::
  "'a::sound_domain abs_state lifted \<Rightarrow> 'g::bounded_semilattice_sup_bot \<Rightarrow> store set"
where
  "gamma_dg_base d g = gamma_state_lift d"

text \<open>The unlifted core is sound at the raw whole-state concretization;
  everything else is the functor chain.\<close>

lemma base_dg_spec_for_sound:
  assumes tf_sound: "sound_transfer_for gs tf"
  shows "sound_dg_spec (base_dg_spec_for gs tf)
           (\<lambda>d _. \<lbrakk>d\<rbrakk>) gs"
proof (rule sound_dg_spec.intro)
  show "\<And>d d' g g'. d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> \<lbrakk>d\<rbrakk> \<subseteq> \<lbrakk>d'\<rbrakk>"
    by (rule gamma_state_mono)
  show "\<And>a d g. edge_collect a \<lbrakk>d\<rbrakk> \<subseteq>
      (case dg_spec_step (base_dg_spec_for gs tf) a d g of (g', d') \<Rightarrow> \<lbrakk>d'\<rbrakk>)"
    unfolding dg_spec_step_base_for
    by (simp add: sound_transfer_for.edge_collect_apply_tf_sound_for[OF tf_sound])
  show "\<And>s dc g ci. s \<in> \<lbrakk>dc\<rbrakk> \<Longrightarrow>
      s \<in> \<lbrakk>dgs_caller_cont (base_dg_spec_for gs tf) ci dc g\<rbrakk>"
    by simp
  show "\<And>s dcont g t de ci. s \<in> \<lbrakk>dcont\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>de\<rbrakk> \<Longrightarrow>
      combine_collect gs (ci_dst ci) s t \<in>
        (case dgs_combine (base_dg_spec_for gs tf) ci dcont de g of (g', d') \<Rightarrow> \<lbrakk>d'\<rbrakk>)"
    unfolding dgs_combine_base_for
    by (simp add: combine_collect_sound)
  show "\<And>s dc g ci. s \<in> \<lbrakk>dc\<rbrakk> \<Longrightarrow>
      call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in>
        (case dgs_enter (base_dg_spec_for gs tf) ci dc g of (g', d') \<Rightarrow> \<lbrakk>d'\<rbrakk>)"
    unfolding dgs_enter_base_for
    by (simp add: call_enter_CallEdge
        sound_transfer_for.tf_sound_enter_entry_for[OF tf_sound])
qed

text \<open>The composed-operation agreements between the frozen record and the
  normalized dead-code lift of the unlifted core.\<close>

lemma dg_spec_step_base_lift_agree:
  "dg_spec_step (base_dg_spec_for_lifted gs empty_pred tf) a d g =
   dg_spec_step
     (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_for gs tf))) a d g"
  unfolding dg_spec_step_base_for_lifted
  by (cases d) (simp_all add: dg_spec_step_base_for transfer_lift_def)

lemma dgs_caller_cont_base_lift_agree:
  "dgs_caller_cont (base_dg_spec_for_lifted gs empty_pred tf) ci dc g =
   dgs_caller_cont
     (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_for gs tf))) ci dc g"
  by (cases dc) (simp_all add: base_dg_spec_for_lifted_def)

lemma dgs_combine_base_lift_agree:
  "dgs_combine (base_dg_spec_for_lifted gs empty_pred tf) ci dc de g =
   dgs_combine
     (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_for gs tf))) ci dc de g"
  unfolding dgs_combine_base_for_lifted
  by (cases dc; cases de) (simp_all add: dgs_combine_base_for transfer_lift2_def)

lemma dgs_enter_base_lift_agree:
  "dgs_enter (base_dg_spec_for_lifted gs empty_pred tf) ci dc g =
   dgs_enter
     (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_for gs tf))) ci dc g"
  unfolding dgs_enter_base_for_lifted
  by (cases dc) (simp_all add: dgs_enter_base_for transfer_lift_def)

text \<open>
  No reference to any concrete domain: instantiating \<open>tf\<close> with a domain's own
  \<^const>\<open>sound_transfer_for\<close> interpretation and \<open>empty_pred\<close> with its
  \<^const>\<open>is_empty_state\<close> (via \<open>is_empty_state_gamma_state_empty\<close>) is the entire
  per-domain obligation.
\<close>

theorem base_dg_spec_sound:
  assumes tf_sound: "sound_transfer_for gs tf"
    and empty_pred_sound: "\<And>sigma. empty_pred sigma \<Longrightarrow> \<lbrakk>sigma\<rbrakk> = {}"
  shows "sound_dg_spec (base_dg_spec_for_lifted gs empty_pred tf) gamma_dg_base gs"
proof -
  have norm: "sound_dg_spec
      (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_for gs tf)))
      (lift_gamma (\<lambda>d _. \<lbrakk>d\<rbrakk>)) gs"
    by (rule dead_code_normalize_sound
          [OF dead_code_lift_sound[OF base_dg_spec_for_sound[OF tf_sound]]])
       (simp add: empty_pred_sound)
  have geq: "gamma_dg_base = lift_gamma (\<lambda>d _. \<lbrakk>d\<rbrakk>)"
    by (auto simp: fun_eq_iff gamma_dg_base_def gamma_lift_def lift_gamma_def
        split: lifted.splits)
  show ?thesis
    unfolding geq
    by (rule sound_dg_spec_cong[OF dg_spec_step_base_lift_agree
          dgs_caller_cont_base_lift_agree dgs_combine_base_lift_agree
          dgs_enter_base_lift_agree norm])
qed

end
