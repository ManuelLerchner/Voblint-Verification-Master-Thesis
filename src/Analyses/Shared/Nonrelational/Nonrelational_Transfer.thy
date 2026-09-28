theory Nonrelational_Transfer
  imports
    Nonrelational_Ops
    "Voblint_Framework.DG_Local_State_Spec"
    "Voblint_Framework.Check_Answer"
    "Voblint_VIMP.VIMP_Globals"
begin

section \<open>What each kind of CFG edge does to one abstract value per variable\<close>

text \<open>
  A non-relational domain gives every variable one abstract value. Say what an
  expression evaluates to, what the whole-value element is, what \<open>Min\<close>/\<open>Max\<close> do,
  and how a guard refines its operands, and every edge operation is already
  fixed: an assignment overwrites its target with the evaluated right-hand side, a
  return writes the same into the return variable, a guard runs the backward
  branch the refinement operations determine, procedure entry resets the callee
  frame to the whole-value element and binds the formals, and skip,
  procedure-body entry and check observation leave the store alone.

  \<open>sound_nonrelational_ops\<close> is the certificate for one \<^type>\<open>nonrelational_ops\<close>
  bundle: the special operations are sound, the refinement operations form a
  reductive backward domain over the bundle's evaluator, and the queries are
  sound checks over the same evaluator. From it this theory states every edge
  operation once and proves each sound --- a concrete store described by the
  input is still described by the output --- ending in the transfer contract the
  analysis framework asks a domain for. \<open>mono_nonrelational_ops\<close> adds
  monotonicity for a bundle whose evaluator, special operations and refinement
  are monotone. A domain proves its capability certificates, interprets one of
  the two locales once at its bundle, and names the results; it proves nothing
  here again.

  \<open>tf_abs\<close> is the per-edge dispatcher these operations add up to, and
  \<open>tf_abs_eq_generic\<close> identifies it with \<^const>\<open>generic_tf_abs\<close> at the derived
  branch, which is what lets \<open>tf_st_for_commute\<close> inherit the executable mirror's
  commutation instead of restating it.
\<close>

locale sound_nonrelational_ops =
  sound_special_ops "n_special ops" "n_aval ops"
  + backward: backward_domain_reductive "r_intersect (n_refine ops)" "n_aval ops"
      "r_tobool (n_refine ops)" "r_inv_less (n_refine ops)" "r_inv_eq (n_refine ops)"
      "r_inv_plus (n_refine ops)" "r_inv_minus (n_refine ops)" "r_inv_times (n_refine ops)"
  + check: abstract_check_domain "q_less (n_query ops)" "q_eq (n_query ops)" gamma_state
      "n_aval ops"
  for ops :: "'a::numeric_domain nonrelational_ops" +
  assumes top_eq: "n_top ops = top"
begin

text \<open>The guard is the branch the refinement operations derive.\<close>

abbreviation br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "br \<equiv> backward.branch"

lemma br_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = pol \<Longrightarrow> s \<in> \<lbrakk>br b pol \<sigma>\<rbrakk>"
  by (rule backward.branch_sound)

text \<open>The whole-value element is the class \<^const>\<open>top\<close>, so its concretization is
  everything by \<open>gamma_top\<close> rather than by an assumption of its own.\<close>

lemma top_gamma: "\<gamma> (n_top ops) = UNIV"
  by (simp add: top_eq)

subsection \<open>Assignment, return, and the operations that do nothing\<close>

definition assign :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "assign x a \<sigma> = \<sigma>(x := n_aval ops a \<sigma>)"

definition skip :: "'a abs_state \<Rightarrow> 'a abs_state" where
  "skip \<sigma> = \<sigma>"

definition body :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "body p \<sigma> = \<sigma>"

text \<open>A check observes its condition but never refines the store --- narrowing a
  state against a checked condition is \<open>abstract_check_domain\<close>'s job --- so
  \<open>event\<close> is the identity like \<open>skip\<close> and \<open>body\<close>.\<close>

definition event :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "event evt \<sigma> = \<sigma>"

definition ret :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "ret e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> assign ret_var a \<sigma>)"

lemma assign_sound:
  assumes \<G>: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(x := \<lbrakk>a\<rbrakk>\<^sub>e s) \<in> \<lbrakk>assign x a \<sigma>\<rbrakk>"
  unfolding assign_def
  using gamma_stateD[OF \<G>] \<G> by blast

lemma skip_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip \<sigma>\<rbrakk>"
  by (simp add: skip_def)

lemma body_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body p \<sigma>\<rbrakk>"
  by (simp add: body_def)

lemma event_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event evt \<sigma>\<rbrakk>"
  by (simp add: event_def)

lemma ret_sound:
  assumes \<G>: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> \<lbrakk>a\<rbrakk>\<^sub>e s)) \<in> \<lbrakk>ret e p \<sigma>\<rbrakk>"
  using assign_sound[OF \<G>] \<G> by (cases e) (simp_all add: ret_def)


subsection \<open>Classifier-parametric procedure entry\<close>

text \<open>
  Entry is the only operation that consults a classifier, inside
  \<^const>\<open>enter_frame\<close>: assignment, guard and return never do, so everything above
  is classifier-free and only these three constants take one.
\<close>

definition enter_frame_for :: "(vname \<Rightarrow> bool) \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "enter_frame_for \<G> = enter_frame \<G> (n_top ops)"

definition enter_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "enter_for \<G> = enter_binding \<G> (n_top ops) (n_aval ops)"

definition enter_ci_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "enter_ci_for \<G> ci = enter_for \<G> (ci_formals ci) (ci_args ci)"

lemma enter_for_sound:
  assumes \<G>: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_for cls xs es \<sigma>\<rbrakk>"
  unfolding enter_for_def enter_binding_concrete[symmetric]
proof (rule enter_binding_sound[OF \<G> top_gamma])
  fix e
  show "\<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (n_aval ops e \<sigma>)"
    using gamma_stateD[OF \<G>] by blast
qed

lemma enter_ci_for_sound:
  assumes \<G>: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals (ci_formals ci) (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) (ci_args ci)) (enter_state cls s)
           \<in> \<lbrakk>enter_ci_for cls ci \<sigma>\<rbrakk>"
  using enter_for_sound[OF \<G>, of \<open>ci_formals ci\<close> \<open>ci_args ci\<close>]
  by (simp add: enter_ci_for_def)


subsection \<open>The transfer contract, and the per-edge dispatcher\<close>

text \<open>The eight operations discharge the framework's contract in one
  \<open>unfold_locales\<close>: the call boundary the contract fixes is the structural one,
  so only the per-edge operations and the callee entry are the domain's own.\<close>

lemma is_sound_nonrelational_transfer:
  "sound_nonrelational_transfer \<G> skip assign special_transfer br body ret (enter_ci_for \<G>) event"
  by unfold_locales
     (simp_all add: assign_sound special_transfer_sound br_sound skip_sound body_sound
        ret_sound enter_ci_for_sound event_sound)

text \<open>The per-edge dispatcher. The executable mirror a domain runs dispatches on
  the action, so the readback equations relating the two are stated at this shape
  rather than one lemma per operation.\<close>

definition tf_abs :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "tf_abs = local_spec_step skip assign special_transfer br body ret event"

lemma tf_abs_simps [simp]:
  "tf_abs EA_Nop = skip"
  "tf_abs (EA_Assign x e) = assign x e"
  "tf_abs (EA_Special sc y) = special_transfer sc y"
  "tf_abs (EA_Assume b) = br b True"
  "tf_abs (EA_AssumeNot b) = br b False"
  "tf_abs (EA_Body p) = body p"
  "tf_abs (EA_Ret eo p) = ret eo p"
  "tf_abs (EA_Check l c) = event (Check_Event l c)"
  by (simp_all add: tf_abs_def)

text \<open>The bundle an executable mirror unfolds against. \<^const>\<open>tf_abs\<close> itself is
  not in it: \<open>tf_abs_simps\<close> is already \<open>[simp]\<close>, so a proof reaches the operation
  the action selects without naming the dispatcher.\<close>

lemmas op_defs =
  assign_def skip_def body_def event_def ret_def
  enter_frame_for_def enter_for_def enter_ci_for_def

subsection \<open>Agreement with the executable mirror\<close>

text \<open>
  Each operation above is the one the bundle determines --- \<open>Nondet_Int\<close>'s
  \<^const>\<open>top\<close> is \<open>n_top ops\<close> by \<open>top_eq\<close>, and every other case is definitional ---
  so this domain's dispatcher is \<^const>\<open>generic_tf_abs\<close> at its own bundle and
  branch. That identification is the whole content: the executable mirror's
  commutation is already proved once against \<^const>\<open>generic_tf_abs\<close>.
\<close>

lemma tf_abs_eq_generic: "tf_abs = generic_tf_abs ops br"
proof (rule ext, rule ext)
  fix a :: edge_action and \<sigma> :: "'a abs_state"
  show "tf_abs a \<sigma> = generic_tf_abs ops br a \<sigma>"
    by (cases a)
       (simp_all add: op_defs top_eq split: special_call.splits option.splits)
qed

text \<open>
  The derived guard filter is the backward domain's executable branch, so it
  commutes with the abstract guard on every live store, and the whole
  executable step with it.
\<close>

lemma n_bfilter_eq: "n_bfilter ops = backward.branch_st"
  using backward.branch_st_with_ops by simp

theorem tf_st_for_commute:
  assumes "live_resolved_st_q \<G> s"
  shows
    "fun_of_resolved_st_q_for \<G> (generic_tf_st_for ops \<G> a s) =
     tf_abs a (fun_of_resolved_st_q_for \<G> s)"
  unfolding tf_abs_eq_generic
  by (rule generic_tf_st_for_commute)
     (simp add: n_bfilter_eq backward.branch_st_commute[OF assms])

end

section \<open>Monotone bundles\<close>

text \<open>
  Monotonicity is a separate certificate: the transfer contract asks only for
  soundness, and a bundle whose evaluator or refinement is not monotone (Int's
  fixpoint refinement) is still a sound one. A monotone bundle additionally has
  monotone special operations and a monotone backward domain, and then every
  derived operation is monotone.
\<close>

locale mono_nonrelational_ops = sound_nonrelational_ops ops
  + mono_special_ops "n_special ops" "n_aval ops"
  + backward: backward_domain_mono "r_intersect (n_refine ops)" "n_aval ops"
      "r_tobool (n_refine ops)" "r_inv_less (n_refine ops)" "r_inv_eq (n_refine ops)"
      "r_inv_plus (n_refine ops)" "r_inv_minus (n_refine ops)" "r_inv_times (n_refine ops)"
  for ops :: "'a::numeric_domain nonrelational_ops"
begin

lemma br_mono: "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> br b pol \<sigma>1 \<le> br b pol \<sigma>2"
  by (rule backward.branch_mono)

lemma assign_mono: "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> assign x a \<sigma>1 \<le> assign x a \<sigma>2"
  unfolding assign_def by (simp add: aval_abs_mono le_funD le_funI)

lemma skip_mono: "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> skip \<sigma>1 \<le> skip \<sigma>2"
  by (simp add: skip_def)

lemma body_mono: "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> body p \<sigma>1 \<le> body p \<sigma>2"
  by (simp add: body_def)

lemma event_mono: "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> event evt \<sigma>1 \<le> event evt \<sigma>2"
  by (simp add: event_def)

lemma ret_mono: "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> ret e p \<sigma>1 \<le> ret e p \<sigma>2"
  by (cases e) (simp_all add: ret_def assign_mono)

lemma enter_for_mono:
  assumes "\<sigma>1 \<le> \<sigma>2"
  shows "enter_for \<G> xs es \<sigma>1 \<le> enter_for \<G> xs es \<sigma>2"
  unfolding enter_for_def
  by (rule enter_binding_mono[OF assms]) (rule aval_abs_mono[OF assms])

end

subsection \<open>Certifying a bundle from its capability certificates\<close>

lemma sound_nonrelational_opsI:
  assumes "sound_special_ops (n_special ops) (n_aval ops)"
    and "backward_domain_reductive (r_intersect (n_refine ops)) (n_aval ops)
           (r_tobool (n_refine ops)) (r_inv_less (n_refine ops)) (r_inv_eq (n_refine ops))
           (r_inv_plus (n_refine ops)) (r_inv_minus (n_refine ops)) (r_inv_times (n_refine ops))"
    and "abstract_check_domain (q_less (n_query ops)) (q_eq (n_query ops)) gamma_state (n_aval ops)"
    and "n_top ops = top"
  shows "sound_nonrelational_ops ops"
  by (intro sound_nonrelational_ops.intro sound_nonrelational_ops_axioms.intro assms)

lemma mono_nonrelational_opsI:
  assumes special: "mono_special_ops (n_special ops) (n_aval ops)"
    and backward: "backward_domain_mono (r_intersect (n_refine ops)) (n_aval ops)
           (r_tobool (n_refine ops)) (r_inv_less (n_refine ops)) (r_inv_eq (n_refine ops))
           (r_inv_plus (n_refine ops)) (r_inv_minus (n_refine ops)) (r_inv_times (n_refine ops))"
    and "abstract_check_domain (q_less (n_query ops)) (q_eq (n_query ops)) gamma_state (n_aval ops)"
    and "n_top ops = top"
  shows "mono_nonrelational_ops ops"
proof -
  interpret mono_special_ops "n_special ops" "n_aval ops" by (rule special)
  interpret backward_domain_mono "r_intersect (n_refine ops)" "n_aval ops"
      "r_tobool (n_refine ops)" "r_inv_less (n_refine ops)" "r_inv_eq (n_refine ops)"
      "r_inv_plus (n_refine ops)" "r_inv_minus (n_refine ops)" "r_inv_times (n_refine ops)"
    by (rule backward)
  show ?thesis
    by (intro mono_nonrelational_ops.intro sound_nonrelational_opsI assms)
       unfold_locales
qed

end
