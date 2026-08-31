theory Placement_Policy
  imports "Voblint_Core.DG_LTR_Sound"
begin

section \<open>Routing by a non-exclusive covering\<close>

text \<open>
  The framework routes a name to exactly one of the local and global components, by the
  classifier \<open>gs\<close>. This theory keeps the alternative the alignment register records: a
  \<^emph>\<open>covering\<close> by two predicates \<open>keep_local\<close>/\<open>publish_side\<close> that may overlap, every
  step joined through the raw lattice join, and the concretization \<open>gamma_join d g = [[d Sup g]]\<close>
  that never inspects the split. It is what the two Placement examples interpret; nothing
  in the analysis pipeline uses it.
\<close>

subsection \<open>Projecting a component\<close>

definition project_component ::
  "('loc \<Rightarrow> bool) \<Rightarrow> ('loc \<Rightarrow> 'a::bot) \<Rightarrow> 'loc \<Rightarrow> 'a" where
  "project_component placed state = (\<lambda>loc. if placed loc then state loc else bot)"

definition classic_split_keep_local :: "(vname \<Rightarrow> bool) \<Rightarrow> vname \<Rightarrow> bool" where
  "classic_split_keep_local storage loc = (\<not> storage loc)"

definition classic_split_publish_side :: "(vname \<Rightarrow> bool) \<Rightarrow> vname \<Rightarrow> bool" where
  "classic_split_publish_side storage loc = storage loc"

subsection \<open>The placed unit step and specification\<close>

definition unit_step_placed ::
  "(vname => bool) => (vname => bool) =>
   ('a::bounded_semilattice_sup_bot abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_step_placed keep_local publish_side f d g =
     (let res = f (d \<squnion> g) in
      (project_component publish_side res, project_component keep_local res))"


definition unit_combine_step_env_placed ::
  "(vname => bool) => (vname => bool) => (vname => bool) => call_info =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state =>
   'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_env_placed gs keep_local publish_side ci dc de g =
     (let res = combine_env gs (dc \<squnion> g) (de \<squnion> g) in
      (project_component publish_side res, project_component keep_local res))"


definition unit_combine_step_assign_placed ::
  "(vname => bool) => (vname => bool) => call_info =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state =>
   'a abs_state \<times> 'a abs_state => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_assign_placed keep_local publish_side ci de g merged =
     (let res = combine_assign (ci_dst ci) ((de \<squnion> g) ret_var)
         (fst merged \<squnion> snd merged)
      in (project_component publish_side res, project_component keep_local res))"


definition unit_dg_spec_placed ::
  "(vname => bool) => (vname => bool) => (vname => bool) =>
   'a::sound_domain domain_transfer => ('a abs_state, 'a abs_state) dg_spec"
where
  "unit_dg_spec_placed gs keep_local publish_side tf = \<lparr>
    dgs_skip       = unit_step_placed keep_local publish_side (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_placed keep_local publish_side
      (apply_tf tf (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_placed keep_local publish_side
      (apply_tf tf (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_placed keep_local publish_side
      (branch\<^sup># tf b pol)),
    dgs_body       = (\<lambda>p. unit_step_placed keep_local publish_side
      (body\<^sup># tf p)),
    dgs_return     = (\<lambda>e p. unit_step_placed keep_local publish_side
      (return\<^sup># tf e p)),
    dgs_enter      = (\<lambda>ci. unit_step_placed keep_local publish_side
      (snd o enter\<^sup># tf ci)),
    dgs_event      = (\<lambda>ev. unit_step_placed keep_local publish_side
      (event\<^sup># tf ev)),
    dgs_caller_cont = (\<lambda>_ d _. d),
    dgs_combine_env = unit_combine_step_env_placed gs keep_local publish_side,
    dgs_combine_assign = unit_combine_step_assign_placed keep_local publish_side
  \<rparr>"
lemma dg_spec_step_unit_placed:
  "dg_spec_step (unit_dg_spec_placed gs keep_local publish_side tf) a =
    unit_step_placed keep_local publish_side (apply_tf tf a)"
  unfolding unit_dg_spec_placed_def
  by (cases a) simp_all

lemma dgs_enter_unit_dg_spec_placed:
  "dgs_enter (unit_dg_spec_placed gs keep_local publish_side tf) ci =
    unit_step_placed keep_local publish_side (snd o enter\<^sup># tf ci)"
  unfolding unit_dg_spec_placed_def
  by simp

subsection \<open>The homogeneous analysis under an independent placement policy\<close>

text \<open>
  \<open>unit_dg_spec_placed\<close> packages every D/G step through the raw lattice join
  (\<open>d \<squnion> g\<close>) rather than \<^const>\<open>combine_env\<close>'s ownership routing: with a
  non-exclusive covering, a name can legitimately be tracked by both
  \<open>keep_local\<close> and \<open>publish_side\<close>, so there is no single owning component to
  route to, and the join is the only combinator that stays sound for every
  covering. \<open>gamma_join\<close> is that join-based target: \<open>gamma_join d g = \<lbrakk>d \<squnion>
  g\<rbrakk>\<close> never inspects the split, so any split whose two projections join back
  to the pre-split value is just as sound as any other. \<^const>\<open>unit_dg_spec_placed\<close>
  exposes that split as two independent predicates, \<open>keep_local\<close>/\<open>publish_side\<close>;
  the only requirement is that every location is covered by at least one of them.
  Unlike \<open>wf_split\<close>, covering does not demand exclusivity: a location may
  sit in both, which is exactly the shape a privatized global needs (kept
  precisely in D for the current activation and also published to G for other
  activations). This is a genuinely different target from \<open>gamma_unit\<close>: the
  exclusive, storage-derived split that \<^const>\<open>unit_dg_spec_for\<close> uses can route
  by ownership because it never has an overlapping name to arbitrate.
\<close>

definition gamma_join ::
  "'a::sound_domain abs_state \<Rightarrow> 'a abs_state \<Rightarrow> store set"
where
  "gamma_join d g = \<lbrakk>d \<squnion> g\<rbrakk>"

lemma gamma_join_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_join d g \<subseteq> gamma_join d' g'"
  unfolding gamma_join_def
  by (rule gamma_state_mono) (rule sup_mono[OF assms])

lemma gamma_joinD [dest]: "s \<in> gamma_join d g \<Longrightarrow> s \<in> \<lbrakk>d \<squnion> g\<rbrakk>"
  unfolding gamma_join_def by simp

text \<open>\<open>gamma_unit\<close> refines \<open>gamma_join\<close>: routing to the owning component is always
  at most as permissive as joining both, since the routed value is one of the two
  join operands. The two targets are genuinely different (an untouched name still
  loses precision under \<open>gamma_join\<close> the way the issue this file's \<open>unit_dg_spec_for\<close>
  chain fixes described), so this is a one-way refinement, not an equivalence --
  \<open>gamma_join\<close> stays the sound target for \<^const>\<open>unit_dg_spec_placed\<close>'s non-exclusive
  covering, where no single component owns every name.\<close>
lemma combine_env_le_sup: "combine_env gs sc se \<le> sc \<squnion> se"
  by (auto simp: combine_env_def le_fun_def)

lemma gamma_unit_subset_gamma_join: "gamma_unit gs d g \<subseteq> gamma_join d g"
  unfolding gamma_unit_def gamma_join_def
  by (rule gamma_state_mono[OF combine_env_le_sup])

lemma project_component_cover_sup:
  fixes sigma :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes "\<forall>x. p1 x \<or> p2 x"
  shows "project_component p1 sigma \<squnion> project_component p2 sigma = sigma"
  unfolding project_component_def using assms by (auto simp: sup_fun_def fun_eq_iff)

lemma project_component_cover_sup2:
  fixes sigma :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes "\<forall>x. p1 x \<or> p2 x"
  shows "project_component p2 sigma \<squnion> project_component p1 sigma = sigma"
  using project_component_cover_sup[OF assms] by (simp add: sup_commute)

lemma dgs_combine_unit_dg_spec_placed:
  assumes cover: "\<forall>x. publish_side x \<or> keep_local x"
  shows "dgs_combine (unit_dg_spec_placed gs keep_local publish_side tf) dst dc de g =
     (let res = combine\<^sup># gs (ci_dst dst) (dc \<squnion> g) (de \<squnion> g)
      in (project_component publish_side res, project_component keep_local res))"
proof -
  have env_join:
    "fst (unit_combine_step_env_placed gs keep_local publish_side dst dc de g) \<squnion>
       snd (unit_combine_step_env_placed gs keep_local publish_side dst dc de g) =
     combine_env gs (dc \<squnion> g) (de \<squnion> g)"
    unfolding unit_combine_step_env_placed_def
    by (simp add: Let_def project_component_cover_sup[OF cover])
  show ?thesis
    unfolding dgs_combine_def unit_dg_spec_placed_def
      unit_combine_step_assign_placed_def combine_collect_abs_def Let_def
    by (simp add: env_join project_component_cover_sup[OF cover])
qed

lemma gamma_join_combine_sound_placed:
  assumes cover: "\<forall>x. publish_side x \<or> keep_local x"
    and sc: "s \<in> gamma_join dc g" and tc: "t \<in> gamma_join de g"
  shows "combine_collect gs (ci_dst dst) s t \<in>
           (case dgs_combine (unit_dg_spec_placed gs keep_local publish_side tf) dst dc de g of (g', d') \<Rightarrow> gamma_join d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc \<squnion> g\<rbrakk>" using gamma_joinD[OF sc] .
  have tc': "t \<in> \<lbrakk>de \<squnion> g\<rbrakk>" using gamma_joinD[OF tc] .
  have "combine_collect gs (ci_dst dst) s t \<in> \<lbrakk>combine\<^sup># gs (ci_dst dst) (dc \<squnion> g) (de \<squnion> g)\<rbrakk>"
    by (rule combine_collect_sound[OF sc' tc'])
  then show ?thesis
    unfolding dgs_combine_unit_dg_spec_placed[OF cover] gamma_join_def
    by (simp add: Let_def project_component_cover_sup2[OF cover])
qed

lemma gamma_join_enter_sound_placed:
  assumes cover: "\<forall>x. publish_side x \<or> keep_local x"
    and sound: "sound_transfer_for gs tf"
    and sc: "s \<in> gamma_join dc g"
  shows "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in>
           (case dgs_enter (unit_dg_spec_placed gs keep_local publish_side tf) ci dc g of (g', d') \<Rightarrow> gamma_join d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc \<squnion> g\<rbrakk>" using gamma_joinD[OF sc] .
  have "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> \<lbrakk>snd (enter\<^sup># tf ci (dc \<squnion> g))\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_entry_for[OF sound sc']
    by (simp add: call_enter_CallEdge)
  then show ?thesis
    unfolding dgs_enter_unit_dg_spec_placed unit_step_placed_def gamma_join_def
    by (simp add: Let_def project_component_cover_sup2[OF cover])
qed

text \<open>The placed generalization for an arbitrary covering placement: covering
  is the only condition \<open>keep_local\<close>/\<open>publish_side\<close> must satisfy.\<close>
theorem sound_dg_spec_unit_placed:
  assumes sound: "sound_transfer_for gs tf"
    and cover: "\<forall>x. publish_side x \<or> keep_local x"
  shows "sound_dg_spec (unit_dg_spec_placed gs keep_local publish_side tf) gamma_join gs"
  apply unfold_locales
  subgoal for d d' g g'
    by (rule gamma_join_mono)
  subgoal for a d g
    unfolding gamma_join_def dg_spec_step_unit_placed unit_step_placed_def
    using sound_transfer_for.edge_collect_apply_tf_sound_for[OF sound, where a = a]
      sound_transfer_for.edge_collect_check_sound_for[OF sound, where \<sigma> = "d \<squnion> g"]
    by (auto simp add: Let_def project_component_cover_sup2[OF cover])
  subgoal premises prems using prems by (simp add: unit_dg_spec_placed_def)
  subgoal premises prems
    by (rule gamma_join_combine_sound_placed[OF cover prems])
  subgoal premises prems
    by (rule gamma_join_enter_sound_placed[OF cover sound prems])
  done

lemma classic_split_cover:
  "\<forall>x. classic_split_publish_side storage x \<or> classic_split_keep_local storage x"
  unfolding classic_split_publish_side_def classic_split_keep_local_def by simp


subsection \<open>The hook route restated over local traces\<close>

locale sound_dg_hooks_ltr =
  sound_dg_hooks gammaDG gs edge_tree combine_tree enter_tree
  for gammaDG :: "'D::bounded_semilattice_sup_bot \<Rightarrow>
      'G::bounded_semilattice_sup_bot \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and edge_tree :: "pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
    and combine_tree :: "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
    and enter_tree :: "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
begin

theorem hook_postfix_collect_sound_ltr:
  assumes pf: "hook_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect gs g S0 v \<subseteq> dg_hook_gamma gammaDG sigma v"
proof (rule ltr_collect_semantic_postfix)
  show "S0 \<subseteq> dg_hook_gamma gammaDG sigma (cfg_entry g)"
  proof -
    have d_le: "s0d \<le> dg_hook_D sigma (cfg_entry g)"
      by (rule hook_postfix_entryD[OF pf])
    have g_le: "s0g \<le> dg_hook_G sigma"
      by (rule hook_postfix_entryG[OF pf])
    have "gammaDG s0d s0g \<subseteq>
        dg_hook_gamma gammaDG sigma (cfg_entry g)"
      unfolding dg_hook_gamma_def
      by (rule gammaDG_mono[OF d_le g_le])
    then show ?thesis using sound0 by blast
  qed
next
  fix u a w s s'
  assume edge: "(u, a, w) \<in> intra g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma u"
    and step: "s' \<in> edge_step a s"
  have "s' \<in> edge_collect a (dg_hook_gamma gammaDG sigma u)"
    using sin step by (auto simp: edge_collect_def)
  then show "s' \<in> dg_hook_gamma gammaDG sigma w"
    by (rule set_mp[OF hook_postfix_edge[OF pf edge]])
next
  fix u dst fs args p cont s
  assume call:
      "(u, CallEdge dst fs args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma u"
  then show "call_enter gs (CallEdge dst fs args) s \<in>
      dg_hook_gamma gammaDG sigma (FunctionEntry p)"
    by (rule hook_postfix_enter[OF pf])
next
  fix caller dst fs args p cont s t
  assume call:
      "(caller, CallEdge dst fs args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
    and tin: "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)"
  then show "combine_collect gs dst s t \<in>
      dg_hook_gamma gammaDG sigma cont"
    by (rule hook_postfix_combine[OF pf])
qed

corollary hook_post_solution_collect_sound_ltr:
  assumes pp:
      "part_post_solution (hook_gen g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_enter:
      "\<And>caller dst fs args p k.
        (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
        \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>caller dst fs args p k.
        (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
        \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect gs g S0 v \<subseteq> dg_hook_gamma gammaDG sigma v"
proof -
  have pf: "hook_postfix g s0d s0g sigma"
    by (rule hook_post_solution_postfix
      [OF pp cover_entry cover_edge cover_enter cover_combine finI finC])
  show ?thesis
    by (rule hook_postfix_collect_sound_ltr[OF pf sound0])
qed

end

end
