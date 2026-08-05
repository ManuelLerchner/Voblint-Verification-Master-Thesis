theory Ghost_Last_Write_Product
  imports Ghost_Last_Write_Domain
begin

section \<open>Product-domain integration: base value component and ghost component\<close>

text \<open>
  Section 6 of \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> asks for a ghost-augmented \<open>dg_spec\<close>
  instance, \<open>'dl = 'a abs_state \<times> 'g_dl\<close>, whose seed step updates both components from the
  same edge.  This theory supplies the generic product construction and its combined-transfer
  soundness theorem, kept independent of any one base domain (\<open>'a::sound_domain\<close> is a type
  variable, not fixed to \<open>sign\<close>) and independent of the \<open>dg_spec\<close>/context-routing machinery: it
  composes with an arbitrary already-sound per-edge base transfer, matching the milestone
  guidance to build "one clean generic product construction... rather than a broad invasive
  migration."  Instantiating this against a concrete domain's own \<open>dg_spec\<close> record (Sign first,
  per the milestone table) is out of scope for this theory; see the accompanying report for
  exactly what remains.
\<close>

subsection \<open>The product step\<close>

text \<open>One edge updates the base component through the caller-supplied \<open>base_tf\<close> and the ghost
  component through \<^const>\<open>ghost_step\<close>, both reading the same \<open>a\<close> and \<open>v\<close> --- the
  pointwise/simultaneous shape section 6 requires, and what makes the joint soundness below
  available without a relational concretization.\<close>

definition product_step ::
  "(edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> edge_action \<Rightarrow> cfg_node
     \<Rightarrow> ('a::sound_domain) abs_state \<times> ghost_lw \<Rightarrow> 'a abs_state \<times> ghost_lw"
where
  "product_step base_tf a v dw = (base_tf a (fst dw), ghost_step a v (snd dw))"

text \<open>Non-interference (replaces old G0, per \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> section 11):
  the base component is exactly what the unmodified base transfer computes, independent of the
  ghost component's own value.  True by construction, not by a separate argument.\<close>
lemma product_step_base_independent_of_ghost:
  "fst (product_step base_tf a v (d, w1)) = fst (product_step base_tf a v (d, w2))"
  by (simp add: product_step_def)

subsection \<open>Combined transfer soundness\<close>

text \<open>Given a per-edge sound base transfer and edge-action functionality, one \<^const>\<open>product_step\<close>
  application preserves soundness of \<^emph>\<open>both\<close> components from the same premises: a store
  admitted by the base component before the step, a writer outcome admitted by the ghost
  component before the step, and the store/edge actually executing the step.  This is the
  combined transfer soundness theorem G-M1 asks for.\<close>

theorem product_step_sound:
  fixes base_tf :: "edge_action \<Rightarrow> ('a::sound_domain) abs_state \<Rightarrow> 'a abs_state"
  assumes base_sound: "\<And>a s s' d. s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> \<lbrakk>base_tf a d\<rbrakk>"
    and fn: "cfg_intra_functional g"
    and e: "(fst (last p), a, v) \<in> intra g"
    and p: "p \<noteq> []"
    and dok: "snd (last p) \<in> \<lbrakk>d\<rbrakk>"
    and wok: "last_writer g x p \<in> gamma_lw_state w x"
    and s': "s' \<in> edge_step a (snd (last p))"
  shows "s' \<in> \<lbrakk>fst (product_step base_tf a v (d, w))\<rbrakk>
           \<and> last_writer g x (p @ [(v, s')]) \<in> gamma_lw_state (snd (product_step base_tf a v (d, w))) x"
  unfolding product_step_def
  using base_sound[OF dok s'] ghost_step_sound[OF fn e p wok] by simp

text \<open>The trace-level counterpart, phrased directly against \<^const>\<open>valid_ltr\<close>'s \<open>intra\<close> rule
  and \<^const>\<open>trace_last_writer\<close>, mirroring \<open>ghost_step_sound_trace\<close>.\<close>

theorem product_step_sound_trace:
  fixes base_tf :: "edge_action \<Rightarrow> ('a::sound_domain) abs_state \<Rightarrow> 'a abs_state"
  assumes base_sound: "\<And>a s s' d. s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> \<lbrakk>base_tf a d\<rbrakk>"
    and fn: "cfg_intra_functional g"
    and t: "t \<in> valid_ltr gs g S"
    and e: "(sink_node t, a, v) \<in> intra g" and s': "s' \<in> edge_step a (sink_store t)"
    and dok: "sink_store t \<in> \<lbrakk>d\<rbrakk>"
    and wok: "trace_last_writer g x t \<in> gamma_lw_state w x"
  shows "s' \<in> \<lbrakk>fst (product_step base_tf a v (d, w))\<rbrakk>
           \<and> trace_last_writer g x (extend t (v, s')) \<in> gamma_lw_state (snd (product_step base_tf a v (d, w))) x"
proof -
  have p: "path t \<noteq> []" using t by (rule valid_ltr_path_nonempty)
  have e': "(fst (last (path t)), a, v) \<in> intra g" using e by (simp add: sink_node_def)
  have dok': "snd (last (path t)) \<in> \<lbrakk>d\<rbrakk>" using dok by (simp add: sink_store_def)
  have s'': "s' \<in> edge_step a (snd (last (path t)))" using s' by (simp add: sink_store_def)
  have wok': "last_writer g x (path t) \<in> gamma_lw_state w x"
    using wok unfolding trace_last_writer_def .
  have "s' \<in> \<lbrakk>fst (product_step base_tf a v (d, w))\<rbrakk>
          \<and> last_writer g x (path t @ [(v, s')]) \<in> gamma_lw_state (snd (product_step base_tf a v (d, w))) x"
    using product_step_sound[OF base_sound fn e' p dok' wok' s''] .
  then show ?thesis unfolding trace_last_writer_def by simp
qed

end
