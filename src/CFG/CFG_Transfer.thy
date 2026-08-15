theory CFG_Transfer
  imports VIMP_Proc_to_CFG
begin

section \<open>Per-edge abstract transfer\<close>

text \<open>\<^const>\<open>edge_step\<close> (from \<^theory>\<open>Voblint_CFG.CFG_Def\<close>) is the primitive intra-edge
  semantics.  \<open>edge_collect\<close> is its pointwise lift to store sets --- the successors of any
  source store in \<open>S\<close> --- so the abstract set transformer is derived from the concrete step and the
  two cannot drift.  This is the per-\<^const>\<open>intra\<close>-edge transfer the constraint system folds over.\<close>

definition edge_collect :: "edge_action \<Rightarrow> store set \<Rightarrow> store set" where
  "edge_collect a S = {t. \<exists>s\<in>S. t \<in> edge_step a s}"

lemma edge_collect_simps [simp]:
  "edge_collect EA_Nop S = S"
  "edge_collect (EA_Assign x a) S = {s(x := aval a s) | s. s \<in> S}"
  "edge_collect (EA_Special sc x) S = {t. \<exists>s\<in>S. t \<in> special_step sc x s}"
  "edge_collect (EA_Assume b) S = {s. s \<in> S \<and> bval b s}"
  "edge_collect (EA_AssumeNot b) S = {s. s \<in> S \<and> \<not> bval b s}"
  "edge_collect (EA_Ret e p) S =
     {s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) | s. s \<in> S}"
  "edge_collect (EA_Check c) S = S"
  unfolding edge_collect_def by (auto split: if_splits)

lemma edge_collect_single:
  "edge_collect a {s} = edge_step a s"
  by (cases a) (auto split: if_splits)

lemma edge_collect_empty_set [simp]: "edge_collect a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
  using assms by (cases a) auto

lemma edge_collect_member:
  "x \<in> edge_collect a S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edge_collect a {s})"
  by (cases a) auto

end
