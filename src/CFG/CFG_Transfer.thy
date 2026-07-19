theory CFG_Transfer
  imports "Voblint_IMP2.IMP2_Expr" CFG_Path "Voblint_IMP2.IMP2_Globals" IMP2_Proc_to_CFG
begin

section \<open>Concrete CFG transfer primitives\<close>

fun edge_collect :: "edge_action => store set => store set" where
    "edge_collect EA_Nop S = S"
  | "edge_collect (EA_Assign x a) S = {s(x := aval a s) | s. s \<in> S}"
  | "edge_collect (EA_Assume b) S = {s. s \<in> S \<and> bval b s}"
  | "edge_collect (EA_AssumeNot b) S = {s. s \<in> S \<and> \<not> bval b s}"
  | "edge_collect (EA_Enter xs es) S =
       {bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s) | s. s \<in> S}"

lemma edge_collect_empty_set[simp]: "edge_collect a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
  using assms by (cases a) auto

lemma edge_collect_member:
  "x \<in> edge_collect a S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edge_collect a {s})"
  by (cases a) auto

fun edge_step :: "edge_action => store => store option" where
    "edge_step EA_Nop s = Some s"
  | "edge_step (EA_Assign x a) s = Some (s(x := aval a s))"
  | "edge_step (EA_Assume b) s = (if bval b s then Some s else None)"
  | "edge_step (EA_AssumeNot b) s = (if bval b s then None else Some s)"
  | "edge_step (EA_Enter xs es) s =
       Some (bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s))"

lemma edge_collect_single:
  "edge_collect a {s} = set_option (edge_step a s)"
  by (cases a) auto

definition call_enter_store :: "cfg => pp => store => store => bool" where
  "call_enter_store g c s t \<longleftrightarrow>
     (\<exists>pe xs es. (c, EA_Enter xs es, pe) \<in> edges g \<and>
       t = bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s))"

fun edges_collect :: "(edge_action * pp) list => store set => store set" where
    "edges_collect [] S = S"
  | "edges_collect ((a, _) # es) S = edges_collect es (edge_collect a S)"

lemma edges_collect_empty_set[simp]: "edges_collect es {} = {}"
  by (induction es) auto

lemma edges_collect_mono_strong:
  "S \<subseteq> T \<Longrightarrow> edges_collect es S \<subseteq> edges_collect es T"
  apply (induction es S arbitrary: T rule: edges_collect.induct)
  by (auto simp: edge_collect_mono)

lemma edges_collect_member:
  "x \<in> edges_collect es S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edges_collect es {s})"
proof (induction es arbitrary: S x)
  case Nil
  then show ?case by auto
next
  case (Cons e es)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case unfolding ep
    by (metis edge_collect_member edges_collect.simps(2) local.Cons)
qed

lemma edges_collect_memberE[elim]:
  assumes "x \<in> edges_collect es S"
  obtains s where "s \<in> S" and "x \<in> edges_collect es {s}"
  using assms edges_collect_member by blast

lemma edges_collect_append[simp]:
  "edges_collect (es1 @ es2) S = edges_collect es2 (edges_collect es1 S)"
  apply (induction es1 arbitrary: S)
  by auto

lemma edges_collect_nop_append:
  "edges_collect (es1 @ [(EA_Nop, w)] @ es2) S =
     edges_collect es2 (edges_collect es1 S)"
proof (induction es1 arbitrary: S)
  case Nil
  then show ?case by simp
next
  case (Cons e es1)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case
    unfolding ep edges_collect.simps edges_collect_append Cons by simp
qed

lemma mem_edges_collect_from_set:
  "t \<in> edges_collect es M \<Longrightarrow> \<exists>m\<in>M. t \<in> edges_collect es {m}"
proof (induction es arbitrary: M t)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain a w where ew: "e = (a, w)" by (cases e) auto
  obtain M' where M': "M' = edge_collect a M" by simp
  from Cons.prems ew obtain t': "t \<in> edges_collect es M'"
    using M' edges_collect.simps(2) by blast
  from Cons.IH[OF this] obtain m where m: "m \<in> M'" and tm: "t \<in> edges_collect es {m}"
    by blast
  from m have "m \<in> edge_collect a M"
    using M' by auto
  then obtain m0 where m0: "m0 \<in> M" and mm: "m \<in> edge_collect a {m0}"
    by (cases a) auto
  have "t \<in> edges_collect (e # es) {m0}"
    unfolding ew edges_collect.simps mm tm
    using mm edges_collect_member tm by blast
  with m0 show ?case by blast
qed

lemma edges_collect_offset_path[simp]:
  "edges_collect (offset_path k es) S = edges_collect es S"
  by (induction es arbitrary: S) (auto simp: offset_path_def)

definition combine_collect :: "vname option \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_collect dst s t = combine_assign dst (t ret_var) (combine_states s t)"

lemma combine_collect_None: "combine_collect None s t = <s|t>"
  by (simp add: combine_collect_def)

end
