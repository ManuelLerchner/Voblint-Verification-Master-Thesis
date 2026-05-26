theory CFG_Edges_Collect
  imports IMP2_to_CFG CFG_Path
begin

(* Per-edge and path-based store-set collecting (edges_collect fold). *)

(* \<midarrow>\<midarrow> Per-Edge Transfer Function on State Sets \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

fun edge_collect :: "edge_action => store set => store set" where
    "edge_collect EA_Nop           S = S"
  | "edge_collect (EA_Assign x a)  S = {s(x := aval a s) | s. s : S}"
  | "edge_collect (EA_Assume b)    S = {s. s \<in> S \<and>  bval b s}"
  | "edge_collect (EA_AssumeNot b) S = {s. s \<in> S \<and> \<not>bval b s}"

lemma edge_collect_empty_set[simp]: "edge_collect a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
  using assms by (cases a) auto

lemma edge_collect_member:
  "x \<in> edge_collect a S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edge_collect a {s})"
  by (cases a) auto

(*
  edges_collect aggregates the resulting state after walking along a list of edges
  and running edge_collect each time
*)
fun edges_collect :: "(edge_action * pp) list => store set => store set" where
  "edges_collect [] S = S"
| "edges_collect ((a, _) # es) S = edges_collect es (edge_collect a S)"


lemma edges_collect_empty_set[simp]: "edges_collect es {} = {}"
  by (induction es) auto

lemma edges_collect_mono_strong:
  "S \<subseteq> T \<Longrightarrow> edges_collect es S \<subseteq> edges_collect es T"
  apply (induction es S arbitrary: T rule:edges_collect.induct)
  by (auto simp add: edge_collect_mono)
 
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
  "edges_collect (es1 @ [(EA_Nop, w)] @ es2) S = edges_collect es2 (edges_collect es1 S)"
proof (induction es1 arbitrary: S)
  case Nil
  show ?case by (simp add: edges_collect_append)
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
    by (cases a) (auto simp: mem_Collect_eq)
  have "t \<in> edges_collect (e # es) {m0}"
    unfolding ew edges_collect.simps mm tm
    using mm edges_collect_member tm by blast
  with m0 show ?case by blast
qed

(*
  edges_collect only inspects edge actions; the pp component of each
  step is discarded.  Hence shifting pp's via offset_path is invisible
  to edges_collect.
*)
lemma edges_collect_offset_path[simp]:
  "edges_collect (offset_path k es) S = edges_collect es S"
  by (induction es arbitrary: S) (auto simp: offset_path_def)


(* \<midarrow>\<midarrow> CFG Collecting Environment \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  A collecting environment maps each program point to the set of states
  that can appear there during any execution starting from some fixed
  initial set.
*)

type_synonym cenv = "pp => store set"


(* \<midarrow>\<midarrow> Collecting Transformer for One Program Point \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  collect_pp g rho v = join of edge_collect(a)(rho u) over all (u,a,v) in g.
  This is the single-step "push" of states through each incoming edge.
*)

definition collect_pp :: "cfg => cenv => pp => store set" where
  "collect_pp g rho v =
     \<Union>{edge_collect a (rho u) | u a. (u, a, v) : edges g}"

(* \<midarrow>\<midarrow> Least Fixpoint (Collecting Semantics over CFG) \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  Given an initial store set S at the entry, the CFG collecting semantics
  is the least fixpoint of the monotone transformer collect_pp.
*)


definition cfg_collect_F :: "cfg => store set => cenv => cenv" where
  "cfg_collect_F g S rho v =
     (if v = cfg_entry g then S else {}) \<union> collect_pp g rho v"

definition cfg_collect :: "cfg => store set => cenv" where
  "cfg_collect g S = lfp (cfg_collect_F g S)"

(* \<midarrow>\<midarrow> Monotonicity of collect_pp \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   Required for lfp to be well-defined. *)

lemma collect_pp_mono:
  "mono (\<lambda>rho. collect_pp g rho v)"
proof
  fix rho1 rho2 :: cenv
  assume "rho1 \<le> rho2"
  then have "\<forall>u. rho1 u \<subseteq> rho2 u"
    by (simp add: le_fun_def)
  then have edge: "\<forall>a u. edge_collect a (rho1 u) \<subseteq> edge_collect a (rho2 u)"
    using edge_collect_mono by auto
  then show "collect_pp g rho1 v \<subseteq> collect_pp g rho2 v"
    unfolding collect_pp_def by auto
qed

lemma cfg_collect_F_mono:
  "mono (cfg_collect_F g S)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  then show "cfg_collect_F g S rho1 \<le> cfg_collect_F g S rho2"
    unfolding cfg_collect_F_def le_fun_def
    using collect_pp_mono le monotoneD by fastforce
qed

lemma cfg_collect_F_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect_F g S rho \<le> cfg_collect_F g S' rho"
  unfolding cfg_collect_F_def le_fun_def by auto

lemma cfg_collect_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect g S \<le> cfg_collect g S'"
  unfolding cfg_collect_def
  by (rule lfp_mono) (rule cfg_collect_F_mono_S)

lemma cfg_collect_lfp_unfold:
  "cfg_collect g S = cfg_collect_F g S (cfg_collect g S)"
  unfolding cfg_collect_def
  by (simp add: cfg_collect_F_mono def_lfp_unfold)


end
