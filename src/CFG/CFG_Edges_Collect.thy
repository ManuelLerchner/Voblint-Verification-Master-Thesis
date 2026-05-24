theory CFG_Edges_Collect
  imports IMP2_to_CFG CFG_Path
begin

(* Per-edge and path-based store-set collecting (edges_collect fold). *)

(* \<midarrow>\<midarrow> Per-Edge Transfer Function on State Sets \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

fun edge_collect :: "edge_action => store set => store set" where
    "edge_collect EA_Nop          S = S"
  | "edge_collect (EA_Assign x a) S = {s(x := aval a s) | s. s : S}"
  | "edge_collect (EA_Assume b)    S = Collect (\<lambda>s. s \<in> S \<and> bval b s)"
  | "edge_collect (EA_AssumeNot b) S = Collect (\<lambda>s. s \<in> S \<and> \<not> bval b s)"

lemma edge_collect_empty_set[simp]: "edge_collect a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
  using assms by (cases a) auto

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
proof (induction es arbitrary: S T)
  case Nil then show ?case by simp
next
  case (Cons e es)
  obtain a w where ep: "e = (a, w)" by (cases e)
  show ?case using Cons ep edge_collect_mono by auto
qed

lemma edges_collect_append[simp]:
  "edges_collect (es1 @ es2) S = edges_collect es2 (edges_collect es1 S)"
  by (induction es1 arbitrary: S) auto

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
     Union {edge_collect a (rho u) | u a. (u, a, v) : edges g}"

(* \<midarrow>\<midarrow> Least Fixpoint (Collecting Semantics over CFG) \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  Given an initial store set S at the entry, the CFG collecting semantics
  is the least fixpoint of the monotone transformer collect_pp.
*)

definition cfg_collect_F :: "cfg => store set => cenv => cenv" where
  "cfg_collect_F g S rho v =
     (if v = cfg_entry g then S Un collect_pp g rho v
      else collect_pp g rho v)"

definition cfg_collect :: "cfg => store set => cenv" where
  "cfg_collect g S = lfp (cfg_collect_F g S)"

(* \<midarrow>\<midarrow> Monotonicity of collect_pp \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   Required for lfp to be well-defined. *)

lemma collect_pp_mono:
  "mono (\<lambda>rho. collect_pp g rho v)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  then have ru: "\<And>u. rho1 u \<subseteq> rho2 u"
    by (simp add: le_fun_def)
  have edge: "\<And>u a. (u, a, v) \<in> edges g \<Longrightarrow> edge_collect a (rho1 u) \<subseteq> edge_collect a (rho2 u)"
    using ru edge_collect_mono by auto
  then show "collect_pp g rho1 v \<subseteq> collect_pp g rho2 v"
    unfolding collect_pp_def by blast
qed

lemma cfg_collect_F_mono:
  "mono (cfg_collect_F g S)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  show "cfg_collect_F g S rho1 \<le> cfg_collect_F g S rho2"
    unfolding cfg_collect_F_def le_fun_def
    using collect_pp_mono le monotoneD by fastforce
qed

lemma cfg_collect_lfp_unfold:
  "cfg_collect g S = cfg_collect_F g S (cfg_collect g S)"
  unfolding cfg_collect_def
  by (simp add: cfg_collect_F_mono def_lfp_unfold)

lemma cfg_collect_F_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect_F g S rho \<le> cfg_collect_F g S' rho"
  unfolding cfg_collect_F_def le_fun_def by auto

lemma cfg_collect_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect g S \<le> cfg_collect g S'"
  unfolding cfg_collect_def
  by (rule lfp_mono) (rule cfg_collect_F_mono_S)


end
