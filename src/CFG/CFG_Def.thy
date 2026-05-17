theory CFG_Def
  imports IMP2_Syntax "HOL-Library.Countable"
begin

(*
  CFG -- Control-Flow Graph Definition.

  A CFG represents a program as a directed graph where:
    - Nodes are program points (natural numbers, allocated during translation).
    - Edges carry edge actions: assignments, branch assumptions, or no-ops.
    - Each edge (u, a, v) means: "go from u to v, performing action a".

  Translation from IMP2 to CFG is in IMP2_to_CFG.thy.
  The equation system over a CFG is in Equations/Constraint_System.thy.
*)

(* \<midarrow>\<midarrow> Program Points \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

type_synonym pp = nat

(* \<midarrow>\<midarrow> Edge Actions \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  Each edge carries one of:
    EA_Nop          -- unconditional edge (no state change)
    EA_Assign x a   -- assignment: state updated as s(x := aval a s)
    EA_Assume b     -- assume b holds: filter states where bval b s = True
    EA_AssumeNot b  -- assume b fails: filter states where bval b s = False
*)

datatype edge_action =
    EA_Nop
  | EA_Assign   vname aexp
  | EA_Assume   bexp
  | EA_AssumeNot bexp

instance edge_action :: countable
  by countable_datatype

instantiation edge_action :: linorder
begin

definition less_eq_edge_action_def:
  "((\<le>) :: edge_action \<Rightarrow> edge_action \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x \<le> to_nat y"

definition less_edge_action_def:
  "((<) :: edge_action \<Rightarrow> edge_action \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x < to_nat y"

instance
  apply (intro_classes)
  unfolding less_edge_action_def less_eq_edge_action_def by auto
end

(* \<midarrow>\<midarrow> CFG Record \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

record cfg =
  cfg_entry :: pp
  cfg_exit  :: pp
  cfg_edges :: "(pp * edge_action * pp) set"

(* Affine shift along program points — compile c (n+k) is compile c n with all pp+k. *)

definition offset_edges :: "nat \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> (pp \<times> edge_action \<times> pp) set" where
  "offset_edges k E = (\<lambda>(u,a,v). (u + k, a, v + k)) ` E"

definition cfg_offset :: "nat \<Rightarrow> cfg \<Rightarrow> cfg" where
  "cfg_offset k g = \<lparr> cfg_entry = cfg_entry g + k, cfg_exit = cfg_exit g + k,
                      cfg_edges = offset_edges k (cfg_edges g) \<rparr>"

lemma offset_edges_Un[simp]:
  "offset_edges k (A \<union> B) = offset_edges k A \<union> offset_edges k B"
  unfolding offset_edges_def by force

lemma offset_edges_insert_union:
  "insert (u + k::nat, a, v + k) (offset_edges k E1) =
   offset_edges k (insert (u, a, v) (E1))"
  using offset_edges_Un offset_edges_def by auto


lemma offset_edges_insert_shift:
  "offset_edges k (insert ((u::nat), a, (v::nat)) S) =
   insert (u + k, a, v + k) (offset_edges k S)"
  unfolding offset_edges_def
  by auto

lemma in_offset_edges_iff:
  "((u + k::nat, a, v + k) \<in> offset_edges k E) \<longleftrightarrow> (u, a, v) \<in> E"
  unfolding offset_edges_def by (force simp: prod_eq_iff)

lemma finite_offset_edges:
  assumes "finite E" shows "finite (offset_edges k E)"
  unfolding offset_edges_def using assms by simp

(* \<midarrow>\<midarrow> Derived Notions \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

definition cfg_nodes :: "cfg => pp set" where
  "cfg_nodes g = {cfg_entry g, cfg_exit g}
                 Un Union ((\<lambda>e. {fst e, snd (snd e)}) ` cfg_edges g)"

lemma cfg_edge_endpoints_in_cfg_nodes:
  assumes e: "(u, av) \<in> cfg_edges g"
  shows "u \<in> cfg_nodes g \<and> snd av \<in> cfg_nodes g"
  unfolding cfg_nodes_def using e by force

definition predecessors :: "cfg => pp => (pp * edge_action) set" where
  "predecessors g v = {(u, a) | u a. (u, a, v) : cfg_edges g}"

definition successors :: "cfg => pp => (pp * edge_action) set" where
  "successors g u = {(w, a) | w a. (u, a, w) : cfg_edges g}"

lemma finite_predecessors:
  assumes "finite (cfg_edges g)"
  shows "finite (predecessors g v)"
proof -
  have "predecessors g v \<subseteq> (\<lambda>e :: pp \<times> edge_action \<times> pp. (fst e, fst (snd e))) ` cfg_edges g"
    unfolding predecessors_def by force
  then show ?thesis
    using assms finite_subset finite_imageI by blast
qed

lemma finite_successors:
  assumes "finite (cfg_edges g)"
  shows "finite (successors g v)"
proof -
  have "successors g v \<subseteq> (\<lambda>e :: pp \<times> edge_action \<times> pp. ( snd (snd e), fst (snd e))) ` cfg_edges g"
    unfolding successors_def by force
  then show ?thesis
    using assms finite_subset finite_imageI by blast
qed 

(* \<midarrow>\<midarrow> Well-Formedness \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

definition cfg_wf :: "cfg => bool" where
  "cfg_wf g = (cfg_entry g \<noteq> cfg_exit g
               \<and> finite (cfg_edges g)
               \<and> (\<forall>e \<in> cfg_edges g. fst e \<in> cfg_nodes g \<and> snd (snd e) \<in> cfg_nodes g))"

end
