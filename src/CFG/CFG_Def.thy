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

(* Affine shift along program points compile c (n+k) is compile c n with all pp+k. *)

definition offset_edges :: "nat \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> (pp \<times> edge_action \<times> pp) set" where
  "offset_edges k E = (\<lambda>(u,a,v). (u + k, a, v + k)) ` E"

lemma offset_edges_Un[simp]:
  "offset_edges k (A \<union> B) = offset_edges k A \<union> offset_edges k B"
  unfolding offset_edges_def by force

lemma offset_edges_insert_shift:
  "offset_edges k (insert ((u::nat), a, (v::nat)) S) =
   insert (u + k, a, v + k) (offset_edges k S)"
  unfolding offset_edges_def
  by auto

lemma in_offset_edges_iff:
  "((u + k::nat, a, v + k) \<in> offset_edges k E) \<longleftrightarrow> (u, a, v) \<in> E"
  unfolding offset_edges_def by (force simp: prod_eq_iff)

(* \<midarrow>\<midarrow> Derived Notions \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

definition predecessors :: "cfg => pp => (pp * edge_action) set" where
  "predecessors g v = {(u, a) | u a. (u, a, v) : cfg_edges g}"

lemma finite_predecessors:
  assumes "finite (cfg_edges g)"
  shows "finite (predecessors g v)"
proof -
  have "predecessors g v \<subseteq> (\<lambda>e :: pp \<times> edge_action \<times> pp. (fst e, fst (snd e))) ` cfg_edges g"
    unfolding predecessors_def by force
  then show ?thesis
    using assms finite_subset finite_imageI by blast
qed

end
