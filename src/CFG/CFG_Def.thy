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

(* ── Program Points ───────────────────────────────────────────── *)

type_synonym pp = nat

(* ── Edge Actions ─────────────────────────────────────────────── *)
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
proof (intro_classes)
  fix x y z :: edge_action
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_edge_action_def less_eq_edge_action_def
    using linorder_not_le by force
  show "x \<le> x"
    by (simp add: less_eq_edge_action_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (simp add: less_eq_edge_action_def order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: less_eq_edge_action_def to_nat_split)
  show "x \<le> y \<or> y \<le> x"
    by (simp add: less_eq_edge_action_def linear)
qed

end

(* ── CFG Record ───────────────────────────────────────────────── *)

record cfg =
  cfg_entry :: pp
  cfg_exit  :: pp
  cfg_edges :: "(pp * edge_action * pp) set"

(* ── Derived Notions ──────────────────────────────────────────── *)

definition cfg_nodes :: "cfg => pp set" where
  "cfg_nodes g = {cfg_entry g, cfg_exit g}
                 Un Union ((\<lambda>e. {fst e, snd (snd e)}) ` cfg_edges g)"

lemma cfg_edge_endpoints_in_cfg_nodes:
  assumes e: "(u, av) \<in> cfg_edges g"
  shows "u \<in> cfg_nodes g \<and> snd av \<in> cfg_nodes g"
  unfolding cfg_nodes_def using e by force

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

definition successors :: "cfg => pp => (pp * edge_action) set" where
  "successors g u = {(w, a) | w a. (u, a, w) : cfg_edges g}"

(* ── Well-Formedness ──────────────────────────────────────────── *)

definition cfg_wf :: "cfg => bool" where
  "cfg_wf g = (cfg_entry g \<noteq> cfg_exit g
               \<and> finite (cfg_edges g)
               \<and> (\<forall>e \<in> cfg_edges g. fst e \<in> cfg_nodes g \<and> snd (snd e) \<in> cfg_nodes g))"

end
