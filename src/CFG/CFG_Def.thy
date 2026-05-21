theory CFG_Def
  imports IMP2_Syntax "HOL-Library.Countable" "Dijkstra_Shortest_Path.Graph"
begin

(*
  CFG -- Control-Flow Graph Definition.

  A CFG represents a program as a directed graph where:
    - Nodes are program points (natural numbers, allocated during translation).
    - Edges carry edge actions: assignments, branch assumptions, or no-ops.
    - Each edge (u, a, v) means: "go from u to v, performing action a".

  A `cfg` is a record-extension of AFP's `Dijkstra_Shortest_Path.Graph.graph`,
  inheriting the `nodes` and `edges` selectors and adding `cfg_entry`,
  `cfg_exit`.  Use the smart constructor `mk_cfg en ex E` to build CFGs:
  it auto-computes `nodes` from the edges plus endpoints so that
  `valid_graph` holds by construction.

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

(* \<midarrow>\<midarrow> CFG Record (extension of AFP graph) \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

record cfg = "(pp, edge_action) graph" +
  cfg_entry :: pp
  cfg_exit  :: pp

(* Smart constructor: auto-computes the node set so valid_graph holds. *)
definition compute_nodes :: "pp \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> pp set" where
  "compute_nodes en ex E = {en, ex} \<union> fst ` E \<union> (snd \<circ> snd) ` E"

definition mk_cfg :: "pp \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> cfg" where
  "mk_cfg en ex E =
     \<lparr> nodes = compute_nodes en ex E, edges = E, cfg_entry = en, cfg_exit = ex \<rparr>"

lemma edges_mk_cfg[simp]: "edges (mk_cfg en ex E) = E"
  by (simp add: mk_cfg_def)

lemma nodes_mk_cfg[simp]: "nodes (mk_cfg en ex E) = compute_nodes en ex E"
  by (simp add: mk_cfg_def)

lemma cfg_entry_mk_cfg[simp]: "cfg_entry (mk_cfg en ex E) = en"
  by (simp add: mk_cfg_def)

lemma cfg_exit_mk_cfg[simp]: "cfg_exit (mk_cfg en ex E) = ex"
  by (simp add: mk_cfg_def)

lemma mk_cfg_valid_graph: "valid_graph (graph.truncate (mk_cfg en ex E))"
  by unfold_locales (force simp: mk_cfg_def compute_nodes_def graph.defs)+

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
  "predecessors g v = {(u, a) | u a. (u, a, v) : edges g}"

lemma finite_predecessors:
  assumes "finite (edges g)"
  shows "finite (predecessors g v)"
proof -
  have "predecessors g v \<subseteq> (\<lambda>e :: pp \<times> edge_action \<times> pp. (fst e, fst (snd e))) ` edges g"
    unfolding predecessors_def by force
  then show ?thesis
    using assms finite_subset finite_imageI by blast
qed

end
