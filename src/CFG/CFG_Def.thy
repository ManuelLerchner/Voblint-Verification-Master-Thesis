theory CFG_Def
  imports "Voblint_IMP2.IMP2_Syntax" "HOL-Library.Countable" "HOL-Library.Product_Lexorder"
          "Dijkstra_Shortest_Path.Graph"
begin

section \<open>Control-flow graph definition\<close>

text \<open>
  A CFG represents a program as a directed graph where:
    - Nodes are program points (natural numbers, allocated during translation).
    - Edges carry edge actions: assignments, branch assumptions, or no-ops.
    - Each edge (u, a, v) means: ''go from u to v, performing action a''.

  A `cfg` is a record-extension of AFP's `Dijkstra_Shortest_Path.Graph.graph`,
  inheriting the `nodes` and `edges` selectors and adding `cfg_entry`,
  `cfg_exit`.  Use the smart constructor `mk_cfg en ex E` to build CFGs:
  it auto-computes `nodes` from the edges plus endpoints so that
  `valid_graph` holds by construction.

  Translation from IMP2 to CFG is in IMP2_Proc_to_CFG.thy.
  The equation system over a CFG is in Equations/Constraint_System.thy.
\<close>

subsection \<open>Program points\<close>

type_synonym pp = nat

subsection \<open>Edge actions\<close>

text \<open>
  Each edge carries one of:
    EA_Nop          -- unconditional edge (no state change)
    EA_Assign x a   -- assignment: state updated as s(x := aval a s)
    EA_Assume b     -- assume b holds: filter states where bval b s = True
    EA_AssumeNot b  -- assume b fails: filter states where bval b s = False
\<close>

datatype edge_action =
    EA_Nop
  | EA_Assign   vname aexp
  | EA_Assume   bexp
  |     EA_AssumeNot bexp
  | EA_Enter                    (* call/scope entry: reset locals, keep globals *)

instance edge_action :: countable
  by countable_datatype

(* Implementation order for @{const cfg_edges_list} / @{const predecessor_list}
   (TD strategy trees), not part of the IMP2 semantics. *)
instantiation edge_action :: linorder
begin

definition less_eq_edge_action_def:
  "((\<le>) :: edge_action \<Rightarrow> edge_action \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x \<le> to_nat y"

definition less_edge_action_def:
  "((<) :: edge_action \<Rightarrow> edge_action \<Rightarrow> bool) \<equiv> \<lambda>x y. to_nat x < to_nat y"

instance
  apply (standard, goal_cases)
  unfolding less_eq_edge_action_def less_edge_action_def by(auto)

end

subsection \<open>CFG record (extension of AFP graph)\<close>

record cfg = "(pp, edge_action) graph" +
  cfg_entry :: pp
  cfg_exit  :: pp
  combines  :: "(pp * pp * pp) set"   (* (call, callee_exit, return) triples *)

subsection \<open>CFG construction\<close>

definition mk_ip_cfg ::
  "pp \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> (pp \<times> pp \<times> pp) set \<Rightarrow> cfg" where
  "mk_ip_cfg entry exit E C =
     \<lparr> nodes = ({entry, exit} \<union> fst ` E \<union> (snd \<circ> snd) ` E
                  \<union> fst ` C \<union> (fst \<circ> snd) ` C \<union> (snd \<circ> snd) ` C),
       edges = E,
       cfg_entry = entry,
       cfg_exit = exit,
       combines = C
     \<rparr>"

definition mk_cfg :: "pp \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> cfg" where
  "mk_cfg entry exit E = mk_ip_cfg entry exit E {}"

declare mk_cfg_def[simp] mk_ip_cfg_def[simp]

lemma mk_cfg_combines_empty[simp]:
  "combines (mk_cfg en ex E) = {}"
  by (simp add: mk_cfg_def)

lemma mk_cfg_valid_graph: "valid_graph (graph.truncate (mk_cfg en ex E))"
  unfolding valid_graph_def graph.truncate_def mk_cfg_def by force

(* Affine shift along program points compile c (n+k) is compile c n with all pp+k. *)

definition offset_edges :: "nat \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> (pp \<times> edge_action \<times> pp) set" where
  "offset_edges k E = (\<lambda>(u,a,v). (u + k, a, v + k)) ` E"

lemma offset_edges_Un[simp]:
  "offset_edges k (A \<union> B) = offset_edges k A \<union> offset_edges k B"
  unfolding offset_edges_def by force

lemma offset_edges_insert_shift:
  "offset_edges k (insert ((u::nat), a, (v::nat)) S) =
   insert (u + k, a, v + k) (offset_edges k S)"
  unfolding offset_edges_def by auto

lemma in_offset_edges_iff:
  "((u + k::nat, a, v + k) \<in> offset_edges k E) \<longleftrightarrow> (u, a, v) \<in> E"
  unfolding offset_edges_def by (force simp: prod_eq_iff)

subsection \<open>Derived notions\<close>

definition predecessors :: "cfg => pp => (pp * edge_action) set" where
  "predecessors g v = {(u, a) | u a. (u, a, v) : edges g}"

lemma finite_predecessors:
  assumes "finite (edges g)"
  shows "finite (predecessors g v)"
proof  -
  have "predecessors g v \<subseteq> (\<lambda>e :: pp \<times> edge_action \<times> pp. (fst e, fst (snd e))) ` edges g"
    unfolding predecessors_def by force
  then show ?thesis
    using assms finite_subset finite_imageI by blast
qed

definition combine_predecessors :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> pp) set" where
  "combine_predecessors g v = {(c, e) | c e. (c, e, v) \<in> combines g}"

lemma finite_combine_predecessors:
  assumes "finite (combines g)"
  shows "finite (combine_predecessors g v)"
proof -
  have "combine_predecessors g v
        \<subseteq> (\<lambda>t :: pp \<times> pp \<times> pp. (fst t, fst (snd t))) ` combines g"
    unfolding combine_predecessors_def by force
  then show ?thesis
    using assms finite_subset finite_imageI by blast
qed

(* Stable edge enumeration for the TD bridge: sort by (source, action, target). *)

definition cfg_edges_list :: "cfg \<Rightarrow> (pp \<times> edge_action \<times> pp) list" where
  "cfg_edges_list g =
     (if finite (edges g) then sorted_list_of_set (edges g) else [])"

definition predecessor_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list" where
  "predecessor_list g v =
     map (\<lambda>(u, a, w). (u, a)) (filter (\<lambda>(u, a, w). w = v) (cfg_edges_list g))"

lemma set_cfg_edges_list[simp]:
  assumes "finite (edges g)"
  shows "set (cfg_edges_list g) = edges g"
  unfolding cfg_edges_list_def using assms by simp

lemma distinct_cfg_edges_list[simp]:
  assumes "finite (edges g)"
  shows "distinct (cfg_edges_list g)"
  unfolding cfg_edges_list_def using assms by simp

lemma set_predecessor_list[simp]:
  assumes "finite (edges g)"
  shows "set (predecessor_list g v) = predecessors g v"
proof -
  show ?thesis
    unfolding predecessor_list_def predecessors_def
    using assms set_cfg_edges_list[OF assms]
    by (force simp: image_iff)
qed

lemma distinct_predecessor_list[simp]:
  assumes "finite (edges g)"
  shows "distinct (predecessor_list g v)"
proof -
  have dist_filt: "distinct (filter (\<lambda>(u, a, w). w = v) (cfg_edges_list g))"
    using distinct_filter distinct_cfg_edges_list assms by simp
  have inj: "inj_on (\<lambda>(u, a, w). (u, a)) (set (filter (\<lambda>(u, a, w). w = v) (cfg_edges_list g)))"
    by (auto simp: inj_on_def)
  show ?thesis
    unfolding predecessor_list_def distinct_map
    using dist_filt inj by simp
qed

lemma predecessor_list_Nil_if_no_in:
  assumes "\<And>u a. (u, a, v) \<notin> edges g"
  shows "predecessor_list g v = []"
proof -
  have "filter (\<lambda>(u, a, w). w = v) (cfg_edges_list g) = []"
  proof (cases "finite (edges g)")
    case True
    then show ?thesis
      using assms set_cfg_edges_list[OF True]
      by (force simp: cfg_edges_list_def filter_empty_conv)
  next
    case False
    then show ?thesis
      by (simp add: cfg_edges_list_def)
  qed
  then show ?thesis
    unfolding predecessor_list_def by simp
qed

(* Stable combine enumeration for the interprocedural TD bridge. *)

definition cfg_combines_list :: "cfg \<Rightarrow> (pp \<times> pp \<times> pp) list" where
  "cfg_combines_list g =
     (if finite (combines g) then sorted_list_of_set (combines g) else [])"

definition combine_predecessor_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> pp) list" where
  "combine_predecessor_list g v =
     map (\<lambda>(c, e, ret). (c, e))
       (filter (\<lambda>(c, e, ret). ret = v) (cfg_combines_list g))"

lemma set_cfg_combines_list[simp]:
  assumes "finite (combines g)"
  shows "set (cfg_combines_list g) = combines g"
  unfolding cfg_combines_list_def using assms by simp

lemma distinct_cfg_combines_list[simp]:
  assumes "finite (combines g)"
  shows "distinct (cfg_combines_list g)"
  unfolding cfg_combines_list_def using assms by simp

lemma set_combine_predecessor_list[simp]:
  assumes "finite (combines g)"
  shows "set (combine_predecessor_list g v) = combine_predecessors g v"
proof -
  show ?thesis
    unfolding combine_predecessor_list_def combine_predecessors_def
    using assms set_cfg_combines_list[OF assms]
    by (force simp: image_iff)
qed

lemma distinct_combine_predecessor_list[simp]:
  assumes "finite (combines g)"
  shows "distinct (combine_predecessor_list g v)"
proof -
  have dist_filt:
      "distinct (filter (\<lambda>(c, e, ret). ret = v) (cfg_combines_list g))"
    using distinct_filter distinct_cfg_combines_list assms by simp
  have inj:
      "inj_on (\<lambda>(c, e, ret). (c, e))
        (set (filter (\<lambda>(c, e, ret). ret = v) (cfg_combines_list g)))"
    by (auto simp: inj_on_def)
  show ?thesis
    unfolding combine_predecessor_list_def distinct_map
    using dist_filt inj by simp
qed

lemma combine_predecessor_list_Nil_if_no_in:
  assumes "\<And>c e. (c, e, v) \<notin> combines g"
  shows "combine_predecessor_list g v = []"
proof -
  have "filter (\<lambda>(c, e, ret). ret = v) (cfg_combines_list g) = []"
  proof (cases "finite (combines g)")
    case True
    then show ?thesis
      using assms set_cfg_combines_list[OF True]
      by (force simp: cfg_combines_list_def filter_empty_conv)
  next
    case False
    then show ?thesis
      by (simp add: cfg_combines_list_def)
  qed
  then show ?thesis
    unfolding combine_predecessor_list_def by simp
qed

end
