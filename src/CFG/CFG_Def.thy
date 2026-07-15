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
  | EA_AssumeNot bexp
  | EA_Enter    "vname list" "aexp list"
      (* call/scope entry: initialize fresh callee locals from caller actuals *)

instance edge_action :: countable
  by countable_datatype

(* bexp linorder is required for edge_action below; derived here (not in
   IMP2_Syntax) so IMP2 stays warning-free. *)
derive linorder bexp

(* Executable structural linear order on edge actions (AFP Deriving), used to
   enumerate edge sets deterministically via @{const sorted_list_of_set} in
   @{const cfg_edges_list} / @{const predecessor_list}. Code-generates, so the
   predecessor lookups feeding the TD bridge run directly. Not part of the IMP2
   semantics. *)
derive linorder edge_action

type_synonym combine_info = "pp * pp * pp * vname option * aexp option"

definition combine_call_node :: "combine_info \<Rightarrow> pp" where
  "combine_call_node ci = (case ci of (call, ex, ret, dst, rex) \<Rightarrow> call)"

definition combine_exit_node :: "combine_info \<Rightarrow> pp" where
  "combine_exit_node ci = (case ci of (call, ex, ret, dst, rex) \<Rightarrow> ex)"

definition combine_return_node :: "combine_info \<Rightarrow> pp" where
  "combine_return_node ci = (case ci of (call, ex, ret, dst, rex) \<Rightarrow> ret)"

subsection \<open>CFG record (extension of AFP graph)\<close>

record cfg = "(pp, edge_action) graph" +
  cfg_entry :: pp
  cfg_exit  :: pp
  combines  :: "combine_info set"

subsection \<open>CFG construction\<close>

definition mk_cfg ::
  "pp \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> combine_info set \<Rightarrow> cfg" where
  "mk_cfg entry exit E C =
     \<lparr> nodes = ({entry, exit} \<union> fst ` E \<union> (snd \<circ> snd) ` E
                  \<union> combine_call_node ` C
                  \<union> combine_exit_node ` C
                  \<union> combine_return_node ` C),
       edges = E,
       cfg_entry = entry,
       cfg_exit = exit,
       combines = C
     \<rparr>"

declare mk_cfg_def[simp]

lemma mk_cfg_valid_graph: "valid_graph (graph.truncate (mk_cfg en ex E C))"
  unfolding valid_graph_def graph.truncate_def mk_cfg_def
  by (simp add: image_comp inf_sup_aci(5) sup.left_commute sup.orderI)

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

definition combine_info_predecessors :: "cfg \<Rightarrow> pp \<Rightarrow> combine_info set" where
  "combine_info_predecessors g v = {ci \<in> combines g. combine_return_node ci = v}"

definition combine_predecessors :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> pp) set" where
  "combine_predecessors g v =
     (\<lambda>ci. (combine_call_node ci, combine_exit_node ci)) ` combine_info_predecessors g v"

lemma finite_combine_predecessors:
  assumes "finite (combines g)"
  shows "finite (combine_predecessors g v)"
proof -
  have "finite (combine_info_predecessors g v)"
    using assms unfolding combine_info_predecessors_def by auto
  then show ?thesis
    unfolding combine_predecessors_def by blast
qed

(* Stable edge enumeration for the TD bridge: sort by (source, action, target). *)

definition cfg_edges_list :: "cfg \<Rightarrow> (pp \<times> edge_action \<times> pp) list" where
  "cfg_edges_list g =
     (if finite (edges g) then sorted_list_of_set (edges g) else [])"

(* Drop the finiteness guard for code generation: sorted_list_of_set already
   yields [] on an infinite set, so the guarded and unguarded forms agree.
   Without this the generated code would have to decide finite (edges g). *)
lemma cfg_edges_list_code [code]:
  "cfg_edges_list g = sorted_list_of_set (edges g)"
  unfolding cfg_edges_list_def
  by (cases "finite (edges g)") auto


definition predecessor_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list" where
  "predecessor_list g v =
     map (\<lambda>(u, a, w). (u, a)) (filter (\<lambda>(u, a, w). w = v) (cfg_edges_list g))"

definition is_enter_action :: "edge_action \<Rightarrow> bool" where
  "is_enter_action a = (case a of EA_Enter _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

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

subsection \<open>Frame-entry predecessor split\<close>

text \<open>
  A frame-entry node is the target of some \<^const>\<open>EA_Enter\<close> edge (a procedure
  or scope entry -- the IMP2-to-CFG compiler emits this edge shape for both
  ``Call`` and ``Scope``).  Splitting \<^const>\<open>predecessor_list\<close> into its
  \<^const>\<open>EA_Enter\<close>
  and non-\<^const>\<open>EA_Enter\<close> parts lets a context-sensitive generator seed a
  frame-entry node's locals from the call context while still folding in any
  other predecessor (e.g. a loop backedge, when the frame entry coincides with
  a loop head) through the ordinary transfer.
\<close>

definition enter_predecessor_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list" where
  "enter_predecessor_list g v = filter (\<lambda>(u, a). is_enter_action a) (predecessor_list g v)"

definition non_enter_predecessor_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list" where
  "non_enter_predecessor_list g v = filter (\<lambda>(u, a). \<not> is_enter_action a) (predecessor_list g v)"

definition is_frame_entry :: "cfg \<Rightarrow> pp \<Rightarrow> bool" where
  "is_frame_entry g v = (enter_predecessor_list g v \<noteq> [])"

lemma set_predecessor_list_enter_split:
  "set (predecessor_list g v)
     = set (enter_predecessor_list g v) \<union> set (non_enter_predecessor_list g v)"
  unfolding enter_predecessor_list_def non_enter_predecessor_list_def by auto

lemma enter_predecessor_list_action:
  "(u, a) \<in> set (enter_predecessor_list g v) \<Longrightarrow> is_enter_action a"
  unfolding enter_predecessor_list_def by auto

lemma non_enter_predecessor_list_action:
  "(u, a) \<in> set (non_enter_predecessor_list g v) \<Longrightarrow> \<not> is_enter_action a"
  unfolding non_enter_predecessor_list_def by auto

lemma non_enter_predecessor_list_mem:
  "(u, a) \<in> set (predecessor_list g v) \<Longrightarrow> \<not> is_enter_action a
   \<Longrightarrow> (u, a) \<in> set (non_enter_predecessor_list g v)"
  unfolding non_enter_predecessor_list_def by auto

lemma enter_predecessor_list_mem:
  "(u, a) \<in> set (predecessor_list g v)
   \<Longrightarrow> is_enter_action a
   \<Longrightarrow> (u, a) \<in> set (enter_predecessor_list g v)"
  unfolding enter_predecessor_list_def by auto

(* Stable combine enumeration for the interprocedural TD bridge. *)

definition cfg_combines_list :: "cfg \<Rightarrow> combine_info list" where
  "cfg_combines_list g =
     (if finite (combines g) then sorted_list_of_set (combines g) else [])"

lemma cfg_combines_list_code [code]:
  "cfg_combines_list g = sorted_list_of_set (combines g)"
  unfolding cfg_combines_list_def
  by (cases "finite (combines g)") auto

definition combine_info_predecessor_list :: "cfg \<Rightarrow> pp \<Rightarrow> combine_info list" where
  "combine_info_predecessor_list g v =
     filter (\<lambda>(_, _, ret, _, _). ret = v) (cfg_combines_list g)"

definition combine_predecessor_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> pp) list" where
  "combine_predecessor_list g v = sorted_list_of_set (combine_predecessors g v)"

lemma set_cfg_combines_list[simp]:
  assumes "finite (combines g)"
  shows "set (cfg_combines_list g) = combines g"
  unfolding cfg_combines_list_def using assms by simp

lemma distinct_cfg_combines_list[simp]:
  assumes "finite (combines g)"
  shows "distinct (cfg_combines_list g)"
  unfolding cfg_combines_list_def using assms by simp

lemma set_combine_info_predecessor_list[simp]:
  assumes "finite (combines g)"
  shows "set (combine_info_predecessor_list g v) = combine_info_predecessors g v"
  unfolding combine_info_predecessor_list_def combine_info_predecessors_def combine_return_node_def
  using assms set_cfg_combines_list[OF assms]
  by auto

lemma distinct_combine_info_predecessor_list[simp]:
  assumes "finite (combines g)"
  shows "distinct (combine_info_predecessor_list g v)"
  unfolding combine_info_predecessor_list_def
  using distinct_filter distinct_cfg_combines_list assms by simp

lemma set_combine_predecessor_list[simp]:
  assumes "finite (combines g)"
  shows "set (combine_predecessor_list g v) = combine_predecessors g v"
  unfolding combine_predecessor_list_def
  using assms finite_combine_predecessors[OF assms]
  by simp

lemma distinct_combine_predecessor_list[simp]:
  assumes "finite (combines g)"
  shows "distinct (combine_predecessor_list g v)"
  unfolding combine_predecessor_list_def
  using assms finite_combine_predecessors[OF assms]
  by simp

lemma combine_predecessor_list_Nil_if_no_in:
  assumes "\<And>c e dst rex. (c, e, v, dst, rex) \<notin> combines g"
  shows "combine_predecessor_list g v = []"
proof -
  have "combine_info_predecessors g v = {}"
    using assms unfolding combine_info_predecessors_def combine_return_node_def by auto
  hence "combine_predecessors g v = {}"
    unfolding combine_predecessors_def by simp
  then show ?thesis
    unfolding combine_predecessor_list_def by simp
qed

subsection \<open>Executable examples\<close>

value "cfg_entry (mk_cfg 0 2 {(0, EA_Nop, 1), (1, EA_Nop, 2)} {})"
value "cfg_exit  (mk_cfg 0 2 {(0, EA_Nop, 1), (1, EA_Nop, 2)} {})"

value "cfg_edges_list (mk_cfg 0 1 {(0, EA_Nop, 1)} {})"
value "predecessor_list (mk_cfg 0 1 {(0, EA_Nop, 1)} {}) 1"
value "predecessor_list (mk_cfg 0 1 {(0, EA_Nop, 1)} {}) 0"

value "cfg_combines_list (mk_cfg 2 3 {(2, EA_Enter [] [], 0)} {(2, 1, 3, None, None)})"
value "combine_predecessor_list (mk_cfg 2 3 {(2, EA_Enter [] [], 0)} {(2, 1, 3, None, None)}) 3"

end
