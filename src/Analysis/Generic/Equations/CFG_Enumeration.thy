theory CFG_Enumeration
  imports "Voblint_CFG.IMP2_Proc_to_CFG"
begin

section \<open>Solver-facing CFG enumeration\<close>

text \<open>
  Backward predecessor relations and deterministic edge/combine enumeration over a
  compiled CFG.  These are the equation-generation and code-generation views the TD
  solver reads to build and evaluate the constraint system; they are not part of the
  concrete CFG semantics --- \<open>valid_ltr\<close> never refers to them.  They live in the
  analysis session, next to the constraint system that consumes them, so that
  \<^theory>\<open>Voblint_CFG.CFG_Def\<close> carries only the control-flow relation and its label
  classification.
\<close>

subsection \<open>Executable orders\<close>

(* bexp linorder is required for edge_action below; derived here (not in
   IMP2_Syntax) so IMP2 stays warning-free. *)
derive linorder bexp

(* Executable structural linear order on edge actions (AFP Deriving), used to
   enumerate edge sets deterministically via @{const sorted_list_of_set} in
   @{const cfg_edges_list} / @{const predecessor_list}. Code-generates, so the
   predecessor lookups feeding the TD bridge run directly. Not part of the IMP2
   semantics. *)
derive linorder edge_action

subsection \<open>Predecessors\<close>

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

definition combine_predecessors ::
    "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> pp \<times> vname option) set" where
  "combine_predecessors g v =
     (\<lambda>ci. (combine_call_node ci, combine_exit_node ci, combine_dst ci))
       ` combine_info_predecessors g v"

lemma combine_predecessors_eq:
  "combine_predecessors g v =
     {(c, ex, dst) | c ex dst. (c, ex, v, dst) \<in> combines g}"
  unfolding combine_predecessors_def combine_info_predecessors_def
    combine_call_node_def combine_exit_node_def combine_return_node_def
    combine_dst_def
  by (auto simp: image_iff)

lemma finite_combine_predecessors:
  assumes "finite (combines g)"
  shows "finite (combine_predecessors g v)"
proof -
  have "finite (combine_info_predecessors g v)"
    using assms unfolding combine_info_predecessors_def by auto
  then show ?thesis
    unfolding combine_predecessors_def by blast
qed

subsection \<open>Edge and predecessor enumeration\<close>

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

text \<open>
  The dual enumeration used by the context-sensitive generator: the
  \<^const>\<open>EA_Enter\<close> edges leaving a call node \<open>u\<close>, each paired with its callee
  entry point \<open>w\<close>.  A monovariant generator folds enter edges as predecessors of
  the callee entry; a context-sensitive one instead publishes, from the caller
  side, a routed callee-entry seed --- for which it enumerates a node's outgoing
  enters here.
\<close>

definition enter_successor_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list" where
  "enter_successor_list g u =
     map (\<lambda>(u', a, w). (w, a))
       (filter (\<lambda>(u', a, w). u' = u \<and> is_enter_action a) (cfg_edges_list g))"

lemma set_enter_successor_list:
  assumes "finite (edges g)"
  shows "set (enter_successor_list g u)
     = {(w, a) |a w. (u, a, w) \<in> edges g \<and> is_enter_action a}"
  unfolding enter_successor_list_def
  using set_cfg_edges_list[OF assms]
  by (force simp: image_iff)

lemma enter_successor_list_action:
  "(w, a) \<in> set (enter_successor_list g u) \<Longrightarrow> is_enter_action a"
  unfolding enter_successor_list_def by auto

lemma enter_successor_list_edge:
  assumes "finite (edges g)"
    and "(w, a) \<in> set (enter_successor_list g u)"
  shows "(u, a, w) \<in> edges g"
  using assms set_enter_successor_list[OF assms(1)] by auto

subsection \<open>Combine enumeration\<close>

(* Stable combine enumeration for the interprocedural TD bridge. *)

definition cfg_combines_list :: "cfg \<Rightarrow> combine_info list" where
  "cfg_combines_list g =
     (if finite (combines g) then sorted_list_of_set (combines g) else [])"

lemma cfg_combines_list_code [code]:
  "cfg_combines_list g = sorted_list_of_set (combines g)"
  unfolding cfg_combines_list_def
  by (cases "finite (combines g)") auto

definition combine_predecessor_list ::
    "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> pp \<times> vname option) list" where
  "combine_predecessor_list g v = sorted_list_of_set (combine_predecessors g v)"

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
  assumes "\<And>c e dst. (c, e, v, dst) \<notin> combines g"
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

value "cfg_edges_list (mk_cfg 0 1 {(0, EA_Nop, 1)} {})"
value "predecessor_list (mk_cfg 0 1 {(0, EA_Nop, 1)} {}) 1"
value "predecessor_list (mk_cfg 0 1 {(0, EA_Nop, 1)} {}) 0"
value "cfg_combines_list (mk_cfg 2 3 {(2, EA_Enter [] [], 0)} {(2, 1, 3, None)})"
value "combine_predecessor_list (mk_cfg 2 3 {(2, EA_Enter [] [], 0)} {(2, 1, 3, None)}) 3"

value "cfg_edges_list (compile_prog (\<lambda>_. None) [] IMP2_Proc.com.SKIP)"
value "cfg_edges_list (compile_prog (\<lambda>_. None) [] (IMP2_Proc.com.Assign ''x'' (N 1)))"
value "cfg_combines_list (compile_prog (\<lambda>_. None) [] (IMP2_Proc.com.Call None ''f'' []))"

end
