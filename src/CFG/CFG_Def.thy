theory CFG_Def
  imports "Voblint_VIMP.VIMP_Proc" "HOL-Library.Countable"
begin

section \<open>Procedure-aware control-flow graph\<close>

text \<open>
  A \<open>cfg\<close> is an interprocedural control-flow graph over two disjoint transition
  relations, one per phenomenon:
    \<^item> \<open>intra\<close> --- ordinary context-preserving flow, labelled by an \<open>edge_action\<close> that is
      a total within-context store transformer.  Executed by \<open>edge_step\<close>.
    \<^item> \<open>calls\<close> --- context-crossing calls, labelled by a \<open>call_action\<close> and carrying the
      call-site, the callee entry node, and the continuation node.

  Nodes are procedure-aware: \<open>FunctionEntry p\<close> and \<open>FunctionResult p\<close> are first-class
  nodes, not keyed side slots.  There is no global exit node and no call/return matching
  side relation: a call edge already names its callee entry and its continuation, and a
  return is an ordinary intra edge into \<open>FunctionResult p\<close>.  Calls carry incompatible
  typing from intra flow, so \<open>edge_step\<close> has no call case and \<open>intra\<close> can never carry a
  call --- by typing, not by a side condition.

  Translation from VIMP to CFG and the collecting/equation layers ride on this structure.
\<close>

subsection \<open>Nodes\<close>

datatype cfg_node =
    Statement nat
  | FunctionEntry pname
  | FunctionResult pname

instance cfg_node :: countable
  by countable_datatype

subsection \<open>Edge actions and call actions\<close>

text \<open>
  \<open>edge_action\<close> labels intra flow.  It has no call constructor: every action is a total
  store transformer within one activation, so an intra edge can never denote a call.  A
  \<open>EA_Ret e p\<close> writes the return value into \<open>ret_var\<close> in the callee's own context; its
  graph target is \<open>FunctionResult p\<close> (enforced by \<open>wf_cfg\<close>), which is why return
  summarisation is ordinary predecessor folding over \<open>FunctionResult p\<close>.

  \<open>call_action\<close> labels call edges.  \<open>CallEdge dst formals args\<close> records the caller
  destination variable, the callee's formal parameter names, and the actual arguments; the
  callee identity and the continuation are the two target nodes of the \<open>calls\<close> tuple, not
  payload of the action.  Carrying \<open>formals\<close> on the edge lets the caller-side entry transfer
  \<open>call_enter\<close> bind actuals to formals without consulting a procedure table, keeping the
  trace kernel independent of the source declaration environment.
\<close>

datatype edge_action =
    EA_Nop
  | EA_Assign   vname aexp
  | EA_Assume   bexp
  | EA_AssumeNot bexp
  | EA_Ret      "aexp option" pname

datatype call_action =
    CallEdge "vname option" "vname list" "aexp list"

instance edge_action :: countable
  by countable_datatype

instance call_action :: countable
  by countable_datatype

subsection \<open>CFG record: two relations\<close>

text \<open>
  \<open>calls\<close> is a four-place relation \<open>(call_site, act, callee_entry, continuation)\<close>: the
  callee entry and the continuation are ordinary nodes, kept explicit so no matching side
  relation is needed.  The flat (call-free) CFG is exactly the \<open>calls = {}\<close> fragment, so
  every fact quantified over \<open>intra\<close> is verbatim a flat-CFG fact.
\<close>

record cfg =
  intra     :: "(cfg_node \<times> edge_action \<times> cfg_node) set"
  calls     :: "(cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
  cfg_entry :: cfg_node

subsection \<open>Intra edge execution\<close>

text \<open>\<open>edge_step\<close> is the single primitive semantics of an intra action.  It is defined for
  every constructor and has no call case; guards are the only source of \<open>None\<close>.\<close>

fun edge_step :: "edge_action \<Rightarrow> store \<Rightarrow> store option" where
  "edge_step EA_Nop s = Some s"
| "edge_step (EA_Assign x a) s = Some (s(x := aval a s))"
| "edge_step (EA_Assume b) s = (if bval b s then Some s else None)"
| "edge_step (EA_AssumeNot b) s = (if bval b s then None else Some s)"
| "edge_step (EA_Ret e p) s =
     Some (s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)))"

subsection \<open>Intra-only execution paths\<close>

text \<open>
  \<open>intra_path\<close> is the reflexive-transitive closure of \<^const>\<open>edge_step\<close> along \<^const>\<open>intra\<close>
  edges, on \<open>(node, store)\<close> pairs.  It deliberately excludes \<^const>\<open>calls\<close>: an intra path
  never pushes or pops an activation, so it lifts to the collecting semantics without any
  stack-representation side condition, and to a stack-preserving CFG run at any stack.
\<close>

text \<open>One intra transition on a \<open>(node, store)\<close> pair.  \<open>intra_path\<close> is its \<^const>\<open>star\<close>, so
  reflexivity, transitivity and the induction rule come from \<^theory>\<open>HOL-IMP.Star\<close> rather than
  from a bespoke closure.  The name avoids \<open>intra_step\<close>, which is the \<^emph>\<open>source\<close>-level
  \<^const>\<open>pstep\<close> fragment.\<close>

definition cfg_intra_step :: "cfg \<Rightarrow> cfg_node \<times> store \<Rightarrow> cfg_node \<times> store \<Rightarrow> bool" where
  "cfg_intra_step g p q \<longleftrightarrow>
     (\<exists>a. (fst p, a, fst q) \<in> intra g \<and> edge_step a (snd p) = Some (snd q))"

abbreviation intra_path :: "cfg \<Rightarrow> cfg_node \<times> store \<Rightarrow> cfg_node \<times> store \<Rightarrow> bool" where
  "intra_path g \<equiv> star (cfg_intra_step g)"

lemma cfg_intra_stepI:
  "(u, a, v) \<in> intra g \<Longrightarrow> edge_step a s = Some s' \<Longrightarrow> cfg_intra_step g (u, s) (v, s')"
  by (auto simp: cfg_intra_step_def)

lemma cfg_intra_stepE:
  assumes "cfg_intra_step g (u, s) (v, s')"
  obtains a where "(u, a, v) \<in> intra g" "edge_step a s = Some s'"
  using assms by (auto simp: cfg_intra_step_def)

lemma intra_path_single:
  "(u, a, v) \<in> intra g \<Longrightarrow> edge_step a s = Some s' \<Longrightarrow> intra_path g (u, s) (v, s')"
  by (intro star_step1 cfg_intra_stepI)

lemma intra_path_nop:
  "(u, EA_Nop, v) \<in> intra g \<Longrightarrow> intra_path g (u, s) (v, s)"
  by (rule intra_path_single[where a = EA_Nop]) simp_all

text \<open>Widening the graph preserves intra paths: only membership in \<^const>\<open>intra\<close> is used.\<close>
lemma cfg_intra_step_mono:
  "cfg_intra_step g1 x y \<Longrightarrow> intra g1 \<subseteq> intra g2 \<Longrightarrow> cfg_intra_step g2 x y"
  by (auto simp: cfg_intra_step_def)

lemma intra_path_mono:
  "intra_path g1 x y \<Longrightarrow> intra g1 \<subseteq> intra g2 \<Longrightarrow> intra_path g2 x y"
  by (induction rule: star.induct) (auto intro: star.step cfg_intra_step_mono)

subsection \<open>Return-value transfer\<close>

text \<open>Return-value rehydration at the caller: write the callee's \<open>ret_var\<close> into the
  destination over the combined store (callee globals, caller locals).  It is fixed by the
  call's destination \<open>dst\<close>, which the \<open>CallEdge\<close> already records --- no side lookup.\<close>

definition combine_collect :: "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_collect gs dst s t = combine_assign dst (t ret_var) (combine_states gs s t)"

lemma combine_collect_None: "combine_collect gs None s t = combine_states gs s t"
  by (simp add: combine_collect_def)

subsection \<open>Call-entry transfer\<close>

text \<open>Caller-side entry transfer at a call.  The actuals are evaluated in the caller store,
  the callee locals are reset (\<^const>\<open>enter_state\<close>, globals preserved), and the resulting
  values are bound to the callee formals.  All payload comes from the \<open>CallEdge\<close>, so the
  transfer needs no procedure table.  This is exactly the callee-entry store produced by the
  source \<^const>\<open>pstep\<close> \<open>Call\<close> rule (see \<open>call_enter_eq_source_call_store\<close>).\<close>

definition call_enter :: "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> store \<Rightarrow> store" where
  "call_enter gs ca s =
     (case ca of CallEdge dst pars actuals \<Rightarrow>
        bind_formals pars (map (\<lambda>e. aval e s) actuals) (enter_state gs s))"

lemma call_enter_CallEdge:
  "call_enter gs (CallEdge dst pars actuals) s
     = bind_formals pars (map (\<lambda>e. aval e s) actuals) (enter_state gs s)"
  by (simp add: call_enter_def)

text \<open>A parameterless call is exactly \<^const>\<open>enter_state\<close>: no actuals to evaluate and no
  formals to bind.\<close>
lemma call_enter_Nil [simp]:
  "call_enter gs (CallEdge dst [] []) s = enter_state gs s"
  by (simp add: call_enter_CallEdge bind_formals_def)

subsection \<open>Structural selectors\<close>

definition intra_successors :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node set" where
  "intra_successors g u = {v. \<exists>a. (u, a, v) \<in> intra g}"



subsection \<open>Node set (derived, not stored)\<close>

text \<open>\<open>cfg_nodes\<close> is reconstructed from the endpoints of \<open>intra\<close>, every node occurring in
  \<open>calls\<close>, and \<open>cfg_entry\<close>.  It is not a record field.\<close>

definition cfg_nodes :: "cfg \<Rightarrow> cfg_node set" where
  "cfg_nodes g =
     {u. \<exists>a v. (u, a, v) \<in> intra g}
     \<union> {v. \<exists>u a. (u, a, v) \<in> intra g}
     \<union> {u. \<exists>act ce after. (u, act, ce, after) \<in> calls g}
     \<union> {ce. \<exists>u act after. (u, act, ce, after) \<in> calls g}
     \<union> {after. \<exists>u act ce. (u, act, ce, after) \<in> calls g}
     \<union> {cfg_entry g}"

subsection \<open>Flatness and well-formedness\<close>

definition flat_cfg :: "cfg \<Rightarrow> bool" where
  "flat_cfg g \<longleftrightarrow> calls g = {}"

text \<open>\<open>wf_cfg\<close> is structural only: call edges enter procedure-entry nodes; no intra edge
  enters a procedure-entry node (so a callee is reached only across a call); and a return
  action lands on the matching procedure result.  No compiler-correctness or
  source-semantic property is included.\<close>

definition wf_cfg :: "cfg \<Rightarrow> bool" where
  "wf_cfg g \<longleftrightarrow>
     (\<forall>u act ce after. (u, act, ce, after) \<in> calls g \<longrightarrow> (\<exists>p. ce = FunctionEntry p))
   \<and> (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow> (\<forall>p. v \<noteq> FunctionEntry p))
   \<and> (\<forall>u e p v. (u, EA_Ret e p, v) \<in> intra g \<longrightarrow> v = FunctionResult p)"

subsection \<open>Structural invariants\<close>

text \<open>Every local-edge endpoint is part of the derived node set.\<close>
lemma intra_endpoints_in_nodes:
  assumes "(u, a, v) \<in> intra g"
  shows "u \<in> cfg_nodes g" and "v \<in> cfg_nodes g"
  using assms by (auto simp: cfg_nodes_def)

text \<open>Every call site, callee entry, and continuation is part of the derived node set.\<close>
lemma call_endpoints_in_nodes:
  assumes "(u, act, ce, after) \<in> calls g"
  shows "u \<in> cfg_nodes g" and "ce \<in> cfg_nodes g" and "after \<in> cfg_nodes g"
  using assms by (auto simp: cfg_nodes_def)

text \<open>The distinguished graph entry is always part of the derived node set.\<close>
lemma cfg_entry_in_nodes: "cfg_entry g \<in> cfg_nodes g"
  by (simp add: cfg_nodes_def)

text \<open>A flat CFG has only local-edge endpoints and the distinguished entry.\<close>
lemma flat_cfg_iff: "flat_cfg g \<longleftrightarrow> calls g = {}"
  by (simp add: flat_cfg_def)

lemma cfg_nodes_flat:
  assumes "flat_cfg g"
  shows "cfg_nodes g =
           {u. \<exists>a v. (u, a, v) \<in> intra g} \<union> {v. \<exists>u a. (u, a, v) \<in> intra g} \<union> {cfg_entry g}"
  using assms by (auto simp: cfg_nodes_def flat_cfg_def)



text \<open>A well-formed call targets a procedure-entry node.\<close>
lemma wf_call_targets_entry:
  assumes "wf_cfg g" and "(u, act, ce, after) \<in> calls g"
  shows "\<exists>p. ce = FunctionEntry p"
  using assms by (fastforce simp: wf_cfg_def)

text \<open>A well-formed local edge cannot enter a procedure.  Callee entry occurs only across a call.\<close>
lemma wf_intra_not_into_entry:
  assumes "wf_cfg g" and "(u, a, v) \<in> intra g"
  shows "v \<noteq> FunctionEntry p"
  using assms by (auto simp: wf_cfg_def)

lemma wf_no_intra_call:
  assumes "wf_cfg g"
  shows "FunctionEntry p \<notin> intra_successors g u"
  using assms wf_intra_not_into_entry by (fastforce simp: intra_successors_def)

text \<open>Every edge action has a transfer; only an unsatisfied guard returns \<open>None\<close>.\<close>
lemma edge_step_fail_iff:
  "edge_step a s = None \<longleftrightarrow>
     (\<exists>b. a = EA_Assume b \<and> \<not> bval b s) \<or> (\<exists>b. a = EA_AssumeNot b \<and> bval b s)"
  by (cases a) auto

lemma edge_step_ret_target:
  assumes "wf_cfg g" and "(u, EA_Ret e p, v) \<in> intra g"
  shows "v = FunctionResult p"
  using assms by (auto simp: wf_cfg_def)



end

