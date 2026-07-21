theory CFG_Def
  imports "Voblint_IMP2.IMP2_Proc" "HOL-Library.Countable"
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

  Translation from IMP2 to CFG and the collecting/equation layers ride on this structure.
\<close>

subsection \<open>Nodes\<close>

type_synonym pp = nat

datatype cfg_node =
    Statement pp
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

  \<open>call_action\<close> labels call edges.  \<open>CallEdge dst args\<close> records the caller destination
  variable and the actual arguments; the callee identity and the continuation are the two
  target nodes of the \<open>calls\<close> tuple, not payload of the action.
\<close>

datatype edge_action =
    EA_Nop
  | EA_Assign   vname aexp
  | EA_Assume   bexp
  | EA_AssumeNot bexp
  | EA_Ret      "aexp option" pname

datatype call_action =
    CallEdge "vname option" "aexp list"

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

subsection \<open>Return-value transfer\<close>

text \<open>Return-value rehydration at the caller: write the callee's \<open>ret_var\<close> into the
  destination over the combined store (callee globals, caller locals).  It is fixed by the
  call's destination \<open>dst\<close>, which the \<open>CallEdge\<close> already records --- no side lookup.\<close>

definition combine_collect :: "vname option \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_collect dst s t = combine_assign dst (t ret_var) (combine_states s t)"

lemma combine_collect_None: "combine_collect None s t = <s|t>"
  by (simp add: combine_collect_def)

subsection \<open>Structural selectors\<close>

definition intra_successors :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node set" where
  "intra_successors g u = {v. \<exists>a. (u, a, v) \<in> intra g}"

definition intra_predecessors :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node set" where
  "intra_predecessors g v = {u. \<exists>a. (u, a, v) \<in> intra g}"

definition call_edges_from :: "cfg \<Rightarrow> cfg_node \<Rightarrow> (call_action \<times> cfg_node \<times> cfg_node) set" where
  "call_edges_from g u = {(act, ce, after). (u, act, ce, after) \<in> calls g}"

definition call_edges_to_entry :: "cfg \<Rightarrow> cfg_node \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node) set" where
  "call_edges_to_entry g ce = {(u, act, after). (u, act, ce, after) \<in> calls g}"

definition call_continuations :: "cfg \<Rightarrow> cfg_node set" where
  "call_continuations g = {after. \<exists>u act ce. (u, act, ce, after) \<in> calls g}"

definition procedure_entry :: "pname \<Rightarrow> cfg_node" where
  "procedure_entry p = FunctionEntry p"

definition procedure_result :: "pname \<Rightarrow> cfg_node" where
  "procedure_result p = FunctionResult p"

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

text \<open>(1) Every \<open>intra\<close> endpoint is a node.\<close>
lemma intra_endpoints_in_nodes:
  assumes "(u, a, v) \<in> intra g"
  shows "u \<in> cfg_nodes g" and "v \<in> cfg_nodes g"
  using assms by (auto simp: cfg_nodes_def)

text \<open>(2) Every call site, callee entry, and continuation is a node.\<close>
lemma call_endpoints_in_nodes:
  assumes "(u, act, ce, after) \<in> calls g"
  shows "u \<in> cfg_nodes g" and "ce \<in> cfg_nodes g" and "after \<in> cfg_nodes g"
  using assms by (auto simp: cfg_nodes_def)

text \<open>(3) The entry is a node.\<close>
lemma cfg_entry_in_nodes: "cfg_entry g \<in> cfg_nodes g"
  by (simp add: cfg_nodes_def)

text \<open>(4) A flat CFG is exactly the call-free fragment; its nodes are the intra endpoints
  and the entry.\<close>
lemma flat_cfg_iff: "flat_cfg g \<longleftrightarrow> calls g = {}"
  by (simp add: flat_cfg_def)

lemma cfg_nodes_flat:
  assumes "flat_cfg g"
  shows "cfg_nodes g =
           {u. \<exists>a v. (u, a, v) \<in> intra g} \<union> {v. \<exists>u a. (u, a, v) \<in> intra g} \<union> {cfg_entry g}"
  using assms by (auto simp: cfg_nodes_def flat_cfg_def)

text \<open>(5) Procedure entry and procedure result are distinct nodes.\<close>
lemma procedure_entry_neq_result: "procedure_entry p \<noteq> procedure_result q"
  by (simp add: procedure_entry_def procedure_result_def)

text \<open>(6) Under \<open>wf_cfg\<close>, call edges target procedure-entry nodes.\<close>
lemma wf_call_targets_entry:
  assumes "wf_cfg g" and "(u, act, ce, after) \<in> calls g"
  shows "\<exists>p. ce = FunctionEntry p"
  using assms by (fastforce simp: wf_cfg_def)

text \<open>(9) Under \<open>wf_cfg\<close>, no intra edge enters a procedure entry: a callee is reachable
  only across a call, never by traversing \<open>intra\<close>.\<close>
lemma wf_intra_not_into_entry:
  assumes "wf_cfg g" and "(u, a, v) \<in> intra g"
  shows "v \<noteq> FunctionEntry p"
  using assms by (auto simp: wf_cfg_def)

lemma wf_no_intra_call:
  assumes "wf_cfg g"
  shows "FunctionEntry p \<notin> intra_successors g u"
  using assms wf_intra_not_into_entry by (fastforce simp: intra_successors_def)

text \<open>(10) \<open>edge_step\<close> is total on \<open>edge_action\<close>: it is defined for every constructor and
  fails only on a failed guard.\<close>
lemma edge_step_fail_iff:
  "edge_step a s = None \<longleftrightarrow>
     (\<exists>b. a = EA_Assume b \<and> \<not> bval b s) \<or> (\<exists>b. a = EA_AssumeNot b \<and> bval b s)"
  by (cases a) auto

lemma edge_step_ret_target:
  assumes "wf_cfg g" and "(u, EA_Ret e p, v) \<in> intra g"
  shows "v = FunctionResult p"
  using assms by (auto simp: wf_cfg_def)

subsection \<open>A well-formed witness: shared continuations and converging returns\<close>

text \<open>Procedure \<open>dpf\<close> reaches \<open>FunctionResult dpf\<close> from two distinct nodes (returns
  converge, (8)); it is called from two distinct sites that share one continuation
  \<open>Statement 99\<close> (continuations need not be unique, (7)).\<close>

definition dmain :: pname where "dmain = ''main''"
definition dpf :: pname where "dpf = ''f''"

definition demo_cfg :: cfg where
  "demo_cfg =
     \<lparr> intra =
         { (FunctionEntry dpf, EA_Ret None dpf, FunctionResult dpf),
           (Statement 0,      EA_Ret None dpf, FunctionResult dpf) },
       calls =
         { (Statement 10, CallEdge None [], FunctionEntry dpf, Statement 99),
           (Statement 20, CallEdge None [], FunctionEntry dpf, Statement 99) },
       cfg_entry = FunctionEntry dmain \<rparr>"

lemmas demo_defs = demo_cfg_def dmain_def dpf_def

lemma demo_wf: "wf_cfg demo_cfg"
  by (auto simp: wf_cfg_def demo_defs)

text \<open>(8) Two distinct return edges converge into one \<open>FunctionResult\<close>.\<close>
lemma demo_returns_converge:
  "(FunctionEntry dpf, EA_Ret None dpf, FunctionResult dpf) \<in> intra demo_cfg"
  "(Statement 0, EA_Ret None dpf, FunctionResult dpf) \<in> intra demo_cfg"
  "FunctionEntry dpf \<noteq> Statement 0"
  by (simp_all add: demo_defs)

text \<open>(7) Two distinct call sites share one continuation.\<close>
lemma demo_shared_continuation:
  "(Statement 10, CallEdge None [], FunctionEntry dpf, Statement 99) \<in> calls demo_cfg"
  "(Statement 20, CallEdge None [], FunctionEntry dpf, Statement 99) \<in> calls demo_cfg"
  "Statement 10 \<noteq> Statement 20"
  by (simp_all add: demo_defs)

lemma demo_continuation_join:
  "Statement 99 \<in> call_continuations demo_cfg"
  by (auto simp: call_continuations_def demo_defs)

end

