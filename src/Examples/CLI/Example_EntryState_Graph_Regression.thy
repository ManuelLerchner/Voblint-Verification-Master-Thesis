theory Example_EntryState_Graph_Regression
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.State_Report_Entry_Ctx"
    "Voblint_Examples_Interval.Example_Interval_DG_EntryState_Result_Regression"
    "Voblint_Examples_Interval.Example_Interval_DG_EntryState_Dead_Check_Regression"
begin

section \<open>Regression: the context-expanded graph's well-formedness and coverage\<close>

text \<open>
  \<^const>\<open>entry_state_ctx_graph_of\<close> draws one node per covered \<^term>\<open>(v, ctx)\<close> pair.
  The CLI graph-snapshot regressions cover rendering for shared callee contexts,
  mixed dead/live branches, and dead call sites. This theory retains the internal
  well-formedness (\<^const>\<open>analysis_graph_wf\<close>) and result-table coverage
  (\<^const>\<open>contextual_result_domain\<close>/\<^const>\<open>result_contexts_at\<close>) obligations, which
  rendered text cannot check.
\<close>

text \<open>
  The expanded builder takes the domain's entry transfer, its injection into
  \<^typ>\<open>abstract_value\<close> and its classifier, so that one renderer serves every
  domain. Interval is the domain these regressions analyse; fixing its three
  values once here keeps the obligations below about the graphs rather than
  about the instantiation.
\<close>

abbreviation ivl_ctx_graph_config ::
    "imp_prog \<Rightarrow> (ivl list, (unit, ivl list) routed_gk, ivl abs_state lifted, ivl abs_state lifted)
       analysis_graph_config" where
  "ivl_ctx_graph_config p \<equiv> entry_state_ctx_graph_config enter_ivl_for IntervalValue p"

abbreviation ivl_ctx_graph ::
    "imp_prog \<Rightarrow> (ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "ivl_ctx_graph p \<equiv>
     entry_state_ctx_graph_of enter_ivl_for IntervalValue interval_classify_check
       (analyse_interval_entry_state_result p) p"

definition gcall_ctx_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "gcall_ctx_graph = ivl_ctx_graph gcall_prog"

lemma gcall_ctx_graph_wf: "analysis_graph_wf gcall_ctx_graph"
  unfolding gcall_ctx_graph_def by (rule entry_state_ctx_graph_wf)

subsection \<open>The drawn domain is exactly the solver's coverage\<close>

text \<open>
  \<^const>\<open>result_contexts_at\<close> orders the covered contexts by their
  \<^const>\<open>context_key\<close>, and \<open>set_ordered_by_key\<close> gives back the set it started
  from only when that key separates them. This program's own contexts are
  checked by execution, which is what the generic lemma leaves to the caller.
\<close>

lemma gcall_ctx_graph_contexts_are_the_covered_ones:
  "set (result_contexts_at (ivl_ctx_graph_config gcall_prog) gcall_result bump_entry)
     = contexts_at gcall_result bump_entry"
  "set (result_contexts_at (ivl_ctx_graph_config gcall_prog) gcall_result (Statement 4))
     = contexts_at gcall_result (Statement 4)"
  by eval+

text \<open>And the domain the graph is built over never names a key the solver did
  not reach: coverage is a property of the drawn domain, checkable against the
  table without inspecting how the domain was ordered.\<close>

lemma gcall_ctx_graph_domain_is_covered:
  "list_all (\<lambda>x. case x of Inl pc \<Rightarrow> pc \<in> result_keys gcall_result | Inr _ \<Rightarrow> True)
     (contextual_result_domain (ivl_ctx_graph_config gcall_prog)
        (prog_cfg gcall_prog) gcall_result)"
  by eval

text \<open>
  \<^const>\<open>mixed_ctx_prog\<close> checks \<open>n == 1\<close> inside the recursive base case,
  reached only in the innermost activation. The expanded-recursion snapshot
  regression covers its rendered shape; its well-formedness stays here.
\<close>

definition mixed_ctx_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "mixed_ctx_graph = ivl_ctx_graph mixed_ctx_prog"

lemma mixed_ctx_graph_wf: "analysis_graph_wf mixed_ctx_graph"
  unfolding mixed_ctx_graph_def by (rule entry_state_ctx_graph_wf)

text \<open>
  \<open>dead_route_prog\<close> calls one callee from a dead call site and a live one,
  both under real (non-\<open>None\<close>-sentinel) contexts. The expanded dead-route
  snapshot regression covers the routing and edge-absence claims.
\<close>

definition dead_route_prog :: imp_prog where
  "dead_route_prog = program {
     fun f(n) { return n; }
     fun main() {
       x = 5;
       if (x < 2) {
         a = f(3);
       }
       b = f(7);
       __voblint_check(b == 7);
     }
   }"

definition dead_route_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "dead_route_graph = ivl_ctx_graph dead_route_prog"

lemma dead_route_graph_wf: "analysis_graph_wf dead_route_graph"
  unfolding dead_route_graph_def by (rule entry_state_ctx_graph_wf)

text \<open>
  The witness uses one formal parameter so distinct caller states yield
  distinct entry-state contexts. A zero-formal callee maps every call to the
  same context \<open>[]\<close> and therefore cannot witness route separation.
  \<open>dead_route_graph_wf\<close> establishes that partial routing draws no false edge.
\<close>

end
