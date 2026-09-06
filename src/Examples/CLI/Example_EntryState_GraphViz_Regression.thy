theory Example_EntryState_GraphViz_Regression
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.State_Report_GraphViz"
    "Voblint_Examples_Interval.Example_Interval_DG_EntryState_Result_Regression"
    "Voblint_Examples_Interval.Example_Interval_DG_EntryState_Dead_Check_Regression"
begin

section \<open>Regression: the context-expanded graph's well-formedness and coverage\<close>

text \<open>
  \<^const>\<open>entry_state_ctx_graph\<close> draws one node per covered \<^term>\<open>(v, ctx)\<close> pair.
  Its rendering-observable behavior (which nodes/edges a real \<open>--graph-snapshot\<close> draws,
  for a shared callee context, a mixed dead/live branch, and a dead call site) is covered
  by \<^verbatim>\<open>tests/regression/11-graph-snapshot/\<close> fixtures directly. What survives here is the
  internal well-formedness (\<^const>\<open>analysis_graph_wf\<close>) and result-table coverage
  (\<^const>\<open>contextual_result_domain\<close>/\<^const>\<open>result_contexts_at\<close>) obligations, neither of
  which a rendered graph's text output could check.
\<close>

definition gcall_ctx_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "gcall_ctx_graph = entry_state_ctx_graph gcall_prog"

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
  "set (result_contexts_at (entry_state_ctx_graph_config gcall_prog) gcall_result bump_entry)
     = contexts_at gcall_result bump_entry"
  "set (result_contexts_at (entry_state_ctx_graph_config gcall_prog) gcall_result (Statement 4))
     = contexts_at gcall_result (Statement 4)"
  by eval+

text \<open>And the domain the graph is built over never names a key the solver did
  not reach: coverage is a property of the drawn domain, checkable against the
  table without inspecting how the domain was ordered.\<close>

lemma gcall_ctx_graph_domain_is_covered:
  "list_all (\<lambda>x. case x of Inl pc \<Rightarrow> pc \<in> result_keys gcall_result | Inr _ \<Rightarrow> True)
     (contextual_result_domain (entry_state_ctx_graph_config gcall_prog)
        (prog_cfg gcall_prog) gcall_result)"
  by eval

text \<open>
  \<^const>\<open>mixed_ctx_prog\<close> checks \<open>n == 1\<close> inside the recursive base case, reached
  only in the innermost activation; drawing it is
  \<^verbatim>\<open>tests/regression/11-graph-snapshot/13-expanded_recursive_dead_branch.vimp\<close>'s job.
  Its well-formedness stays here.
\<close>

definition mixed_ctx_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "mixed_ctx_graph = entry_state_ctx_graph mixed_ctx_prog"

lemma mixed_ctx_graph_wf: "analysis_graph_wf mixed_ctx_graph"
  unfolding mixed_ctx_graph_def by (rule entry_state_ctx_graph_wf)

text \<open>
  \<open>dead_route_prog\<close> calls one callee from a dead call site and a live one,
  both under real (non-\<open>None\<close>-sentinel) contexts; the routing/edge-absence
  claims that distinguish them are
  \<^verbatim>\<open>tests/regression/11-graph-snapshot/09-expanded_dead_route.vimp\<close>'s job.
\<close>

definition dead_route_prog :: imp_prog where
  "dead_route_prog = program {
     void f(n) { return n }
     void main() {
       x := 5;
       if (x < 2) {
         a := f(3)
       } else {
         skip
       };
       b := f(7);
       __voblint_check(b == 7)
     }
   }"

definition dead_route_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "dead_route_graph = entry_state_ctx_graph dead_route_prog"

lemma dead_route_graph_wf: "analysis_graph_wf dead_route_graph"
  unfolding dead_route_graph_def by (rule entry_state_ctx_graph_wf)

text \<open>
  A record of a case that turned out not to be safely testable: a
  zero-formal callee (\<open>void f() { ... }\<close>) called from two call sites, one
  of them dead, routes both to the same context \<open>[]\<close> -- the same value the
  program root itself is seeded at, since \<^const>\<open>formals_context\<close> on an
  empty formal list is constant regardless of caller state. Evaluating
  \<^const>\<open>analyse_interval_entry_state_result\<close> for that program did not
  terminate in this session, confirmed both interactively and in an
  isolated batch process with a generous timeout well past what a program
  this size would otherwise need. Careful reading of
  \<^const>\<open>routed_node_rhs_buffered\<close>, \<^const>\<open>routed_call_tree\<close>,
  \<^const>\<open>routed_entry_seed_tree\<close>, and the vendored warrowing solver's own
  per-origin global bookkeeping (\<open>update_global_warrowing_apinis\<close>) found no
  evident defect on inspection, so whether this is a genuine
  non-terminating instance of a solver whose termination is checked per
  program rather than universally guaranteed (\<^const>\<open>entry_state_terminates\<close>
  exists for exactly this reason), or a real, more subtle defect, is not
  established here and needs its own dedicated investigation rather than a
  same-session guess. \<open>dead_route_graph_wf\<close> above establishes the same
  design property -- partial routing draws no false edge -- on an input that
  is known to terminate.
\<close>

end
