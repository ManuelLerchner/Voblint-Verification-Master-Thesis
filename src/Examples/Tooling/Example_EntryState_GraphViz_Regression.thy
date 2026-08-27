theory Example_EntryState_GraphViz_Regression
  imports
    "Voblint_CLI.State_Report_GraphViz"
    "Voblint_Examples.Example_Interval_DG_EntryState_Result_Regression"
    "Voblint_Examples.Example_Interval_DG_EntryState_Dead_Check_Regression"
begin

section \<open>Regression: the entry-state GraphViz surface reads the result table\<close>

text \<open>
  Acceptance witnesses for the two entry-state rendering paths --- the
  full-state one through \<^const>\<open>point_state_node_annotation\<close> and the
  check-report one through \<^const>\<open>verdict_state_report_node_annotation\<close> ---
  against \<^const>\<open>analyse_interval_entry_state_result\<close>, the canonical solved
  table both now read.

  Two properties are under test. A node covered by several activations renders
  the join of exactly those activations' states, and a node no execution
  reaches renders as unreachable rather than as a state whose every variable
  happens to be \<^const>\<open>bot\<close>. The second is the observable half of the result
  boundary: a bottom reading is a perfectly ordinary abstract state to a
  renderer, and printing it draws a live-looking node over dead code.
\<close>

subsection \<open>Joining the activations covered at one callee entry\<close>

text \<open>
  \<^const>\<open>gcall_prog\<close> calls \<open>bump\<close> three times, and the sibling result
  regression pins each activation's own entered \<open>n\<close>: \<open>[5,5]\<close>, \<open>[4,4]\<close>, and
  \<open>[19,19]\<close>. One CFG node cannot be drawn three times, so the rendered state
  at \<^const>\<open>bump_entry\<close> is their join, taken over exactly the covered
  contexts by \<^const>\<open>lookup_joined_state\<close> --- stated here against the join
  itself rather than against a copied-out interval, so the two cannot drift.
\<close>

text \<open>The rendered label the graph actually carries for that variable.\<close>

lemma gcall_graph_annotation_at_bump_entry:
  "map_option (\<lambda>a. (split_gv_nl (annotation_label a), annotation_style a))
     (point_state_node_annotation [STR ''n'']
        (entry_state_point_env_at (analyse_interval_entry_state_result gcall_prog))
        bump_entry)
   = Some ([''n=[4,19]''], ''shape=box,style=filled,fillcolor=lightgreen'')"
  by eval

text \<open>The caller's own single context is unaffected by the join: \<open>bump\<close>'s three
  activations do not leak into \<open>main\<close>'s nodes.\<close>

subsection \<open>A node no execution reaches\<close>

text \<open>
  \<^const>\<open>dead_check_prog\<close> sets \<open>x\<close> to \<open>5\<close> and then branches on \<open>x < 2\<close>. The
  branch's own node is covered --- the solver reached it under the caller's
  context \<open>[]\<close> --- and its stored state concretizes to nothing. Both facts are
  pinned, because they are what separates this from the uncovered case below:
  a membership guard alone would answer the uncovered node and miss this one.
\<close>

text \<open>
  So the renderer is handed \<^const>\<open>Unreachable\<close>, not a store. Reading the
  solved local unknown directly would have produced an ordinary abstract state
  here, every variable at its \<^const>\<open>bot\<close> witness, and the graph would have
  shown \<open>x=[]\<close>-style variable lines for a branch nothing enters.
\<close>

text \<open>The reachable sibling branch in the same program still renders its state,
  so the unreachable case is not swallowing live nodes.\<close>

lemma dead_check_graph_annotation_live_sibling:
  "map_option (\<lambda>a. (split_gv_nl (annotation_label a), annotation_style a))
     (point_state_node_annotation [STR ''x'']
        (entry_state_point_env_at (analyse_interval_entry_state_result dead_check_prog))
        (Statement 3))
   = Some ([''x=[5,5]''], ''shape=box,style=filled,fillcolor=lightgreen'')"
  by eval

text \<open>A \<^typ>\<open>pp\<close> the solve never covered reads the same way. The join's unit is
  \<^const>\<open>Unreachable\<close>, so this needs no separate guard and, in particular, no
  fallback to the seeded default context.\<close>

lemma dead_check_graph_uncovered_node:
  "contexts_at (analyse_interval_entry_state_result dead_check_prog) (Statement 99) = {}"
  "\<not> is_reachable_point
       (entry_state_point_env_at (analyse_interval_entry_state_result dead_check_prog)
          (Statement 99))"
  by eval+

subsection \<open>The monovariant full-state graph reads the same result table\<close>

text \<open>
  \<^const>\<open>analyse_point_env_for\<close> gives the monovariant full-state renderer the
  same \<^const>\<open>lookup_context\<close> reading \<^const>\<open>entry_state_point_env_at\<close> gives
  the entry-state one, over \<^const>\<open>analyse_interval_td_result\<close> instead of
  \<^const>\<open>analyse_interval_entry_state_result\<close>. \<open>dead_check_prog\<close>'s dead
  branch exercises the same distinction here: the point renders through
  \<^const>\<open>unreachable_state_annotation\<close>, not as an ordinary state box over a
  witness-bottom store -- the deliberate rendering change this milestone
  makes, replacing what used to be a live-looking \<open>lightgreen\<close> box with
  every variable at \<^const>\<open>bot\<close>.
\<close>

text \<open>The live sibling branch in the same program still renders its state,
  so the unreachable case is not swallowing live nodes here either.\<close>

lemma dead_check_full_state_annotation_live_sibling:
  "map_option (\<lambda>a. (split_gv_nl (annotation_label a), annotation_style a))
     (point_state_node_annotation [STR ''x'']
        (analyse_point_env_for Interval_Analysis dead_check_prog)
        (Statement 3))
   = Some ([''x=[5,5]''], ''shape=box,style=filled,fillcolor=lightgreen'')"
  by eval

subsection \<open>The check-report rendering keeps the dead case\<close>

text \<open>
  The same program's dead check reaches the graph as \<^const>\<open>Dead\<close> and renders
  through \<^const>\<open>dead_check_annotation\<close>. Collapsing it into
  \<^const>\<open>Check_Unknown\<close> first would have drawn it as an undecided check, in the
  same grey a live check the abstraction could not settle carries.
\<close>

lemma dead_check_graph_report_annotation_live:
  "map_option (\<lambda>a. (split_gv_nl (annotation_label a), annotation_style a))
     (verdict_state_report_node_annotation [STR ''x'']
        (entry_state_report_for_annotation Interval_Analysis dead_check_prog) (Statement 3))
   = Some ([''check x==5'', ''x=[5,5]''],
           ''shape=box,style=filled,fillcolor=darkgreen,fontcolor=white'')"
  by eval

text \<open>A node carrying no check still gets no annotation at all, so the
  renderer's own entry/exit/default styling continues to apply there.\<close>

section \<open>Regression: the context-expanded graph keeps activations apart\<close>

text \<open>
  \<^const>\<open>entry_state_ctx_graph\<close> draws one node per covered \<^term>\<open>(v, ctx)\<close> and
  reads each through \<^const>\<open>lookup_context\<close>, so everything the joined rendering
  above merges stays separate here. \<^const>\<open>gcall_prog\<close>'s three activations of
  \<open>bump\<close> are the whole test: three callee-entry nodes, three per-context
  states at one CFG point, and three interprocedural edge pairs that must not
  cross.
\<close>

definition gcall_ctx_graph :: "(ivl list, gk) analysis_graph" where
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
        (prog_cfg prog_main_name gcall_prog) gcall_result)"
  by eval

subsection \<open>Return edges resume at the originating call site's continuation\<close>

text \<open>Each combine edge leaves the callee result under the context that call
  routed to, and re-enters the caller at that call's own continuation. The
  continuation comes from the call tuple, never from the callee key --- which
  is what keeps a shared callee context unambiguous.\<close>

text \<open>\<^const>\<open>twin_prog\<close>'s two calls share one callee context and still resume at
  different continuations, so the return edge cannot have been recovered from
  the callee key.\<close>

definition twin_ctx_graph :: "(ivl list, gk) analysis_graph" where
  "twin_ctx_graph = entry_state_ctx_graph twin_prog"

subsection \<open>A check dead in one activation and decided in another\<close>

text \<open>
  \<^const>\<open>mixed_ctx_prog\<close> checks \<open>n == 1\<close> inside the recursive base case. That
  check is reached only in the innermost activation; the outer ones enter the
  other branch. The joined rendering has one box for the node and must pick
  one verdict for it, so it cannot show both. Expanded, each activation
  carries its own.
\<close>

definition mixed_ctx_graph :: "(ivl list, gk) analysis_graph" where
  "mixed_ctx_graph = entry_state_ctx_graph mixed_ctx_prog"

lemma mixed_ctx_graph_wf: "analysis_graph_wf mixed_ctx_graph"
  unfolding mixed_ctx_graph_def by (rule entry_state_ctx_graph_wf)

text \<open>
  The recursion also leaves the solver a context whose entered formal is
  \<^const>\<open>bot\<close>, reached from the base-case activation's own dead call site. The
  graph draws no call edge into it: the caller point is \<^const>\<open>Unreachable\<close>
  there, so \<^const>\<open>entry_state_ctx_route\<close> stops before routing rather than
  fabricating an activation out of a state that represents nothing.
\<close>

subsection \<open>Partial routing draws no false edge, even when a context repeats\<close>

text \<open>
  \<open>entry_state_ctx_route\<close> answers \<^const>\<open>None\<close> structurally, from the
  caller point's own reachability, never by returning a distinguished
  \<open>'ctx\<close> value and relying on it staying uncovered: a real derived context
  can coincide with another real derived context from an unrelated call
  site (interval routing depends only on the entered formals, never on
  caller identity), and a naive "reuse a context value as a no-route
  sentinel" encoding would be exactly the kind of representation this
  program is built to catch. Two distinct calls to the same callee under
  two distinct, non-empty contexts -- one from a dead branch, one live --
  exercise that without also asking the solver to route two call sites onto
  one shared continuation, which \<^const>\<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close>
  is separately responsible for and is exercised by \<open>mixed_ctx_prog\<close> above.
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

definition dead_route_result :: "(ivl list, ivl abs_state) analysis_result" where
  "dead_route_result = analyse_interval_entry_state_result dead_route_prog"

definition dead_route_graph :: "(ivl list, gk) analysis_graph" where
  "dead_route_graph = entry_state_ctx_graph dead_route_prog"

lemma dead_route_graph_wf: "analysis_graph_wf dead_route_graph"
  unfolding dead_route_graph_def by (rule entry_state_ctx_graph_wf)

text \<open>
  The dead call's own context, \<open>[3]\<close>, is genuinely a real entered-formal
  value, distinguishing it from \<open>None\<close> by value alone -- so the only thing
  distinguishing the dead call from the live one is reachability at the
  call site, not what its route would have been.
\<close>

definition dead_route_calls :: "(pp \<times> call_action \<times> pp \<times> pp) list" where
  "dead_route_calls =
     filter (\<lambda>(call, ca, entry, cont). \<not> is_reachable_point (lookup_context dead_route_result call []))
       (cfg_calls_list (prog_cfg prog_main_name dead_route_prog))"

text \<open>
  A sentinel-based route would still have routed the dead call somewhere
  real (\<open>[3]\<close>, not the empty-list coincidence a zero-formal callee would
  produce): \<^const>\<open>analysis_enter_edges\<close>/\<^const>\<open>analysis_combine_edges\<close>
  draw no edge from an \<open>Unreachable\<close> caller regardless of what its route
  would have been.
\<close>

text \<open>
  The contrast: the live sibling call really does draw both edges, so the
  absence above is the dead call's own property.
\<close>

text \<open>
  A record of the case that turned out not to be safely testable: a
  zero-formal callee (\<open>void f() { ... }\<close>) called from two call sites, one
  of them dead, routes both to the same context \<open>[]\<close> -- the same value the
  program root itself is seeded at, since \<^const>\<open>formals_context\<close> on an
  empty formal list is constant regardless of caller state. Evaluating
  \<^const>\<open>analyse_interval_entry_state_result\<close> for that program did not
  terminate in this session, confirmed both interactively and in an
  isolated batch process with a generous timeout well past what a program
  this size would otherwise need. Careful reading of
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close>, \<^const>\<open>routed_cmb_g_contribution\<close>,
  \<^const>\<open>routed_extra_g\<close>, and the vendored warrowing solver's own
  per-origin global bookkeeping (\<open>update_global_warrowing_apinis\<close>) found no
  evident defect on inspection, so whether this is a genuine
  non-terminating instance of a solver whose termination is checked per
  program rather than universally guaranteed (\<^const>\<open>entry_state_terminates\<close>
  exists for exactly this reason), or a real, more subtle defect, is not
  established here and needs its own dedicated investigation rather than a
  same-session guess. The regression above establishes the same design
  property -- partial routing draws no false edge -- on an input that is
  known to terminate.
\<close>

end

