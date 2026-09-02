theory Example_EntryState_GraphViz_Regression
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.State_Report_GraphViz"
    "Voblint_Examples.Example_Interval_DG_EntryState_Result_Regression"
    "Voblint_Examples.Example_Interval_DG_EntryState_Dead_Check_Regression"
begin

section \<open>Regression: the entry-state GraphViz surface reads the result table\<close>

text \<open>
  Acceptance witnesses for the two entry-state rendering paths --- the
  full-state one through \<^const>\<open>point_node_annotation\<close> and the
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

lemma gcall_graph_state_at_bump_entry_is_context_join:
  "map_lift (\<lambda>st. st (STR ''n''))
     (entry_state_point_env_at (analyse_interval_entry_state_result gcall_prog) bump_entry)
   = Lifted (IntervalValue
       (Ivl (Fin 5) (Fin 5) \<squnion> Ivl (Fin 4) (Fin 4) \<squnion> Ivl (Fin 19) (Fin 19)))"
  by eval

text \<open>The rendered label the graph actually carries for that variable.\<close>

lemma gcall_graph_annotation_at_bump_entry:
  "map_option (\<lambda>a. (split_gv_nl (annotation_label a), annotation_style a))
     (point_node_annotation [STR ''n'']
        (entry_state_point_env_at (analyse_interval_entry_state_result gcall_prog))
        bump_entry)
   = Some ([''n=[4,19]''], ''shape=box,style=filled,fillcolor=lightgreen'')"
  by eval

text \<open>The caller's own single context is unaffected by the join: \<open>bump\<close>'s three
  activations do not leak into \<open>main\<close>'s nodes.\<close>

lemma gcall_graph_state_after_first_return:
  "map_lift (\<lambda>st. st (STR ''a''))
     (entry_state_point_env_at (analyse_interval_entry_state_result gcall_prog) (Statement 5))
   = Lifted (IntervalValue (Ivl (Fin 15) (Fin 15)))"
  by eval

subsection \<open>A node no execution reaches\<close>

text \<open>
  \<^const>\<open>dead_check_prog\<close> sets \<open>x\<close> to \<open>5\<close> and then branches on \<open>x < 2\<close>. The
  branch's own node is covered --- the solver reached it under the caller's
  context \<open>[]\<close> --- and its stored state concretizes to nothing. Both facts are
  pinned, because they are what separates this from the uncovered case below:
  a membership guard alone would answer the uncovered node and miss this one.
\<close>

lemma dead_check_graph_node_covered:
  "(Statement 2, []) \<in> result_keys (analyse_interval_entry_state_result dead_check_prog)"
  by eval

lemma dead_check_graph_node_not_live:
  "\<not> node_live_ex (analyse_interval_entry_state_result dead_check_prog) (Statement 2)"
  by eval

text \<open>
  So the renderer is handed \<^const>\<open>Bot\<close>, not a store. Reading the
  solved local unknown directly would have produced an ordinary abstract state
  here, every variable at its \<^const>\<open>bot\<close> witness, and the graph would have
  shown \<open>x=[]\<close>-style variable lines for a branch nothing enters.
\<close>

lemma dead_check_graph_state_unreachable:
  "\<not> is_reachable_point
       (entry_state_point_env_at (analyse_interval_entry_state_result dead_check_prog)
          (Statement 2))"
  by eval

lemma dead_check_graph_annotation_unreachable:
  "point_node_annotation (program_vars dead_check_prog)
     (entry_state_point_env_at (analyse_interval_entry_state_result dead_check_prog))
     (Statement 2)
   = Some unreachable_state_annotation"
  by eval

text \<open>The reachable sibling branch in the same program still renders its state,
  so the unreachable case is not swallowing live nodes.\<close>

lemma dead_check_graph_annotation_live_sibling:
  "map_option (\<lambda>a. (split_gv_nl (annotation_label a), annotation_style a))
     (point_node_annotation [STR ''x'']
        (entry_state_point_env_at (analyse_interval_entry_state_result dead_check_prog))
        (Statement 3))
   = Some ([''x=[5,5]''], ''shape=box,style=filled,fillcolor=lightgreen'')"
  by eval

text \<open>A \<^typ>\<open>pp\<close> the solve never covered reads the same way. The join's unit is
  \<^const>\<open>Bot\<close>, so this needs no separate guard and, in particular, no
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

lemma dead_check_full_state_unreachable:
  "\<not> is_reachable_point (analyse_point_env_for Interval_Analysis dead_check_prog (Statement 2))"
  by eval

lemma dead_check_full_state_annotation_unreachable:
  "point_node_annotation (program_vars dead_check_prog)
     (analyse_point_env_for Interval_Analysis dead_check_prog)
     (Statement 2)
   = Some unreachable_state_annotation"
  by eval

text \<open>The live sibling branch in the same program still renders its state,
  so the unreachable case is not swallowing live nodes here either.\<close>

lemma dead_check_full_state_annotation_live_sibling:
  "map_option (\<lambda>a. (split_gv_nl (annotation_label a), annotation_style a))
     (point_node_annotation [STR ''x'']
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

lemma dead_check_graph_report_verdicts:
  "map (\<lambda>(v, cnd, verdict, st). (v, verdict))
     (entry_state_report_for_annotation Interval_Analysis dead_check_prog)
   = [(Statement 2, Dead), (Statement 3, Decided Check_Proved)]"
  by eval

lemma dead_check_graph_report_annotation_dead:
  "verdict_state_report_node_annotation [STR ''x'']
     (entry_state_report_for_annotation Interval_Analysis dead_check_prog) (Statement 2)
   = Some (dead_check_annotation (exp.Eq (V (STR ''x'')) (exp.N 99)))"
  by eval

lemma dead_check_graph_report_annotation_live:
  "map_option (\<lambda>a. (split_gv_nl (annotation_label a), annotation_style a))
     (verdict_state_report_node_annotation [STR ''x'']
        (entry_state_report_for_annotation Interval_Analysis dead_check_prog) (Statement 3))
   = Some ([''check x==5'', ''x=[5,5]''],
           ''shape=box,style=filled,fillcolor=darkgreen,fontcolor=white'')"
  by eval

text \<open>A node carrying no check still gets no annotation at all, so the
  renderer's own entry/exit/default styling continues to apply there.\<close>

lemma dead_check_graph_report_annotation_absent:
  "verdict_state_report_node_annotation [STR ''x'']
     (entry_state_report_for_annotation Interval_Analysis dead_check_prog) (Statement 0) = None"
  by eval

section \<open>Regression: the context-expanded graph keeps activations apart\<close>

text \<open>
  \<^const>\<open>entry_state_ctx_graph\<close> draws one node per covered \<^term>\<open>(v, ctx)\<close> and
  reads each through \<^const>\<open>lookup_context\<close>, so everything the joined rendering
  above merges stays separate here. \<^const>\<open>gcall_prog\<close>'s three activations of
  \<open>bump\<close> are the whole test: three callee-entry nodes, three per-context
  states at one CFG point, and three interprocedural edge pairs that must not
  cross.
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

subsection \<open>One node per activation of the callee\<close>

lemma gcall_ctx_graph_callee_instances:
  "LocalNode bump_entry gcall_ctx_first \<in> set (analysis_graph_nodes gcall_ctx_graph)"
  "LocalNode bump_entry gcall_ctx_second \<in> set (analysis_graph_nodes gcall_ctx_graph)"
  "LocalNode bump_entry gcall_ctx_third \<in> set (analysis_graph_nodes gcall_ctx_graph)"
  by eval+

text \<open>The root context is \<open>main\<close>'s, and no callee node is materialized under
  it, so the expanded graph invents no activation the solver never had.\<close>

lemma gcall_ctx_graph_no_callee_under_root:
  "LocalNode bump_entry [] \<notin> set (analysis_graph_nodes gcall_ctx_graph)"
  by eval

subsection \<open>Per-activation states at one CFG point\<close>

text \<open>\<open>Statement 0\<close> is \<open>bump\<close>'s own first statement. Each activation reads its
  own entered \<open>n\<close> there, individually pinned --- the joined view one section
  up would answer the single interval spanning all three.\<close>

lemma gcall_ctx_graph_states_per_context:
  "map (\<lambda>ctx. map_lift (\<lambda>st. st (STR ''n''))
          (lookup_context gcall_result (Statement 0) ctx))
     [gcall_ctx_first, gcall_ctx_second, gcall_ctx_third]
   = [Lifted (Ivl (Fin 5) (Fin 5)),
      Lifted (Ivl (Fin 4) (Fin 4)),
      Lifted (Ivl (Fin 19) (Fin 19))]"
  by eval

lemma gcall_ctx_graph_states_are_not_the_join:
  "map_lift (\<lambda>st. st (STR ''n'')) (lookup_joined_state gcall_result (Statement 0))
   = Lifted (Ivl (Fin 4) (Fin 19))"
  by eval

subsection \<open>Call edges land on their own call site's context\<close>

lemma gcall_ctx_graph_enter_edges:
  "filter (\<lambda>e. case e of (_, EnterEdge _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
     (analysis_graph_edges gcall_ctx_graph)
   = [(LocalNode (Statement 4) [], EnterEdge ''bump'' gcall_call_first,
       LocalNode bump_entry gcall_ctx_first),
      (LocalNode (Statement 5) [], EnterEdge ''bump'' gcall_call_second,
       LocalNode bump_entry gcall_ctx_second),
      (LocalNode (Statement 9) [], EnterEdge ''bump'' gcall_call_third,
       LocalNode bump_entry gcall_ctx_third)]"
  by eval

text \<open>Stated as an absence too, not only as a list: a builder that paired call
  sites with covered callee contexts by position, or drew every call site to
  every covered activation, would still satisfy a purely positive test that
  named only the edges it does draw.\<close>

lemma gcall_ctx_graph_no_cross_enter_edge:
  "(LocalNode (Statement 4) [], EnterEdge ''bump'' gcall_call_first,
    LocalNode bump_entry gcall_ctx_third)
     \<notin> set (analysis_graph_edges gcall_ctx_graph)"
  "(LocalNode (Statement 9) [], EnterEdge ''bump'' gcall_call_third,
    LocalNode bump_entry gcall_ctx_first)
     \<notin> set (analysis_graph_edges gcall_ctx_graph)"
  by eval+

subsection \<open>Return edges resume at the originating call site's continuation\<close>

text \<open>Each combine edge leaves the callee result under the context that call
  routed to, and re-enters the caller at that call's own continuation. The
  continuation comes from the call tuple, never from the callee key --- which
  is what keeps a shared callee context unambiguous.\<close>

lemma gcall_ctx_graph_combine_edges:
  "filter (\<lambda>e. case e of (_, CombineEdge _ _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
     (analysis_graph_edges gcall_ctx_graph)
   = [(LocalNode (FunctionResult (STR ''bump'')) gcall_ctx_first,
       CombineEdge (Statement 4) (Some (STR ''a'')) (Some (STR ''#ret'')),
       LocalNode (Statement 5) []),
      (LocalNode (FunctionResult (STR ''bump'')) gcall_ctx_second,
       CombineEdge (Statement 5) (Some (STR ''b'')) (Some (STR ''#ret'')),
       LocalNode (Statement 6) []),
      (LocalNode (FunctionResult (STR ''bump'')) gcall_ctx_third,
       CombineEdge (Statement 9) (Some (STR ''c'')) (Some (STR ''#ret'')),
       LocalNode (Statement 10) [])]"
  by eval

text \<open>\<^const>\<open>twin_prog\<close>'s two calls share one callee context and still resume at
  different continuations, so the return edge cannot have been recovered from
  the callee key.\<close>

definition twin_ctx_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "twin_ctx_graph = entry_state_ctx_graph twin_prog"

lemma twin_ctx_graph_combine_edges_are_call_site_derived:
  "map (\<lambda>e. case e of (LocalNode _ ctx, CombineEdge call _ _, LocalNode cont _) \<Rightarrow>
               (call, ctx, cont))
     (filter (\<lambda>e. case e of (_, CombineEdge _ _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
       (analysis_graph_edges twin_ctx_graph))
   = [(Statement 2, [Ivl (Fin 5) (Fin 5)], Statement 3),
      (Statement 3, [Ivl (Fin 5) (Fin 5)], Statement 4)]"
  by eval

subsection \<open>Intra edges stay inside one activation\<close>

lemma gcall_ctx_graph_intra_edges_per_context:
  "filter (\<lambda>e. case e of (LocalNode v _, IntraEdge _, _) \<Rightarrow> v = Statement 0 | _ \<Rightarrow> False)
     (analysis_graph_edges gcall_ctx_graph)
   = [(LocalNode (Statement 0) gcall_ctx_third,
       IntraEdge (EA_Assign (STR ''g'') (Plus (V (STR ''g'')) (V (STR ''n'')))),
       LocalNode (Statement 1) gcall_ctx_third),
      (LocalNode (Statement 0) gcall_ctx_second,
       IntraEdge (EA_Assign (STR ''g'') (Plus (V (STR ''g'')) (V (STR ''n'')))),
       LocalNode (Statement 1) gcall_ctx_second),
      (LocalNode (Statement 0) gcall_ctx_first,
       IntraEdge (EA_Assign (STR ''g'') (Plus (V (STR ''g'')) (V (STR ''n'')))),
       LocalNode (Statement 1) gcall_ctx_first)]"
  by eval

lemma gcall_ctx_graph_no_cross_context_intra_edge:
  "(LocalNode (Statement 0) gcall_ctx_first,
    IntraEdge (EA_Assign (STR ''g'') (Plus (V (STR ''g'')) (V (STR ''n'')))),
    LocalNode (Statement 1) gcall_ctx_second)
     \<notin> set (analysis_graph_edges gcall_ctx_graph)"
  by eval

subsection \<open>A check dead in one activation and decided in another\<close>

text \<open>
  \<^const>\<open>mixed_ctx_prog\<close> checks \<open>n == 1\<close> inside the recursive base case. That
  check is reached only in the innermost activation; the outer ones enter the
  other branch. The joined rendering has one box for the node and must pick
  one verdict for it, so it cannot show both. Expanded, each activation
  carries its own.
\<close>

definition mixed_ctx_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "mixed_ctx_graph = entry_state_ctx_graph mixed_ctx_prog"

lemma mixed_ctx_graph_wf: "analysis_graph_wf mixed_ctx_graph"
  unfolding mixed_ctx_graph_def by (rule entry_state_ctx_graph_wf)

lemma mixed_ctx_graph_check_live_and_dead:
  "entry_state_ctx_check_annotation (prog_cfg mixed_ctx_prog)
     (analyse_interval_entry_state_result mixed_ctx_prog) (Statement 1) [Ivl (Fin 1) (Fin 1)]
   = Some (check_result_annotation Check_Proved (exp.Eq (V (STR ''n'')) (exp.N 1)))"
  "entry_state_ctx_check_annotation (prog_cfg mixed_ctx_prog)
     (analyse_interval_entry_state_result mixed_ctx_prog) (Statement 1) [Ivl (Fin 3) (Fin 3)]
   = Some (dead_check_annotation (exp.Eq (V (STR ''n'')) (exp.N 1)))"
  by eval+

lemma mixed_ctx_graph_states_live_and_dead:
  "is_reachable_point
     (lookup_context (analyse_interval_entry_state_result mixed_ctx_prog) (Statement 1)
        [Ivl (Fin 1) (Fin 1)])"
  "\<not> is_reachable_point
     (lookup_context (analyse_interval_entry_state_result mixed_ctx_prog) (Statement 1)
        [Ivl (Fin 3) (Fin 3)])"
  by eval+

text \<open>
  The recursion also leaves the solver a context whose entered formal is
  \<^const>\<open>bot\<close>, reached from the base-case activation's own dead call site. The
  graph draws no call edge into it: the caller point is \<^const>\<open>Bot\<close>
  there, so \<^const>\<open>entry_state_ctx_route\<close> stops before routing rather than
  fabricating an activation out of a state that represents nothing.
\<close>

lemma mixed_ctx_graph_enter_edges:
  "map (\<lambda>e. case e of (LocalNode call ctx, _, LocalNode entry ctx') \<Rightarrow> (call, ctx, entry, ctx'))
     (filter (\<lambda>e. case e of (_, EnterEdge _ _, _) \<Rightarrow> True | _ \<Rightarrow> False)
       (analysis_graph_edges mixed_ctx_graph))
   = [(Statement 3, [Ivl (Fin 2) (Fin 2)], FunctionEntry (STR ''f''), [Ivl (Fin 1) (Fin 1)]),
      (Statement 3, [Ivl (Fin 3) (Fin 3)], FunctionEntry (STR ''f''), [Ivl (Fin 2) (Fin 2)]),
      (Statement 6, [], FunctionEntry (STR ''f''), [Ivl (Fin 3) (Fin 3)])]"
  by eval

lemma mixed_ctx_graph_bottom_context_is_covered_but_unentered:
  "(FunctionEntry (STR ''f''), [Ivl PlusInf MinInf])
     \<in> result_keys (analyse_interval_entry_state_result mixed_ctx_prog)"
  "(LocalNode (Statement 3) [Ivl (Fin 1) (Fin 1)],
    EnterEdge ''f'' (CallEdge (Some (STR ''r'')) [STR ''n''] [Minus (V (STR ''n'')) (exp.N 1)]),
    LocalNode (FunctionEntry (STR ''f'')) [Ivl PlusInf MinInf])
     \<notin> set (analysis_graph_edges mixed_ctx_graph)"
  by eval+

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

definition dead_route_graph :: "(ivl list, (unit, ivl list) routed_gk) analysis_graph" where
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
       (cfg_calls_list (prog_cfg dead_route_prog))"

lemma dead_route_has_exactly_one_dead_call:
  "length dead_route_calls = 1"
  by eval

lemma dead_route_dead_call_route_is_none:
  "list_all (\<lambda>(call, ca, entry, cont).
       entry_state_ctx_route dead_route_prog call [] ca
         (lookup_context dead_route_result call []) = None)
     dead_route_calls"
  by eval

text \<open>
  A sentinel-based route would still have routed the dead call somewhere
  real (\<open>[3]\<close>, not the empty-list coincidence a zero-formal callee would
  produce): \<^const>\<open>analysis_enter_edges\<close>/\<^const>\<open>analysis_combine_edges\<close>
  draw no edge from an \<open>Bot\<close> caller regardless of what its route
  would have been.
\<close>

lemma dead_route_dead_call_no_enter_edge:
  "list_all (\<lambda>(call, ca, entry, cont).
       list_all (\<lambda>(src, kind, dst).
           \<not> (src = LocalNode call [] \<and> (case kind of EnterEdge _ _ \<Rightarrow> True | _ \<Rightarrow> False)))
         (analysis_graph_edges dead_route_graph))
     dead_route_calls"
  by eval

lemma dead_route_dead_call_no_combine_edge:
  "list_all (\<lambda>(call, ca, entry, cont).
       list_all (\<lambda>(src, kind, dst).
           \<not> (dst = LocalNode cont [] \<and> (case kind of CombineEdge _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)))
         (analysis_graph_edges dead_route_graph))
     dead_route_calls"
  by eval

text \<open>
  The contrast: the live sibling call really does draw both edges, so the
  absence above is the dead call's own property.
\<close>

lemma dead_route_live_call_has_enter_and_combine_edge:
  "list_ex (\<lambda>(call, ca, entry, cont).
       is_reachable_point (lookup_context dead_route_result call []) \<and>
       list_ex (\<lambda>(src, kind, dst).
           src = LocalNode call [] \<and> (case kind of EnterEdge _ _ \<Rightarrow> True | _ \<Rightarrow> False))
         (analysis_graph_edges dead_route_graph) \<and>
       list_ex (\<lambda>(src, kind, dst).
           dst = LocalNode cont [] \<and> (case kind of CombineEdge _ _ _ \<Rightarrow> True | _ \<Rightarrow> False))
         (analysis_graph_edges dead_route_graph))
     (cfg_calls_list (prog_cfg dead_route_prog))"
  by eval

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
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close>, \<^const>\<open>routed_cmb_g\<close>,
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

