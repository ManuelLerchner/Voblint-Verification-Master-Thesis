theory State_Report_Entry_Ctx
  imports State_Report_Graph
begin

section \<open>The context-expanded entry-state graph\<close>

text \<open>
  Everything above renders one visual node per \<^typ>\<open>pp\<close> and shows
  \<^const>\<open>lookup_joined_state\<close> there. That join is lossy in exactly the way the
  entry-state analysis is precise: three activations of one callee collapse
  into one box, and a point dead in one activation and live in another reads
  as live.

  The expanded rendering draws one node per covered \<^term>\<open>(v, ctx)\<close> instead
  and annotates each through \<^const>\<open>lookup_context\<close>, so no join takes place at
  all. The generic contextual builder already carries every part of this:
  the node set is \<^const>\<open>contextual_result_domain\<close> over the same table, the
  routing hook is \<^const>\<open>entry_state_callee_ctx\<close>, and intra, enter, combine and
  call-to-return edges come from \<^const>\<open>build_analysis_graph\<close> unchanged.
\<close>

text \<open>
  Two values carry the domain: \<open>enter\<close>, its procedure-entry transfer, and
  \<open>into\<close>, the injection of its carrier into \<^typ>\<open>abstract_value\<close>. The first
  decides which callee context a call edge routes to and cannot be projected
  away --- an entry-state context \<^emph>\<open>is\<close> a list of this domain's values --- so
  the graph stays typed in \<open>'a\<close>. The second is only display, and past it every
  hook below is domain-agnostic.

  The state source is \<^const>\<open>lookup_context\<close> at the node's own key, so the
  solution the builder is handed is already the result table, not the
  solver's map. \<^const>\<open>Inr\<close> is answered \<^const>\<open>Bot\<close>: the entry-state
  system carries every program variable in the local unknown, so its
  solver-global slots hold no program state to draw, and
  \<^const>\<open>contextual_result_domain\<close> contributes no \<^const>\<open>GlobalNode\<close> keys either.
\<close>

definition entry_state_ctx_sol ::
    "('a list, 'a abs_state) analysis_result
       \<Rightarrow> pp \<times> 'a list + (unit, 'a list) routed_gk \<Rightarrow> 'a abs_state lifted" where
  "entry_state_ctx_sol r k =
     (case k of Inl (v, ctx) \<Rightarrow> lookup_context r v ctx | Inr _ \<Rightarrow> Bot)"

text \<open>
  The routing hook ignores its call site and its caller context, matching
  \<^const>\<open>entry_state_route_gen\<close>, and takes the caller's own reachability case
  split before routing: an \<^const>\<open>Bot\<close> caller answers \<^const>\<open>None\<close> directly, so
  \<^const>\<open>analysis_enter_edges\<close> and \<^const>\<open>analysis_combine_edges\<close> draw no edge at
  all, and \<^const>\<open>callee_ctx_of\<close> is never applied to a state that represents
  nothing --- which is also what makes its \<^const>\<open>is_empty_state\<close> test agree with
  the restricted one Interval states for itself.
\<close>

definition entry_state_ctx_route ::
    "((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> 'a list \<Rightarrow> call_action
       \<Rightarrow> ('a::executable_domain) abs_state lifted \<Rightarrow> 'a list option" where
  "entry_state_ctx_route enter p u ctx ca d =
     (case d of Bot \<Rightarrow> None
      | Lifted st \<Rightarrow> callee_ctx_of enter (declared_global p) ca st)"

definition entry_state_ctx_graph_config ::
    "((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list
        \<Rightarrow> ('a::executable_domain) abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> ('a \<Rightarrow> abstract_value) \<Rightarrow> imp_prog
       \<Rightarrow> ('a list, (unit, 'a list) routed_gk, 'a abs_state lifted, 'a abs_state lifted)
            analysis_graph_config" where
  "entry_state_ctx_graph_config enter into p =
    \<lparr> local_of = id,
      route = entry_state_ctx_route enter p,
      is_dead_local = (\<lambda>d. case d of Bot \<Rightarrow> True | Lifted _ \<Rightarrow> False),
      context_key = ctx_key_of into,
      show_context = ctx_show_of into,
      locals_for_pp = (\<lambda>v.
        let sc = compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p) (prog_cfg p) v
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>v.
        scope_return_slot (compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p) (prog_cfg p) v)),
      globals_to_show = [],
      show_local = (\<lambda>v ctx vars d.
        case d of Bot \<Rightarrow> [STR ''unreachable'']
        | Lifted st \<Rightarrow>
            map (\<lambda>x. x + STR ''='' + string_of_abstract_value (into (st x))) vars),
      format_return = (\<lambda>v ctx ret d.
        case d of Bot \<Rightarrow> []
        | Lifted st \<Rightarrow>
            if is_top_abstract_value (into (st ret)) then []
            else [STR ''ret='' + string_of_abstract_value (into (st ret))]),
      show_global = (\<lambda>k vars s. []),
      show_global_key = (\<lambda>k. STR ''Global''),
      is_shared_global = (\<lambda>k. False),
      show_internal_globals = False,
      owner_of = compiled_owner_of (prog_table p) (prog_procs p),
      cluster_label = (\<lambda>owner ctx. owner + STR '' / '' + ctx_show_of into ctx),
      source_text = Some (pretty_string_of_program (prog_table p) (prog_procs p) (prog_main p) []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

subsection \<open>Per-context check verdicts\<close>

text \<open>
  A check's verdict is per activation, so the annotation hook takes the
  context along with the point. Nothing classifies a second time:
  \<^const>\<open>classify_point\<close> against \<^const>\<open>lookup_context\<close> at that key is exactly the
  element \<^const>\<open>classify_checks_ctx\<close> would put in its own observation set for
  the same key, at the same classifier, over the same table. Consulting the
  table directly keeps the annotation a lookup rather than a scan of a report
  built beside it.
\<close>

definition check_cond_at :: "cfg \<Rightarrow> pp \<Rightarrow> exp option" where
  "check_cond_at g v =
     map_option (\<lambda>(u, a, w). ea_check_cond a)
       (find (\<lambda>(u, a, w). u = v \<and> is_EA_Check a) (cfg_intra_list g))"

definition entry_state_ctx_check_annotation ::
    "(exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result) \<Rightarrow> ('a list, 'a abs_state) analysis_result
       \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> 'a list \<Rightarrow> graph_node_annotation option" where
  "entry_state_ctx_check_annotation classify r g v ctx =
     (case check_cond_at g v of
        None \<Rightarrow> None
      | Some cnd \<Rightarrow>
          Some (case classify_point classify cnd (lookup_context r v ctx) of
                  Dead \<Rightarrow> dead_check_annotation cnd
                | Decided res \<Rightarrow> check_result_annotation res cnd))"

text \<open>
  Every projection below takes the already-solved table as an argument. That is
  what keeps a rendering to one solve once it reaches generated code: a body
  naming an analyser once for the node set, once for the states and once for the
  annotations is three calls in the emitted OCaml, hence three solves of the same
  equation system.
\<close>

definition entry_state_ctx_annotated_config ::
    "((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> ('a \<Rightarrow> abstract_value) \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> ('a::executable_domain list, 'a abs_state) analysis_result \<Rightarrow> imp_prog
       \<Rightarrow> ('a list, (unit, 'a list) routed_gk, 'a abs_state lifted, 'a abs_state lifted)
            analysis_graph_config" where
  "entry_state_ctx_annotated_config enter into classify r p =
     entry_state_ctx_graph_config enter into p
       \<lparr> node_annotation := entry_state_ctx_check_annotation classify r (prog_cfg p) \<rparr>"

definition entry_state_ctx_graph_of ::
    "((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> ('a \<Rightarrow> abstract_value) \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> ('a::executable_domain list, 'a abs_state) analysis_result \<Rightarrow> imp_prog
       \<Rightarrow> ('a list, (unit, 'a list) routed_gk) analysis_graph" where
  "entry_state_ctx_graph_of enter into classify r p =
     build_analysis_graph (entry_state_ctx_annotated_config enter into classify r p) (prog_cfg p)
       (contextual_result_domain (entry_state_ctx_graph_config enter into p) (prog_cfg p) r)
       (entry_state_ctx_sol r)"

text \<open>The rendered graph is well-formed for every program: it is built over a compiled
  CFG, whose call sites are unique and whose edge relations are finite, which is all
  \<open>build_analysis_graph_wf\<close> asks for.\<close>

lemma entry_state_ctx_graph_wf:
  "analysis_graph_wf (entry_state_ctx_graph_of enter into classify r p)"
  unfolding entry_state_ctx_graph_of_def prog_cfg_def
  by (rule build_analysis_graph_wf
        [OF calls_source_unique_compile_prog compile_prog_finite[THEN conjunct2]])

definition entry_state_ctx_export_of ::
    "((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> ('a \<Rightarrow> abstract_value) \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> ('a::executable_domain list, 'a abs_state) analysis_result \<Rightarrow> imp_prog
       \<Rightarrow> export_graph" where
  "entry_state_ctx_export_of enter into classify r p =
     (let g = prog_cfg p;
          base = entry_state_ctx_graph_config enter into p;
          cfg = entry_state_ctx_annotated_config enter into classify r p;
          sol = entry_state_ctx_sol r
      in analysis_graph_to_export cfg g sol
           (build_analysis_graph cfg g (contextual_result_domain base g r) sol))"

definition entry_state_ctx_graph_snapshot_of ::
    "((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> ('a \<Rightarrow> abstract_value) \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> ('a::executable_domain list, 'a abs_state) analysis_result \<Rightarrow> imp_prog
       \<Rightarrow> String.literal" where
  "entry_state_ctx_graph_snapshot_of enter into classify r p =
     (let g = prog_cfg p;
          base = entry_state_ctx_graph_config enter into p;
          cfg = entry_state_ctx_annotated_config enter into classify r p;
          sol = entry_state_ctx_sol r
      in analysis_graph_to_canonical_text cfg g sol
           (build_analysis_graph cfg g (contextual_result_domain base g r) sol))"

end
