theory State_Report_Call_String
  imports State_Report_Entry_Ctx
begin

section \<open>The context-expanded call-string graph\<close>

text \<open>
  The call-string counterpart of the entry-state section above, and the point at which the
  contextual renderer stops being per-domain. An entry-state context is the analysed
  domain's own value list (\<^typ>\<open>ivl list\<close>), so its graph configuration can only ever be
  written for one domain at a time. A call-string context is a \<^typ>\<open>cfg_node list\<close>
  (\<^theory>\<open>Voblint_Framework.Call_String_Context\<close>) --- pure call history, no domain content ---
  and every rendered state here is projected into \<^typ>\<open>abstract_value\<close> exactly as
  \<^const>\<open>analyse_point_env_for\<close> already projects the monovariant tables. Both axes of
  domain-dependence are therefore removed, and all five domains share \<open>one\<close>
  configuration, one solution reader, and one annotation hook, selected by an ordinary
  \<^typ>\<open>analysis_domain\<close> argument rather than by five parallel renderers.
\<close>

text \<open>
  Every projection below accepts one already-solved result. This is the ownership
  boundary that survives code generation: graph structure, state labels, check
  annotations, verdicts, and globals may inspect the result independently, while
  the public dispatcher is the only function allowed to run the analyser.
\<close>

definition cs_ctx_sol_of ::
    "('a \<Rightarrow> abstract_value)
       \<Rightarrow> (call_string, 'a abs_state) analysis_result
       \<Rightarrow> pp \<times> call_string + call_string_gk
       \<Rightarrow> abstract_value abs_state lifted"
where
  "cs_ctx_sol_of into r x =
     (case x of
        Inl (v, ctx) \<Rightarrow>
          map_lift (\<lambda>st. into \<circ> st) (lookup_context r v ctx)
      | Inr _ \<Rightarrow> Bot)"

definition cs_ctx_domain_of ::
    "(call_string, call_string_gk, abstract_value abs_state lifted,
        abstract_value abs_state lifted) analysis_graph_config
       \<Rightarrow> imp_prog \<Rightarrow> (call_string, 'a abs_state) analysis_result
       \<Rightarrow> ((pp \<times> call_string) + call_string_gk) list"
where
  "cs_ctx_domain_of base p r =
     contextual_result_domain base (prog_cfg p) r"

definition cs_ctx_check_annotation_of ::
    "(exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (call_string, 'a abs_state) analysis_result
       \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> call_string
       \<Rightarrow> graph_node_annotation option"
where
  "cs_ctx_check_annotation_of classify r g v ctx =
     (case check_cond_at g v of
        None \<Rightarrow> None
      | Some cnd \<Rightarrow>
          Some (case classify_point classify cnd (lookup_context r v ctx) of
                  Dead \<Rightarrow> dead_check_annotation cnd
                | Decided res \<Rightarrow> check_result_annotation res cnd))"

text \<open>
  The configuration contains presentation policy only. The result-dependent
  annotation is installed by the result-parametric configuration below, after
  the public dispatcher has selected and solved one domain.
\<close>

definition cs_ctx_graph_config ::
    "imp_prog \<Rightarrow> nat \<Rightarrow> (call_string, call_string_gk,
        abstract_value abs_state lifted, abstract_value abs_state lifted)
       analysis_graph_config"
where
  "cs_ctx_graph_config p k =
    \<lparr> local_of = id,
      route = (\<lambda>u ctx ca d. cs_graph_route k u ctx ca d),
      is_dead_local = (\<lambda>d. case d of Bot \<Rightarrow> True | Lifted _ \<Rightarrow> False),
      context_key = cs_context_key,
      show_context = cs_show_context,
      locals_for_pp = (\<lambda>v.
        let sc = compiled_procedure_scope (declared_global p) (prog_table p)
          (prog_procs p) (prog_cfg p) v
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>v.
        scope_return_slot
          (compiled_procedure_scope (declared_global p) (prog_table p)
            (prog_procs p) (prog_cfg p) v)),
      globals_to_show = [],
      show_local = (\<lambda>v ctx vars d.
        case d of Bot \<Rightarrow> [STR ''unreachable'']
        | Lifted st \<Rightarrow>
            map (\<lambda>x. x + STR ''='' + string_of_abstract_value (st x)) vars),
      format_return = (\<lambda>v ctx ret d.
        case d of Bot \<Rightarrow> []
        | Lifted st \<Rightarrow>
            if is_top_abstract_value (st ret) then []
            else [STR ''ret='' + string_of_abstract_value (st ret)]),
      show_global = (\<lambda>x vars s. []),
      show_global_key = (\<lambda>x. STR ''Global''),
      is_shared_global = (\<lambda>x. False),
      show_internal_globals = False,
      owner_of = compiled_owner_of (prog_table p) (prog_procs p),
      cluster_label = cs_cluster_label,
      source_text =
        Some (pretty_string_of_program (prog_table p) (prog_procs p)
          (prog_main p) []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

definition cs_ctx_annotated_config_of ::
    "(exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (call_string, 'a abs_state) analysis_result
       \<Rightarrow> imp_prog \<Rightarrow> nat
       \<Rightarrow> (call_string, call_string_gk, abstract_value abs_state lifted,
            abstract_value abs_state lifted) analysis_graph_config"
where
  "cs_ctx_annotated_config_of classify r p k =
     cs_ctx_graph_config p k
       \<lparr> node_annotation :=
           cs_ctx_check_annotation_of classify r (prog_cfg p) \<rparr>"

definition cs_ctx_export_of ::
    "('a \<Rightarrow> abstract_value)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (call_string, 'a abs_state) analysis_result
       \<Rightarrow> nat \<Rightarrow> imp_prog \<Rightarrow> export_graph"
where
  "cs_ctx_export_of into classify r k p =
     (let g = prog_cfg p;
          base = cs_ctx_graph_config p k;
          cfg = cs_ctx_annotated_config_of classify r p k;
          sol = cs_ctx_sol_of into r
      in analysis_graph_to_export cfg g sol
           (build_analysis_graph cfg g (cs_ctx_domain_of base p r) sol))"

definition cs_ctx_graph_snapshot_of ::
    "('a \<Rightarrow> abstract_value)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (call_string, 'a abs_state) analysis_result
       \<Rightarrow> nat \<Rightarrow> imp_prog \<Rightarrow> String.literal"
where
  "cs_ctx_graph_snapshot_of into classify r k p =
     (let g = prog_cfg p;
          base = cs_ctx_graph_config p k;
          cfg = cs_ctx_annotated_config_of classify r p k;
          sol = cs_ctx_sol_of into r
      in analysis_graph_to_canonical_text cfg g sol
           (build_analysis_graph cfg g (cs_ctx_domain_of base p r) sol))"

definition cs_ctx_checked_payload_of ::
    "('a::semilattice_sup \<Rightarrow> abstract_value)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (call_string, 'a abs_state) analysis_result
       \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> export_graph
            \<times> (pp \<times> exp \<times> contextual_verdict) list
            \<times> (String.literal \<times> String.literal list) list"
where
  "cs_ctx_checked_payload_of into classify r k p =
     (cs_ctx_export_of into classify r k p,
      classify_checks_verdicts (prog_cfg p) r classify,
      ctx_seed_globals into cs_context_key cs_show_context r p)"

text \<open>
  The dispatcher below takes the \<^typ>\<open>solver_choice\<close> its caller's plan resolved
  to, rather than reading whichever table its domain happens to publish first.
  The two differ: Int's call-string route publishes an always-join table and a
  warrowing one, and warrowing is the discipline \<open>resolve_analysis_config\<close>
  defaults that pairing to, so a dispatcher keyed on the domain alone drew a
  graph from one solve while the text report answered from the other.

  \<^const>\<open>None\<close> marks a pairing whose call-string route publishes a verdict
  report but no result table --- there is no solved table to draw or to list
  seeds from, and \<open>resolve_analysis_config\<close> rejects those pairings before a
  renderer runs.
\<close>

definition cs_ctx_checked_payload_auto ::
    "analysis_domain \<Rightarrow> solver_choice \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> (export_graph
            \<times> (pp \<times> exp \<times> contextual_verdict) list
            \<times> (String.literal \<times> String.literal list) list) option"
where
  "cs_ctx_checked_payload_auto kind sc k p =
     (case (kind, sc) of
        (Sign_Analysis, Solver_Join) \<Rightarrow>
          (let r = analyse_sign_call_string_result k p
           in Some (cs_ctx_checked_payload_of SignValue sign_classify_check r k p))
      | (Sign_Analysis, _) \<Rightarrow> None
      | (Interval_Analysis, Solver_Warrow) \<Rightarrow>
          (let r = analyse_interval_call_string_result k p
           in Some (cs_ctx_checked_payload_of IntervalValue interval_classify_check r k p))
      | (Interval_Analysis, _) \<Rightarrow> None
      | (Int_Analysis, Solver_Join) \<Rightarrow>
          (let r = analyse_int_call_string_result k p
           in Some (cs_ctx_checked_payload_of IntDomValue int_classify_check r k p))
      | (Int_Analysis, Solver_Warrow) \<Rightarrow>
          (let r = analyse_int_call_string_result_warrow k p
           in Some (cs_ctx_checked_payload_of IntDomValue int_classify_check r k p))
      | (Int_Analysis, _) \<Rightarrow> None
      | (Parity_Analysis, Solver_Join) \<Rightarrow>
          (let r = analyse_parity_call_string_result k p
           in Some (cs_ctx_checked_payload_of ParityValue parity_classify_check r k p))
      | (Parity_Analysis, _) \<Rightarrow> None
      | (Congruence_Analysis, Solver_Join) \<Rightarrow>
          (let r = analyse_congruence_call_string_result k p
           in Some (cs_ctx_checked_payload_of
                CongruenceValue congruence_classify_check r k p))
      | (Congruence_Analysis, _) \<Rightarrow> None)"

text \<open>
  Each pairing's verdict column is the call-string report its own domain
  publishes at that discipline. Six tables are named by hand above, and the two
  Int rows differ only in the solver they name, so a mismatch would render
  perfectly and disagree with the text report only where the disciplines do.
\<close>

lemma cs_ctx_checked_payload_verdicts [simp]:
  "map_option (fst \<circ> snd) (cs_ctx_checked_payload_auto kind sc k p)
     = (case (kind, sc) of
          (Sign_Analysis, Solver_Join) \<Rightarrow> Some (analyse_sign_call_string_report k p)
        | (Sign_Analysis, _) \<Rightarrow> None
        | (Interval_Analysis, Solver_Warrow) \<Rightarrow> Some (analyse_interval_call_string_report k p)
        | (Interval_Analysis, _) \<Rightarrow> None
        | (Int_Analysis, Solver_Join) \<Rightarrow> Some (analyse_int_call_string_report k p)
        | (Int_Analysis, Solver_Warrow) \<Rightarrow> Some (analyse_int_call_string_report_warrow k p)
        | (Int_Analysis, _) \<Rightarrow> None
        | (Parity_Analysis, Solver_Join) \<Rightarrow> Some (analyse_parity_call_string_report k p)
        | (Parity_Analysis, _) \<Rightarrow> None
        | (Congruence_Analysis, Solver_Join) \<Rightarrow> Some (analyse_congruence_call_string_report k p)
        | (Congruence_Analysis, _) \<Rightarrow> None)"
  by (cases kind; cases sc)
     (simp_all add: cs_ctx_checked_payload_auto_def cs_ctx_checked_payload_of_def Let_def
        analyse_sign_call_string_report_def analyse_sign_call_string_result_def
        analyse_interval_call_string_report_def analyse_interval_call_string_result_def
        analyse_interval_call_string_result_for_def
        analyse_int_call_string_report_def analyse_int_call_string_result_def
        analyse_int_call_string_result_for_def
        analyse_int_call_string_report_warrow_def analyse_int_call_string_result_warrow_def
        analyse_int_call_string_result_for_warrow_def
        analyse_parity_call_string_report_def analyse_parity_call_string_result_def
        analyse_congruence_call_string_report_def analyse_congruence_call_string_result_def
        routed_dg_pipeline.verdict_report_def)

end
