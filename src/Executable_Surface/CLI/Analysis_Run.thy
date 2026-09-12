theory Analysis_Run
  imports Dispatch_Config State_Report_Call_String Arithmetic_Diagnostics
begin

section \<open>Running one configuration once\<close>

text \<open>
  The public analysis operation. A caller hands over the three choices that
  decide what gets solved and a program, and receives everything a report
  consumer reads back: the exported graph, the per-check column, and the seed
  state of every activation the solve covered. One solve stands behind all of
  them.

  The point of collecting them here is that nothing outside this theory
  decides which analyser runs. \<^const>\<open>resolve_analysis_config\<close> answers that
  once, as an \<^type>\<open>analysis_plan\<close>, and every branch below reads the table
  that plan names --- domain, context policy \<^emph>\<open>and\<close> solver discipline
  together. A dispatcher keyed on fewer of those axes silently answered from a
  neighbouring discipline's solve wherever a domain publishes more than one.

  The per-check column comes in two shapes, and neither is forced onto the
  other: a context-free plan carries a \<^typ>\<open>check_result\<close> beside the state it
  was decided from, a context-sensitive one a \<^typ>\<open>contextual_verdict\<close> that
  keeps \<^const>\<open>Dead\<close> apart from an undecided check. Each output carries the
  one its plan produces and \<^const>\<open>None\<close> for the other.
\<close>

subsection \<open>What a caller asks to see\<close>

text \<open>
  Which analysis runs and which drawing of its result comes back are separate
  questions, and \<^type>\<open>analysis_config\<close> deliberately answers only the first.
  This is the second: the same solved table renders four ways, and picking one
  is a presentation choice that changes no verdict.

  \<open>View_Contexts\<close> is the exception that proves the split. It draws one node per
  \<^term>\<open>(v, ctx)\<close> pair instead of joining the contexts covering a point, so it
  needs a context policy to have produced more than one --- and a configuration
  that cannot serve it is refused rather than quietly answered with the joined
  picture.
\<close>

datatype output_view =
    View_Report
  | View_Checks
  | View_States
  | View_Checked_States
  | View_Contexts

text \<open>
  One check, as a reader meets it. The condition and the state slice arrive
  rendered because the alternative is worse: a caller outside this session
  would otherwise hold a \<^typ>\<open>abstract_value abs_state\<close> --- a function from
  names to values --- and could only read it by guessing which names to ask
  about. Rendering the row here keeps \<^const>\<open>exp_vnames_list\<close> and
  \<^const>\<open>string_of_exp\<close> out of the handwritten OCaml.

  \<open>row_verdict\<close> is a \<^typ>\<open>check_result lifted\<close> rather than a
  \<^typ>\<open>check_result\<close>, so one row type serves both a context-free and a
  context-sensitive run: \<^const>\<open>Bot\<close> is the check no execution reaches, which a
  flat run reports through its unreachability flag and a contextual run through
  \<^const>\<open>Dead\<close>. Neither is collapsed into an undecided verdict --- ``nothing
  reaches this check'' and ``the abstraction could not decide'' are different
  findings.
\<close>

text \<open>
  The condition appears twice, and both are load-bearing. \<open>row_condition\<close> is what a
  reader sees; \<open>row_exp\<close> is the condition itself, which is what a \<^emph>\<open>theorem\<close> can
  quantify over --- \<^const>\<open>aval\<close> evaluates an \<^typ>\<open>exp\<close> against a store, and no
  amount of rendered text can be evaluated against anything. A row carrying only
  its rendering would make this analyser's own soundness unstatable over its
  published output.
\<close>

datatype check_row =
  Check_Row
    (row_point: pp)
    (row_exp: exp)
    (row_condition: String.literal)
    (row_verdict: "check_result lifted")
    (row_state: String.literal)

text \<open>
  The drawing is optional, and for two independent reasons. A caller printing a
  text report asks for none, and building one for it would be work nobody reads
  --- on a recursive program with many activations, enough work to matter. And
  a discipline that publishes a verdict report but no result table has nothing
  to draw \<^emph>\<open>from\<close>: its checks are known and its graph is not.
\<close>

datatype analysis_output =
  Analysis_Output
    (out_graph: "export_graph option")
    (out_snapshot: "String.literal option")
    (out_checks: "check_row list")
    (out_globals: "(String.literal \<times> String.literal list) list")
    (out_diagnostics: "arithmetic_diagnostic list")

definition diagnostic_message :: "arithmetic_diagnostic \<Rightarrow> String.literal" where
  "diagnostic_message diagnostic =
     (let operation = arithmetic_operation (diagnostic_obligation diagnostic);
          kind = (case operation of Mod _ _ \<Rightarrow> ''remainder'' | _ \<Rightarrow> ''division'');
          message = (if diagnostic_verdict diagnostic = Check_Refuted
            then kind @ '' by zero whenever this operation is evaluated: ''
            else ''possible '' @ kind @ '' by zero: '')
      in String.implode (message @ string_of_exp 0 operation))"

fun with_diagnostics :: "arithmetic_diagnostic list \<Rightarrow> analysis_output \<Rightarrow> analysis_output"
where
  "with_diagnostics ds (Analysis_Output g snap rows globals old) =
     Analysis_Output g snap rows globals ds"

text \<open>
  Three answers, because a caller has three genuinely different things to do.
  A malformed program was never analysed; an unsupported configuration names a
  pairing this build publishes no route for; and \<open>Analysed\<close> carries a
  result. Collapsing the first two into one \<^const>\<open>None\<close> would leave the CLI
  unable to say which of them happened, which is the distinction its exit codes
  are built on.
\<close>

datatype analysis_answer =
    Malformed_Program
  | Unsupported_Configuration
  | Analysed analysis_output

subsection \<open>A check, rendered\<close>

text \<open>
  The state slice shows the variables the checked condition mentions, and only
  those: they are the ones whose values decided the verdict, and a reader
  comparing a \<^const>\<open>Check_Unknown\<close> against the state wants to see them rather
  than every name in the program. An unreachable point has no state to slice,
  which is the empty string here and \<^const>\<open>Bot\<close> in the verdict column beside it.
\<close>

definition comma_join :: "string list \<Rightarrow> string" where
  "comma_join xs = (case xs of [] \<Rightarrow> '''' | y # ys \<Rightarrow> y @ concat (map (\<lambda>z. '', '' @ z) ys))"

definition state_slice ::
    "abstract_value abs_state lifted \<Rightarrow> exp \<Rightarrow> String.literal" where
  "state_slice st cnd =
     (case st of
        Bot \<Rightarrow> STR ''''
      | Lifted f \<Rightarrow>
          String.implode
            (comma_join (map (\<lambda>x. String.explode x @ ''='' @ string_of_abstract_value (f x))
                             (exp_vnames_list cnd))))"

definition check_rows_of ::
    "(pp \<Rightarrow> abstract_value abs_state lifted) \<Rightarrow> (pp \<times> exp \<times> check_result lifted) list
       \<Rightarrow> check_row list" where
  "check_rows_of env verdicts =
     map (\<lambda>(v, cnd, verdict).
            Check_Row v cnd (String.implode (string_of_exp 0 cnd)) verdict
              (state_slice (env v) cnd))
         verdicts"

subsection \<open>One solved table, drawn as asked\<close>

text \<open>
  The collapsed views differ only in what hangs on the nodes of one graph, so
  the view selects an annotation and nothing else. The exported graph and its
  canonical text are two readings of that same annotated graph rather than two
  renderings, which is what keeps a caller wanting both from paying for two.
\<close>

definition view_annotation ::
    "output_view \<Rightarrow> imp_prog \<Rightarrow> (pp \<Rightarrow> abstract_value abs_state lifted)
       \<Rightarrow> (pp \<times> exp \<times> check_result lifted) list \<Rightarrow> pp \<Rightarrow> graph_node_annotation option" where
  "view_annotation view p env rows =
     (case view of
        View_States \<Rightarrow> point_node_annotation (program_vars p) env
      | View_Checked_States \<Rightarrow>
          full_state_checked_node_annotation (program_vars p) env (decided_verdicts rows)
      | _ \<Rightarrow>
          verdict_state_report_node_annotation (report_vars rows)
            (map (\<lambda>(v, cnd, verdict). (v, cnd, verdict, env v)) rows))"

definition collapsed_output ::
    "output_view \<Rightarrow> imp_prog \<Rightarrow> (pp \<Rightarrow> abstract_value abs_state lifted)
       \<Rightarrow> (pp \<times> exp \<times> check_result lifted) list
       \<Rightarrow> (String.literal \<times> String.literal list) list \<Rightarrow> analysis_output" where
  "collapsed_output view p env rows globals =
     (let ann = view_annotation view p env rows
      in Analysis_Output
           (Some (raw_cfg_export (prog_table p) (prog_procs p) ann))
           (Some (raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) ann))
           (check_rows_of env rows)
           globals [])"

text \<open>
  The check column with nothing drawn beside it. A verdict-report route reaches
  this with no table behind it, so its rows carry no state to slice --- the
  verdicts are what that route publishes, and the empty slice says so rather
  than inventing one.
\<close>

definition report_output ::
    "(pp \<Rightarrow> abstract_value abs_state lifted) \<Rightarrow> (pp \<times> exp \<times> check_result lifted) list
       \<Rightarrow> (String.literal \<times> String.literal list) list \<Rightarrow> analysis_output" where
  "report_output env rows globals =
     Analysis_Output None None (check_rows_of env rows) globals []"

text \<open>
  A route that publishes verdicts and no table answers the report view and
  refuses the drawings, rather than being absent from the configuration space
  altogether: \<open>--solver join --context entry-state\<close> is a supported pairing whose
  checks are proved, and only its picture is missing.
\<close>

definition verdict_report_answer ::
    "output_view \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list \<Rightarrow> analysis_answer" where
  "verdict_report_answer view rows =
     (case view of
        View_Report \<Rightarrow> Analysed (report_output (\<lambda>_. Bot) rows [])
      | _ \<Rightarrow> Unsupported_Configuration)"

text \<open>
  The per-context drawing cannot be assembled from an annotation: its nodes are
  \<^term>\<open>(v, ctx)\<close> pairs, so the graph comes from the contextual builder already
  and only the columns beside it are shared.
\<close>

definition contextual_output ::
    "export_graph \<Rightarrow> String.literal \<Rightarrow> (pp \<Rightarrow> abstract_value abs_state lifted)
       \<Rightarrow> (pp \<times> exp \<times> check_result lifted) list
       \<Rightarrow> (String.literal \<times> String.literal list) list \<Rightarrow> analysis_output" where
  "contextual_output g snap env rows globals =
     Analysis_Output (Some g) (Some snap) (check_rows_of env rows) globals []"
subsection \<open>The three routes, each from one solved table\<close>

text \<open>
  A context-free route reports a check's reachability in a flag beside its
  verdict; a contextual one reports it as \<^const>\<open>Dead\<close>. Both become
  \<^const>\<open>Bot\<close> in a row, which is why one row type serves all three routes
  without either convention being lost.
\<close>

definition flat_rows_of ::
    "(exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result) \<Rightarrow> 'a abs_state
       \<Rightarrow> (unit, 'a abs_state) analysis_result \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> check_result lifted) list" where
  "flat_rows_of classify bot_state r p =
     map (\<lambda>(u, cnd, res, unr, st). (u, cnd, if unr then Bot else Lifted res))
       (classify_checks_with_state (prog_cfg p)
          (\<lambda>v. case lookup_context r v () of
                 Bot \<Rightarrow> (True, bot_state) | Lifted st \<Rightarrow> (False, st))
          (\<lambda>cnd (_, s). classify cnd s))"

definition rendered_globals ::
    "('a \<Rightarrow> abstract_value) \<Rightarrow> vname list \<Rightarrow> (String.literal \<times> 'a abs_state lifted) list
       \<Rightarrow> (String.literal \<times> String.literal list) list" where
  "rendered_globals into vars gvs =
     map (\<lambda>(k, st). (k, point_lines vars (map_lift (\<lambda>s. into \<circ> s) st))) gvs"

definition flat_output_of ::
    "output_view \<Rightarrow> ('a \<Rightarrow> abstract_value) \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> 'a abs_state \<Rightarrow> (unit, 'a abs_state) analysis_result
       \<Rightarrow> (String.literal \<times> String.literal list) list \<Rightarrow> imp_prog
       \<Rightarrow> analysis_answer" where
  "flat_output_of view into classify bot_state r globals p =
     (let finish = with_diagnostics (arithmetic_diagnostics (prog_cfg p) r classify);
          env = project_env into r;
          rows = flat_rows_of classify bot_state r p
      in case view of
           View_Contexts \<Rightarrow> Unsupported_Configuration
         | View_Report \<Rightarrow> Analysed (finish (report_output env rows globals))
         | _ \<Rightarrow> Analysed (finish (collapsed_output view p env rows globals)))"

text \<open>
  A contextual route answers every view. The collapsed ones read the table
  through \<^const>\<open>project_joined_env\<close>, which joins the contexts covering a point
  before the renderer sees them; \<open>View_Contexts\<close> keeps them apart and takes its
  graph from the builder that draws one node per activation. That builder is
  named inside the branch rather than passed in, so a collapsed rendering never
  pays to construct a graph it will not show.
\<close>

definition entry_state_output_of ::
    "output_view \<Rightarrow> ((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list
        \<Rightarrow> ('a::{executable_domain,semilattice_sup}) abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> ('a \<Rightarrow> abstract_value) \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> ('a list, 'a abs_state) analysis_result \<Rightarrow> imp_prog \<Rightarrow> analysis_answer" where
  "entry_state_output_of view enter into classify r p =
     (let finish = with_diagnostics (arithmetic_diagnostics (prog_cfg p) r classify);
          env = project_joined_env into r;
          rows = classify_checks_verdicts (prog_cfg p) r classify;
          globals = ctx_seed_globals into (ctx_key_of into) (ctx_show_of into) r p
      in case view of
           View_Contexts \<Rightarrow>
             Analysed (finish (contextual_output
                         (entry_state_ctx_export_of enter into classify r p)
                         (entry_state_ctx_graph_snapshot_of enter into classify r p)
                         env rows globals))
         | View_Report \<Rightarrow> Analysed (finish (report_output env rows globals))
         | _ \<Rightarrow> Analysed (finish (collapsed_output view p env rows globals)))"

definition cs_output_of ::
    "output_view \<Rightarrow> ('a::semilattice_sup \<Rightarrow> abstract_value)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (call_string, 'a abs_state) analysis_result \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> analysis_answer" where
  "cs_output_of view into classify r k p =
     (let finish = with_diagnostics (arithmetic_diagnostics (prog_cfg p) r classify);
          env = project_joined_env into r;
          rows = classify_checks_verdicts (prog_cfg p) r classify;
          globals = ctx_seed_globals into cs_context_key cs_show_context r p
      in case view of
           View_Contexts \<Rightarrow>
             Analysed (finish (contextual_output (cs_ctx_export_of into classify r k p)
                         (cs_ctx_graph_snapshot_of into classify r k p)
                         env rows globals))
         | View_Report \<Rightarrow> Analysed (finish (report_output env rows globals))
         | _ \<Rightarrow> Analysed (finish (collapsed_output view p env rows globals)))"

subsection \<open>One plan, one run\<close>

text \<open>
  The plan already names the domain, the context policy and the solver
  discipline together, so nothing below chooses an analyser: each branch names
  the one table its plan resolved to, binds it once, and every column comes off
  that binding. That is what stops a graph being drawn from one solve while the
  checks beside it come from another.

  \<^const>\<open>Unsupported_Configuration\<close> survives at the pairings whose route
  publishes a verdict report but no result table --- there is nothing to draw,
  to slice states from, or to list activations of --- and at \<open>View_Contexts\<close>
  asked of a context-free plan, which has one context and so nothing to expand.
\<close>

definition table_report_answer ::
    "output_view \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result)
       \<Rightarrow> imp_prog \<Rightarrow> analysis_answer" where
  "table_report_answer view r classify p =
     (case view of
        View_Report \<Rightarrow> Analysed
          (with_diagnostics (arithmetic_diagnostics (prog_cfg p) r classify)
            (report_output (\<lambda>_. Bot) (classify_checks_verdicts (prog_cfg p) r classify) []))
      | _ \<Rightarrow> Unsupported_Configuration)"

definition plan_answer :: "analysis_plan \<Rightarrow> output_view \<Rightarrow> imp_prog \<Rightarrow> analysis_answer" where
  "plan_answer pl view p =
     (case pl of
        Plan_Sign Solver_Join \<Rightarrow>
          (case analyse_sign_ctx_solved_for (declared_global p) p of (r, gvs) \<Rightarrow>
             flat_output_of view SignValue sign_classify_check bot r
               (rendered_globals SignValue (program_vars p) gvs) p)
      | Plan_Sign Solver_PerOrigin \<Rightarrow>
          (let r = analyse_sign_result_per_origin p
           in flat_output_of view SignValue sign_classify_check bot r
                (unit_seed_globals SignValue r p) p)
      | Plan_Sign _ \<Rightarrow> Unsupported_Configuration
      | Plan_Interval Solver_Warrow \<Rightarrow>
          (case analyse_interval_ctx_solved_for (declared_global p) p of (r, gvs) \<Rightarrow>
             flat_output_of view IntervalValue interval_classify_check bot r
               (rendered_globals IntervalValue (program_vars p) gvs) p)
      | Plan_Interval Solver_Join \<Rightarrow>
          (let r = analyse_interval_result_join p
           in flat_output_of view IntervalValue interval_classify_check bot r
                (unit_seed_globals IntervalValue r p) p)
      | Plan_Interval Solver_PerOrigin \<Rightarrow>
          (let r = analyse_interval_result_per_origin p
           in flat_output_of view IntervalValue interval_classify_check bot r
                (unit_seed_globals IntervalValue r p) p)
      | Plan_Interval Solver_WarrowPerOrigin \<Rightarrow>
          (let r = analyse_interval_result_wpo p
           in flat_output_of view IntervalValue interval_classify_check bot r
                (unit_seed_globals IntervalValue r p) p)
      | Plan_Int Solver_Warrow \<Rightarrow>
          (case analyse_int_ctx_solved_warrow_for Refine_Fixpoint (declared_global p) p of
             (r, gvs) \<Rightarrow>
               flat_output_of view IntDomValue int_classify_check bot r
                 (rendered_globals IntDomValue (program_vars p) gvs) p)
      | Plan_Int Solver_Join \<Rightarrow>
          (let r = analyse_int_join_result p
           in flat_output_of view IntDomValue int_classify_check bot r
                (unit_seed_globals IntDomValue r p) p)
      | Plan_Int Solver_PerOrigin \<Rightarrow>
          (let r = analyse_int_per_origin_result p
           in flat_output_of view IntDomValue int_classify_check bot r
                (unit_seed_globals IntDomValue r p) p)
      | Plan_Int Solver_WarrowPerOrigin \<Rightarrow>
          (let r = analyse_int_wpo_result p
           in flat_output_of view IntDomValue int_classify_check bot r
                (unit_seed_globals IntDomValue r p) p)
      | Plan_Parity Solver_Join \<Rightarrow>
          (case analyse_parity_ctx_solved_for (declared_global p) p of (r, gvs) \<Rightarrow>
             flat_output_of view ParityValue parity_classify_check bot r
               (rendered_globals ParityValue (program_vars p) gvs) p)
      | Plan_Parity Solver_PerOrigin \<Rightarrow>
          (let r = analyse_parity_result_per_origin p
           in flat_output_of view ParityValue parity_classify_check bot r
                (unit_seed_globals ParityValue r p) p)
      | Plan_Parity _ \<Rightarrow> Unsupported_Configuration
      | Plan_Congruence Solver_Join \<Rightarrow>
          (case analyse_congruence_ctx_solved_for (declared_global p) p of (r, gvs) \<Rightarrow>
             flat_output_of view CongruenceValue congruence_classify_check bot r
               (rendered_globals CongruenceValue (program_vars p) gvs) p)
      | Plan_Congruence Solver_PerOrigin \<Rightarrow>
          (let r = analyse_congruence_result_per_origin p
           in flat_output_of view CongruenceValue congruence_classify_check bot r
                (unit_seed_globals CongruenceValue r p) p)
      | Plan_Congruence _ \<Rightarrow> Unsupported_Configuration
      | Plan_Sign_EntryState Solver_Join \<Rightarrow>
          entry_state_output_of view enter_sign_for SignValue sign_classify_check
            (analyse_sign_entry_state_result p) p
      | Plan_Sign_EntryState _ \<Rightarrow> Unsupported_Configuration
      | Plan_Interval_EntryState Solver_Warrow \<Rightarrow>
          entry_state_output_of view enter_ivl_for IntervalValue interval_classify_check
            (analyse_interval_entry_state_result p) p
      | Plan_Interval_EntryState Solver_Join \<Rightarrow>
          table_report_answer view
            (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
              (Analysis_Global ()) Activation_Seed exec_formals_route []
              TD_side_always_join_Interp_solve (declared_global p) p)
            interval_classify_check p
      | Plan_Interval_EntryState Solver_PerOrigin \<Rightarrow>
          table_report_answer view
            (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
              (Analysis_Global ()) Activation_Seed exec_formals_route []
              TD_side_per_origin_Interp_solve (declared_global p) p)
            interval_classify_check p
      | Plan_Interval_EntryState Solver_WarrowPerOrigin \<Rightarrow>
          table_report_answer view
            (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
              (Analysis_Global ()) Activation_Seed exec_formals_route []
              TD_side_warrowing_per_origin_Interp_solve (declared_global p) p)
            interval_classify_check p
      | Plan_Int_EntryState Solver_Join \<Rightarrow>
          entry_state_output_of view (enter_int_dom_for Refine_Fixpoint) IntDomValue
            int_classify_check (analyse_int_entry_state_result p) p
      | Plan_Int_EntryState Solver_Warrow \<Rightarrow>
          entry_state_output_of view (enter_int_dom_for Refine_Fixpoint) IntDomValue
            int_classify_check (analyse_int_entry_state_result_warrow p) p
      | Plan_Int_EntryState _ \<Rightarrow> Unsupported_Configuration
      | Plan_Parity_EntryState Solver_Join \<Rightarrow>
          entry_state_output_of view enter_parity_for ParityValue parity_classify_check
            (analyse_parity_entry_state_result p) p
      | Plan_Parity_EntryState _ \<Rightarrow> Unsupported_Configuration
      | Plan_Congruence_EntryState Solver_Join \<Rightarrow>
          entry_state_output_of view enter_congruence_for CongruenceValue
            congruence_classify_check (analyse_congruence_entry_state_result p) p
      | Plan_Congruence_EntryState _ \<Rightarrow> Unsupported_Configuration
      | Plan_Sign_CallString Solver_Join k \<Rightarrow>
          cs_output_of view SignValue sign_classify_check
            (analyse_sign_call_string_result k p) k p
      | Plan_Sign_CallString _ _ \<Rightarrow> Unsupported_Configuration
      | Plan_Interval_CallString Solver_Warrow k \<Rightarrow>
          cs_output_of view IntervalValue interval_classify_check
            (analyse_interval_call_string_result k p) k p
      | Plan_Interval_CallString Solver_Join k \<Rightarrow>
          table_report_answer view
            (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
              Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
              TD_side_always_join_Interp_solve (declared_global p) p)
            interval_classify_check p
      | Plan_Interval_CallString Solver_PerOrigin k \<Rightarrow>
          table_report_answer view
            (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
              Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
              TD_side_per_origin_Interp_solve (declared_global p) p)
            interval_classify_check p
      | Plan_Interval_CallString Solver_WarrowPerOrigin k \<Rightarrow>
          table_report_answer view
            (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
              Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
              TD_side_warrowing_per_origin_Interp_solve (declared_global p) p)
            interval_classify_check p
      | Plan_Int_CallString Solver_Join k \<Rightarrow>
          cs_output_of view IntDomValue int_classify_check
            (analyse_int_call_string_result k p) k p
      | Plan_Int_CallString Solver_Warrow k \<Rightarrow>
          cs_output_of view IntDomValue int_classify_check
            (analyse_int_call_string_result_warrow k p) k p
      | Plan_Int_CallString _ _ \<Rightarrow> Unsupported_Configuration
      | Plan_Parity_CallString Solver_Join k \<Rightarrow>
          cs_output_of view ParityValue parity_classify_check
            (analyse_parity_call_string_result k p) k p
      | Plan_Parity_CallString _ _ \<Rightarrow> Unsupported_Configuration
      | Plan_Congruence_CallString Solver_Join k \<Rightarrow>
          cs_output_of view CongruenceValue congruence_classify_check
            (analyse_congruence_call_string_result k p) k p
      | Plan_Congruence_CallString _ _ \<Rightarrow> Unsupported_Configuration)"

text \<open>
  The public operation. A caller names the three choices that decide what gets
  solved, the drawing it wants back, and a program. Everything else --- which
  analyser runs, whether the pairing is supported at all, whether the program
  is even well-formed --- is settled here, so no consumer reconstructs any of
  it from the flags it happens to hold.
\<close>

definition run_voblint ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode \<Rightarrow> output_view \<Rightarrow> imp_prog
       \<Rightarrow> analysis_answer" where
  "run_voblint kind solver ctx view p =
     (if \<not> wf_program_compile_input_exec p then Malformed_Program
      else
        case resolve_analysis_config (mk_analysis_config kind solver ctx) of
          None \<Rightarrow> Unsupported_Configuration
        | Some pl \<Rightarrow> plan_answer pl view p)"
end
