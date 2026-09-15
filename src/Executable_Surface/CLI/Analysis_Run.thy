theory Analysis_Run
  imports Dispatch_Config State_Report_Call_String Arithmetic_Diagnostics
begin

section \<open>Running one configuration once\<close>

text \<open>
  The public analysis operation. A caller hands over the three choices that
  decide what gets solved and a program, and receives the solve as data: every
  covered point-and-context state, the contexts each call enters, the check
  column and the arithmetic diagnostics. One solve stands behind all of them, and
  every rendering of them --- text, graphs, report pages --- is built outside this
  development from that one result.

  Nothing outside this theory decides which analyser runs.
  \<^const>\<open>resolve_analysis_config\<close> answers that once, as an
  \<^type>\<open>analysis_plan\<close>, and every branch below reads the table that plan names ---
  domain, context policy and solver discipline together. A dispatcher keyed on
  fewer of those axes silently answered from a neighbouring discipline's solve
  wherever a domain publishes more than one.
\<close>


subsection \<open>The result a run hands back, as data\<close>

text \<open>
  Everything a consumer reads back from one solve, with no rendering in it. Points
  are CFG nodes of \<open>res_cfg\<close>, contexts are indices into \<open>res_contexts\<close>, and every
  abstract value is the type parameter \<open>'v\<close>: \<^typ>\<open>abstract_value\<close> where a theorem
  reads the result, \<^typ>\<open>String.literal\<close> after \<open>map_run_result\<close> has applied
  each domain's own rendering. Context identity is the index, never a rendering, so
  a consumer never has to infer which states belong together from displayed text.

  A route lists every callee context a call enters from one caller context: an
  entry specification may offer several alternatives, and each may land in its own
  context. The empty list is a call the caller context does not take.
\<close>

datatype 'v analysis_context =
    Context_Unit
  | Context_Entry "'v list"
  | Context_Call_String "pp list"

record 'v result_state =
  state_point :: pp
  state_context :: nat
  state_value :: "(vname \<times> 'v) list lifted"
  state_checks :: "(exp \<times> contextual_verdict) list"
  state_diagnostics :: "(arithmetic_obligation \<times> contextual_verdict) list"

record call_route =
  route_point :: pp
  route_context :: nat
  route_callee :: pname
  route_targets :: "nat list"

record result_check =
  check_point :: pp
  check_exp :: exp
  check_verdict :: contextual_verdict

record 'v result_global =
  global_var :: vname
  global_val :: 'v

record 'v run_result =
  res_cfg :: cfg
  res_contexts :: "'v analysis_context list"
  res_states :: "'v result_state list"
  res_routes :: "call_route list"
  res_checks :: "result_check list"
  res_globals :: "'v result_global list"
  res_diagnostics :: "arithmetic_diagnostic list"

text \<open>
  The one transformation presentation may apply to a result, spelled out field by
  field: every abstract value, wherever it sits, and nothing else. Points, context
  indices, routes, checks and diagnostics pass through untouched.
\<close>

fun map_analysis_context :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v analysis_context \<Rightarrow> 'w analysis_context"
where
  "map_analysis_context f Context_Unit = Context_Unit"
| "map_analysis_context f (Context_Entry vs) = Context_Entry (map f vs)"
| "map_analysis_context f (Context_Call_String us) = Context_Call_String us"

definition map_result_state :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v result_state \<Rightarrow> 'w result_state" where
  "map_result_state f st =
     \<lparr> state_point = state_point st,
       state_context = state_context st,
       state_value = map_lift (map (\<lambda>(x, v). (x, f v))) (state_value st),
       state_checks = state_checks st,
       state_diagnostics = state_diagnostics st \<rparr>"

definition map_result_global :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v result_global \<Rightarrow> 'w result_global" where
  "map_result_global f g = \<lparr> global_var = global_var g, global_val = f (global_val g) \<rparr>"

definition map_run_result :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v run_result \<Rightarrow> 'w run_result" where
  "map_run_result f res =
     \<lparr> res_cfg = res_cfg res,
       res_contexts = map (map_analysis_context f) (res_contexts res),
       res_states = map (map_result_state f) (res_states res),
       res_routes = res_routes res,
       res_checks = res_checks res,
       res_globals = map (map_result_global f) (res_globals res),
       res_diagnostics = res_diagnostics res \<rparr>"

lemma map_run_result_structure [simp]:
  "res_cfg (map_run_result f res) = res_cfg res"
  "length (res_contexts (map_run_result f res)) = length (res_contexts res)"
  "res_routes (map_run_result f res) = res_routes res"
  "res_checks (map_run_result f res) = res_checks res"
  "res_diagnostics (map_run_result f res) = res_diagnostics res"
  "map (\<lambda>st. (state_point st, state_context st)) (res_states (map_run_result f res))
     = map (\<lambda>st. (state_point st, state_context st)) (res_states res)"
  by (simp_all add: map_run_result_def map_result_state_def comp_def)

subsection \<open>One builder for every context policy\<close>

text \<open>
  A result is built the same way whatever the context policy: list the contexts the
  table covers, file every covered \<open>(point, context)\<close> state under its context's
  index, ask the policy which contexts each live call enters, and take the check and
  diagnostic columns off the same table. The policy contributes only three things:
  how its contexts are ordered (\<open>ctx_key\<close>, injective), how a context reads as data
  (\<open>ctx_view\<close>), and which contexts a call enters from a caller state
  (\<open>targets\<close>, the routing the equation system itself applies).
\<close>

fun callee_of_entry :: "cfg_node \<Rightarrow> pname" where
  "callee_of_entry (FunctionEntry p) = p"
| "callee_of_entry _ = STR ''''"

definition context_indices :: "(nat \<times> 'c) list \<Rightarrow> 'c \<Rightarrow> nat list" where
  "context_indices indexed ctx = map fst (filter (\<lambda>(i, ctx'). ctx' = ctx) indexed)"

definition result_checks_of :: "(pp \<times> exp \<times> contextual_verdict) list \<Rightarrow> result_check list" where
  "result_checks_of verdicts =
     map (\<lambda>(v, cnd, verdict). \<lparr> check_point = v, check_exp = cnd, check_verdict = verdict \<rparr>)
       verdicts"

definition run_result_of ::
    "('a \<Rightarrow> abstract_value) \<Rightarrow> ('c \<Rightarrow> order_key) \<Rightarrow> ('c \<Rightarrow> abstract_value analysis_context)
       \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'c list)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result) \<Rightarrow> ('c, 'a abs_state) analysis_result
       \<Rightarrow> abstract_value result_global list \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result" where
  "run_result_of into ctx_key ctx_view targets classify r globals p =
     (let g = prog_cfg p;
          vars = program_vars p;
          ctxs = ordered_by_key ctx_key (snd ` result_keys r);
          indexed = enumerate 0 ctxs;
          state_at = (\<lambda>i ctx v.
            \<lparr> state_point = v, state_context = i,
              state_value = map_lift (\<lambda>st. map (\<lambda>x. (x, into (st x))) vars)
                              (lookup_context r v ctx),
              state_checks =
                map (\<lambda>(u, a, w). (ea_check_cond a,
                                   classify_point classify (ea_check_cond a)
                                     (lookup_context r v ctx)))
                  (filter (\<lambda>(u, a, w). u = v \<and> is_EA_Check a) (cfg_intra_list g)),
              state_diagnostics =
                map (\<lambda>obligation. (obligation,
                                     classify_point classify (arithmetic_condition obligation)
                                       (lookup_context r v ctx)))
                  (concat (map snd (filter (\<lambda>(u, obligations). u = v) (arithmetic_sites g))))
            \<rparr>);
          route_at = (\<lambda>u ca ce i ctx.
            \<lparr> route_point = u, route_context = i, route_callee = callee_of_entry ce,
              route_targets =
                (case lookup_context r u ctx of
                   Bot \<Rightarrow> []
                 | Lifted st \<Rightarrow>
                     remdups (concat (map (context_indices indexed)
                       (targets u ctx ca (callee_of_entry ce) st)))) \<rparr>)
      in \<lparr> res_cfg = g,
           res_contexts = map ctx_view ctxs,
           res_states =
             concat (map (\<lambda>(i, ctx).
                            map (state_at i ctx)
                              (filter (\<lambda>v. (v, ctx) \<in> result_keys r) (cfg_node_list g)))
                       indexed),
           res_routes =
             concat (map (\<lambda>(u, ca, ce, after).
                            map (\<lambda>(i, ctx). route_at u ca ce i ctx)
                              (filter (\<lambda>(i, ctx). (u, ctx) \<in> result_keys r) indexed))
                       (cfg_calls_list g)),
           res_checks = result_checks_of (classify_checks_verdicts g r classify),
           res_globals = globals,
           res_diagnostics = arithmetic_diagnostics g r classify \<rparr>)"


subsection \<open>The three context policies, as builder parameters\<close>

text \<open>
  Which callee contexts a call enters from one caller state. The entry transfer runs
  on the caller state; if a formal comes out empty the entered frame is bottom and
  the call enters nothing, which is exactly when the solver's call tree skips the seed
  publication; otherwise the policy routes the entered frame to one context. Every
  policy shares this, and differs only in \<open>route\<close>.
\<close>

definition entered_targets ::
    "((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> imp_prog
       \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> ('a::executable_domain) abs_state \<Rightarrow> 'c list"
where
  "entered_targets enter pick_ctx p u ctx ca callee st =
     (case ca of CallEdge dst pars args \<Rightarrow>
        (let entered = enter (declared_global p) pars args st
         in if list_ex (\<lambda>x. is_empty (entered x)) pars then []
            else [pick_ctx u ctx entered ca]))"

definition unit_run_result ::
    "('a \<Rightarrow> abstract_value)
       \<Rightarrow> ((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result) \<Rightarrow> (unit, ('a::executable_domain) abs_state) analysis_result
       \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result" where
  "unit_run_result into enter classify r p =
     run_result_of into (\<lambda>_. Key_List []) (\<lambda>_. Context_Unit)
       (entered_targets enter (\<lambda>_ _ _ _. ()) p) classify r [] p"

definition entry_state_run_result ::
    "('a \<Rightarrow> abstract_value)
       \<Rightarrow> ((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> ('a list, ('a::executable_domain) abs_state) analysis_result
       \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result" where
  "entry_state_run_result into enter classify r p =
     run_result_of into (\<lambda>ctx. Key_List (map (abstract_value_key \<circ> into) ctx))
       (\<lambda>ctx. Context_Entry (map into ctx))
       (entered_targets enter
          (\<lambda>_ _ entered ca. case ca of CallEdge dst pars args \<Rightarrow> formals_context pars entered) p)
       classify r [] p"

definition call_string_run_result ::
    "('a \<Rightarrow> abstract_value)
       \<Rightarrow> ((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (call_string, ('a::executable_domain) abs_state) analysis_result \<Rightarrow> nat
       \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result" where
  "call_string_run_result into enter classify r k p =
     run_result_of into (\<lambda>ctx. Key_List (map Key_Node ctx)) Context_Call_String
       (entered_targets enter (\<lambda>u ctx _ _. take k (u # ctx)) p) classify r [] p"

subsection \<open>One plan, one typed result\<close>

text \<open>
  Each branch names the one table its plan resolved to and hands it to the builder of
  that plan's context policy, together with the domain's tag and entry transfer.
  \<^const>\<open>None\<close> is a pairing with no solved table.
\<close>

definition plan_result :: "analysis_plan \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result option" where
  "plan_result pl p =
     (case pl of
        Plan_Sign Solver_Join \<Rightarrow>
          Some (unit_run_result SignValue enter_sign_for sign_classify_check
                  (fst (analyse_sign_ctx_solved_for (declared_global p) p)) p)
      | Plan_Sign Solver_PerOrigin \<Rightarrow>
          Some (unit_run_result SignValue enter_sign_for sign_classify_check
                  (analyse_sign_result_per_origin p) p)
      | Plan_Sign _ \<Rightarrow> None
      | Plan_Interval Solver_Warrow \<Rightarrow>
          Some (unit_run_result IntervalValue enter_ivl_for interval_classify_check
                  (fst (analyse_interval_ctx_solved_for (declared_global p) p)) p)
      | Plan_Interval Solver_Join \<Rightarrow>
          Some (unit_run_result IntervalValue enter_ivl_for interval_classify_check
                  (analyse_interval_result_join p) p)
      | Plan_Interval Solver_PerOrigin \<Rightarrow>
          Some (unit_run_result IntervalValue enter_ivl_for interval_classify_check
                  (analyse_interval_result_per_origin p) p)
      | Plan_Interval Solver_WarrowPerOrigin \<Rightarrow>
          Some (unit_run_result IntervalValue enter_ivl_for interval_classify_check
                  (analyse_interval_result_wpo p) p)
      | Plan_Int Solver_Warrow \<Rightarrow>
          Some (unit_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint) int_classify_check
                  (fst (analyse_int_ctx_solved_warrow_for Refine_Fixpoint (declared_global p) p)) p)
      | Plan_Int Solver_Join \<Rightarrow>
          Some (unit_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint) int_classify_check
                  (analyse_int_join_result p) p)
      | Plan_Int Solver_PerOrigin \<Rightarrow>
          Some (unit_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint) int_classify_check
                  (analyse_int_per_origin_result p) p)
      | Plan_Int Solver_WarrowPerOrigin \<Rightarrow>
          Some (unit_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint) int_classify_check
                  (analyse_int_wpo_result p) p)
      | Plan_Parity Solver_Join \<Rightarrow>
          Some (unit_run_result ParityValue enter_parity_for parity_classify_check
                  (fst (analyse_parity_ctx_solved_for (declared_global p) p)) p)
      | Plan_Parity Solver_PerOrigin \<Rightarrow>
          Some (unit_run_result ParityValue enter_parity_for parity_classify_check
                  (analyse_parity_result_per_origin p) p)
      | Plan_Parity _ \<Rightarrow> None
      | Plan_Congruence Solver_Join \<Rightarrow>
          Some (unit_run_result CongruenceValue enter_congruence_for congruence_classify_check
                  (fst (analyse_congruence_ctx_solved_for (declared_global p) p)) p)
      | Plan_Congruence Solver_PerOrigin \<Rightarrow>
          Some (unit_run_result CongruenceValue enter_congruence_for congruence_classify_check
                  (analyse_congruence_result_per_origin p) p)
      | Plan_Congruence _ \<Rightarrow> None
      | Plan_Sign_EntryState Solver_Join \<Rightarrow>
          Some (entry_state_run_result SignValue enter_sign_for sign_classify_check
                  (analyse_sign_entry_state_result p) p)
      | Plan_Sign_EntryState _ \<Rightarrow> None
      | Plan_Interval_EntryState Solver_Warrow \<Rightarrow>
          Some (entry_state_run_result IntervalValue enter_ivl_for interval_classify_check
                  (analyse_interval_entry_state_result p) p)
      | Plan_Interval_EntryState Solver_Join \<Rightarrow>
          Some (entry_state_run_result IntervalValue enter_ivl_for interval_classify_check
                  (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
                    (Analysis_Global ()) Activation_Seed exec_formals_route []
                    TD_side_always_join_Interp_solve (declared_global p) p) p)
      | Plan_Interval_EntryState Solver_PerOrigin \<Rightarrow>
          Some (entry_state_run_result IntervalValue enter_ivl_for interval_classify_check
                  (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
                    (Analysis_Global ()) Activation_Seed exec_formals_route []
                    TD_side_per_origin_Interp_solve (declared_global p) p) p)
      | Plan_Interval_EntryState Solver_WarrowPerOrigin \<Rightarrow>
          Some (entry_state_run_result IntervalValue enter_ivl_for interval_classify_check
                  (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
                    (Analysis_Global ()) Activation_Seed exec_formals_route []
                    TD_side_warrowing_per_origin_Interp_solve (declared_global p) p) p)
      | Plan_Int_EntryState Solver_Join \<Rightarrow>
          Some (entry_state_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint)
                  int_classify_check (analyse_int_entry_state_result p) p)
      | Plan_Int_EntryState Solver_Warrow \<Rightarrow>
          Some (entry_state_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint)
                  int_classify_check (analyse_int_entry_state_result_warrow p) p)
      | Plan_Int_EntryState _ \<Rightarrow> None
      | Plan_Parity_EntryState Solver_Join \<Rightarrow>
          Some (entry_state_run_result ParityValue enter_parity_for parity_classify_check
                  (analyse_parity_entry_state_result p) p)
      | Plan_Parity_EntryState _ \<Rightarrow> None
      | Plan_Congruence_EntryState Solver_Join \<Rightarrow>
          Some (entry_state_run_result CongruenceValue enter_congruence_for
                  congruence_classify_check (analyse_congruence_entry_state_result p) p)
      | Plan_Congruence_EntryState _ \<Rightarrow> None
      | Plan_Sign_CallString Solver_Join k \<Rightarrow>
          Some (call_string_run_result SignValue enter_sign_for sign_classify_check
                  (analyse_sign_call_string_result k p) k p)
      | Plan_Sign_CallString _ _ \<Rightarrow> None
      | Plan_Interval_CallString Solver_Warrow k \<Rightarrow>
          Some (call_string_run_result IntervalValue enter_ivl_for interval_classify_check
                  (analyse_interval_call_string_result k p) k p)
      | Plan_Interval_CallString Solver_Join k \<Rightarrow>
          Some (call_string_run_result IntervalValue enter_ivl_for interval_classify_check
                  (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
                    Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
                    TD_side_always_join_Interp_solve (declared_global p) p) k p)
      | Plan_Interval_CallString Solver_PerOrigin k \<Rightarrow>
          Some (call_string_run_result IntervalValue enter_ivl_for interval_classify_check
                  (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
                    Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
                    TD_side_per_origin_Interp_solve (declared_global p) p) k p)
      | Plan_Interval_CallString Solver_WarrowPerOrigin k \<Rightarrow>
          Some (call_string_run_result IntervalValue enter_ivl_for interval_classify_check
                  (routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
                    Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
                    TD_side_warrowing_per_origin_Interp_solve (declared_global p) p) k p)
      | Plan_Int_CallString Solver_Join k \<Rightarrow>
          Some (call_string_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint)
                  int_classify_check (analyse_int_call_string_result k p) k p)
      | Plan_Int_CallString Solver_Warrow k \<Rightarrow>
          Some (call_string_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint)
                  int_classify_check (analyse_int_call_string_result_warrow k p) k p)
      | Plan_Int_CallString _ _ \<Rightarrow> None
      | Plan_Parity_CallString Solver_Join k \<Rightarrow>
          Some (call_string_run_result ParityValue enter_parity_for parity_classify_check
                  (analyse_parity_call_string_result k p) k p)
      | Plan_Parity_CallString _ _ \<Rightarrow> None
      | Plan_Congruence_CallString Solver_Join k \<Rightarrow>
          Some (call_string_run_result CongruenceValue enter_congruence_for
                  congruence_classify_check (analyse_congruence_call_string_result k p) k p)
      | Plan_Congruence_CallString _ _ \<Rightarrow> None)"

subsection \<open>The public operation\<close>

text \<open>
  Three answers, because a caller has three genuinely different things to do.
  A malformed program was never analysed; an unsupported configuration names a
  pairing this build publishes no route for; and the third carries a result.
  Collapsing the first two into one \<^const>\<open>None\<close> would leave the CLI unable to say
  which of them happened, which is the distinction its exit codes are built on.
\<close>

datatype 'v analysis_answer =
    Malformed_Program
  | Unsupported_Configuration
  | Analysed "'v run_result"

definition analyse_program ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode \<Rightarrow> imp_prog
       \<Rightarrow> abstract_value analysis_answer" where
  "analyse_program kind solver ctx p =
     (if \<not> wf_program_compile_input_exec p then Malformed_Program
      else
        case resolve_analysis_config (mk_analysis_config kind solver ctx) of
          None \<Rightarrow> Unsupported_Configuration
        | Some pl \<Rightarrow>
            (case plan_result pl p of
               None \<Rightarrow> Unsupported_Configuration
             | Some res \<Rightarrow> Analysed res))"

fun map_analysis_answer :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v analysis_answer \<Rightarrow> 'w analysis_answer" where
  "map_analysis_answer f Malformed_Program = Malformed_Program"
| "map_analysis_answer f Unsupported_Configuration = Unsupported_Configuration"
| "map_analysis_answer f (Analysed res) = Analysed (map_run_result f res)"

text \<open>
  The operation a consumer outside Isabelle calls: \<^const>\<open>analyse_program\<close>, with each
  domain's rendering applied to every abstract value and nothing else changed.
\<close>

definition run_voblint ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode \<Rightarrow> imp_prog
       \<Rightarrow> String.literal analysis_answer" where
  "run_voblint kind solver ctx p =
     map_analysis_answer string_of_abstract_value (analyse_program kind solver ctx p)"

end
