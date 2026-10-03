theory Analysis_Run
  imports
    Arithmetic_Diagnostics
    MCP_Split
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Abstract_Char"
begin

section \<open>Running one configuration once\<close>

text \<open>
  The public analysis operation. A caller hands over the three choices that
  decide what gets solved and a program, and receives the solve as a report:
  every covered point-and-context state, the contexts each call enters, the check
  column and the arithmetic diagnostics. One solve stands behind all of them. The
  report holds semantic states, never their rendering; text, graphs and report
  pages are built from it by a projection outside the theorems.

  Nothing outside this theory decides which analyser runs: the one function below
  that reads the context policy names the registration that policy solves with.
\<close>

subsection \<open>The rows of a report\<close>

text \<open>
  Points are CFG nodes and contexts are indices into the report's context list, so
  a consumer never has to infer which states belong together from displayed text.
  A row's state is the type parameter \<open>'s\<close>: the semantic state in a report, its
  rendering after a presentation has been applied.

  A route lists every callee context a call enters from one caller context: an
  entry specification may offer several alternatives, and each may land in its own
  context. The empty list is a call the caller context does not take.

  A state also lists, for every edge leaving its point, that edge's target and what
  the edge's own step makes of the state. Where the target is a join of several
  incoming edges -- a loop head, the point after a branch -- this is the only place
  the effect of one statement survives.
\<close>

record 's result_state =
  state_point :: pp
  state_context :: nat
  state_value :: "'s lifted"
  state_checks :: "(exp \<times> contextual_verdict) list"
  state_diagnostics :: "(arithmetic_obligation \<times> contextual_verdict) list"
  state_steps :: "(pp \<times> 's lifted) list"

record call_route =
  route_point :: pp
  route_context :: nat
  route_callee :: pname
  route_targets :: "nat list"

record result_check =
  check_point :: pp
  check_label :: check_label
  check_exp :: exp
  check_verdict :: contextual_verdict

text \<open>
  A global unknown is a program global kept at its own unknown, or the seed of a
  procedure entry, named by the procedure and the index of the context it was
  entered at; a seed without a context belongs to a procedure the solve never
  entered.
\<close>

datatype result_global_unknown =
    Global_Named vname
  | Global_Seed pname "nat option"

record 's result_global =
  global_unknown :: result_global_unknown
  global_state :: "'s lifted"

definition map_result_state :: "('s \<Rightarrow> 't) \<Rightarrow> 's result_state \<Rightarrow> 't result_state" where
  "map_result_state f st =
     \<lparr> state_point = state_point st,
       state_context = state_context st,
       state_value = map_lift f (state_value st),
       state_checks = state_checks st,
       state_diagnostics = state_diagnostics st,
       state_steps = map (\<lambda>(w, s). (w, map_lift f s)) (state_steps st) \<rparr>"

definition map_result_global :: "('s \<Rightarrow> 't) \<Rightarrow> 's result_global \<Rightarrow> 't result_global" where
  "map_result_global f g =
     \<lparr> global_unknown = global_unknown g,
       global_state = map_lift f (global_state g) \<rparr>"

subsection \<open>The configuration\<close>

text \<open>
  A caller's three choices travel together as one value: the analyses that run, the
  rule for side-effected globals, and the context policy. A configuration is valid
  when it activates at least one analysis and none twice.
\<close>

text \<open>
  Where a program's globals live: in every point's own state, flow-sensitively, or
  on the shared channel, as one flow-insensitive fact every point reads.
\<close>

datatype program_globals = Program_Globals_Flow_Sensitive | Program_Globals_Flow_Insensitive

datatype analysis_config = Analysis_Config
  (config_analyses: "analysis_domain list")
  (config_rule: globals_rule)
  (config_context: context_mode)
  (config_globals: program_globals)

definition valid_config :: "analysis_config \<Rightarrow> bool" where
  "valid_config config \<longleftrightarrow> config_analyses config \<noteq> [] \<and> distinct (config_analyses config)"

subsection \<open>The report\<close>

text \<open>
  A context is kept as the policy's own value, tagged by policy, so one report type
  serves every policy. The report also keeps the configuration, which names the
  concretization its states are read through, and the program's variables, which a
  rendering lists.
\<close>

datatype report_context =
    Report_Unit
  | Report_Entry mcp_ctx
  | Report_Call_String "pp list"

record analysis_report =
  report_config :: analysis_config
  report_vars :: "vname list"
  report_cfg :: cfg
  report_contexts :: "report_context list"
  report_states :: "mcp_val result_state list"
  report_routes :: "call_route list"
  report_checks :: "result_check list"
  report_globals :: "mcp_val result_global list"
  report_diagnostics :: "arithmetic_diagnostic list"

subsection \<open>One builder for every context policy\<close>

text \<open>
  A report is built the same way whatever the context policy: list the contexts the
  table covers, file every covered \<open>(point, context)\<close> state under its context's
  index, ask the run which context each live call enters, and take the check and
  diagnostic columns off the same table. The policy contributes only how its
  contexts are ordered (\<open>ctx_key\<close>, injective) and tagged (\<open>ctx_tag\<close>).

  Points are listed in graph order. A covered point outside the graph's node list
  is listed after them, so the rows hold every covered key without a separate
  argument about which points the solver visits.
\<close>

fun callee_of_entry :: "cfg_node \<Rightarrow> pname" where
  "callee_of_entry (FunctionEntry p) = p"
| "callee_of_entry _ = STR ''''"

definition context_indices :: "(nat \<times> 'c) list \<Rightarrow> 'c \<Rightarrow> nat list" where
  "context_indices indexed ctx = map fst (filter (\<lambda>(i, ctx'). ctx' = ctx) indexed)"

text \<open>
  Contexts are listed in the order of an injective key, which picks each context back
  out of the key set by \<^const>\<open>the_elem\<close>. HOL's own code equation for that
  matches only a literal one-element list, but a set built by an image or a filter is
  backed by a list that may repeat its element --- the contexts of a context-free
  table are one \<open>()\<close> per point --- and the generated code then fails with a match
  error. Deduplicating first is the same set.
\<close>

lemma the_elem_set_remdups [code]:
  "the_elem (set xs) =
     (case remdups xs of
        [x] \<Rightarrow> x
      | _ \<Rightarrow> Code.abort (STR ''the_elem: not a singleton'') (\<lambda>_. the_elem (set xs)))"
proof (cases "remdups xs")
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  then show ?thesis
  proof (cases ys)
    case Nil
    with Cons have "set xs = {y}" by (metis set_remdups empty_set list.simps(15))
    with Cons Nil show ?thesis by simp
  next
    case (Cons z zs)
    with \<open>remdups xs = y # ys\<close> show ?thesis by simp
  qed
qed

definition ordered_by_key ::
  "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a set \<Rightarrow> 'a list" where
  "ordered_by_key rank S =
    map
      (\<lambda>k. the_elem (Set.filter (\<lambda>x. rank x = k) S))
      (sorted_list_of_set (rank ` S))"

text \<open>
  The check column: one row per compiled check edge, carrying the edge's label beside
  its node, its condition, and the verdict \<^const>\<open>classify_checks_verdicts\<close> computes
  there. The label is what a consumer finds a source check's row by.
\<close>

definition result_checks_of ::
    "cfg \<Rightarrow> ('ctx, 'a) solved_table \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result) \<Rightarrow> result_check list"
where
  "result_checks_of g r classify =
     map (\<lambda>(u, a, w).
            \<lparr> check_point = u, check_label = ea_check_label a, check_exp = ea_check_cond a,
              check_verdict = point_verdict r classify u (ea_check_cond a) \<rparr>)
       (filter (\<lambda>(u, a, w). is_EA_Check a) (cfg_intra_list g))"

text \<open>
  Which callee contexts a call enters from a caller context: the one the solve itself
  routed it to, or none when the entered state is unreachable, which is exactly when
  the solver's call tree skips the seed publication.
\<close>

definition live_targets ::
    "(pp \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'c option)
       \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'c list" where
  "live_targets succ u ctx ca q = (case succ u ctx ca q of None \<Rightarrow> [] | Some ctx' \<Rightarrow> [ctx'])"

text \<open>
  The globals column lists the global unknowns of the constraint system: with
  flow-insensitive program globals, one unknown per declared global, then for every
  procedure the seed of each context its entry was solved at. A procedure entered at
  no context is listed once, unreachable. Flow-sensitive program globals sit in
  every point's own state and have no unknown of their own.
\<close>

text \<open>
  One row: the state the table filed at a point under a context, with the verdicts of
  the checks and arithmetic obligations there and the steps of the edges leaving it.
  The check, obligation and step lists come grouped by point, built once per report.
\<close>

definition report_row ::
    "('c, vname, mcp_val) solved_run \<Rightarrow> (exp \<Rightarrow> mcp_val \<Rightarrow> check_result)
       \<Rightarrow> (pp, exp list) rbt \<Rightarrow> (pp, arithmetic_obligation list list) rbt
       \<Rightarrow> (pp, (edge_action \<times> pp) list) rbt \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> mcp_val result_state" where
  "report_row sr classify conds obls edges i ctx v =
     (let state = lookup_table (run_table sr) v ctx
      in \<lparr> state_point = v, state_context = i,
           state_value = state,
           state_checks =
             map (\<lambda>cond. (cond, classify_point classify cond state)) (group_lookup conds v),
           state_diagnostics =
             map (\<lambda>obligation. (obligation,
                                  classify_point classify (arithmetic_condition obligation) state))
               (concat (group_lookup obls v)),
           state_steps = map (\<lambda>(a, w). (w, run_step sr v ctx a)) (group_lookup edges v) \<rparr>)"

lemma report_row_simps [simp]:
  "state_point (report_row sr classify conds obls edges i ctx v) = v"
  "state_context (report_row sr classify conds obls edges i ctx v) = i"
  "state_value (report_row sr classify conds obls edges i ctx v)
     = lookup_table (run_table sr) v ctx"
  by (simp_all add: report_row_def Let_def)

definition report_of ::
    "analysis_config \<Rightarrow> ('c \<Rightarrow> order_key) \<Rightarrow> ('c \<Rightarrow> report_context)
       \<Rightarrow> (exp \<Rightarrow> mcp_val \<Rightarrow> check_result) \<Rightarrow> ('c, vname, mcp_val) solved_run \<Rightarrow> imp_prog
       \<Rightarrow> analysis_report" where
  "report_of config ctx_key ctx_tag classify sr p =
     (let g = prog_cfg p;
          r = run_table sr;
          ctxs = ordered_by_key ctx_key (snd ` covered_keys r);
          indexed = enumerate 0 ctxs;
          nodes = cfg_node_list g
            @ sorted_list_of_set (fst ` covered_keys r - set (cfg_node_list g));
          intra = cfg_intra_list g;
          steps = group_by_key (\<lambda>(u, a, w). u) (\<lambda>(u, a, w). Some (a, w)) intra;
          checks = group_by_key (\<lambda>(u, a, w). u)
            (\<lambda>(u, a, w). if is_EA_Check a then Some (ea_check_cond a) else None) intra;
          obligations = group_by_key fst (Some \<circ> snd) (arithmetic_sites g);
          state_at = report_row sr classify checks obligations steps;
          route_at = (\<lambda>u ca ce i ctx.
            \<lparr> route_point = u, route_context = i, route_callee = callee_of_entry ce,
              route_targets =
                (case lookup_table r u ctx of
                   Bot \<Rightarrow> []
                 | Lifted _ \<Rightarrow>
                     remdups (concat (map (context_indices indexed)
                       (live_targets (run_succ sr) u ctx ca (callee_of_entry ce))))) \<rparr>);
          seeds_of = (\<lambda>f.
            (case filter (\<lambda>(i, ctx). (FunctionEntry f, ctx) \<in> covered_keys r) indexed of
               [] \<Rightarrow> [\<lparr> global_unknown = Global_Seed f None, global_state = Bot \<rparr>]
             | entered \<Rightarrow>
                 map (\<lambda>(i, ctx). \<lparr> global_unknown = Global_Seed f (Some i),
                                   global_state = run_seed sr f ctx \<rparr>)
                   entered))
      in \<lparr> report_config = config,
           report_vars = program_vars p,
           report_cfg = g,
           report_contexts = map ctx_tag ctxs,
           report_states =
             concat (map (\<lambda>(i, ctx).
                            map (state_at i ctx)
                              (filter (\<lambda>v. (v, ctx) \<in> covered_keys r) nodes))
                       indexed),
           report_routes =
             concat (map (\<lambda>(u, ca, ce, after).
                            map (\<lambda>(i, ctx). route_at u ca ce i ctx)
                              (filter (\<lambda>(i, ctx). (u, ctx) \<in> covered_keys r) indexed))
                       (cfg_calls_list g)),
           report_checks = result_checks_of g r classify,
           report_globals =
             (case config_globals config of
                Program_Globals_Flow_Sensitive \<Rightarrow> []
              | Program_Globals_Flow_Insensitive \<Rightarrow>
                  map (\<lambda>x. \<lparr> global_unknown = Global_Named x, global_state = run_shared sr x \<rparr>)
                    (declared_global_vars p))
               @ concat (map seeds_of (prog_main_name # prog_procs p)),
           report_diagnostics = arithmetic_diagnostics g r classify \<rparr>)"

subsection \<open>One configuration, one report\<close>

text \<open>
  An entry-state context reads as the formal values the active analyses key it by,
  in activation order, and is listed in the order of those values. Those values
  alone do not tell every context apart --- they skip the fields of inactive
  analyses --- so the whole context breaks ties, which makes the key injective and
  leaves the order of contexts that the values already tell apart unchanged.
\<close>

definition mcp_ctx_values :: "analysis_domain list \<Rightarrow> mcp_ctx \<Rightarrow> abstract_value list" where
  "mcp_ctx_values as ctx = concat (map (\<lambda>a. context_values (registration_of a) ctx) as)"

definition entry_ctx_key :: "analysis_domain list \<Rightarrow> mcp_ctx \<Rightarrow> order_key" where
  "entry_ctx_key as ctx =
     Key_List [Key_List (map abstract_value_key (mcp_ctx_values as ctx)), mcp_ctx_key ctx]"

lemma entry_ctx_key_inject: "entry_ctx_key as a = entry_ctx_key as b \<Longrightarrow> a = b"
  by (simp add: entry_ctx_key_def mcp_ctx_key_inject)

text \<open>
  The one place the context policy is read. Each policy names the registration the
  active analyses run as under the chosen global update rule, solves its equations
  with the executable solver from the program exit at the root context, and reads
  the report off the answer. The logical \<open>None\<close> branch of \<open>solve_c\<close> yields no report.
  Where the solve diverges, the generated code does not return at all, so that
  branch is not an operational timeout result.
\<close>
text \<open>
  The executable boundary, specialised once. The registrations are generic in their
  carrier; these three constants fix it at the combined state and leave only the
  context and global-key types open. Generated code then builds the carrier's
  equality and lattice dictionaries inside each constant rather than inline in every
  branch below.
\<close>

text \<open>
  The placement the configuration chooses: the component as it is, or wrapped by the
  keyed lifter with each program global at its own unknown and a point's state
  recombined against the solved global environment.
\<close>

definition mcp_place_spec :: "program_globals \<Rightarrow> imp_prog \<Rightarrow> mcp_st lifted local_spec
    \<Rightarrow> (pp \<times> 'c, 'k, vname, mcp_st lifted, mcp_st lifted) dg_spec" where
  "mcp_place_spec pg = (case pg of
     Program_Globals_Flow_Sensitive \<Rightarrow> (\<lambda>\<G> c. dg_spec_of c)
   | Program_Globals_Flow_Insensitive \<Rightarrow> (\<lambda>p c. keyed_split_spec (declared_global p)
       (declared_global_vars p) split_cmb split_rl split_global_at split_free c))"

definition mcp_place_cmb ::
    "program_globals \<Rightarrow> imp_prog \<Rightarrow> mcp_st lifted \<Rightarrow> (vname \<Rightarrow> mcp_st lifted)
       \<Rightarrow> mcp_st lifted" where
  "mcp_place_cmb pg = (case pg of
     Program_Globals_Flow_Sensitive \<Rightarrow> (\<lambda>\<G> d e. d)
   | Program_Globals_Flow_Insensitive \<Rightarrow>
       (\<lambda>p d e. split_cmb d (full_view split_global_at (declared_global_vars p) e)))"

definition mcp_place_rl :: "program_globals \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> mcp_st lifted \<Rightarrow> mcp_st lifted" where
  "mcp_place_rl pg = (case pg of
     Program_Globals_Flow_Sensitive \<Rightarrow> (\<lambda>\<G> d. d) | Program_Globals_Flow_Insensitive \<Rightarrow> (\<lambda>\<G>. split_rl))"

definition mcp_place_rg :: "program_globals \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> mcp_st lifted \<Rightarrow> mcp_st lifted" where
  "mcp_place_rg pg = (\<lambda>\<G> d. Bot)"

definition mcp_place_inits :: "program_globals \<Rightarrow> analysis_domain list
    \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (vname \<times> mcp_st lifted) list" where
  "mcp_place_inits pg as = (case pg of
     Program_Globals_Flow_Sensitive \<Rightarrow> (\<lambda>\<G> p. [])
   | Program_Globals_Flow_Insensitive \<Rightarrow>
       (\<lambda>\<G> p. map (\<lambda>x. (x, split_global_at x (Lifted (mcp_init as)))) (declared_global_vars p)))"

lemmas mcp_place_defs = mcp_place_spec_def mcp_place_cmb_def mcp_place_rl_def mcp_place_rg_def
  mcp_place_inits_def

definition mcp_equations ::
    "analysis_domain list \<Rightarrow> program_globals \<Rightarrow> 'k \<Rightarrow> (vname \<Rightarrow> 'k) \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
       \<Rightarrow> ((vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> mcp_st lifted \<Rightarrow> call_action \<Rightarrow> 'c) \<Rightarrow> 'c
       \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> 'c, 'k, (mcp_st lifted, mcp_st lifted) dg_state) eqsT" where
  "mcp_equations as pg buffer global seed route root =
     dg_pipeline.equations (mcp_comp as) (mcp_init as) buffer global seed route root
       (mcp_place_spec pg) (mcp_place_rg pg) (mcp_place_inits pg as)"

definition mcp_solve_c ::
    "globals_rule \<Rightarrow> (pp \<times> 'c, 'k, (mcp_st lifted, mcp_st lifted) dg_state) eqsT \<Rightarrow> pp \<times> 'c
       \<Rightarrow> ((pp \<times> 'c) set \<times> (pp \<times> 'c + 'k \<Rightarrow> (mcp_st lifted, mcp_st lifted) dg_state)) option"
  where
  "mcp_solve_c = TD_side_rule_Interp_solve_c"

definition mcp_run_of ::
    "analysis_domain list \<Rightarrow> program_globals \<Rightarrow> (vname \<Rightarrow> 'k) \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k)
       \<Rightarrow> ((vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> mcp_st lifted \<Rightarrow> call_action \<Rightarrow> 'c)
       \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> 'c) set \<times> (pp \<times> 'c + 'k \<Rightarrow> (mcp_st lifted, mcp_st lifted) dg_state)
       \<Rightarrow> ('c, vname, mcp_val) solved_run" where
  "mcp_run_of as pg global seed route =
     dg_pipeline.solved_run_of (mcp_comp as) (mcp_emp as) mcp_rd global seed route
       (mcp_place_cmb pg) (mcp_place_rl pg)"

lemmas mcp_wrappers = mcp_equations_def mcp_solve_c_def mcp_run_of_def


fun analysis_report_of :: "analysis_config \<Rightarrow> imp_prog \<Rightarrow> analysis_report option" where
  "analysis_report_of (Analysis_Config as r Ctx_None pg) p =
     map_option
       (\<lambda>sol. report_of (Analysis_Config as r Ctx_None pg) (\<lambda>_. Key_List []) (\<lambda>_. Report_Unit)
          (mcp_classify (activation as))
          (mcp_run_of (activation as) pg Analysis_Global Activation_Seed (\<lambda>_. route_unit)
             (declared_global p) p sol) p)
       (mcp_solve_c r
          (mcp_equations (activation as) pg Analysis_Buffer Analysis_Global Activation_Seed
             (\<lambda>_. route_unit) () (declared_global p) p)
          (cfg_exit (prog_cfg p), ()))"
| "analysis_report_of (Analysis_Config as r Ctx_EntryState pg) p =
     map_option
       (\<lambda>sol. report_of (Analysis_Config as r Ctx_EntryState pg)
          (entry_ctx_key (activation as)) Report_Entry (mcp_classify (activation as))
          (mcp_run_of (activation as) pg Analysis_Global Activation_Seed
             (mcp_formals_route (activation as)) (declared_global p) p sol) p)
       (mcp_solve_c r
          (mcp_equations (activation as) pg Analysis_Buffer Analysis_Global Activation_Seed
             (mcp_formals_route (activation as)) mcp_root_ctx (declared_global p) p)
          (cfg_exit (prog_cfg p), mcp_root_ctx))"
| "analysis_report_of (Analysis_Config as r (Ctx_CallString k) pg) p =
     map_option
       (\<lambda>sol. report_of (Analysis_Config as r (Ctx_CallString k) pg)
          (\<lambda>ctx. Key_List (map Key_Node ctx)) Report_Call_String
          (mcp_classify (activation as))
          (mcp_run_of (activation as) pg Analysis_Global Activation_Seed
             (\<lambda>_. cs_route k) (declared_global p) p sol) p)
       (mcp_solve_c r
          (mcp_equations (activation as) pg Analysis_Buffer Analysis_Global Activation_Seed
             (\<lambda>_. cs_route k) [] (declared_global p) p)
          (cfg_exit (prog_cfg p), []))"

subsection \<open>The public operation\<close>

text \<open>
  Four answers: an invalid configuration asks for no run, a malformed program was
  never analysed, the logical \<open>None\<close> branch of the executable solve has no report,
  and every other run hands back its report.
\<close>

datatype 'r analysis_answer =
    Invalid_Activation
  | Malformed_Program
  | No_Answer
  | Analysed 'r

definition run_voblint :: "analysis_config \<Rightarrow> imp_prog \<Rightarrow> analysis_report analysis_answer"
where
  "run_voblint config p =
     (if \<not> valid_config config then Invalid_Activation
      else if \<not> wf_program_compile_input_exec p then Malformed_Program
      else case analysis_report_of config p of
             None \<Rightarrow> No_Answer
           | Some res \<Rightarrow> Analysed res)"

end
