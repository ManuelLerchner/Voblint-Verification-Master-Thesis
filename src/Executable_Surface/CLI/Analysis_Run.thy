theory Analysis_Run
  imports
    Arithmetic_Diagnostics
    Dispatch_Carrier
    MCP_Split
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Abstract_Char"
begin

section \<open>The report of one run\<close>

text \<open>
  A solve is handed back as a report: every covered point-and-context state, the
  contexts each call enters, the check column and the arithmetic diagnostics. One
  solve stands behind all of them. The report holds semantic states, never their
  rendering; text, graphs and report pages are built from it by a projection outside
  the theorems.
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

record ('e, 's) result_state =
  state_point :: pp
  state_context :: nat
  state_value :: "'s lifted"
  state_checks :: "('e \<times> contextual_verdict) list"
  state_diagnostics :: "('e arithmetic_obligation \<times> contextual_verdict) list"
  state_steps :: "(pp \<times> 's lifted) list"

record call_route =
  route_point :: pp
  route_context :: nat
  route_callee :: pname
  route_targets :: "nat list"

record 'e result_check =
  check_point :: pp
  check_label :: check_label
  check_exp :: 'e
  check_verdict :: contextual_verdict

text \<open>
  A global unknown is a program global kept at its own unknown, or the seed of a
  procedure entry, named by the procedure and the index of the context it was
  entered at; a seed without a context belongs to a procedure the solve never
  entered.
\<close>

datatype 'n result_global_unknown =
    Global_Named 'n
  | Global_Seed pname "nat option"

record ('n, 's) result_global =
  global_unknown :: "'n result_global_unknown"
  global_state :: "'s lifted"

definition map_result_state :: "('s \<Rightarrow> 't) \<Rightarrow> ('e, 's) result_state \<Rightarrow> ('e, 't) result_state" where
  "map_result_state f st =
     \<lparr> state_point = state_point st,
       state_context = state_context st,
       state_value = map_lift f (state_value st),
       state_checks = state_checks st,
       state_diagnostics = state_diagnostics st,
       state_steps = map (\<lambda>(w, s). (w, map_lift f s)) (state_steps st) \<rparr>"

definition map_result_global :: "('s \<Rightarrow> 't) \<Rightarrow> ('n, 's) result_global \<Rightarrow> ('n, 't) result_global" where
  "map_result_global f g =
     \<lparr> global_unknown = global_unknown g,
       global_state = map_lift f (global_state g) \<rparr>"

subsection \<open>The report\<close>

text \<open>
  A context is kept as the policy's own value, tagged by policy, so one report type
  serves every policy. The report also keeps the configuration, which names the
  concretization its states are read through, and the program's variables, which a
  rendering lists. The configuration, the context tag, the variables, the expressions,
  the global names and the states are parameters, so one report and one builder serve
  every language an analysis runs on.
\<close>

datatype 'm report_context =
    Report_Unit
  | Report_Entry 'm
  | Report_Call_String "pp list"

record ('k, 'x, 'vr, 'e, 'n, 's) analysis_report =
  report_config :: 'k
  report_vars :: "'vr list"
  report_cfg :: "('vr, 'e) gcfg"
  report_contexts :: "'x list"
  report_states :: "('e, 's) result_state list"
  report_routes :: "call_route list"
  report_checks :: "'e result_check list"
  report_globals :: "('n, 's) result_global list"
  report_diagnostics :: "'e arithmetic_diagnostic list"

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
    "('vr::linorder, 'e::linorder) gcfg \<Rightarrow> ('ctx, 'a) solved_table
       \<Rightarrow> ('e \<Rightarrow> 'a \<Rightarrow> check_result) \<Rightarrow> 'e result_check list"
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
    "(pp \<Rightarrow> 'c \<Rightarrow> ('vr, 'e) gcall_action \<Rightarrow> pname \<Rightarrow> 'c option)
       \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> ('vr, 'e) gcall_action \<Rightarrow> pname \<Rightarrow> 'c list" where
  "live_targets succ u ctx ca q = (case succ u ctx ca q of None \<Rightarrow> [] | Some ctx' \<Rightarrow> [ctx'])"

text \<open>
  The globals column lists the global unknowns of the constraint system: one unknown
  per global name the placement keeps apart, then for every procedure the seed of each
  context its entry was solved at. A procedure entered at no context is listed once,
  unreachable. Globals the placement keeps in every point's own state have no unknown
  of their own.
\<close>

text \<open>
  One row: the state the table filed at a point under a context, with the verdicts of
  the checks and arithmetic obligations there and the steps of the edges leaving it.
  The check, obligation and step lists come grouped by point, built once per report.
\<close>

definition report_row ::
    "('c, 'n, 's) solved_run \<Rightarrow> (exp \<Rightarrow> 's \<Rightarrow> check_result)
       \<Rightarrow> (exp arithmetic_obligation \<Rightarrow> 's \<Rightarrow> check_result)
       \<Rightarrow> (pp, exp list) rbt \<Rightarrow> (pp, exp arithmetic_obligation list list) rbt
       \<Rightarrow> (pp, ((var_id, exp) gedge_action \<times> pp) list) rbt \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> pp
       \<Rightarrow> (exp, 's) result_state" where
  "report_row sr classify classify_ob conds obls edges i ctx v =
     (let state = lookup_table (run_table sr) v ctx
      in \<lparr> state_point = v, state_context = i,
           state_value = state,
           state_checks =
             map (\<lambda>c. (c, classify_point classify c state)) (group_lookup conds v),
           state_diagnostics =
             map (\<lambda>obligation. (obligation, classify_point classify_ob obligation state))
               (concat (group_lookup obls v)),
           state_steps = map (\<lambda>(a, w). (w, run_step sr v ctx a)) (group_lookup edges v) \<rparr>)"

lemma report_row_simps [simp]:
  "state_point (report_row sr classify classify_ob conds obls edges i ctx v) = v"
  "state_context (report_row sr classify classify_ob conds obls edges i ctx v) = i"
  "state_value (report_row sr classify classify_ob conds obls edges i ctx v)
     = lookup_table (run_table sr) v ctx"
  by (simp_all add: report_row_def Let_def)

text \<open>
  The builder reads the program only through what it is handed: its variables, its
  graph, the global names kept at their own unknowns, the arithmetic obligation sites
  with the classifier that decides one, and its procedures.
\<close>

definition report_of ::
    "'k \<Rightarrow> var_id list \<Rightarrow> (var_id, exp) gcfg \<Rightarrow> 'n list
       \<Rightarrow> (pp \<times> exp arithmetic_obligation list) list
       \<Rightarrow> (exp arithmetic_obligation \<Rightarrow> 's \<Rightarrow> check_result)
       \<Rightarrow> pname list \<Rightarrow> ('c \<Rightarrow> order_key) \<Rightarrow> ('c \<Rightarrow> 'x)
       \<Rightarrow> (exp \<Rightarrow> 's \<Rightarrow> check_result) \<Rightarrow> ('c, 'n, 's) solved_run
       \<Rightarrow> ('k, 'x, var_id, exp, 'n, 's) analysis_report" where
  "report_of config vars g globals sites classify_ob procs ctx_key ctx_tag classify sr =
     (let r = run_table sr;
          ctxs = ordered_by_key ctx_key (snd ` covered_keys r);
          indexed = enumerate 0 ctxs;
          nodes = cfg_node_list g
            @ sorted_list_of_set (fst ` covered_keys r - set (cfg_node_list g));
          intra = cfg_intra_list g;
          steps = group_by_key (\<lambda>(u, a, w). u) (\<lambda>(u, a, w). Some (a, w)) intra;
          checks = group_by_key (\<lambda>(u, a, w). u)
            (\<lambda>(u, a, w). if is_EA_Check a then Some (ea_check_cond a) else None) intra;
          obligations = group_by_key fst (Some \<circ> snd) sites;
          state_at = report_row sr classify classify_ob checks obligations steps;
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
           report_vars = vars,
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
             map (\<lambda>x. \<lparr> global_unknown = Global_Named x, global_state = run_shared sr x \<rparr>)
               globals
             @ concat (map seeds_of procs),
           report_diagnostics = arithmetic_diagnostics sites r classify_ob \<rparr>)"

subsection \<open>The answer\<close>

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

end
