theory Analysis_Run
  imports
    Analysis_Config
    Dispatch_Carrier
    Arithmetic_Diagnostics
    Voblint_Analysis_Sign.Sign_Analyses
    Voblint_Analysis_Interval.Interval_Analyses
    Voblint_Analysis_Int.Int_Analyses
    Voblint_Analysis_Parity.Parity_Analyses
    Voblint_Analysis_Congruence.Congruence_Analyses
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Code_Abstract_Char"
begin

section \<open>Running one configuration once\<close>

text \<open>
  The public analysis operation. A caller hands over the three choices that
  decide what gets solved and a program, and receives the solve as data: every
  covered point-and-context state, the contexts each call enters, the check
  column and the arithmetic diagnostics. One solve stands behind all of them, and
  every rendering of them --- text, graphs, report pages --- is built outside this
  development from that one result.

  Nothing outside this theory decides which analyser runs: every branch below reads
  the one table its domain, context policy and global update rule name together.
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

  A state also lists, for every edge leaving its point, that edge's target and what
  the edge's own step makes of the state. Where the target is a join of several
  incoming edges -- a loop head, the point after a branch -- this is the only place
  the effect of one statement survives.
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
  state_steps :: "(pp \<times> (vname \<times> 'v) list lifted) list"

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
  A global unknown is the analysis-wide global or the seed of a procedure entry,
  named by the procedure and the index of the context it was entered at; a seed
  without a context belongs to a procedure the solve never entered.
\<close>

datatype result_global_key =
    Global_Shared
  | Global_Seed pname "nat option"

record 'v result_global =
  global_key :: result_global_key
  global_state :: "(vname \<times> 'v) list lifted"

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
       state_diagnostics = state_diagnostics st,
       state_steps =
         map (\<lambda>(w, s). (w, map_lift (map (\<lambda>(x, v). (x, f v))) s)) (state_steps st) \<rparr>"

definition map_result_global :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v result_global \<Rightarrow> 'w result_global" where
  "map_result_global f g =
     \<lparr> global_key = global_key g,
       global_state = map_lift (map (\<lambda>(x, v). (x, f v))) (global_state g) \<rparr>"

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

text \<open>
  A state lists every variable some procedure of the program declares: a program-wide
  superset of any one activation's scope, so no point's state misses a name its own
  procedure reads.
\<close>

definition program_vars :: "imp_prog \<Rightarrow> vname list" where
  "program_vars p =
     remdups (concat (map (scope_vnames_list p) (prog_main_name # prog_procs p)))"

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
    "cfg \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result) \<Rightarrow> result_check list"
where
  "result_checks_of g r classify =
     map (\<lambda>(u, a, w).
            \<lparr> check_point = u, check_label = ea_check_label a, check_exp = ea_check_cond a,
              check_verdict = aggregate_verdicts
                ((\<lambda>ctx. classify_point classify (ea_check_cond a) (lookup_context r u ctx))
                   ` contexts_at r u) \<rparr>)
       (filter (\<lambda>(u, a, w). is_EA_Check a) (cfg_intra_list g))"

text \<open>
  The globals column lists the global unknowns of the constraint system rather than
  the program's global variables, whose values sit in every point's state: the
  analysis-wide global, then for every procedure the seed of each context its entry
  was solved at. A procedure entered at no context is listed once, unreachable.
\<close>

definition run_result_of ::
    "('a \<Rightarrow> abstract_value) \<Rightarrow> ('c \<Rightarrow> order_key) \<Rightarrow> ('c \<Rightarrow> abstract_value analysis_context)
       \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'c list)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result) \<Rightarrow> ('c, 'a abs_state) analysis_result
       \<Rightarrow> 'a abs_state lifted \<Rightarrow> (pname \<Rightarrow> 'c \<Rightarrow> 'a abs_state lifted)
       \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> edge_action \<Rightarrow> 'a abs_state lifted)
       \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result" where
  "run_result_of into ctx_key ctx_view targets classify r shared seed_at step_at p =
     (let g = prog_cfg p;
          vars = program_vars p;
          view = map_lift (\<lambda>st. map (\<lambda>x. (x, into (st x))) vars);
          ctxs = ordered_by_key ctx_key (snd ` result_keys r);
          indexed = enumerate 0 ctxs;
          nodes = cfg_node_list g;
          intra = cfg_intra_list g;
          steps = group_by_key (\<lambda>(u, a, w). u) (\<lambda>(u, a, w). Some (a, w)) intra;
          checks = group_by_key (\<lambda>(u, a, w). u)
            (\<lambda>(u, a, w). if is_EA_Check a then Some (ea_check_cond a) else None) intra;
          obligations = group_by_key fst (Some \<circ> snd) (arithmetic_sites g);
          state_at = (\<lambda>i ctx v.
            \<lparr> state_point = v, state_context = i,
              state_value = view (lookup_context r v ctx),
              state_checks =
                map (\<lambda>cond. (cond, classify_point classify cond (lookup_context r v ctx)))
                  (group_lookup checks v),
              state_diagnostics =
                map (\<lambda>obligation. (obligation,
                                     classify_point classify (arithmetic_condition obligation)
                                       (lookup_context r v ctx)))
                  (concat (group_lookup obligations v)),
              state_steps =
                map (\<lambda>(a, w). (w, view (step_at v ctx a))) (group_lookup steps v)
            \<rparr>);
          route_at = (\<lambda>u ca ce i ctx.
            \<lparr> route_point = u, route_context = i, route_callee = callee_of_entry ce,
              route_targets =
                (case lookup_context r u ctx of
                   Bot \<Rightarrow> []
                 | Lifted st \<Rightarrow>
                     remdups (concat (map (context_indices indexed)
                       (targets u ctx ca (callee_of_entry ce) st)))) \<rparr>);
          seeds_of = (\<lambda>f.
            (case filter (\<lambda>(i, ctx). (FunctionEntry f, ctx) \<in> result_keys r) indexed of
               [] \<Rightarrow> [\<lparr> global_key = Global_Seed f None, global_state = Bot \<rparr>]
             | entered \<Rightarrow>
                 map (\<lambda>(i, ctx). \<lparr> global_key = Global_Seed f (Some i),
                                   global_state = view (seed_at f ctx) \<rparr>)
                   entered))
      in \<lparr> res_cfg = g,
           res_contexts = map ctx_view ctxs,
           res_states =
             concat (map (\<lambda>(i, ctx).
                            map (state_at i ctx)
                              (filter (\<lambda>v. (v, ctx) \<in> result_keys r) nodes))
                       indexed),
           res_routes =
             concat (map (\<lambda>(u, ca, ce, after).
                            map (\<lambda>(i, ctx). route_at u ca ce i ctx)
                              (filter (\<lambda>(i, ctx). (u, ctx) \<in> result_keys r) indexed))
                       (cfg_calls_list g)),
           res_checks = result_checks_of g r classify,
           res_globals =
             \<lparr> global_key = Global_Shared, global_state = view shared \<rparr>
               # concat (map seeds_of (prog_main_name # prog_procs p)),
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
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (unit, ('a::executable_domain) abs_state) analysis_result \<times> 'a abs_state lifted
            \<times> (pname \<Rightarrow> unit \<Rightarrow> 'a abs_state lifted)
            \<times> (pp \<Rightarrow> unit \<Rightarrow> edge_action \<Rightarrow> 'a abs_state lifted)
       \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result" where
  "unit_run_result into enter classify solved p =
     (case solved of (r, shared, seed_at, step_at) \<Rightarrow>
        run_result_of into (\<lambda>_. Key_List []) (\<lambda>_. Context_Unit)
          (entered_targets enter (\<lambda>_ _ _ _. ()) p) classify r shared seed_at step_at p)"

definition entry_state_run_result ::
    "('a \<Rightarrow> abstract_value)
       \<Rightarrow> ((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> ('a list, ('a::executable_domain) abs_state) analysis_result \<times> 'a abs_state lifted
            \<times> (pname \<Rightarrow> 'a list \<Rightarrow> 'a abs_state lifted)
            \<times> (pp \<Rightarrow> 'a list \<Rightarrow> edge_action \<Rightarrow> 'a abs_state lifted)
       \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result" where
  "entry_state_run_result into enter classify solved p =
     (case solved of (r, shared, seed_at, step_at) \<Rightarrow>
        run_result_of into (\<lambda>ctx. Key_List (map (abstract_value_key \<circ> into) ctx))
          (\<lambda>ctx. Context_Entry (map into ctx))
          (entered_targets enter
             (\<lambda>_ _ entered ca.
                case ca of CallEdge dst pars args \<Rightarrow> formals_context pars entered) p)
          classify r shared seed_at step_at p)"

definition call_string_run_result ::
    "('a \<Rightarrow> abstract_value)
       \<Rightarrow> ((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result)
       \<Rightarrow> (call_string, ('a::executable_domain) abs_state) analysis_result \<times> 'a abs_state lifted
            \<times> (pname \<Rightarrow> call_string \<Rightarrow> 'a abs_state lifted)
            \<times> (pp \<Rightarrow> call_string \<Rightarrow> edge_action \<Rightarrow> 'a abs_state lifted)
       \<Rightarrow> nat \<Rightarrow> imp_prog \<Rightarrow> abstract_value run_result" where
  "call_string_run_result into enter classify solved k p =
     (case solved of (r, shared, seed_at, step_at) \<Rightarrow>
        run_result_of into (\<lambda>ctx. Key_List (map Key_Node ctx)) Context_Call_String
          (entered_targets enter (\<lambda>u ctx _ _. take k (u # ctx)) p)
          classify r shared seed_at step_at p)"

subsection \<open>One configuration, one typed result\<close>

text \<open>
  Each branch names the one solve its domain and context policy run under the
  chosen global update rule, and hands its table and global unknowns to the builder
  of that context policy together with the domain's tag and entry transfer. Every
  combination has a solve.
\<close>

fun analysis_result ::
    "analysis_domain \<Rightarrow> globals_rule \<Rightarrow> context_mode \<Rightarrow> imp_prog
       \<Rightarrow> abstract_value run_result" where
  "analysis_result Sign_Analysis r Ctx_None p =
     unit_run_result SignValue enter_sign_for sign_classify_check
       (sign_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Sign_Analysis r Ctx_EntryState p =
     entry_state_run_result SignValue enter_sign_for sign_classify_check
       (sign_es_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Sign_Analysis r (Ctx_CallString k) p =
     call_string_run_result SignValue enter_sign_for sign_classify_check
       (sign_cs_rule.result_with_globals k r (declared_global p) p) k p"
| "analysis_result Interval_Analysis r Ctx_None p =
     unit_run_result IntervalValue enter_ivl_for interval_classify_check
       (interval_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Interval_Analysis r Ctx_EntryState p =
     entry_state_run_result IntervalValue enter_ivl_for interval_classify_check
       (interval_es_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Interval_Analysis r (Ctx_CallString k) p =
     call_string_run_result IntervalValue enter_ivl_for interval_classify_check
       (interval_cs_rule.result_with_globals k r (declared_global p) p) k p"
| "analysis_result Int_Analysis r Ctx_None p =
     unit_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint) int_classify_check
       (int_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Int_Analysis r Ctx_EntryState p =
     entry_state_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint) int_classify_check
       (int_es_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Int_Analysis r (Ctx_CallString k) p =
     call_string_run_result IntDomValue (enter_int_dom_for Refine_Fixpoint) int_classify_check
       (int_cs_rule.result_with_globals k r (declared_global p) p) k p"
| "analysis_result Parity_Analysis r Ctx_None p =
     unit_run_result ParityValue enter_parity_for parity_classify_check
       (parity_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Parity_Analysis r Ctx_EntryState p =
     entry_state_run_result ParityValue enter_parity_for parity_classify_check
       (parity_es_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Parity_Analysis r (Ctx_CallString k) p =
     call_string_run_result ParityValue enter_parity_for parity_classify_check
       (parity_cs_rule.result_with_globals k r (declared_global p) p) k p"
| "analysis_result Congruence_Analysis r Ctx_None p =
     unit_run_result CongruenceValue enter_congruence_for congruence_classify_check
       (congruence_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Congruence_Analysis r Ctx_EntryState p =
     entry_state_run_result CongruenceValue enter_congruence_for congruence_classify_check
       (congruence_es_rule.result_with_globals r (declared_global p) p) p"
| "analysis_result Congruence_Analysis r (Ctx_CallString k) p =
     call_string_run_result CongruenceValue enter_congruence_for congruence_classify_check
       (congruence_cs_rule.result_with_globals k r (declared_global p) p) k p"

subsection \<open>The public operation\<close>

text \<open>
  Two answers: a malformed program was never analysed, and every well-formed one is.
\<close>

datatype 'v analysis_answer =
    Malformed_Program
  | Analysed "'v run_result"

definition analyse_program ::
    "analysis_domain \<Rightarrow> globals_rule \<Rightarrow> context_mode \<Rightarrow> imp_prog
       \<Rightarrow> abstract_value analysis_answer" where
  "analyse_program kind rule ctx p =
     (if wf_program_compile_input_exec p then Analysed (analysis_result kind rule ctx p)
      else Malformed_Program)"

fun map_analysis_answer :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v analysis_answer \<Rightarrow> 'w analysis_answer" where
  "map_analysis_answer f Malformed_Program = Malformed_Program"
| "map_analysis_answer f (Analysed res) = Analysed (map_run_result f res)"

text \<open>
  The operation a consumer outside Isabelle calls: \<^const>\<open>analyse_program\<close>, with each
  domain's rendering applied to every abstract value and nothing else changed.
\<close>

definition run_voblint ::
    "analysis_domain \<Rightarrow> globals_rule \<Rightarrow> context_mode \<Rightarrow> imp_prog
       \<Rightarrow> String.literal analysis_answer" where
  "run_voblint kind rule ctx p =
     map_analysis_answer string_of_abstract_value
       (analyse_program kind rule ctx p)"

end

