theory Interval_Analyses
  imports
    Interval_Sound
    Interval_Assembly
    Interval_Contextual_Assembly
    Interval_Classify
    "Voblint_Result.Routed_Live_Keys"
    "Voblint_Framework.Call_String_Context"
    "Voblint_Framework.Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_VIMP.VIMP_Program"
    "TD.TD_side_upd_rule"
begin

chapter \<open>How Interval is run under each context-sensitive policy\<close>

text \<open>
  Interval's analysis package -- specification, concretization and soundness --
  lives in \<^theory>\<open>Voblint_Analysis_Interval.Interval_Sound\<close> and mentions no
  context. This theory supplies the other half for the two policies that route a
  call to more than one context: the call-string run, which truncates the caller's
  string at a runtime bound, and the entry-state run, which keys a callee on the
  abstract values its formals hold on entry.

  Neither policy has a pipeline of its own here. Both are interpretations of
  \<^locale>\<open>routed_dg_analysis\<close>, the same one Sign, Parity and Congruence
  interpret; the context-insensitive run is \<open>Interval_Assembly\<close>'s four
  interpretations of the unit assembly, one per update rule. Production reporting
  selects Apinis warrowing at both policies because Interval has infinite
  ascending chains; the other three disciplines are in
  \<open>Interval_Solver_Analyses\<close>, and differ from these by a solver name.

  What is Interval's own, and stays here, is the presentation-side routing: the
  question "which callee context does this call site route to, read off a solved
  table rather than the solver's map" has an Interval-specific answer, because
  deciding whether the entered callee frame is dead needs a bottom test on the
  formals rather than the non-executable whole-state one.
\<close>

section \<open>Interval at the call-string context\<close>

text \<open>
  A call string is the last \<open>k\<close> call sites on the stack, so a procedure entered
  from two places is analysed twice rather than once at the join.
  \<^const>\<open>cs_route\<close> never reads the state it is handed, which is what makes
  \<open>fun_route_activation_collect_sound\<close> --- the endpoint for a route that is a
  function of the call site and the caller's context alone --- the applicable one,
  at the trace-semantic counterpart \<^const>\<open>cs_context\<close>.

  \<open>k\<close> is runtime data, so the interpretation is local to a context fixing it and
  the published constants below are applications of the pipeline's own constants
  at \<^term>\<open>cs_route k\<close>.
\<close>

text \<open>
  The registration and the two re-exports that cite its binder are generated
  --- \<^theory>\<open>Voblint_Analysis_Interval.Interval_Contextual_Assembly\<close>.
  They travel together because \<open>interval_cs\<close> is a plain
  \<^theory_text>\<open>interpretation\<close> inside a context fixing \<open>k\<close>, and such a
  binder does not escape it. The three constants every domain publishes at a
  routed context --- the \<open>_for\<close> hop, the result at the program's own
  globals, and the verdict report --- are generated beside it.

  The two below are not, because no other domain publishes them: the equation
  system itself and its raw solution, which name no report and route through no
  classifier. They are what an example pins a solved value against, one unknown
  at a time, rather than what a caller reads a verdict off.
\<close>


subsection \<open>The call-string equation system and its solution\<close>

definition cs_call_string_eqs_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string, call_string_gk,
            (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "cs_call_string_eqs_prog k =
     routed_dg_pipeline.equations ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k)"

definition cs_call_string_sol_prog ::
    "nat \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> call_string) set
            \<times> (pp \<times> call_string + call_string_gk
                 \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "cs_call_string_sol_prog k =
     routed_dg_pipeline.solution ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

section \<open>Interval at the entry-state context\<close>

text \<open>
  Keying a callee on the abstract values its formals hold on entry.
  \<^const>\<open>exec_formals_route\<close> genuinely reads the state it is handed --- the callee
  frame the routed generator has already entered --- so the applicable endpoint is
  \<open>entry_state_activation_collect_sound\<close>, whose admitted-context relation is the
  one the entry answer induces rather than the graph of a function on stores.

  The definitions in this section are Interval's presentation-side vocabulary:
  what the entered callee frame is, when it is dead, and which context a call site
  routes to when the answer is read off a published table rather than off the
  solver's own map. None of them takes part in building the equation system.
\<close>
subsection \<open>The routed context hooks, generic over the compiled program\<close>

text \<open>
  The one D/G spec every hook below shares.
\<close>

text \<open>
  \<open>interval_spec\<close> is the Base-style whole-state specification
  (\<^const>\<open>local_state_dg_spec_st_for_lifted\<close>), the same one context-insensitive Interval already
  solves over in \<^const>\<open>interval_td_equations\<close>, at the same
  \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close> primitives: the local unknown
  \<^typ>\<open>ivl exec_dg_st lifted\<close> carries every VIMP variable, global and local alike, so a
  global is read and written exactly where a local is. The solver-global carrier stays
  diagonal at \<^typ>\<open>ivl exec_dg_st lifted\<close> -- the type the keyed generator and its
  warrowing solver instance already fix -- but is inert: every field of
  \<^const>\<open>local_state_dg_spec_st_for_lifted\<close> threads its incoming \<open>g\<close> through unchanged, so
  \<open>Inr (Analysis_Global ())\<close> is never read back to reconstruct program state.

  \<open>interval_spec\<close> carries an explicit executable bottom predicate and solves over the lifted
  carrier, mirroring \<open>interval_conf_eqs_prog\<close>'s convention of taking \<open>empty_pred\<close> as a
  caller-supplied parameter rather than deriving it internally. Callers with a concrete
  program supply \<open>resolved_st_q_is_bot_for (declared_global_vars p)\<close>, exact for
  \<^const>\<open>is_empty_state\<close> (\<open>resolved_st_q_is_bot_for_iff\<close>).\<close>

text \<open>
  \<^const>\<open>formals_context\<close> (\<^theory>\<open>Voblint_Framework.Routed_Context\<close>)
  reads the entered callee formals off an arbitrary \<^const>\<open>CallEdge\<close> generically,
  but only at the semantic \<^typ>\<open>'a abs_state\<close> carrier, not the executable
  \<^typ>\<open>'a exec_dg_st\<close> one this equation system solves over: the entered callee
  store is materialized here by the same \<^const>\<open>ivl_enter_st_for\<close> primitive
  \<open>interval_spec\<close>'s own \<open>dgs_enter\<close> field applies and read back through
  \<^const>\<open>lookup_resolved_st_q\<close>, then \<^const>\<open>formals_context\<close> -- the same generic
  per-variable projection -- reads off the formals. The caller's whole state, globals
  included, feeds that entry, so a call argument mentioning a global is routed at the
  global's own abstract value rather than at \<open>bot\<close>.
\<close>

definition entry_state_enter_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st \<Rightarrow> ivl exec_dg_st" where
  "entry_state_enter_exec gs ca s =
     bind_formals_resolved_q gs (ce_formals ca)
       (map (\<lambda>e. aval_ivl e (fun_of_resolved_st_q_for gs s)) (ce_args ca))
       (enter_frame_D_resolved_q ivl_top s)"

lemma ivl_enter_st_for_call_info_of_eq_entry_state_enter_exec:
  "ivl_enter_st_for gs (call_info_of ca p) s = entry_state_enter_exec gs ca s"
  unfolding entry_state_enter_exec_def by simp

definition entry_state_enter_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state" where
  "entry_state_enter_abs gs ca s =
     enter_ivl_for gs (ce_formals ca) (ce_args ca) s"

lemma enter_ivl_ci_for_call_info_of_eq_entry_state_enter_abs:
  "enter_ivl_ci_for gs (call_info_of ca p) s = entry_state_enter_abs gs ca s"
  unfolding entry_state_enter_abs_def ivl_tf.enter_ci_for_def ivl_tf.enter_for_def
  by simp

definition entry_state_entered ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool)
       \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st lifted" where
  "entry_state_entered gs empty_pred d ca =
     transfer_lift empty_pred (entry_state_enter_exec gs ca) d"

lemma enter_st_interval_eq_entry_state_entered:
  "transfer_lift empty_pred (ivl_enter_st_for gs (call_info_of ca p)) d =
   entry_state_entered gs empty_pred d ca"
  unfolding entry_state_entered_def
  by (cases d)
     (simp_all add: transfer_lift_def normalize_lift_def entry_state_enter_exec_def)

definition entry_state_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool)
       \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route gs empty_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars
          (\<lambda>x. lookup_resolved_st_q
                 (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)
                 (location_of gs x)))"

definition entry_state_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> ivl list
       \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_gen gs empty_pred u ctx d ca = entry_state_route gs empty_pred d ca"

text \<open>
  The same routing decision taken on a caller state that has already left the
  executable substrate: the argument is the \<^typ>\<open>ivl abs_state\<close> a
  \<^const>\<open>Lifted\<close> point of an \<^type>\<open>analysis_result\<close> hands out, so a
  consumer of a solved table can recompute a call's callee context without
  reopening the solver's own solution map.

  The type is \<^typ>\<open>ivl abs_state\<close>, not \<^typ>\<open>ivl abs_state lifted\<close>, on
  purpose: reachability is the caller's case split, decided once by
  \<^const>\<open>readback_result_value\<close> when the table was built, and an \<^const>\<open>Bot\<close>
  point has no call edge to route at all.

  A live caller can still enter a callee frame that is itself semantically
  empty, e.g. an actual argument whose abstract value is already bottom. In
  that case \<^const>\<open>entry_state_route\<close> does not skip routing: it reports the
  all-\<^const>\<open>bot\<close> formal context the solver actually materialized a (dead)
  callee activation under, and that all-\<^const>\<open>bot\<close> context is a real,
  distinct context, never the empty list \<open>[]\<close>, which is a legitimate root
  or zero-formal context in its own right and must not double as a sentinel
  for "no route". So \<open>entry_state_callee_ctx\<close> answers \<^const>\<open>None\<close> exactly
  on this case, restricting the bottom test that decides it to the finite
  list of formals \<open>entered_is_bot_for\<close> below, rather than repeating the
  non-executable whole-state test \<^const>\<open>is_empty_state\<close> quantifies over all
  of \<^typ>\<open>vname\<close>, which is what keeps \<open>entry_state_route_abs\<close> non-executable.

  It routes on the static \<^const>\<open>CallEdge\<close> and the entered caller state alone,
  matching \<^const>\<open>entry_state_route_gen\<close>'s own independence of the caller's
  identity, \<open>entry_state_route_gen_def\<close>: the callee context is a function of
  what is passed, never of who passes it.
\<close>

definition entered_is_bot_for :: "vname list \<Rightarrow> ivl abs_state \<Rightarrow> bool" where
  "entered_is_bot_for pars ent = list_ex (\<lambda>x. is_empty (ent x)) pars"

text \<open>
  Restricting \<^const>\<open>is_empty_state\<close>'s witness search to the formals is exact,
  not merely a heuristic: \<^const>\<open>enter_frame\<close> resets every non-global
  variable to \<^const>\<open>ivl_top\<close> and leaves every global at the caller's own
  value, so no name outside the formals can ever witness bottomness once the
  caller itself is not \<^const>\<open>is_empty_state\<close> -- \<open>entered_is_bot_for_correct\<close>
  below states this precisely.
\<close>

lemma entered_is_bot_for_correct:
  assumes not_bot: "\<not> is_empty_state st"
  shows "entered_is_bot_for pars (entry_state_enter_abs gs (CallEdge dst pars args) st) =
         is_empty_state (entry_state_enter_abs gs (CallEdge dst pars args) st)"
proof -
  define frame where "frame = enter_frame gs ivl_top st"
  define entered where "entered = bind_formals pars (map (\<lambda>e. aval_ivl e st) args) frame"
  have unfold: "entry_state_enter_abs gs (CallEdge dst pars args) st = entered"
    unfolding entry_state_enter_abs_def
    by (simp add: ivl_tf.enter_for_def enter_binding_def entered_def frame_def)
  have frame_not_bot: "\<not> is_empty (frame x)" for x
  proof (cases "gs x")
    case True
    then have "frame x = st x" by (simp add: frame_def enter_frame_def)
    with not_bot show ?thesis by (auto simp: is_empty_state_def)
  next
    case False
    then have "frame x = ivl_top" by (simp add: frame_def enter_frame_def)
    then show ?thesis by (simp add: ivl_top_def is_bottom_ivl_def)
  qed

  have off_pars_generic: "\<And>ps as (\<tau>::vname \<Rightarrow> ivl) x. x \<notin> set ps
      \<Longrightarrow> fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) (zip ps as) \<tau> x = \<tau> x"
  proof -
    fix ps show "\<And>as (\<tau>::vname \<Rightarrow> ivl) x. x \<notin> set ps
        \<Longrightarrow> fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) (zip ps as) \<tau> x = \<tau> x"
    proof (induction ps)
      case Nil
      then show ?case by simp
    next
      case (Cons p ps)
      show ?case
      proof (cases as)
        case Nil
        then show ?thesis by simp
      next
        case (Cons a as')
        have neq: "x \<noteq> p" using Cons.prems by simp
        have notin: "x \<notin> set ps" using Cons.prems by simp
        show ?thesis
          unfolding local.Cons
          using Cons.IH[where as = as' and \<tau> = "\<tau>(p := a)" and x = x] notin neq
          by simp
      qed
    qed
  qed
  have off_pars: "x \<notin> set pars \<Longrightarrow> entered x = frame x" for x
    unfolding entered_def
    using off_pars_generic by blast
  have "is_empty_state entered \<longleftrightarrow> (\<exists>x. is_empty (entered x))"
    by (simp add: is_empty_state_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>x \<in> set pars. is_empty (entered x))"
    using off_pars frame_not_bot by metis
  also have "\<dots> \<longleftrightarrow> list_ex (\<lambda>x. is_empty (entered x)) pars"
    by (simp add: list_ex_iff)
  finally show ?thesis
    unfolding unfold entered_is_bot_for_def by (simp add: unfold)
qed

definition entry_state_callee_ctx ::
    "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> ivl abs_state \<Rightarrow> ivl list option" where
  "entry_state_callee_ctx gs ca st =
     (case ca of CallEdge dst pars args \<Rightarrow>
        (let entered = entry_state_enter_abs gs ca st
         in if entered_is_bot_for pars entered then None
            else Some (formals_context pars entered)))"

text \<open>
  \<^const>\<open>callee_ctx_of\<close> is this same decision written once for every domain.
  The two coincide outright, with no side condition: both enter the callee with
  this domain's own transfer and both look for an empty formal, so the equality
  is the two definitions meeting rather than two conventions agreeing.
\<close>

lemma callee_ctx_of_enter_ivl_for_eq:
  "callee_ctx_of enter_ivl_for gs ca st = entry_state_callee_ctx gs ca st"
  by (cases ca)
     (simp add: callee_ctx_of_def entry_state_callee_ctx_def entered_is_bot_for_def
        entry_state_enter_abs_def Let_def)


subsection \<open>The entry-state pipeline's published re-exports\<close>

text \<open>
  The registration itself is generated --- \<open>Interval_Contextual_Assembly\<close> ---
  and \<open>interval_es\<close> is a \<^theory_text>\<open>global_interpretation\<close>, so its
  binder is in scope here and the re-exports below need no context of their own.
\<close>

lemmas entry_state_terminates_via_solve_c = interval_es.terminates_of_solve_c

text \<open>
  The covered-key set and the solved map, spelled as projections of the solved
  pair. A caller that established coverage by evaluating the pair -- which is
  what every regression witness does -- states its facts about
  \<^const>\<open>fst\<close>/\<^const>\<open>snd\<close> of that pair, while the endpoints are stated over the
  two named readers; these two equations are the bridge, and are the only place
  the two spellings meet.
\<close>

lemma entry_state_vars_prog_alt:
  "entry_state_vars_prog gs p = fst (entry_state_sol_prog gs p)"
  by (rule interval_es.sol_vars_def)

lemma entry_state_env_prog_alt:
  "entry_state_env_prog gs p = snd (entry_state_sol_prog gs p)"
  by (rule interval_es.sol_env_def)
section \<open>The abstract-carrier route witness\<close>

text \<open>
  \<open>interval_abs_spec\<close> is the abstract-carrier half of the \<open>route\<close>/\<open>resolve\<close> pair
  \<^locale>\<open>routed_context_base_hetero\<close> requires: its \<open>route_agree\<close> assumption
  needs both an executable-carrier route and an abstract-carrier one it
  agrees with along the readback, so this witness stays even once the
  interpretation below runs entirely at the executable carrier.
\<close>


definition entered_state_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> ivl abs_state lifted" where
  "entered_state_abs gs d ca =
     transfer_lift is_empty_state (entry_state_enter_abs gs ca) d"

definition entry_state_route_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_abs gs d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0))"

definition entry_state_route_abs_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_abs_gen gs u ctx d ca = entry_state_route_abs gs d ca"

text \<open>
  \<open>entry_state_route_abs\<close>/\<open>entry_state_route_abs_gen\<close> are exactly
  \<^theory>\<open>Voblint_Framework.Routed_Context\<close>'s \<open>formals_route_lifted\<close>/\<open>formals_route_lifted_gen\<close>,
  generalized so any domain interprets them instead of restating them: both case-split
  the same \<^const>\<open>CallEdge\<close> and read the same entered-frame Bot/Lifted collapse, and
  the action-only entry primitive used by entered_state_abs agrees with the entered frame
  interval_abs_spec's own enter transfer produces. Kept as their own named
  definitions -- rather than replaced outright -- because both are cited by name from the
  regression examples
  (\<open>Example_Interval_DG_Ctx_Collect\<close>, \<open>Example_Interval_DG_EntryState_Collect\<close>); this
  identity is what lets the routed interpretation below use the generic Core locale while
  every existing citation of these two names keeps working unchanged.
\<close>

lemma entry_state_route_abs_gen_eq_formals_route_lifted_gen:
  "entry_state_route_abs_gen gs = formals_route_lifted_gen"
proof (intro ext)
  fix u ctx d ca
  show "entry_state_route_abs_gen gs u ctx d ca = formals_route_lifted_gen u ctx d ca"
    unfolding entry_state_route_abs_gen_def formals_route_lifted_gen_def
      entry_state_route_abs_def formals_route_lifted_def
    by (cases ca) simp_all
qed

subsection \<open>The route-consistency core\<close>

lemma entry_state_entered_commute:
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs) (entry_state_entered gs empty_pred s ca)
     = entered_state_abs gs (map_lift (fun_of_resolved_st_q_for gs) s) ca"
proof -
  fix p :: pname
  have commute: "\<And>d. fun_of_resolved_st_q_for gs (entry_state_enter_exec gs ca d) =
      entry_state_enter_abs gs ca (fun_of_resolved_st_q_for gs d)"
  proof -
    fix d
    have "fun_of_resolved_st_q_for gs
        (ivl_enter_st_for gs (call_info_of ca p) d) =
        enter_ivl_ci_for gs (call_info_of ca p) (fun_of_resolved_st_q_for gs d)"
      by (rule ivl_enter_st_for_commute)
    then show "fun_of_resolved_st_q_for gs (entry_state_enter_exec gs ca d) =
        entry_state_enter_abs gs ca (fun_of_resolved_st_q_for gs d)"
      by (simp only: ivl_enter_st_for_call_info_of_eq_entry_state_enter_exec
          enter_ivl_ci_for_call_info_of_eq_entry_state_enter_abs)
  qed
  show ?thesis
    unfolding entry_state_entered_def entered_state_abs_def
    by (rule transfer_lift_commute
          [where phi = "fun_of_resolved_st_q_for gs"
             and f = "entry_state_enter_exec gs ca"
             and F = "entry_state_enter_abs gs ca"
             and empty_pred = empty_pred
             and empty_pred' = is_empty_state, OF commute exact])
qed

lemma entry_state_route_commute:
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "entry_state_route_abs gs (map_lift (fun_of_resolved_st_q_for gs) s) ca
           = entry_state_route gs empty_pred s ca"
  by (cases ca; cases s)
     (simp_all add: entry_state_route_abs_def entry_state_route_def
                    formals_context_def fun_of_resolved_st_q_for_def)

lemma entry_state_route_commute_gen:
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "entry_state_route_gen gs empty_pred u ctx s ca
           = entry_state_route_abs_gen gs u ctx (map_lift (fun_of_resolved_st_q_for gs) s) ca"
  by (simp add: entry_state_route_gen_def entry_state_route_abs_gen_def
        entry_state_route_commute[OF exact])

text \<open>
  Presentation-side routing agrees with the routing that built the equation
  system, on both outcomes. A caller point the table answers \<^const>\<open>Lifted\<close>
  either routes to the same callee context the solved system was built with,
  or is exactly the case that context is dead: \<open>entry_state_callee_ctx\<close>
  answers \<^const>\<open>None\<close> iff the entered callee frame is itself
  \<^const>\<open>is_empty_state\<close>, which is precisely when \<^const>\<open>entry_state_route_abs\<close>'s
  own bottom collapse fires. There is no unaddressed case left over: unlike
  the earlier single-outcome fact this replaces, this theorem needs no \<open>live\<close>
  side condition, because it states what happens on both branches instead of
  assuming the live one.

  \<open>reach\<close> says the normalized state is the reader's image of the solved local
  unknown -- what \<^const>\<open>readback_result_value\<close> supplies for any point a result
  table answered \<^const>\<open>Lifted\<close>. \<open>not_bot\<close> says that
  normalized state is not itself \<^const>\<open>is_empty_state\<close>, which
  \<open>readback_result_value\<close>'s own witness-bottom test already guarantees for every
  \<^const>\<open>Lifted\<close> point a table built through it can produce.
\<close>

theorem entry_state_callee_ctx_eq_route_partial:
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and reach: "map_lift (fun_of_resolved_st_q_for gs) d = Lifted st"
    and not_bot: "\<not> is_empty_state st"
  shows "entry_state_callee_ctx gs ca st =
    (if entered_state_abs gs (Lifted st) ca = Bot
     then None
     else Some (entry_state_route gs empty_pred (entry_state_entered gs empty_pred d ca) ca))"
proof (cases ca)
  case (CallEdge dst pars args)
  define entered where "entered = entry_state_enter_abs gs ca st"
  have entered_state_eq: "entered_state_abs gs (Lifted st) ca =
      (if entered_is_bot_for pars entered then Bot else Lifted entered)"
    unfolding entered_state_abs_def CallEdge entered_def
    by (simp add: normalize_lift_def entered_is_bot_for_correct[OF not_bot])
  have callee_ctx_eq: "entry_state_callee_ctx gs ca st =
      (if entered_is_bot_for pars entered then None else Some (formals_context pars entered))"
    unfolding entry_state_callee_ctx_def CallEdge Let_def entered_def by simp
  show ?thesis
  proof (cases "entered_is_bot_for pars entered")
    case True
    with entered_state_eq callee_ctx_eq show ?thesis by simp
  next
    case False
    have "entry_state_route gs empty_pred (entry_state_entered gs empty_pred d ca) ca
        = entry_state_route_abs gs
            (map_lift (fun_of_resolved_st_q_for gs) (entry_state_entered gs empty_pred d ca)) ca"
      by (simp add: entry_state_route_commute[OF exact])
    also have "\<dots> = entry_state_route_abs gs (entered_state_abs gs (Lifted st) ca) ca"
      using entry_state_entered_commute[OF exact] reach by simp
    also have "\<dots> = formals_context pars entered"
      unfolding entry_state_route_abs_def
      using entered_state_eq False CallEdge by simp
    finally have "entry_state_route gs empty_pred (entry_state_entered gs empty_pred d ca) ca
        = formals_context pars entered" .
    with False entered_state_eq callee_ctx_eq show ?thesis by simp
  qed
qed


subsection \<open>Interval's own route is the shared one\<close>

text \<open>
  \<^const>\<open>entry_state_route_gen\<close> reads the entered frame through
  \<^const>\<open>lookup_resolved_st_q\<close> at each formal's location; \<^const>\<open>exec_formals_route\<close>
  reads it through \<^const>\<open>fun_of_resolved_st_q_for\<close>, which is that same lookup.
  The equation is what lets the presentation-side names above and the equation
  system the assembly builds refer to one routing decision rather than two that
  happen to agree.
\<close>

lemma entry_state_route_gen_eq_exec_formals_route:
  "entry_state_route_gen gs empty_pred u ctx d ca = exec_formals_route gs u ctx d ca"
proof -
  have f: "(\<lambda>x. lookup_resolved_st_q s (location_of gs x)) = fun_of_resolved_st_q_for gs s"
    for s :: "ivl resolved_st_q"
    by (simp add: fun_eq_iff fun_of_resolved_st_q_for_def)
  show ?thesis
    by (cases ca)
       (simp add: entry_state_route_gen_def entry_state_route_def
          exec_formals_route_def f)
qed

section \<open>Activation-indexed collecting soundness\<close>

text \<open>
  Every endpoint below is \<^locale>\<open>routed_dg_analysis\<close>'s, re-exported under the
  name Interval publishes. The four coverage premises are properties of the
  \<^emph>\<open>solved\<close> system --- which keys the executable solver actually covered --- and
  are carried the way \<^const>\<open>entry_state_terminates_prog\<close> is: as
  \<^theory_text>\<open>eval\<close>-checkable facts about a concrete, terminated solve.
\<close>

lemmas entry_state_routed_analysis_sound =
  interval_es.entry_state_routed_analysis_sound

lemmas entry_state_activation_collect_sound =
  interval_es.entry_state_activation_collect_sound

lemmas entry_state_has_context = interval_es.entry_state_has_context

lemmas entry_state_ltr_collect_eq_Union =
  interval_es.entry_state_ltr_collect_eq_Union

lemmas entry_state_gamma_reader_eq_lookup =
  interval_es.gamma_reader_eq_lookup

lemmas entry_state_activation_collect_sound_of_cover =
  interval_es.entry_state_activation_collect_sound_of_cover

lemmas entry_state_ltr_collect_eq_Union_of_cover =
  interval_es.entry_state_ltr_collect_eq_Union_of_cover

lemmas entry_state_activation_collect_sound_of_terminates =
  interval_es.entry_state_activation_collect_sound_of_terminates

lemmas entry_state_ltr_collect_eq_Union_of_terminates =
  interval_es.entry_state_ltr_collect_eq_Union_of_terminates

text \<open>
  The two routed protocol facts a caller reasoning about one call needs: the
  callee entry state published under an admitted context is sound, and a return
  combine at the caller's own context is sound. Both are the routed spine's, at
  the interpretation the four coverage premises establish.
\<close>

lemmas entry_state_routed_context_call =
  interval_es.entry_state_routed_context_call

lemmas entry_state_routed_context_comb =
  interval_es.entry_state_routed_context_comb

section \<open>Solved-result table\<close>

text \<open>
  The solved entry-state D/G system, read as a
  \<^typ>\<open>(ivl list, ivl abs_state) analysis_result\<close>. This is the
  context-sensitive counterpart of \<open>Interval_Checks\<close>'s monovariant
  \<open>analyse_interval_result_for\<close>: the context type is \<^typ>\<open>ivl list\<close>, the
  entered abstract value of the callee's declared formals, so a node covered
  under several activations keeps one \<^type>\<open>lifted\<close> per activation.

  The solver's own first component is the key set verbatim, so nothing rescans
  the solved map or reconstructs coverage, and an uncovered context is answered
  by \<^const>\<open>lookup_context\<close>'s membership guard with \<^const>\<open>Bot\<close> rather than by
  falling back to the seeded default context \<open>[]\<close>.
\<close>

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and
  \<^const>\<open>prog_main_name\<close>, the instantiation the production entry points use.\<close>

definition analyse_interval_entry_state_result ::
    "imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result p =
     analyse_interval_entry_state_result_for (declared_global p) p"

text \<open>
  The route-consistency corollary at the table, on both outcomes: a caller
  point the table answers \<^const>\<open>Lifted\<close> either routes to the same callee
  context the solved system was built with, or is exactly the case that
  context is dead. \<^const>\<open>lookup_context\<close>'s membership guard supplies \<open>reach\<close>
  --- an uncovered key answers \<^const>\<open>Bot\<close>, so a \<^const>\<open>Lifted\<close>
  answer already witnesses that the solver stored this point --- and the
  \<open>not_bot\<close> premise \<open>entry_state_callee_ctx_eq_route_partial\<close> needs now
  comes from \<^const>\<open>canonicalize_lift\<close>'s own case split at the result
  boundary, not from \<open>readback_result_value\<close> inspecting the raw value itself:
  \<open>norm\<close> below is stated over \<open>canonicalize_lift (resolved_st_q_is_bot_for
  (declared_global_vars p))\<close> applied to the raw solved local unknown,
  matching exactly what \<open>analyse_interval_entry_state_result_for\<close> now
  builds. No \<open>live\<close> side condition survives to this corollary either.
\<close>

corollary entry_state_callee_ctx_at_result:
  assumes reach: "lookup_context (analyse_interval_entry_state_result_for (declared_global p) p)
                    u ctx = Lifted st"
  shows "entry_state_callee_ctx (declared_global p) ca st =
    (if entered_state_abs (declared_global p) (Lifted st) ca = Bot
     then None
     else Some (entry_state_route (declared_global p)
               (resolved_st_q_is_bot_for (declared_global_vars p))
               (entry_state_entered (declared_global p)
                  (resolved_st_q_is_bot_for (declared_global_vars p))
                  (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx)))) ca)
               ca))"
proof -
  have globals: "\<And>x. declared_global p x = (x \<in> set (declared_global_vars p))" by simp
  have exact: "\<And>s::ivl resolved_st_q. resolved_st_q_is_bot_for (declared_global_vars p) s
                     = is_empty_state (fun_of_resolved_st_q_for (declared_global p) s)"
    by (rule resolved_st_q_is_bot_for_iff[OF globals])
  have norm: "readback_result_value (declared_global p)
                (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                  (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx)))))
              = Lifted st"
    using reach
    by (simp add: analyse_interval_entry_state_result_for_def
        routed_dg_pipeline.result_def entry_state_sol_prog_def split: if_splits)
  have key: "map_lift (fun_of_resolved_st_q_for (declared_global p))
               (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx))))
             = Lifted st
           \<and> \<not> is_empty_state st"
  proof (cases "locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx)))")
    case Bot
    with norm show ?thesis by simp
  next
    case (Lifted s0)
    show ?thesis
    proof (cases "resolved_st_q_is_bot_for (declared_global_vars p) s0")
      case True
      with norm Lifted show ?thesis by simp
    next
      case False
      with norm Lifted exact show ?thesis by auto
    qed
  qed
  have reach_raw: "map_lift (fun_of_resolved_st_q_for (declared_global p))
                      (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx))))
                    = Lifted st"
    and not_bot: "\<not> is_empty_state st"
    using key by auto
  show ?thesis
    by (rule entry_state_callee_ctx_eq_route_partial[OF exact reach_raw not_bot])
qed


section \<open>Contextual check report\<close>

text \<open>
  The check report is a projection of the result table above, not a second
  reading of the solved system: \<^const>\<open>classify_checks_ctx\<close> takes only a
  \<^type>\<open>cfg\<close>, an \<^type>\<open>analysis_result\<close>, and a classifier, so no solver
  state, solved map, or per-key lookup reaches the classification step. The
  entry-state specifics live here, in the one argument that supplies the
  table.

  This is what removes the fabricated verdict a solver-level reading gives
  dead code. Querying an uncovered or dead \<open>(node, context)\<close> pair against the
  solved map answers with a bottom abstract state, and a bottom state
  satisfies \<^const>\<open>interval_less_true\<close> vacuously, so \<open>check_query\<close> answers
  \<^term>\<open>Some True\<close> and the check classifies \<^const>\<open>Check_Proved\<close> even though
  no execution reaches
  it. \<^const>\<open>lookup_context\<close> answers \<^const>\<open>Bot\<close> for both cases
  instead --- the membership guard for the uncovered one, \<^const>\<open>readback_result_value\<close>'s
  witness-bottom test for the covered-but-dead one --- and
  \<^const>\<open>classify_point\<close> declines to classify against it at all.

  Contexts stay separate in \<open>entry_state_check_projection\<close> and are
  aggregated only in \<open>entry_state_verdict_report_prog\<close>, which is the
  resolution the source level actually needs: one source check may be dead
  in some activations and live in others, and only the dead ones must drop
  out of the join.

  \<^const>\<open>analyse_interval_entry_state_result_for\<close> occurs once here, and it
  binds its own solve once, so a whole report costs exactly one solve
  regardless of how many checks or contexts it covers.
\<close>

definition entry_state_check_projection ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> (ivl list \<times> contextual_verdict) set) list" where
  "entry_state_check_projection p =
     classify_checks_ctx (prog_cfg p)
       (analyse_interval_entry_state_result_for (declared_global p) p)
       interval_classify_check"

definition entry_state_verdict_report_prog ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (entry_state_check_projection p)"

text \<open>Aggregating the projection is exactly \<^const>\<open>classify_checks_verdicts\<close>
  over the same table; going through the projection is what keeps the two
  reports to one shared solve.\<close>

lemma entry_state_verdict_report_prog_eq:
  "entry_state_verdict_report_prog p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for (declared_global p) p)
       interval_classify_check"
  unfolding entry_state_verdict_report_prog_def entry_state_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_interval_entry_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state p = entry_state_verdict_report_prog p"

end
