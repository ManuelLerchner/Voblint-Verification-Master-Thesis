theory Interval_Ctx_Entry_State_Sound
  imports
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Analysis.Interval_Transfer"
    "Voblint_Analysis.Interval_Exec_Sound"
    "Voblint_Analysis.Interval_Checks"
    "Voblint_Core.Routed_Context"
    Entry_State_Routed_Context
    "Voblint_Solver.TD_Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Program"
begin

section \<open>Generic executable entry-state context analysis for Interval\<close>

text \<open>
  Promotes the routed D/G machinery a fixed-program example (an entry-state
  acceptance case such as \<open>void p(a) { return a }\<close> / \<open>void main() { x := __voblint_nondet_int();
  y := p(x) }\<close>) exercises to an executable analysis over an arbitrary
  \<^type>\<open>imp_prog\<close>: the context at a call is the entered abstract value of the
  callee's declared formals (\<^const>\<open>formals_route\<close>/\<^const>\<open>formals_context\<close>),
  never call-site history, so a call whose argument is unconstrained (e.g.
  \<open>__voblint_nondet_int()\<close>) is analyzed once under one wide context rather than diverging over
  every concrete value. Mirrors \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s
  \<open>analyse_interval_td\<close> family and naming convention, adding one context
  dimension: every quantity here is keyed on \<^typ>\<open>pp \<times> ivl list\<close>, not \<^typ>\<open>pp\<close>
  alone.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ivl: "ivl list")

subsection \<open>The routed context hooks, generic over the compiled program\<close>

text \<open>
  The one D/G spec every hook below shares.
\<close>

text \<open>
  \<open>ectx_spec\<close> is the Base-style whole-state specification
  (\<^const>\<open>base_dg_spec_st_for_lifted\<close>), the same one context-insensitive Interval already
  solves over in \<^const>\<open>analyse_interval_dg_eqs_for\<close>, at the same
  \<^const>\<open>ivl_tf_st_for\<close>/\<^const>\<open>ivl_enter_st_for\<close> primitives: the local unknown
  \<^typ>\<open>ivl exec_dg_st lifted\<close> carries every VIMP variable, global and local alike, so a
  global is read and written exactly where a local is. The solver-global carrier stays
  diagonal at \<^typ>\<open>ivl exec_dg_st lifted\<close> -- the type the keyed generator and its
  warrowing solver instance already fix -- but is inert: every field of
  \<^const>\<open>base_dg_spec_st_for_lifted\<close> threads its incoming \<open>g\<close> through unchanged, so
  \<open>Inr Global\<close> is never read back to reconstruct program state.

  \<open>ectx_spec\<close> carries an explicit executable bottom predicate and solves over the lifted
  carrier, mirroring \<open>ictx_eqs\<close>'s convention
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) of taking \<open>empty_pred\<close> as a
  caller-supplied parameter rather than deriving it internally. Callers with a concrete
  program supply \<open>resolved_st_q_is_bot_for (declared_global_vars p)\<close>, exact for
  \<^const>\<open>is_empty_state\<close> (\<open>resolved_st_q_is_bot_for_iff\<close>).\<close>
definition ectx_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_spec"
where
  "ectx_spec gs empty_pred = base_dg_spec_st_for_lifted gs empty_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)"

text \<open>
  \<^const>\<open>formals_route\<close>/\<^const>\<open>formals_route_gen\<close> (\<^theory>\<open>Voblint_Core.Routed_Context\<close>)
  read the entered callee formals off an arbitrary \<^const>\<open>CallEdge\<close> generically,
  but only at the semantic \<^typ>\<open>'a abs_state\<close> carrier, not the executable
  \<^typ>\<open>'a exec_dg_st\<close> one this equation system solves over: the entered callee
  store is materialized here by the same \<^const>\<open>ivl_enter_st_for\<close> primitive
  \<open>ectx_spec\<close>'s own \<open>dgs_enter\<close> field applies and read back through
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

lemma tf_enter_ivl_for_call_info_of_eq_entry_state_enter_abs:
  "snd (tf_enter (ivl_tf_for gs) (call_info_of ca p) s) =
   entry_state_enter_abs gs ca s"
  unfolding entry_state_enter_abs_def ivl_tf_for_def
    enter_pair_ivl_for_def enter_pair_D_def enter_ivl_for_def
  by simp

definition entry_state_entered ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st lifted" where
  "entry_state_entered gs empty_pred d ca =
     transfer_lift empty_pred (entry_state_enter_exec gs ca) d"

lemma enter_local_ectx_spec_eq_entry_state_entered:
  "enter_local (ectx_spec gs empty_pred) (call_info_of ca p) d g =
   entry_state_entered gs empty_pred d ca"
  unfolding ectx_spec_def dgs_enter_base_st_for_lifted entry_state_entered_def
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def entry_state_enter_exec_def)

definition entry_state_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route gs empty_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars
          (\<lambda>x. lookup_resolved_st_q
                 (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)
                 (location_of gs x)))"

definition entry_state_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_gen gs empty_pred u ctx d ca = entry_state_route gs empty_pred d ca"

text \<open>
  The same routing decision taken on a caller state that has already left the
  executable substrate: the argument is the \<^typ>\<open>ivl abs_state\<close> a
  \<^const>\<open>Lifted\<close> point of an \<^type>\<open>analysis_result\<close> hands out, so a
  consumer of a solved table can recompute a call's callee context without
  reopening the solver's own solution map.

  The type is \<^typ>\<open>ivl abs_state\<close>, not \<^typ>\<open>ivl abs_state lifted\<close>, on
  purpose: reachability is the caller's case split, decided once by
  \<^const>\<open>normalize_point\<close> when the table was built, and an \<^const>\<open>Bot\<close>
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
  "entered_is_bot_for pars entered = list_ex (\<lambda>x. is_empty (entered x)) pars"

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
    by (simp add: enter_ivl_for_def enter_D_def entered_def frame_def)
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

subsection \<open>The routed equation system and its executable solution\<close>

definition entry_state_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> ivl list, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "entry_state_eqs gs empty_pred Pi ps =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       (entry_state_route_gen gs empty_pred)
      (routed_cmb_g_contribution (ectx_spec gs empty_pred) Global Seed
         (static_resolve (compile_prog Pi ps)))
      (routed_extra_g Seed Global)
       (compile_prog Pi ps) (ectx_spec gs empty_pred) Bot (Lifted cinit_ivl_st) Bot"

definition entry_state_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp_solve (entry_state_eqs gs empty_pred Pi ps)
       (cfg_exit (compile_prog Pi ps), [])"

definition entry_state_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> bool" where
  "entry_state_terminates gs empty_pred Pi ps =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (entry_state_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"

text \<open>
  Discharging termination by execution, exactly as
  \<open>ictx_terminates_prog_via_solve_c\<close> discharges
  \<open>ictx_terminates_prog\<close>.
\<close>

lemma entry_state_terminates_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (entry_state_eqs gs empty_pred Pi ps)
             (cfg_exit (compile_prog Pi ps), []) \<noteq> None"
  shows "entry_state_terminates gs empty_pred Pi ps"
  unfolding entry_state_terminates_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Whole-program convenience layer\<close>

text \<open>
  \<open>Pi ps\<close> alone give no @{type imp_prog} to read a declared-global list off of, so
  \<open>entry_state_eqs\<close> and friends keep \<open>empty_pred\<close> as an explicit parameter, mirroring
  \<open>ictx_eqs\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>). The \<open>_prog\<close> wrappers do
  have a program and instantiate \<open>empty_pred\<close> to \<^const>\<open>resolved_st_q_is_bot_for\<close> at its own
  \<^const>\<open>declared_global_vars\<close>, mirroring \<open>ictx_sol_prog\<close>.
\<close>

definition entry_state_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "entry_state_eqs_prog gs p =
     entry_state_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition entry_state_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog gs p =
     entry_state_sol gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

definition entry_state_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "entry_state_terminates_prog gs p =
     entry_state_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p)"

lemma entry_state_terminates_prog_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (entry_state_eqs_prog gs p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p)), []) \<noteq> None"
  shows "entry_state_terminates_prog gs p"
  using assms
  unfolding entry_state_terminates_prog_def entry_state_eqs_prog_def
  by (rule entry_state_terminates_via_solve_c)

section \<open>The abstract-carrier route witness\<close>

text \<open>
  \<open>ectx_abs_spec\<close> is the abstract-carrier half of the \<open>route\<close>/\<open>resolve\<close> pair
  \<^locale>\<open>routed_context_base_hetero\<close> requires: its \<open>route_agree\<close> assumption
  needs both an executable-carrier route and an abstract-carrier one it
  agrees with along the readback, so this witness stays even once the
  interpretation below runs entirely at the executable carrier.
\<close>


definition ectx_abs_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_spec" where
  "ectx_abs_spec gs = base_dg_spec_for_lifted gs is_empty_state (ivl_tf_for gs)"

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
  \<^theory>\<open>Voblint_Core.Routed_Context\<close>'s \<open>formals_route_lifted\<close>/\<open>formals_route_lifted_gen\<close>,
  generalized so any domain interprets them instead of restating them: both case-split
  the same \<^const>\<open>CallEdge\<close> and read the same entered-frame Bot/Lifted collapse, and
  the action-only entry primitive used by entered_state_abs agrees with enter_local applied
  to ectx_abs_spec (dgs_enter_base_for_lifted). Kept as their own named
  definitions -- rather than replaced outright -- because both are cited by name from the
  regression examples
  (\<open>Example_Interval_DG_Ctx_Collect\<close>, \<open>Example_Interval_DG_EntryState_Collect\<close>); this
  identity is what lets the routed interpretation below use the generic Core locale while
  every existing citation of these two names keeps working unchanged.
\<close>

lemma entry_state_route_abs_gen_eq_formals_route_lifted_gen:
  "entry_state_route_abs_gen gs = formals_route_lifted_gen (ectx_abs_spec gs)"
proof (intro ext)
  fix u ctx d ca
  show "entry_state_route_abs_gen gs u ctx d ca = formals_route_lifted_gen (ectx_abs_spec gs) u ctx d ca"
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
        snd (tf_enter (ivl_tf_for gs) (call_info_of ca p)
          (fun_of_resolved_st_q_for gs d))"
      by (rule ivl_enter_st_for_commute)
    then show "fun_of_resolved_st_q_for gs (entry_state_enter_exec gs ca d) =
        entry_state_enter_abs gs ca (fun_of_resolved_st_q_for gs d)"
      by (simp only: ivl_enter_st_for_call_info_of_eq_entry_state_enter_exec
          tf_enter_ivl_for_call_info_of_eq_entry_state_enter_abs)
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
  by (simp add: entry_state_route_gen_def entry_state_route_abs_gen_def entry_state_route_commute[OF exact])

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
  unknown -- what \<^const>\<open>normalize_point\<close> supplies for any point a result
  table answered \<^const>\<open>Lifted\<close>. \<open>not_bot\<close> says that
  normalized state is not itself \<^const>\<open>is_empty_state\<close>, which
  \<open>normalize_point\<close>'s own witness-bottom test already guarantees for every
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

subsection \<open>Per-tree transport commutation\<close>

text \<open>
  The same interpretation Interval's unit-context instance makes, at the entry-state
  routing policy. \<^locale>\<open>routed_domain_exec\<close> takes the routing functions and their
  agreement as parameters; here the agreement is the route-consistency core just
  proved, since the entry-state route reads the entered state.
\<close>

lemma seed_ne_global [simp]: "Seed p ctx \<noteq> Global"
  by simp

text \<open>The concretization the executable-carrier interpretations below use: a local
  unknown means \<^const>\<open>gamma_state_lift\<close> of its readback, the global slot is ignored as
  in \<^const>\<open>gamma_dg_base\<close>. Named at top level so a downstream theory can state it.\<close>

definition ectx_gamma ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> store set" where
  "ectx_gamma gs d g = gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) d)"

lemma ectx_gamma_Bot [simp]: "ectx_gamma gs Bot g = {}"
  by (simp add: ectx_gamma_def)

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation ivl_es: routed_domain_exec
  gs empty_pred "ivl_tf_st_for gs" "ivl_enter_st_for gs" "ivl_tf_for gs"
  Global Seed "entry_state_route_gen gs empty_pred" "entry_state_route_abs_gen gs"
  static_resolve static_resolve
  by unfold_locales
     (rule ivl_tf_st_for_commute, rule ivl_enter_st_for_commute, rule exact, simp,
      rule entry_state_route_commute_gen[OF exact], simp add: static_resolve_def)

lemmas ivl_es_pp_st_gen = ivl_es.pp_st

lemma ectx_gamma_eq: "ectx_gamma gs = ivl_es.gamma_exec"
  by (intro ext) (simp add: ectx_gamma_def ivl_es.gamma_exec_def gamma_dg_base_def)

theorem ectx_sound_exec: "sound_dg_spec (ectx_spec gs empty_pred) (ectx_gamma gs) gs"
  unfolding ectx_gamma_eq ectx_spec_def
  by (rule ivl_es.sound_dg_spec_st)
     (rule base_dg_spec_sound[OF ivl_is_sound_transfer_for is_empty_state_gamma_state_empty])

end


subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "entry_state_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

lemma entry_state_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     (entry_state_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])"
  using solves[unfolded entry_state_terminates_def] .

lemma entry_state_pp_st:
  "part_post_solution (entry_state_eqs gs empty_pred Pi ps) (cfg_exit (compile_prog Pi ps), [])
     (snd (entry_state_sol gs empty_pred Pi ps)) (fst (entry_state_sol gs empty_pred Pi ps))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF entry_state_solve_dom, of "fst (entry_state_sol gs empty_pred Pi ps)"
             "snd (entry_state_sol gs empty_pred Pi ps)"]
  unfolding entry_state_sol_def by simp

text \<open>The solver's post-solution, for the unbuffered routed generator at the executable
  spec and Interval's executable route: the shape \<^locale>\<open>dg_ctx_activation_base\<close>
  consumes.\<close>

theorem entry_state_pp_routed:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
        (entry_state_route_gen gs empty_pred)
        (routed_cmb_g (ectx_spec gs empty_pred) Global Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) (ectx_spec gs empty_pred) Bot (Lifted cinit_ivl_st) Bot)
     (cfg_exit (compile_prog Pi ps), [])
     (snd (entry_state_sol gs empty_pred Pi ps)) (fst (entry_state_sol gs empty_pred Pi ps))"
  using entry_state_pp_st unfolding entry_state_eqs_def ectx_spec_def
  by (rule ivl_es_pp_st_gen[OF exact])


end


section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  The routed spine is interpreted at Interval's executable carrier and fed the solver's
  own table: a local unknown concretizes to \<^const>\<open>gamma_state_lift\<close> of its readback
  (\<^const>\<open>ectx_gamma\<close>), the covered reader \<open>entry_state_sg_st\<close> hands the table's local
  slot through unchanged, and the route is Interval's own executable
  \<^const>\<open>entry_state_route_gen\<close>. The reader is unconditional so the code generator and
  the examples can evaluate it; the soundness obligations below are hypotheses of the
  context, not of the reader.
\<close>

definition entry_state_sg_st ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list
       \<Rightarrow> pp \<times> ivl list + gk \<Rightarrow> ivl exec_dg_st lifted" where
  "entry_state_sg_st gs empty_pred Pi ps k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)
           then locals (snd (entry_state_sol gs empty_pred Pi ps) (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and empty_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "entry_state_terminates gs empty_pred Pi ps"
    and exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), []) \<in> fst (entry_state_sol gs empty_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p,
              entry_state_route_gen gs empty_pred u ctx
                (enter_local (ectx_spec gs empty_pred) (call_info_of (CallEdge dst pars args) p)
                   (locals (snd (entry_state_sol gs empty_pred Pi ps) (Inl (u, ctx))))
                   (globs (snd (entry_state_sol gs empty_pred Pi ps) (Inr Global))))
                (CallEdge dst pars args))
            \<in> fst (entry_state_sol gs empty_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (entry_state_sol gs empty_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (entry_state_sol gs empty_pred Pi ps)"
begin

subsection \<open>The solver's table as the solved system\<close>

text \<open>
  The trace-semantic context function: ignores its store argument entirely and
  recomputes the routed value from the caller's own solved state in the solver's table,
  using \<^const>\<open>call_action_at_call_site\<close> for the one call at \<open>u\<close>. This is a total
  context function, so coverage of infinitely many concrete stores comes from the
  caller's own value being imprecise, not from \<open>entry_state_context\<close> being multi-valued.
\<close>

definition entry_state_context :: "cfg_node \<Rightarrow> ivl list \<Rightarrow> store \<Rightarrow> ivl list" where
  "entry_state_context u ctx s =
     (let ca = call_action_at_call_site (compile_prog Pi ps) u;
          p = (case callee_entry_at_call_site (compile_prog Pi ps) u of FunctionEntry q \<Rightarrow> q | _ \<Rightarrow> undefined)
      in entry_state_route_gen gs empty_pred u ctx
          (enter_local (ectx_spec gs empty_pred) (call_info_of ca p)
             (locals (snd (entry_state_sol gs empty_pred Pi ps) (Inl (u, ctx))))
             (globs (snd (entry_state_sol gs empty_pred Pi ps) (Inr Global)))) ca)"

interpretation entry_state_compiled: compiled_cfg Pi ps "compile_prog Pi ps"
  by (unfold_locales; simp add: compile_prog_finite)

lemmas entry_state_fin = entry_state_compiled.finite_intra
lemmas entry_state_finC = entry_state_compiled.finite_calls

lemma entry_state_sg_st_covered:
  "(v, ctx) \<in> fst (entry_state_sol gs empty_pred Pi ps)
   \<Longrightarrow> entry_state_sg_st gs empty_pred Pi ps (Inl (v, ctx))
         = locals (snd (entry_state_sol gs empty_pred Pi ps) (Inl (v, ctx)))"
  by (simp add: entry_state_sg_st_def)

lemma entry_state_sg_st_uncovered_empty:
  "(v, ctx) \<notin> fst (entry_state_sol gs empty_pred Pi ps)
     \<Longrightarrow> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (entry_state_sg_st gs empty_pred Pi ps (Inl (v, ctx)))) = {}"
  by (simp add: entry_state_sg_st_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

interpretation entry_state_dg_base: sound_dg_spec "ectx_spec gs empty_pred" "ectx_gamma gs" gs
  by (rule ectx_sound_exec[OF exact])


interpretation entry_state_routed: entry_state_routed_context "ectx_spec gs empty_pred"
    "ectx_gamma gs" gs Pi ps Global "entry_state_route_gen gs empty_pred"
    Bot "Lifted cinit_ivl_st" Bot
    "snd (entry_state_sol gs empty_pred Pi ps)" "fst (entry_state_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "entry_state_sg_st gs empty_pred Pi ps" Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd SeedNe CallFwd CombFwd)
  case FinE show ?case by (rule entry_state_fin)
next
  case PP show ?case by (rule entry_state_pp_routed[OF solves exact])
next
  case (SgCov v ctx) then show ?case
    by (simp add: entry_state_sg_st_def ectx_gamma_def)
next
  case (SgUncov v ctx) then show ?case by (rule entry_state_sg_st_uncovered_empty)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case (SeedNe p ctx) show ?case by simp
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using CallFwd(1,2) by (rule call_fwd_ok)
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
qed

text \<open>
  \<^const>\<open>entry_state_context\<close> -- ignore the store, recompute the route from the table at
  \<^const>\<open>call_action_at_call_site\<close> -- is exactly \<^locale>\<open>entry_state_routed_context\<close>'s
  own \<open>enterc\<close> (\<open>route_enterc_of_sigma\<close>).
\<close>

lemma entry_state_context_eq_route_enterc_of_sigma:
  "entry_state_context = route_enterc_of_sigma (ectx_spec gs empty_pred)
     (entry_state_route_gen gs empty_pred) (snd (entry_state_sol gs empty_pred Pi ps)) Global
     (compile_prog Pi ps)"
  unfolding entry_state_context_def route_enterc_of_sigma_def by (rule refl)

lemmas entry_state_routed_context_call =
  entry_state_routed.routed_context_call[folded entry_state_context_eq_route_enterc_of_sigma]
lemmas entry_state_routed_context_comb =
  entry_state_routed.routed_context_comb[folded entry_state_context_eq_route_enterc_of_sigma]

lemma entry_state_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps (Inl (u, ctx))))"
  shows "call_enter gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps
                 (Inl (FunctionEntry p, entry_state_context u ctx (call_enter gs (CallEdge dst xs es) s)))))"
  by (rule entry_state_routed_context_call[OF assms])

lemma entry_state_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls (compile_prog Pi ps)"
    and "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps (Inl (cl, c1))))"
    and "t \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps
                 (Inl (FunctionResult p, entry_state_context cl c1 es))))"
    and "call_enter_store gs (compile_prog Pi ps) cl s es"
  shows "combine_collect gs dst s t
           \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
               (entry_state_sg_st gs empty_pred Pi ps (Inl (v, c1))))"
  by (rule entry_state_routed_context_comb[OF assms])


subsection \<open>Activation-indexed collecting soundness\<close>

lemma entry_state_cinit_le_cinit_ivl_st:
  "cinit_stores gs \<subseteq> ectx_gamma gs (Lifted cinit_ivl_st) Bot"
  by (auto simp: ectx_gamma_def cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def
                 fun_of_st_cinit_ivl_st_for)

text \<open>
  \<^locale>\<open>dg_analysis_adapter\<close> at the same executable solved system, handed the readback
  as \<open>rd\<close> and Interval's classifier; its activation-collect soundness is the entry-state
  soundness theorem, stated against the routed local unknown read back through
  \<^const>\<open>gamma_state_lift\<close>. The four coverage hypotheses are properties of the
  \<^emph>\<open>solved\<close> system -- which keys the executable solver actually covers -- and are
  carried the same way \<^const>\<open>entry_state_terminates\<close> is: as \<open>by eval\<close>-checkable facts
  about a concrete, terminated solve.
\<close>

interpretation entry_state_adapter: dg_analysis_adapter "ectx_spec gs empty_pred" "ectx_gamma gs" gs
    "compile_prog Pi ps" Global "entry_state_route_gen gs empty_pred" Bot "Lifted cinit_ivl_st" Bot
    "snd (entry_state_sol gs empty_pred Pi ps)" "fst (entry_state_sol gs empty_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), [])" "entry_state_sg_st gs empty_pred Pi ps"
    Seed "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)" entry_state_context
    "map_lift (fun_of_resolved_st_q_for gs)" interval_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree GammaRd ClProved ClRefuted)
  case FinE show ?case by (rule entry_state_fin)
next
  case PP show ?case by (rule entry_state_pp_routed[OF solves exact])
next
  case (SgCov v c)
  thus ?case by (simp add: entry_state_sg_st_def ectx_gamma_def)
next
  case (SgUncov v c)
  thus ?case by (simp add: entry_state_sg_st_def)
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case by (rule entry_state_finC)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff[OF entry_state_finC])
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case unfolding entry_state_context_eq_route_enterc_of_sigma
    by (rule route_enterc_of_sigma_agree[OF entry_state_finC compile_prog_calls_source_unique
                                              RouteEnterc(2)])
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using CallFwd(1,2) by (rule call_fwd_ok)
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) by (rule comb_fwd_ok)
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (GammaRd d g')
  show ?case by (simp add: ectx_gamma_def)
next
  case (ClProved c d s)
  thus ?case by (rule interval_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule interval_classify_check_refuted)
qed

theorem entry_state_activation_collect_sound:
  "activation_collect gs entry_state_context [] (compile_prog Pi ps) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs)
           (entry_state_sg_st gs empty_pred Pi ps (Inl (v, ctx))))"
  by (rule entry_state_adapter.activation_collect_dg_sound
             [OF entry_cov entry_state_cinit_le_cinit_ivl_st])

end



section \<open>Solved-result table\<close>

text \<open>
  The solved entry-state D/G system, read as a
  \<^typ>\<open>(ivl list, ivl abs_state) analysis_result\<close>. This is the
  context-sensitive counterpart of \<open>Interval_Checks\<close>'s monovariant
  \<open>analyse_interval_td_result_for\<close>: the context type is \<^typ>\<open>ivl list\<close>, the
  entered abstract value of the callee's declared formals, so a node covered
  under several activations keeps one \<^type>\<open>lifted\<close> per activation.

  Construction is mechanical. \<^const>\<open>entry_state_sol\<close>'s own first component is
  the key set verbatim -- the solver already knows exactly which
  \<open>(node, context)\<close> pairs it reached, so nothing here rescans the solved map
  or reconstructs coverage. Each local unknown goes through
  \<^const>\<open>normalize_point\<close> exactly as it is stored, in its pre-conversion
  \<^typ>\<open>ivl resolved_st_q lifted\<close> shape; no context is joined at construction
  time, and an uncovered context is answered by \<^const>\<open>lookup_context\<close>'s
  membership guard with \<^const>\<open>Bot\<close>, never by falling back to the
  seeded default context \<open>[]\<close>.

  The \<open>[code]\<close> rewrite is a single-solve fix: binding \<open>sol\<close> once, outside the
  per-key closure, compiles to a single shared thunk, so neither building the
  table nor querying it re-solves. \<^const>\<open>entry_state_sol_prog\<close> is fully
  applied at that binding, so it is not the partially applied closure
  \<^const>\<open>entry_state_sg_st\<close> would produce, whose body -- including its own
  internal \<^const>\<open>entry_state_sol\<close> calls -- would re-run at every key.
\<close>

definition analyse_interval_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for gs p =
     Analysis_Result
       (fst (entry_state_sol_prog gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_def [code del]

lemma analyse_interval_entry_state_result_for_code [code]:
  "analyse_interval_entry_state_result_for gs p =
     (let sol = entry_state_sol_prog gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_def Let_def by (rule refl)

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
  boundary, not from \<open>normalize_point\<close> inspecting the raw value itself:
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
  have norm: "normalize_point (declared_global p)
                (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                  (locals (snd (entry_state_sol_prog (declared_global p) p) (Inl (u, ctx)))))
              = Lifted st"
    using reach
    by (simp add: lookup_context_def analyse_interval_entry_state_result_for_def
                  split: if_splits)
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
  instead --- the membership guard for the uncovered one, \<^const>\<open>normalize_point\<close>'s
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

section \<open>Solver-choice generalization\<close>

text \<open>
  \<^const>\<open>entry_state_eqs\<close> names no solve function -- only \<open>ectx_spec\<close> and
  the routing policy -- so it is exactly as solver-independent as
  \<open>ictx_eqs\<close> at \<open>Ctx_None\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s \<open>analyse_interval_dg_join_for\<close>/
  \<open>_per_origin_for\<close> alongside the Warrow default), and exactly as its own
  \<open>Interval_Ctx_Call_String_Sound\<close> sibling solves the routed call-string
  system under every discipline. \<^const>\<open>entry_state_sol_prog\<close> (Warrow,
  the shipped default) is untouched.
\<close>

definition entry_state_sol_prog_join ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_join gs p =
     TD_side_always_join_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition entry_state_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_per_origin gs p =
     TD_side_per_origin_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_entry_state_result_for_join ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_join gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_join gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_join gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_join_def [code del]

lemma analyse_interval_entry_state_result_for_join_code [code]:
  "analyse_interval_entry_state_result_for_join gs p =
     (let sol = entry_state_sol_prog_join gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_join_def Let_def by (rule refl)

definition analyse_interval_entry_state_result_for_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_per_origin gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_per_origin gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_per_origin gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_per_origin_def [code del]

lemma analyse_interval_entry_state_result_for_per_origin_code [code]:
  "analyse_interval_entry_state_result_for_per_origin gs p =
     (let sol = entry_state_sol_prog_per_origin gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_per_origin_def Let_def by (rule refl)

definition entry_state_verdict_report_prog_join ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_join p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_join (declared_global p) p)
       interval_classify_check"

definition entry_state_verdict_report_prog_per_origin ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_per_origin p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_per_origin (declared_global p) p)
       interval_classify_check"

definition analyse_interval_entry_state_join ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_join p = entry_state_verdict_report_prog_join p"

definition analyse_interval_entry_state_per_origin ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_per_origin p =
     entry_state_verdict_report_prog_per_origin p"

definition entry_state_sol_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_wpo gs p =
     TD_side_warrowing_per_origin_Interp_solve (entry_state_eqs_prog gs p)
       (cfg_exit (prog_cfg p), [])"

definition analyse_interval_entry_state_result_for_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_wpo gs p =
     Analysis_Result
       (fst (entry_state_sol_prog_wpo gs p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_wpo gs p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_wpo_def [code del]

lemma analyse_interval_entry_state_result_for_wpo_code [code]:
  "analyse_interval_entry_state_result_for_wpo gs p =
     (let sol = entry_state_sol_prog_wpo gs p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_wpo_def Let_def by (rule refl)

definition entry_state_verdict_report_prog_wpo ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_wpo p =
     classify_checks_verdicts (prog_cfg p)
       (analyse_interval_entry_state_result_for_wpo (declared_global p) p)
       interval_classify_check"

definition analyse_interval_entry_state_wpo ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_wpo p =
     entry_state_verdict_report_prog_wpo p"

end
