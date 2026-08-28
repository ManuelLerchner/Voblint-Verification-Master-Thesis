theory Interval_Ctx_Entry_State_Sound
  imports
    "Voblint_Core.Exec_DG_Bridge"
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Analysis.Interval_Transfer"
    "Voblint_Analysis.Interval_Exec_Sound"
    "Voblint_Analysis.Interval_Checks"
    "Voblint_Core.Routed_Context"
    "Voblint_Core.Entry_State_Routed_Context"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation"
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
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) of taking \<open>is_bot_pred\<close> as a
  caller-supplied parameter rather than deriving it internally. Callers with a concrete
  program supply \<open>resolved_st_q_is_bot_for (declared_global_vars p)\<close>, exact for
  \<^const>\<open>is_bot_state\<close> (\<open>resolved_st_q_is_bot_for_iff\<close>).\<close>
definition ectx_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_spec"
where
  "ectx_spec gs is_bot_pred = base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)"

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

definition entry_state_entered ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st lifted" where
  "entry_state_entered gs is_bot_pred d ca =
     (case ca of CallEdge dst fs as \<Rightarrow> transfer_lift is_bot_pred (ivl_enter_st_for gs fs as) d)"

definition entry_state_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route gs is_bot_pred d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars
          (\<lambda>x. lookup_resolved_st_q
                 (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)
                 (location_of gs x)))"

definition entry_state_route_gen ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> ivl exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "entry_state_route_gen gs is_bot_pred u ctx d ca = entry_state_route gs is_bot_pred d ca"

text \<open>
  The same routing decision taken on a caller state that has already left the
  executable substrate: the argument is the \<^typ>\<open>ivl abs_state\<close> a
  \<^const>\<open>Reachable\<close> point of an \<^type>\<open>analysis_result\<close> hands out, so a
  consumer of a solved table can recompute a call's callee context without
  reopening the solver's own solution map.

  The type is \<^typ>\<open>ivl abs_state\<close>, not \<^typ>\<open>ivl abs_state point_state\<close>, on
  purpose: reachability is the caller's case split, decided once by
  \<^const>\<open>normalize_point\<close> when the table was built, and an \<^const>\<open>Unreachable\<close>
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
  non-executable whole-state test \<^const>\<open>is_bot_state\<close> quantifies over all
  of \<^typ>\<open>vname\<close>, which is what keeps \<open>entry_state_route_abs\<close> non-executable.

  It routes on the static \<^const>\<open>CallEdge\<close> and the entered caller state alone,
  matching \<^const>\<open>entry_state_route_gen\<close>'s own independence of the caller's
  identity, \<open>entry_state_route_gen_def\<close>: the callee context is a function of
  what is passed, never of who passes it.
\<close>

definition entered_is_bot_for :: "vname list \<Rightarrow> ivl abs_state \<Rightarrow> bool" where
  "entered_is_bot_for pars entered = list_ex (\<lambda>x. is_bot (entered x)) pars"

text \<open>
  Restricting \<^const>\<open>is_bot_state\<close>'s witness search to the formals is exact,
  not merely a heuristic: \<^const>\<open>enter_frame_D\<close> resets every non-global
  variable to \<^const>\<open>ivl_top\<close> and leaves every global at the caller's own
  value, so no name outside the formals can ever witness bottomness once the
  caller itself is not \<^const>\<open>is_bot_state\<close> -- \<open>entered_is_bot_for_correct\<close>
  below states this precisely.
\<close>

lemma entered_is_bot_for_correct:
  assumes not_bot: "\<not> is_bot_state st"
  shows "entered_is_bot_for pars (enter\<^sup># (ivl_tf_for gs) pars args st)
           = is_bot_state (enter\<^sup># (ivl_tf_for gs) pars args st)"
proof -
  define frame where "frame = enter_frame_D gs ivl_top st"
  define entered where "entered = bind_formals pars (map (\<lambda>e. aval_ivl e st) args) frame"
  have unfold: "enter\<^sup># (ivl_tf_for gs) pars args st = entered"
    by (simp add: ivl_tf_for_def enter_ivl_for_def enter_D_def entered_def frame_def)
  have frame_not_bot: "\<not> is_bot (frame x)" for x
  proof (cases "gs x")
    case True
    then have "frame x = st x" by (simp add: frame_def enter_frame_D_def)
    with not_bot show ?thesis by (auto simp: is_bot_state_def)
  next
    case False
    then have "frame x = ivl_top" by (simp add: frame_def enter_frame_D_def)
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
  have "is_bot_state entered \<longleftrightarrow> (\<exists>x. is_bot (entered x))"
    by (simp add: is_bot_state_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>x \<in> set pars. is_bot (entered x))"
    using off_pars frame_not_bot by metis
  also have "\<dots> \<longleftrightarrow> list_ex (\<lambda>x. is_bot (entered x)) pars"
    by (simp add: list_ex_iff)
  finally show ?thesis
    unfolding unfold entered_is_bot_for_def by (simp add: unfold)
qed

definition entry_state_callee_ctx ::
    "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> ivl abs_state \<Rightarrow> ivl list option" where
  "entry_state_callee_ctx gs ca st =
     (case ca of CallEdge dst pars args \<Rightarrow>
        (let entered = enter\<^sup># (ivl_tf_for gs) pars args st
         in if entered_is_bot_for pars entered then None
            else Some (formals_context pars entered)))"

subsection \<open>The routed equation system and its executable solution\<close>

definition entry_state_eqs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> ivl list, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "entry_state_eqs gs is_bot_pred Pi ps mnm main =
     side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
       (entry_state_route_gen gs is_bot_pred)
      (routed_cmb_g_contribution (ectx_spec gs is_bot_pred) Global Seed
         (static_resolve (compile_prog Pi ps mnm main)))
      (routed_extra_g Seed Global)
       (compile_prog Pi ps mnm main) (ectx_spec gs is_bot_pred) Bot (Lifted cinit_ivl_st) Bot"

definition entry_state_sol ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol gs is_bot_pred Pi ps mnm main =
     TD_side_warrowing_apinis_Interp_solve (entry_state_eqs gs is_bot_pred Pi ps mnm main)
       (cfg_exit (compile_prog Pi ps mnm main), [])"

definition entry_state_terminates ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "entry_state_terminates gs is_bot_pred Pi ps mnm main =
     TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       (entry_state_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"

text \<open>
  Discharging termination by execution, exactly as
  \<open>ictx_terminates_prog_via_solve_c\<close> discharges
  \<open>ictx_terminates_prog\<close>.
\<close>

lemma entry_state_terminates_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c (entry_state_eqs gs is_bot_pred Pi ps mnm main)
             (cfg_exit (compile_prog Pi ps mnm main), []) \<noteq> None"
  shows "entry_state_terminates gs is_bot_pred Pi ps mnm main"
  unfolding entry_state_terminates_def
  by (rule TD_side_warrowing_apinis_Interp.solve_dom_of_solve_c[OF assms])

subsection \<open>Whole-program convenience layer\<close>

text \<open>
  \<open>Pi ps mnm main\<close> alone give no @{type imp_prog} to read a declared-global list off of, so
  \<open>entry_state_eqs\<close> and friends keep \<open>is_bot_pred\<close> as an explicit parameter, mirroring
  \<open>ictx_eqs\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>). The \<open>_prog\<close> wrappers do
  have a program and instantiate \<open>is_bot_pred\<close> to \<^const>\<open>resolved_st_q_is_bot_for\<close> at its own
  \<^const>\<open>declared_global_vars\<close>, mirroring \<open>ictx_sol_prog\<close>.
\<close>

definition entry_state_eqs_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "entry_state_eqs_prog gs mnm p =
     entry_state_eqs gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition entry_state_sol_prog ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog gs mnm p =
     entry_state_sol gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

definition entry_state_terminates_prog :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "entry_state_terminates_prog gs mnm p =
     entry_state_terminates gs (resolved_st_q_is_bot_for (declared_global_vars p))
       (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma entry_state_terminates_prog_via_solve_c:
  assumes "TD_side_warrowing_apinis_Interp_solve_c
             (entry_state_eqs_prog gs mnm p)
             (cfg_exit (compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)), []) \<noteq> None"
  shows "entry_state_terminates_prog gs mnm p"
  using assms
  unfolding entry_state_terminates_prog_def entry_state_eqs_prog_def
  by (rule entry_state_terminates_via_solve_c)

section \<open>Route consistency and the abstract transport of the executable solution\<close>

text \<open>
  Mirrors an entry-state acceptance example's \<open>Sound\<close> theory, generalized from one
  fixed compiled program to an arbitrary one: nothing in that argument used the
  example's concrete shape, only the generic commutation facts
  \<open>ivl_Henter_for\<close>/\<open>ivl_Hcomb_for\<close>/\<open>ivl_Hstep_for\<close>, so every lemma
  below repeats \<open>gs Pi ps mnm main\<close> as free variables exactly as
  \<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>'s own theorems do.
\<close>

subsection \<open>The abstract routed hooks\<close>

text \<open>
  Classifier-parametric commutation mirrors, generic in \<open>gs\<close>: same aliases the
  entry-state example's own base theory defines, not tied to any one \<open>gs\<close>.
\<close>

subsection \<open>The abstract routed hooks\<close>

text \<open>
  Classifier-parametric commutation mirrors, generic in \<open>gs\<close>: same aliases the
  entry-state example's own base theory defines, not tied to any one \<open>gs\<close>.
  \<open>ectx_abs_spec\<close> and every hook below carry the reachability-lifted abstract
  carrier, mirroring \<open>ectx_spec\<close> itself.
  Every commutation fact between the executable and abstract solvers threads
  the same explicit \<open>is_bot_pred\<close>/\<open>exact\<close> pair the flat pipeline uses,
  discharged only once a concrete program supplies \<open>resolved_st_q_is_bot_for\<close>.
  The whole-CFG commute obligations (\<open>Hcmb\<close>/\<open>Hextra\<close> below) are discharged
  through \<open>dg_reader_commute_gen\<close>, the carrier-generic
  engine \<open>Voblint_Core.Exec_DG_Bridge\<close> proves once and instantiates here at
  the lifted reader \<open>map_lift (fun_of_resolved_st_q_for gs)\<close>.
\<close>

text \<open>
  The three primitive packaging commutes, at the Base-style record: \<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>
  proves them once generically from \<^theory>\<open>Voblint_Core.DG_Base\<close>'s \<open>transfer_lift_commute\<close>/
  \<open>transfer_lift2_commute\<close>, so only Interval's own primitive facts
  \<open>ivl_tf_st_for_commute\<close>/\<open>ivl_enter_st_for_commute\<close> are supplied here. They are restated at
  \<^const>\<open>fun_of_resolved_st_q_for\<close> rather than its \<^const>\<open>fun_of_exec_dg_st_for\<close> alias so
  every fact below shares one reader with \<open>part_post_solution_seed_dg_st_to_abs_lifted_for\<close>.
\<close>

lemma ivl_Hstep_lifted_for:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
           (dg_spec_step (base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)) a d g)
         = dg_spec_step (base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)) a
             (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [unfolded fun_of_exec_dg_st_for_def, OF ivl_tf_st_for_commute exact])

lemma ivl_Henter_lifted_for:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
           (dgs_enter (base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)) xs es d g)
         = dgs_enter (base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)) xs es
             (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [unfolded fun_of_exec_dg_st_for_def, OF ivl_enter_st_for_commute exact])

lemma ivl_Hcomb_lifted_for:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
           (dgs_combine (base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)) dst dc de g)
         = dgs_combine (base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)) dst
             (map_lift (fun_of_resolved_st_q_for gs) dc) (map_lift (fun_of_resolved_st_q_for gs) de)
             (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute
        [where tf = "ivl_tf_for gs", unfolded fun_of_exec_dg_st_for_def, OF exact])

lemma ivl_Hcont_lifted_for:
  "map_lift (fun_of_resolved_st_q_for gs)
     (caller_cont (base_dg_spec_st_for_lifted gs is_bot_pred (ivl_tf_st_for gs) (ivl_enter_st_for gs)) ci dc g)
   = caller_cont (base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)) ci
       (map_lift (fun_of_resolved_st_q_for gs) dc) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_caller_cont_commute
        [where tf = "ivl_tf_for gs", unfolded fun_of_exec_dg_st_for_def])

text \<open>
  Registers \<open>dg_reader_commute_gen\<close> (\<^theory>\<open>Voblint_Core.Exec_DG_Bridge\<close>)
  at the one reader this whole section needs --
  the lifted executable-to-abstract readback \<open>map_lift (fun_of_resolved_st_q_for gs)\<close> used
  identically for both the local and global carrier -- so every locale fact below
  (\<open>dg_tree_st_commute_def\<close>, \<open>fun_of_dg_st_gen_sup\<close>, ...) is available unconditionally,
  the guard already discharged, instead of citing each one with an explicit \<open>[OF ...]\<close>.
\<close>

lemma dg_reader_commute_gen_ivl_lifted:
  "dg_reader_commute_gen
     (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))"
  by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)

definition ectx_abs_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_spec" where
  "ectx_abs_spec gs = base_dg_spec_for_lifted gs is_bot_state (ivl_tf_for gs)"

definition entered_state_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> ivl abs_state lifted \<Rightarrow> call_action \<Rightarrow> ivl abs_state lifted" where
  "entered_state_abs gs d ca =
     (case ca of CallEdge dst fs as \<Rightarrow> transfer_lift is_bot_state (enter\<^sup># (ivl_tf_for gs) fs as) d)"

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
  \<^const>\<open>entered_state_abs\<close>'s own \<open>enter#\<close> application is exactly \<open>enter_local\<close> applied
  to \<^const>\<open>ectx_abs_spec\<close> (\<open>dgs_enter_base_for_lifted\<close>). Kept as their own named
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
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs) (entry_state_entered gs is_bot_pred s ca)
     = entered_state_abs gs (map_lift (fun_of_resolved_st_q_for gs) s) ca"
proof (cases ca)
  case (CallEdge dst fs as)
  have step: "map_lift (fun_of_resolved_st_q_for gs) (transfer_lift is_bot_pred (ivl_enter_st_for gs fs as) s)
      = transfer_lift is_bot_state (enter\<^sup># (ivl_tf_for gs) fs as) (map_lift (fun_of_resolved_st_q_for gs) s)"
    by (rule transfer_lift_commute
          [where phi = "fun_of_resolved_st_q_for gs" and f = "ivl_enter_st_for gs fs as"
             and F = "enter\<^sup># (ivl_tf_for gs) fs as" and is_bot_pred = is_bot_pred
             and is_bot_pred' = is_bot_state, OF ivl_enter_st_for_commute exact])
  show ?thesis
    unfolding entry_state_entered_def entered_state_abs_def CallEdge
    by (simp add: step)
qed

lemma entry_state_route_commute:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "entry_state_route_abs gs (map_lift (fun_of_resolved_st_q_for gs) s) ca
           = entry_state_route gs is_bot_pred s ca"
  by (cases ca; cases s)
     (simp_all add: entry_state_route_abs_def entry_state_route_def
                    formals_context_def fun_of_resolved_st_q_for_def)

lemma entry_state_route_commute_gen:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
  shows "entry_state_route_gen gs is_bot_pred u ctx s ca
           = entry_state_route_abs_gen gs u ctx (map_lift (fun_of_resolved_st_q_for gs) s) ca"
  by (simp add: entry_state_route_gen_def entry_state_route_abs_gen_def entry_state_route_commute[OF exact])

text \<open>
  Presentation-side routing agrees with the routing that built the equation
  system, on both outcomes. A caller point the table answers \<^const>\<open>Reachable\<close>
  either routes to the same callee context the solved system was built with,
  or is exactly the case that context is dead: \<open>entry_state_callee_ctx\<close>
  answers \<^const>\<open>None\<close> iff the entered callee frame is itself
  \<^const>\<open>is_bot_state\<close>, which is precisely when \<^const>\<open>entry_state_route_abs\<close>'s
  own bottom collapse fires. There is no unaddressed case left over: unlike
  the earlier single-outcome fact this replaces, this theorem needs no \<open>live\<close>
  side condition, because it states what happens on both branches instead of
  assuming the live one.

  \<open>reach\<close> says the normalized state is the reader's image of the solved local
  unknown -- the shape \<open>normalize_point_Reachable_map_lift\<close> supplies for any
  point a result table answered \<^const>\<open>Reachable\<close>. \<open>not_bot\<close> says that
  normalized state is not itself \<^const>\<open>is_bot_state\<close>, which
  \<open>normalize_point\<close>'s own witness-bottom test already guarantees for every
  \<^const>\<open>Reachable\<close> point a table built through it can produce.
\<close>

theorem entry_state_callee_ctx_eq_route_partial:
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and reach: "map_lift (fun_of_resolved_st_q_for gs) d = Lifted st"
    and not_bot: "\<not> is_bot_state st"
  shows "entry_state_callee_ctx gs ca st =
    (if entered_state_abs gs (Lifted st) ca = Bot
     then None
     else Some (entry_state_route gs is_bot_pred (entry_state_entered gs is_bot_pred d ca) ca))"
proof (cases ca)
  case (CallEdge dst pars args)
  define entered where "entered = enter\<^sup># (ivl_tf_for gs) pars args st"
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
    have "entry_state_route gs is_bot_pred (entry_state_entered gs is_bot_pred d ca) ca
        = entry_state_route_abs gs
            (map_lift (fun_of_resolved_st_q_for gs) (entry_state_entered gs is_bot_pred d ca)) ca"
      by (simp add: entry_state_route_commute[OF exact])
    also have "\<dots> = entry_state_route_abs gs (entered_state_abs gs (Lifted st) ca) ca"
      using entry_state_entered_commute[OF exact] reach by simp
    also have "\<dots> = formals_context pars entered"
      unfolding entry_state_route_abs_def
      using entered_state_eq False CallEdge by simp
    finally have "entry_state_route gs is_bot_pred (entry_state_entered gs is_bot_pred d ca) ca
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

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
  assumes exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

interpretation ivl_es: routed_domain_exec
  gs is_bot_pred "ivl_tf_st_for gs" "ivl_enter_st_for gs" "ivl_tf_for gs"
  Global Seed "entry_state_route_gen gs is_bot_pred" "entry_state_route_abs_gen gs"
  static_resolve static_resolve
  by unfold_locales
     (rule ivl_tf_st_for_commute, rule ivl_enter_st_for_commute, rule exact, simp,
      rule entry_state_route_commute_gen[OF exact], simp add: static_resolve_def)

lemmas ivl_es_pp_abs_gen = ivl_es.pp_abs

end


subsection \<open>The certified executable post-solution, generic per compiled program\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "entry_state_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma entry_state_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(gk) TYPE((ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
     (entry_state_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])"
  using solves[unfolded entry_state_terminates_def] .

lemma entry_state_pp_st:
  "part_post_solution (entry_state_eqs gs is_bot_pred Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main), [])
     (snd (entry_state_sol gs is_bot_pred Pi ps mnm main)) (fst (entry_state_sol gs is_bot_pred Pi ps mnm main))"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF entry_state_solve_dom, of "fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
             "snd (entry_state_sol gs is_bot_pred Pi ps mnm main)"]
  unfolding entry_state_sol_def by simp

theorem entry_state_pp_abs:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) (entry_state_route_abs_gen gs)
        (routed_cmb_g (ectx_abs_spec gs) Global Seed
           (static_resolve (compile_prog Pi ps mnm main)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps mnm main) (ectx_abs_spec gs)
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))
        (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
        (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)))
     (cfg_exit (compile_prog Pi ps mnm main), [])
     (fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
        \<circ> snd (entry_state_sol gs is_bot_pred Pi ps mnm main))
     (fst (entry_state_sol gs is_bot_pred Pi ps mnm main))"
proof -
  have pp_buf: "part_post_solution
       (side_cfg_T_eff_keyed_seed_dg_buffered intra_predecessor_addr_list (\<lambda>_. Global)
          (entry_state_route_gen gs is_bot_pred)
          (routed_cmb_g_contribution (ectx_spec gs is_bot_pred) Global Seed
             (static_resolve (compile_prog Pi ps mnm main)))
          (routed_extra_g Seed Global)
          (compile_prog Pi ps mnm main) (ectx_spec gs is_bot_pred)
          Bot (Lifted cinit_ivl_st) Bot)
       (cfg_exit (compile_prog Pi ps mnm main), [])
       (snd (entry_state_sol gs is_bot_pred Pi ps mnm main))
       (fst (entry_state_sol gs is_bot_pred Pi ps mnm main))"
    using entry_state_pp_st unfolding entry_state_eqs_def by simp
  show ?thesis
    using pp_buf unfolding ectx_spec_def
    by (rule ivl_es_pp_abs_gen[OF exact, folded ectx_abs_spec_def])
qed


end


section \<open>Activation-indexed collecting soundness, generic per compiled program\<close>

text \<open>
  Stated for an arbitrary compiled program: the trace-semantic context function
  \<open>entry_state_context\<close> ignores its concrete-store argument and instead
  recomputes the routed value the executable solver already produced, using
  \<^const>\<open>call_action_at_call_site\<close> to resolve the one call at a node --
  \<open>compile_prog_calls_source_unique\<close> is what makes that resolution unambiguous
  for \<open>any\<close> \<^const>\<open>compile_prog\<close> output, not just the acceptance example's one
  call site.

  Four more obligations are properties of the \<open>solved\<close> system -- which keys the
  executable solver actually covers, given its own seed/routing/query behavior --
  not of routing ambiguity. \<open>compile_prog_calls_source_unique\<close> does not
  bear on them, and no generic dependency-closure theorem for the keyed D/G solver
  exists yet in this development: the analogous fact for the flat, unkeyed solver
  does not transfer to \<^const>\<open>side_cfg_T_eff_keyed_seed_dg\<close>. They are carried here the same way
  \<^const>\<open>entry_state_terminates\<close> already is: as \<open>by eval\<close>-checkable hypotheses on
  a concrete, terminated solve, not as a hidden singleton- or exact-entry-style
  premise. Closing that gap with a proved dependency-closure theorem is future
  work, not required by this milestone.
\<close>

text \<open>
  Executable twins of the context's own \<open>entry_state_sigma_abs\<close>/\<open>entry_state_sg\<close>
  (below), defined here before that \<open>context\<close> so their equations are
  unconditional. Neither reads anything but \<^const>\<open>entry_state_sol\<close>: none of
  the context's soundness obligations (\<open>wf\<close>, \<open>solves\<close>, \<open>entry_cov\<close>, \<open>fwd_ok\<close>,
  \<open>call_fwd_ok\<close>, \<open>comb_fwd_ok\<close>) are needed to compute them, but the code
  generator cannot discharge those obligations as a runtime side-condition,
  so the context-local names -- kept, unchanged in shape, for the soundness
  development below -- are simply defined as aliases of these.
\<close>

definition entry_state_sigma_abs_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> ivl list + gk \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "entry_state_sigma_abs_exec gs is_bot_pred Pi ps mnm main =
     fun_of_dg_st_gen (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
       \<circ> snd (entry_state_sol gs is_bot_pred Pi ps mnm main)"

definition entry_state_sg_exec ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> pp \<times> ivl list + gk \<Rightarrow> ivl abs_state lifted" where
  "entry_state_sg_exec gs is_bot_pred Pi ps mnm main k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)
           then locals (entry_state_sigma_abs_exec gs is_bot_pred Pi ps mnm main (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "ivl exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes wf: "wf_compile_input gs Pi ps mnm main"
    and solves: "entry_state_terminates gs is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), []) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p,
              entry_state_route_abs_gen gs u ctx
                (enter_local (ectx_abs_spec gs) pars args
                   (locals (entry_state_sigma_abs_exec gs is_bot_pred Pi ps mnm main (Inl (u, ctx))))
                   (globs (entry_state_sigma_abs_exec gs is_bot_pred Pi ps mnm main (Inr Global))))
                (CallEdge dst pars args))
            \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
begin

subsection \<open>The semantic solution projection\<close>

definition entry_state_sigma_abs ::
    "pp \<times> ivl list + gk \<Rightarrow> (ivl abs_state lifted, ivl abs_state lifted) dg_state" where
  "entry_state_sigma_abs = entry_state_sigma_abs_exec gs is_bot_pred Pi ps mnm main"

definition entry_state_sg :: "pp \<times> ivl list + gk \<Rightarrow> ivl abs_state lifted" where
  "entry_state_sg = entry_state_sg_exec gs is_bot_pred Pi ps mnm main"

text \<open>
  The trace-semantic context function: ignores its store argument entirely and
  recomputes the routed value from the caller's own solved abstract state, using
  \<^const>\<open>call_action_at_call_site\<close> for the one call at \<open>u\<close>.  This is
  \<open>admiss_exact\<close>'s functional shape, specialized so coverage of infinitely many
  concrete stores comes from the caller's own value being imprecise, not from
  \<open>entry_state_context\<close> being multi-valued.
\<close>

definition entry_state_context :: "cfg_node \<Rightarrow> ivl list \<Rightarrow> store \<Rightarrow> ivl list" where
  "entry_state_context u ctx s =
     (let ca = call_action_at_call_site (compile_prog Pi ps mnm main) u in
        entry_state_route_abs_gen gs u ctx
          (enter_local (ectx_abs_spec gs) (ce_formals ca) (ce_args ca)
             (locals (entry_state_sigma_abs (Inl (u, ctx))))
             (globs (entry_state_sigma_abs (Inr Global)))) ca)"

lemma entry_state_reserved: "reserved_ret_var gs"
  using wf by (rule wf_compile_input_reserved_ret_var)

lemma entry_state_fin: "finite (intra (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

lemma entry_state_finC: "finite (calls (compile_prog Pi ps mnm main))"
  using compile_prog_finite by blast

interpretation entry_state_dg_base: sound_dg_spec "ectx_abs_spec gs" gamma_dg_base gs
  unfolding ectx_abs_spec_def
  by (rule base_dg_spec_sound[OF ivl_is_sound_transfer_for is_bot_state_gamma_state_empty])

text \<open>
  \<^const>\<open>gamma_dg_base\<close> discards its \<open>'G\<close> argument outright, so a covered point's reading
  is the solved local unknown itself, the same projection
  \<^const>\<open>analyse_interval_dg_env_for\<close> reads on the context-insensitive side.
\<close>

lemma entry_state_sg_covered:
  "(v, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)
   \<Longrightarrow> entry_state_sg (Inl (v, ctx)) = locals (entry_state_sigma_abs (Inl (v, ctx)))"
  by (simp add: entry_state_sg_def entry_state_sg_exec_def entry_state_sigma_abs_def entry_state_sigma_abs_exec_def)

lemma entry_state_sg_uncovered_empty:
  "(v, ctx) \<notin> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)
     \<Longrightarrow> gamma_state_lift (entry_state_sg (Inl (v, ctx))) = {}"
  by (simp add: entry_state_sg_def entry_state_sg_exec_def)

subsection \<open>Instantiating the generic routed-context locale\<close>

text \<open>
  \<^locale>\<open>entry_state_routed_context\<close> (\<^theory>\<open>Voblint_Core.Entry_State_Routed_Context\<close>)
  packages the two interpretations this section previously proved separately
  (\<^locale>\<open>dg_ctx_activation_base\<close>, then \<^locale>\<open>routed_context_hetero\<close>) into one: \<open>FinC\<close>,
  \<open>RouteAgree\<close>, and \<open>EnterAgree\<close> -- previously reproved here from \<open>compile_prog_finite\<close>/
  \<open>call_action_at_call_site_eq\<close>/\<open>compile_prog_calls_source_unique\<close> -- are now discharged
  once, generically, inside that locale. Only the five genuine
  \<^locale>\<open>dg_ctx_activation_base\<close> obligations, \<open>seed_key_ne_gk0\<close> (datatype distinctness
  for \<open>gk\<close>), and the two solver-coverage facts \<open>call_fwd\<close>/\<open>comb_fwd\<close> remain premises here.
  \<^const>\<open>entry_state_context\<close> keeps its own name and definition (both \<open>Example_Interval_DG_Ctx_Collect\<close>
  and \<open>Example_Interval_DG_EntryState_Collect\<close> cite it by name); \<open>entry_state_context_eq_route_enterc_of_sigma\<close>
  below identifies it with the locale's own \<open>enterc\<close>, so \<open>entry_state_sg_seed\<close>/\<open>entry_state_sg_comb\<close>
  can still be stated against \<^const>\<open>entry_state_context\<close> while citing the generic \<open>routed_context_call\<close>/\<open>_comb\<close>.
\<close>

interpretation entry_state_routed: entry_state_routed_context "ectx_abs_spec gs" gs
    Pi ps mnm main Global
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)"
    entry_state_sigma_abs "fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), [])" entry_state_sg
    Seed
proof unfold_locales
  show "finite (intra (compile_prog Pi ps mnm main))" by (rule entry_state_fin)
next
  show "part_post_solution
          (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global)
             (formals_route_lifted_gen (ectx_abs_spec gs))
             (routed_cmb_g (ectx_abs_spec gs) Global Seed
                (static_resolve (compile_prog Pi ps mnm main)))
             (routed_extra_g Seed Global)
             (compile_prog Pi ps mnm main) (ectx_abs_spec gs)
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))
             (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
             (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted)))
          (cfg_exit (compile_prog Pi ps mnm main), []) entry_state_sigma_abs
          (fst (entry_state_sol gs is_bot_pred Pi ps mnm main))"
    unfolding entry_state_route_abs_gen_eq_formals_route_lifted_gen[symmetric]
      entry_state_sigma_abs_def entry_state_sigma_abs_exec_def
    by (rule entry_state_pp_abs[OF solves exact])
next
  fix v ctx assume "(v, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (entry_state_sg (Inl (v, ctx)))
          = gamma_dg_base (locals (entry_state_sigma_abs (Inl (v, ctx)))) (globs (entry_state_sigma_abs (Inr Global)))"
    by (simp add: entry_state_sg_covered gamma_dg_base_def)
next
  fix v ctx assume "(v, ctx) \<notin> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
  thus "gamma_state_lift (entry_state_sg (Inl (v, ctx))) = {}"
    by (rule entry_state_sg_uncovered_empty)
next
  fix u a v ctx assume "(u, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)" "(u, a, v) \<in> intra (compile_prog Pi ps mnm main)"
  thus "(v, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)" by (rule fwd_ok)
next
  show "\<And>p ctx. Seed p ctx \<noteq> Global" by simp
next
  fix u ctx dst pars args p cont
  assume mem: "(u, ctx) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
  show "(FunctionEntry p,
           formals_route_lifted_gen (ectx_abs_spec gs) u ctx
             (enter_local (ectx_abs_spec gs) pars args
                (locals (entry_state_sigma_abs (Inl (u, ctx))))
                (globs (entry_state_sigma_abs (Inr Global)))) (CallEdge dst pars args))
          \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
    unfolding entry_state_route_abs_gen_eq_formals_route_lifted_gen[symmetric]
    using mem ce call_fwd_ok
    unfolding entry_state_sigma_abs_def entry_state_sigma_abs_exec_def by blast
next
  fix cl c1 dst pars args p cont
  assume mem: "(cl, c1) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
    and ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
  show "(cont, c1) \<in> fst (entry_state_sol gs is_bot_pred Pi ps mnm main)"
    using mem ce by (rule comb_fwd_ok)
qed

text \<open>
  \<^const>\<open>entry_state_context\<close> -- ignore the store, recompute \<open>route\<close> from \<open>sigma\<close> at
  \<^const>\<open>call_action_at_call_site\<close> -- is exactly \<^locale>\<open>entry_state_routed_context\<close>'s
  own \<open>enterc\<close> (\<open>route_enterc_of_sigma\<close>), once \<open>entry_state_route_abs_gen\<close>'s identity with
  \<^const>\<open>formals_route_lifted_gen\<close> is unfolded.
\<close>

lemma entry_state_context_eq_route_enterc_of_sigma:
  "entry_state_context = route_enterc_of_sigma (ectx_abs_spec gs)
     (formals_route_lifted_gen (ectx_abs_spec gs)) entry_state_sigma_abs Global
     (compile_prog Pi ps mnm main)"
  unfolding entry_state_context_def route_enterc_of_sigma_def
    entry_state_route_abs_gen_eq_formals_route_lifted_gen[symmetric]
  by (rule refl)

lemmas entry_state_routed_context_call =
  entry_state_routed.routed_context_call[folded entry_state_context_eq_route_enterc_of_sigma]
lemmas entry_state_routed_context_comb =
  entry_state_routed.routed_context_comb[folded entry_state_context_eq_route_enterc_of_sigma]

lemma entry_state_sg_seed:
  assumes "(u, CallEdge dst xs es, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
    and "s \<in> gamma_state_lift (entry_state_sg (Inl (u, ctx)))"
  shows "call_enter gs (CallEdge dst xs es) s
           \<in> gamma_state_lift (entry_state_sg
               (Inl (FunctionEntry p, entry_state_context u ctx (call_enter gs (CallEdge dst xs es) s))))"
  by (rule entry_state_routed_context_call[OF assms])

lemma entry_state_sg_comb:
  assumes "(cl, CallEdge dst pars args, FunctionEntry p, v) \<in> calls (compile_prog Pi ps mnm main)"
    and "s \<in> gamma_state_lift (entry_state_sg (Inl (cl, c1)))"
    and "t \<in> gamma_state_lift (entry_state_sg (Inl (FunctionResult p, entry_state_context cl c1 es)))"
    and "call_enter_store gs (compile_prog Pi ps mnm main) cl s es"
  shows "combine_collect gs dst s t \<in> gamma_state_lift (entry_state_sg (Inl (v, c1)))"
  by (rule entry_state_routed_context_comb[OF assms])

subsection \<open>Activation-indexed collecting soundness\<close>

lemma entry_state_cinit_le_cinit_ivl_st:
  "cinit_stores gs \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))"
  by (auto simp: cinit_stores_def gamma_state_def fun_of_resolved_st_q_for_def fun_of_st_cinit_ivl_st_for)

lemma entry_state_locals_ge_s0d:
  "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)
     \<le> locals (entry_state_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))"
proof -
  have "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st)
      \<le> locals (eq entry_state_routed.Gen (cfg_entry (compile_prog Pi ps mnm main), []) entry_state_sigma_abs)"
    by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)
       (rule order_trans[OF _ side_acc_dg_ge_acc], simp add: le_supI2)
  also have "\<dots> \<le> locals (entry_state_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))"
    using entry_state_routed.pp_eq_bound[OF entry_cov] by (simp add: less_eq_dg_state_def)
  finally show ?thesis .
qed

theorem entry_state_activation_collect_sound:
  "activation_collect gs (admiss_exact entry_state_context) [] (compile_prog Pi ps mnm main) (cinit_stores gs) v ctx
     \<subseteq> gamma_state_lift (entry_state_sg (Inl (v, ctx)))"
proof (rule activation_collect_sound_gen[where sg = entry_state_sg and gammaM = gamma_state_lift
        and admiss = "admiss_exact entry_state_context"
        and startcontext = "[]" and S = "cinit_stores gs" and g = "compile_prog Pi ps mnm main" and gs = gs])
  \<comment> \<open>ENTRY_G\<close>
  fix s assume "s \<in> cinit_stores gs"
  hence "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))"
    using entry_state_cinit_le_cinit_ivl_st by blast
  also have "gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
        = gamma_dg_base (map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_ivl_st))
            (map_lift (fun_of_resolved_st_q_for gs) (Bot::ivl exec_dg_st lifted))"
    by (simp add: gamma_dg_base_def)
  also have "\<dots> \<subseteq> gamma_dg_base (locals (entry_state_sigma_abs (Inl (cfg_entry (compile_prog Pi ps mnm main), []))))
                   (globs (entry_state_sigma_abs (Inr Global)))"
    by (rule gamma_dg_base_mono[OF entry_state_locals_ge_s0d entry_state_routed.pp_entry_s0g_bound[OF entry_cov]])
  also have "\<dots> = gamma_state_lift (entry_state_sg (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))"
    unfolding entry_state_sg_covered[OF entry_cov] gamma_dg_base_def by (rule refl)
  finally show "s \<in> gamma_state_lift (entry_state_sg (Inl (cfg_entry (compile_prog Pi ps mnm main), [])))" .

next
  \<comment> \<open>EDGE\<close>
  show "\<And>u a v c s s'. (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
        \<Longrightarrow> s \<in> gamma_state_lift (entry_state_sg (Inl (u, c))) \<Longrightarrow> s' \<in> edge_step a s
        \<Longrightarrow> s' \<in> gamma_state_lift (entry_state_sg (Inl (v, c)))"
    by (rule entry_state_routed.dg_ctx_act_edge)
next
  \<comment> \<open>ADMISS_TOTAL\<close>
  show "\<And>u c s. \<exists>c'. admiss_exact entry_state_context u c s c'"
    by (simp add: admiss_exact_def)
next
  \<comment> \<open>CALL\<close>
  fix u dst pars args p cont c s c'
  assume ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
    and sm: "s \<in> gamma_state_lift (entry_state_sg (Inl (u, c)))"
    and adm: "admiss_exact entry_state_context u c (call_enter gs (CallEdge dst pars args) s) c'"
  show "call_enter gs (CallEdge dst pars args) s \<in> gamma_state_lift (entry_state_sg (Inl (FunctionEntry p, c')))"
    using adm entry_state_sg_seed[OF ce sm] by (simp add: admiss_exact_def)
next
  \<comment> \<open>COMB\<close>
  fix cl dst pars args p cont c1 c2 s t es
  assume ce: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)"
    and sm: "s \<in> gamma_state_lift (entry_state_sg (Inl (cl, c1)))"
    and adm: "admiss_exact entry_state_context cl c1 es c2"
    and tm: "t \<in> gamma_state_lift (entry_state_sg (Inl (FunctionResult p, c2)))"
    and ces: "call_enter_store gs (compile_prog Pi ps mnm main) cl s es"
  show "combine_collect gs dst s t \<in> gamma_state_lift (entry_state_sg (Inl (cont, c1)))"
    using adm tm entry_state_sg_comb[OF ce sm _ ces] by (simp add: admiss_exact_def)
qed

end



section \<open>Solved-result table\<close>

text \<open>
  The solved entry-state D/G system, read as a
  \<^typ>\<open>(ivl list, ivl abs_state) analysis_result\<close>. This is the
  context-sensitive counterpart of \<open>Interval_Checks\<close>'s monovariant
  \<open>analyse_interval_td_result_for\<close>: the context type is \<^typ>\<open>ivl list\<close>, the
  entered abstract value of the callee's declared formals, so a node covered
  under several activations keeps one \<^type>\<open>point_state\<close> per activation.

  Construction is mechanical. \<^const>\<open>entry_state_sol\<close>'s own first component is
  the key set verbatim -- the solver already knows exactly which
  \<open>(node, context)\<close> pairs it reached, so nothing here rescans the solved map
  or reconstructs coverage. Each local unknown goes through
  \<^const>\<open>normalize_point\<close> exactly as it is stored, in its pre-conversion
  \<^typ>\<open>ivl resolved_st_q lifted\<close> shape; no context is joined at construction
  time, and an uncovered context is answered by \<^const>\<open>lookup_context\<close>'s
  membership guard with \<^const>\<open>Unreachable\<close>, never by falling back to the
  seeded default context \<open>[]\<close>.

  The \<open>[code]\<close> rewrite is a single-solve fix: binding \<open>sol\<close> once, outside the
  per-key closure, compiles to a single shared thunk, so neither building the
  table nor querying it re-solves. \<^const>\<open>entry_state_sol_prog\<close> is fully
  applied at that binding, so it is not the partially applied closure
  \<^const>\<open>entry_state_sg_exec\<close> would produce, whose body -- including its own
  internal \<^const>\<open>entry_state_sol\<close> calls -- would re-run at every key.
\<close>

definition analyse_interval_entry_state_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for gs mnm p =
     Analysis_Result
       (fst (entry_state_sol_prog gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog gs mnm p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_def [code del]

lemma analyse_interval_entry_state_result_for_code [code]:
  "analyse_interval_entry_state_result_for gs mnm p =
     (let sol = entry_state_sol_prog gs mnm p; gl = declared_global_vars p
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
     analyse_interval_entry_state_result_for (declared_global p) prog_main_name p"

text \<open>
  The route-consistency corollary at the table, on both outcomes: a caller
  point the table answers \<^const>\<open>Reachable\<close> either routes to the same callee
  context the solved system was built with, or is exactly the case that
  context is dead. \<^const>\<open>lookup_context\<close>'s membership guard supplies \<open>reach\<close>
  --- an uncovered key answers \<^const>\<open>Unreachable\<close>, so a \<^const>\<open>Reachable\<close>
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
  assumes reach: "lookup_context (analyse_interval_entry_state_result_for (declared_global p) mnm p)
                    u ctx = Reachable st"
  shows "entry_state_callee_ctx (declared_global p) ca st =
    (if entered_state_abs (declared_global p) (Lifted st) ca = Bot
     then None
     else Some (entry_state_route (declared_global p)
               (resolved_st_q_is_bot_for (declared_global_vars p))
               (entry_state_entered (declared_global p)
                  (resolved_st_q_is_bot_for (declared_global_vars p))
                  (locals (snd (entry_state_sol_prog (declared_global p) mnm p) (Inl (u, ctx)))) ca)
               ca))"
proof -
  have globals: "\<And>x. declared_global p x = (x \<in> set (declared_global_vars p))" by simp
  have exact: "\<And>s. resolved_st_q_is_bot_for (declared_global_vars p) s
                     = is_bot_state (fun_of_resolved_st_q_for (declared_global p) s)"
    by (rule resolved_st_q_is_bot_for_iff[OF globals])
  have norm: "normalize_point (declared_global p)
                (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                  (locals (snd (entry_state_sol_prog (declared_global p) mnm p) (Inl (u, ctx)))))
              = Reachable st"
    using reach
    by (simp add: lookup_context_def analyse_interval_entry_state_result_for_def
                  split: if_splits)
  have key: "map_lift (fun_of_resolved_st_q_for (declared_global p))
               (locals (snd (entry_state_sol_prog (declared_global p) mnm p) (Inl (u, ctx))))
             = Lifted st
           \<and> \<not> is_bot_state st"
  proof (cases "locals (snd (entry_state_sol_prog (declared_global p) mnm p) (Inl (u, ctx)))")
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
                      (locals (snd (entry_state_sol_prog (declared_global p) mnm p) (Inl (u, ctx))))
                    = Lifted st"
    and not_bot: "\<not> is_bot_state st"
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
  satisfies \<^const>\<open>interval_less_true\<close> and \<open>check_true\<close> vacuously, so
  the check classifies \<^const>\<open>Check_Proved\<close> even though no execution reaches
  it. \<^const>\<open>lookup_context\<close> answers \<^const>\<open>Unreachable\<close> for both cases
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
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> (ivl list \<times> contextual_verdict) set) list" where
  "entry_state_check_projection mnm p =
     classify_checks_ctx (prog_cfg mnm p)
       (analyse_interval_entry_state_result_for (declared_global p) mnm p)
       interval_classify_check"

definition entry_state_verdict_report_prog ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog mnm p =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs)))
       (entry_state_check_projection mnm p)"

text \<open>Aggregating the projection is exactly \<^const>\<open>classify_checks_verdicts\<close>
  over the same table; going through the projection is what keeps the two
  reports to one shared solve.\<close>

lemma entry_state_verdict_report_prog_eq:
  "entry_state_verdict_report_prog mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_interval_entry_state_result_for (declared_global p) mnm p)
       interval_classify_check"
  unfolding entry_state_verdict_report_prog_def entry_state_check_projection_def
  by (rule classify_checks_verdicts_proj)

definition analyse_interval_entry_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state p = entry_state_verdict_report_prog prog_main_name p"

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
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_join gs mnm p =
     TD_side_always_join_Interp_solve (entry_state_eqs_prog gs mnm p)
       (cfg_exit (prog_cfg mnm p), [])"

definition entry_state_sol_prog_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_per_origin gs mnm p =
     TD_side_per_origin_Interp_solve (entry_state_eqs_prog gs mnm p)
       (cfg_exit (prog_cfg mnm p), [])"

definition analyse_interval_entry_state_result_for_join ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_join gs mnm p =
     Analysis_Result
       (fst (entry_state_sol_prog_join gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_join gs mnm p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_join_def [code del]

lemma analyse_interval_entry_state_result_for_join_code [code]:
  "analyse_interval_entry_state_result_for_join gs mnm p =
     (let sol = entry_state_sol_prog_join gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_join_def Let_def by (rule refl)

definition analyse_interval_entry_state_result_for_per_origin ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_per_origin gs mnm p =
     Analysis_Result
       (fst (entry_state_sol_prog_per_origin gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_per_origin gs mnm p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_per_origin_def [code del]

lemma analyse_interval_entry_state_result_for_per_origin_code [code]:
  "analyse_interval_entry_state_result_for_per_origin gs mnm p =
     (let sol = entry_state_sol_prog_per_origin gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_per_origin_def Let_def by (rule refl)

definition entry_state_verdict_report_prog_join ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_join mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_interval_entry_state_result_for_join (declared_global p) mnm p)
       interval_classify_check"

definition entry_state_verdict_report_prog_per_origin ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_per_origin mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_interval_entry_state_result_for_per_origin (declared_global p) mnm p)
       interval_classify_check"

definition analyse_interval_entry_state_join ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_join p = entry_state_verdict_report_prog_join prog_main_name p"

definition analyse_interval_entry_state_per_origin ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_per_origin p =
     entry_state_verdict_report_prog_per_origin prog_main_name p"

definition entry_state_sol_prog_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "entry_state_sol_prog_wpo gs mnm p =
     TD_side_warrowing_per_origin_Interp_solve (entry_state_eqs_prog gs mnm p)
       (cfg_exit (prog_cfg mnm p), [])"

definition analyse_interval_entry_state_result_for_wpo ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (ivl list, ivl abs_state) analysis_result" where
  "analyse_interval_entry_state_result_for_wpo gs mnm p =
     Analysis_Result
       (fst (entry_state_sol_prog_wpo gs mnm p))
       (\<lambda>v ctx. normalize_point gs
                  (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                    (locals (snd (entry_state_sol_prog_wpo gs mnm p) (Inl (v, ctx))))))"

declare analyse_interval_entry_state_result_for_wpo_def [code del]

lemma analyse_interval_entry_state_result_for_wpo_code [code]:
  "analyse_interval_entry_state_result_for_wpo gs mnm p =
     (let sol = entry_state_sol_prog_wpo gs mnm p; gl = declared_global_vars p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"
  unfolding analyse_interval_entry_state_result_for_wpo_def Let_def by (rule refl)

definition entry_state_verdict_report_prog_wpo ::
    "pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdict_report_prog_wpo mnm p =
     classify_checks_verdicts (prog_cfg mnm p)
       (analyse_interval_entry_state_result_for_wpo (declared_global p) mnm p)
       interval_classify_check"

definition analyse_interval_entry_state_wpo ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "analyse_interval_entry_state_wpo p =
     entry_state_verdict_report_prog_wpo prog_main_name p"

end
