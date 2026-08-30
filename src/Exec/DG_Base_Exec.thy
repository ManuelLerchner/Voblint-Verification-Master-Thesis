theory DG_Base_Exec
  imports "Voblint_Core.DG_Base" Exec_DG_Bridge
begin

section \<open>Executable Base-style DG construction\<close>

text \<open>
  Executable mirror of \<^const>\<open>base_dg_spec_for_lifted\<close>: same shape, over
  \<open>'a exec_dg_st lifted\<close> instead of \<open>'a abs_state lifted\<close>, with \<open>tf_st\<close> a bare
  \<open>edge_action \<Rightarrow> _\<close> dispatcher (the executable representation has no
  \<^type>\<open>domain_transfer\<close> record) and \<open>enter_st\<close> its enter counterpart.

  Unlike the mathematical side, \<open>dgs_combine_env\<close> here is \<^emph>\<open>not\<close> the identity:
  \<^const>\<open>combine_assign_resolved_q\<close> (unlike \<^const>\<open>combine_collect_abs\<close> on the
  mathematical side) does not itself select locals-from-caller/globals-from-callee
  -- that selection is exactly what \<^const>\<open>combine_resolved_st_q\<close> already computes
  (\<open>fun_of_resolved_st_q_for_combine\<close>: it agrees with \<^const>\<open>combine_env_abs\<close> under
  the executable/mathematical correspondence), so the env stage must compute it
  explicitly here before the assign stage writes the return value.
\<close>

definition base_dg_spec_st_for_lifted ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (vname list \<Rightarrow> exp list \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('a exec_dg_st lifted, 'g::bounded_semilattice_sup_bot) dg_spec"
where
  "base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st = (|
    dgs_skip       = (\<lambda>d g. (g, transfer_lift is_bot_pred (tf_st EA_Nop) d)),
    dgs_assign     = (\<lambda>x e d g. (g, transfer_lift is_bot_pred (tf_st (EA_Assign x e)) d)),
    dgs_special    = (\<lambda>sc x d g. (g, transfer_lift is_bot_pred (tf_st (EA_Special sc x)) d)),
    dgs_branch     = (\<lambda>b pol d g. (g, transfer_lift is_bot_pred
      (tf_st (if pol then EA_Assume b else EA_AssumeNot b)) d)),
    dgs_body       = (\<lambda>p d g. (g, transfer_lift is_bot_pred (tf_st EA_Nop) d)),
    dgs_return     = (\<lambda>e p d g. (g, transfer_lift is_bot_pred (tf_st (EA_Ret e p)) d)),
    dgs_enter      = (\<lambda>xs es d g. (g, transfer_lift is_bot_pred (enter_st xs es) d)),
    dgs_event      = (\<lambda>ev d g. (g, case ev of Check_Event bc \<Rightarrow>
                                      transfer_lift is_bot_pred (tf_st (EA_Check bc)) d)),
    dgs_caller_cont    = (\<lambda>ci dc g. dc),
    dgs_combine_env    = (\<lambda>ci dc de g. (g, case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
                                            (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))),
    dgs_combine_assign = (\<lambda>ci de g merged.
      (g, transfer_lift2 is_bot_pred
            (\<lambda>env0 de0. combine_assign_resolved_q gs (ci_dst ci)
                (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
            (snd merged) de))
  |)"

subsection \<open>Basic equations\<close>

lemma dg_spec_step_base_st_for_lifted:
  "dg_spec_step (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) a d g =
     (g, transfer_lift is_bot_pred (tf_st a) d)"
  unfolding base_dg_spec_st_for_lifted_def
  by (cases a) simp_all

lemma dgs_enter_base_st_for_lifted:
  "dgs_enter (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) xs es d g =
     (g, transfer_lift is_bot_pred (enter_st xs es) d)"
  unfolding base_dg_spec_st_for_lifted_def by simp

text \<open>The caller half of \<open>enter\<close> is the identity here for the same reason as in the
  abstract Base record: the carrier relates no two locations, so a call has
  nothing in it to invalidate.\<close>

lemma dgs_caller_cont_base_st_for_lifted [simp]:
  "dgs_caller_cont (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) ci dc g = dc"
  unfolding base_dg_spec_st_for_lifted_def by simp

lemma dgs_combine_base_st_for_lifted:
  "dgs_combine (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) ci dc de g =
     (g, transfer_lift2 is_bot_pred
           (\<lambda>env0 de0. combine_assign_resolved_q gs (ci_dst ci)
               (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
           (case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
              (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))
           de)"
  unfolding dgs_combine_def base_dg_spec_st_for_lifted_def by simp

subsection \<open>Packaging correspondence\<close>

text \<open>
  Whole-record commute: an executable dispatcher and enter function that
  agree with their mathematical counterparts under \<^const>\<open>fun_of_exec_dg_st_for\<close>
  make the entire \<^const>\<open>base_dg_spec_st_for_lifted\<close> record agree with
  \<^const>\<open>base_dg_spec_for_lifted\<close>, proved once here from
  \<^theory>\<open>Voblint_Core.DG_Base\<close>'s generic \<open>transfer_lift_commute\<close>/
  \<open>transfer_lift2_commute\<close> -- no per-domain packaging proof is needed, only
  the per-domain primitive commute facts these theorems take as hypotheses.
\<close>

theorem base_dg_spec_st_for_lifted_dg_spec_step_commute:
  assumes commute: "\<And>a s. fun_of_exec_dg_st_for gs (tf_st a s) = apply_tf tf a (fun_of_exec_dg_st_for gs s)"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
           (dg_spec_step (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) a d g) =
         dg_spec_step (base_dg_spec_for_lifted gs is_bot_state tf) a
           (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  unfolding dg_spec_step_base_st_for_lifted dg_spec_step_base_for_lifted map_prod_def
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def commute exact)

theorem base_dg_spec_st_for_lifted_dgs_enter_commute:
  assumes commute: "\<And>xs es s. fun_of_exec_dg_st_for gs (enter_st xs es s) =
                       enter\<^sup># tf xs es (fun_of_exec_dg_st_for gs s)"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
           (dgs_enter (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) xs es d g) =
         dgs_enter (base_dg_spec_for_lifted gs is_bot_state tf) xs es
           (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
  unfolding dgs_enter_base_st_for_lifted dgs_enter_base_for_lifted map_prod_def
  by (cases d) (simp_all add: transfer_lift_def normalize_lift_def commute exact)

text \<open>The caller half of \<open>enter\<close> carries its own correspondence, alongside the
  ones for \<open>dg_spec_step\<close>, \<open>dgs_enter\<close> and \<open>dgs_combine\<close>; a Base-style executable
  spec with a nontrivial continuation discharges this same obligation instead of
  the bridge assuming an identity.\<close>

theorem base_dg_spec_st_for_lifted_dgs_caller_cont_commute:
  "map_lift (fun_of_exec_dg_st_for gs)
     (dgs_caller_cont (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) ci dc g) =
   dgs_caller_cont (base_dg_spec_for_lifted gs is_bot_state tf) ci
     (map_lift (fun_of_exec_dg_st_for gs) dc) (map_lift (fun_of_exec_dg_st_for gs) g)"
  unfolding base_dg_spec_st_for_lifted_def base_dg_spec_for_lifted_def by simp

theorem base_dg_spec_st_for_lifted_dgs_combine_commute:
  assumes exact: "\<And>(s::'a::sound_domain resolved_st_q). is_bot_pred s = is_bot_state (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
           (dgs_combine (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) ci dc de g) =
         dgs_combine (base_dg_spec_for_lifted gs is_bot_state tf) ci
           (map_lift (fun_of_exec_dg_st_for gs) dc) (map_lift (fun_of_exec_dg_st_for gs) de)
           (map_lift (fun_of_exec_dg_st_for gs) g)"
  unfolding dgs_combine_base_st_for_lifted dgs_combine_base_for_lifted map_prod_def
    fun_of_exec_dg_st_for_def
  by (cases dc; cases de)
     (auto simp add: transfer_lift2_def normalize_lift_def exact[unfolded fun_of_exec_dg_st_for_def]
       combine_collect_abs_def fun_of_resolved_st_q_for_def)

subsection \<open>Routed-domain compatibility, independent of any routing context\<close>

text \<open>
  Every current routed instance (Sign, Interval, Int) reproves the same three
  shapes -- \<open>dg_spec_step\<close>/\<open>dgs_enter\<close>/\<open>dgs_combine\<close> commuting under
  \<^const>\<open>fun_of_resolved_st_q_for\<close>, plus \<^locale>\<open>dg_reader_commute_gen\<close> at that
  same reader -- from its own executable/abstract transfer-commute facts,
  citing this theory's packaging theorems verbatim. Nothing in that derivation
  is domain-specific beyond the three primitive commute facts a domain's own
  executable-transfer soundness development already proves (\<open>sign_tf_st_for_commute\<close>,
  \<open>ivl_tf_st_for_commute\<close>, ...): this locale states the derivation once, so a
  domain interprets it instead of restating it. The locale is deliberately free
  of any routing context (\<open>route\<close>, \<open>Seed\<close>, \<open>Global\<close>, a solver): those are
  context-owned and solver-owned respectively, not domain-owned.
\<close>

text \<open>
  \<^locale>\<open>dg_reader_commute_gen\<close>'s instance at the same reader on both sides needs no
  domain fact at all: \<^const>\<open>fun_of_resolved_st_q_for\<close> is already carrier-polymorphic and
  \<open>sup\<close>-homomorphic (\<open>fun_of_resolved_st_q_for_sup\<close>, \<^theory>\<open>Voblint_Exec.Exec_St\<close>), so this
  is a free-standing fact, not part of the \<open>routed_dg_domain_exec\<close> locale below -- keeping it
  outside means citing it never drags in that locale's \<open>is_bot_pred\<close>/transfer obligations.
\<close>

lemma dg_reader_commute_gen_lifted_for:
  "dg_reader_commute_gen
     (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))"
  by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)

locale routed_dg_domain_exec =
  fixes gs :: "vname \<Rightarrow> bool"
    and is_bot_pred :: "'a::sound_domain exec_dg_st \<Rightarrow> bool"
    and tf_st :: "edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "vname list \<Rightarrow> exp list \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and tf :: "'a domain_transfer"
  assumes tf_st_commute:
      "\<And>a s. fun_of_resolved_st_q_for gs (tf_st a s) = apply_tf tf a (fun_of_resolved_st_q_for gs s)"
    and enter_st_commute:
      "\<And>xs es s. fun_of_resolved_st_q_for gs (enter_st xs es s)
                   = enter\<^sup># tf xs es (fun_of_resolved_st_q_for gs s)"
    and is_bot_pred_exact:
      "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
begin

lemma Hstep_lifted_for:
  "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
     (dg_spec_step (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) a d g)
   = dg_spec_step (base_dg_spec_for_lifted gs is_bot_state tf) a
       (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dg_spec_step_commute
        [unfolded fun_of_exec_dg_st_for_def, OF tf_st_commute is_bot_pred_exact])

lemma Henter_lifted_for:
  "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
     (dgs_enter (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) xs es d g)
   = dgs_enter (base_dg_spec_for_lifted gs is_bot_state tf) xs es
       (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_enter_commute
        [unfolded fun_of_exec_dg_st_for_def, OF enter_st_commute is_bot_pred_exact])

lemma Hcomb_lifted_for:
  "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
     (dgs_combine (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) dst dc de g)
   = dgs_combine (base_dg_spec_for_lifted gs is_bot_state tf) dst
       (map_lift (fun_of_resolved_st_q_for gs) dc) (map_lift (fun_of_resolved_st_q_for gs) de)
       (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_combine_commute
        [unfolded fun_of_exec_dg_st_for_def, OF is_bot_pred_exact])

lemma Hcont_lifted_for:
  "map_lift (fun_of_resolved_st_q_for gs)
     (caller_cont (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st) ci dc g)
   = caller_cont (base_dg_spec_for_lifted gs is_bot_state tf) ci
       (map_lift (fun_of_resolved_st_q_for gs) dc) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule base_dg_spec_st_for_lifted_dgs_caller_cont_commute
        [unfolded fun_of_exec_dg_st_for_def])

lemma dg_reader_commute_gen_lifted:
  "dg_reader_commute_gen
     (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))"
  by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)

subsection \<open>A generic exec-level formal-entry route, and its commute to the abstract one\<close>

text \<open>
  \<open>formals_route_lifted\<close>/\<open>formals_route_lifted_gen\<close> (\<^theory>\<open>Voblint_Core.Routed_Context\<close>)
  are already domain-generic at the abstract carrier \<open>'a abs_state lifted\<close> -- the shape
  \<^locale>\<open>routed_context_hetero\<close>'s own \<open>route\<close> parameter needs. The executable equation
  system a solver actually runs needs the same construction at the exec carrier
  \<open>'a exec_dg_st lifted\<close> instead, built from this locale's own \<open>enter_st\<close>/\<open>is_bot_pred\<close>
  rather than the mathematical \<open>enter#\<close>/\<open>tf\<close>: every current EntryState-style routed
  instance (Interval's own \<open>entry_state_route\<close>, \<open>Interval_Ctx_Entry_State_Sound\<close>)
  reproves this exact projection and its commute lemma; stating it here once lets a
  domain interpret it instead of restating it, mirroring how \<open>Hstep_lifted_for\<close> etc.
  already generalize the step/enter/combine commute facts.

  The route is a pure projection of the state it is handed: the routed generator
  enters the callee frame once and routes on that entered state, so entering again
  here would key the seed on a doubly-entered frame.
\<close>

definition entry_exec_route :: "'a exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'a list" where
  "entry_exec_route d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (fun_of_resolved_st_q_for gs
          (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

definition entry_exec_route_gen :: "pp \<Rightarrow> 'a list \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'a list" where
  "entry_exec_route_gen u ctx d ca = entry_exec_route d ca"

lemma entry_exec_route_commute:
  "formals_route_lifted (base_dg_spec_for_lifted gs is_bot_state tf)
     (map_lift (fun_of_resolved_st_q_for gs) s) ca = entry_exec_route s ca"
  by (cases ca; cases s)
     (simp_all add: formals_route_lifted_def entry_exec_route_def
                    formals_context_def fun_of_resolved_st_q_for_def)

lemma entry_exec_route_gen_commute:
  "formals_route_lifted_gen (base_dg_spec_for_lifted gs is_bot_state tf) u ctx
     (map_lift (fun_of_resolved_st_q_for gs) s) ca = entry_exec_route_gen u ctx s ca"
  by (simp add: formals_route_lifted_gen_def entry_exec_route_gen_def entry_exec_route_commute)

end

end

