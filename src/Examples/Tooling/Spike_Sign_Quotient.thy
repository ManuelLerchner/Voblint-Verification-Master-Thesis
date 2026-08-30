theory Spike_Sign_Quotient
  imports "Voblint_Analysis.Sign_Ctx_None_Sound"
begin

section \<open>Can the routed spine be instantiated at the executable carrier directly?\<close>

text \<open>
  Today the framework is instantiated at \<open>sign abs_state lifted\<close>, the solver runs on
  \<open>sign exec_dg_st lifted\<close>, and \<open>Exec_DG_Bridge\<close> transports the solved system from
  the second carrier to the first. This spike instantiates \<open>sound_dg_spec\<close>,
  \<open>dg_ctx_activation_base\<close> and \<open>unit_routed_context\<close> at the executable carrier,
  with the concretization going through the readback, and feeds them the solver's
  own post-solution. If that goes through, the transport has nothing left to move.
\<close>

subsection \<open>Sign, routed at the executable carrier\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list"
  assumes solves: "sctx_terminates gs is_bot_pred Pi ps"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps), ()) \<in> fst (sctx_sol gs is_bot_pred Pi ps)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps)
                   \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (sctx_sol gs is_bot_pred Pi ps)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sctx_sol gs is_bot_pred Pi ps)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol gs is_bot_pred Pi ps)"
begin

interpretation sign_unit: routed_domain_exec
  gs is_bot_pred "sign_tf_st_for gs" "sign_enter_st_for gs" "sign_tf_for gs"
  Global Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales
     (rule sign_tf_st_for_commute, rule sign_enter_st_for_commute, rule exact,
      simp, simp, simp add: static_resolve_def)

lemma sound_exec: "sound_dg_spec (sctx_spec gs is_bot_pred) sign_unit.gamma_exec gs"
  unfolding sctx_spec_def
  by (rule sign_unit.sound_dg_spec_st)
     (rule base_dg_spec_sound[OF sign_is_sound_transfer_for is_bot_state_gamma_state_empty])

text \<open>The solver's own post-solution, for the unbuffered generator at the executable spec:
  \<open>routed_domain_exec.pp_st\<close>, the half of \<open>pp_abs\<close> that does not transport.\<close>

lemma pp_st:
  "part_post_solution
     (side_cfg_T_eff_keyed_seed_dg intra_predecessor_addr_list (\<lambda>_. Global) route_unit
        (routed_cmb_g (sctx_spec gs is_bot_pred) Global Seed (static_resolve (compile_prog Pi ps)))
        (routed_extra_g Seed Global)
        (compile_prog Pi ps) (sctx_spec gs is_bot_pred) Bot (Lifted cinit_sign_st) Bot)
     (cfg_exit (compile_prog Pi ps), ())
     (snd (sctx_sol gs is_bot_pred Pi ps)) (fst (sctx_sol gs is_bot_pred Pi ps))"
  using sctx_pp_st[OF solves exact]
  unfolding sctx_eqs_def sctx_spec_def by (rule sign_unit.pp_st)

definition sg_st :: "pp \<times> unit + gk \<Rightarrow> sign exec_dg_st lifted" where
  "sg_st k =
     (case k of
        Inl (v, ctx) \<Rightarrow>
          (if (v, ctx) \<in> fst (sctx_sol gs is_bot_pred Pi ps)
           then locals (snd (sctx_sol gs is_bot_pred Pi ps) (Inl (v, ctx)))
           else Bot)
      | Inr _ \<Rightarrow> Bot)"

interpretation q_base: sound_dg_spec "sctx_spec gs is_bot_pred" sign_unit.gamma_exec gs
  by (rule sound_exec)

interpretation q: unit_routed_context "sctx_spec gs is_bot_pred" sign_unit.gamma_exec gs
    "compile_prog Pi ps" Global Bot "Lifted cinit_sign_st" Bot
    "snd (sctx_sol gs is_bot_pred Pi ps)" "fst (sctx_sol gs is_bot_pred Pi ps)"
    "(cfg_exit (compile_prog Pi ps), ())" sg_st Seed
    "\<lambda>m. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) m)"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey CallFwd CombFwd EnterAgree)
  case FinE show ?case using compile_prog_finite by blast
next
  case PP show ?case by (rule pp_st)
next
  case (SgCov v ctx) then show ?case
    by (simp add: sg_st_def sign_unit.gamma_exec_def gamma_dg_base_def)
next
  case (SgUncov v ctx) then show ?case by (simp add: sg_st_def)
next
  case (Fwd u a v ctx) then show ?case by (rule fwd_ok)
next
  case FinC show ?case using compile_prog_finite by blast
next
  case (SeedKey p ctx) show ?case by simp
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case using CallFwd(1,2) call_fwd_ok unfolding route_unit_def by blast
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) comb_fwd_ok by blast
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
qed

text \<open>The obligations the activation backbone consumes, now stated over the solver's own
  table: EDGE from the post-solution, CALL and COMB from the routed layer.\<close>

lemmas spike_edge = q.dg_ctx_act_edge
lemmas spike_call = q.routed_context_call
lemmas spike_comb = q.routed_context_comb

end

end
