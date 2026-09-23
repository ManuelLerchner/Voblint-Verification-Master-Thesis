theory Example_Sign_Mixed_Flow
  imports
    "Voblint_Analysis_Sign.Sign_Analyses"
    "Voblint_Exec.Ownership_Split_Exec"
    "Voblint_Framework.Routed_Context_Unit"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>A mixed flow-sensitive analysis, sound end to end for one program\<close>

subsection \<open>The ownership-split Sign specification at the executable carrier\<close>

abbreviation mf_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('x, 'k, unit, sign exec_dg_st, sign exec_dg_st) dg_spec" where
  "mf_spec \<G> \<equiv> ownership_split_dg_spec_st_for \<G> (sign_tf_st_for \<G>) (sign_enter_st_for \<G>)"

definition split_gamma ::
  "(vname \<Rightarrow> bool) \<Rightarrow> sign exec_dg_st \<Rightarrow> sign exec_dg_st \<Rightarrow> store set" where
  "split_gamma \<G> d g = \<lbrakk>fun_of_resolved_st_q_for \<G> (combine_resolved_st_q d g)\<rbrakk>"

lemma combine_restrict_split [simp]:
  "combine_resolved_st_q (restrict_local_resolved_q x) (restrict_global_resolved_q x) = x"
  by (rule resolved_st_q_eqI) (simp split: location.split)

lemma combine_restrict_local_left [simp]:
  "combine_resolved_st_q (restrict_local_resolved_q x) y = combine_resolved_st_q x y"
  by (rule resolved_st_q_eqI) (simp split: location.split)

lemma combine_self_restrict_global [simp]:
  "combine_resolved_st_q x (restrict_global_resolved_q x) = x"
  by (rule resolved_st_q_eqI) (simp split: location.split)

lemma sign_tf_st_sound:
  "edge_collect a \<lbrakk>fun_of_resolved_st_q_for \<G> s\<rbrakk>
     \<subseteq> \<lbrakk>fun_of_resolved_st_q_for \<G> (sign_tf_st_for \<G> a s)\<rbrakk>"
proof (cases "live_resolved_st_q \<G> s")
  case True
  show ?thesis
    unfolding sign_tf_st_for_commute[OF True, unfolded sign_tf.tf_abs_def]
    by (rule sound_transfer_for.step_sound_for[OF sign_tf.is_sound_transfer_for])
next
  case False
  then have "\<lbrakk>fun_of_resolved_st_q_for \<G> s\<rbrakk> = {}"
    by (simp add: live_resolved_st_q_def is_empty_state_gamma_state_empty)
  then show ?thesis by (simp add: edge_collect_empty_set)
qed

lemma dg_spec_wf_mf_spec [intro, simp]: "dg_spec_wf (mf_spec \<G>)"
proof (unfold dg_spec_wf_def, intro conjI allI)
  fix a d key
  show "sp_wf (dg_spec_step (mf_spec \<G>) a (mk_dg_man d key))"
    unfolding dg_spec_step_ownership_split_st_for ownership_split_transfer_st_def
    by (auto simp: ownership_split_transfer_gen_def local_transfer_def intro!: sp_wf_bind)
next
  fix ci d key
  show "sp_wf (enter\<^sup># (mf_spec \<G>) ci (mk_dg_man d key))"
    unfolding dgs_enter_ownership_split_dg_spec_st_for ownership_split_enter_transfer_st_def
    by (auto simp: ownership_split_enter_transfer_gen_def local_enter_transfer_def
        intro!: sp_wf_bind)
next
  fix ci d key ex
  show "sp_wf (dg_spec_combine_transfer (mf_spec \<G>) ci (mk_dg_man d key) ex)"
    unfolding dg_spec_combine_transfer_ownership_split_dg_spec_st_for
      ownership_split_combine_transfer_st_def
    by (auto simp: ownership_split_combine_transfer_gen_def local_combine_transfer_def
        intro!: sp_wf_bind)
qed

theorem sound_dg_spec_core_mf:
  "sound_dg_spec_core (mf_spec \<G>) (split_gamma \<G>) \<G>"
proof (unfold_locales, goal_cases)
  case 1 show ?case by (rule dg_spec_wf_mf_spec)
next
  case (2 d d' g g')
  then show ?case
    unfolding split_gamma_def fun_of_resolved_st_q_for_combine
    by (intro gamma_state_mono combine_env_mono fun_of_resolved_st_q_for_mono)
next
  case (3 a \<tau> src gk)
  show ?case
    unfolding dg_spec_edge_program_def dg_spec_step_ownership_split_st_for
      ownership_split_transfer_st_def split_gamma_def
    by (simp add: sign_tf_st_sound del: fun_of_resolved_st_q_for_combine)
next
  case (4 s dc \<tau> gk t de ci)
  let ?G = "globs (\<tau> (Inr gk))"
  let ?x = "combine_resolved_st_q dc ?G" and ?y = "combine_resolved_st_q de ?G"
  have xy: "combine_resolved_st_q ?x ?y = ?x"
    by (rule resolved_st_q_eqI) (simp split: location.split)
  have "combine_collect \<G> (ci_dst ci) s t
      \<in> \<lbrakk>combine\<^sup># \<G> (ci_dst ci) (fun_of_resolved_st_q_for \<G> ?x) (fun_of_resolved_st_q_for \<G> ?y)\<rbrakk>"
    using 4 unfolding split_gamma_def by (intro combine_collect_sound)
  also have "\<dots> = \<lbrakk>fun_of_resolved_st_q_for \<G>
      (combine_assign_resolved_q \<G> (ci_dst ci) (lookup_resolved_st_q ?y (location_of \<G> ret_var))
         ?x)\<rbrakk>"
    by (subst (2) xy[symmetric]) (simp only: fun_of_resolved_st_q_for_combine_assign)
  finally show ?case
    unfolding dg_spec_combine_transfer_ownership_split_dg_spec_st_for
      ownership_split_combine_transfer_st_def split_gamma_def
    by (simp add: ownership_split_combine_transfer_gen_def local_combine_transfer_def
        mk_dg_man_def dg_read_global_def dg_sideg_def sp_bind_assoc
        del: fun_of_resolved_st_q_for_combine combine_restrict_local_left)
qed

subsection \<open>The call boundary\<close>

lemma bind_formals_other:
  "y \<notin> set xs \<Longrightarrow> bind_formals xs vs s y = s y"
proof (induction xs arbitrary: vs s)
  case (Cons x xs)
  then show ?case by (cases vs) auto
qed simp

lemma split_gamma_bot:
  assumes "\<not> \<G> x"
  shows "split_gamma \<G> bot g = {}"
  unfolding split_gamma_def
proof (rule is_empty_state_gamma_state_empty, rule is_empty_stateI)
  show "is_empty (fun_of_resolved_st_q_for \<G> (combine_resolved_st_q bot g) x)"
    using assms by (simp add: combine_env_def is_bottom_sign_def bot_sign_def)
qed

lemma split_gamma_restrict_local_combine:
  "split_gamma \<G> (restrict_local_resolved_q (combine_resolved_st_q d G)) G = split_gamma \<G> d G"
  unfolding split_gamma_def
  by (rule arg_cong[where f = gamma_state], rule arg_cong[where f = "fun_of_resolved_st_q_for \<G>"],
      rule resolved_st_q_eqI) (simp split: location.split)

lemma split_gamma_enter:
  assumes "\<forall>f \<in> set (ci_formals ci). \<not> \<G> f"
  shows "split_gamma \<G>
           (restrict_local_resolved_q (sign_enter_st_for \<G> ci (combine_resolved_st_q d G))) G
         = \<lbrakk>fun_of_resolved_st_q_for \<G> (sign_enter_st_for \<G> ci (combine_resolved_st_q d G))\<rbrakk>"
  unfolding split_gamma_def
proof (rule arg_cong[where f = gamma_state], rule ext)
  fix x
  show "fun_of_resolved_st_q_for \<G> (combine_resolved_st_q
            (restrict_local_resolved_q (sign_enter_st_for \<G> ci (combine_resolved_st_q d G))) G) x
        = fun_of_resolved_st_q_for \<G> (sign_enter_st_for \<G> ci (combine_resolved_st_q d G)) x"
  proof (cases "\<G> x")
    case True
    then have "x \<notin> set (ci_formals ci)" using assms by blast
    with True show ?thesis
      by (simp add: bind_formals_other combine_env_def enter_frame_def)
  qed (simp add: combine_env_def)
qed

lemma sign_call_enter_sound:
  assumes "s \<in> \<lbrakk>fun_of_resolved_st_q_for \<G> D\<rbrakk>"
  shows "call_enter \<G> (CallEdge dst pars args) s
           \<in> \<lbrakk>fun_of_resolved_st_q_for \<G>
                (sign_enter_st_for \<G> (call_info_of (CallEdge dst pars args) p) D)\<rbrakk>"
  unfolding sign_enter_st_for_commute
  using sound_transfer_for.tf_sound_enter_entry_for[OF sign_tf.is_sound_transfer_for assms,
      of "call_info_of (CallEdge dst pars args) p"]
  by (simp add: call_enter_CallEdge)

subsection \<open>The program and its equation system\<close>

definition mf_program :: imp_prog where
  "mf_program = program { global Gx;
     fun set() { Gx = 1; }
     fun get() { return Gx; }
     fun main() { x = 1; set(); y = get(); } }"

abbreviation mf_gs :: "vname \<Rightarrow> bool" where
  "mf_gs \<equiv> declared_global mf_program"

definition mf_cfg :: cfg where
  "mf_cfg = compile_prog (prog_table mf_program) (prog_procs mf_program)"

definition mf_eqs ::
  "(pp \<times> unit, (unit, unit) routed_gk, (sign exec_dg_st, sign exec_dg_st) dg_state) eqsT" where
  "mf_eqs =
     routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. Analysis_Global ())
       route_unit
       (\<lambda>ctx' src a. dg_spec_edge_program (mf_spec mf_gs) a src (\<lambda>_. Analysis_Global ()))
       (routed_call_program (mf_spec mf_gs) (Analysis_Global ()) Activation_Seed
          (static_resolve mf_cfg) (\<lambda>d. d = bot))
       (routed_entry_seed_programs Activation_Seed)
       mf_cfg bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

definition mf_sol ::
  "(pp \<times> unit) set \<times>
   (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "mf_sol = TD_side_always_join_Interp_solve mf_eqs (cfg_exit mf_cfg, ())"

lemma mf_terminates_c:
  "TD_side_always_join_Interp_solve_c mf_eqs (cfg_exit mf_cfg, ()) \<noteq> None"
  unfolding mf_eqs_def mf_cfg_def mf_program_def by eval

abbreviation mf_G :: "sign exec_dg_st" where
  "mf_G \<equiv> globs (snd mf_sol (Inr (Analysis_Global ())))"

definition mf_reader :: "pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> sign exec_dg_st lifted" where
  "mf_reader k = (case k of
     Inl vc \<Rightarrow> if vc \<in> fst mf_sol
       then Lifted (combine_resolved_st_q (locals (snd mf_sol (Inl vc))) mf_G) else Bot
   | Inr _ \<Rightarrow> Bot)"

abbreviation mf_gammaM :: "sign exec_dg_st lifted \<Rightarrow> store set" where
  "mf_gammaM m \<equiv> \<lbrakk>map_lift (fun_of_resolved_st_q_for mf_gs) m\<rbrakk>\<^sub>\<bottom>"

lemma mf_snapshot_raw:
  "(let sol = mf_sol;
        G = globs (snd sol (Inr (Analysis_Global ())));
        at7 = combine_resolved_st_q (locals (snd sol (Inl (Statement 7, ())))) G
    in TD_side_always_join_Interp_solve_c mf_eqs (cfg_exit mf_cfg, ()) \<noteq> None
     \<and> (cfg_entry mf_cfg, ()) \<in> fst sol
     \<and> \<not> mf_gs ret_var
     \<and> (\<forall>(u, ctx) \<in> fst sol. \<forall>(u', a, v) \<in> intra mf_cfg. u = u' \<longrightarrow> (v, ctx) \<in> fst sol)
     \<and> (\<forall>(u, ctx) \<in> fst sol. \<forall>(u', ca, ce, cont) \<in> calls mf_cfg.
          u = u' \<longrightarrow> (cont, ctx) \<in> fst sol \<and> (ce, ctx) \<in> fst sol)
     \<and> (\<forall>(u, ca, ce, cont) \<in> calls mf_cfg. \<forall>f \<in> set (ce_formals ca). \<not> mf_gs f)
     \<and> (Statement 7, ()) \<in> fst sol
     \<and> fun_of_resolved_st_q_for mf_gs at7 (STR ''x'') = SPos
     \<and> fun_of_resolved_st_q_for mf_gs at7 (STR ''y'') = SNonNeg
     \<and> fun_of_resolved_st_q_for mf_gs G (STR ''Gx'') = SNonNeg)"
  unfolding mf_sol_def mf_eqs_def mf_cfg_def mf_program_def by eval

lemma mf_snapshot:
  "(cfg_entry mf_cfg, ()) \<in> fst mf_sol
   \<and> \<not> mf_gs ret_var
   \<and> (\<forall>(u, ctx) \<in> fst mf_sol. \<forall>(u', a, v) \<in> intra mf_cfg. u = u' \<longrightarrow> (v, ctx) \<in> fst mf_sol)
   \<and> (\<forall>(u, ctx) \<in> fst mf_sol. \<forall>(u', ca, ce, cont) \<in> calls mf_cfg.
        u = u' \<longrightarrow> (cont, ctx) \<in> fst mf_sol \<and> (ce, ctx) \<in> fst mf_sol)
   \<and> (\<forall>(u, ca, ce, cont) \<in> calls mf_cfg. \<forall>f \<in> set (ce_formals ca). \<not> mf_gs f)
   \<and> (Statement 7, ()) \<in> fst mf_sol
   \<and> fun_of_resolved_st_q_for mf_gs
       (combine_resolved_st_q (locals (snd mf_sol (Inl (Statement 7, ())))) mf_G) (STR ''x'') = SPos
   \<and> fun_of_resolved_st_q_for mf_gs
       (combine_resolved_st_q (locals (snd mf_sol (Inl (Statement 7, ())))) mf_G) (STR ''y'')
       = SNonNeg
   \<and> fun_of_resolved_st_q_for mf_gs mf_G (STR ''Gx'') = SNonNeg"
  using mf_snapshot_raw unfolding Let_def by fastforce

lemma mf_pp: "part_post_solution mf_eqs (cfg_exit mf_cfg, ()) (snd mf_sol) (fst mf_sol)"
  using TD_side_always_join_Interp.part_post_solution_of_solve_c[OF mf_terminates_c]
  unfolding mf_sol_def by simp

interpretation mf_routed: routed_context_base_hetero
  "mf_spec mf_gs" "split_gamma mf_gs" mf_gs mf_cfg "Analysis_Global ()"
  route_unit bot cinit_sign_st "restrict_global_resolved_q cinit_sign_st"
  "snd mf_sol" "fst mf_sol" "(cfg_exit mf_cfg, ())" mf_reader Activation_Seed
  "static_resolve mf_cfg" "\<lambda>d. d = bot" mf_gammaM "call_context_rel_of_fun enterc_unit"
proof (rule routed_context_base_hetero.intro
    [OF dg_ctx_activation_base.intro[OF sound_dg_spec_core_mf]],
  unfold_locales, goal_cases CmbWf ExtraWf FinE PP SgCov SgUncov Fwd FinC CallsUnique
    SeedKey IsBotBot IsBotSound ResolveSound EnterCover EnterTotal CombFwd)
  case CmbWf show ?case by (rule sp_wf_routed_call_program[OF dg_spec_wf_mf_spec])
next
  case ExtraWf then show ?case by (rule sp_wf_routed_entry_seed_programs)
next
  case FinE show ?case unfolding mf_cfg_def by (simp add: compile_prog_finite)
next
  case PP show ?case by (rule post_bounded_of_part_post_solution[OF mf_pp[unfolded mf_eqs_def]])
next
  case (SgCov v ctx)
  thus ?case by (simp add: mf_reader_def split_gamma_def del: fun_of_resolved_st_q_for_combine)
next
  case (SgUncov v ctx)
  thus ?case by (simp add: mf_reader_def)
next
  case (Fwd u a v ctx)
  then show ?case using mf_snapshot by fastforce
next
  case FinC show ?case unfolding mf_cfg_def by (simp add: compile_prog_finite)
next
  case CallsUnique show ?case
    unfolding mf_cfg_def calls_source_unique_def using compile_prog_calls_source_unique
    by blast
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv)
  then show ?case using split_gamma_bot mf_snapshot by blast
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case unfolding mf_cfg_def by (simp add: compile_prog_finite)
next
  case (EnterCover u ctx dst pars args p cont s ctx')
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?d = "locals (snd mf_sol (Inl (u, ctx)))"
  let ?D = "combine_resolved_st_q ?d mf_G"
  let ?E = "sign_enter_st_for mf_gs ?ci ?D"
  let ?pairs = "map (\<lambda>(cont, entry). (restrict_local_resolved_q cont, restrict_local_resolved_q entry))
                  [(?D, ?E)]"
  have Rr: "\<exists>pub. enter_runs (enter\<^sup># (mf_spec mf_gs) ?ci)
      (mk_dg_man ?d (\<lambda>_. Analysis_Global ())) (snd mf_sol) ?pairs pub"
    unfolding dgs_enter_ownership_split_dg_spec_st_for ownership_split_enter_transfer_st_def
    by (rule exI, rule enter_runs_ownership_split_enter_transfer_gen)
       (rule enter_runs_local_enter_transfer_mk_dg_man)
  have Dd: "\<exists>deps. enter_deps (enter\<^sup># (mf_spec mf_gs) ?ci)
      (mk_dg_man ?d (\<lambda>_. Analysis_Global ())) (snd mf_sol) ?pairs deps"
    unfolding dgs_enter_ownership_split_dg_spec_st_for ownership_split_enter_transfer_st_def
    by (rule exI, rule enter_deps_ownership_split_enter_transfer_gen)
       (rule enter_deps_local_enter_transfer_mk_dg_man)
  have ccov: "s \<in> split_gamma mf_gs (restrict_local_resolved_q ?D) mf_G"
    using EnterCover(3) by (simp only: split_gamma_restrict_local_combine)
  have formals: "\<forall>f \<in> set (ci_formals ?ci). \<not> mf_gs f"
    using mf_snapshot EnterCover(2) by fastforce
  have ecov: "call_enter mf_gs (CallEdge dst pars args) s
      \<in> split_gamma mf_gs (restrict_local_resolved_q ?E) mf_G"
    unfolding split_gamma_enter[OF formals]
    by (rule sign_call_enter_sound) (use EnterCover(3) in \<open>simp only: split_gamma_def\<close>)
  have fwd: "(FunctionEntry p, ctx') \<in> fst mf_sol"
    using mf_snapshot EnterCover(1,2) by fastforce
  show ?case using Rr Dd ccov ecov fwd by auto
next
  case (EnterTotal u ctx dst pars args p cont s)
  show ?case by simp
next
  case (CombFwd cl c1 dst pars args p cont)
  then show ?case using mf_snapshot by fastforce
qed

subsection \<open>Soundness against the concrete trace semantics\<close>

lemma mf_cinit_sound:
  "cinit_stores mf_gs \<subseteq> split_gamma mf_gs cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"
  using sign_cinit_gamma[of mf_gs]
  by (simp add: split_gamma_def fun_of_exec_dg_st_for_def del: fun_of_resolved_st_q_for_combine)

theorem mf_activation_collect_sound:
  "activation_collect mf_gs (call_context_rel_of_fun enterc_unit) () mf_cfg (cinit_stores mf_gs) v ()
     \<subseteq> mf_gammaM (mf_reader (Inl (v, ())))"
  using mf_snapshot
  by (intro mf_routed.activation_collect_dg_sound mf_cinit_sound) blast

theorem mf_ltr_collect_sound:
  "\<C>\<^bsub>mf_gs,mf_cfg,cinit_stores mf_gs\<^esub> v
     \<subseteq> mf_gammaM (mf_reader (Inl (v, ())))"
  using mf_activation_collect_sound unfolding activation_collect_unit_eq_ltr_collect .

corollary mf_ltr_collect_solved:
  assumes "(v, ()) \<in> fst mf_sol"
  shows "\<C>\<^bsub>mf_gs,mf_cfg,cinit_stores mf_gs\<^esub> v
           \<subseteq> split_gamma mf_gs (locals (snd mf_sol (Inl (v, ())))) mf_G"
  using mf_ltr_collect_sound[of v] assms
  by (simp add: mf_reader_def split_gamma_def del: fun_of_resolved_st_q_for_combine)

corollary mf_after_calls:
  assumes "s \<in> \<C>\<^bsub>mf_gs,mf_cfg,cinit_stores mf_gs\<^esub> (Statement 7)"
  shows "0 < s (STR ''x'') \<and> 0 \<le> s (STR ''y'')"
proof -
  have "s \<in> split_gamma mf_gs (locals (snd mf_sol (Inl (Statement 7, ())))) mf_G"
    using mf_ltr_collect_solved mf_snapshot assms by blast
  then have mem: "s \<in> \<lbrakk>fun_of_resolved_st_q_for mf_gs
      (combine_resolved_st_q (locals (snd mf_sol (Inl (Statement 7, ())))) mf_G)\<rbrakk>"
    unfolding split_gamma_def .
  have "s (STR ''x'') \<in> \<gamma> SPos"
    using gamma_stateD[OF mem, of "STR ''x''"] mf_snapshot by simp
  moreover have "s (STR ''y'') \<in> \<gamma> SNonNeg"
    using gamma_stateD[OF mem, of "STR ''y''"] mf_snapshot by simp
  ultimately show ?thesis by simp
qed

subsection \<open>Source runs\<close>

lemma mf_wf: "wf_compile_input mf_gs (prog_table mf_program) (prog_procs mf_program)"
  by (auto simp: wf_compile_input_simps mf_program_def split: if_splits)

theorem mf_source_sound:
  assumes init: "s0 \<in> cinit_stores mf_gs"
    and run: "mf_gs, prog_table mf_program \<turnstile> (main_body (prog_table mf_program), s0, [])
                \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk. prog_table mf_program, mf_cfg \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> mf_gammaM (mf_reader (Inl (v, ())))"
proof -
  obtain v stk t c
    where sim: "prog_table mf_program, mf_cfg \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and act: "s \<in> activation_collect mf_gs (call_context_rel_of_fun enterc_unit) ()
                     mf_cfg (cinit_stores mf_gs) v c"
    using source_store_in_activation_collect_of_fun[OF mf_wf init run,
        of enterc_unit "()"]
    unfolding mf_cfg_def by blast
  moreover have "c = ()" by simp
  ultimately show ?thesis using mf_activation_collect_sound[of v] by blast
qed

end
