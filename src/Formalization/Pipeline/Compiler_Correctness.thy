theory Compiler_Correctness
  imports
    "Voblint_CFG.Located_Reaches"
    "Voblint_Analysis.Analysis_Sound"
    "Voblint_Analysis.Sign_Side_Soundness"
begin

subsection \<open>Compiler simulation contract\<close>

locale compiled_source_simulation =
  fixes \<Pi> :: proc_table and ps :: "pname list" and main :: IMP2_Proc.com
    and g :: cfg
    and match :: "(IMP2_Proc.com \<times> store \<times> frame list) \<Rightarrow> cconf \<Rightarrow> bool"
  assumes g_def: "g = compile_prog \<Pi> ps main"
      and wf: "wf_compile_input \<Pi> ps main"
      and initial_match:
        "\<And>s. match (main, s, []) (cfg_entry g, s, [])"
      and step_match:
        "\<And>src src' cf.
           match src cf \<Longrightarrow>
           pstep \<Pi> src src' \<Longrightarrow>
           \<exists>cf'. star (cstep g) cf cf' \<and> match src' cf'"
begin

lemma source_steps_match:
  assumes "match src cf"
      and "star (pstep \<Pi>) src src'"
  shows "\<exists>cf'. star (cstep g) cf cf' \<and> match src' cf'"
proof -
  from assms(2) show ?thesis
    using assms(1)
  proof (induction arbitrary: cf rule: star.induct)
    case (refl src)
    show ?case
    proof (rule exI[where x = cf], intro conjI)
      show "star (cstep g) cf cf"
        by (rule star.refl)
      show "match src cf"
        by (rule refl.prems)
    qed
  next
    case (step src mid dst)
    obtain cf_mid where run1: "star (cstep g) cf cf_mid"
        and match_mid: "match mid cf_mid"
      using step_match[OF step.prems step.hyps(1)] by blast
    obtain cf_dst where run2: "star (cstep g) cf_mid cf_dst"
        and match_dst: "match dst cf_dst"
      using step.IH[OF match_mid] by blast
    have "star (cstep g) cf cf_dst"
      using run1 run2 by (rule star_trans)
    then show ?case
      using match_dst by blast
  qed
qed

theorem source_reaches_cfg_collect:
  assumes run: "psteps \<Pi> (main, s, []) src'"
  shows "\<exists>v t stk.
     match src' (v, t, stk) \<and>
     t \<in> cfg_collect g {s} v \<and>
     cfg_reaches g (cfg_entry g) v"
proof -
  have initial: "match (main, s, []) (cfg_entry g, s, [])"
    by (rule initial_match)
  obtain cf' where cfg_run:
      "star (cstep g) (cfg_entry g, s, []) cf'"
      and matched: "match src' cf'"
    using source_steps_match[OF initial run] by blast
  have sound_initial: "located_sound g {s} (cfg_entry g, s, [])"
    by (rule located_sound_entry) simp
  have sound_final: "located_sound g {s} cf'"
    by (rule csteps_preserve_located_sound[OF sound_initial cfg_run])
  obtain v t stk where cf': "cf' = (v, t, stk)"
    by (cases cf') auto
  have reachable: "cfg_reaches g (cfg_entry g) v"
    using csteps_imp_cfg_reaches[OF cfg_run]
    unfolding cf' by simp
  show ?thesis
    using matched sound_final reachable
    unfolding cf' located_sound_def
    by blast
qed

corollary source_reaches_post_fixpoint:
  fixes env :: "pp \<Rightarrow> 'a::sound_domain abs_state"
    and s0 :: "'a abs_state"
  assumes stf: "sound_transfer tf"
      and run: "psteps \<Pi> (main, s, []) src'"
      and post: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
  shows "\<exists>v t stk.
     match src' (v, t, stk) \<and> t \<in> \<lbrakk>env v\<rbrakk>"
proof -
  interpret sound_transfer tf
    by (rule stf)
  obtain v t stk where matched: "match src' (v, t, stk)"
      and collected: "t \<in> cfg_collect g {s} v"
    using source_reaches_cfg_collect[OF run] by blast
  have fin: "finite (edges g)"
    using compile_prog_finite g_def by blast
  have finC: "finite (combines g)"
    using compile_prog_finite g_def by blast
  have initial: "{s} \<le> \<lbrakk>s0\<rbrakk>"
    using init by simp
  have "cfg_collect g {s} v \<le> \<lbrakk>env v\<rbrakk>"
    by (meson fin finC initial post_fixpoint_sound)
  then have "t \<in> \<lbrakk>env v\<rbrakk>"
    using collected by blast
  then show ?thesis
    using matched by blast
qed

end


subsection \<open>Arbitrary-query side-solver result\<close>

theorem side_collect_sound_at_pruned_eff:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set"
    and etf :: "('g, 'a) effectful_domain_transfer"
    and gseed :: 'g and v :: pp
  assumes se: "sound_effectful_transfer etf"
      and pp: "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed)
                 v \<sigma> vars"
      and fin: "finite (edges g)"
      and finC: "finite (combines g)"
      and entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
      and cone: "cone_compatible_etf etf"
      and inr: "inr_slot_locals_bot \<sigma>"
  shows "cfg_collect g S v \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer etf
    by (rule se)
  define pg where "pg = prune_to g v"
  have fin_pg: "finite (edges pg)"
    using fin by (auto simp: pg_def)
  have finC_pg: "finite (combines pg)"
    using finC by (auto simp: pg_def)
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges pg \<Longrightarrow>
       etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  proof -
    fix u a w
    assume edge_pg: "(u, a, w) \<in> edges pg"
    have edge_g: "(u, a, w) \<in> edges g"
      using edge_pg by (simp add: pg_def)
    have reaches: "cfg_reaches g w v"
      using edge_pg by (simp add: pg_def cone_def)
    have "w \<in> vars"
      by (rule side_cone_in_vars_eff_cone[OF pp fin finC cone reaches])
    then show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
      by (rule etf_combined_le_eff[OF pp _ edge_g fin])
  qed
  have combine_le:
    "\<And>call ex ret dst rex.
        (call, ex, ret, dst, rex) \<in> combines pg \<Longrightarrow>
        etf_full (etf_combine etf call ex) \<sigma> \<le> side_env \<sigma> ret"
  proof -
    fix call ex ret dst rex
    assume combine_pg: "(call, ex, ret, dst, rex) \<in> combines pg"
    have combine_g: "(call, ex, ret, dst, rex) \<in> combines g"
      using combine_pg by (simp add: pg_def)
    have reaches: "cfg_reaches g ret v"
      using combine_pg by (simp add: pg_def cone_def)
    have "ret \<in> vars"
      by (rule side_cone_in_vars_eff_cone[OF pp fin finC cone reaches])
    then show "etf_full (etf_combine etf call ex) \<sigma> \<le> side_env \<sigma> ret"
      by (rule etf_combine_combined_le_eff[OF pp _ combine_g finC])
  qed
  have entry_pg: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry pg)\<rbrakk>"
    using entry by (simp add: pg_def)
  have collect_pg: "cfg_collect pg S v \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    by (rule se.post_fixpoint_sound_at_eff[OF inr entry_pg step_le combine_le order_refl])
  have frame: "cfg_collect g S v \<subseteq> cfg_collect pg S v"
    using cfg_collect_prune_to_query[of g S v] by (simp add: pg_def)
  show ?thesis
    using frame collect_pg by blast
qed

theorem side_analyse_eff_collect_sound_at_pruned:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and S :: "store set"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g and v :: pp
  defines "g \<equiv> compile_prog \<Pi> ps main"
  assumes se: "sound_effectful_transfer etf"
      and tfm: "threefold_mono (side_cfg_T_eff g etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and dom: "side_cfg_solve_dom_eff g etf bot s0 gseed v"
      and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
      and entry_reaches: "cfg_reaches g (cfg_entry g) v"
  shows "cfg_collect g S v
         \<le> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed v\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer etf
    by (rule se)
  interpret ip: td_cfg_side_solver_eff g etf bot s0 gseed
    using threefold_monoD_eq[OF tfm]
      threefold_monoD_sides[OF tfm]
      threefold_monoD_deps[OF tfm]
    by unfold_locales
  define \<sigma> where "\<sigma> = ip.nu_at v"
  have fin: "finite (edges g)"
    unfolding g_def using compile_prog_finite by simp
  have finC: "finite (combines g)"
    unfolding g_def using compile_prog_finite by simp
  have pp: "part_post_solution (side_cfg_T_eff g etf bot s0 gseed)
      v \<sigma> (ip.stabl_at v)"
    using ip.part_post_at_cfg[OF dom] unfolding \<sigma>_def by simp
  have entry_in: "cfg_entry g \<in> ip.stabl_at v"
    by (rule side_cone_in_vars_eff_cone[OF pp fin finC cone entry_reaches])
  have entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp entry_in])
  have entry_cov: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using S_sound gamma_state_mono[OF entry_le] by blast
  have least: "least_part_post_solution (side_cfg_T_eff g etf bot s0 gseed)
      v \<sigma> (ip.stabl_at v)"
    by (metis (mono_tags, opaque_lifting) dom ip.cfg_pkg_eff_eq
        ip.least_part_post_at_cfg \<sigma>_def)
  have inr: "inr_slot_locals_bot \<sigma>"
    by (metis cone_compatible_etf_comb_inr
        cone_compatible_etf_comb_static
        cone_compatible_etf_edge_inr
        cone_compatible_etf_edge_static
        least
        least_part_post_solution_inr_slot_locals_bot_eff
        threefold_monoD_eq[OF tfm]
        threefold_monoD_sides[OF tfm]
        cone)
  have collect: "cfg_collect g S v \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    by (rule side_collect_sound_at_pruned_eff[OF se pp fin finC entry_cov cone inr])
  have analyse_eq:
      "side_analyse_eff \<Pi> ps main etf bot s0 gseed v = side_env \<sigma> v"
    unfolding side_analyse_eff_def \<sigma>_def g_def by simp
  show ?thesis
    using collect analyse_eq by simp
qed
context compiled_source_simulation
begin

corollary source_reaches_side_analyse_eff:
  fixes s0 :: "'a::sound_domain abs_state"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes run: "psteps \<Pi> (main, s, []) src'"
      and se: "sound_effectful_transfer etf"
      and tfm: "threefold_mono (side_cfg_T_eff g etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
      and dom: "\<And>v. cfg_reaches g (cfg_entry g) v \<Longrightarrow>
        side_cfg_solve_dom_eff g etf bot s0 gseed v"
  shows "\<exists>v t stk.
    match src' (v, t, stk) \<and>
    t \<in> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed v\<rbrakk>"
proof -
  obtain v t stk where matched: "match src' (v, t, stk)"
      and collected: "t \<in> cfg_collect g {s} v"
      and reachable: "cfg_reaches g (cfg_entry g) v"
    using source_reaches_cfg_collect[OF run] by blast
  have init_set: "{s} \<le> \<lbrakk>s0\<rbrakk>"
    using init by simp
  have bound:
      "cfg_collect (compile_prog \<Pi> ps main) {s} v
       \<le> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed v\<rbrakk>"
  proof (rule side_analyse_eff_collect_sound_at_pruned)
    show "sound_effectful_transfer etf"
      by (rule se)
    show "threefold_mono
        (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
      using tfm unfolding g_def .
    show "cone_compatible_etf etf"
      by (rule cone)
    show "side_cfg_solve_dom_eff
        (compile_prog \<Pi> ps main) etf bot s0 gseed v"
      using dom[OF reachable] unfolding g_def .
    show "{s} \<le> \<lbrakk>s0\<rbrakk>"
      by (rule init_set)
    show "cfg_reaches (compile_prog \<Pi> ps main)
        (cfg_entry (compile_prog \<Pi> ps main)) v"
      using reachable unfolding g_def .
  qed
  have "t \<in> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed v\<rbrakk>"
    using collected bound unfolding g_def by blast
  then show ?thesis
    using matched by blast
qed

end

theorem concrete_source_reaches_side_analyse_eff:
  fixes s0 :: "'a::sound_domain abs_state"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes wf: "wf_compile_input Pi ps main"
      and run: "psteps Pi (main, s, []) src'"
      and se: "sound_effectful_transfer etf"
      and tfm:
        "threefold_mono
          (side_cfg_T_eff (compile_prog Pi ps main) etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
      and dom:
        "\<And>v.
          cfg_reaches (compile_prog Pi ps main)
            (cfg_entry (compile_prog Pi ps main)) v \<Longrightarrow>
          side_cfg_solve_dom_eff
            (compile_prog Pi ps main) etf bot s0 gseed v"
  shows "\<exists>v t stk.
    concrete_program_match Pi ps main src' (v, t, stk) \<and>
    t \<in> \<lbrakk>side_analyse_eff Pi ps main etf bot s0 gseed v\<rbrakk>"
proof -
  have source_main: "source_com main"
    using wf unfolding wf_compile_input_def by blast
  interpret sim: compiled_source_simulation
      Pi ps main "compile_prog Pi ps main"
      "concrete_program_match Pi ps main"
  proof
    show "compile_prog Pi ps main = compile_prog Pi ps main"
      by simp
    show "wf_compile_input Pi ps main"
      by (rule wf)
    fix t
    show "concrete_program_match Pi ps main
      (main, t, []) (cfg_entry (compile_prog Pi ps main), t, [])"
      by (rule concrete_program_initial_match[OF source_main])
    fix source source' concrete
    assume matched:
        "concrete_program_match Pi ps main source concrete"
       and stepped: "pstep Pi source source'"
    show "\<exists>concrete'.
      star (cstep (compile_prog Pi ps main)) concrete concrete' \<and>
      concrete_program_match Pi ps main source' concrete'"
      by (rule concrete_program_step_match[OF wf matched stepped])
  qed
  show ?thesis
    by (rule sim.source_reaches_side_analyse_eff[
          OF run se tfm cone init dom])
qed

locale source_to_analysis_bridge =
  fixes Pi :: proc_table
    and ps :: "pname list"
    and main :: IMP2_Proc.com
    and g :: cfg
    and s :: store
    and src' :: "(IMP2_Proc.com \<times> store \<times> frame list)"
    and etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and s0 :: "'a abs_state"
    and gseed :: 'g
  assumes g_def: "g = compile_prog Pi ps main"
      and wf: "wf_compile_input Pi ps main"
      and run: "psteps Pi (main, s, []) src'"
      and se: "sound_effectful_transfer etf"
      and tfm: "threefold_mono (side_cfg_T_eff g etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
begin

theorem source_reaches_side_analyse_eff:
  assumes dom:
    "\<And>v. cfg_reaches g (cfg_entry g) v \<Longrightarrow>
      side_cfg_solve_dom_eff g etf bot s0 gseed v"
  shows "\<exists>v t stk.
     concrete_program_match Pi ps main src' (v, t, stk) \<and>
     t \<in> \<lbrakk>side_analyse_eff Pi ps main etf bot s0 gseed v\<rbrakk>"
proof -
  have tfm':
      "threefold_mono (side_cfg_T_eff (compile_prog Pi ps main) etf bot s0 gseed)"
    using tfm g_def by simp
  have dom':
      "\<And>v. cfg_reaches (compile_prog Pi ps main)
            (cfg_entry (compile_prog Pi ps main)) v \<Longrightarrow>
          side_cfg_solve_dom_eff
            (compile_prog Pi ps main) etf bot s0 gseed v"
    using dom g_def by simp
  show ?thesis
    by (rule concrete_source_reaches_side_analyse_eff[
          OF wf run se tfm' cone init dom'])
qed

end


end
