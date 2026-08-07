theory LTR_TD_Side_Eff_Exit
  imports TD_Side_Eff_Cone_Lemmas LTR_TD_Side_Eff_Sound
begin

section \<open>Cone-guarded effectful exit soundness over the original CFG\<close>

text \<open>
  Effectful solver soundness at the program exit, stated directly over the original CFG's
  stack-faithful collecting \<^const>\<open>ltr_collect\<close> --- with no graph transformation and no
  compiled-CFG restriction.  The cone theorem restricts the effectful solver obligations to
  demand-relevant nodes.

  cone-guarded concretization: \<open>acc v _ = (if cfg_reaches g v v0 then \<lbrakk>side_env \<sigma> v\<rbrakk> else UNIV)\<close>.

  Each closure obligation splits: off the cone the slot is \<^term>\<open>UNIV\<close> and the axiom is
  trivial; on the cone the source is on the cone too (\<open>cfg_reaches_intra_src\<close> /
  \<open>cfg_reaches_entry_src\<close> / \<open>cfg_reaches_comb_caller_src\<close> / \<open>cfg_reaches_comb_result_src\<close>), so
  the real \<^const>\<open>side_env\<close> bound applies --- exactly the bound the cone solver computed.  The
  queried node reaches itself, so the conclusion is unguarded there.
\<close>

theorem ltr_post_fixpoint_sound_at_eff_cone:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and S :: "store set" and v0 :: pp
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes se: "sound_effectful_transfer gs etf"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> cfg_reaches g w v0
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes enter_le:
    "\<And>u dst pars args p cont. (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> cfg_reaches g (FunctionEntry p) v0
       \<Longrightarrow> etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env \<sigma> (FunctionEntry p)"
  assumes combine_le:
    "\<And>cl dst pars args p cont. (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> cfg_reaches g cont v0
       \<Longrightarrow> etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma> \<le> side_env \<sigma> cont"
  shows "ltr_collect gs g S v0 \<subseteq> \<lbrakk>side_env \<sigma> v0\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer gs etf by (rule se)
  interpret G: ltr_gamma g S "\<lambda>v _. if cfg_reaches g v v0 then \<lbrakk>side_env \<sigma> v\<rbrakk> else UNIV"
      "\<lambda>_ _ _. ()" "()" gs
  proof (standard, goal_cases ROOT EDGE CALL COMB)
    case (ROOT s)
    show ?case
    proof (cases "cfg_reaches g (cfg_entry g) v0")
      case True then show ?thesis using ROOT entry by auto
    next
      case False then show ?thesis by simp
    qed
  next
    case (EDGE u a v c s s')
    show ?case
    proof (cases "cfg_reaches g v v0")
      case True
      have ru: "cfg_reaches g u v0" using cfg_reaches_intra_src[OF EDGE(1) True] .
      have s_in: "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>" using EDGE(2) ru by simp
      have "s' \<in> \<lbrakk>side_env \<sigma> v\<rbrakk>"
        by (rule se.edge_step_sound_eff[OF inr step_le[OF EDGE(1) True] s_in EDGE(3)])
      then show ?thesis using True by simp
    next
      case False then show ?thesis by simp
    qed
  next
    case (CALL u dst pars args p cont c s)
    show ?case
    proof (cases "cfg_reaches g (FunctionEntry p) v0")
      case True
      have ru: "cfg_reaches g u v0" using cfg_reaches_entry_src[OF CALL(1) True] .
      have s_in: "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>" using CALL(2) ru by simp
      have "call_enter gs (CallEdge dst pars args) s \<in> \<lbrakk>side_env \<sigma> (FunctionEntry p)\<rbrakk>"
        by (rule se.call_enter_sound_eff[OF inr enter_le[OF CALL(1) True] s_in])
      then show ?thesis using True by simp
    next
      case False then show ?thesis by simp
    qed
  next
    case (COMB cl dst pars args p cont c1 s t es)
    show ?case
    proof (cases "cfg_reaches g cont v0")
      case True
      have rcl: "cfg_reaches g cl v0" using cfg_reaches_comb_caller_src[OF COMB(1) True] .
      have rex: "cfg_reaches g (FunctionResult p) v0"
        using cfg_reaches_comb_result_src[OF COMB(1) True] .
      have s_in: "s \<in> \<lbrakk>side_env \<sigma> cl\<rbrakk>" using COMB(2) rcl by simp
      have t_in: "t \<in> \<lbrakk>side_env \<sigma> (FunctionResult p)\<rbrakk>" using COMB(3) rex by simp
      have "combine_collect gs dst s t \<in> \<lbrakk>etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma>\<rbrakk>"
        using se.etf_sound_combine inr s_in t_in unfolding side_env_def by auto
      then have "combine_collect gs dst s t \<in> \<lbrakk>side_env \<sigma> cont\<rbrakk>"
        using gamma_state_mono[OF combine_le[OF COMB(1) True]] by blast
      then show ?thesis using True by simp
    next
      case False then show ?thesis by simp
    qed
  qed
  show ?thesis
  proof (rule subsetI)
    fix x assume "x \<in> ltr_collect gs g S v0"
    then obtain u where u: "u \<in> valid_ltr gs g S" "sink_node u = v0" "sink_store u = x"
      unfolding ltr_collect_def by blast
    have "u \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr u(1) by blast
    then have "sink_store u
        \<in> (if cfg_reaches g (sink_node u) v0 then \<lbrakk>side_env \<sigma> (sink_node u)\<rbrakk> else UNIV)"
      by (simp add: G.gamma_ltr_def)
    then have "sink_store u \<in> \<lbrakk>side_env \<sigma> v0\<rbrakk>" using u(2) by (simp add: cfg_reaches_refl)
    then show "x \<in> \<lbrakk>side_env \<sigma> v0\<rbrakk>" using u(3) by simp
  qed
qed

theorem ltr_post_fixpoint_sound_in_eff_cone:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and S :: "store set" and v0 v :: pp
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes se: "sound_effectful_transfer gs etf"
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> cfg_reaches g w v0
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes enter_le:
    "\<And>u dst pars args p cont. (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> cfg_reaches g (FunctionEntry p) v0
       \<Longrightarrow> etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env \<sigma> (FunctionEntry p)"
  assumes combine_le:
    "\<And>cl dst pars args p cont. (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> cfg_reaches g cont v0
       \<Longrightarrow> etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma> \<le> side_env \<sigma> cont"
  assumes v0_reach: "cfg_reaches g v v0"
  shows "ltr_collect gs g S v \<subseteq> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof (rule ltr_post_fixpoint_sound_at_eff_cone[OF se inr entry])
  fix u a w
  assume e: "(u, a, w) \<in> intra g" and rw: "cfg_reaches g w v"
  show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
    by (rule step_le[OF e cfg_reaches_trans[OF rw v0_reach]])
next
  fix u dst pars args p cont
  assume c: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and rr: "cfg_reaches g (FunctionEntry p) v"
  show "etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env \<sigma> (FunctionEntry p)"
    by (rule enter_le[OF c cfg_reaches_trans[OF rr v0_reach]])
next
  fix cl dst pars args p cont
  assume cmb: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and rr: "cfg_reaches g cont v"
  show "etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma> \<le> side_env \<sigma> cont"
    by (rule combine_le[OF cmb cfg_reaches_trans[OF rr v0_reach]])
qed

text \<open>
  The solver-facing query-cone theorem discharges the demand-relevant obligations
  for an arbitrary query node.  The exit endpoint below is its standard
  specialization.
\<close>
theorem side_collect_sound_in_eff_cone:
  fixes q v :: pp
  assumes se:    "sound_effectful_transfer gs etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) q \<sigma> vars"
  assumes fin:   "finite (intra g)"
  assumes finC:  "finite (calls g)"
  assumes wf:    "wf_cfg g"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes cone:  "cone_compatible_etf gs etf"
  assumes inr:   "inr_slot_locals_bot gs \<sigma>"
  assumes vq:    "cfg_reaches g v q"
  shows "ltr_collect gs g S v \<subseteq> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof -
  have step_le:
    "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> cfg_reaches g w q
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  proof -
    fix u a w assume e: "(u, a, w) \<in> intra g" and rw: "cfg_reaches g w q"
    have wv: "w \<in> vars" by (rule side_cone_in_vars_eff_cone[OF pp fin finC wf cone rw])
    show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
      by (rule etf_combined_le_eff[OF pp wv e fin])
  qed
  have enter_le:
    "\<And>u dst pars args p cont. (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> cfg_reaches g (FunctionEntry p) q
       \<Longrightarrow> etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env \<sigma> (FunctionEntry p)"
  proof -
    fix u dst pars args p cont
    assume cmb: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
      and rr: "cfg_reaches g (FunctionEntry p) q"
    have wv: "FunctionEntry p \<in> vars"
      by (rule side_cone_in_vars_eff_cone[OF pp fin finC wf cone rr])
    show "etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env \<sigma> (FunctionEntry p)"
      by (rule etf_enter_combined_le_eff[OF pp wv cmb finC])
  qed
  have combine_le:
    "\<And>cl dst pars args p cont. (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
       \<Longrightarrow> cfg_reaches g cont q
       \<Longrightarrow> etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma> \<le> side_env \<sigma> cont"
  proof -
    fix cl dst pars args p cont
    assume cmb: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
      and rr: "cfg_reaches g cont q"
    have rv: "cont \<in> vars" by (rule side_cone_in_vars_eff_cone[OF pp fin finC wf cone rr])
    show "etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma> \<le> side_env \<sigma> cont"
      by (rule etf_combine_combined_le_eff[OF pp rv cmb finC])
  qed
  show ?thesis
    by (rule ltr_post_fixpoint_sound_in_eff_cone[OF se inr entry step_le enter_le combine_le vq])
qed

corollary side_collect_sound_exit_eff_ltr_cone:
  assumes se:    "sound_effectful_transfer gs etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff gs g etf bot0 s0 gseed) (cfg_exit g) \<sigma> vars"
  assumes fin:   "finite (intra g)"
  assumes finC:  "finite (calls g)"
  assumes wf:    "wf_cfg g"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes cone:  "cone_compatible_etf gs etf"
  assumes inr:   "inr_slot_locals_bot gs \<sigma>"
  shows "ltr_collect gs g S (cfg_exit g) \<subseteq> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
  by (rule side_collect_sound_in_eff_cone[OF se pp fin finC wf entry cone inr cfg_reaches_refl])

theorem side_analyse_eff_collect_sound_exit_ltr:
  fixes \<Pi> ps mnm main and s0 :: "'a::sound_domain abs_state"
    and S :: "store set"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes se: "sound_effectful_transfer gs etf"
  assumes mono_eq: "is_mono_eq (side_cfg_T_eff gs (compile_prog \<Pi> ps mnm main) etf bot s0 gseed)"
  assumes mono_sides: "mono_sides (side_cfg_T_eff gs (compile_prog \<Pi> ps mnm main) etf bot s0 gseed)"
  assumes mono_deps: "mono_deps (side_cfg_T_eff gs (compile_prog \<Pi> ps mnm main) etf bot s0 gseed)"
  assumes dom: "side_cfg_solve_dom_eff gs (compile_prog \<Pi> ps mnm main) etf bot s0 gseed
                  (cfg_exit (compile_prog \<Pi> ps mnm main))"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes enter_dep: "\<And>c2 f2 a2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_enter etf f2 a2 c2)"
  assumes comb_dep1: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes enter_static: "\<And>cl fs as. static_deps (etf_enter etf fs as cl)"
  assumes comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  assumes edge_inr:
    "\<And>a u \<sigma>' g. local_bot_on_locals gs (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  assumes enter_inr:
    "\<And>cl fs as \<sigma>' g. local_bot_on_locals gs (sides_of_rhs (etf_enter etf fs as cl) \<sigma>' (Inr g))"
  assumes comb_inr:
    "\<And>cc ex dst \<sigma>' g. local_bot_on_locals gs (sides_of_rhs (etf_combine etf dst cc ex) \<sigma>' (Inr g))"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) S (cfg_exit (compile_prog \<Pi> ps mnm main))
         \<le> \<lbrakk>side_analyse_eff gs \<Pi> ps mnm main etf bot s0 gseed
              (cfg_exit (compile_prog \<Pi> ps mnm main))\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer gs etf by (rule se)
  define g where "g = compile_prog \<Pi> ps mnm main"
  define v0 where "v0 = cfg_exit g"
  interpret ip: td_cfg_side_solver_eff gs g etf bot s0 gseed
    using mono_eq mono_sides mono_deps unfolding g_def by unfold_locales
  define \<sigma> where "\<sigma> = ip.nu_at v0"
  have fin: "finite (intra g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (calls g)" unfolding g_def using compile_prog_finite by simp
  have wf: "wf_cfg g" unfolding g_def by (rule compile_prog_wf)
  have dom': "side_cfg_solve_dom_eff gs g etf bot s0 gseed v0"
    using dom unfolding g_def v0_def by simp
  have pp: "part_post_solution (side_cfg_T_eff gs g etf bot s0 gseed) v0 \<sigma> (ip.stabl_at v0)"
    using ip.part_post_at_cfg[OF dom'] unfolding \<sigma>_def by simp
  have entry_reach: "cfg_reaches g (cfg_entry g) v0"
    using compile_prog_entry_cfg_reaches_exit unfolding g_def v0_def by simp
  have entry_in: "cfg_entry g \<in> ip.stabl_at v0"
    by (rule side_cone_in_vars_eff[OF pp fin finC wf edge_dep enter_dep comb_dep1 comb_dep2
          edge_static enter_static comb_static entry_reach])
  have entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp entry_in])
  have entry_cov: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using S_sound gamma_state_mono[OF entry_le] by blast
  have least: "least_part_post_solution (side_cfg_T_eff gs g etf bot s0 gseed) v0 \<sigma> (ip.stabl_at v0)"
    by (metis (mono_tags, opaque_lifting) dom' ip.cfg_pkg_eff_eq ip.least_part_post_at_cfg
        local.\<sigma>_def)
  have inr: "inr_slot_locals_bot gs \<sigma>"
    by (metis comb_inr comb_static edge_inr edge_static enter_inr enter_static g_def least
        least_part_post_solution_inr_slot_locals_bot_eff mono_eq mono_sides)
  have cone: "cone_compatible_etf gs etf"
    unfolding cone_compatible_etf_def
    by (intro conjI allI edge_dep enter_dep comb_dep1 comb_dep2
          edge_static enter_static comb_static edge_inr comb_inr enter_inr)
  have collect: "ltr_collect gs g S (cfg_exit g) \<subseteq> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
    by (rule side_collect_sound_exit_eff_ltr_cone[OF se pp[unfolded v0_def] fin finC wf
          entry_cov cone inr])
  have analyse_eq:
    "side_analyse_eff gs \<Pi> ps mnm main etf bot s0 gseed (cfg_exit g) = side_env \<sigma> (cfg_exit g)"
    unfolding side_analyse_eff_def \<sigma>_def v0_def g_def by simp
  show ?thesis using collect analyse_eq by (simp add: g_def)
qed

corollary side_analyse_eff_collect_sound_exit_ltr_cone:
  fixes \<Pi> ps mnm main and s0 :: "'a::sound_domain abs_state"
    and S :: "store set"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes se: "sound_effectful_transfer gs etf"
  assumes tfm: "threefold_mono (side_cfg_T_eff gs (compile_prog \<Pi> ps mnm main) etf bot s0 gseed)"
  assumes cone: "cone_compatible_etf gs etf"
  assumes dom: "side_cfg_solve_dom_eff gs (compile_prog \<Pi> ps mnm main) etf bot s0 gseed
                  (cfg_exit (compile_prog \<Pi> ps mnm main))"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows "ltr_collect gs (compile_prog \<Pi> ps mnm main) S (cfg_exit (compile_prog \<Pi> ps mnm main))
         \<le> \<lbrakk>side_analyse_eff gs \<Pi> ps mnm main etf bot s0 gseed
              (cfg_exit (compile_prog \<Pi> ps mnm main))\<rbrakk>"
  by (rule side_analyse_eff_collect_sound_exit_ltr[OF se
        threefold_monoD_eq[OF tfm] threefold_monoD_sides[OF tfm]
        threefold_monoD_deps[OF tfm] dom S_sound
        cone_compatible_etf_edge_dep[OF cone]
        cone_compatible_etf_enter_dep[OF cone]
        cone_compatible_etf_comb_dep1[OF cone]
        cone_compatible_etf_comb_dep2[OF cone]
        cone_compatible_etf_edge_static[OF cone]
        cone_compatible_etf_enter_static[OF cone]
        cone_compatible_etf_comb_static[OF cone]
        cone_compatible_etf_edge_inr[OF cone]
        cone_compatible_etf_enter_inr[OF cone]
        cone_compatible_etf_comb_inr[OF cone]])

end

