theory LTR_TD_Side_Eff_Exit
  imports TD_Side_Eff_Cone_Lemmas LTR_TD_Side_Eff_Sound
begin

section \<open>Cone-guarded effectful exit soundness over the original CFG\<close>

text \<open>
  Effectful solver soundness at the program exit, stated directly over the original CFG's
  stack-faithful collecting \<^const>\<open>ltr_collect\<close> --- with no graph transformation, no
  \<open>call_return_reaches\<close> bridge, and no compiled-CFG restriction.
  The cone theorem restricts the effectful solver obligations to demand-relevant nodes.
  It is a graph-structure result used by the trace-native exit endpoint.
  cone-guarded concretization

  \<^item> \<open>acc v _ = (if cfg_reaches g v v0 then \<lbrakk>side_env \<sigma> v\<rbrakk> else UNIV)\<close>.

  Each closure obligation splits: off the cone the slot is \<^term>\<open>UNIV\<close> and the axiom is trivial;
  on the cone the source is on the cone too (\<open>cfg_reaches_edge_src\<close> /
  \<open>cfg_reaches_combine_exit_src\<close>), so the real \<^const>\<open>side_env\<close> bound applies --- exactly the
  bound the cone solver computed.  The queried node \<^term>\<open>cfg_exit g\<close> reaches itself, so the
  conclusion is unguarded there.  The R5d obstruction does not arise: a dead procedure's call site
  is off the cone, where the guard makes the obligation vacuous.
\<close>

text \<open>
  The cone-guarded interface theorem.  Its hypotheses constrain only cone edges/combines
  (target / return node reaches \<open>v0\<close>) --- precisely what the demand-driven solver proves.
\<close>
theorem ltr_post_fixpoint_sound_at_eff_cone:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and S :: "store set" and v0 :: pp
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes se: "sound_effectful_transfer etf"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> cfg_reaches g w v0
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes combine_le:
    "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow> cfg_reaches g ret v0 \<Longrightarrow>
       etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
  shows "ltr_collect g S v0 \<subseteq> \<lbrakk>side_env \<sigma> v0\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer etf by (rule se)
  interpret G: ltr_gamma g S "\<lambda>v _. if cfg_reaches g v v0 then \<lbrakk>side_env \<sigma> v\<rbrakk> else UNIV"
      "\<lambda>_ _. ()" "()"
  proof (standard, goal_cases ROOT EDGE SEED COMB)
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
      have ru: "cfg_reaches g u v0" using cfg_reaches_edge_src[OF EDGE(1) True] .
      have s_in: "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>" using EDGE(3) ru by simp
      have "s' \<in> \<lbrakk>side_env \<sigma> v\<rbrakk>"
        by (rule se.edge_step_sound_eff[OF inr step_le[OF EDGE(1) True] s_in EDGE(4)])
      then show ?thesis using True by simp
    next
      case False then show ?thesis by simp
    qed
  next
    case (SEED u v c s s' xs es)
    show ?case
    proof (cases "cfg_reaches g v v0")
      case True
      have ru: "cfg_reaches g u v0" using cfg_reaches_edge_src[OF SEED(1) True] .
      have s_in: "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>" using SEED(2) ru by simp
      have "s' \<in> \<lbrakk>side_env \<sigma> v\<rbrakk>"
        by (rule se.edge_step_sound_eff[OF inr step_le[OF SEED(1) True] s_in SEED(3)])
      then show ?thesis using True by simp
    next
      case False then show ?thesis by simp
    qed
  next
    case (COMB cl ex v dst c1 s t es)
    show ?case
    proof (cases "cfg_reaches g v v0")
      case True
      have "cfg_reaches g cl v"
        using cfg_reaches_combine_call[OF COMB(1)]
        by (simp add: combine_call_node_def combine_return_node_def)
      then have rcl: "cfg_reaches g cl v0" using cfg_reaches_trans True by blast
      have rex: "cfg_reaches g ex v0" using cfg_reaches_combine_exit_src[OF COMB(1) True] .
      have s_in: "s \<in> \<lbrakk>side_env \<sigma> cl\<rbrakk>" using COMB(2) rcl by simp
      have t_in: "t \<in> \<lbrakk>side_env \<sigma> ex\<rbrakk>" using COMB(3) rex by simp
      have "combine_collect dst s t \<in> \<lbrakk>etf_full (etf_combine etf dst cl ex) \<sigma>\<rbrakk>"
        using se.etf_sound_combine inr s_in t_in unfolding side_env_def by auto
      then have "combine_collect dst s t \<in> \<lbrakk>side_env \<sigma> v\<rbrakk>"
        using gamma_state_mono[OF combine_le[OF COMB(1) True]] by blast
      then show ?thesis using True by simp
    next
      case False then show ?thesis by simp
    qed
  qed
  show ?thesis
  proof
    fix x assume "x \<in> ltr_collect g S v0"
    then obtain u where u: "u \<in> valid_ltr g S" "sink_node u = v0" "sink_store u = x"
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
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite => 'a::sound_domain abs_state"
    and S :: "store set" and v0 v :: pp
    and etf :: "('g, 'a) effectful_domain_transfer"
  assumes se: "sound_effectful_transfer etf"
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes entry: "S <= \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> cfg_reaches g w v0
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> <= side_env \<sigma> w"
  assumes combine_le:
    "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow> cfg_reaches g ret v0 \<Longrightarrow>
       etf_full (etf_combine etf dst c ex) \<sigma> <= side_env \<sigma> ret"
  assumes v0_reach: "cfg_reaches g v v0"
  shows "ltr_collect g S v \<subseteq> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof (rule ltr_post_fixpoint_sound_at_eff_cone[OF se inr entry])
  fix u a w
  assume e: "(u, a, w) \<in> edges g" and rw: "cfg_reaches g w v"
  show "etf_full (apply_etf etf a u) \<sigma> <= side_env \<sigma> w"
    by (rule step_le[OF e cfg_reaches_trans[OF rw v0_reach]])
next
  fix c ex ret dst
  assume cmb: "(c, ex, ret, dst) \<in> combines g" and rr: "cfg_reaches g ret v"
  show "etf_full (etf_combine etf dst c ex) \<sigma> <= side_env \<sigma> ret"
    by (rule combine_le[OF cmb cfg_reaches_trans[OF rr v0_reach]])
qed

text \<open>
  The solver-facing query-cone theorem discharges the demand-relevant obligations
  for an arbitrary query node. The exit endpoint below is its standard
  specialization.
\<close>
theorem side_collect_sound_in_eff_cone:
  fixes q v :: pp
  assumes se:    "sound_effectful_transfer etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) q \<sigma> vars"
  assumes fin:   "finite (edges g)"
  assumes finC:  "finite (combines g)"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes cone:  "cone_compatible_etf etf"
  assumes inr:   "inr_slot_locals_bot \<sigma>"
  assumes vq:    "cfg_reaches g v q"
  shows "ltr_collect g S v \<subseteq> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof -
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> cfg_reaches g w q
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  proof -
    fix u a w assume e: "(u, a, w) \<in> edges g" and rw: "cfg_reaches g w q"
    have wv: "w \<in> vars"
      by (rule side_cone_in_vars_eff[OF pp fin finC
            cone_compatible_etf_edge_dep[OF cone] cone_compatible_etf_comb_dep1[OF cone]
            cone_compatible_etf_comb_dep2[OF cone] cone_compatible_etf_edge_static[OF cone]
            cone_compatible_etf_comb_static[OF cone] rw])
    show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
      by (rule etf_combined_le_eff[OF pp wv e fin])
  qed
  have combine_le:
    "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow> cfg_reaches g ret q \<Longrightarrow>
       etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
  proof -
    fix c ex ret dst assume cmb: "(c, ex, ret, dst) \<in> combines g"
      and rr: "cfg_reaches g ret q"
    have rv: "ret \<in> vars"
      by (rule side_cone_in_vars_eff[OF pp fin finC
            cone_compatible_etf_edge_dep[OF cone] cone_compatible_etf_comb_dep1[OF cone]
            cone_compatible_etf_comb_dep2[OF cone] cone_compatible_etf_edge_static[OF cone]
            cone_compatible_etf_comb_static[OF cone] rr])
    show "etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
      by (rule etf_combine_combined_le_eff[OF pp rv cmb finC])
  qed
  show ?thesis
    by (rule ltr_post_fixpoint_sound_in_eff_cone[OF se inr entry step_le combine_le vq])
qed

corollary side_collect_sound_exit_eff_ltr_cone:
  assumes se:    "sound_effectful_transfer etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) (cfg_exit g) \<sigma> vars"
  assumes fin:   "finite (edges g)"
  assumes finC:  "finite (combines g)"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes cone:  "cone_compatible_etf etf"
  assumes inr:   "inr_slot_locals_bot \<sigma>"
  shows "ltr_collect g S (cfg_exit g) \<subseteq> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
  by (rule side_collect_sound_in_eff_cone[OF se pp fin finC entry cone inr cfg_reaches_refl])




theorem side_analyse_eff_collect_sound_exit_ltr:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and S :: "store set"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes se: "sound_effectful_transfer etf"
  assumes mono_eq: "is_mono_eq (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
  assumes mono_sides: "mono_sides (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
  assumes mono_deps: "mono_deps (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
  assumes dom: "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) etf bot s0 gseed
                  (cfg_exit (compile_prog \<Pi> ps main))"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes edge_dep: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf etf b z)"
  assumes comb_dep1: "\<And>c2 e2 d2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes comb_dep2: "\<And>c2 e2 d2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine etf d2 c2 e2)"
  assumes edge_static: "\<And>a u. static_deps (apply_etf etf a u)"
  assumes comb_static: "\<And>cc ex dst. static_deps (etf_combine etf dst cc ex)"
  assumes edge_inr:
    "\<And>a u \<sigma>' g. local_bot_on_locals (sides_of_rhs (apply_etf etf a u) \<sigma>' (Inr g))"
  assumes comb_inr:
    "\<And>cc ex dst \<sigma>' g. local_bot_on_locals (sides_of_rhs (etf_combine etf dst cc ex) \<sigma>' (Inr g))"
  shows "ltr_collect (compile_prog \<Pi> ps main) S (cfg_exit (compile_prog \<Pi> ps main))
         \<le> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed
              (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer etf by (rule se)
  define g where "g = compile_prog \<Pi> ps main"
  define v0 where "v0 = cfg_exit g"
  interpret ip: td_cfg_side_solver_eff g etf bot s0 gseed
    using mono_eq mono_sides mono_deps unfolding g_def by unfold_locales
  define \<sigma> where "\<sigma> = ip.nu_at v0"
  have fin: "finite (edges g)" unfolding g_def using compile_prog_finite by simp
  have finC: "finite (combines g)" unfolding g_def using compile_prog_finite by simp
  have dom': "side_cfg_solve_dom_eff g etf bot s0 gseed v0"
    using dom unfolding g_def v0_def by simp
  have pp: "part_post_solution (side_cfg_T_eff g etf bot s0 gseed) v0 \<sigma> (ip.stabl_at v0)"
    using ip.part_post_at_cfg[OF dom'] unfolding \<sigma>_def by simp
  have entry_reach: "cfg_reaches g (cfg_entry g) v0"
    using compile_prog_entry_cfg_reaches_exit unfolding g_def v0_def by simp
  have entry_in: "cfg_entry g \<in> ip.stabl_at v0"
    by (rule side_cone_in_vars_eff[OF pp fin finC edge_dep comb_dep1 comb_dep2
          edge_static comb_static entry_reach])
  have entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp entry_in])
  have entry_cov: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using S_sound gamma_state_mono[OF entry_le] by blast
  have least: "least_part_post_solution (side_cfg_T_eff g etf bot s0 gseed) v0 \<sigma> (ip.stabl_at v0)"
    by (metis (mono_tags, opaque_lifting) dom' ip.cfg_pkg_eff_eq ip.least_part_post_at_cfg
        local.\<sigma>_def)
  have inr: "inr_slot_locals_bot \<sigma>"
    by (metis comb_inr comb_static edge_inr edge_static g_def least
        least_part_post_solution_inr_slot_locals_bot_eff mono_eq mono_sides)
  have collect: "ltr_collect g S (cfg_exit g) \<le> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
  proof (rule ltr_post_fixpoint_sound_at_eff_cone[OF se inr entry_cov])
    fix u a w
    assume e: "(u, a, w) \<in> edges g" and rw: "cfg_reaches g w (cfg_exit g)"
    have wv': "w \<in> ip.stabl_at (cfg_exit g)"
      by (rule side_cone_in_vars_eff[OF pp[unfolded v0_def] fin finC edge_dep comb_dep1 comb_dep2
            edge_static comb_static rw])
    have wv: "w \<in> ip.stabl_at v0"
      using wv' unfolding v0_def by simp
    show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
      by (rule etf_combined_le_eff[OF pp wv e fin])
  next
    fix c ex ret dst
    assume cmb: "(c, ex, ret, dst) \<in> combines g"
      and rr: "cfg_reaches g ret (cfg_exit g)"
    have rv': "ret \<in> ip.stabl_at (cfg_exit g)"
      by (rule side_cone_in_vars_eff[OF pp[unfolded v0_def] fin finC edge_dep comb_dep1 comb_dep2
            edge_static comb_static rr])
    have rv: "ret \<in> ip.stabl_at v0"
      using rv' unfolding v0_def by simp
    show "etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
      by (rule etf_combine_combined_le_eff[OF pp rv cmb finC])
  qed
  have analyse_eq:
    "side_analyse_eff \<Pi> ps main etf bot s0 gseed (cfg_exit g) = side_env \<sigma> (cfg_exit g)"
    unfolding side_analyse_eff_def \<sigma>_def v0_def g_def by simp
  show ?thesis using collect analyse_eq by (simp add: g_def)
qed
corollary side_analyse_eff_collect_sound_exit_ltr_cone:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and S :: "store set"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes se: "sound_effectful_transfer etf"
  assumes tfm: "threefold_mono (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
  assumes cone: "cone_compatible_etf etf"
  assumes dom: "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) etf bot s0 gseed
                  (cfg_exit (compile_prog \<Pi> ps main))"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows "ltr_collect (compile_prog \<Pi> ps main) S (cfg_exit (compile_prog \<Pi> ps main))
         \<le> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed
              (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
  by (rule side_analyse_eff_collect_sound_exit_ltr[OF se
        threefold_monoD_eq[OF tfm] threefold_monoD_sides[OF tfm]
        threefold_monoD_deps[OF tfm] dom S_sound
        cone_compatible_etf_edge_dep[OF cone]
        cone_compatible_etf_comb_dep1[OF cone]
        cone_compatible_etf_comb_dep2[OF cone]
        cone_compatible_etf_edge_static[OF cone]
        cone_compatible_etf_comb_static[OF cone]
        cone_compatible_etf_edge_inr[OF cone]
        cone_compatible_etf_comb_inr[OF cone]])



end
