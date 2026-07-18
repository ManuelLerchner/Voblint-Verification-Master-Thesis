theory LTR_TD_Side_Eff_Exit
  imports TD_Side_Eff_Soundness LTR_TD_Side_Eff_Sound
begin

section \<open>Cone-guarded effectful exit soundness over the original CFG\<close>

text \<open>
  Effectful solver soundness at the program exit, stated directly over the original CFG's
  stack-faithful collecting \<^const>\<open>ltr_collect\<close> --- with no graph transformation, no
  \<open>call_return_reaches\<close> bridge, and no compiled-CFG restriction.

  Pruning was a graph-structure artifact of the \<^const>\<open>cfg_collect\<close> proof chain: the raw-CFG
  effectful theorem demanded per-edge bounds everywhere, while the demand-driven solver bounds only
  the exit cone, so the graph was shrunk to the cone to match.  With local-trace semantics the cone
  restriction is intrinsic: a trace reaching \<open>v0\<close> visits only nodes that reach \<open>v0\<close>.  We move the
  cone from the graph into the abstract guarantee, interpreting \<^locale>\<open>ltr_gamma\<close> at the
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

text \<open>
  The primary compiled-program exit corollary: from an effectful post-solution covering the exit
  cone, soundness against \<^const>\<open>ltr_collect\<close> at \<^term>\<open>cfg_exit g\<close>, directly over the original
  graph.  The five dependency/static obligations come from a single \<^const>\<open>cone_compatible_etf\<close>
  hypothesis; the cone solver supplies the guarded per-edge / per-combine bounds because each cone
  node is a solver variable (\<open>side_cone_in_vars_eff\<close>).  No \<^const>\<open>prune_cfg\<close>, no
  \<open>call_return_reaches\<close>, no \<^const>\<open>cfg_collect\<close>; holds for arbitrary CFGs, compiled or not.
\<close>
theorem side_collect_sound_exit_eff_ltr_cone:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set"
    and etf :: "('g, 'a) effectful_domain_transfer" and gseed :: 'g
  assumes se:    "sound_effectful_transfer etf"
  assumes pp:    "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed) (cfg_exit g) \<sigma> vars"
  assumes fin:   "finite (edges g)"
  assumes finC:  "finite (combines g)"
  assumes entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
  assumes cone:  "cone_compatible_etf etf"
  assumes inr:   "inr_slot_locals_bot \<sigma>"
  shows "ltr_collect g S (cfg_exit g) \<subseteq> \<lbrakk>side_env \<sigma> (cfg_exit g)\<rbrakk>"
proof -
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> cfg_reaches g w (cfg_exit g)
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  proof -
    fix u a w assume e: "(u, a, w) \<in> edges g" and rw: "cfg_reaches g w (cfg_exit g)"
    have wv: "w \<in> vars"
      by (rule side_cone_in_vars_eff[OF pp fin finC
            cone_compatible_etf_edge_dep[OF cone] cone_compatible_etf_comb_dep1[OF cone]
            cone_compatible_etf_comb_dep2[OF cone] cone_compatible_etf_edge_static[OF cone]
            cone_compatible_etf_comb_static[OF cone] rw])
    show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
      by (rule etf_combined_le_eff[OF pp wv e fin])
  qed
  have combine_le:
    "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow> cfg_reaches g ret (cfg_exit g) \<Longrightarrow>
       etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
  proof -
    fix c ex ret dst assume cmb: "(c, ex, ret, dst) \<in> combines g"
      and rr: "cfg_reaches g ret (cfg_exit g)"
    have rv: "ret \<in> vars"
      by (rule side_cone_in_vars_eff[OF pp fin finC
            cone_compatible_etf_edge_dep[OF cone] cone_compatible_etf_comb_dep1[OF cone]
            cone_compatible_etf_comb_dep2[OF cone] cone_compatible_etf_edge_static[OF cone]
            cone_compatible_etf_comb_static[OF cone] rr])
    show "etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
      by (rule etf_combine_combined_le_eff[OF pp rv cmb finC])
  qed
  show ?thesis
    by (rule ltr_post_fixpoint_sound_at_eff_cone[OF se inr entry step_le combine_le])
qed

end
