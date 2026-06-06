theory TD_Side_Soundness
  imports TD_Side_Interface Constraint_System_Sound
begin

(*
  Side-effecting TD solver soundness.

  Core theorems take a partial post-solution (what TD_side guarantees on
  solve_dom).  Corollaries discharge that from mono + solve_dom via
  TD_Side_Interface.
*)

context sound_domain
begin

theorem side_collect_sound_at_pp:
  fixes g :: cfg and tf :: "'a domain_transfer" and bot0 s0 :: "'a abs_state"
    and S :: "store set" and v :: pp and x :: pp
    and sigma :: "pp + unit => 'a abs_state" and vars :: "pp set"
  assumes tf_sound_assign:
    "\<forall>x a sg. \<forall>s \<in> gamma_state sg.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sg)"
  assumes tf_sound_assume:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sg)"
  assumes tf_sound_assume_not:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sg)"
  assumes fin_cfg: "finite (edges g)"
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) x sigma vars"
  assumes vars_reach: "\<And>u es w. g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> w \<Longrightarrow> w \<in> vars"
  assumes entry_cov: "S \<subseteq> gamma_state (side_env sigma (cfg_entry g))"
  assumes path: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v"
  shows "cfg_collect g S v \<le> gamma_state (side_env sigma v)"
  using side_collect_sound_at[OF tf_sound_assign tf_sound_assume tf_sound_assume_not
    pp vars_reach fin_cfg entry_cov path] .

theorem side_analyse_collect_sound_at:
  fixes c :: com and tf :: "'a domain_transfer" and bot0 s0 :: "'a abs_state"
    and S :: "store set" and v0 :: pp and es :: "(edge_action * pp) list"
  assumes tf_sound_assign:
    "\<forall>x a sg. \<forall>s \<in> gamma_state sg.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sg)"
  assumes tf_sound_assume:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sg)"
  assumes tf_sound_assume_not:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sg)"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes pp:
    "part_post_solution (side_cfg_T (to_cfg c) tf (\<squnion>) bot0 s0)
       (cfg_entry (to_cfg c))
       (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c)))
       (td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c)))"
  assumes entry_cov:
    "S \<subseteq> gamma_state
       (side_env (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c)))
                 (cfg_entry (to_cfg c)))"
  assumes cfg_in_stabl:
    "\<And>u es w. cfg_path (to_cfg c) u es w
     \<Longrightarrow> w \<in> td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c))"
  assumes entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v0"
  shows "cfg_collect (to_cfg c) S v0
         \<le> gamma_state (side_analyse c tf bot0 s0 v0)"
proof -
  define g where "g = to_cfg c"
  define x where "x = cfg_entry g"
  define sigma where
    "sigma = td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c))"
  define vars where
    "vars = td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c))"
  have g_def: "g = to_cfg c" by (simp add: g_def)
  have x_def: "x = cfg_entry g" by (simp add: x_def g_def)
  have sigma_def: "sigma = td_cfg_side_solver.side_sigma_at g tf bot0 s0 x"
    by (simp add: sigma_def g_def x_def)
  have vars_def: "vars = td_cfg_side_solver.side_stabl_at g tf bot0 s0 x"
    by (simp add: vars_def g_def x_def)
  have pp': "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) x sigma vars"
    using pp unfolding g_def x_def sigma_def vars_def by simp
  have vars_reach: "\<And>u es w. g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> w \<Longrightarrow> w \<in> vars"
    using cfg_in_stabl unfolding g_def x_def vars_def by auto
  have entry: "S \<subseteq> gamma_state (side_env sigma (cfg_entry g))"
    using entry_cov unfolding sigma_def g_def x_def by simp
  have collect: "cfg_collect g S v0 \<le> gamma_state (side_env sigma v0)"
    using side_collect_sound_at_pp[OF tf_sound_assign tf_sound_assume tf_sound_assume_not
      fin_cfg[unfolded g_def] pp' vars_reach entry entry_path]
    unfolding g_def .
  show ?thesis
    unfolding side_analyse_def td_cfg_side_solver.side_env_entry_def
      td_cfg_side_solver.side_env_at_def side_env_def sigma_def g_def x_def
    using collect by simp
qed

theorem side_analyse_collect_sound:
  fixes c :: com and tf :: "'a domain_transfer" and bot0 s0 :: "'a abs_state"
    and S :: "store set"
  assumes tf_sound_assign:
    "\<forall>x a sg. \<forall>s \<in> gamma_state sg.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sg)"
  assumes tf_sound_assume:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sg)"
  assumes tf_sound_assume_not:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sg)"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes pp:
    "part_post_solution (side_cfg_T (to_cfg c) tf (\<squnion>) bot0 s0)
       (cfg_entry (to_cfg c))
       (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c)))
       (td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c)))"
  assumes entry_cov:
    "S \<subseteq> gamma_state
       (side_env (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c)))
                 (cfg_entry (to_cfg c)))"
  assumes cfg_in_stabl:
    "\<And>u es w. cfg_path (to_cfg c) u es w
     \<Longrightarrow> w \<in> td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c))"
  assumes entry_reachable:
    "\<And>v. \<exists>es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
  shows "\<forall>v. cfg_collect (to_cfg c) S v
         \<le> gamma_state (side_analyse c tf bot0 s0 v)"
proof (intro allI)
  fix v
  obtain es where entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
    using entry_reachable by blast
  show "cfg_collect (to_cfg c) S v
        \<le> gamma_state (side_analyse c tf bot0 s0 v)"
    by (rule side_analyse_collect_sound_at[OF tf_sound_assign tf_sound_assume
          tf_sound_assume_not fin_cfg pp entry_cov cfg_in_stabl entry_path])
qed

theorem side_analyse_collect_sound_at_solver:
  fixes c :: com and tf :: "'a domain_transfer" and bot0 s0 :: "'a abs_state"
    and S :: "store set" and v0 :: pp and es :: "(edge_action * pp) list"
  assumes tf_sound_assign:
    "\<forall>x a sg. \<forall>s \<in> gamma_state sg.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sg)"
  assumes tf_sound_assume:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sg)"
  assumes tf_sound_assume_not:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sg)"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v0"
  assumes side_solve_dom: "side.solve_dom (cfg_entry (to_cfg c))"
  assumes S_sub: "S \<subseteq> gamma_state s0"
  assumes s0_global_bot: "restrict_global s0 = bot"
  assumes cfg_in_stabl:
    "\<And>u es w. cfg_path (to_cfg c) u es w
     \<Longrightarrow> w \<in> td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 (cfg_entry (to_cfg c))"
  shows "cfg_collect (to_cfg c) S v0
         \<le> gamma_state (side_analyse c tf bot0 s0 v0)"
proof -
  interpret side: td_cfg_side_solver "to_cfg c" tf bot0 s0
    using tf_mono by unfold_locales
  have pp: "part_post_solution side.cfg_side_T (cfg_entry (to_cfg c))
             (side.side_sigma_at (cfg_entry (to_cfg c)))
             (side.side_stabl_at (cfg_entry (to_cfg c)))"
    using side.side_solver_part_post_at_entry[OF side_solve_dom] by simp
  have entry_cov: "S \<subseteq> gamma_state
       (side_env (side.side_sigma_at (cfg_entry (to_cfg c))) (cfg_entry (to_cfg c)))"
  proof -
    have acc0_le: "bot0 \<squnion> restrict_local s0
                   \<le> side.side_sigma_at (cfg_entry (to_cfg c)) (Inl (cfg_entry (to_cfg c)))"
      using side_post_solution_le_local[OF pp side.side_entry_in_stabl[OF side_solve_dom]]
      unfolding eq_side_cfg_T side.cfg_side_T_def by simp
    have s0_le: "s0 \<le> bot0 \<squnion> restrict_local s0"
    proof (rule le_funI)
      fix x
      show "s0 x \<le> (bot0 \<squnion> restrict_local s0) x"
      proof (cases "is_global x")
        case True
        then show ?thesis using s0_global_bot unfolding restrict_global_def by simp
      next
        case False
        then show ?thesis unfolding restrict_local_def using sup_ge2 by simp
      qed
    qed
    have "s0 \<le> side_env (side.side_sigma_at (cfg_entry (to_cfg c))) (cfg_entry (to_cfg c))"
      unfolding side_env_def using acc0_le s0_le sup_ge1 sup_left_mono by auto
    thus ?thesis using S_sub gamma_state_mono by blast
  qed
  show ?thesis
    using side_analyse_collect_sound_at[OF tf_sound_assign tf_sound_assume
      tf_sound_assume_not fin_cfg pp entry_cov cfg_in_stabl entry_path]
    by simp
qed

end

end
