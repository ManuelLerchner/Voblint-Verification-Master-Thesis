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
    and S :: "store set" and v :: pp
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
  assumes tf_sound_enter:
    "\<forall>sg. \<forall>s \<in> gamma_state sg.
       enter_state s \<in> gamma_state (tf_enter tf sg)"
  assumes fin_cfg: "finite (edges g)"
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) v sigma vars"
  assumes entry_cov: "S \<subseteq> gamma_state (side_env sigma (cfg_entry g))"
  assumes path: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v"
  shows "cfg_collect g S v \<le> gamma_state (side_env sigma v)"
proof -
  interpret st: sound_transfer gamma tf
  proof unfold_locales
    show "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
         s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
      using tf_sound_assign by simp
    show "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
         \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
      using tf_sound_assume by simp
    show "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
         \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
      using tf_sound_assume_not by simp
    show "\<forall>sigma. \<forall>s \<in> gamma_state sigma.
         enter_state s \<in> gamma_state (tf_enter tf sigma)"
      using tf_sound_enter by simp
  qed
  show ?thesis using st.side_collect_sound_at[OF pp fin_cfg entry_cov path] .
qed

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
  assumes tf_sound_enter:
    "\<forall>sg. \<forall>s \<in> gamma_state sg.
       enter_state s \<in> gamma_state (tf_enter tf sg)"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes pp:
    "part_post_solution (side_cfg_T (to_cfg c) tf (\<squnion>) bot0 s0) v0
       (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 v0)
       (td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 v0)"
  assumes entry_cov:
    "S \<subseteq> gamma_state
       (side_env (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 v0)
                 (cfg_entry (to_cfg c)))"
  assumes entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v0"
  shows "cfg_collect (to_cfg c) S v0
         \<le> gamma_state (side_analyse c tf bot0 s0 v0)"
proof -
  define g where "g = to_cfg c"
  define sigma where
    "sigma = td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 v0"
  have g_def: "g = to_cfg c" by (simp add: g_def)
  have sigma_def: "sigma = td_cfg_side_solver.side_sigma_at g tf bot0 s0 v0"
    by (simp add: sigma_def g_def)
  have pp': "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) v0 sigma
             (td_cfg_side_solver.side_stabl_at g tf bot0 s0 v0)"
    using pp unfolding g_def sigma_def by simp
  have entry: "S \<subseteq> gamma_state (side_env sigma (cfg_entry g))"
    using entry_cov unfolding sigma_def g_def by simp
  have fin_g: "finite (edges g)" using fin_cfg unfolding g_def by simp
  have path': "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v0"
    using entry_path unfolding g_def by simp
  show "cfg_collect (to_cfg c) S v0 \<le> gamma_state (side_analyse c tf bot0 s0 v0)"
  proof (rule order_trans)
    show "cfg_collect (to_cfg c) S v0 \<le> gamma_state (side_env sigma v0)"
      using side_collect_sound_at_pp[OF tf_sound_assign tf_sound_assume
            tf_sound_assume_not tf_sound_enter fin_g pp' entry path']
      unfolding g_def by simp
    show "gamma_state (side_env sigma v0) \<le> gamma_state (side_analyse c tf bot0 s0 v0)"
      unfolding side_analyse_def side_env_def sigma_def g_def
      by (rule order_refl)
  qed
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
  assumes tf_sound_enter:
    "\<forall>sg. \<forall>s \<in> gamma_state sg.
       enter_state s \<in> gamma_state (tf_enter tf sg)"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes pp:
    "\<And>v. part_post_solution (side_cfg_T (to_cfg c) tf (\<squnion>) bot0 s0) v
       (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 v)
       (td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 v)"
  assumes entry_cov:
    "\<And>v. S \<subseteq> gamma_state
       (side_env (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 v)
                 (cfg_entry (to_cfg c)))"
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
          tf_sound_assume_not tf_sound_enter fin_cfg pp entry_cov entry_path])
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
  assumes tf_sound_enter:
    "\<forall>sg. \<forall>s \<in> gamma_state sg.
       enter_state s \<in> gamma_state (tf_enter tf sg)"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes fin_cfg: "finite (edges (to_cfg c))"  assumes entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v0"
  assumes side_solve_dom:
    "side_cfg_solve_dom (to_cfg c) tf bot0 s0 v0"
  assumes S_sub: "S \<subseteq> gamma_state s0"
  assumes s0_global_bot: "restrict_global s0 = bot"
  shows "cfg_collect (to_cfg c) S v0
         \<le> gamma_state (side_analyse c tf bot0 s0 v0)"
proof -
  interpret solver: td_cfg_side_solver "to_cfg c" tf bot0 s0
    using tf_mono by unfold_locales
  have pp: "part_post_solution solver.cfg_side_T v0 (solver.side_sigma_at v0) (solver.side_stabl_at v0)"
    using solver.side_solver_part_post_at_cfg[OF side_solve_dom] by simp
  define g where "g = to_cfg c"
  have g_def: "g = to_cfg c" by (simp add: g_def)
  have pp': "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) v0
             (solver.side_sigma_at v0) (solver.side_stabl_at v0)"
    using pp unfolding g_def solver.cfg_side_T_eq by simp
  have fin: "finite (edges g)" using fin_cfg unfolding g_def by simp
  have entry_path': "g \<turnstile> cfg_entry g \<longrightarrow>\<^bsub>es\<^esub> v0"
    using entry_path unfolding g_def by simp
  have entry_in: "cfg_entry g \<in> solver.side_stabl_at v0"
    using side_vars_on_query_path[OF pp' fin entry_path'] by simp
  have entry_cov: "S \<subseteq> gamma_state
       (side_env (solver.side_sigma_at v0) (cfg_entry g))"
  proof -
    have local_le: "side_acc tf (\<squnion>) (bot0 \<squnion> restrict_local s0) (solver.side_sigma_at v0)
                     (predecessor_list g (cfg_entry g))
                   \<le> solver.side_sigma_at v0 (Inl (cfg_entry g))"
      using side_post_solution_le_local[OF pp' entry_in] unfolding g_def by simp
    have acc0_le: "bot0 \<squnion> restrict_local s0 \<le> solver.side_sigma_at v0 (Inl (cfg_entry g))"
      using side_acc_ge_acc local_le by (rule order_trans)
    have s0_le: "s0 \<le> bot0 \<squnion> restrict_local s0"
    proof (rule le_funI)
      fix x
      show "s0 x \<le> (bot0 \<squnion> restrict_local s0) x"
      proof (cases "is_global x")
        case True
        have "restrict_global s0 x = bot x"
          using s0_global_bot by (simp add: fun_eq_iff restrict_global_def)
        then show ?thesis using True unfolding restrict_global_def by simp
      next
        case False
        then show ?thesis unfolding restrict_local_def using sup_ge2 by simp
      qed
    qed
    have sigma_le: "s0 \<le> solver.side_sigma_at v0 (Inl (cfg_entry g))"
      using acc0_le s0_le by (auto intro: order_trans)
    have "s0 \<le> side_env (solver.side_sigma_at v0) (cfg_entry g)"
      unfolding side_env_def by (rule order_trans[OF sigma_le sup_ge1])
    thus ?thesis using S_sub gamma_state_mono by blast
  qed
  show ?thesis
  proof (rule side_analyse_collect_sound_at)
    show "part_post_solution (side_cfg_T (to_cfg c) tf (\<squnion>) bot0 s0) v0
          (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 v0)
          (td_cfg_side_solver.side_stabl_at (to_cfg c) tf bot0 s0 v0)"
      using pp' unfolding g_def by simp
    show "S \<subseteq> gamma_state
          (side_env (td_cfg_side_solver.side_sigma_at (to_cfg c) tf bot0 s0 v0)
                    (cfg_entry (to_cfg c)))"
      using entry_cov unfolding g_def by simp
    show "finite (edges (to_cfg c))" using fin_cfg .
    show "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v0" using entry_path .
    show "\<forall>x a sg. \<forall>s \<in> gamma_state sg.
          s(x := aval a s) \<in> gamma_state (tf_assign tf x a sg)"
      using tf_sound_assign .
    show "\<forall>b sg. \<forall>s \<in> gamma_state sg. bval b s
          \<longrightarrow> s \<in> gamma_state (tf_assume tf b sg)"
      using tf_sound_assume .
    show "\<forall>b sg. \<forall>s \<in> gamma_state sg. \<not> bval b s
          \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sg)"
      using tf_sound_assume_not .
    show "\<forall>sg. \<forall>s \<in> gamma_state sg.
          enter_state s \<in> gamma_state (tf_enter tf sg)"
      using tf_sound_enter .
  qed
qed

theorem side_analyse_collect_sound_solver:
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
  assumes tf_sound_enter:
    "\<forall>sg. \<forall>s \<in> gamma_state sg.
       enter_state s \<in> gamma_state (tf_enter tf sg)"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_reachable:
    "\<And>v. \<exists>es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
  assumes side_solve_dom:
    "\<And>v. side_cfg_solve_dom (to_cfg c) tf bot0 s0 v"
  assumes S_sub: "S \<subseteq> gamma_state s0"
  assumes s0_global_bot: "restrict_global s0 = bot"
  shows "\<forall>v. cfg_collect (to_cfg c) S v
         \<le> gamma_state (side_analyse c tf bot0 s0 v)"
proof (intro allI)
  fix v
  obtain es where entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
    using entry_reachable by blast
  show "cfg_collect (to_cfg c) S v
        \<le> gamma_state (side_analyse c tf bot0 s0 v)"
    by (rule side_analyse_collect_sound_at_solver[OF tf_sound_assign tf_sound_assume
          tf_sound_assume_not tf_sound_enter tf_mono fin_cfg entry_path side_solve_dom S_sub
          s0_global_bot])
qed

theorem side_solver_sound:
  fixes c :: com and tf :: "'a domain_transfer" and bot0 s0 :: "'a abs_state"
    and s t :: store and es :: "(edge_action * pp) list"
  assumes tf_sound_assign:
    "\<forall>x a sg. \<forall>s \<in> gamma_state sg.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sg)"
  assumes tf_sound_assume:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sg)"
  assumes tf_sound_assume_not:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sg)"
  assumes tf_sound_enter:
    "\<forall>sg. \<forall>s \<in> gamma_state sg.
       enter_state s \<in> gamma_state (tf_enter tf sg)"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes s0_sound: "s \<in> gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
  assumes side_solve_dom:
    "side_cfg_solve_dom (to_cfg c) tf bot0 s0 (cfg_exit (to_cfg c))"
  assumes s0_global_bot: "restrict_global s0 = bot"
  shows "t \<in> gamma_state (side_analyse c tf bot0 s0 (cfg_exit (to_cfg c)))"
proof -
  have S_sub: "{s} \<subseteq> gamma_state s0" using s0_sound by auto
  have collect: "cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))
    \<le> gamma_state (side_analyse c tf bot0 s0 (cfg_exit (to_cfg c)))"
    by (rule side_analyse_collect_sound_at_solver[OF tf_sound_assign tf_sound_assume
          tf_sound_assume_not tf_sound_enter tf_mono fin_cfg entry_path side_solve_dom S_sub
          s0_global_bot])
  show ?thesis using collect exit_in_collect by blast
qed

end

(* Domain instantiation: Domains/Sign_Side_Soundness.thy *)

end
