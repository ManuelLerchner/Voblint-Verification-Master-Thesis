theory TD_Soundness
  imports TD_Interface Constraint_System_Sound Sign_Domain Interval_Domain
begin

(*
  TD Solver Soundness (Fix B: per-pp solve).

  Combines:
    (1)  Per-pp TD env localized to queried node (TD_Interface)
    (2)  post_fixpoint_sound_at (Constraint_System_Sound)

  to obtain per-pp collecting soundness and exit-point corollaries.
*)

(* -- Combined Soundness ───────────────────────────────────────── *)

context sound_transfer
begin

theorem td_analyse_collect_sound_at:
  fixes v0
  assumes S_sub: "S \<le> gamma_state s0"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v0"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree (to_cfg c) tf (\<squnion>) bot s0) v0"
  shows "cfg_collect (to_cfg c) S v0
         \<le> gamma_state (td_analyse c tf (\<squnion>) bot s0 v0)"
proof -
  interpret plain: td_cfg_plain_solver "to_cfg c" tf "(\<squnion>)" bot s0 .
  define env where "env = plain.td_env_at v0"
  have cfi: "comp_fun_idem ((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    by (rule join_state_comp_fun_idem)
  have join_sym: "\<And>x y :: 'a abs_state. x \<squnion> y = y \<squnion> x"
    by (rule sup.commute)
  have join_is_sup: "(\<squnion>) = (\<squnion>)" by simp
  have bot_is_bot: "bot = bot" by simp
  have dom: "TD_plain.solve_dom plain.cfg_T v0"
    unfolding plain.cfg_T_def by (rule td_solve_dom)
  have v0_reach: "v0 \<in> reach plain.cfg_T (plain.td_sigma_at v0) v0"
    by (simp add: reach.base)
  have rhs_le: "rhs (to_cfg c) tf (\<squnion>) bot s0 env v0 \<le> env v0"
    using plain.td_env_at_rhs_le[OF fin_cfg cfi join_sym dom v0_reach]    by (simp add: env_def)
  have step_le:
    "\<And>u a w es'. cfg_path (to_cfg c) u ((a, w) # es') v0
     \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  proof -
    fix u a w es'
    assume p: "cfg_path (to_cfg c) u ((a, w) # es') v0"
    show "apply_tf tf a (env u) \<le> env w"
      using plain.td_env_at_path_step_le[OF fin_cfg cfi join_sym join_is_sup
        bot_is_bot dom p]
      by (simp add: env_def)
  qed
  have entry_le: "s0 \<le> env (cfg_entry (to_cfg c))"
    using plain.td_env_at_entry_le[OF fin_cfg cfi join_sym join_is_sup bot_is_bot
      dom entry_path]
    by (simp add: env_def)
  show ?thesis
    unfolding env_def td_analyse_eq_env_at
    using S_sub entry_le env_def fin_cfg post_fixpoint_sound_at rhs_le step_le by blast
qed

theorem td_analyse_collect_sound:
  assumes S_sub: "S \<le> gamma_state s0"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_reachable:
    "\<And>v. \<exists>es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom (make_rhs_tree (to_cfg c) tf (\<squnion>) bot s0) v"
  shows "\<forall>v. cfg_collect (to_cfg c) S v
         \<le> gamma_state (td_analyse c tf (\<squnion>) bot s0 v)"
proof (intro allI)
  fix v
  obtain es where entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
    using entry_reachable by blast
  show "cfg_collect (to_cfg c) S v
        \<le> gamma_state (td_analyse c tf (\<squnion>) bot s0 v)"
    by (rule td_analyse_collect_sound_at[OF S_sub fin_cfg entry_path td_solve_dom])
qed

theorem td_solver_sound:
  assumes s0_sound: "s \<in> gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom (make_rhs_tree (to_cfg c) tf (\<squnion>) bot s0) v"
  shows
    "t \<in> gamma_state ((td_analyse c tf (\<squnion>) bot s0)
                       (cfg_exit (to_cfg c)))"
proof -
  have S_sub: "{s} \<le> gamma_state s0"
    using s0_sound by auto
  have collect: "cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))
    \<le> gamma_state (td_analyse c tf (\<squnion>) bot s0 (cfg_exit (to_cfg c)))"
    by (rule td_analyse_collect_sound_at[OF S_sub fin_cfg entry_path td_solve_dom])
  show ?thesis using collect exit_in_collect by blast
qed

end

(* -- Sign Domain Instantiation --------------------------------- *)

theorem sign_analysis_sound:
  assumes s_sound:    "s \<in> sign_domain.gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot s0) v"
  shows   "t \<in> sign_domain.gamma_state
((td_analyse c sign_tf (\<squnion>) bot s0)
                   (cfg_exit (to_cfg c)))"
  by (rule sign_sound_tf.td_solver_sound
        [OF s_sound exit_in_collect fin_cfg entry_path td_solve_dom])

(* -- Interval Domain Instantiation ------------------------------ *)

theorem interval_analysis_sound:
  assumes s_sound:    "s \<in> ivl_domain.gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes entry_path:
    "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot s0) v"
  shows   "t \<in> ivl_domain.gamma_state
((td_analyse c ivl_tf (\<squnion>) bot s0)
                   (cfg_exit (to_cfg c)))"
  by (rule ivl_sound_tf.td_solver_sound
        [OF s_sound exit_in_collect fin_cfg entry_path td_solve_dom])

end
