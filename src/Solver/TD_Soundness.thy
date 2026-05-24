theory TD_Soundness
  imports TD_Interface Constraint_System_Sound Sign_Domain Interval_Domain
begin

(*
  TD Solver Soundness.

  Combines:
    (1)  TD solver produces a post-fixpoint         (TD_Interface.td_analyse_post_fixpoint)
    (2)  Post-fixpoints overapproximate reachability (Constraint_System_Sound.post_fixpoint_sound)

  to obtain exit-point soundness:

    If s0 is in gamma(env_entry) and t is in cfg_collect at the exit,
    then t is in gamma(env_exit).

  where env = td_analyse c tf ...
*)

(* ── Combined Soundness ───────────────────────────────────────── *)

context abstract_domain
begin

theorem td_solver_sound:
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  assumes s0_sound:
    "s \<in> gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  assumes fin_cfg: "finite (edges (to_cfg c))"
  assumes sup_cfi:
    "comp_fun_idem ((\<squnion>) :: 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree (to_cfg c) tf (\<squnion>) bot s0)
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach (make_rhs_tree (to_cfg c) tf (\<squnion>) bot s0)
                    (TD_plain_Interp_solve (make_rhs_tree (to_cfg c) tf (\<squnion>) bot s0)
                      (cfg_entry (to_cfg c)))
                    (cfg_entry (to_cfg c))"
  shows
    "t \<in> gamma_state ((td_analyse c tf (\<squnion>) bot s0)
                       (cfg_exit (to_cfg c)))"
proof -
  have post_fp: "is_post_fixpoint (to_cfg c) tf (\<squnion>) bot s0
                   (td_analyse c tf (\<squnion>) bot s0)"
    by (rule td_analyse_post_fixpoint[OF fin_cfg sup_cfi sup_commute
          td_solve_dom td_cfg_in_reach])
  show ?thesis
    by (rule exit_sound[OF post_fp order.refl tf_sound_assign tf_sound_assume
          tf_sound_assume_not s0_sound exit_in_collect])
qed

end

(* ── Sign Domain Instantiation ────────────────────────────────── *)

theorem sign_analysis_sound:
  assumes s_sound:    "s \<in> sign_domain.gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
assumes sup_cfi:
    "comp_fun_idem ((\<squnion>) ::
       sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot s0)
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
                  (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot s0)
                  (TD_plain_Interp_solve
                     (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot s0)
                     (cfg_entry (to_cfg c)))
                  (cfg_entry (to_cfg c))"
  shows   "t \<in> sign_domain.gamma_state
                 ((td_analyse c sign_tf (\<squnion>) bot s0)
                   (cfg_exit (to_cfg c)))"
proof -
  have h1: "\<forall>x a sigma. \<forall>s \<in> sign_domain.gamma_state sigma.
              s(x := aval a s) \<in> sign_domain.gamma_state (tf_assign sign_tf x a sigma)"
    unfolding sign_tf_def by (simp add: assign_sign_sound)
  have h2: "\<forall>b sigma. \<forall>s \<in> sign_domain.gamma_state sigma.
              bval b s \<longrightarrow> s \<in> sign_domain.gamma_state (tf_assume sign_tf b sigma)"
    unfolding sign_tf_def by (simp add: assume_sign_sound)
  have h3: "\<forall>b sigma. \<forall>s \<in> sign_domain.gamma_state sigma.
              \<not> bval b s \<longrightarrow> s \<in> sign_domain.gamma_state (tf_assume_not sign_tf b sigma)"
    unfolding sign_tf_def by (simp add: assume_not_sign_sound)
  show ?thesis
    by (rule sign_domain.td_solver_sound
          [OF h1 h2 h3 s_sound exit_in_collect to_cfg_finite sup_cfi
              td_solve_dom td_cfg_in_reach])
qed

(* ── Interval Domain Instantiation ───────────────────────────── *)

theorem interval_analysis_sound:
  assumes s_sound:    "s \<in> ivl_domain.gamma_state s0"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
assumes sup_cfi:
    "comp_fun_idem ((\<squnion>) ::
       ivl abs_state \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot s0)
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
                  (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot s0)
                  (TD_plain_Interp_solve
                     (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot s0)
                     (cfg_entry (to_cfg c)))
                  (cfg_entry (to_cfg c))"
  shows   "t \<in> ivl_domain.gamma_state
                 ((td_analyse c ivl_tf (\<squnion>) bot s0)
                   (cfg_exit (to_cfg c)))"
proof -
  have h1: "\<forall>x a sigma. \<forall>s \<in> ivl_domain.gamma_state sigma.
              s(x := aval a s) \<in> ivl_domain.gamma_state (tf_assign ivl_tf x a sigma)"
    unfolding ivl_tf_def by (simp add: assign_ivl_sound)
  have h2: "\<forall>b sigma. \<forall>s \<in> ivl_domain.gamma_state sigma.
              bval b s \<longrightarrow> s \<in> ivl_domain.gamma_state (tf_assume ivl_tf b sigma)"
    unfolding ivl_tf_def by simp
  have h3: "\<forall>b sigma. \<forall>s \<in> ivl_domain.gamma_state sigma.
              \<not> bval b s \<longrightarrow> s \<in> ivl_domain.gamma_state (tf_assume_not ivl_tf b sigma)"
    unfolding ivl_tf_def by simp
  show ?thesis
    by (rule ivl_domain.td_solver_sound
          [OF h1 h2 h3 s_sound exit_in_collect to_cfg_finite sup_cfi
              td_solve_dom td_cfg_in_reach])
qed

end
