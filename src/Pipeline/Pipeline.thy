theory Pipeline
  imports TD_Soundness Sign_Domain Interval_Domain
begin

(*
  Full Analysis Pipeline.

  This theory assembles the complete end-to-end pipeline:

    IMP2 source  --[to_cfg]\<longrightarrow>  CFG
                 --[rhs]-----\<longrightarrow>  Constraint System
                 --[td_solve]\<longrightarrow>  Fixed-Point Environment
                 --[gamma]---\<longrightarrow>  State-Set Overapproximation

  The pipeline is parameterised over an abstract domain.
  Concrete instantiations for Sign and Interval are provided below.

  Top-level soundness theorem:
    For any domain D with verified transfer functions, if program c is run
    from initial store s (with s in gamma(sigma_0) for some initial abstraction
    sigma_0), and c terminates in t, then t in gamma(sigma_exit).
*)

(* ── Transfer-Function Soundness Bundle ──────────────────────── *)
(*
  Packages the three soundness conditions for domain transfer functions
  into a single predicate, parameterised over a concretisation gamma.
*)

definition domain_transfer_sound ::
    "('a::bounded_semilattice_sup_bot => int set)
     => 'a domain_transfer
     => bool"
where
  "domain_transfer_sound gamma tf =
     ((\<forall>x a sigma. \<forall>s \<in> sound_domain.gamma_state gamma sigma.
         s(x := aval a s) \<in> sound_domain.gamma_state gamma (tf_assign tf x a sigma))
      \<and> (\<forall>b sigma. \<forall>s \<in> sound_domain.gamma_state gamma sigma. bval b s
           \<longrightarrow> s \<in> sound_domain.gamma_state gamma (tf_assume tf b sigma))
      \<and> (\<forall>b sigma. \<forall>s \<in> sound_domain.gamma_state gamma sigma. \<not> bval b s
           \<longrightarrow> s \<in> sound_domain.gamma_state gamma (tf_assume_not tf b sigma)))"

(* ── Generic Pipeline Record ──────────────────────────────────── *)
(*
  Bundle everything needed to run an analysis:
    - the abstract domain operations
    - the transfer functions
    - the initial abstract store
*)

record 'a analysis_config =
  ac_join     :: "'a abs_state => 'a abs_state => 'a abs_state"
  ac_bot      :: "'a abs_state"
  ac_gamma    :: "'a => int set"
  ac_tf       :: "'a domain_transfer"
  ac_init     :: "'a abs_state"

(* ── Run the Pipeline ─────────────────────────────────────────── *)

definition run_analysis ::
    "('a::bounded_semilattice_sup_bot) analysis_config => com => pp => 'a abs_state"
where
  "run_analysis cfg c =
     td_analyse c
       (ac_tf cfg)
       (ac_join cfg)
       (ac_bot cfg)
       (ac_init cfg)"

(* ── Pipeline Soundness (Generic) ────────────────────────────── *)
(*
  The main theorem of the thesis:
    If the transfer functions in cfg are sound with respect to gamma,
    and the initial concrete store s is in gamma(ac_init cfg),
    and program c terminates in t,
    then t is in gamma(run_analysis cfg c (exit of c)).
*)

(* pipeline_sound is the cfg_exit specialisation of pipeline_invariant_sound
   plus termination proven below the invariant theorem. *)

(* ── Sign Analysis Pipeline ───────────────────────────────────── *)
(*
  Concrete analysis using the Sign domain.
*)

definition sign_analysis_config :: "store => sign analysis_config" where
  "sign_analysis_config s =
     (| ac_join  = ((\<squnion>) :: sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state),
        ac_bot   = (bot :: sign abs_state),
        ac_gamma = gamma_sign,
        ac_tf    = (| tf_assign    = assign_sign,
                      tf_assume    = assume_sign,
                      tf_assume_not = assume_not_sign |),
        ac_init  = (\<lambda>x. sign_of_int (s x)) |)"

text \<open>
  Scaffold: reduce sign pipeline soundness to the generic pipeline theorem at
  @{const sign_analysis_config}; discharge Sign TF lemmas (Phase I) and
  @{const sign_of_int} / @{const gamma_sign} for the initial store.
\<close>

lemma sign_analysis_init_in_gamma_stub:
  "s : sign_domain.gamma_state (ac_init (sign_analysis_config s))"
  unfolding sign_analysis_config_def sign_domain.gamma_state_def
  by (simp add: sign_of_int_gamma)

lemma sign_analysis_tf_sound_stub:
  "domain_transfer_sound gamma_sign (ac_tf (sign_analysis_config s))"
  unfolding domain_transfer_sound_def sign_analysis_config_def
  by (simp add: assign_sign_sound assume_sign_sound)


lemma sign_pipeline_sound_scaffold:
  assumes runs: "big_step (c, s) t"
    and init_ok: "s \<in> sign_domain.gamma_state (ac_init (sign_analysis_config s))"
    and join_cfi:
      "comp_fun_idem ((\<squnion>) ::
         sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state)"
    and td_solve_dom:
      "TD_plain.solve_dom
         (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot
            (ac_init (sign_analysis_config s)))
         (cfg_entry (to_cfg c))"
    and td_cfg_in_reach:
      "\<And>v::pp. v \<in> reach
         (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot
            (ac_init (sign_analysis_config s)))
         (TD_plain_Interp_solve
            (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot
              (ac_init (sign_analysis_config s)))
            (cfg_entry (to_cfg c)))
         (cfg_entry (to_cfg c))"
  shows "t \<in> sign_domain.gamma_state
             (run_analysis (sign_analysis_config s) c (cfg_exit (to_cfg c)))"
proof -
  have run_eq: "run_analysis (sign_analysis_config s) c
    = td_analyse c sign_tf (\<squnion>) bot
                    (ac_init (sign_analysis_config s))"
    unfolding run_analysis_def sign_analysis_config_def sign_tf_def by simp
  show ?thesis
    unfolding run_eq
    by (rule sign_analysis_sound[OF init_ok runs join_cfi td_solve_dom td_cfg_in_reach])
qed

(* ── Interval Analysis Pipeline ──────────────────────────────── *)
(*
  Concrete analysis using the Interval domain.
*)

definition ivl_analysis_config :: "store => ivl analysis_config" where
  "ivl_analysis_config s =
     (| ac_join  = ((\<squnion>) :: ivl abs_state \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state),
        ac_bot   = (bot :: ivl abs_state),
        ac_gamma = gamma_ivl,
        ac_tf    = (| tf_assign    = assign_ivl,
                      tf_assume    = assume_ivl,
                      tf_assume_not = assume_not_ivl |),
        ac_init  = (\<lambda>x. Ivl (Fin (s x)) (Fin (s x))) |)"

(*
  Same structure as sign_pipeline_sound.
  Requires ivl TF soundness + init soundness (analogues of the sign stubs).
  Those must be proved before this corollary can be closed.
*)
lemma ivl_analysis_init_in_gamma_stub:
  "s \<in> ivl_domain.gamma_state (ac_init (ivl_analysis_config s))"
  unfolding ivl_analysis_config_def ivl_domain.gamma_state_def
  by (simp add: eint_le_refl)

corollary ivl_pipeline_sound:
  assumes runs: "big_step (c, s) t"
    and join_cfi:
      "comp_fun_idem ((\<squnion>) ::
         ivl abs_state \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state)"
    and td_solve_dom:
      "TD_plain.solve_dom
         (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot
            (ac_init (ivl_analysis_config s)))
         (cfg_entry (to_cfg c))"
    and td_cfg_in_reach:
      "\<And>v::pp. v \<in> reach
         (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot
            (ac_init (ivl_analysis_config s)))
         (TD_plain_Interp_solve
            (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot
              (ac_init (ivl_analysis_config s)))
            (cfg_entry (to_cfg c)))
         (cfg_entry (to_cfg c))"
  shows   "t \<in> ivl_domain.gamma_state
                  (run_analysis (ivl_analysis_config s) c
                     (cfg_exit (to_cfg c)))"
proof -
  have run_eq: "run_analysis (ivl_analysis_config s) c
    = td_analyse c ivl_tf (\<squnion>) bot
                    (ac_init (ivl_analysis_config s))"
    unfolding run_analysis_def ivl_analysis_config_def ivl_tf_def by simp
  show ?thesis
    unfolding run_eq
    by (rule interval_analysis_sound
          [OF ivl_analysis_init_in_gamma_stub runs join_cfi
              td_solve_dom td_cfg_in_reach])
qed

(* ── Option 2: Point-Map Invariant (Recommended Presentation) ── *)
(*
  Stronger than pipeline_sound: the abstract store at EVERY program point
  is a sound invariant, not just at the exit.

  This falls out for free from post_fixpoint_sound + td_analyse_post_fixpoint:
    td_analyse_post_fixpoint  \<rightarrow>  is_post_fixpoint ... (run_analysis cfg c)
    post_fixpoint_sound       \<rightarrow>  \<forall>v. cfg_collect g {s} v \<subseteq> gamma_state (env v)
  Exit soundness (pipeline_sound) is the v = cfg_exit special case.

  This is what supervisors requested in meeting 2:
    "point-map soundness predicate: \<forall> p. collect_sem_at c p \<subseteq> \<gamma>(mlup \<sigma> p)"
*)

(*
  Point-map invariant: the solver result is sound at EVERY program point.
  Does NOT require termination holds for all starting states s in gamma(init).
  The terminates assumption was removed; it is unused (the \<forall>v conclusion
  does not depend on any specific execution reaching exit).
*)
theorem pipeline_invariant_sound:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes cfi:        "comp_fun_idem (ac_join cfg)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (TD_plain_Interp_solve
          (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
          (cfg_entry (to_cfg c)))
       (cfg_entry (to_cfg c))"
  shows   "\<forall>v. cfg_collect (to_cfg c) {s} v \<le>
                    sound_domain.gamma_state (ac_gamma cfg)
                      (run_analysis cfg c v)"
proof -
  interpret sd: sound_domain "ac_gamma cfg"
    using sound .
  have join_eq': "ac_join cfg = ((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    unfolding sup_fun_def using join_eq by simp
  have bot_eq':  "ac_bot cfg = (bot :: 'a abs_state)"
    unfolding bot_fun_def using bot_eq by simp
  have join_sym: "\<And>x y. ac_join cfg x y = ac_join cfg y x"
    unfolding join_eq using sup_commute by (auto simp: fun_eq_iff)
  have pfp: "is_post_fixpoint (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg)
              (ac_init cfg) (run_analysis cfg c)"
    unfolding run_analysis_def
    by (rule td_analyse_post_fixpoint[OF to_cfg_finite cfi join_sym
              td_solve_dom td_cfg_in_reach])
  have pfp': "is_post_fixpoint (to_cfg c) (ac_tf cfg) (\<squnion>) bot
              (ac_init cfg) (run_analysis cfg c)"
    using pfp join_eq' bot_eq' by simp
  have S_sub: "{s} \<le> sd.gamma_state (ac_init cfg)"
    using s_in_gamma by blast
  from tf_sound have ta: "\<forall>x a sigma. \<forall>s \<in> sd.gamma_state sigma.
              s(x := aval a s) \<in> sd.gamma_state (tf_assign (ac_tf cfg) x a sigma)"
    unfolding domain_transfer_sound_def by blast
  from tf_sound have tb: "\<forall>b sigma. \<forall>s \<in> sd.gamma_state sigma.
              bval b s \<longrightarrow> s \<in> sd.gamma_state (tf_assume (ac_tf cfg) b sigma)"
    unfolding domain_transfer_sound_def by blast
  from tf_sound have tn: "\<forall>b sigma. \<forall>s \<in> sd.gamma_state sigma.
              \<not> bval b s \<longrightarrow> s \<in> sd.gamma_state (tf_assume_not (ac_tf cfg) b sigma)"
    unfolding domain_transfer_sound_def by blast
  show ?thesis
    by (rule sd.post_fixpoint_sound[OF to_cfg_finite pfp' S_sub ta tb tn])
qed

(* -- Pipeline Soundness (Per-pp, path-based) -----------------------------

   Per-program-point soundness without any big-step assumption.

   Statement: at every program point v reachable via a CFG path from the
   entry, every store t obtainable from {s} along that path is concretized
   by the analyzer's abstract value at v.

   This is the canonical small-step-flavoured top-level result:
     * no `(c, s) \<Rightarrow> t` premise;
     * holds at intermediate program points, not just the exit;
     * direct consequence of `pipeline_invariant_sound` +
       `path_sound_cfg_collect`.

   The big-step `pipeline_sound` and the small-step `pipeline_sound_small_step`
   are derived as exit-only corollaries below.
*)
theorem pipeline_sound_path:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes cfi:        "comp_fun_idem (ac_join cfg)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (TD_plain_Interp_solve
          (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
          (cfg_entry (to_cfg c)))
       (cfg_entry (to_cfg c))"
  assumes path:     "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
  assumes t_in:     "t \<in> edges_collect es {s}"
  shows "t \<in> sound_domain.gamma_state (ac_gamma cfg) (run_analysis cfg c v)"
proof -
  have inv: "\<forall>v. cfg_collect (to_cfg c) {s} v \<le>
                  sound_domain.gamma_state (ac_gamma cfg) (run_analysis cfg c v)"
    by (rule pipeline_invariant_sound[OF sound join_eq bot_eq tf_sound s_in_gamma
              cfi td_solve_dom td_cfg_in_reach])
  have t_in_cfg: "t \<in> cfg_collect (to_cfg c) {s} v"
    using path_sound_cfg_collect[OF path] t_in by blast
  from inv[rule_format, of v] t_in_cfg show ?thesis by blast
qed


(* -- Pipeline Soundness (Big-step exit corollary) -------------------------

   Reconstructs the original big-step soundness statement as a corollary
   of `pipeline_sound_path` via `big_step_cfg_path`. Kept for consumers
   that prefer the `(c,s) \<Rightarrow> t` formulation (Hoare-style specs,
   code-extraction demos).
*)
theorem pipeline_sound:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes cfi:        "comp_fun_idem (ac_join cfg)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (TD_plain_Interp_solve
          (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
          (cfg_entry (to_cfg c)))
       (cfg_entry (to_cfg c))"
  assumes terminates: "(c, s) \<Rightarrow> t"
  shows "t \<in> sound_domain.gamma_state (ac_gamma cfg)
                  (run_analysis cfg c (cfg_exit (to_cfg c)))"
proof -
  obtain es where
    es:   "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))" and
    t_in: "t \<in> edges_collect es {s}"
    using big_step_cfg_path[OF terminates, of "{s}"] by auto
  show ?thesis
    by (rule pipeline_sound_path[OF sound join_eq bot_eq tf_sound s_in_gamma
              cfi td_solve_dom td_cfg_in_reach es t_in])
qed


(* -- Pipeline Soundness (Small-step exit corollary) -----------------------

   Small-step formulation of the exit soundness: replace the big-step
   premise `(c, s) \<Rightarrow> t` by the small-step trace `(c, s) \<rightarrow>* (SKIP, t)`.

   Derivation is a one-line rewrite via `small_step_big_step_eq`. Useful
   when downstream proofs are themselves operational/small-step.
*)
theorem pipeline_sound_small_step:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes cfi:        "comp_fun_idem (ac_join cfg)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (TD_plain_Interp_solve
          (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
          (cfg_entry (to_cfg c)))
       (cfg_entry (to_cfg c))"
  assumes reaches: "(c, s) \<rightarrow>* (SKIP, t)"
  shows "t \<in> sound_domain.gamma_state (ac_gamma cfg)
                  (run_analysis cfg c (cfg_exit (to_cfg c)))"
proof -
  from reaches small_step_big_step_eq have bs: "(c, s) \<Rightarrow> t" by blast
  show ?thesis
    by (rule pipeline_sound[OF sound join_eq bot_eq tf_sound s_in_gamma
              cfi td_solve_dom td_cfg_in_reach bs])
qed

(*
  Sign-domain specialisation.  Hypotheses must match pipeline_invariant_sound:
  TF soundness + s \<in> gamma(init).  The (c,s)\<Rightarrow>t assumption was superfluous.
*)
theorem sign_pipeline_invariant_sound:
  assumes tf_ok:   "domain_transfer_sound gamma_sign (ac_tf (sign_analysis_config s))"
  assumes init_ok: "s \<in> sign_domain.gamma_state (ac_init (sign_analysis_config s))"
  assumes cfi:     "comp_fun_idem (ac_join (sign_analysis_config s)
                      :: sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf (sign_analysis_config s))
          (ac_join (sign_analysis_config s)) (ac_bot (sign_analysis_config s))
          (ac_init (sign_analysis_config s)))
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
       (make_rhs_tree (to_cfg c) (ac_tf (sign_analysis_config s))
          (ac_join (sign_analysis_config s)) (ac_bot (sign_analysis_config s))
          (ac_init (sign_analysis_config s)))
       (TD_plain_Interp_solve
          (make_rhs_tree (to_cfg c) (ac_tf (sign_analysis_config s))
            (ac_join (sign_analysis_config s)) (ac_bot (sign_analysis_config s))
            (ac_init (sign_analysis_config s)))
          (cfg_entry (to_cfg c)))
       (cfg_entry (to_cfg c))"
  shows   "\<forall>v. cfg_collect (to_cfg c) {s} v \<le>
                    sign_domain.gamma_state
                      (run_analysis (sign_analysis_config s) c v)"
proof -
  have ge: "ac_gamma (sign_analysis_config s) = gamma_sign"
    unfolding sign_analysis_config_def by simp
  have sound: "sound_domain (ac_gamma (sign_analysis_config s))"
    unfolding ge by (rule sign_domain.sound_domain_axioms)
  have je: "ac_join (sign_analysis_config s)
            = (\<lambda>s1 s2 x. s1 x \<squnion> s2 x)"
    unfolding sign_analysis_config_def sup_fun_def by simp
  have be: "ac_bot (sign_analysis_config s) = (\<lambda>_. bot)"
    unfolding sign_analysis_config_def by (simp add: bot_fun_def)
  have gs_eq: "sign_domain.gamma_state
             = sound_domain.gamma_state (ac_gamma (sign_analysis_config s))"
    unfolding ge sign_domain.gamma_state_def sound_domain.gamma_state_def[OF sound[unfolded ge]]
    by simp
  have init_ok': "s \<in> sound_domain.gamma_state (ac_gamma (sign_analysis_config s))
                       (ac_init (sign_analysis_config s))"
    using init_ok by (simp add: gs_eq)
  have tf_ok': "domain_transfer_sound (ac_gamma (sign_analysis_config s))
                  (ac_tf (sign_analysis_config s))"
    using tf_ok by (simp add: ge)
  have inv: "\<forall>v. cfg_collect (to_cfg c) {s} v \<le>
             sound_domain.gamma_state (ac_gamma (sign_analysis_config s))
                (run_analysis (sign_analysis_config s) c v)"
    by (rule pipeline_invariant_sound[OF sound je be tf_ok' init_ok'
              cfi td_solve_dom td_cfg_in_reach])
  show ?thesis using inv by (simp add: gs_eq)
qed

end
