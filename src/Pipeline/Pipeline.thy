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

  Canonical soundness: pipeline_invariant_sound / pipeline_sound_path
  (cfg_collect at every pp; no termination premise).

  Exit corollary pipeline_sound_runs_to: cfg_collect at exit implies t in gamma.
  Source-level runs_to framing: runs_to_def or sign_pipeline_sound / goblint_sign_sound.
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
           \<longrightarrow> s \<in> sound_domain.gamma_state gamma (tf_assume_not tf b sigma))
      \<and> (\<forall>sigma. \<forall>s \<in> sound_domain.gamma_state gamma sigma.
           enter_state s \<in> sound_domain.gamma_state gamma (tf_enter tf sigma)))"

lemma domain_transfer_sound_sound_transfer:
  assumes sound: "sound_domain gamma"
  assumes tf: "domain_transfer_sound gamma tf"
  shows "sound_transfer gamma tf"
proof -
  interpret sd: sound_domain gamma using sound .
  interpret st: sound_transfer gamma tf
  proof unfold_locales
    show "\<forall>x a sigma. \<forall>s \<in> sd.gamma_state sigma.
         s(x := aval a s) \<in> sd.gamma_state (tf_assign tf x a sigma)"
      using tf unfolding domain_transfer_sound_def sd.gamma_state_def by simp
    show "\<forall>b sigma. \<forall>s \<in> sd.gamma_state sigma. bval b s
         \<longrightarrow> s \<in> sd.gamma_state (tf_assume tf b sigma)"
      using tf unfolding domain_transfer_sound_def sd.gamma_state_def by simp
    show "\<forall>b sigma. \<forall>s \<in> sd.gamma_state sigma. \<not> bval b s
         \<longrightarrow> s \<in> sd.gamma_state (tf_assume_not tf b sigma)"
      using tf unfolding domain_transfer_sound_def sd.gamma_state_def by simp
    show "\<forall>sigma. \<forall>s \<in> sd.gamma_state sigma.
         enter_state s \<in> sd.gamma_state (tf_enter tf sigma)"
      using tf unfolding domain_transfer_sound_def sd.gamma_state_def by simp
  qed
  show ?thesis ..
qed

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

(* Canonical: pipeline_invariant_sound, pipeline_sound_path;
   exit corollary: pipeline_sound_runs_to. *)

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
                      tf_assume_not = assume_not_sign,
                      tf_enter     = enter_sign |),
        ac_init  = (\<lambda>x. sign_of_int (s x)) |)"

lemma sign_init_in_gamma:
  "s : sign_domain.gamma_state (ac_init (sign_analysis_config s))"
  unfolding sign_analysis_config_def sign_domain.gamma_state_def
  by (simp add: sign_of_int_gamma)

lemma sign_tf_sound:
  "domain_transfer_sound gamma_sign (ac_tf (sign_analysis_config s))"
  unfolding domain_transfer_sound_def sign_analysis_config_def
  by (auto simp: assign_sign_sound assume_sign_sound assume_not_sign_sound enter_sign_sound)


lemma sign_pipeline_sound:
  assumes runs: "runs_to c s t"
    and init_ok: "s \<in> sign_domain.gamma_state (ac_init (sign_analysis_config s))"
    and td_solve_dom:
      "\<And>v. TD_plain.solve_dom
         (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot
            (ac_init (sign_analysis_config s))) v"
  shows "t \<in> sign_domain.gamma_state
             (run_analysis (sign_analysis_config s) c (cfg_exit (to_cfg c)))"
proof -
  have run_eq: "run_analysis (sign_analysis_config s) c
    = td_analyse c sign_tf (\<squnion>) bot
                    (ac_init (sign_analysis_config s))"
    unfolding run_analysis_def sign_analysis_config_def sign_tf_def by simp
  from runs_to_imp_path[OF runs] obtain es where
    entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
    and _: "t \<in> edges_collect es {s}"
    by blast
  show ?thesis
    unfolding run_eq
    using runs_toD[OF runs]
    by (rule sign_analysis_sound[OF init_ok _ to_cfg_finite entry_path td_solve_dom])
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
                      tf_assume_not = assume_not_ivl,
                      tf_enter     = enter_ivl |),
        ac_init  = (\<lambda>x. Ivl (Fin (s x)) (Fin (s x))) |)"

lemma ivl_init_in_gamma:
  "s \<in> ivl_domain.gamma_state (ac_init (ivl_analysis_config s))"
  unfolding ivl_analysis_config_def ivl_domain.gamma_state_def
  by (simp add: eint_le_refl)

corollary ivl_pipeline_sound:
  assumes runs: "runs_to c s t"
    and td_solve_dom:
      "\<And>v. TD_plain.solve_dom
         (make_rhs_tree (to_cfg c) ivl_tf (\<squnion>) bot
            (ac_init (ivl_analysis_config s))) v"
  shows   "t \<in> ivl_domain.gamma_state
                  (run_analysis (ivl_analysis_config s) c
                     (cfg_exit (to_cfg c)))"
proof -
  have run_eq: "run_analysis (ivl_analysis_config s) c
    = td_analyse c ivl_tf (\<squnion>) bot
                    (ac_init (ivl_analysis_config s))"
    unfolding run_analysis_def ivl_analysis_config_def ivl_tf_def by simp
  from runs_to_imp_path[OF runs] obtain es where
    entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
    and _: "t \<in> edges_collect es {s}"
    by blast
  show ?thesis
    unfolding run_eq
    using runs_toD[OF runs]
    by (rule interval_analysis_sound
          [OF ivl_init_in_gamma _ to_cfg_finite entry_path td_solve_dom])
qed

(* Point-map invariant (td_analyse_collect_sound, Fix B per-pp). *)
theorem pipeline_invariant_sound:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes entry_reachable:
    "\<And>v. \<exists>es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg)) v"
  shows   "\<forall>v. cfg_collect (to_cfg c) {s} v \<le>
                    sound_domain.gamma_state (ac_gamma cfg)
                      (run_analysis cfg c v)"
proof -
  interpret sd: sound_domain "ac_gamma cfg"
    using sound .
  interpret st: sound_transfer "ac_gamma cfg" "ac_tf cfg"
    by (rule domain_transfer_sound_sound_transfer[OF sound tf_sound])
  have je: "ac_join cfg = ((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    unfolding sup_fun_def using join_eq by simp
  have be: "ac_bot cfg = (bot :: 'a abs_state)"
    unfolding bot_fun_def using bot_eq by simp
  have dom':
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (\<squnion>) bot (ac_init cfg)) v"
    using td_solve_dom unfolding je be by simp
  have S_sub: "{s} \<le> sd.gamma_state (ac_init cfg)"
    using s_in_gamma by auto
  show ?thesis
    unfolding run_analysis_def je be
    by (rule st.td_analyse_collect_sound[OF S_sub to_cfg_finite entry_reachable dom'])
qed
(* -- Pipeline Soundness (Per-pp, path-based) -----------------------------

   Per-program-point soundness, the canonical top-level result.

   Statement: at every program point v reachable via a CFG path from the
   entry, every store t obtainable from {s} along that path is concretized
   by the analyzer's abstract value at v.  No termination premise; holds
   at intermediate program points, not just the exit.  Direct consequence
   of `pipeline_invariant_sound` + `path_sound_cfg_collect`.

   `pipeline_sound_runs_to` below is the exit-only corollary for consumers
   that want the source-level ``c runs s to t'' framing.
*)
theorem pipeline_sound_path:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg)) v"
  assumes path:     "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
  assumes t_in:     "t \<in> edges_collect es {s}"
  shows "t \<in> sound_domain.gamma_state (ac_gamma cfg) (run_analysis cfg c v)"
proof -
  interpret sd: sound_domain "ac_gamma cfg"
    using sound .
  interpret st: sound_transfer "ac_gamma cfg" "ac_tf cfg"
    by (rule domain_transfer_sound_sound_transfer[OF sound tf_sound])
  have je: "ac_join cfg = ((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    unfolding sup_fun_def using join_eq by simp
  have be: "ac_bot cfg = (bot :: 'a abs_state)"
    unfolding bot_fun_def using bot_eq by simp
  have S_sub: "{s} \<le> sd.gamma_state (ac_init cfg)"
    using s_in_gamma by auto
  have dom': "TD_plain.solve_dom
      (make_rhs_tree (to_cfg c) (ac_tf cfg) (\<squnion>) bot (ac_init cfg)) v"
    using td_solve_dom unfolding je be by simp
  have collect: "cfg_collect (to_cfg c) {s} v
    \<le> sd.gamma_state (run_analysis cfg c v)"
    unfolding run_analysis_def je be
    by (rule st.td_analyse_collect_sound_at[OF S_sub to_cfg_finite path dom'])
  have t_in_cfg: "t \<in> cfg_collect (to_cfg c) {s} v"
    using path_sound_cfg_collect[OF path] t_in by blast
  show ?thesis using collect t_in_cfg by blast
qed


(* -- Pipeline Soundness (runs_to exit corollary) --------------------------

   Exit corollary of pipeline_invariant_sound: membership in cfg_collect at
   exit implies the analyzer's exit env covers t. Primary spec premise
   (not runs_to). For runs_to c s t use runs_to_def once, or the
   sign/interval pipeline lemmas that keep runs_to for examples.
*)
theorem pipeline_sound_runs_to:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg)) v"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  shows "t \<in> sound_domain.gamma_state (ac_gamma cfg)
                  (run_analysis cfg c (cfg_exit (to_cfg c)))"
proof -
  interpret sd: sound_domain "ac_gamma cfg"
    using sound .
  interpret st: sound_transfer "ac_gamma cfg" "ac_tf cfg"
    by (rule domain_transfer_sound_sound_transfer[OF sound tf_sound])
  have je: "ac_join cfg = ((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    unfolding sup_fun_def using join_eq by simp
  have be: "ac_bot cfg = (bot :: 'a abs_state)"
    unfolding bot_fun_def using bot_eq by simp
  have S_sub: "{s} \<le> sd.gamma_state (ac_init cfg)"
    using s_in_gamma by auto
  from exit_in_collect
  have path_mem: "t \<in> cfg_collect_paths (to_cfg c) {s} (cfg_exit (to_cfg c))"
    by (simp add: cfg_collect_eq_cfg_collect_paths[symmetric])
  obtain es where entry_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
    and _: "t \<in> edges_collect es {s}"    using path_mem unfolding cfg_collect_paths_def by auto
  have dom': "TD_plain.solve_dom
      (make_rhs_tree (to_cfg c) (ac_tf cfg) (\<squnion>) bot (ac_init cfg)) (cfg_exit (to_cfg c))"
    using td_solve_dom unfolding je be by simp
  have collect: "cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))
    \<le> sd.gamma_state (run_analysis cfg c (cfg_exit (to_cfg c)))"
    unfolding run_analysis_def je be
    by (rule st.td_analyse_collect_sound_at[OF S_sub to_cfg_finite entry_path dom'])
  show ?thesis using collect exit_in_collect by blast
qed

corollary pipeline_sound_runs_to_runs:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg)) v"
  assumes runs: "runs_to c s t"
  shows "t \<in> sound_domain.gamma_state (ac_gamma cfg)
                  (run_analysis cfg c (cfg_exit (to_cfg c)))"
  using runs runs_toD pipeline_sound_runs_to[OF sound join_eq bot_eq tf_sound s_in_gamma
          td_solve_dom]
  by blast

theorem sign_pipeline_invariant_sound:
  assumes tf_ok:   "domain_transfer_sound gamma_sign (ac_tf (sign_analysis_config s))"
  assumes init_ok: "s \<in> sign_domain.gamma_state (ac_init (sign_analysis_config s))"
  assumes entry_reachable:
    "\<And>v. \<exists>es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es v"
  assumes td_solve_dom:
    "\<And>v. TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) (ac_tf (sign_analysis_config s))
          (ac_join (sign_analysis_config s)) (ac_bot (sign_analysis_config s))
          (ac_init (sign_analysis_config s))) v"
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
    by (rule pipeline_invariant_sound[OF sound je be tf_ok' init_ok' entry_reachable
              td_solve_dom])
  show ?thesis using inv by (simp add: gs_eq)
qed

end
