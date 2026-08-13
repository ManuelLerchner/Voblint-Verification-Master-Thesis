theory Interval_Checks
  imports Interval_Numeric_Queries Interval_Backward "Voblint_Core.Abstract_Checks"
    Interval_Exec_Sound
begin

hide_const phase.N

section \<open>Interval instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here, mirroring \<open>Sign_Checks\<close>: the Interval bound
  tables (\<open>interval_less_true\<close>/\<open>interval_less_false\<close>/\<open>interval_eq_true\<close>/
  \<open>interval_eq_false\<close>) and their \<open>Interval_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Interval expression
  evaluator \<open>aval_ivl\<close> lives in \<open>Interval_Backward\<close>. The Boolean recursion over
  \<^typ>\<open>bexp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from interpreting
  \<open>abstract_check_domain\<close> once, below, reusing the numeric-query facts
  already proved sound in \<open>interval_numeric_queries\<close> rather than re-deriving
  the comparison tables --- the same way \<open>ivl_backward_domain\<close> in
  \<open>Interval_Backward.thy\<close> interprets \<open>backward_domain\<close> for guard narrowing.
\<close>

global_interpretation interval_check_domain:
  abstract_check_domain gamma_ivl interval_less_true interval_less_false interval_eq_true
    interval_eq_false gamma_state aval_ivl
  defines
    interval_check_true = interval_check_domain.check_true
    and interval_check_false = interval_check_domain.check_false
    and interval_classify_check = interval_check_domain.classify_check
    and interval_checks_proven = interval_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: aexp and \<sigma> :: "ivl abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_ivl (aval_ivl e \<sigma>)" using aval_ivl_sound by blast
qed

text \<open>
  Only the consumer-facing aliases get a short Interval-prefixed name, the
  same choice \<open>Sign_Checks\<close> makes: \<open>classify_check\<close>'s two directions and the
  \<open>checks_proven\<close> bridge, both exercised by the worked example. The lower-
  level \<open>check_true_sound\<close>/\<open>check_false_sound\<close>/\<open>check_true_false_vacuous\<close>
  facts \<open>classify_check\<close>'s own soundness is built from stay reachable under
  the qualified \<open>interval_check_domain.\<close> name instead of a dedicated alias
  here.
\<close>

lemmas interval_classify_check_proved = interval_check_domain.classify_check_proved
lemmas interval_classify_check_refuted = interval_check_domain.classify_check_refuted
lemmas interval_checks_provenI = interval_check_domain.abstract_checks_provenI
lemmas interval_checks_proven_sound = interval_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>ivl_top\<close>) environment, so each test exercises exactly the comparison it
  names, and one showing the precision gain over Sign: a bounded range proves
  both a wider upper bound and a tighter lower bound in one classification,
  which Sign's four-value lattice cannot distinguish from \<open>STop\<close>.\<close>

definition test_env_bounded :: "ivl abs_state" where
  "test_env_bounded = (\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 4) (Fin 7))"

lemma interval_classify_less_proved:
  "interval_classify_check (Less (V (STR ''x'')) (N 11)) test_env_bounded = Check_Proved"
  unfolding test_env_bounded_def by eval

lemma interval_classify_less_refuted:
  "interval_classify_check (Less (V (STR ''x'')) (N 0)) test_env_bounded = Check_Refuted"
  unfolding test_env_bounded_def by eval

lemma interval_classify_eq_unknown:
  "interval_classify_check (Eq (V (STR ''x'')) (N 5)) test_env_bounded = Check_Unknown"
  unfolding test_env_bounded_def by eval

text \<open>The precision gain over Sign: \<open>0 < x\<close> and \<open>x < 8\<close> both hold outright
  once \<open>x\<close> is known to lie strictly between \<open>3\<close> and \<open>8\<close> --- a fact only a
  domain that tracks numeric bounds can prove; Sign's \<open>SPos\<close>/\<open>SNonNeg\<close> would
  classify \<open>x < 8\<close> \<^term>\<open>Check_Unknown\<close> on the same information.\<close>

definition test_env_precision :: "ivl abs_state" where
  "test_env_precision = (\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 4) (Fin 7))"

lemma interval_classify_precision_lower_proved:
  "interval_classify_check (Less (N 2) (V (STR ''x''))) test_env_precision = Check_Proved"
  unfolding test_env_precision_def by eval

lemma interval_classify_precision_upper_proved:
  "interval_classify_check (Less (V (STR ''x'')) (N 9)) test_env_precision = Check_Proved"
  unfolding test_env_precision_def by eval

subsection \<open>Whole-program check report\<close>

text \<open>Thin composition, mirroring \<open>sign_check_report\<close>: \<^const>\<open>classify_checks\<close>
  owns the traversal and ordering, \<^const>\<open>ivl_exec_prog_at\<close> owns the
  node-indexed Interval environment, and \<open>interval_classify_check\<close> owns the
  per-check classification.\<close>

definition interval_check_report ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "interval_check_report gs mnm p =
     classify_checks (prog_cfg mnm p)
       (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>) (ivl_exec_prog_at gs mnm p v))
       interval_classify_check"

text \<open>
  The definitional equation above unfolds \<^const>\<open>ivl_exec_prog_at\<close> at every
  check node, and that unfolding re-invokes \<^const>\<open>ivl_exec_raw\<close> (the
  actual solver run) each time --- so naive code generation would re-run the
  whole D/G solver once per check, for an \<open>N\<close>-check program, \<open>N\<close> solver
  runs instead of one. The \<open>[code]\<close> equation below is provably equal (a
  direct \<open>Let\<close>-unfold of the same definitions) but binds
  \<^term>\<open>ivl_exec_raw (resolved_st_q_is_bot_for (declared_global_vars p)) gs
        (prog_table p) (prog_procs p) mnm (prog_main p)\<close>
  once, outside the per-check closure \<^const>\<open>classify_checks\<close> applies; the
  target language compiles that \<open>let\<close> to a single shared thunk, so the
  generated OCaml computes the solved system exactly once per
  report, regardless of how many checks the program has. Mirrors the
  \<open>analyse_sign_report_for_code\<close> fix for the Sign counterpart of this
  report (\<open>Example_Sign_Codegen\<close>, downstream of this theory).
\<close>

declare interval_check_report_def [code del]

lemma interval_check_report_code [code]:
  "interval_check_report gs mnm p =
     (let raw = ivl_exec_raw (resolved_st_q_is_bot_for (declared_global_vars p)) gs
                  (prog_table p) (prog_procs p) mnm (prog_main p)
      in classify_checks (prog_cfg mnm p)
           (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>)
                  (side_env_lift_st gs (raw (Inl v)) (raw (Inr ()))))
           interval_classify_check)"
  unfolding interval_check_report_def ivl_exec_prog_at_def[abs_def] ivl_exec_at_def[abs_def] Let_def
            side_env_lift_st_eq_side_env_lift
  by (rule refl)

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close> and \<open>prog_main_name\<close>,
  matching \<^const>\<open>analyse_interval\<close>'s own fixed choices --- built on the
  exact same \<^const>\<open>ivl_exec_prog\<close> pipeline, not a parallel one.
\<close>

definition analyse_interval_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_report p = interval_check_report (declared_global p) prog_main_name p"

text \<open>
  Soundness reuses \<open>classify_checks_proved_sound\<close>/
  \<open>classify_checks_refuted_sound\<close> (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>, fully
  domain-generic already) with \<open>ivl_exec_prog_sound_collecting_at\<close>
  supplying the one per-node fact each needs.  The
  \<open>cfg_reaches ... (cfg_exit ...)\<close> hypothesis is real and unavoidable, not a
  proof gap: it is the same structural fact \<open>Example_Checks_Store_Only\<close>
  proves per concrete check node (\<open>checks_ex_statement1_reaches_exit\<close> etc.)
  for its one hard-coded example, left here as a hypothesis for an arbitrary
  \<open>p\<close> instead.
\<close>

lemma gamma_state_case_lifted:
  fixes x :: "'a::sound_domain abs_state lifted"
  shows "gamma_state (case_lifted bot (\<lambda>\<sigma>. \<sigma>) x) = gamma_state_lift x"
  by (cases x) (simp_all add: gamma_state_bot)

theorem analyse_interval_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes fin: "finite (intra (prog_cfg prog_main_name p))"
      and terminates: "ivl_terminates_prog (declared_global p) prog_main_name p"
      and reach_exit: "cfg_reaches (prog_cfg prog_main_name p) v (cfg_exit (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           bval c s"
proof -
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
                       \<subseteq> gamma_state (case_lifted bot (\<lambda>\<sigma>. \<sigma>) (ivl_exec_prog_at (declared_global p) prog_main_name p v))"
    unfolding gamma_state_case_lifted
    by (rule ivl_exec_prog_sound_collecting_at[OF refl terminates reach_exit])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>) (ivl_exec_prog_at (declared_global p) prog_main_name p v)"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF fin mem[unfolded analyse_interval_report_def interval_check_report_def]
              interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes fin: "finite (intra (prog_cfg prog_main_name p))"
      and terminates: "ivl_terminates_prog (declared_global p) prog_main_name p"
      and reach_exit: "cfg_reaches (prog_cfg prog_main_name p) v (cfg_exit (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> bval c s"
proof -
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
                       \<subseteq> gamma_state (case_lifted bot (\<lambda>\<sigma>. \<sigma>) (ivl_exec_prog_at (declared_global p) prog_main_name p v))"
    unfolding gamma_state_case_lifted
    by (rule ivl_exec_prog_sound_collecting_at[OF refl terminates reach_exit])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>) (ivl_exec_prog_at (declared_global p) prog_main_name p v)"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF fin mem[unfolded analyse_interval_report_def interval_check_report_def]
              interval_classify_check_refuted node_sound])
qed

subsection \<open>Whole-program check report: the widening/warrowing backend\<close>

text \<open>
  \<open>interval_td_check_report\<close>/\<open>analyse_interval_td_report\<close> mirror
  \<open>interval_check_report\<close>/\<open>analyse_interval_report\<close> exactly, reading through
  \<^const>\<open>analyse_interval_td_at\<close> (the warrowing pipeline) instead of \<^const>\<open>ivl_exec_prog_at\<close>
  (the always-join one) --- the only reason to prefer this report over the always-join one is
  that its backend terminates on programs whose flow-insensitive globals would make the
  always-join solver diverge.
\<close>

definition interval_td_check_report ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "interval_td_check_report gs mnm p =
     classify_checks (prog_cfg mnm p)
       (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>)
              (analyse_interval_td_at (resolved_st_q_is_bot_for (declared_global_vars p)) gs
                 (prog_table p) (prog_procs p) mnm (prog_main p) v))
       interval_classify_check"

text \<open>
  Same single-solve-per-report fix as \<open>interval_check_report_code\<close>: bind
  \<^term>\<open>analyse_interval_td_raw (resolved_st_q_is_bot_for (declared_global_vars p)) gs
        (prog_table p) (prog_procs p) mnm (prog_main p)\<close> once, outside
  \<^const>\<open>classify_checks\<close>'s per-check closure.
\<close>

declare interval_td_check_report_def [code del]

lemma interval_td_check_report_code [code]:
  "interval_td_check_report gs mnm p =
     (let raw = analyse_interval_td_raw (resolved_st_q_is_bot_for (declared_global_vars p)) gs
                  (prog_table p) (prog_procs p) mnm (prog_main p)
      in classify_checks (prog_cfg mnm p)
           (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>)
                  (side_env_lift_st gs (raw (Inl v)) (raw (Inr ()))))
           interval_classify_check)"
  unfolding interval_td_check_report_def analyse_interval_td_at_def[abs_def] Let_def
            side_env_lift_st_eq_side_env_lift
  by (rule refl)

definition analyse_interval_td_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_interval_td_report p = interval_td_check_report (declared_global p) prog_main_name p"

text \<open>
  Soundness mirrors \<open>analyse_interval_report_sound_proved\<close>/\<open>_refuted\<close> exactly, with
  \<open>ivl_terminates_prog\<close>/\<open>ivl_exec_prog_sound_collecting_at\<close> swapped for
  \<open>analyse_interval_td_terminates\<close>/\<open>analyse_interval_td_prog_sound_collecting_at\<close>.
\<close>

theorem analyse_interval_td_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes fin: "finite (intra (prog_cfg prog_main_name p))"
      and terminates: "analyse_interval_td_terminates
                          (resolved_st_q_is_bot_for (declared_global_vars p))
                          (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and reach_exit: "cfg_reaches (prog_cfg prog_main_name p) v (cfg_exit (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           bval c s"
proof -
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
                       \<subseteq> gamma_state (case_lifted bot (\<lambda>\<sigma>. \<sigma>)
                           (analyse_interval_td_at
                              (resolved_st_q_is_bot_for (declared_global_vars p))
                              (declared_global p) (prog_table p) (prog_procs p)
                              prog_main_name (prog_main p) v))"
    unfolding gamma_state_case_lifted
    by (rule analyse_interval_td_prog_sound_collecting_at[OF terminates reach_exit])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>)
                          (analyse_interval_td_at
                             (resolved_st_q_is_bot_for (declared_global_vars p))
                             (declared_global p) (prog_table p) (prog_procs p)
                             prog_main_name (prog_main p) v)"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF fin mem[unfolded analyse_interval_td_report_def interval_td_check_report_def]
              interval_classify_check_proved node_sound])
qed

theorem analyse_interval_td_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes fin: "finite (intra (prog_cfg prog_main_name p))"
      and terminates: "analyse_interval_td_terminates
                          (resolved_st_q_is_bot_for (declared_global_vars p))
                          (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and reach_exit: "cfg_reaches (prog_cfg prog_main_name p) v (cfg_exit (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> bval c s"
proof -
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
                       \<subseteq> gamma_state (case_lifted bot (\<lambda>\<sigma>. \<sigma>)
                           (analyse_interval_td_at
                              (resolved_st_q_is_bot_for (declared_global_vars p))
                              (declared_global p) (prog_table p) (prog_procs p)
                              prog_main_name (prog_main p) v))"
    unfolding gamma_state_case_lifted
    by (rule analyse_interval_td_prog_sound_collecting_at[OF terminates reach_exit])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>)
                          (analyse_interval_td_at
                             (resolved_st_q_is_bot_for (declared_global_vars p))
                             (declared_global p) (prog_table p) (prog_procs p)
                             prog_main_name (prog_main p) v)"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF fin mem[unfolded analyse_interval_td_report_def interval_td_check_report_def]
              interval_classify_check_refuted node_sound])
qed

subsection \<open>Whole-program check report with state: the widening/warrowing backend\<close>

text \<open>
  State-carrying sibling of \<open>interval_td_check_report\<close>/\<open>analyse_interval_td_report\<close>,
  via \<^const>\<open>classify_checks_with_state\<close>: same warrowing D/G pipeline, with
  the per-check Interval environment attached to each report entry instead of
  discarded. The \<open>[code]\<close> rewrite mirrors \<open>interval_td_check_report_code\<close> for
  the same single-solve-per-report reason.
\<close>

definition interval_td_check_report_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> ivl abs_state) list" where
  "interval_td_check_report_with_state gs mnm p =
     classify_checks_with_state (prog_cfg mnm p)
       (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>)
              (analyse_interval_td_at (resolved_st_q_is_bot_for (declared_global_vars p)) gs
                 (prog_table p) (prog_procs p) mnm (prog_main p) v))
       interval_classify_check"

declare interval_td_check_report_with_state_def [code del]

lemma interval_td_check_report_with_state_code [code]:
  "interval_td_check_report_with_state gs mnm p =
     (let raw = analyse_interval_td_raw (resolved_st_q_is_bot_for (declared_global_vars p)) gs
                  (prog_table p) (prog_procs p) mnm (prog_main p)
      in classify_checks_with_state (prog_cfg mnm p)
           (\<lambda>v. case_lifted bot (\<lambda>\<sigma>. \<sigma>)
                  (side_env_lift_st gs (raw (Inl v)) (raw (Inr ()))))
           interval_classify_check)"
  unfolding interval_td_check_report_with_state_def analyse_interval_td_at_def[abs_def] Let_def
            side_env_lift_st_eq_side_env_lift
  by (rule refl)


definition analyse_interval_td_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> ivl abs_state) list" where
  "analyse_interval_td_report_with_state p =
     interval_td_check_report_with_state (declared_global p) prog_main_name p"

end
