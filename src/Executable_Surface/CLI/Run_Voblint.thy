theory Run_Voblint
  imports Typed_Report
begin

section \<open>The public analysis operation\<close>

text \<open>
  \<open>run_voblint\<close> analyzes a program under its kind declarations with the options of a
  \<^typ>\<open>voblint_conf\<close>: the activated typed analyses, a context policy, a global update
  rule and the options the domains read, as Goblint's configuration tree selects them
  (\<^verbatim>\<open>ana.activated\<close>, \<^verbatim>\<open>sem.int.signed_overflow\<close>). It answers the report
  \<^const>\<open>report_of\<close> builds from the solve. An activation is valid when it names at
  least one analysis and none twice. The analyzer over mathematical integers stays
  available as \<^const>\<open>run_voblint_legacy\<close>.
\<close>

definition valid_activation :: "typed_domain list \<Rightarrow> bool" where
  "valid_activation as \<longleftrightarrow> as \<noteq> [] \<and> distinct as"

definition run_voblint :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_report analysis_answer" where
  "run_voblint conf ds p =
     (if \<not> valid_activation (conf_analyses conf) then Invalid_Activation
      else if \<not> wf_program_compile_input_exec p then Malformed_Program
      else case typed_report_run (conf_sem conf) (conf_analyses conf) (conf_globals conf)
                  (conf_context conf) ds p of
             None \<Rightarrow> No_Answer
           | Some res \<Rightarrow> Analysed res)"

subsection \<open>What an answer guarantees\<close>

text \<open>
  The headline theorem, about the report a caller receives. Its stores are the typed
  stores that reach a node from a store whose globals are zero at their kinds. Every
  such store lies in one of the states the report lists at the node, read through the
  concretization of the activated analyses; a proved check holds at it and a refuted one
  fails. Neither verdict says that the node is reached, and an unknown verdict says
  nothing. The theorem holds for every configuration. It assumes only that the run
  answered: termination of the solve is not a premise, because the executable solve
  answers only when it has terminated.
\<close>

theorem run_voblint_sound:
  assumes run: "run_voblint conf ds p = Analysed res"
  shows run_voblint_states:
      "\<And>v s. s \<in> reaching ds p v
         \<Longrightarrow> \<exists>d. Lifted d \<in> report_states_at res v
               \<and> s \<in> tmcp.act_gamma ds (tactivation (conf_analyses conf)) d"
    and run_voblint_proved:
      "\<And>chk s. chk \<in> set (report_checks res) \<Longrightarrow> check_verdict chk = Decided Check_Proved
         \<Longrightarrow> s \<in> reaching ds p (check_point chk) \<Longrightarrow> truthy (teval (check_exp chk) s)"
    and run_voblint_refuted:
      "\<And>chk s. chk \<in> set (report_checks res) \<Longrightarrow> check_verdict chk = Decided Check_Refuted
         \<Longrightarrow> s \<in> reaching ds p (check_point chk) \<Longrightarrow> \<not> truthy (teval (check_exp chk) s)"
proof -
  have exec: "wf_program_compile_input_exec p"
    and rep: "typed_report_run (conf_sem conf) (conf_analyses conf) (conf_globals conf)
                (conf_context conf) ds p = Some res"
    using run by (auto simp: run_voblint_def split: if_splits option.splits)
  note wf = wf_program_compile_input_exec_sound[OF exec]
  show "\<And>v s. s \<in> reaching ds p v
          \<Longrightarrow> \<exists>d. Lifted d \<in> report_states_at res v
                \<and> s \<in> tmcp.act_gamma ds (tactivation (conf_analyses conf)) d"
    by (erule typed_report_state_sound[OF wf rep]) blast
  show "\<And>chk s. chk \<in> set (report_checks res) \<Longrightarrow> check_verdict chk = Decided Check_Proved
          \<Longrightarrow> s \<in> reaching ds p (check_point chk) \<Longrightarrow> truthy (teval (check_exp chk) s)"
    using typed_report_check_sound(1)[OF wf rep] by blast
  show "\<And>chk s. chk \<in> set (report_checks res) \<Longrightarrow> check_verdict chk = Decided Check_Refuted
          \<Longrightarrow> s \<in> reaching ds p (check_point chk) \<Longrightarrow> \<not> truthy (teval (check_exp chk) s)"
    using typed_report_check_sound(2)[OF wf rep] by blast
qed

text \<open>An answer was given for a valid activation and a well-formed program, and its
  report records the configuration it was run with.\<close>

lemma run_voblint_AnalysedE:
  assumes "run_voblint conf ds p = Analysed res"
  obtains "valid_activation (conf_analyses conf)" and "wf_program_compile_input_exec p"
    and "typed_report_run (conf_sem conf) (conf_analyses conf) (conf_globals conf)
           (conf_context conf) ds p = Some res"
  using assms unfolding run_voblint_def by (auto split: if_splits option.splits)

lemma run_voblint_config:
  assumes "run_voblint conf ds p = Analysed res"
  shows "report_config res = conf"
  using assms
  by (cases conf)
     (auto simp: run_voblint_def typed_report_run_def typed_cs_report_def typed_es_report_def
      report_of_def Let_def split: if_splits option.splits typed_context.splits)

end
