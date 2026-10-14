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

subsection \<open>What the arithmetic diagnostics guarantee\<close>

text \<open>
  A point the report's diagnostics do not name is safe: at every store that reaches it,
  every obligation of every expression an edge or a call there evaluates holds, and
  every value returned there fits the kind each caller converts it to. No divisor is
  zero, no signed operation computes a result outside its kind, and no conversion
  narrower than its source kind converts a value outside its target. A
  diagnostic says nothing on its own unless it is refuted: then its obligation fails at
  every store that reaches its point, which is a definite violation only if the point is
  reached. Both hold under either overflow policy, which changes only how precisely the
  analyses bound a wrapped value.
\<close>

theorem run_voblint_arithmetic_safe:
  assumes run: "run_voblint conf ds p = Analysed res"
    and absent: "SAFE res v"
    and s: "s \<in> reaching ds p v"
  shows run_voblint_arithmetic_safe_intra:
      "(v, a, w) \<in> intra (typed_cfg p ds) \<Longrightarrow> e \<in> set (edge_expressions a)
         \<Longrightarrow> ob \<in> set (tarith_obligations e) \<Longrightarrow> s \<Turnstile> ob"
    and run_voblint_arithmetic_safe_call:
      "(v, ca, ce, k) \<in> calls (typed_cfg p ds) \<Longrightarrow> e \<in> set (ce_args ca)
         \<Longrightarrow> ob \<in> set (tarith_obligations e) \<Longrightarrow> s \<Turnstile> ob"
    and run_voblint_arithmetic_safe_return:
      "(u, ca, ce, k) \<in> calls (typed_cfg p ds) \<Longrightarrow> ce_dst ca = Some x
         \<Longrightarrow> (v, EA_Ret (Some e) (callee_of_entry ce), w) \<in> intra (typed_cfg p ds)
         \<Longrightarrow> \<not> ik_widens (texp_kind e) (kenv_of ds x)
         \<Longrightarrow> teval e s \<in> ik_range (kenv_of ds x)"
proof -
  from run have wf: "wf_program_compile_input p"
    and rep: "typed_report_run (conf_sem conf) (conf_analyses conf) (conf_globals conf)
                (conf_context conf) ds p = Some res"
    by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
  note safe = typed_report_obligation_safe[OF wf rep s _ _ absent]
  show "s \<Turnstile> ob"
    if "(v, a, w) \<in> intra (typed_cfg p ds)" "e \<in> set (edge_expressions a)"
      "ob \<in> set (tarith_obligations e)"
    using tobligation_site_intra[OF that] safe by blast
  show "s \<Turnstile> ob"
    if "(v, ca, ce, k) \<in> calls (typed_cfg p ds)" "e \<in> set (ce_args ca)"
      "ob \<in> set (tarith_obligations e)"
    using tobligation_site_call[OF that] safe by blast
  show "teval e s \<in> ik_range (kenv_of ds x)"
    if "(u, ca, ce, k) \<in> calls (typed_cfg p ds)" "ce_dst ca = Some x"
      "(v, EA_Ret (Some e) (callee_of_entry ce), w) \<in> intra (typed_cfg p ds)"
      "\<not> ik_widens (texp_kind e) (kenv_of ds x)"
    using safe[OF tobligation_site_return[OF that]] by simp
qed

theorem run_voblint_arithmetic_refuted:
  assumes run: "run_voblint conf ds p = Analysed res"
    and d: "d \<in> set (report_diagnostics res)" and r: "diagnostic_verdict d = Check_Refuted"
    and s: "s \<in> reaching ds p (diagnostic_point d)"
  shows "\<not> s \<Turnstile> diagnostic_obligation d"
proof -
  from run have wf: "wf_program_compile_input p"
    and rep: "typed_report_run (conf_sem conf) (conf_analyses conf) (conf_globals conf)
                (conf_context conf) ds p = Some res"
    by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
  show ?thesis by (rule typed_report_obligation_refuted[OF wf rep s d r refl])
qed

text \<open>
  For signed overflow in particular: at a point no diagnostic names, every signed
  addition, subtraction, multiplication and division nested in an expression evaluated
  there computes, from the operand values of any reaching store, a mathematical result
  its kind represents. So no execution that reaches the point overflows there, whichever
  value wraparound would have produced.
\<close>

corollary run_voblint_no_signed_overflow:
  assumes run: "run_voblint conf ds p = Analysed res"
    and absent: "SAFE res v"
    and s: "s \<in> reaching ds p v"
    and evaluated: "((v, a, w) \<in> intra (typed_cfg p ds) \<and> e \<in> set (edge_expressions a))
                    \<or> ((v, ca, ce, k) \<in> calls (typed_cfg p ds) \<and> e \<in> set (ce_args ca))"
    and sub: "TArith ik op x y \<in> tsubexps e" and signed: "ik_signed ik" and op: "op \<noteq> AMod"
  shows "aop_eval op (teval x s) (teval y s) \<in> ik_range ik"
  using evaluated tarith_obligations_overflow[OF sub signed op]
    run_voblint_arithmetic_safe[OF run absent s]
  by (metis tobligation_holds_overflow)

text \<open>
  For conversions: at a point no diagnostic names, every conversion nested in an
  expression evaluated there whose source kind does not widen into its target converts
  a value the target represents, so no conversion changes the value it converts.
\<close>

corollary run_voblint_no_conversion_overflow:
  assumes run: "run_voblint conf ds p = Analysed res"
    and absent: "SAFE res v"
    and s: "s \<in> reaching ds p v"
    and evaluated: "((v, a, w) \<in> intra (typed_cfg p ds) \<and> e \<in> set (edge_expressions a))
                    \<or> ((v, ca, ce, k) \<in> calls (typed_cfg p ds) \<and> e \<in> set (ce_args ca))"
    and sub: "TCast ik x \<in> tsubexps e" and narrows: "\<not> ik_widens (texp_kind x) ik"
  shows "teval x s \<in> ik_range ik"
  using evaluated tarith_obligations_conversion[OF sub narrows]
    run_voblint_arithmetic_safe[OF run absent s]
  by (metis tobligation_holds_conversion(1))

subsection \<open>The report's vocabulary\<close>

text \<open>
  The guarantees above, read through the predicates every report shares:
  \<^const>\<open>PROVED\<close>, \<^const>\<open>REFUTED\<close>, \<^const>\<open>DEAD\<close> and \<^const>\<open>SAFE\<close>, and
  \<open>s \<Turnstile> ob\<close> for a store meeting an obligation. \<open>reaching ds p v\<close> are the stores that
  reach \<open>v\<close>. A proved check holds at each of them and a refuted one fails; a dead
  point has none; at a safe point every obligation the report decides there holds.
  None of them says that \<open>v\<close> is reached.

  \<open>SAFE\<close> is only as strong as the obligations it covers: those of every expression
  an edge or a call at \<open>v\<close> evaluates and of every value returned there that a
  caller converts to a narrower kind (\<open>run_voblint_obligations_cover\<close>). It says
  nothing about a hazard Voblint does not check, such as the conversion of a
  library call's result.
\<close>

theorem run_voblint_report_sound:
  assumes run: "run_voblint conf ds p = Analysed res" and s: "s \<in> reaching ds p v"
  shows run_voblint_PROVED: "PROVED res v c \<Longrightarrow> truthy (teval c s)"
    and run_voblint_REFUTED: "REFUTED res v c \<Longrightarrow> \<not> truthy (teval c s)"
    and run_voblint_DEAD: "DEAD res v \<Longrightarrow> False"
    and run_voblint_SAFE: "SAFE res v \<Longrightarrow> ob \<in> tobligations_at ds p v \<Longrightarrow> s \<Turnstile> ob"
proof -
  show "PROVED res v c \<Longrightarrow> truthy (teval c s)"
    using run_voblint_proved[OF run] s by (auto simp: HAS_VERDICT_def)
  show "REFUTED res v c \<Longrightarrow> \<not> truthy (teval c s)"
    using run_voblint_refuted[OF run] s by (auto simp: HAS_VERDICT_def)
  show "DEAD res v \<Longrightarrow> False"
    using run_voblint_states[OF run s] by (auto simp: DEAD_def)
  show "SAFE res v \<Longrightarrow> ob \<in> tobligations_at ds p v \<Longrightarrow> s \<Turnstile> ob"
  proof -
    assume safe: "SAFE res v" and ob: "ob \<in> tobligations_at ds p v"
    from run have wf: "wf_program_compile_input p"
      and rep: "typed_report_run (conf_sem conf) (conf_analyses conf) (conf_globals conf)
                  (conf_context conf) ds p = Some res"
      by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
    from ob obtain obs where "(v, obs) \<in> set (tobligation_sites ds p)" and "ob \<in> set obs"
      by (auto simp: mem_tobligations_at)
    from typed_report_obligation_safe[OF wf rep s this] safe show "s \<Turnstile> ob" .
  qed
qed

corollary run_voblint_dead_unreached:
  "run_voblint conf ds p = Analysed res \<Longrightarrow> DEAD res v \<Longrightarrow> reaching ds p v = {}"
  using run_voblint_DEAD by blast

text \<open>Every obligation of an expression evaluated at \<open>v\<close>, and every narrowing
  conversion of a value returned at \<open>v\<close>, is one the report decides there.\<close>

lemma run_voblint_obligations_cover:
  shows "(v, a, w) \<in> intra (typed_cfg p ds) \<Longrightarrow> e \<in> set (edge_expressions a)
           \<Longrightarrow> set (tarith_obligations e) \<subseteq> tobligations_at ds p v"
    and "(v, ca, ce, k) \<in> calls (typed_cfg p ds) \<Longrightarrow> e \<in> set (ce_args ca)
           \<Longrightarrow> set (tarith_obligations e) \<subseteq> tobligations_at ds p v"
    and "(u, ca, ce, k) \<in> calls (typed_cfg p ds) \<Longrightarrow> ce_dst ca = Some x
           \<Longrightarrow> (v, EA_Ret (Some e) (callee_of_entry ce), w) \<in> intra (typed_cfg p ds)
           \<Longrightarrow> \<not> ik_widens (texp_kind e) (kenv_of ds x)
           \<Longrightarrow> Arithmetic_Obligation Conversion_Overflow (TCast (kenv_of ds x) e) e
                 \<in> tobligations_at ds p v"
  by (auto simp: mem_tobligations_at dest: tobligation_site_intra tobligation_site_call
      intro: tobligation_site_return)

end
