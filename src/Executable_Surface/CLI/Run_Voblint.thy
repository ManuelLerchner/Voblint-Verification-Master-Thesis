theory Run_Voblint
  imports Typed_Report
begin

section \<open>The public analysis operation\<close>

text \<open>
  \<open>run_voblint\<close> analyzes a program under its kind declarations with the options of a
  \<^typ>\<open>voblint_conf\<close>: the activated typed analyses, a context policy, a global update
  rule, where program globals live, and the options the domains read, as Goblint's
  configuration tree selects them (\<^verbatim>\<open>ana.activated\<close>, \<^verbatim>\<open>sem.int.signed_overflow\<close>). It
  answers the report \<^const>\<open>report_of\<close> builds from the solve. An activation is valid
  when it names at least one analysis and none twice.
\<close>

definition valid_activation :: "typed_domain list \<Rightarrow> bool" where
  "valid_activation as \<longleftrightarrow> as \<noteq> [] \<and> distinct as"

definition run_voblint :: "voblint_conf \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> typed_report analysis_answer" where
  "run_voblint conf ds p =
     (if \<not> valid_activation (conf_analyses conf) then Invalid_Activation
      else if \<not> wf_program_compile_input_exec p then Malformed_Program
      else case typed_report_run conf ds p of
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
    and rep: "typed_report_run conf ds p = Some res"
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
    and "typed_report_run conf ds p = Some res"
  using assms unfolding run_voblint_def by (auto split: if_splits option.splits)

lemma typed_report_run_shape:
  assumes "typed_report_run conf ds p = Some res"
  shows "report_config res = conf" and "report_cfg res = typed_cfg p ds"
  using assms
  by (auto simp: typed_report_run_def typed_cs_run_def typed_es_run_def typed_report_of_def
      report_of_def Let_def split: typed_context.splits program_globals.splits)

lemma run_voblint_config:
  assumes "run_voblint conf ds p = Analysed res"
  shows "report_config res = conf"
  using assms by (auto elim!: run_voblint_AnalysedE dest: typed_report_run_shape)

lemma run_voblint_cfg:
  assumes "run_voblint conf ds p = Analysed res"
  shows "report_cfg res = typed_cfg p ds"
  using assms by (auto elim!: run_voblint_AnalysedE dest: typed_report_run_shape)


text \<open>
  The report contract in one statement: an analysed answer was given for a valid
  activation and a well-formed program, and is a report of exactly that
  configuration and the program's typed graph. The theorems that follow read it.
\<close>

theorem run_voblint_report_contract:
  assumes "run_voblint conf ds p = Analysed res"
  shows "valid_activation (conf_analyses conf)" and "wf_program_compile_input_exec p"
    and "report_config res = conf" and "report_cfg res = typed_cfg p ds"
  using assms run_voblint_config run_voblint_cfg by (auto elim: run_voblint_AnalysedE)

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
    and rep: "typed_report_run conf ds p = Some res"
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
    and rep: "typed_report_run conf ds p = Some res"
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
      and rep: "typed_report_run conf ds p = Some res"
      by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
    from ob obtain obs where "(v, obs) \<in> set (tobligation_sites ds p)" and "ob \<in> set obs"
      by (auto simp: mem_tobligations_at)
    from typed_report_obligation_safe[OF wf rep s this] safe show "s \<Turnstile> ob" .
  qed
qed

corollary run_voblint_dead_unreached:
  "run_voblint conf ds p = Analysed res \<Longrightarrow> DEAD res v \<Longrightarrow> reaching ds p v = {}"
  using run_voblint_DEAD by blast

subsection \<open>What an answer guarantees about a run of the program\<close>

text \<open>
  The same guarantees, read at a run of the typed program itself rather than at a
  node of its graph. Run the program from a store whose globals are zero at their
  kinds and stop anywhere: the configuration reached is simulated at a node \<open>v\<close> of
  the typed graph, the store reaches \<open>v\<close>, the report holds a state at \<open>v\<close> describing
  it, \<open>v\<close> is not dead, every check the report decides at \<open>v\<close> has its verdict at the
  store, and if \<open>v\<close> is safe every obligation decided there holds of the store.
\<close>

theorem run_voblint_source_sound:
  assumes run: "run_voblint conf ds p = Analysed res"
    and s0: "s0 \<in> tinit_stores (kenv_of ds)"
    and exec: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                 (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. typed_ptable p ds, typed_cfg p ds, prog_main_name
                    \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> s \<in> reaching ds p v
           \<and> (\<exists>d. Lifted d \<in> report_states_at res v
                  \<and> s \<in> tmcp.act_gamma ds (tactivation (conf_analyses conf)) d)
           \<and> \<not> DEAD res v
           \<and> (\<forall>c. PROVED res v c \<longrightarrow> truthy (teval c s))
           \<and> (\<forall>c. REFUTED res v c \<longrightarrow> \<not> truthy (teval c s))
           \<and> (SAFE res v \<longrightarrow> (\<forall>ob \<in> tobligations_at ds p v. s \<Turnstile> ob))"
proof -
  from run have wf: "wf_program_compile_input p"
    by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
  from typed_source_reaches_node_collect[OF wf s0 exec] obtain v stk
    where sim: "typed_ptable p ds, typed_cfg p ds, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and s: "s \<in> reaching ds p v"
    by blast
  show ?thesis
    using sim s run_voblint_states[OF run s] run_voblint_report_sound[OF run s] by blast
qed

text \<open>
  Read at a check: a run about to execute \<open>Check l e\<close> finds a check labelled \<open>l\<close> for
  \<open>e\<close> in the report, listed at a node this very store reaches. Its verdict is not
  \<open>Dead\<close>, and a decided verdict holds of the store.
\<close>

theorem run_voblint_check_sound:
  assumes run: "run_voblint conf ds p = Analysed res"
    and s0: "s0 \<in> tinit_stores (kenv_of ds)"
    and exec: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                 (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
    and chk: "next_check residual = Some (l, e)"
  shows "\<exists>c \<in> set (report_checks res). check_label c = l \<and> check_exp c = e
           \<and> s \<in> reaching ds p (check_point c)
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (teval e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval e s))"
proof -
  from run have wf: "wf_program_compile_input p"
    and rep: "typed_report_run conf ds p = Some res"
    by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
  from typed_source_reaches_node_collect[OF wf s0 exec] obtain v stk
    where sim: "typed_ptable p ds, typed_cfg p ds, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and s: "s \<in> reaching ds p v"
    by blast
  from csim_next_check_edge[OF sim chk] obtain w where "(v, EA_Check l e, w) \<in> intra (typed_cfg p ds)"
    by blast
  from typed_report_check_row[OF wf rep this] obtain c where c: "c \<in> set (report_checks res)"
    and pt: "check_point c = v" and lbl: "check_label c = l" and ex: "check_exp c = e"
    by blast
  have "check_verdict c \<noteq> Dead" by (rule typed_report_check_live[OF wf rep s c pt])
  with c pt lbl ex s run_voblint_proved[OF run c] run_voblint_refuted[OF run c] show ?thesis
    by force
qed

text \<open>
  Read by label, as a consumer finds a source check's row: when the report's labels
  are distinct, which a consumer can decide on the report, the row labelled \<open>l\<close> is the
  one for the check about to run, and its verdict holds of the store. That the parser
  wrote each check's own source position into its label stays outside the theorem.
\<close>

corollary run_voblint_labelled_check_sound:
  assumes run: "run_voblint conf ds p = Analysed res"
    and s0: "s0 \<in> tinit_stores (kenv_of ds)"
    and exec: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                 (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
    and chk: "next_check residual = Some (l, e)"
    and distinct: "distinct (map check_label (report_checks res))"
  shows "\<exists>c \<in> set (report_checks res). check_label c = l"
    and "\<forall>c \<in> set (report_checks res). check_label c = l \<longrightarrow>
           check_exp c = e
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (teval e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval e s))"
proof -
  from run_voblint_check_sound[OF run s0 exec chk]
  obtain c0 where c0: "c0 \<in> set (report_checks res)" "check_label c0 = l" "check_exp c0 = e"
    and v0: "check_verdict c0 \<noteq> Dead"
      "check_verdict c0 = Decided Check_Proved \<longrightarrow> truthy (teval e s)"
      "check_verdict c0 = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval e s)"
    by blast
  from c0 show "\<exists>c \<in> set (report_checks res). check_label c = l" by blast
  have inj: "inj_on check_label (set (report_checks res))"
    using distinct by (simp add: distinct_map)
  show "\<forall>c \<in> set (report_checks res). check_label c = l \<longrightarrow>
           check_exp c = e
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (teval e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval e s))"
  proof (intro ballI impI)
    fix c assume "c \<in> set (report_checks res)" and "check_label c = l"
    with c0 inj have "c = c0" by (auto dest: inj_onD)
    with c0 v0 show "check_exp c = e \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (teval e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (teval e s))" by simp
  qed
qed

text \<open>
  The whole chain for any context policy, given what the policy owes: every valid
  activation trace of the typed graph carries some context, and the stores filed
  under the policy's contexts at a node are exactly the stores that reach it. A run
  of the typed program is then simulated at a node, by a valid activation trace with
  a context, whose store lies in that context's bucket; the buckets make up the
  stores reaching the node, the report holds a state there describing the store, and
  the report's checks hold of it.
\<close>

theorem run_voblint_spine:
  fixes p :: imp_prog and ds :: kind_decls and adm c\<^sub>0
  defines "g \<equiv> typed_cfg p ds" and "S \<equiv> tinit_stores (kenv_of ds)"
  assumes run: "run_voblint conf ds p = Analysed res"
    and s0: "s0 \<in> S"
    and exec: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                 (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
    and has_ctx: "\<And>t. t \<in> typed.gvalid_activation_trace (kenv_of ds) g S
                   \<Longrightarrow> \<exists>c. typed.gactivation_context_rel (kenv_of ds) adm c\<^sub>0 g t c"
    and buckets: "\<And>v. (\<Union>c'. typed.gactivation_collect (kenv_of ds) adm c\<^sub>0 g S v c')
                   = reaching ds p v"
  shows "\<exists>v stk t c. typed_ptable p ds, g, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> typed.gactivation_trace_repr (kenv_of ds) g S (v, s, stk) t
           \<and> typed.gactivation_context_rel (kenv_of ds) adm c\<^sub>0 g t c
           \<and> s \<in> typed.gactivation_collect (kenv_of ds) adm c\<^sub>0 g S v c
           \<and> (\<Union>c'. typed.gactivation_collect (kenv_of ds) adm c\<^sub>0 g S v c') = reaching ds p v
           \<and> (\<exists>d. Lifted d \<in> report_states_at res v
                  \<and> s \<in> tmcp.act_gamma ds (tactivation (conf_analyses conf)) d)
           \<and> (\<forall>c. PROVED res v c \<longrightarrow> truthy (teval c s))
           \<and> (\<forall>c. REFUTED res v c \<longrightarrow> \<not> truthy (teval c s))"
proof -
  from run have wf: "wf_program_compile_input p"
    by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
  have cfg: "g = compile_prog (typed_ptable p ds) (prog_procs p)"
    unfolding g_def by (rule typed_cfg_def)
  from typed.source_store_in_activation_collect
         [OF typed_wf_compile_input[OF wf] s0 exec has_ctx[unfolded cfg]]
  obtain v stk t c
    where sim: "typed_ptable p ds, g, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and rep: "typed.gactivation_trace_repr (kenv_of ds) g S (v, s, stk) t"
      and rel: "typed.gactivation_context_rel (kenv_of ds) adm c\<^sub>0 g t c"
      and mem: "s \<in> typed.gactivation_collect (kenv_of ds) adm c\<^sub>0 g S v c"
    unfolding cfg by blast
  have s: "s \<in> reaching ds p v" using mem buckets[of v] by blast
  show ?thesis
    using sim rep rel mem buckets[of v] run_voblint_states[OF run s] run_voblint_report_sound[OF run s]
    by blast
qed

text \<open>
  Each context policy owes the spine's two facts. A call string is a function of the
  trace, so every trace carries one and the buckets cover the stores outright. An
  entry-state context is read off the solve, and the answer was given only because
  the solve terminated, which is what makes the admitted contexts cover every trace.
\<close>

theorem run_voblint_call_string_chain:
  fixes p :: imp_prog and ds :: kind_decls and k :: nat
  defines "g \<equiv> typed_cfg p ds" and "S \<equiv> tinit_stores (kenv_of ds)"
    and "adm \<equiv> context_policy_of_fun (typed_cs k)"
  assumes run: "run_voblint conf ds p = Analysed res"
    and cx: "conf_context conf = Typed_Call_String k"
    and s0: "s0 \<in> S"
    and exec: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                 (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "\<exists>v stk t c. typed_ptable p ds, g, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> typed.gactivation_trace_repr (kenv_of ds) g S (v, s, stk) t
           \<and> typed.gactivation_context_rel (kenv_of ds) adm [] g t c
           \<and> s \<in> typed.gactivation_collect (kenv_of ds) adm [] g S v c
           \<and> (\<Union>c'. typed.gactivation_collect (kenv_of ds) adm [] g S v c') = reaching ds p v
           \<and> (\<exists>d. Lifted d \<in> report_states_at res v
                  \<and> s \<in> tmcp.act_gamma ds (tactivation (conf_analyses conf)) d)
           \<and> (\<forall>c. PROVED res v c \<longrightarrow> truthy (teval c s))
           \<and> (\<forall>c. REFUTED res v c \<longrightarrow> \<not> truthy (teval c s))"
proof -
  have has_ctx: "\<exists>c. typed.gactivation_context_rel (kenv_of ds) adm [] g t c"
    if "t \<in> typed.gvalid_activation_trace (kenv_of ds) g S" for t
    unfolding adm_def by (rule exI, subst typed.activation_context_rel_of_fun_iff[OF that]) (rule refl)
  have buckets: "(\<Union>c'. typed.gactivation_collect (kenv_of ds) adm [] g S v c') = reaching ds p v"
    for v
    unfolding adm_def g_def S_def tnode_collect_def
    by (rule typed_mcp.fun_route_node_collect_eq_Union[where ctx_fun = "typed_cs k", symmetric])
  show ?thesis
    unfolding g_def S_def
    by (rule run_voblint_spine[OF run s0[unfolded S_def] exec has_ctx[unfolded g_def S_def]
          buckets[unfolded g_def S_def]])
qed

text \<open>An entry-state run admits the contexts its placement's registration reads off the
  solve.\<close>

theorem run_voblint_entry_state_chain:
  fixes p :: imp_prog and ds :: kind_decls and conf :: voblint_conf
  defines "g \<equiv> typed_cfg p ds" and "S \<equiv> tinit_stores (kenv_of ds)"
    and "adm \<equiv> (case conf_program_globals conf of
                 Program_Globals_Flow_Sensitive \<Rightarrow>
                   typed_mcp_es.entry_context_rel (conf_sem conf) ds (conf_analyses conf)
                     (conf_globals conf) p
               | Program_Globals_Flow_Insensitive \<Rightarrow>
                   typed_mcp_split_es.entry_context_rel (conf_sem conf) ds (conf_analyses conf)
                     (conf_globals conf) (tdeclared_globals p) p)"
  assumes run: "run_voblint conf ds p = Analysed res"
    and cx: "conf_context conf = Typed_Entry_State"
    and s0: "s0 \<in> S"
    and exec: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                 (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "\<exists>v stk t c. typed_ptable p ds, g, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> typed.gactivation_trace_repr (kenv_of ds) g S (v, s, stk) t
           \<and> typed.gactivation_context_rel (kenv_of ds) adm tmcp_root_ctx g t c
           \<and> s \<in> typed.gactivation_collect (kenv_of ds) adm tmcp_root_ctx g S v c
           \<and> (\<Union>c'. typed.gactivation_collect (kenv_of ds) adm tmcp_root_ctx g S v c')
               = reaching ds p v
           \<and> (\<exists>d. Lifted d \<in> report_states_at res v
                  \<and> s \<in> tmcp.act_gamma ds (tactivation (conf_analyses conf)) d)
           \<and> (\<forall>c. PROVED res v c \<longrightarrow> truthy (teval c s))
           \<and> (\<forall>c. REFUTED res v c \<longrightarrow> \<not> truthy (teval c s))"
proof -
  from run have wf: "wf_program_compile_input p"
    and rep: "typed_report_run conf ds p = Some res"
    by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
  have chain: "(\<forall>t. t \<in> typed.gvalid_activation_trace (kenv_of ds) g S
                  \<longrightarrow> (\<exists>c. typed.gactivation_context_rel (kenv_of ds) adm tmcp_root_ctx g t c))
    \<and> (\<forall>v. (\<Union>c'. typed.gactivation_collect (kenv_of ds) adm tmcp_root_ctx g S v c')
             = reaching ds p v)"
  proof (cases "conf_program_globals conf")
    case Program_Globals_Flow_Sensitive
    from rep cx Program_Globals_Flow_Sensitive obtain sol where
      "TD_side_rule_Interp_solve_c (conf_globals conf)
         (typed_mcp_es.equations (conf_sem conf) ds (conf_analyses conf) tglobal p)
         (typed_mcp_es.root_query ds p) = Some sol"
      by (auto simp: typed_report_run_def typed_es_run_def Let_def dg_pipeline.root_query_def)
    note solves = typed_mcp_es.solve_c_run(1)[OF this]
    show ?thesis
      using typed_mcp_es.gentry_state_has_context_of_terminates
          [OF typed_cfg_def typed_wf_compile_input[OF wf] solves]
        typed_mcp_es.gentry_state_node_collect_eq_Union_of_terminates
          [OF typed_cfg_def typed_wf_compile_input[OF wf] solves]
      unfolding adm_def g_def S_def tnode_collect_def Program_Globals_Flow_Sensitive by simp
  next
    case Program_Globals_Flow_Insensitive
    from rep cx Program_Globals_Flow_Insensitive obtain sol where
      "TD_side_rule_Interp_solve_c (conf_globals conf)
         (typed_mcp_split_es.equations (conf_sem conf) ds (conf_analyses conf) (tdeclared_globals p)
            tglobal p)
         (typed_mcp_split_es.root_query ds p) = Some sol"
      by (auto simp: typed_report_run_def typed_es_run_def Let_def dg_pipeline.root_query_def)
    note solves = typed_mcp_split_es.solve_c_run(1)[OF this]
    show ?thesis
      using typed_mcp_split_es.gentry_state_has_context_of_terminates
          [OF typed_cfg_def typed_wf_compile_input[OF wf] solves]
        typed_mcp_split_es.gentry_state_node_collect_eq_Union_of_terminates
          [OF typed_cfg_def typed_wf_compile_input[OF wf] solves]
      unfolding adm_def g_def S_def tnode_collect_def Program_Globals_Flow_Insensitive by simp
  qed
  show ?thesis
    unfolding g_def S_def
    by (rule run_voblint_spine[OF run s0[unfolded S_def] exec
          conjunct1[OF chain, unfolded g_def S_def, rule_format]
          conjunct2[OF chain, unfolded g_def S_def, rule_format]])
qed

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
