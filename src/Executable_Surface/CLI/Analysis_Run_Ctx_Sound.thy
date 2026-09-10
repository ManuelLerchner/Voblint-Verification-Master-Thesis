theory Analysis_Run_Ctx_Sound
  imports Analysis_Run_Sound
begin

section \<open>What a run at a context-sensitive configuration proves about a run of the program\<close>

text \<open>
  The context-free endpoint reads one abstract state per program point. A
  context-sensitive configuration reads one per point \<^emph>\<open>and\<close> context, so a
  concrete store reaching a point is described by the entry the analysis filed
  under \<^emph>\<open>some\<close> context its own call history is admitted at --- exactly one for a
  call string, possibly several for the relational entry-state routing, and in
  general not every context the node was solved at. That extra step is what this
  theory supplies, and it runs in the
  opposite direction to the published soundness: soundness bounds one bucket
  from above, while a store in hand needs a bucket to sit in at all.

  Three things are settled below. A decided row of a contextual answer is an
  entry of the published contextual verdict report over the same table
  (\<open>decided_row_in_entry_state_verdicts\<close>, \<open>decided_row_in_cs_verdicts\<close>). A
  store known to reach a point sits in some context's entry of that table
  (\<open>lookup_context_covers_of_activation\<close>). And the two compose into a
  source-level endpoint, stated once over an arbitrary context policy and
  instantiated at every domain's two contextual configurations, each at the
  discipline its policy defaults to. The same endpoint at an explicitly named
  discipline lives in \<open>Analysis_Run_Solver_Sound\<close>, which imports this one.
\<close>

subsection \<open>A decided row of a contextual answer is an entry of its verdict report\<close>

text \<open>
  Both contextual routes build every view from one \<^const>\<open>classify_checks_verdicts\<close>
  call over the table their plan resolved to, so the check column is that call
  regardless of which drawing was asked for. A verdict-report route reaches the
  same rows without a table; those plans are outside what follows, because
  nothing there can be read back per context.
\<close>

lemma out_checks_of_entry_state_output:
  assumes "entry_state_output_of view enter into classify r p = Analysed out"
  shows "out_checks out
           = check_rows_of (project_joined_env into r)
               (classify_checks_verdicts (prog_cfg p) r classify)"
  using assms
  by (cases view)
     (auto simp: entry_state_output_of_def contextual_output_def report_output_def
        collapsed_output_def Let_def)

text \<open>
  \<^const>\<open>verdict_report_answer\<close> looks like a different output path and is not
  one: its argument is already the contextual verdict report, so the rows it
  renders are the same \<^const>\<open>classify_checks_verdicts\<close> the other two build
  internally.  Only the state column differs, and no theorem reads it.
\<close>

lemma out_checks_of_verdict_report_answer:
  assumes "verdict_report_answer view rows = Analysed out"
  shows "out_checks out = check_rows_of (\<lambda>_. Bot) rows"
  using assms unfolding verdict_report_answer_def report_output_def
  by (auto split: output_view.splits)

lemma out_checks_of_cs_output:
  assumes "cs_output_of view into classify r k p = Analysed out"
  shows "out_checks out
           = check_rows_of (project_joined_env into r)
               (classify_checks_verdicts (prog_cfg p) r classify)"
  using assms
  by (cases view)
     (auto simp: cs_output_of_def contextual_output_def report_output_def
        collapsed_output_def Let_def)

lemma decided_row_in_entry_state_verdicts:
  assumes ans: "entry_state_output_of view enter into classify r p = Analysed out"
      and row: "row \<in> set (out_checks out)"
      and dec: "row_verdict row = Decided res"
  shows "(row_point row, row_exp row, Decided res)
           \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
  using row [unfolded out_checks_of_entry_state_output [OF ans]] dec
  by (rule decided_row_of_check_rows)

lemma decided_row_in_cs_verdicts:
  assumes ans: "cs_output_of view into classify r k p = Analysed out"
      and row: "row \<in> set (out_checks out)"
      and dec: "row_verdict row = Decided res"
  shows "(row_point row, row_exp row, Decided res)
           \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
  using row [unfolded out_checks_of_cs_output [OF ans]] dec
  by (rule decided_row_of_check_rows)

text \<open>
  The same correspondence without deciding the verdict first, which is what a
  claim about a \<^const>\<open>Dead\<close> row needs: the row's own verdict, whatever it is, is
  the one the report filed at that point and condition.
\<close>

lemma row_in_check_rows:
  assumes "row \<in> set (check_rows_of env rows)"
  shows "(row_point row, row_exp row, row_verdict row) \<in> set rows"
  using assms by (auto simp: check_rows_of_def)

subsection \<open>A store that reaches a point sits in one of that point's contexts\<close>

text \<open>
  The published contextual soundness bounds one activation bucket by the table
  entry filed under that bucket's context. A caller holding a store knows only
  that the store reaches the point at all, so it needs the buckets to exhaust
  the point --- the union direction, which is where a context policy pays for
  being total. Both readings are settled in
  \<^theory>\<open>Voblint_CFG.LTR_Collect\<close>: a functional policy has the union outright,
  a relational one --- such as the entry-state policy --- earns it from the
  existence of a context for every valid trace. Either way the caller arrives
  with the inclusion the next lemma consumes.
\<close>

text \<open>
  The two halves composed, in the shape a caller can use: a store known to reach
  \<^term>\<open>v\<close> is described by a \<^emph>\<open>reachable\<close> table entry at \<^term>\<open>v\<close> under some
  context. \<^const>\<open>Bot\<close> cannot be that entry --- it concretizes to no store at
  all --- so the context this produces is one the solve actually covered, which
  is what the per-context check soundness below needs as its premise.
\<close>

lemma lookup_context_covers_of_activation:
  fixes r :: "('c, 'a::sound_domain abs_state) analysis_result"
  assumes union: "ltr_collect gs g S v \<subseteq> (\<Union>c. activation_collect gs R rc g S v c)"
      and sound: "\<And>ctx. activation_collect gs R rc g S v ctx
                    \<subseteq> gamma_point (lookup_context r v ctx)"
      and mem: "s \<in> ltr_collect gs g S v"
  obtains ctx st where "s \<in> activation_collect gs R rc g S v ctx"
    and "lookup_context r v ctx = Lifted st" and "s \<in> \<lbrakk>st\<rbrakk>"
proof -
  from mem union obtain ctx where a: "s \<in> activation_collect gs R rc g S v ctx" by blast
  with sound have g: "s \<in> gamma_point (lookup_context r v ctx)" by blast
  show ?thesis
  proof (cases "lookup_context r v ctx")
    case Bot
    with g show ?thesis by simp
  next
    case (Lifted st)
    with g a show ?thesis by (intro that [of ctx st]) simp_all
  qed
qed

subsection \<open>The endpoint, over an arbitrary context policy\<close>

text \<open>
  The contextual counterpart of \<open>run_voblint_source_sound\<close>, with the two
  policy-dependent facts left as premises: that the activation buckets exhaust
  each point, and that each bucket is described by the table entry filed under
  its context. Everything else --- reaching a graph node from a source run,
  finding a covered context, reading the check column --- is fixed here, so an
  instance owes only those two and its domain's own classifier soundness.

  The state conclusion names the context, and that is the substance of the
  difference from the context-free endpoint. There the table has one entry per
  point and the store sits in it; here it has one per point and context, and the
  store sits in \<^emph>\<open>at least one\<close> of them --- a context its own call history is
  admitted at, unique when the policy keys on that history alone. A statement
  quantifying over every context the node was solved at instead would be false:
  another activation's entry need not describe this store at all.
\<close>

text \<open>
  The check column's claim at a node the caller names, rather than at the node a
  source run happened to reach. This is the half of the endpoint below that does
  not mention a source execution at all: given a store the collecting semantics
  admits at \<open>v\<close>, every row printed for \<open>v\<close> is correct of it. A caller who can
  exhibit that store --- by walking the graph, say --- gets the verdict claim at
  the point it was printed for, which the existential witness below cannot give.
\<close>

lemma ctx_rows_sound_at:
  fixes p :: imp_prog and s :: store
    and r :: "('c, 'a::sound_domain abs_state) analysis_result"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
  assumes union: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                          (cinit_stores (declared_global p)) u
                    \<subseteq> (\<Union>c. activation_collect (declared_global p) R rc (prog_cfg p)
                                (cinit_stores (declared_global p)) u c)"
      and sound: "\<And>u ctx. activation_collect (declared_global p) R rc (prog_cfg p)
                              (cinit_stores (declared_global p)) u ctx
                    \<subseteq> gamma_point (lookup_context r u ctx)"
      and fin: "finite_analysis_result r"
      and proved: "\<And>c d t. classify c d = Check_Proved \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> truthy (aval c t)"
      and refuted: "\<And>c d t. classify c d = Check_Refuted \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk>
                        \<Longrightarrow> \<not> truthy (aval c t)"
      and rows: "out_checks out
                   = check_rows_of env (classify_checks_verdicts (prog_cfg p) r classify)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
           row_verdict row \<noteq> Dead
         \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
         \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain ctx st where act: "s \<in> activation_collect (declared_global p) R rc (prog_cfg p)
                                  (cinit_stores (declared_global p)) v ctx"
    and look: "lookup_context r v ctx = Lifted st" and gst: "s \<in> \<lbrakk>st\<rbrakk>"
    by (rule lookup_context_covers_of_activation [OF union sound mem])
  have decided: "(v, row_exp row, Decided res)
                   \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
    if "row \<in> set (out_checks out)" and "row_point row = v" and "row_verdict row = Decided res"
    for row res
    using decided_row_of_check_rows [OF that(1) [unfolded rows] that(3)] that(2) by simp
  show ?thesis
  proof (intro ballI impI conjI)
    fix row
    assume rm: "row \<in> set (out_checks out)" and at: "row_point row = v"
    show "row_verdict row \<noteq> Dead"
    proof
      assume dead: "row_verdict row = Dead"
      from row_in_check_rows [OF rm [unfolded rows]] at dead
      have "(v, row_exp row, Dead) \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
        by simp
      then have agg: "aggregate_verdicts
                        ((\<lambda>c'. classify_point classify (row_exp row) (lookup_context r v c'))
                           ` contexts_at r v) = Dead"
        using classify_checks_verdicts_mem_iff [OF finI] by metis
      have "classify_point classify (row_exp row) (lookup_context r v ctx)
              \<in> (\<lambda>c'. classify_point classify (row_exp row) (lookup_context r v c'))
                  ` contexts_at r v"
        using lookup_context_LiftedD [OF look] by blast
      with agg aggregate_verdicts_eq_Dead_iff [OF finite_imageI [OF finite_contexts_at [OF fin]]]
      have "classify_point classify (row_exp row) (lookup_context r v ctx) = Dead" by meson
      with look show False by simp
    qed
  next
    fix row
    assume "row \<in> set (out_checks out)" and "row_point row = v"
       and "row_verdict row = Decided Check_Proved"
    from classify_checks_ctx_proved_sound [OF finI decided [OF this] look]
    show "truthy (aval (row_exp row) s)" by (rule proved) (rule gst)
  next
    fix row
    assume "row \<in> set (out_checks out)" and "row_point row = v"
       and "row_verdict row = Decided Check_Refuted"
    from classify_checks_ctx_refuted_sound [OF finI decided [OF this] look]
    show "\<not> truthy (aval (row_exp row) s)" by (rule refuted) (rule gst)
  qed
qed

theorem ctx_source_sound_of_activation:
  fixes p :: imp_prog and s0 s :: store
    and r :: "('c, 'a::sound_domain abs_state) analysis_result"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and union: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                          (cinit_stores (declared_global p)) u
                    \<subseteq> (\<Union>c. activation_collect (declared_global p) R rc (prog_cfg p)
                                (cinit_stores (declared_global p)) u c)"
      and sound: "\<And>u ctx. activation_collect (declared_global p) R rc (prog_cfg p)
                              (cinit_stores (declared_global p)) u ctx
                    \<subseteq> gamma_point (lookup_context r u ctx)"
      and fin: "finite_analysis_result r"
      and proved: "\<And>c d t. classify c d = Check_Proved \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> truthy (aval c t)"
      and refuted: "\<And>c d t. classify c d = Check_Refuted \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> \<not> truthy (aval c t)"
      and rows: "out_checks out
                   = check_rows_of env (classify_checks_verdicts (prog_cfg p) r classify)"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p) R rc (prog_cfg p)
                   (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context r v ctx = Lifted st \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)" by (rule prog_cfg_def)
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  from source_reaches_ltr_collect [OF wf s0 run]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
    unfolding cfg by blast
  obtain ctx st where act: "s \<in> activation_collect (declared_global p) R rc (prog_cfg p)
                                  (cinit_stores (declared_global p)) v ctx"
    and look: "lookup_context r v ctx = Lifted st" and gst: "s \<in> \<lbrakk>st\<rbrakk>"
    by (rule lookup_context_covers_of_activation [OF union sound mem])
  have decided: "(v, row_exp row, Decided res)
                   \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
    if "row \<in> set (out_checks out)" and "row_point row = v" and "row_verdict row = Decided res"
    for row res
    using decided_row_of_check_rows [OF that(1) [unfolded rows] that(3)] that(2) by simp
  have checks: "\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
                  row_verdict row \<noteq> Dead
                \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
                \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))"
  proof (intro ballI impI conjI)
    fix row
    assume rm: "row \<in> set (out_checks out)" and at: "row_point row = v"
    show "row_verdict row \<noteq> Dead"
    proof
      assume dead: "row_verdict row = Dead"
      from row_in_check_rows [OF rm [unfolded rows]] at dead
      have "(v, row_exp row, Dead) \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
        by simp
      then have agg: "aggregate_verdicts
                        ((\<lambda>c'. classify_point classify (row_exp row) (lookup_context r v c'))
                           ` contexts_at r v) = Dead"
        using classify_checks_verdicts_mem_iff [OF finI] by metis
      have "classify_point classify (row_exp row) (lookup_context r v ctx)
              \<in> (\<lambda>c'. classify_point classify (row_exp row) (lookup_context r v c'))
                  ` contexts_at r v"
        using lookup_context_LiftedD [OF look] by blast
      with agg aggregate_verdicts_eq_Dead_iff [OF finite_imageI [OF finite_contexts_at [OF fin]]]
      have "classify_point classify (row_exp row) (lookup_context r v ctx) = Dead" by meson
      with look show False by simp
    qed
  next
    fix row
    assume "row \<in> set (out_checks out)" and "row_point row = v"
       and "row_verdict row = Decided Check_Proved"
    from classify_checks_ctx_proved_sound [OF finI decided [OF this] look]
    show "truthy (aval (row_exp row) s)" by (rule proved) (rule gst)
  next
    fix row
    assume "row \<in> set (out_checks out)" and "row_point row = v"
       and "row_verdict row = Decided Check_Refuted"
    from classify_checks_ctx_refuted_sound [OF finI decided [OF this] look]
    show "\<not> truthy (aval (row_exp row) s)" by (rule refuted) (rule gst)
  qed
  from m act look gst checks show ?thesis by blast
qed

subsection \<open>What a dead row claims, contextually\<close>

text \<open>
  The contextual counterpart of \<open>dead_row_unreached\<close>, and it lands in the same
  shape rather than a context-indexed one.  A dead aggregate means no context
  published a live entry at the point, so every bucket there is empty; the union
  premise then collapses them back to the context-insensitive collection.  So
  the conclusion is again that nothing reaches the point at all, which is what a
  reader wants a dead marker to mean, and it needs no context to state.
\<close>

theorem ctx_dead_row_unreached:
  fixes p :: imp_prog
    and r :: "('c, 'a::sound_domain abs_state) analysis_result"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
  assumes union: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                          (cinit_stores (declared_global p)) u
                    \<subseteq> (\<Union>c. activation_collect (declared_global p) R rc (prog_cfg p)
                                (cinit_stores (declared_global p)) u c)"
      and sound: "\<And>u ctx. activation_collect (declared_global p) R rc (prog_cfg p)
                              (cinit_stores (declared_global p)) u ctx
                    \<subseteq> gamma_point (lookup_context r u ctx)"
      and fin: "finite_analysis_result r"
      and rows: "out_checks out
                   = check_rows_of env (classify_checks_verdicts (prog_cfg p) r classify)"
      and row: "row \<in> set (out_checks out)"
      and dead: "row_verdict row = Dead"
  shows "ltr_collect (declared_global p) (prog_cfg p)
           (cinit_stores (declared_global p)) (row_point row) = {}"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  from row_in_check_rows [OF row [unfolded rows]] dead
  have "(row_point row, row_exp row, Dead)
          \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
    by simp
  then have agg: "aggregate_verdicts
                    ((\<lambda>c'. classify_point classify (row_exp row)
                             (lookup_context r (row_point row) c'))
                       ` contexts_at r (row_point row)) = Dead"
    using classify_checks_verdicts_mem_iff [OF finI] by metis
  have bot: "lookup_context r (row_point row) ctx = Bot" for ctx
  proof (rule ccontr)
    assume "lookup_context r (row_point row) ctx \<noteq> Bot"
    then obtain st where look: "lookup_context r (row_point row) ctx = Lifted st"
      by (cases "lookup_context r (row_point row) ctx") auto
    have "classify_point classify (row_exp row) (lookup_context r (row_point row) ctx)
            \<in> (\<lambda>c'. classify_point classify (row_exp row)
                       (lookup_context r (row_point row) c'))
                ` contexts_at r (row_point row)"
      using lookup_context_LiftedD [OF look] by blast
    with agg aggregate_verdicts_eq_Dead_iff [OF finite_imageI [OF finite_contexts_at [OF fin]]]
    have "classify_point classify (row_exp row) (lookup_context r (row_point row) ctx) = Dead"
      by meson
    with look show False by simp
  qed
  have "activation_collect (declared_global p) R rc (prog_cfg p)
          (cinit_stores (declared_global p)) (row_point row) ctx = {}" for ctx
    using sound [of "row_point row" ctx] by (simp add: bot)
  with union [of "row_point row"] show ?thesis by blast
qed

subsection \<open>Sign at the entry-state configuration\<close>

text \<open>
  The generic endpoint at one concrete configuration, over the operation
  \<^const>\<open>run_voblint\<close> exports. Everything the abstraction asked for is discharged
  by name here: the union comes from
  \<^const>\<open>sign_entry_state_context_rel\<close>'s totality, the per-bucket bound
  from Sign's own routed soundness, and the reader-to-table step from Sign's
  \<open>gamma_reader_eq_lookup\<close> alias. What is left as premises is the coverage the
  solve achieved, which nothing here proves for an arbitrary program --- the same
  standing that \<^const>\<open>analyse_certified\<close> has at the context-free configuration,
  and the same shape: a termination fact and one coverage fact. The coverage is
  \<^const>\<open>ctx_vars_cover\<close> rather than \<^const>\<open>vars_cover\<close>, whose key type is
  \<^typ>\<open>unit\<close>, and it is closure rather than blanket coverage --- which contexts
  a node was solved at is decided by the run.
\<close>

theorem run_voblint_sign_entry_state_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "sign_entry_state_terminates_for (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (sign_es.ctx_succ (declared_global p) p) []
                    (sign_entry_state_vars (declared_global p) p)"
      and ans: "run_voblint Sign_Analysis None Ctx_EntryState view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (sign_entry_state_context_rel (declared_global p) p) [] (prog_cfg p)
                   (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_sign_entry_state_result p) v ctx = Lifted st \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  have res: "analyse_sign_entry_state_result p
               = analyse_sign_entry_state_result_for (declared_global p) p"
    by (rule analyse_sign_entry_state_result_def)
  from ans
  have "entry_state_output_of view enter_sign_for SignValue sign_classify_check
          (analyse_sign_entry_state_result p) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_entry_state_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ sign_classify_check_proved sign_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (sign_entry_state_context_rel (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: analyse_sign_entry_state_ltr_collect_eq_Union_of_cover [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (sign_entry_state_context_rel (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_sign_entry_state_result p) u ctx)"
      using analyse_sign_entry_state_sound_of_cover [OF cov]
      unfolding res analyse_sign_entry_state_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_sign_entry_state_result p)"
      using sign_es.vars_finite_of_terminates [OF solves]
      by (simp add: finite_analysis_result_def analyse_sign_entry_state_result_def
          sign_es.result_def sign_es.sol_vars_def)
  qed
qed

subsection \<open>Sign at the call-string configuration\<close>

text \<open>
  The call-string route is a function of the call site and the caller's context
  alone, so its union side is unconditional --- there is no context-totality
  obligation to discharge, unlike entry state. What is left is the same single
  closure premise. The published constants stop at the result table here, so the
  solve's termination, its solved keys and its successor function are named the
  way \<^const>\<open>routed_dg_pipeline.result\<close> is: by spelling out the pipeline at this
  route's own operands.
\<close>

abbreviation sign_cs_terminates where
  "sign_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation sign_cs_ctx_succ where
  "sign_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation sign_cs_vars where
  "sign_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars sign_tf_st_for sign_enter_st_for cinit_sign_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

theorem run_voblint_sign_call_string_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "sign_cs_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (sign_cs_ctx_succ k (declared_global p) p) []
                    (sign_cs_vars k (declared_global p) p)"
      and ans: "run_voblint Sign_Analysis None (Ctx_CallString k) view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_sign_call_string_result k p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "cs_output_of view SignValue sign_classify_check
          (analyse_sign_call_string_result k p) k p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_cs_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ sign_classify_check_proved sign_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_sign_call_string_ltr_collect_eq_Union
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_sign_call_string_result k p) u ctx)"
      using analyse_sign_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_sign_call_string_result_def
                analyse_sign_call_string_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_sign_call_string_result k p)"
      using analyse_sign_call_string_vars_finite [OF solves]
      by (simp add: finite_analysis_result_def analyse_sign_call_string_result_def
          routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
  qed
qed

subsection \<open>Parity, Congruence, Interval and Int at the call-string configuration\<close>

text \<open>
  The same block at the four remaining domains. Parity and Congruence solve by
  joining and Interval and Int by warrowing, which shows up only in the operands
  the pipeline is spelled out at; the argument does not notice.
\<close>

abbreviation parity_cs_terminates where
  "parity_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates parity_tf_st_for parity_enter_st_for cinit_parity_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation parity_cs_ctx_succ where
  "parity_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ parity_tf_st_for parity_enter_st_for cinit_parity_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation parity_cs_vars where
  "parity_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars parity_tf_st_for parity_enter_st_for cinit_parity_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

theorem run_voblint_parity_call_string_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "parity_cs_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (parity_cs_ctx_succ k (declared_global p) p) []
                    (parity_cs_vars k (declared_global p) p)"
      and ans: "run_voblint Parity_Analysis None (Ctx_CallString k) view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_parity_call_string_result k p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "cs_output_of view ParityValue parity_classify_check
          (analyse_parity_call_string_result k p) k p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_cs_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ parity_classify_check_proved parity_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_parity_call_string_ltr_collect_eq_Union
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_parity_call_string_result k p) u ctx)"
      using analyse_parity_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_parity_call_string_result_def
                analyse_parity_call_string_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_parity_call_string_result k p)"
      using analyse_parity_call_string_vars_finite [OF solves]
      by (simp add: finite_analysis_result_def analyse_parity_call_string_result_def
          routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
  qed
qed

abbreviation congruence_cs_terminates where
  "congruence_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates congruence_tf_st_for congruence_enter_st_for
       cinit_congruence_st Call_String_Context.Global Call_String_Context.Seed
       (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation congruence_cs_ctx_succ where
  "congruence_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ congruence_tf_st_for congruence_enter_st_for
       cinit_congruence_st Call_String_Context.Global Call_String_Context.Seed
       (\<lambda>_. cs_route k) [] TD_side_always_join_Interp_solve"

abbreviation congruence_cs_vars where
  "congruence_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars congruence_tf_st_for congruence_enter_st_for
       cinit_congruence_st Call_String_Context.Global Call_String_Context.Seed
       (\<lambda>_. cs_route k) [] TD_side_always_join_Interp_solve"

theorem run_voblint_congruence_call_string_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "congruence_cs_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p)
                    (congruence_cs_ctx_succ k (declared_global p) p) []
                    (congruence_cs_vars k (declared_global p) p)"
      and ans: "run_voblint Congruence_Analysis None (Ctx_CallString k) view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_congruence_call_string_result k p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "cs_output_of view CongruenceValue congruence_classify_check
          (analyse_congruence_call_string_result k p) k p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_cs_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ congruence_classify_check_proved congruence_classify_check_refuted
          rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_congruence_call_string_ltr_collect_eq_Union
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_congruence_call_string_result k p) u ctx)"
      using analyse_congruence_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_congruence_call_string_result_def
                analyse_congruence_call_string_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_congruence_call_string_result k p)"
      using analyse_congruence_call_string_vars_finite [OF solves]
      by (simp add: finite_analysis_result_def analyse_congruence_call_string_result_def
          routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
  qed
qed

abbreviation interval_cs_terminates where
  "interval_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_warrowing_apinis)"

abbreviation interval_cs_ctx_succ where
  "interval_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation interval_cs_vars where
  "interval_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

theorem run_voblint_interval_call_string_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_cs_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (interval_cs_ctx_succ k (declared_global p) p) []
                    (interval_cs_vars k (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis None (Ctx_CallString k) view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_interval_call_string_result k p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "cs_output_of view IntervalValue interval_classify_check
          (analyse_interval_call_string_result k p) k p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_cs_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ interval_classify_check_proved interval_classify_check_refuted
          rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_interval_call_string_ltr_collect_eq_Union
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_interval_call_string_result k p) u ctx)"
      using analyse_interval_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_interval_call_string_result_def
                analyse_interval_call_string_result_for_def
                analyse_interval_call_string_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_interval_call_string_result k p)"
      using analyse_interval_call_string_vars_finite [OF solves]
      by (simp add: finite_analysis_result_def analyse_interval_call_string_result_def
          analyse_interval_call_string_result_for_def
          routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
  qed
qed

abbreviation int_cs_terminates where
  "int_cs_terminates k \<equiv>
     routed_dg_pipeline.terminates (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_warrowing_apinis)"

abbreviation int_cs_ctx_succ where
  "int_cs_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation int_cs_vars where
  "int_cs_vars k \<equiv>
     routed_dg_pipeline.sol_vars (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_apinis_Interp_solve"

theorem run_voblint_int_call_string_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "int_cs_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (int_cs_ctx_succ k (declared_global p) p) []
                    (int_cs_vars k (declared_global p) p)"
      and ans: "run_voblint Int_Analysis None (Ctx_CallString k) view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_int_call_string_result_warrow k p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "cs_output_of view IntDomValue int_classify_check
          (analyse_int_call_string_result_warrow k p) k p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_cs_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ int_classify_check_proved int_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_int_call_string_ltr_collect_eq_Union_warrow
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point
                 (lookup_context (analyse_int_call_string_result_warrow k p) u ctx)"
      using analyse_int_call_string_sound_of_cover_warrow [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_int_call_string_result_warrow_def
                analyse_int_call_string_result_for_warrow_def
                analyse_int_call_string_gamma_reader_eq_lookup_warrow .
  next
    show "finite_analysis_result (analyse_int_call_string_result_warrow k p)"
      using analyse_int_call_string_vars_finite_warrow [OF solves]
      by (simp add: finite_analysis_result_def analyse_int_call_string_result_warrow_def
          analyse_int_call_string_result_for_warrow_def
          routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
  qed
qed

subsection \<open>Parity and Congruence at the entry-state configuration\<close>

text \<open>
  The same instantiation at the two remaining join-solved domains. Nothing is
  domain-specific but the names: each supplies its own classifier soundness, its
  own published table, and its own pair of packaged coverage endpoints.
\<close>

theorem run_voblint_parity_entry_state_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "parity_entry_state_terminates_for (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (parity_es.ctx_succ (declared_global p) p) []
                    (parity_entry_state_vars (declared_global p) p)"
      and ans: "run_voblint Parity_Analysis None Ctx_EntryState view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (parity_entry_state_context_rel (declared_global p) p) [] (prog_cfg p)
                   (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_parity_entry_state_result p) v ctx = Lifted st \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  have res: "analyse_parity_entry_state_result p
               = analyse_parity_entry_state_result_for (declared_global p) p"
    by (rule analyse_parity_entry_state_result_def)
  from ans
  have "entry_state_output_of view enter_parity_for ParityValue parity_classify_check
          (analyse_parity_entry_state_result p) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_entry_state_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ parity_classify_check_proved parity_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (parity_entry_state_context_rel (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: analyse_parity_entry_state_ltr_collect_eq_Union_of_cover [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (parity_entry_state_context_rel (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_parity_entry_state_result p) u ctx)"
      using analyse_parity_entry_state_sound_of_cover [OF cov]
      unfolding res analyse_parity_entry_state_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_parity_entry_state_result p)"
      using parity_es.vars_finite_of_terminates [OF solves]
      by (simp add: finite_analysis_result_def analyse_parity_entry_state_result_def
          parity_es.result_def parity_es.sol_vars_def)
  qed
qed

theorem run_voblint_congruence_entry_state_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "congruence_entry_state_terminates_for (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (congruence_es.ctx_succ (declared_global p) p) []
                    (congruence_entry_state_vars (declared_global p) p)"
      and ans: "run_voblint Congruence_Analysis None Ctx_EntryState view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (congruence_entry_state_context_rel (declared_global p) p) [] (prog_cfg p)
                   (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_congruence_entry_state_result p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  have res: "analyse_congruence_entry_state_result p
               = analyse_congruence_entry_state_result_for (declared_global p) p"
    by (rule analyse_congruence_entry_state_result_def)
  from ans
  have "entry_state_output_of view enter_congruence_for CongruenceValue
          congruence_classify_check (analyse_congruence_entry_state_result p) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_entry_state_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ congruence_classify_check_proved congruence_classify_check_refuted
          rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (congruence_entry_state_context_rel (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: analyse_congruence_entry_state_ltr_collect_eq_Union_of_cover [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (congruence_entry_state_context_rel (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_congruence_entry_state_result p) u ctx)"
      using analyse_congruence_entry_state_sound_of_cover [OF cov]
      unfolding res analyse_congruence_entry_state_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_congruence_entry_state_result p)"
      using congruence_es.vars_finite_of_terminates [OF solves]
      by (simp add: finite_analysis_result_def analyse_congruence_entry_state_result_def
          congruence_es.result_def congruence_es.sol_vars_def)
  qed
qed

subsection \<open>Interval at the entry-state configuration\<close>

text \<open>
  Interval's entry-state route is solved by warrowing rather than by joining, so
  \<^const>\<open>run_voblint\<close> with no solver resolves it to that discipline. Nothing in
  the argument changes: the discipline is already sealed inside the published
  coverage endpoints, which is why the instantiation reads the same as the
  join-solved domains above.
\<close>

theorem run_voblint_interval_entry_state_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "entry_state_terminates_prog (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (interval_es.ctx_succ (declared_global p) p) []
                    (entry_state_vars_prog (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis None Ctx_EntryState view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (entry_state_context_rel (declared_global p) p) [] (prog_cfg p)
                   (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_interval_entry_state_result p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  have res: "analyse_interval_entry_state_result p
               = analyse_interval_entry_state_result_for (declared_global p) p"
    by (rule analyse_interval_entry_state_result_def)
  from ans
  have "entry_state_output_of view enter_ivl_for IntervalValue interval_classify_check
          (analyse_interval_entry_state_result p) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_entry_state_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ interval_classify_check_proved interval_classify_check_refuted
          rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (entry_state_context_rel (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: entry_state_ltr_collect_eq_Union_of_cover [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (entry_state_context_rel (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_interval_entry_state_result p) u ctx)"
      using entry_state_activation_collect_sound_of_cover [OF cov]
      unfolding res entry_state_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_interval_entry_state_result p)"
      using interval_es.vars_finite_of_terminates [OF solves]
      by (simp add: finite_analysis_result_def analyse_interval_entry_state_result_def
          interval_es.result_def interval_es.sol_vars_def)
  qed
qed

subsection \<open>Int at the entry-state configuration\<close>

text \<open>
  Int's registrations are parameterised by a \<^typ>\<open>refine_mode\<close>, so they are
  plain interpretations inside a context block and export no binder a caller
  outside can name. Its published constants are spelled out from the pipeline
  instead, at the mode the dispatcher uses; \<^const>\<open>routed_dg_pipeline.ctx_succ\<close>
  is named the same way here, which is why it had to sit in the pipeline locale
  rather than beside the soundness endpoints.
\<close>

abbreviation int_es_ctx_succ where
  "int_es_ctx_succ \<equiv>
     routed_dg_pipeline.ctx_succ
       (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation int_es_terminates where
  "int_es_terminates \<equiv>
     routed_dg_pipeline.terminates
       (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed exec_formals_route []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_warrowing_apinis)"

abbreviation int_es_vars where
  "int_es_vars \<equiv>
     routed_dg_pipeline.sol_vars
       (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_apinis_Interp_solve"

abbreviation int_es_ctx_rel where
  "int_es_ctx_rel \<equiv>
     routed_dg_analysis.admitted_contexts
       (int_tf_st_for Refine_Fixpoint) (int_dom_enter_st_for Refine_Fixpoint)
       cinit_int_dom_st (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_warrowing_apinis_Interp_solve"

theorem run_voblint_int_entry_state_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "int_es_terminates (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p)
                    (int_es_ctx_succ (declared_global p) p) []
                    (int_es_vars (declared_global p) p)"
      and ans: "run_voblint Int_Analysis None Ctx_EntryState view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (int_es_ctx_rel (declared_global p) p) [] (prog_cfg p)
                   (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_int_entry_state_result_warrow p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  have res: "analyse_int_entry_state_result_warrow p
               = analyse_int_entry_state_result_for_warrow (declared_global p) p"
    by (rule analyse_int_entry_state_result_warrow_def)
  from ans
  have "entry_state_output_of view (enter_int_dom_for Refine_Fixpoint) IntDomValue
          int_classify_check (analyse_int_entry_state_result_warrow p) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_entry_state_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ int_classify_check_proved int_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (int_es_ctx_rel (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: analyse_int_entry_state_ltr_collect_eq_Union_of_cover_warrow [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (int_es_ctx_rel (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point
                 (lookup_context (analyse_int_entry_state_result_warrow p) u ctx)"
      using analyse_int_entry_state_sound_of_cover_warrow [OF cov]
      by (simp add: analyse_int_entry_state_gamma_reader_eq_lookup_warrow
          analyse_int_entry_state_result_for_warrow_def res)
  next
    show "finite_analysis_result (analyse_int_entry_state_result_warrow p)"
      using analyse_int_entry_state_vars_finite_warrow [OF solves]
      by (simp add: finite_analysis_result_def analyse_int_entry_state_result_warrow_def
          analyse_int_entry_state_result_for_warrow_def
          routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
  qed
qed

end
