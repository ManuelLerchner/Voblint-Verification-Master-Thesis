theory Source_Progress
  imports Simulation_Preservation
begin

section \<open>Reachable source configurations are never stuck\<close>

text \<open>
  A stuck source configuration would silently cut executions short: every later program point
  would be unreachable under \<^const>\<open>pstep\<close>, so an unreachability verdict could hold for the
  wrong reason.  Progress rules this out for accepted programs: a reachable configuration
  either has finished --- \<^const>\<open>SKIP\<close> with no caller frame left --- or can take a step.

  The shapes that could get stuck are the runtime markers: a bare \<^const>\<open>Unwind\<close>, and a
  \<^const>\<open>Restore\<close> or \<^term>\<open>Seq Unwind Restore\<close> with no frame to pop.  \<^const>\<open>csim\<close> already
  pairs every \<^const>\<open>Restore\<close> with its frame and confines \<^const>\<open>Unwind\<close> to the returning
  phase, so it is reused here as the invariant; the only additional fact is that call sites
  are well formed.
\<close>

subsection \<open>Source commands\<close>

lemma pstep_seq_after_lift:
  "\<G>, \<Pi> \<turnstile> (w, s, frs) \<rightarrow>\<^sub>p (w', s', frs')
   \<Longrightarrow> \<G>, \<Pi> \<turnstile> (seq_after w afters, s, frs) \<rightarrow>\<^sub>p (seq_after w' afters, s', frs')"
  by (induction afters arbitrary: w w') auto

text \<open>A well-formed source command is \<^const>\<open>SKIP\<close> or steps, at any frame stack.  A
  \<^const>\<open>Return\<close> steps too; whether its \<^const>\<open>Unwind\<close> can later pop a frame is the
  simulation's concern, not this lemma's.\<close>
lemma wf_source_com_progress:
  assumes distinct_formals: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> distinct (formals decl)"
      and "wf_source_com \<Pi> c"
  shows "c = SKIP \<or> (\<exists>cfg'. \<G>, \<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p cfg')"
  using assms(2)
proof (induction c)
  case (Seq c1 c2)
  from Seq.prems have "wf_source_com \<Pi> c1" by simp
  from Seq.IH(1)[OF this] show ?case
  proof
    assume "c1 = SKIP"
    then show ?thesis by blast
  next
    assume "\<exists>cfg'. \<G>, \<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p cfg'"
    then obtain c1' s' frs' where "\<G>, \<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p (c1', s', frs')" by auto
    then show ?thesis by blast
  qed
next
  case (If b c1 c2)
  show ?case by (cases "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s)") blast+
next
  case (Return e)
  show ?case by (cases e) blast+
next
  case (Call dst p actuals)
  show ?case
  proof (cases "special_table p")
    case None
    with Call.prems obtain decl where
      decl: "\<Pi> p = Some decl" and arity: "length actuals = length (formals decl)"
      by (auto split: option.splits)
    show ?thesis
      using pstep_Call[where \<Pi> = \<Pi> and p = p, OF decl arity distinct_formals[OF decl]]
      by blast
  next
    case (Some desc)
    with Call.prems obtain sc x where
      sc: "classify_special desc actuals = Some sc" and dst: "dst = Some x"
      by (auto split: option.splits)
    obtain v where "special_result sc s v" using special_result_ex by blast
    with Some sc show ?thesis unfolding dst by blast
  qed
qed auto

lemma control_at_wf_source_com:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> wf_source_com \<Pi> c0 \<Longrightarrow> wf_source_com \<Pi> r"
  by (induction rule: control_at.induct) auto

subsection \<open>The frame-pop phase\<close>

lemma unwinding_progress:
  "unwinding u \<Longrightarrow> u \<noteq> Unwind \<Longrightarrow> \<exists>u'. \<G>, \<Pi> \<turnstile> (u, s, frs) \<rightarrow>\<^sub>p (u', s, frs)"
proof (induction u)
  case (Seq u1 c2)
  then have u1: "unwinding u1" and c2: "c2 \<noteq> Restore" by simp_all
  show ?case
  proof (cases "u1 = Unwind")
    case True
    then show ?thesis using c2 by blast
  next
    case False
    from Seq.IH(1)[OF u1 False] obtain u1' where "\<G>, \<Pi> \<turnstile> (u1, s, frs) \<rightarrow>\<^sub>p (u1', s, frs)" ..
    then show ?thesis by blast
  qed
qed simp_all

text \<open>The frame a \<open>Returning\<close> configuration carries is what lets it pop.\<close>
lemma pop_ready_progress:
  assumes "pop_ready w"
  shows "\<exists>cfg'. \<G>, \<Pi> \<turnstile> (w, s, Frame fr dst # frs) \<rightarrow>\<^sub>p cfg'"
  using assms
proof (cases w rule: pop_ready.cases)
  case 1
  then show ?thesis by blast
next
  case (2 u)
  with assms have uw: "unwinding u" by simp
  show ?thesis
  proof (cases "u = Unwind")
    case True
    then show ?thesis using 2 by blast
  next
    case False
    from unwinding_progress[OF uw False] obtain u' where
      "\<G>, \<Pi> \<turnstile> (u, s, Frame fr dst # frs) \<rightarrow>\<^sub>p (u', s, Frame fr dst # frs)" ..
    then show ?thesis using 2 by blast
  qed
qed (use assms in simp_all)

subsection \<open>Progress under the simulation relation\<close>

text \<open>Only a \<open>Base\<close> activation can have finished: \<open>Nested\<close> and \<open>Returning\<close> both carry a
  caller frame and a pending \<^const>\<open>Restore\<close> that will pop it.  No graph fact is used, so
  the relation serves here purely as a shape invariant.\<close>
lemma csim_progress_cfg:
  assumes "\<Pi>, g \<turnstile> cfg \<approx> dg"
      and wf_decls: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> wf_proc_decl \<G> \<Pi> decl"
  shows "(fst cfg = SKIP \<and> snd (snd cfg) = []) \<or> (\<exists>cfg'. \<G>, \<Pi> \<turnstile> cfg \<rightarrow>\<^sub>p cfg')"
  using assms(1)
proof (induction rule: csim.induct)
  case (Base p c0 k n c v s)
  from Base.hyps(2) obtain decl where decl: "\<Pi> p = Some decl" and c0: "c0 = body decl"
    by (rule compiled_at_decl)
  have "wf_source_com \<Pi> c0"
    using wf_decls[OF decl] c0 by (simp add: wf_proc_decl_def)
  from control_at_wf_source_com[OF Base.hyps(1) this]
  have "wf_source_com \<Pi> c" .
  from wf_source_com_progress[OF _ this, of \<G> s "[]"] wf_decls
  show ?case by (auto simp: wf_proc_decl_def)
next
  case (Nested inner s frs v stk pc c0c kc nc afters cont caller dst)
  let ?F = "[Frame caller dst]"
  have "\<exists>w'. \<G>, \<Pi> \<turnstile> (Seq inner Restore, s, frs @ ?F) \<rightarrow>\<^sub>p w'"
    using Nested.IH
  proof
    assume "fst (inner, s, frs) = SKIP \<and> snd (snd (inner, s, frs)) = []"
    then show ?thesis by auto
  next
    assume "\<exists>cfg'. \<G>, \<Pi> \<turnstile> (inner, s, frs) \<rightarrow>\<^sub>p cfg'"
    then obtain i' s' f' where "\<G>, \<Pi> \<turnstile> (inner, s, frs) \<rightarrow>\<^sub>p (i', s', f')" by auto
    from pstep_frame_extend[OF this, of ?F]
    show ?thesis by blast
  qed
  then obtain w' s' f' where "\<G>, \<Pi> \<turnstile> (Seq inner Restore, s, frs @ ?F) \<rightarrow>\<^sub>p (w', s', f')"
    by auto
  from pstep_seq_after_lift[OF this, of afters] show ?case by auto
next
  case (Returning w pc c0c kc nc afters cont callee caller dst p)
  from pop_ready_progress[OF Returning.hyps(1), of \<G> \<Pi> callee caller dst "[]"]
  obtain w' s' f' where "\<G>, \<Pi> \<turnstile> (w, callee, [Frame caller dst]) \<rightarrow>\<^sub>p (w', s', f')"
    by auto
  from pstep_seq_after_lift[OF this, of afters] show ?case by auto
qed

theorem csim_progress:
  assumes "\<Pi>, g \<turnstile> (c, s, frs) \<approx> dg"
      and "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> wf_proc_decl \<G> \<Pi> decl"
  shows "(c = SKIP \<and> frs = []) \<or> (\<exists>cfg'. \<G>, \<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p cfg')"
  using csim_progress_cfg[OF assms] by simp

subsection \<open>Progress for accepted programs\<close>

text \<open>
  The premise is source well-formedness alone; no compiled graph is involved.  \<^const>\<open>csim\<close>
  still needs some graph with every body embedded, and the complete graph --- every edge
  present --- embeds anything, so it stands in for the compiler's output.  The finished shape
  is exactly \<^term>\<open>(SKIP, s, [])\<close>: \<open>main\<close> contains no \<^const>\<open>Return\<close>
  (\<^const>\<open>no_return\<close>), so a top-level \<^const>\<open>Unwind\<close> never arises.
\<close>
theorem source_progress:
  assumes wf: "wf_source_program \<G> \<Pi>"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (c, s, frs)"
  shows "(c = SKIP \<and> frs = []) \<or> (\<exists>cfg'. \<G>, \<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p cfg')"
proof -
  define g :: cfg where
    "g = \<lparr>intra = UNIV, calls = UNIV, cfg_entry = FunctionEntry prog_main_name, checks = {}\<rparr>"
  have pc: "procs_embedded \<Pi> g"
    unfolding procs_embedded_def
  proof (intro allI impI)
    fix p decl assume pd: "\<Pi> p = Some decl"
    obtain n' en E K where
      cb: "compile \<Pi> p (body decl) (FunctionResult p) 0 = (n', en, E, K)"
      by (metis prod_cases4)
    have "source_com (body decl)" "special_table p = None"
      using wf_source_programD(6,7)[OF wf] pd by (auto simp: source_pi_def)
    with cb show "\<exists>k n n' en E K. compile \<Pi> p (body decl) k n = (n', en, E, K)
          \<and> E \<subseteq> intra g \<and> K \<subseteq> calls g
          \<and> (FunctionEntry p, EA_Body p, en) \<in> intra g
          \<and> (falls_through (body decl) \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g)
          \<and> source_com (body decl) \<and> special_table p = None"
      by (intro exI[of _ "FunctionResult p"] exI[of _ "0 :: nat"] exI[of _ n'] exI[of _ en]
            exI[of _ E] exI[of _ K])
         (simp add: g_def)
  qed
  have main_decl: "\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>"
    by (rule wf_source_programD(2)[OF wf])
  obtain k n en where
    cacc: "compiled_at \<Pi> g prog_main_name (body \<lparr>formals = [], body = main_body \<Pi>\<rparr>) k n"
    and ctrl: "control_at \<Pi> prog_main_name (body \<lparr>formals = [], body = main_body \<Pi>\<rparr>) k n
                 (body \<lparr>formals = [], body = main_body \<Pi>\<rparr>) en"
    by (rule procs_embedded_activation[OF pc main_decl])
  have base: "\<Pi>, g \<turnstile> (main_body \<Pi>, s0, []) \<approx> (en, s0, [])"
    using csim.Base[OF ctrl cacc] by simp
  have safe: "return_safe (main_body \<Pi>)"
    using wf_source_programD(8,4)[OF wf] by (rule return_safe_if_no_return)
  from csim_star[OF base pc safe run] obtain dg where "\<Pi>, g \<turnstile> (c, s, frs) \<approx> dg"
    by blast
  then show ?thesis
    by (rule csim_progress) (rule wf_source_programD(5)[OF wf])
qed

end
