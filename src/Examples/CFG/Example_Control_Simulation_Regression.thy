theory Example_Control_Simulation_Regression
  imports "Voblint_Compile.Simulation_Relation"
begin

section \<open>How a call, a return and a resume line up in source and in graph\<close>

text \<open>
  A source run steps a command over a store and a stack of \<open>Frame\<close>s; the compiled graph
  steps a node over a store and a stack of resume triples.  \<open>frames_match\<close> says the two
  stacks describe the same nesting.  Each lemma below takes one interprocedural moment ---
  entering a callee, initiating a return, completing it back into the caller --- and puts
  the source step, the graph step and the surviving \<open>frames_match\<close> side by side, so a
  reader sees which graph edge each source rule needs.  The rest fixes what \<open>return_safe\<close>
  admits: a bare \<open>Return\<close> in the entry procedure gets stuck and is rejected, while a
  \<open>Return\<close> under a \<open>Restore\<close> is exactly the shape a call installs.
\<close>

lemma call_transition:
  assumes decl: "\<Pi> q = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct: "distinct (formals decl)"
      and edge: "(u, CallEdge dst (formals decl) actuals, FunctionEntry q, cont) \<in> calls g"
      and fm: "frames_match frs stk"
  shows "\<G>, \<Pi> \<turnstile> (Call dst q actuals, s, frs)
           \<rightarrow>\<^sub>p (Seq (body decl) Restore,
            bind_formals (formals decl) (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals) (enter_state \<G> s),
            Frame s dst # frs)"
    and "\<G>, g \<turnstile> (u, s, stk)
           \<rightarrow>\<^sub>c (FunctionEntry q,
            call_enter \<G> (CallEdge dst (formals decl) actuals) s, (cont, dst, s) # stk)"
    and "call_enter \<G> (CallEdge dst (formals decl) actuals) s
           = bind_formals (formals decl) (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals) (enter_state \<G> s)"
    and "frames_match (Frame s dst # frs) ((cont, dst, s) # stk)"
proof -
  show "\<G>, \<Pi> \<turnstile> (Call dst q actuals, s, frs)
           \<rightarrow>\<^sub>p (Seq (body decl) Restore,
            bind_formals (formals decl) (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals) (enter_state \<G> s),
            Frame s dst # frs)"
    using decl arity distinct
    by (intro pstep.Call[where vals = "map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals"]) auto
  show "\<G>, g \<turnstile> (u, s, stk)
           \<rightarrow>\<^sub>c (FunctionEntry q,
            call_enter \<G> (CallEdge dst (formals decl) actuals) s, (cont, dst, s) # stk)"
    by (rule cstep.Call[OF edge])
  show "call_enter \<G> (CallEdge dst (formals decl) actuals) s
           = bind_formals (formals decl) (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals) (enter_state \<G> s)"
    by (rule call_enter_CallEdge)
  show "frames_match (Frame s dst # frs) ((cont, dst, s) # stk)"
    using fm by (simp add: frames_match_activation)
qed

lemma return_initiation:
  assumes loc: "control_at \<Pi> p c0 kk n (Return e) v"
      and comp: "compile \<Pi> p c0 kk n = (n', en, E, K)"
      and sub: "E \<subseteq> intra g"
  obtains k where "v = Statement k"
    and "\<G>, \<Pi> \<turnstile> (Return e, s, frs) \<rightarrow>\<^sub>p (Unwind, ret_store e s, frs)"
    and "\<G>, g \<turnstile> (Statement k, s, stk) \<rightarrow>\<^sub>c (FunctionResult p, ret_store e s, stk)"
proof -
  from control_at_return_edge[OF loc refl comp] obtain k where
    k: "v = Statement k" "(Statement k, EA_Ret e p, FunctionResult p) \<in> E" by blast
  have edge: "(Statement k, EA_Ret e p, FunctionResult p) \<in> intra g" using k(2) sub by blast
  have src: "\<G>, \<Pi> \<turnstile> (Return e, s, frs) \<rightarrow>\<^sub>p (Unwind, ret_store e s, frs)"
    by (cases e) (auto simp: ret_store_def)
  have cfg: "\<G>, g \<turnstile> (Statement k, s, stk) \<rightarrow>\<^sub>c (FunctionResult p, ret_store e s, stk)"
    using cstep.Intra[OF edge edge_step_EA_Ret_ret_store_mem] .
  show ?thesis by (rule that[OF k(1) src cfg])
qed

lemma return_completion_restore:
  assumes fm: "frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  shows "\<G>, \<Pi> \<turnstile> (Restore, callee, Frame caller dst # frs)
           \<rightarrow>\<^sub>p (SKIP, combine_collect \<G> dst caller callee, frs)"
    and "\<G>, g \<turnstile> (FunctionResult p, callee, (cont, dst, caller) # stk)
           \<rightarrow>\<^sub>c (cont, combine_collect \<G> dst caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "\<G>, \<Pi> \<turnstile> (Restore, callee, Frame caller dst # frs)
          \<rightarrow>\<^sub>p (SKIP, combine_collect \<G> dst caller callee, frs)"
    using pstep.RestoreStep by (simp add: combine_collect_def)
  show "\<G>, g \<turnstile> (FunctionResult p, callee, (cont, dst, caller) # stk)
           \<rightarrow>\<^sub>c (cont, combine_collect \<G> dst caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_activation)
qed

lemma return_completion_unwind:
  assumes fm: "frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  shows "\<G>, \<Pi> \<turnstile> (Seq Unwind Restore, callee, Frame caller dst # frs)
           \<rightarrow>\<^sub>p (SKIP, combine_collect \<G> dst caller callee, frs)"
    and "\<G>, g \<turnstile> (FunctionResult p, callee, (cont, dst, caller) # stk)
           \<rightarrow>\<^sub>c (cont, combine_collect \<G> dst caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "\<G>, \<Pi> \<turnstile> (Seq Unwind Restore, callee, Frame caller dst # frs)
          \<rightarrow>\<^sub>p (SKIP, combine_collect \<G> dst caller callee, frs)"
    using pstep.UnwindAct by (simp add: combine_collect_def)
  show "\<G>, g \<turnstile> (FunctionResult p, callee, (cont, dst, caller) # stk)
           \<rightarrow>\<^sub>c (cont, combine_collect \<G> dst caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_activation)
qed

lemma Unwind_not_pcompletes: "\<not> pcompletes \<G> \<Pi> Unwind s t"
proof (rule notI)
  assume "\<G>, \<Pi> \<turnstile> (Unwind, s, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP, t, [])"
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

lemma Return_empty_not_pcompletes: "\<not> pcompletes \<G> \<Pi> (Return e) s t"
proof (rule notI)
  assume "\<G>, \<Pi> \<turnstile> (Return e, s, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP, t, [])"
  then obtain y where step: "\<G>, \<Pi> \<turnstile> (Return e, s, []) \<rightarrow>\<^sub>p y"
      and rest: "\<G>, \<Pi> \<turnstile> y \<rightarrow>\<^sub>p\<^sup>* (SKIP, t, [])"
    by (cases rule: star.cases) auto
  from step have "y = (Unwind, ret_store e s, [])"
    by (cases e) (auto simp: ret_store_def)
  with rest have "\<G>, \<Pi> \<turnstile> (Unwind, ret_store e s, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP, t, [])" by simp
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

lemma return_safe_main:
  "no_return c \<Longrightarrow> source_com c \<Longrightarrow> return_safe c"
  by (rule return_safe_if_no_return)

lemma return_safe_return_main_rejected: "\<not> return_safe (Return e)"
  by (simp add: return_safe_def)

lemma return_safe_seq_return_main_rejected: "\<not> return_safe (Seq SKIP (Return e))"
  by (simp add: return_safe_def)

lemma return_main_stuck_but_rejected:
  "\<G>, \<Pi> \<turnstile> (Return e, s, []) \<rightarrow>\<^sub>p (Unwind, ret_store e s, []) \<and> ~ return_safe (Return e)"
  by (cases e) (auto simp: return_safe_def ret_store_def)

lemma return_safe_return_in_callee:
  "return_safe (Seq (Return e) Restore)"
  by (simp add: return_safe_def)

lemma return_safe_psteps:
  assumes "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and "\<G>, \<Pi> \<turnstile> sc \<rightarrow>\<^sub>p\<^sup>* sc'" and "return_safe (fst sc)"
  shows "return_safe (fst sc')"
  using assms(2,3)
proof (induction rule: star.induct)
  case (step a b c)
  obtain c0 s0 f0 where a: "a = (c0, s0, f0)" by (cases a)
  obtain c1 s1 f1 where b: "b = (c1, s1, f1)" by (cases b)
  from step.prems a have "return_safe c0" by simp
  from return_safe_pstep[OF assms(1) _ this] step.hyps(1) a b
  have "return_safe c1" by simp
  with step.IH b show ?case by simp
qed simp

lemma csim_tailcall_callee_entry:
  assumes callee: "control_at \<Pi> p c0 k n SKIP v"
      and calleecacc: "compiled_at \<Pi> g p c0 k n"
      and caller: "control_at \<Pi> pc c0c kc nc SKIP cont"
      and callercacc: "compiled_at \<Pi> g pc c0c kc nc"
  shows "\<Pi>, g \<turnstile> (Seq SKIP Restore, callee, [Frame caller dst]) \<approx> (v, callee, [(cont, dst, caller)])"
proof -
  have base: "\<Pi>, g \<turnstile> (SKIP, callee, []) \<approx> (v, callee, [])"
    by (rule csim.Base[OF callee calleecacc])
  have caller': "control_at \<Pi> pc c0c kc nc (seq_after SKIP []) cont" using caller by simp
  have "\<Pi>, g \<turnstile> (seq_after (Seq SKIP Restore) [], callee, [] @ [Frame caller dst]) \<approx> (v, callee, [] @ [(cont, dst, caller)])"
    by (rule csim.Nested[OF base caller' callercacc])
  thus ?thesis by simp
qed
end
