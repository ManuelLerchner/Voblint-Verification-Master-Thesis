theory Example_Control_Simulation_Regression
  imports "Voblint_CFG.Control_Simulation"
begin

section \<open>Examples: source-to-CFG simulation\<close>

lemma call_transition:
  assumes decl: "\<Pi> q = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct: "distinct (formals decl)"
      and edge: "(u, CallEdge dst (formals decl) actuals, FunctionEntry q, cont) \<in> calls g"
      and fm: "frames_match frs stk"
  shows "pstep \<Pi> (Call dst q actuals, s, frs)
           (Seq (body decl) Restore,
            bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s),
            Frame s dst # frs)"
    and "cstep g (u, s, stk)
           (FunctionEntry q,
            call_enter (CallEdge dst (formals decl) actuals) s, (cont, dst, s) # stk)"
    and "call_enter (CallEdge dst (formals decl) actuals) s
           = bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s)"
    and "frames_match (Frame s dst # frs) ((cont, dst, s) # stk)"
proof -
  show "pstep \<Pi> (Call dst q actuals, s, frs)
           (Seq (body decl) Restore,
            bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s),
            Frame s dst # frs)"
    using decl arity distinct
    by (intro pstep.Call[where vals = "map (\<lambda>e. aval e s) actuals"]) auto
  show "cstep g (u, s, stk)
           (FunctionEntry q,
            call_enter (CallEdge dst (formals decl) actuals) s, (cont, dst, s) # stk)"
    by (rule cstep.Call[OF edge])
  show "call_enter (CallEdge dst (formals decl) actuals) s
           = bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s)"
    by (rule call_enter_eq_source_call_store)
  show "frames_match (Frame s dst # frs) ((cont, dst, s) # stk)"
    using fm by (simp add: frames_match_Cons_iff)
qed

lemma return_initiation:
  assumes loc: "control_at \<Pi> p c0 kk n (Return e) v"
      and comp: "compile \<Pi> p c0 kk n = (n', en, E, K)"
      and sub: "E \<subseteq> intra g"
  obtains k where "v = Statement k"
    and "pstep \<Pi> (Return e, s, frs) (Unwind, ret_store e s, frs)"
    and "cstep g (Statement k, s, stk) (FunctionResult p, ret_store e s, stk)"
proof -
  from control_at_return_edge[OF loc refl comp] obtain k where
    k: "v = Statement k" "(Statement k, EA_Ret e p, FunctionResult p) \<in> E" by blast
  have edge: "(Statement k, EA_Ret e p, FunctionResult p) \<in> intra g" using k(2) sub by blast
  have src: "pstep \<Pi> (Return e, s, frs) (Unwind, ret_store e s, frs)"
    by (cases e) (auto simp: ret_store_def)
  have cfg: "cstep g (Statement k, s, stk) (FunctionResult p, ret_store e s, stk)"
    using cstep.Intra[OF edge edge_step_EA_Ret_ret_store] .
  show ?thesis by (rule that[OF k(1) src cfg])
qed

lemma return_completion_restore:
  assumes fm: "frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  shows "pstep \<Pi> (Restore, callee, Frame caller dst # frs)
           (SKIP, combine_collect dst caller callee, frs)"
    and "cstep g (FunctionResult p, callee, (cont, dst, caller) # stk)
           (cont, combine_collect dst caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "pstep \<Pi> (Restore, callee, Frame caller dst # frs)
          (SKIP, combine_collect dst caller callee, frs)"
    using pstep.RestoreStep by (simp add: combine_collect_def)
  show "cstep g (FunctionResult p, callee, (cont, dst, caller) # stk)
           (cont, combine_collect dst caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_Cons_iff)
qed

lemma return_completion_unwind:
  assumes fm: "frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  shows "pstep \<Pi> (Seq Unwind Restore, callee, Frame caller dst # frs)
           (SKIP, combine_collect dst caller callee, frs)"
    and "cstep g (FunctionResult p, callee, (cont, dst, caller) # stk)
           (cont, combine_collect dst caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "pstep \<Pi> (Seq Unwind Restore, callee, Frame caller dst # frs)
          (SKIP, combine_collect dst caller callee, frs)"
    using pstep.UnwindAct by (simp add: combine_collect_def)
  show "cstep g (FunctionResult p, callee, (cont, dst,caller) # stk)
           (cont, combine_collect dst caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_Cons_iff)
qed

lemma Unwind_not_pcompletes: "\<not> pcompletes \<Pi> Unwind s t"
  unfolding pcompletes_def
proof
  assume "star (pstep \<Pi>) (Unwind, s, []) (SKIP, t, [])"
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

lemma Return_empty_not_pcompletes: "\<not> pcompletes \<Pi> (Return e) s t"
  unfolding pcompletes_def
proof
  assume "star (pstep \<Pi>) (Return e, s, []) (SKIP, t, [])"
  then obtain y where step: "pstep \<Pi> (Return e, s, []) y"
      and rest: "star (pstep \<Pi>) y (SKIP, t, [])"
    by (cases rule: star.cases) auto
  from step have "y = (Unwind, ret_store e s, [])"
    by (cases e) (auto simp: ret_store_def)
  with rest have "star (pstep \<Pi>) (Unwind, ret_store e s, []) (SKIP, t, [])" by simp
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

lemma ret_guarded_False_no_return:
  "no_return c \<Longrightarrow> source_com c \<Longrightarrow> ret_guarded False c"
  by (induction c) (auto split: if_splits)

lemma source_wf_main:
  "no_return c \<Longrightarrow> source_com c \<Longrightarrow> source_wf (c, s, [])"
  by (simp add: source_wf_def ret_guarded_False_no_return)

lemma source_wf_return_main_rejected: "\<not> source_wf (Return e, s, [])"
  by (simp add: source_wf_def)

lemma source_wf_seq_return_main_rejected: "\<not> source_wf (Seq SKIP (Return e), s, [])"
  by (simp add: source_wf_def)

lemma return_main_stuck_but_rejected:
  "pstep \<Pi> (Return e, s, []) (Unwind, ret_store e s, []) \<and> \<not> source_wf (Return e, s, [])"
  by (cases e) (auto simp: source_wf_def ret_store_def)

lemma source_wf_return_in_callee:
  "source_wf (Seq (Return e) Restore, s, [Frame caller dst])"
  by (simp add: source_wf_def)

lemma source_wf_psteps:
  assumes "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and "star (pstep \<Pi>) sc sc'" and "source_wf sc"
  shows "source_wf sc'"
  using assms(2,3)
proof (induction rule: star.induct)
  case (step a b c)
  obtain c0 s0 f0 where a: "a = (c0, s0, f0)" by (cases a)
  obtain c1 s1 f1 where b: "b = (c1, s1, f1)" by (cases b)
  from step.prems a have "source_wf (c0, s0, f0)" by simp
  from source_wf_pstep[OF assms(1) _ this] step.hyps(1) a b
  have "source_wf (c1, s1, f1)" by simp
  with step.IH b show ?case by simp
qed simp

lemma csim_tailcall_callee_entry:
  assumes callee: "control_at \<Pi> p c0 k n SKIP v"
      and calleecacc: "compiled_at \<Pi> g p c0 k n"
      and calleepa: "proc_activation \<Pi> p c0"
      and caller: "control_at \<Pi> pc c0c kc nc SKIP cont"
      and callercacc: "compiled_at \<Pi> g pc c0c kc nc"
      and callerpa: "proc_activation \<Pi> pc c0c"
  shows "csim \<Pi> g (Seq SKIP Restore, callee, [Frame caller dst])
                  (v, callee, [(cont, dst, caller)])"
proof -
  have base: "csim \<Pi> g (SKIP, callee, []) (v, callee, [])"
    by (rule csim.Base[OF callee calleecacc calleepa])
  have caller': "control_at \<Pi> pc c0c kc nc (seq_after SKIP []) cont" using caller by simp
  have "csim \<Pi> g (seq_after (Seq SKIP Restore) [], callee, [] @ [Frame caller dst])
                 (v, callee, [] @ [(cont, dst, caller)])"
    by (rule csim.Nested[OF base caller' callercacc callerpa])
  thus ?thesis by simp
qed

end
