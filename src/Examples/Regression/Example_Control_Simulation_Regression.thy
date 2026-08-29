theory Example_Control_Simulation_Regression
  imports "Voblint_Compile.Simulation_Relation"
begin

section \<open>Examples: source-to-CFG simulation\<close>

lemma call_transition:
  assumes decl: "\<Pi> q = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct: "distinct (formals decl)"
      and edge: "(u, CallEdge dst (formals decl) actuals, FunctionEntry q, cont) \<in> calls g"
      and fm: "frames_match frs stk"
  shows "pstep is_global \<Pi> (Call dst q actuals, s, frs)
           (Seq (body decl) Restore,
            bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state is_global s),
            Frame s dst # frs)"
    and "cstep is_global g (u, s, stk)
           (FunctionEntry q,
            call_enter is_global (CallEdge dst (formals decl) actuals) s, (cont, dst, s) # stk)"
    and "call_enter is_global (CallEdge dst (formals decl) actuals) s
           = bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state is_global s)"
    and "frames_match (Frame s dst # frs) ((cont, dst, s) # stk)"
proof -
  show "pstep is_global \<Pi> (Call dst q actuals, s, frs)
           (Seq (body decl) Restore,
            bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state is_global s),
            Frame s dst # frs)"
    using decl arity distinct
    by (intro pstep.Call[where vals = "map (\<lambda>e. aval e s) actuals"]) auto
  show "cstep is_global g (u, s, stk)
           (FunctionEntry q,
            call_enter is_global (CallEdge dst (formals decl) actuals) s, (cont, dst, s) # stk)"
    by (rule cstep.Call[OF edge])
  show "call_enter is_global (CallEdge dst (formals decl) actuals) s
           = bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state is_global s)"
    by (rule call_enter_CallEdge)
  show "frames_match (Frame s dst # frs) ((cont, dst, s) # stk)"
    using fm by (simp add: frames_match_activation)
qed

lemma return_initiation:
  assumes loc: "control_at \<Pi> p c0 kk n (Return e) v"
      and comp: "compile \<Pi> p c0 kk n = (n', en, E, K)"
      and sub: "E \<subseteq> intra g"
  obtains k where "v = Statement k"
    and "pstep is_global \<Pi> (Return e, s, frs) (Unwind, ret_store e s, frs)"
    and "cstep is_global g (Statement k, s, stk) (FunctionResult p, ret_store e s, stk)"
proof -
  from control_at_return_edge[OF loc refl comp] obtain k where
    k: "v = Statement k" "(Statement k, EA_Ret e p, FunctionResult p) \<in> E" by blast
  have edge: "(Statement k, EA_Ret e p, FunctionResult p) \<in> intra g" using k(2) sub by blast
  have src: "pstep is_global \<Pi> (Return e, s, frs) (Unwind, ret_store e s, frs)"
    by (cases e) (auto simp: ret_store_def)
  have cfg: "cstep is_global g (Statement k, s, stk) (FunctionResult p, ret_store e s, stk)"
    using cstep.Intra[OF edge edge_step_EA_Ret_ret_store_mem] .
  show ?thesis by (rule that[OF k(1) src cfg])
qed

lemma return_completion_restore:
  assumes fm: "frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  shows "pstep is_global \<Pi> (Restore, callee, Frame caller dst # frs)
           (SKIP, combine_collect is_global dst caller callee, frs)"
    and "cstep is_global g (FunctionResult p, callee, (cont, dst, caller) # stk)
           (cont, combine_collect is_global dst caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "pstep is_global \<Pi> (Restore, callee, Frame caller dst # frs)
          (SKIP, combine_collect is_global dst caller callee, frs)"
    using pstep.RestoreStep by (simp add: combine_collect_def)
  show "cstep is_global g (FunctionResult p, callee, (cont, dst, caller) # stk)
           (cont, combine_collect is_global dst caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_activation)
qed

lemma return_completion_unwind:
  assumes fm: "frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  shows "pstep is_global \<Pi> (Seq Unwind Restore, callee, Frame caller dst # frs)
           (SKIP, combine_collect is_global dst caller callee, frs)"
    and "cstep is_global g (FunctionResult p, callee, (cont, dst, caller) # stk)
           (cont, combine_collect is_global dst caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "pstep is_global \<Pi> (Seq Unwind Restore, callee, Frame caller dst # frs)
          (SKIP, combine_collect is_global dst caller callee, frs)"
    using pstep.UnwindAct by (simp add: combine_collect_def)
  show "cstep is_global g (FunctionResult p, callee, (cont, dst,caller) # stk)
           (cont, combine_collect is_global dst caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_activation)
qed

lemma Unwind_not_pcompletes: "\<not> pcompletes is_global \<Pi> Unwind s t"
proof (rule notI)
  assume "star (pstep is_global \<Pi>) (Unwind, s, []) (SKIP, t, [])"
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

lemma Return_empty_not_pcompletes: "\<not> pcompletes is_global \<Pi> (Return e) s t"
proof (rule notI)
  assume "star (pstep is_global \<Pi>) (Return e, s, []) (SKIP, t, [])"
  then obtain y where step: "pstep is_global \<Pi> (Return e, s, []) y"
      and rest: "star (pstep is_global \<Pi>) y (SKIP, t, [])"
    by (cases rule: star.cases) auto
  from step have "y = (Unwind, ret_store e s, [])"
    by (cases e) (auto simp: ret_store_def)
  with rest have "star (pstep is_global \<Pi>) (Unwind, ret_store e s, []) (SKIP, t, [])" by simp
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
  "pstep is_global \<Pi> (Return e, s, []) (Unwind, ret_store e s, []) \<and> \<not> return_safe (Return e)"
  by (cases e) (auto simp: return_safe_def ret_store_def)

lemma return_safe_return_in_callee:
  "return_safe (Seq (Return e) Restore)"
  by (simp add: return_safe_def)

lemma return_safe_psteps:
  assumes "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and "star (pstep is_global \<Pi>) sc sc'" and "return_safe (fst sc)"
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
  shows "csim \<Pi> g (Seq SKIP Restore, callee, [Frame caller dst])
                  (v, callee, [(cont, dst, caller)])"
proof -
  have base: "csim \<Pi> g (SKIP, callee, []) (v, callee, [])"
    by (rule csim.Base[OF callee calleecacc])
  have caller': "control_at \<Pi> pc c0c kc nc (seq_after SKIP []) cont" using caller by simp
  have "csim \<Pi> g (seq_after (Seq SKIP Restore) [], callee, [] @ [Frame caller dst])
                 (v, callee, [] @ [(cont, dst, caller)])"
    by (rule csim.Nested[OF base caller' callercacc])
  thus ?thesis by simp
qed
end
