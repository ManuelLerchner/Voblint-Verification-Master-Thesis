theory Example_Compile_Regression
  imports "Voblint_CFG.Control_Simulation" "Voblint_CFG.Compile_Invariants"
begin

section \<open>Examples: procedure-aware CFG compilation\<close>

lemma ex_return_before_dead:
  assumes "compile \<Pi> p (Seq (Return (Some e)) (Assign yv ay)) n = (n', en, ex, E, K)"
  shows "\<exists>k. (Statement k, EA_Ret (Some e) p, FunctionResult p) \<in> E"
  using compile_return_edge[OF assms] by simp

lemmas ex_dead_after_return_unreached = inv11_return_exit_unreached

lemmas ex_multi_return = inv13_multi_return_converge

lemma ex_fallthrough:
  assumes "compile_proc \<Pi> p (proc_decl_of [] SKIP) n = (n', E, K)"
  shows "\<exists>bex. (bex, EA_Ret None p, FunctionResult p) \<in> E"
  using assms by (auto simp: compile_proc_def proc_decl_of_def Let_def split: prod.splits)

lemma ex_nested_calls:
  "(Statement n, CallEdge (Some r1) (case \<Pi> p1 of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) [], FunctionEntry p1, Statement (Suc n))
      \<in> snd (snd (snd (snd (compile \<Pi> q (Seq (Call (Some r1) p1 []) (Call (Some r2) p2 [])) n))))
   \<and> (Statement (Suc (Suc n)), CallEdge (Some r2) (case \<Pi> p2 of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) [], FunctionEntry p2, Statement (Suc (Suc (Suc n))))
      \<in> snd (snd (snd (snd (compile \<Pi> q (Seq (Call (Some r1) p1 []) (Call (Some r2) p2 [])) n))))
   \<and> Statement (Suc n) \<noteq> Statement (Suc (Suc (Suc n)))"
  by (simp add: Let_def)

lemmas ex_recursion = inv14_recursion_edge

lemma compile_seq_call_edge:
  assumes "\<Pi> pin = Some decl"
      and "compile \<Pi> pout (Seq (Call (Some rin) pin actuals) after) n = (n', en, ex, E, K)"
  shows "(Statement n, CallEdge (Some rin) (formals decl) actuals, FunctionEntry pin,
          Statement (Suc n)) \<in> K"
  using assms by (auto split: prod.splits)

lemma compile_seq_return_edge:
  "compile \<Pi> p (Seq (Return (Some e)) dead) n = (n', en, ex, E, K) \<Longrightarrow>
   (Statement n, EA_Ret (Some e) p, FunctionResult p) \<in> E"
  by (auto split: prod.splits)

theorem example_early_return_skips_dead:
  assumes comp: "compile \<Pi> p (Seq (Return (Some e)) dead) n = (n', en, ex, E, K)"
      and sub: "E \<subseteq> intra g"
  shows "control_at \<Pi> p (Seq (Return (Some e)) dead) n
           (Seq (Return (Some e)) dead) (Statement n)"
    and "cstep g (Statement n, s, stk)
           (FunctionResult p, s(ret_var := aval e s), stk)"
    and "\<forall>k. FunctionResult p \<noteq> Statement k"
proof -
  show "control_at \<Pi> p (Seq (Return (Some e)) dead) n
          (Seq (Return (Some e)) dead) (Statement n)"
    by (rule control_at.SeqLeft[OF control_at.ReturnHead])
  have "(Statement n, EA_Ret (Some e) p, FunctionResult p) \<in> intra g"
    using compile_seq_return_edge[OF comp] sub by blast
  from cstep_ret[OF this]
  show "cstep g (Statement n, s, stk) (FunctionResult p, s(ret_var := aval e s), stk)"
    by simp
  show "\<forall>k. FunctionResult p \<noteq> Statement k" by simp
qed

theorem example_nested_call_preserves_outer:
  assumes p: "\<Pi> pin = Some decl"
      and comp: "compile \<Pi> pout (Seq (Call (Some rin) pin actuals) after) n = (n', en, ex, E, K)"
      and sub: "K \<subseteq> calls g"
  shows "cstep g (Statement n, s, outer # stk)
           (FunctionEntry pin,
            call_enter (CallEdge (Some rin) (formals decl) actuals) s,
            (Statement (Suc n), Some rin, s) # outer # stk)"
proof -
  have "(Statement n, CallEdge (Some rin) (formals decl) actuals, FunctionEntry pin,
         Statement (Suc n)) \<in> calls g"
    using compile_seq_call_edge[OF p comp] sub by blast
  from cstep_call[OF this] show ?thesis .
qed

lemma example_nested_call_frames:
  "frames_match frs stk \<Longrightarrow>
   frames_match (Frame caller (Some rin) # frs)
     ((Statement (Suc n), Some rin, caller) # stk)"
  by (rule frames_match_call)

theorem example_normal_fallthrough:
  assumes comp: "compile_proc \<Pi> p decl n = (n', E, K)"
      and body: "body decl = Assign x a"
  shows "control_at \<Pi> p (body decl) n SKIP (Statement (Suc n))"
    and "(Statement (Suc n), EA_Ret None p, FunctionResult p) \<in> E"
proof -
  show "control_at \<Pi> p (body decl) n SKIP (Statement (Suc n))"
    unfolding body by (rule control_at.AssignDone)
  show "(Statement (Suc n), EA_Ret None p, FunctionResult p) \<in> E"
    using comp by (auto simp: compile_proc_def Let_def body split: prod.splits)
qed

end
