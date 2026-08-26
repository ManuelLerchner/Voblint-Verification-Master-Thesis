theory Example_Control_Simulation_Regression
  imports "Voblint_CFG.Control_Simulation"
begin

section \<open>Examples: source-to-CFG simulation\<close>

text \<open>The bound values are the ones \<^const>\<open>pstep\<close>'s \<open>Call\<close> rule computes: each
  actual is evaluated at its own synthesized kind and converted to the formal's
  declared kind. The compiled edge carries the same conversion inside its
  elaborated actual list, which is what makes the two agree with no typing
  environment on the CFG side.\<close>
lemma call_transition:
  fixes s :: store
  assumes decl: "\<Pi> q = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct: "distinct (formals decl)"
      and edge: "(u, CallEdge dst (formals decl) (compile_actuals \<Gamma> (formals decl) actuals),
                  FunctionEntry q, cont) \<in> calls g"
      and fm: "frames_match frs stk"
      and sty: "styped \<Gamma> s"
  defines "vals \<equiv> map2 (\<lambda>x e. ik_norm (\<Gamma> x) (taval_syn \<Gamma> e s)) (formals decl) actuals"
  shows "pstep \<Gamma> is_global \<Pi> (Call (map_option tv_name dst) q actuals, s, frs, rk)
           (Seq (body decl) Restore,
            bind_formals (formals decl) vals (enter_state is_global s),
            Frame s (map_option tv_name dst) rk # frs,
            case ret_kind decl of None \<Rightarrow> I32 | Some k \<Rightarrow> k)"
    and "cstep is_global g (u, s, stk)
           (FunctionEntry q,
            call_enter is_global
              (CallEdge dst (formals decl) (compile_actuals \<Gamma> (formals decl) actuals)) s,
            (cont, dst, s) # stk)"
    and "call_enter is_global
           (CallEdge dst (formals decl) (compile_actuals \<Gamma> (formals decl) actuals)) s
           = bind_formals (formals decl) vals (enter_state is_global s)"
    and "frames_match (Frame s (map_option tv_name dst) rk # frs) ((cont, dst, s) # stk)"
proof -
  show "pstep \<Gamma> is_global \<Pi> (Call (map_option tv_name dst) q actuals, s, frs, rk)
           (Seq (body decl) Restore,
            bind_formals (formals decl) vals (enter_state is_global s),
            Frame s (map_option tv_name dst) rk # frs,
            case ret_kind decl of None \<Rightarrow> I32 | Some k \<Rightarrow> k)"
    using decl arity distinct
    by (intro pstep.Call[where vals = vals]) (auto simp: vals_def)
  show "cstep is_global g (u, s, stk)
           (FunctionEntry q,
            call_enter is_global
              (CallEdge dst (formals decl) (compile_actuals \<Gamma> (formals decl) actuals)) s,
            (cont, dst, s) # stk)"
    by (rule cstep.Call[OF edge])
  show "call_enter is_global
          (CallEdge dst (formals decl) (compile_actuals \<Gamma> (formals decl) actuals)) s
          = bind_formals (formals decl) vals (enter_state is_global s)"
    unfolding vals_def by (rule call_enter_eq_source_call_store[OF sty])
  show "frames_match (Frame s (map_option tv_name dst) rk # frs) ((cont, dst, s) # stk)"
    using fm by (simp add: frames_match_activation)
qed

lemma return_initiation:
  assumes loc: "control_at \<Pi> p c0 kk n (Return e) v"
      and comp: "compile \<Gamma> \<Pi> p c0 kk n = (n', en, E, K)"
      and sub: "E \<subseteq> intra g"
      and rk: "rk = proc_ret_kind \<Pi> p"
      and sty: "styped \<Gamma> s"
  obtains k where "v = Statement k"
    and "pstep \<Gamma> is_global \<Pi> (Return e, s, frs, rk) (Unwind, ret_store \<Gamma> rk e s, frs, rk)"
    and "cstep is_global g (Statement k, s, stk) (FunctionResult p, ret_store \<Gamma> rk e s, stk)"
proof -
  from control_at_return_edge[OF loc refl comp] obtain k where
    k: "v = Statement k"
       "(Statement k, EA_Ret (map_option (elaborate_to \<Gamma> rk) e) p rk, FunctionResult p) \<in> E"
    using rk by blast
  have edge: "(Statement k, EA_Ret (map_option (elaborate_to \<Gamma> rk) e) p rk, FunctionResult p)
                \<in> intra g"
    using k(2) sub by blast
  have src: "pstep \<Gamma> is_global \<Pi> (Return e, s, frs, rk) (Unwind, ret_store \<Gamma> rk e s, frs, rk)"
    by (cases e) (auto simp: ret_store_def)
  have cfg: "cstep is_global g (Statement k, s, stk)
               (FunctionResult p, ret_store \<Gamma> rk e s, stk)"
    using cstep.Intra[OF edge edge_step_EA_Ret_ret_store_mem[OF sty]] .
  show ?thesis by (rule that[OF k(1) src cfg])
qed

lemma return_completion_restore:
  assumes fm: "frames_match (Frame caller dst rk # frs) ((cont, compile_dst \<Gamma> dst, caller) # stk)"
  shows "pstep \<Gamma> is_global \<Pi> (Restore, callee, Frame caller dst rk # frs, rk')
           (SKIP, combine_collect is_global (compile_dst \<Gamma> dst) caller callee, frs, rk)"
    and "cstep is_global g (FunctionResult p, callee, (cont, compile_dst \<Gamma> dst, caller) # stk)
           (cont, combine_collect is_global (compile_dst \<Gamma> dst) caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "pstep \<Gamma> is_global \<Pi> (Restore, callee, Frame caller dst rk # frs, rk')
          (SKIP, combine_collect is_global (compile_dst \<Gamma> dst) caller callee, frs, rk)"
    using pstep.RestoreStep
    by (simp add: combine_collect_def combine_assign_tv_eq_combine_assign compile_dst_def)
  show "cstep is_global g (FunctionResult p, callee, (cont, compile_dst \<Gamma> dst, caller) # stk)
           (cont, combine_collect is_global (compile_dst \<Gamma> dst) caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_def cframe_act_def)
qed

lemma return_completion_unwind:
  assumes fm: "frames_match (Frame caller dst rk # frs) ((cont, compile_dst \<Gamma> dst, caller) # stk)"
  shows "pstep \<Gamma> is_global \<Pi> (Seq Unwind Restore, callee, Frame caller dst rk # frs, rk')
           (SKIP, combine_collect is_global (compile_dst \<Gamma> dst) caller callee, frs, rk)"
    and "cstep is_global g (FunctionResult p, callee, (cont, compile_dst \<Gamma> dst, caller) # stk)
           (cont, combine_collect is_global (compile_dst \<Gamma> dst) caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "pstep \<Gamma> is_global \<Pi> (Seq Unwind Restore, callee, Frame caller dst rk # frs, rk')
          (SKIP, combine_collect is_global (compile_dst \<Gamma> dst) caller callee, frs, rk)"
    using pstep.UnwindAct
    by (simp add: combine_collect_def combine_assign_tv_eq_combine_assign compile_dst_def)
  show "cstep is_global g (FunctionResult p, callee, (cont, compile_dst \<Gamma> dst,caller) # stk)
           (cont, combine_collect is_global (compile_dst \<Gamma> dst) caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_def cframe_act_def)
qed

lemma Unwind_not_pcompletes: "\<not> pcompletes \<Gamma> is_global \<Pi> Unwind s t rk"
  unfolding pcompletes_def
proof (rule notI)
  assume "star (pstep \<Gamma> is_global \<Pi>) (Unwind, s, [], rk) (SKIP, t, [], rk)"
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

lemma Return_empty_not_pcompletes: "\<not> pcompletes \<Gamma> is_global \<Pi> (Return e) s t rk"
  unfolding pcompletes_def
proof (rule notI)
  assume "star (pstep \<Gamma> is_global \<Pi>) (Return e, s, [], rk) (SKIP, t, [], rk)"
  then obtain y where step: "pstep \<Gamma> is_global \<Pi> (Return e, s, [], rk) y"
      and rest: "star (pstep \<Gamma> is_global \<Pi>) y (SKIP, t, [], rk)"
    by (cases rule: star.cases) auto
  from step have "y = (Unwind, ret_store \<Gamma> rk e s, [], rk)"
    by (cases e) (auto simp: ret_store_def)
  with rest have "star (pstep \<Gamma> is_global \<Pi>) (Unwind, ret_store \<Gamma> rk e s, [], rk) (SKIP, t, [], rk)"
    by simp
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

lemma ret_guarded_False_no_return:
  "no_return c \<Longrightarrow> source_com c \<Longrightarrow> ret_guarded False c"
  by (induction c) (auto split: if_splits)

lemma source_wf_main:
  "no_return c \<Longrightarrow> source_com c \<Longrightarrow> source_wf (c, s, [], rk)"
  by (simp add: source_wf_def ret_guarded_False_no_return)

lemma source_wf_return_main_rejected: "\<not> source_wf (Return e, s, [], rk)"
  by (simp add: source_wf_def)

lemma source_wf_seq_return_main_rejected: "\<not> source_wf (Seq SKIP (Return e), s, [], rk)"
  by (simp add: source_wf_def)

lemma return_main_stuck_but_rejected:
  "pstep \<Gamma> is_global \<Pi> (Return e, s, [], rk) (Unwind, ret_store \<Gamma> rk e s, [], rk)
     \<and> \<not> source_wf (Return e, s, [], rk)"
  by (cases e) (auto simp: source_wf_def ret_store_def)

lemma source_wf_return_in_callee:
  "source_wf (Seq (Return e) Restore, s, [Frame caller dst rk'], rk)"
  by (simp add: source_wf_def)

lemma source_wf_psteps:
  assumes "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and "star (pstep \<Gamma> is_global \<Pi>) sc sc'" and "source_wf sc"
  shows "source_wf sc'"
  using assms(2,3)
proof (induction rule: star.induct)
  case (step a b c)
  obtain c0 s0 f0 r0 where a: "a = (c0, s0, f0, r0)" by (cases a)
  obtain c1 s1 f1 r1 where b: "b = (c1, s1, f1, r1)" by (cases b)
  from step.prems a have "source_wf (c0, s0, f0, r0)" by simp
  from source_wf_pstep[OF assms(1) _ this] step.hyps(1) a b
  have "source_wf (c1, s1, f1, r1)" by simp
  with step.IH b show ?case by simp
qed simp

lemma csim_tailcall_callee_entry:
  assumes callee: "control_at \<Pi> p c0 k n SKIP v"
      and calleecacc: "compiled_at \<Gamma> \<Pi> g p c0 k n"
      and calleepa: "proc_activation \<Pi> p c0"
      and caller: "control_at \<Pi> pc c0c kc nc SKIP cont"
      and callercacc: "compiled_at \<Gamma> \<Pi> g pc c0c kc nc"
      and callerpa: "proc_activation \<Pi> pc c0c"
      and calleety: "styped \<Gamma> callee"
      and callerty: "styped \<Gamma> caller"
  shows "csim \<Gamma> \<Pi> g (Seq SKIP Restore, callee, [Frame caller dst (proc_ret_kind \<Pi> pc)],
                     proc_ret_kind \<Pi> p)
                  (v, callee, [(cont, compile_dst \<Gamma> dst, caller)])"
proof -
  have base: "csim \<Gamma> \<Pi> g (SKIP, callee, [], proc_ret_kind \<Pi> p) (v, callee, [])"
    by (rule csim.Base[OF callee calleecacc calleepa calleety])
  have caller': "control_at \<Pi> pc c0c kc nc (seq_after SKIP []) cont" using caller by simp
  have "csim \<Gamma> \<Pi> g (seq_after (Seq SKIP Restore) [], callee,
                    [] @ [Frame caller dst (proc_ret_kind \<Pi> pc)], proc_ret_kind \<Pi> p)
                 (v, callee, [] @ [(cont, compile_dst \<Gamma> dst, caller)])"
    by (rule csim.Nested[OF base caller' callercacc callerpa callerty])
  thus ?thesis by simp
qed

end
