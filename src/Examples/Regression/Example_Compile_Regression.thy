theory Example_Compile_Regression
  imports "Voblint_CFG.Control_Simulation" "Voblint_CFG.Compile_Invariants"
begin

section \<open>Examples: procedure-aware CFG compilation\<close>

text \<open>These witnesses build small hand-written commands rather than compiling a source
  program, so there is no \<^const>\<open>declared_global\<close> table to read a classifier off; they
  reuse the G-prefix convention directly as a fixed classifier.\<close>
abbreviation cr_gs :: "vname \<Rightarrow> bool" where
  "cr_gs \<equiv> (\<lambda>x. x \<noteq> STR '''' \<and> hd (String.explode x) = CHR ''G'')"

lemma ex_return_before_dead:
  assumes "compile \<Gamma> \<Pi> p (Seq (Return (Some e)) (Assign yv ay)) k n = (n', en, E, K)"
  shows "\<exists>j. (Statement j, EA_Ret (Some (elaborate_to \<Gamma> (proc_ret_kind \<Pi> p) e)) p
                (proc_ret_kind \<Pi> p), FunctionResult p) \<in> E"
  using compile_return_edge[OF assms] by simp

lemmas ex_return_ignores_continuation = inv11_return_ignores_continuation

lemmas ex_multi_return = inv13_multi_return_converge

lemma ex_fallthrough:
  assumes "compile_proc \<Gamma> \<Pi> p (proc_decl_of [] SKIP) n = (n', E, K)"
  shows "\<exists>bex. (bex, EA_Ret None p (proc_ret_kind \<Pi> p), FunctionResult p) \<in> E"
  using assms by (auto simp: compile_proc_def proc_decl_of_def Let_def split: prod.splits)

lemma ex_nested_calls:
  assumes "special_table p1 = None" and "special_table p2 = None"
  shows
  "(Statement n, CallEdge (compile_dst \<Gamma> (Some r1)) (call_formals \<Pi> p1) [], FunctionEntry p1, Statement (Suc n))
      \<in> snd (snd (snd (compile \<Gamma> \<Pi> q (Seq (Call (Some r1) p1 []) (Call (Some r2) p2 []))
            (Statement (Suc (Suc (Suc n)))) n)))
   \<and> (Statement (Suc n), CallEdge (compile_dst \<Gamma> (Some r2)) (call_formals \<Pi> p2) [], FunctionEntry p2, Statement (Suc (Suc (Suc n))))
      \<in> snd (snd (snd (compile \<Gamma> \<Pi> q (Seq (Call (Some r1) p1 []) (Call (Some r2) p2 []))
            (Statement (Suc (Suc (Suc n)))) n)))
   \<and> Statement n \<noteq> Statement (Suc (Suc (Suc n)))"
  using assms by (simp add: Let_def)

lemmas ex_recursion = inv14_recursion_edge

lemma compile_seq_call_edge:
  assumes "\<Pi> pin = Some decl" and "special_table pin = None"
      and "compile \<Gamma> \<Pi> pout (Seq (Call (Some rin) pin actuals) after) k n = (n', en, E, K)"
  shows "(Statement n, CallEdge (compile_dst \<Gamma> (Some rin)) (formals decl)
            (compile_actuals \<Gamma> (formals decl) actuals), FunctionEntry pin,
          Statement (Suc n)) \<in> K"
  using assms by (auto split: prod.splits)

lemma compile_seq_return_edge:
  "compile \<Gamma> \<Pi> p (Seq (Return (Some e)) dead) k n = (n', en, E, K) \<Longrightarrow>
   (Statement n, EA_Ret (Some (elaborate_to \<Gamma> (proc_ret_kind \<Pi> p) e)) p (proc_ret_kind \<Pi> p),
    FunctionResult p) \<in> E"
  by (auto split: prod.splits)

theorem example_early_return_skips_dead:
  assumes comp: "compile \<Gamma> \<Pi> p (Seq (Return (Some e)) dead) k n = (n', en, E, K)"
      and sub: "E \<subseteq> intra g"
  shows "control_at \<Pi> p (Seq (Return (Some e)) dead) k n
           (Seq (Return (Some e)) dead) (Statement n)"
    and "cstep cr_gs g (Statement n, s, stk)
           (FunctionResult p,
            s(ret_var := teval (elaborate_to \<Gamma> (proc_ret_kind \<Pi> p) e) s), stk)"
    and "\<forall>k. FunctionResult p \<noteq> Statement k"
proof -
  show "control_at \<Pi> p (Seq (Return (Some e)) dead) k n
          (Seq (Return (Some e)) dead) (Statement n)"
    by (rule control_at.SeqLeft[OF control_at.ReturnHead])
  have "(Statement n, EA_Ret (Some (elaborate_to \<Gamma> (proc_ret_kind \<Pi> p) e)) p
          (proc_ret_kind \<Pi> p), FunctionResult p) \<in> intra g"
    using compile_seq_return_edge[OF comp] sub by blast
  from cstep_ret[OF this]
  show "cstep cr_gs g (Statement n, s, stk)
          (FunctionResult p,
           s(ret_var := teval (elaborate_to \<Gamma> (proc_ret_kind \<Pi> p) e) s), stk)"
    by simp
  show "\<forall>k. FunctionResult p \<noteq> Statement k" by simp
qed

theorem example_nested_call_preserves_outer:
  assumes p: "\<Pi> pin = Some decl" and spNone: "special_table pin = None"
      and comp: "compile \<Gamma> \<Pi> pout (Seq (Call (Some rin) pin actuals) after) k n = (n', en, E, K)"
      and sub: "K \<subseteq> calls g"
  shows "cstep cr_gs g (Statement n, s, outer # stk)
           (FunctionEntry pin,
            call_enter cr_gs
              (CallEdge (compile_dst \<Gamma> (Some rin)) (formals decl)
                 (compile_actuals \<Gamma> (formals decl) actuals)) s,
            (Statement (Suc n), compile_dst \<Gamma> (Some rin), s) # outer # stk)"
proof -
  have "(Statement n, CallEdge (compile_dst \<Gamma> (Some rin)) (formals decl)
           (compile_actuals \<Gamma> (formals decl) actuals), FunctionEntry pin,
         Statement (Suc n)) \<in> calls g"
    using compile_seq_call_edge[OF p spNone comp] sub by blast
  from cstep_call[OF this] show ?thesis .
qed

lemma example_nested_call_frames:
  "frames_match frs stk \<Longrightarrow>
   frames_match (Frame caller (map_option tv_name tdst) rk # frs)
     ((Statement (Suc n), tdst, caller) # stk)"
  by (rule frames_match_call)

theorem example_normal_fallthrough:
  assumes comp: "compile_proc \<Gamma> \<Pi> p decl n = (n', E, K)"
      and body: "body decl = Assign x a"
  shows "control_at \<Pi> p (body decl) (Statement (Suc n)) n SKIP (Statement (Suc n))"
    and "(Statement (Suc n), EA_Ret None p (proc_ret_kind \<Pi> p), FunctionResult p) \<in> E"
proof -
  show "control_at \<Pi> p (body decl) (Statement (Suc n)) n SKIP (Statement (Suc n))"
    unfolding body by (rule control_at.AssignDone)
  show "(Statement (Suc n), EA_Ret None p (proc_ret_kind \<Pi> p), FunctionResult p) \<in> E"
    using comp by (auto simp: compile_proc_def Let_def body split: prod.splits)
qed


section \<open>Compiler-input contract regressions\<close>

lemma unknown_call_rejected:
  assumes "\<Pi> p = None" and "special_table p = None"
  shows "\<not> wf_source_com \<Pi> (Call dst p actuals)"
  using assms by simp

lemma wrong_call_arity_rejected:
  assumes "\<Pi> p = Some decl" and "length actuals \<noteq> length (formals decl)"
      and "special_table p = None"
  shows "\<not> wf_source_com \<Pi> (Call dst p actuals)"
  using assms by simp

lemma reserved_formal_rejected:
  "~ wf_proc_decl cr_gs \<Pi> (proc_decl_of [ret_var] SKIP)"
  by (simp add: wf_proc_decl_def proc_decl_of_def valid_formal_def)

lemma duplicate_formals_rejected:
  "~ wf_proc_decl cr_gs \<Pi> (proc_decl_of [x, x] SKIP)"
  by (simp add: wf_proc_decl_def proc_decl_of_def)

lemma global_formal_rejected:
  assumes "cr_gs x"
  shows "~ wf_proc_decl cr_gs \<Pi> (proc_decl_of [x] SKIP)"
  using assms by (simp add: wf_proc_decl_def proc_decl_of_def valid_formal_def)

lemma reserved_assignment_rejected:
  "\<not> wf_source_com \<Pi> (Assign ret_var a)"
  by simp

lemma reserved_read_rejected:
  "\<not> wf_source_com \<Pi> (Assign x (V ret_var))"
  by (simp add: source_exp_def)

lemma root_return_rejected:
  "~ wf_compile_input cr_gs \<Pi> ps mnm (Return e)"
  by (simp add: wf_compile_input_def wf_source_program_def)

lemma value_call_requires_value_provider:
  assumes "\<Pi> p = Some (proc_decl_of [] SKIP)" and "special_table p = None"
  shows "\<not> wf_source_com \<Pi> (Call (Some x) p [])"
  using assms by (simp add: proc_decl_of_def value_providing_def)

lemma void_call_accepted:
  assumes "\<Pi> p = Some (proc_decl_of [] SKIP)" and "special_table p = None"
  shows "wf_source_com \<Pi> (Call None p [])"
  using assms by (simp add: proc_decl_of_def)

lemma value_call_accepted:
  assumes "\<Pi> p = Some (proc_decl_of [] (Return (Some (N 0))))"
      and "x \<noteq> ret_var" and "special_table p = None"
  shows "wf_source_com \<Pi> (Call (Some x) p [])"
  using assms
  by (simp add: proc_decl_of_def value_providing_def source_exp_def)

lemma ignored_value_call_accepted:
  assumes "\<Pi> p = Some (proc_decl_of [] (Return (Some (N 0))))" and "special_table p = None"
  shows "wf_source_com \<Pi> (Call None p [])"
  using assms by (simp add: proc_decl_of_def)

definition fallthrough_pi :: proc_table where
  "fallthrough_pi p =
     (if p = (STR ''main'') then Some (proc_decl_of [] SKIP) else None)"

lemma explode_ret_hd [simp]: "hd (String.explode (STR ''#ret'')) \<noteq> CHR ''G''" by eval

lemma main_fallthrough_accepted:
  "wf_compile_input cr_gs fallthrough_pi [] (STR ''main'') SKIP"
  by (auto simp: wf_compile_input_def wf_source_program_def fallthrough_pi_def
        wf_proc_decl_def proc_decl_of_def reserved_ret_var_def ret_var_def
        special_table_def special_pname_nondet_int_def
        special_pname_min_def special_pname_max_def)

lemma missing_main_rejected:
  assumes "\<Pi> mnm = None"
  shows "~ wf_compile_input cr_gs \<Pi> ps mnm main"
  using assms
  by (auto simp: wf_compile_input_def wf_source_program_def)

lemma duplicate_procedure_names_rejected:
  "~ wf_compile_input cr_gs \<Pi> [p, p] mnm main"
  by (simp add: wf_compile_input_def)
end
