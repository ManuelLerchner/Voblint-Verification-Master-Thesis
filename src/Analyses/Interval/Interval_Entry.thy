theory Interval_Entry
  imports Interval_Checks "Voblint_Soundness.Run_Analysis_Sound"
begin

section \<open>Interval public runtime API and source-level soundness\<close>

text \<open>
  Interval's public soundness, in the vocabulary its runtime API returns. Nothing is
  derived here: \<open>Interval_Assembly\<close>'s instances of the shared unit-context assembly
  already prove each statement over the assembly's own names, and one equation per
  solver discipline is all that is needed to say the same thing about the names a
  caller sees.

  Three disciplines appear below because three are published as verdicts callers may
  rely on: Apinis warrowing, which \<open>analyse\<close> dispatches to, and the always-join and
  per-origin siblings \<open>analyse_with_solver\<close> compares against it on the identical
  equation system. They differ in one parameter of one locale, so the three blocks
  differ only in which instance they name.

  In each block the four coverage facts are stated once, as context assumptions,
  rather than repeated on every theorem. They are requirements on the solved key set,
  assumed and not derived from termination: an edge or call out of an unknown the
  solve visited must land on one it also visited. They are weaker than the
  unconditional \<^const>\<open>vars_cover\<close>, so each statement is exactly as applicable as the
  hand-written one it replaces. The \<open>vars_cover\<close> readings follow.
\<close>

subsection \<open>Reading the assembly's state at a node under each discipline\<close>

lemma interval_td_state_at_eq:
  "interval_td_state_at gs p v
     = (case lookup_context (analyse_interval_td_result_for gs p) v () of
          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"
  by (simp add: interval_warrow_asm.state_at_unfold analyse_interval_td_result_for_def)

lemma interval_join_state_at_eq:
  "interval_join_state_at gs p v
     = (case lookup_context (analyse_interval_join_result_for gs p) v () of
          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"
  by (simp add: interval_join_asm.state_at_unfold analyse_interval_join_result_for_def)

lemma interval_po_state_at_eq:
  "interval_po_state_at gs p v
     = (case lookup_context (analyse_interval_per_origin_result_for gs p) v () of
          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"
  by (simp add: interval_po_asm.state_at_unfold analyse_interval_per_origin_result_for_def)

section \<open>Apinis warrowing: the production default\<close>

context
  fixes p :: imp_prog
  assumes solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and entry_cov: "(cfg_entry (prog_cfg p), ())
        \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
    and fwd_ok: "\<And>u a w ctx.
        (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
        \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
        \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
    and call_fwd_ok: "\<And>u ctx dst fs as q k.
        (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
        \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
    and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
        (cl, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
        \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
begin

lemmas interval_warrow_closure =
  solve entry_cov[unfolded interval_warrow_asm.sol_vars_def[symmetric]]
  fwd_ok[unfolded interval_warrow_asm.sol_vars_def[symmetric]]
  call_fwd_ok[unfolded interval_warrow_asm.sol_vars_def[symmetric]]
  comb_fwd_ok[unfolded interval_warrow_asm.sol_vars_def[symmetric]]

lemma analyse_interval_td_result_node_sound_for:
  "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
     \<subseteq> \<lbrakk>case lookup_context (analyse_interval_td_result_for (declared_global p) p) v () of
                       Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using interval_warrow_asm.result_node_sound_closure[OF interval_warrow_closure]
  unfolding interval_td_state_at_eq .

theorem analyse_interval_td_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Proved)
      \<in> set (analyse_interval_td_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule interval_warrow_asm.report_proved_sound_closure
        [OF interval_warrow_closure mem[unfolded analyse_interval_td_report_for_def]])

theorem analyse_interval_td_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Refuted)
      \<in> set (analyse_interval_td_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule interval_warrow_asm.report_refuted_sound_closure
        [OF interval_warrow_closure mem[unfolded analyse_interval_td_report_for_def]])

end

subsection \<open>Coverage as one checkable side condition\<close>

text \<open>
  \<^const>\<open>vars_cover\<close> implies the four closure facts above, at the one context this
  routed solve uses. Bundling them is what makes the side condition decidable in a
  single step: \<^const>\<open>vars_cover_exec\<close> walks the two edge enumerations, so a caller
  discharges coverage \<^theory_text>\<open>by eval\<close> instead of by four hand-written case analyses over
  the solved key set.
\<close>

context
  fixes p :: imp_prog
begin

lemma interval_conf_vars_cover_prog_of_exec:
  assumes cover: "vars_cover_exec (prog_cfg p)
      (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
  shows "vars_cover (prog_cfg p)
      (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
  by (rule vars_cover_of_exec[OF _ _ cover])
     (simp_all add: prog_cfg_def compile_prog_finite)

lemma analyse_interval_td_result_node_sound_of_cover:
  assumes solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
        (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
  shows "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
           \<subseteq> \<lbrakk>case lookup_context
                    (analyse_interval_td_result_for (declared_global p) p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using interval_warrow_asm.result_node_sound
          [OF solve cover[unfolded interval_warrow_asm.sol_vars_def[symmetric]]]
  unfolding interval_td_state_at_eq .

subsection \<open>Source runs, in the vocabulary the runtime API returns\<close>

text \<open>
  What a caller of \<^const>\<open>analyse_interval_td_result_for\<close> actually wants to know: run
  the source program, stop anywhere, and the store you are holding is described by the
  entry the analysis returned for the program point you are standing at. The simulation
  \<^const>\<open>csim\<close> is what names that point.
\<close>

theorem analyse_interval_td_source_sound_for:
  fixes s0 s :: store
  assumes solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
        (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context
                                  (analyse_interval_td_result_for (declared_global p) p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using interval_warrow_asm.source_sound
          [OF solve cover[unfolded interval_warrow_asm.sol_vars_def[symmetric]] wf s0 run]
  unfolding interval_td_state_at_eq .

text \<open>
  The completed-run reading of the same fact: a source run that finishes leaves its
  final store inside the analysis result at the program exit. It is weaker --- one point
  instead of all of them --- but it needs no \<^const>\<open>csim\<close> witness to state.
\<close>

theorem analyse_interval_td_completed_run_sound_for:
  fixes s0 s :: store
  assumes solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
        (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_interval_td_result_for (declared_global p) p)
                            (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using interval_warrow_asm.completed_run_sound
          [OF solve cover[unfolded interval_warrow_asm.sol_vars_def[symmetric]] wf s0 run]
  unfolding interval_td_state_at_eq .

end

subsection \<open>The warrowing endpoints at \<open>declared_global\<close>\<close>

corollary analyse_interval_td_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ())
          \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and fwd_ok: "\<And>u a w ctx.
          (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
          \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and call_fwd_ok: "\<And>u ctx dst fs as q k.
          (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
          (cl, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_td_report_sound_proved_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_interval_td_report_def]])

corollary analyse_interval_td_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ())
          \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and fwd_ok: "\<And>u a w ctx.
          (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
          \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and call_fwd_ok: "\<And>u ctx dst fs as q k.
          (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
          (cl, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_interval_td_report_sound_refuted_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_interval_td_report_def]])

text \<open>
  The headline pair, over \<^const>\<open>analyse_interval_td_result\<close> --- the table the runtime
  API hands back on the branch \<open>analyse\<close> takes for Interval. Two side conditions
  survive, and both are decided per program rather than proved once: the solver
  returned a partial post-solution for this program
  (\<^const>\<open>interval_conf_terminates_prog_warrow\<close>; no result here proves the solver
  terminates on every input), and it solved enough keys (\<^const>\<open>vars_cover\<close>, decidable
  through \<open>interval_conf_vars_cover_prog_of_exec\<close>).
\<close>

corollary analyse_interval_td_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_interval_td_result p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_interval_td_result_def
  by (rule analyse_interval_td_source_sound_for[OF solve cover wf s0 run])

corollary analyse_interval_td_completed_run_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_interval_td_result p)
                            (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_interval_td_result_def
  by (rule analyse_interval_td_completed_run_sound_for[OF solve cover wf s0 run])

section \<open>Solver-choice soundness: join and per-origin update rules\<close>

text \<open>
  The two siblings \<open>analyse_with_solver\<close> compares against the production default. Each
  reads its own instance's solved table, and each proves the same statement by the same
  route --- the update rule is a parameter of \<^locale>\<open>unit_dg_analysis\<close>, so nothing
  below re-derives node soundness.
\<close>

context
  fixes p :: imp_prog
  assumes solve: "interval_conf_terminates_prog (declared_global p) p"
    and entry_cov: "(cfg_entry (prog_cfg p), ())
        \<in> fst (interval_conf_sol_prog (declared_global p) p)"
    and fwd_ok: "\<And>u a w ctx.
        (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
        \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
        \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
    and call_fwd_ok: "\<And>u ctx dst fs as q k.
        (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
        \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
    and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
        (cl, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)
        \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
begin

lemmas interval_join_closure =
  solve entry_cov[unfolded interval_join_asm.sol_vars_def[symmetric]]
  fwd_ok[unfolded interval_join_asm.sol_vars_def[symmetric]]
  call_fwd_ok[unfolded interval_join_asm.sol_vars_def[symmetric]]
  comb_fwd_ok[unfolded interval_join_asm.sol_vars_def[symmetric]]

lemma analyse_interval_join_result_node_sound_for:
  "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
     \<subseteq> \<lbrakk>case lookup_context
              (analyse_interval_join_result_for (declared_global p) p) v () of
                       Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using interval_join_asm.result_node_sound_closure[OF interval_join_closure]
  unfolding interval_join_state_at_eq .

theorem analyse_interval_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Proved)
      \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule interval_join_asm.report_proved_sound_closure
        [OF interval_join_closure mem[unfolded analyse_interval_report_for_def]])

theorem analyse_interval_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Refuted)
      \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule interval_join_asm.report_refuted_sound_closure
        [OF interval_join_closure mem[unfolded analyse_interval_report_for_def]])

end

corollary analyse_interval_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ())
          \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and fwd_ok: "\<And>u a w ctx.
          (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
          \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok: "\<And>u ctx dst fs as q k.
          (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
          (cl, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_report_sound_proved_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_interval_report_def]])

corollary analyse_interval_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ())
          \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and fwd_ok: "\<And>u a w ctx.
          (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
          \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok: "\<And>u ctx dst fs as q k.
          (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
          (cl, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_interval_report_sound_refuted_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_interval_report_def]])

context
  fixes p :: imp_prog
  assumes solve: "interval_conf_terminates_prog_per_origin (declared_global p) p"
    and entry_cov: "(cfg_entry (prog_cfg p), ())
        \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
    and fwd_ok: "\<And>u a w ctx.
        (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
        \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
        \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
    and call_fwd_ok: "\<And>u ctx dst fs as q k.
        (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
        \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q, ())
              \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
    and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
        (cl, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
        \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
begin

lemmas interval_po_closure =
  solve entry_cov[unfolded interval_po_asm.sol_vars_def[symmetric]]
  fwd_ok[unfolded interval_po_asm.sol_vars_def[symmetric]]
  call_fwd_ok[unfolded interval_po_asm.sol_vars_def[symmetric]]
  comb_fwd_ok[unfolded interval_po_asm.sol_vars_def[symmetric]]

lemma analyse_interval_per_origin_result_node_sound_for:
  "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
     \<subseteq> \<lbrakk>case lookup_context
              (analyse_interval_per_origin_result_for (declared_global p) p) v () of
                       Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using interval_po_asm.result_node_sound_closure[OF interval_po_closure]
  unfolding interval_po_state_at_eq .

theorem analyse_interval_report_per_origin_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Proved)
      \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule interval_po_asm.report_proved_sound_closure
        [OF interval_po_closure
            mem[unfolded analyse_interval_report_per_origin_for_def]])

theorem analyse_interval_report_per_origin_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Refuted)
      \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule interval_po_asm.report_refuted_sound_closure
        [OF interval_po_closure
            mem[unfolded analyse_interval_report_per_origin_for_def]])

end

corollary analyse_interval_report_per_origin_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_per_origin (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ())
          \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and fwd_ok: "\<And>u a w ctx.
          (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
          \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and call_fwd_ok: "\<And>u ctx dst fs as q k.
          (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (FunctionEntry q, ())
                \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
          (cl, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_report_per_origin_sound_proved_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_interval_report_per_origin_def]])

corollary analyse_interval_report_per_origin_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_per_origin (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ())
          \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and fwd_ok: "\<And>u a w ctx.
          (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
          \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and call_fwd_ok: "\<And>u ctx dst fs as q k.
          (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (FunctionEntry q, ())
                \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
          (cl, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_interval_report_per_origin_sound_refuted_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_interval_report_per_origin_def]])

end

