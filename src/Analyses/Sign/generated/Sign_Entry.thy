theory Sign_Entry
  imports
    Sign_Checks
begin

section \<open>Sign codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>manifests/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  Sign's public soundness, in the vocabulary its runtime API returns: the branch the
  unified dispatcher takes when the configured domain is Sign. Nothing is derived here.
  Each published solver discipline has its own instance of the shared unit-context
  assembly, that instance already proves every statement below over the assembly's own
  names, and one equation per discipline is all it takes to say the same thing about
  the name a caller sees.

  The four coverage facts are stated once, as context assumptions, rather than repeated
  on every theorem. They are requirements on the solved key set, assumed here and not
  derived from termination: an edge or call out of an unknown the solve visited must
  land on one it also visited. They are weaker than the unconditional \<^const>\<open>vars_cover\<close>, so
  each statement below is exactly as applicable as an unconditional one would be. The
  \<open>vars_cover\<close> readings, which a caller can discharge \<^theory_text>\<open>by eval\<close>, follow each
  discipline that publishes them.

  No per-domain \<^theory_text>\<open>export_code\<close> here: a caller reaches the generic, already-sound report
  through the unified dispatcher \<open>analyse\<close>, which is the one thing exported to OCaml. A
  second, domain-specific export module would be a parallel, redundant API surface for
  the same computation.
\<close>

subsection \<open>Always join: the production default\<close>

lemma sign_unit_state_at_eq:
  "sign_unit_state_at gs p v
     = (case lookup_context (analyse_sign_result_for gs p) v () of
          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"
  by (simp add: sign_join.state_at_unfold analyse_sign_result_for_def)

context
  fixes p :: imp_prog
  assumes solve: "sign_conf_terminates_prog (declared_global p) p"
    and entry_cov: "(cfg_entry (prog_cfg p), ())
        \<in> fst (sign_conf_sol_prog (declared_global p) p)"
    and fwd_ok: "\<And>u a w ctx. (u, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)
        \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
        \<Longrightarrow> (w, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
    and call_fwd_ok: "\<And>u ctx dst fs as q k.
        (u, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)
        \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
    and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
        (cl, c1) \<in> fst (sign_conf_sol_prog (declared_global p) p)
        \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (k, c1) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
begin

lemmas sign_closure =
  solve
  fwd_ok[unfolded sign_join.sol_vars_def[symmetric]]
  call_fwd_ok[unfolded sign_join.sol_vars_def[symmetric]]
  comb_fwd_ok[unfolded sign_join.sol_vars_def[symmetric]]
  entry_cov[unfolded sign_join.sol_vars_def[symmetric]]

lemma analyse_sign_result_node_sound_for:
  "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
     \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for (declared_global p) p) v () of
                       Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using sign_join.result_node_sound_closure[OF sign_closure]
  unfolding sign_unit_state_at_eq .

theorem analyse_sign_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule sign_join.report_proved_sound_closure
        [OF sign_closure mem[unfolded analyse_sign_report_for_def]])

theorem analyse_sign_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule sign_join.report_refuted_sound_closure
        [OF sign_closure mem[unfolded analyse_sign_report_for_def]])

end

subsection \<open>Coverage as one checkable side condition\<close>

text \<open>
  \<^const>\<open>vars_cover\<close> implies the four closure facts above, at the one context this routed
  solve uses. Bundling them is what makes the side condition decidable in a single
  step: \<^const>\<open>vars_cover_exec\<close> walks the two edge enumerations, so a caller discharges
  coverage \<^theory_text>\<open>by eval\<close> instead of by four hand-written case analyses over the solved key
  set.
\<close>

context
  fixes p :: imp_prog
begin

lemma sign_conf_vars_cover_prog_of_exec:
  assumes cover: "vars_cover_exec (prog_cfg p)
      (fst (sign_conf_sol_prog (declared_global p) p))"
  shows "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
  by (rule sign_join.vars_cover_of_exec_prog[unfolded sign_join.sol_vars_def, OF cover])

lemma analyse_sign_result_node_sound_of_cover:
  assumes solve: "sign_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
  shows "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for (declared_global p) p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using sign_join.result_node_sound
          [OF solve cover[unfolded sign_join.sol_vars_def[symmetric]]]
  unfolding sign_unit_state_at_eq .

subsection \<open>Source runs, in the vocabulary the runtime API returns\<close>

text \<open>
  What a caller of \<^const>\<open>analyse_sign_result_for\<close> actually wants to know: run the source
  program, stop anywhere, and the store you are holding is described by the entry the
  analysis returned for the program point you are standing at. The simulation \<^const>\<open>csim\<close>
  is what names that point --- a partly executed command and its frame stack sit at a
  graph node, and it is that node's table entry the store belongs to.
\<close>

theorem analyse_sign_source_sound_for:
  fixes s0 s :: store
  assumes solve: "sign_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
    and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context
                                (analyse_sign_result_for (declared_global p) p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using sign_join.source_sound
          [OF solve cover[unfolded sign_join.sol_vars_def[symmetric]] wf s0 run]
  unfolding sign_unit_state_at_eq .

text \<open>
  The completed-run reading of the same fact, and the one a reader meets first: a
  source run that finishes leaves its final store inside the analysis result at the
  program exit. It is weaker --- one point instead of all of them --- but it needs no
  \<^const>\<open>csim\<close> witness to state.
\<close>

theorem analyse_sign_completed_run_sound_for:
  fixes s0 s :: store
  assumes solve: "sign_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
    and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_sign_result_for (declared_global p) p)
                            (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using sign_join.completed_run_sound
          [OF solve cover[unfolded sign_join.sol_vars_def[symmetric]] wf s0 run]
  unfolding sign_unit_state_at_eq .

end

text \<open>
  \<^const>\<open>analyse_sign_report\<close>'s own soundness corollaries: the check-report layer's
  \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances, matching
  \<open>analyse_sign_report_sound_proved_for\<close>/\<open>_refuted_for\<close> above.
\<close>

corollary analyse_sign_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "sign_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ())
          \<in> fst (sign_conf_sol_prog (declared_global p) p)"
      and fwd_ok: "\<And>u a w ctx. (u, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
          \<Longrightarrow> (w, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok: "\<And>u ctx dst fs as q k.
          (u, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
          (cl, c1) \<in> fst (sign_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (k, c1) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_sign_report_sound_proved_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_sign_report_def]])

corollary analyse_sign_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "sign_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ())
          \<in> fst (sign_conf_sol_prog (declared_global p) p)"
      and fwd_ok: "\<And>u a w ctx. (u, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
          \<Longrightarrow> (w, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok: "\<And>u ctx dst fs as q k.
          (u, ctx) \<in> fst (sign_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
          (cl, c1) \<in> fst (sign_conf_sol_prog (declared_global p) p)
          \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
          \<Longrightarrow> (k, c1) \<in> fst (sign_conf_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_sign_report_sound_refuted_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_sign_report_def]])

text \<open>
  The headline pair, at \<^const>\<open>declared_global\<close> \<open>p\<close> and over \<^const>\<open>analyse_sign_result\<close> --- the
  table the runtime API hands back. Two side conditions survive, and both are decided
  per program rather than proved once: the solver returned a partial post-solution for
  this program (\<^const>\<open>sign_conf_terminates_prog\<close>; no result here proves the solver
  terminates on every input), and it solved enough keys (\<^const>\<open>vars_cover\<close>, decidable
  through \<open>sign_conf_vars_cover_prog_of_exec\<close>).
\<close>

corollary analyse_sign_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "sign_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_sign_result p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_sign_result_def
  by (rule analyse_sign_source_sound_for[OF solve cover wf s0 run])

corollary analyse_sign_completed_run_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "sign_conf_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sign_conf_sol_prog (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_sign_result p) (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_sign_result_def
  by (rule analyse_sign_completed_run_sound_for[OF solve cover wf s0 run])

end
