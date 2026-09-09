theory Sign_Entry
  imports Sign_Checks "Voblint_Soundness.Run_Analysis_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

section \<open>Sign codegen API: an arbitrary VIMP program, and its OCaml export\<close>

subsection \<open>Whole-program entry point: an arbitrary VIMP program\<close>

text \<open>
  Sign's public soundness, in the vocabulary its runtime API returns. Nothing is
  derived here: \<open>Sign_Assembly\<close>'s instance of the shared unit-context assembly
  already proves each statement over the assembly's own names, and the single
  equation below is all that is needed to say the same thing about the name a
  caller sees.

  The four coverage facts are stated once, as context assumptions, rather than
  repeated on every theorem. They are requirements on the solved key set, assumed
  here and not derived from termination: an edge or call out of an unknown the
  solve visited must land on one it also visited. They are weaker than the
  unconditional \<^const>\<open>vars_cover\<close>, so each statement below is exactly as
  applicable as the hand-written one it replaces. The \<open>vars_cover\<close> readings, which
  a caller can discharge \<^theory_text>\<open>by eval\<close>, follow at the end.
\<close>

lemma sign_unit_state_at_eq:
  "sign_unit_state_at gs p v
     = (case lookup_context (analyse_sign_result_for gs p) v () of
          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"
  by (simp add: sign_join.state_at_unfold analyse_sign_result_for_def)

context
  fixes p :: imp_prog
  assumes solve: "sctx_terminates_prog (declared_global p) p"
    and entry_cov: "(cfg_entry (prog_cfg p), ())
        \<in> fst (sctx_sol_prog (declared_global p) p)"
    and fwd_ok: "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
        \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p)
        \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)"
    and call_fwd_ok: "\<And>u ctx dst fs as q k.
        (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
        \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
    and comb_fwd_ok: "\<And>cl c1 dst fs as q k.
        (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) p)
        \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
        \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) p)"
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
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule sign_join.report_proved_sound_closure
        [OF sign_closure mem[unfolded analyse_sign_report_for_def]])

theorem analyse_sign_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule sign_join.report_refuted_sound_closure
        [OF sign_closure mem[unfolded analyse_sign_report_for_def]])

end

subsection \<open>Coverage as one checkable side condition\<close>

text \<open>
  \<^const>\<open>vars_cover\<close> implies the four closure facts above, at the one context this
  routed solve uses. Bundling them is what makes the side condition decidable in a
  single step: \<^const>\<open>vars_cover_exec\<close> walks the two edge enumerations, so a caller
  discharges coverage \<^theory_text>\<open>by eval\<close> instead of by four hand-written case analyses
  over the solved key set.
\<close>

context
  fixes p :: imp_prog
begin

lemma sctx_vars_cover_prog_of_exec:
  assumes cover: "vars_cover_exec (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
  shows "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
  by (rule vars_cover_of_exec[OF _ _ cover])
     (simp_all add: prog_cfg_def compile_prog_finite)

lemma analyse_sign_result_node_sound_of_cover:
  assumes solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
  shows "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for (declared_global p) p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  using sign_join.result_node_sound
          [OF solve cover[unfolded sign_join.sol_vars_def[symmetric]]]
  unfolding sign_unit_state_at_eq .

subsection \<open>Source runs, in the vocabulary the runtime API returns\<close>

text \<open>
  What a caller of \<^const>\<open>analyse_sign_result_for\<close> actually wants to know: run the
  source program, stop anywhere, and the store you are holding is described by the
  entry the analysis returned for the program point you are standing at. The
  simulation \<^const>\<open>csim\<close> is what names that point --- a partly executed command and
  its frame stack sit at a graph node, and it is that node's table entry the store
  belongs to.
\<close>

theorem analyse_sign_source_sound_for:
  fixes s0 s :: store
  assumes solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
    and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_sign_result_for (declared_global p) p) v () of
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
  assumes solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
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
  \<open>analyse_sign_report\<close>'s own soundness corollaries below are the
  check-report layer's \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances,
  matching \<open>analyse_sign_report_sound_proved_for\<close>/\<open>_refuted_for\<close> above.
\<close>

corollary analyse_sign_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "sctx_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_sign_report_sound_proved_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_sign_report_def]])

corollary analyse_sign_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "sctx_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_sign_report_sound_refuted_for
        [OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok
            mem[unfolded analyse_sign_report_def]])

text \<open>
  The headline pair, at \<^const>\<open>declared_global\<close> \<open>p\<close> and over
  \<^const>\<open>analyse_sign_result\<close> --- the table the runtime API hands back. Two side
  conditions survive, and both are decided per program rather than proved once:
  the solver returned a partial post-solution for this program
  (\<^const>\<open>sctx_terminates_prog\<close>; no result here proves the solver terminates on
  every input), and it solved enough keys (\<^const>\<open>vars_cover\<close>, decidable through
  \<open>sctx_vars_cover_prog_of_exec\<close>).
\<close>

corollary analyse_sign_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
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
    and solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_sign_result p) (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_sign_result_def
  by (rule analyse_sign_completed_run_sound_for[OF solve cover wf s0 run])

text \<open>
  \<open>gEx\<close>, \<open>dgEx_eqs\<close>, and \<open>dgEx_sol\<close> (\<open>Exec_Sign_DG_Run\<close>, Examples) are the
  \<open>gs = sign_ex_gs\<close>, \<open>p = sign_ex_prog\<close> instance of the arbitrary-classifier,
  arbitrary-program chain above, not a separate parallel definition.
\<close>

text \<open>
  No per-domain \<open>export_code\<close> here: a caller reaches the generic, already-sound
  \<^const>\<open>analyse_sign_report\<close> through the unified dispatcher \<open>analyse\<close>
  (\<open>Analyse_Dispatch\<close>, downstream), which is the one thing exported to OCaml.
  A second, domain-specific export module would be a parallel, redundant API
  surface for the same computation.
\<close>
subsection \<open>Base-style flow-sensitive global regressions\<close>

text \<open>
  Acceptance regressions for the Base-style migration: \<open>D\<close> carries the whole abstract
  state (VIMP globals included), reachability-lifted, instead of routing globals
  through a separate flow-\<^emph>\<open>in\<close>sensitive solver-global unknown.
\<close>

definition sign_flow_sensitive_global_prog :: imp_prog where
  "sign_flow_sensitive_global_prog = program { global Gx;
     void f() { Gx := 1 }
     void main() { Gx := 0; f(); __voblint_check(0 < Gx) } }"

text \<open>
  Under the old unlifted routing, \<open>Gx := 0\<close> and \<open>Gx := 1\<close> both feed the same
  flow-insensitive shared summary and join to \<open>SNonNeg\<close>, leaving the check
  \<open>UNKNOWN\<close>. With the whole state lifted into \<open>D\<close>, the call's own local answer
  at the \<open>main\<close> exit carries \<open>Gx\<close>'s value exactly as \<^const>\<open>sign_tf_st_for\<close>
  and \<^const>\<open>sign_enter_st_for\<close> left it, so the check is exact.
\<close>

lemma sign_flow_sensitive_global_result:
  "(Statement 4, Less (N 0) (V (STR ''Gx'')), Check_Proved) \<in> set (analyse_sign_report sign_flow_sensitive_global_prog)"
  by eval

definition sign_dead_branch_bot_prog :: imp_prog where
  "sign_dead_branch_bot_prog = program { global Gx;
     void f(n) { if (n < 0) { Gx := -1 } else { Gx := 1 } }
     void main() { Gx := 0; f(5); __voblint_check(0 < Gx) } }"

text \<open>
  \<open>f\<close> is called with \<open>n = 5\<close>, abstracted to \<open>SPos\<close>: Sign's own comparison-against-zero
  tables refute \<open>n < 0\<close> exactly (\<open>SPos < SZero\<close> is definitely false), so the \<open>Gx := -1\<close>
  arm's own local answer is genuinely \<^const>\<open>Bot\<close> in the lifted carrier, not merely an
  imprecise contribution the exit join has to absorb. The two arms deliberately carry
  \<^emph>\<open>different\<close> signs so a leaked dead arm is observable: were the reachability-lift
  fix absent (or otherwise defeated), the join \<open>SNeg \<squnion> SPos = STop\<close> would leave the
  check \<open>UNKNOWN\<close> instead of \<open>PROVED\<close>. Contrast a numeric-bound guard such as \<open>n < 2\<close>
  at \<open>n = 5\<close>: Sign cannot refute that from \<open>SPos\<close> alone (unlike Interval, which tracks
  exact bounds -- see \<open>03-procedures/precision/05-dead_branch_no_bottom_leak.vimp\<close>), so
  that shape does not isolate this property for Sign.
\<close>

lemma sign_dead_branch_bot_result:
  "(Statement 6, Less (N 0) (V (STR ''Gx'')), Check_Proved) \<in> set (analyse_sign_report sign_dead_branch_bot_prog)"
  by eval

subsection \<open>Recursion and repeated call sites\<close>

text \<open>
  Sign otherwise has no regression fixture exercising recursion or a procedure called
  from two call sites -- the mechanism that separates how callee-entry values thread
  through the equation system (a flow-sensitive local unknown revisited per predecessor
  vs. a keyed-seed slot per callee entry). \<open>sign_factorial_prog\<close> mirrors Interval's own
  recursive-factorial regression at Sign's coarser granularity; Sign has no
  \<open>--context\<close> flag, so there is no CLI parameter to fix here, only the program shape.
  The entry check \<open>0 < n\<close> stays \<open>UNKNOWN\<close>: Sign has no context-sensitivity feature, so
  the callee entry joins over every call site's argument (here \<open>3\<close> and \<open>4\<close>).
\<close>

definition sign_factorial_prog :: imp_prog where
  "sign_factorial_prog =
     program {
       void factorial(n) {
         __voblint_check(0 < n);
         if (n < 2) {
           return 1
         } else {
           r := factorial(n - 1);
           __voblint_check(0 < r);
           return n * r
         }
       }
       void main() {
         a := factorial(3);
         b := factorial(4);
         __voblint_check(0 < a);
         __voblint_check(0 < b)
       }
     }"

lemma sign_factorial_result:
  "set (analyse_sign_report sign_factorial_prog) =
     {(Statement 0, Less (N 0) (V (STR ''n'')), Check_Unknown),
      (Statement 4, Less (N 0) (V (STR ''r'')), Check_Proved),
      (Statement 9, Less (N 0) (V (STR ''a'')), Check_Proved),
      (Statement 10, Less (N 0) (V (STR ''b'')), Check_Proved)}"
  by eval

text \<open>
  \<open>sign_two_call_sites_prog\<close> mirrors
  \<open>tests/regression/03-procedures/known-imprecision/01-two_call_sites_same_procedure.vimp\<close>:
  one non-recursive procedure, two call sites, isolating repeated-entry-node evaluation
  without recursion's added complexity. Unlike Interval's analogue, which genuinely loses
  precision at a repeated call site under Interval's infinite-height carrier and its
  warrowing solver, both checks here stay \<open>PROVED\<close>: Sign's finite height and its
  always-join solver rule never separate the two call sites' contributions here.
\<close>

definition sign_two_call_sites_prog :: imp_prog where
  "sign_two_call_sites_prog =
     program {
       void square(n) {
         return n * n
       }
       void main() {
         a := square(3);
         b := square(4);
         __voblint_check(0 < a);
         __voblint_check(0 < b)
       }
     }"

lemma sign_two_call_sites_result:
  "set (analyse_sign_report sign_two_call_sites_prog) =
     {(Statement 4, Less (N 0) (V (STR ''a'')), Check_Proved),
      (Statement 5, Less (N 0) (V (STR ''b'')), Check_Proved)}"
  by eval

end

