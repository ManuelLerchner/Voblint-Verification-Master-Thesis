theory Example_Interval_DG_Ctx_Factorial_Regression
  imports
    "Voblint_Formalization.Interval_Exec_Ctx_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Recursive factorial under entry-state context sensitivity\<close>

text \<open>
  Acceptance regression for issue #123's structural-reachability lift together with the
  keyed D/G generator's buffered same-key \<^const>\<open>Side\<close> publication: recursive
  \<open>factorial\<close>, called at \<open>n=3\<close> and \<open>n=4\<close> from \<open>main\<close>, exercises four distinct entry-state
  contexts (\<open>n=[1,1]\<close>, \<open>[2,2]\<close>, \<open>[3,3]\<close>, \<open>[4,4]\<close>). Before the buffering fix,
  \<^const>\<open>entry_state_eqs\<close> never terminated on this program: two Side writes to the same
  global key within one equation evaluation destabilized the update rule's per-origin gate.
  Before the reachability lift, the dead \<open>n<2\<close> base-case branch's own \<open>#ret := 1\<close>
  assignment still produced a non-bottom value from an already-unreachable predecessor,
  widening every \<open>factorial(n>=2)\<close> result to \<open>[1,n!]\<close> instead of the exact \<open>[n!,n!]\<close>.
\<close>

definition fact_prog :: imp_prog where
  "fact_prog = program {
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
       __voblint_check(a == 6);
       __voblint_check(b == 24)
     }
   }"

abbreviation fact_gs :: "vname \<Rightarrow> bool" where "fact_gs \<equiv> declared_global fact_prog"

definition fact_cfg :: cfg where
  "fact_cfg = compile_prog (prog_table fact_prog) (prog_procs fact_prog) prog_main_name (prog_main fact_prog)"

definition fact_is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "fact_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars fact_prog)"

definition fact_sol ::
  "(pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "fact_sol = entry_state_sol_prog fact_gs prog_main_name fact_prog"

lemma fact_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c
     (entry_state_eqs_prog fact_gs prog_main_name fact_prog)
     (cfg_exit fact_cfg, []) \<noteq> None"
  by eval

abbreviation fact_lookup :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "fact_lookup s x \<equiv> lookup_resolved_st_q s (location_of fact_gs x)"

definition ctx_a :: "ivl list" where
  "ctx_a = entry_state_route fact_gs fact_is_bot_pred
             (locals (snd fact_sol (Inl (Statement 7, []))))
             (CallEdge (Some (STR ''a'')) [STR ''n''] [aexp.N 3])"

definition ctx_b :: "ivl list" where
  "ctx_b = entry_state_route fact_gs fact_is_bot_pred
             (locals (snd fact_sol (Inl (Statement 8, []))))
             (CallEdge (Some (STR ''b'')) [STR ''n''] [aexp.N 4])"

definition ctx_rec :: "ivl list \<Rightarrow> ivl list" where
  "ctx_rec caller_ctx = entry_state_route fact_gs fact_is_bot_pred
                          (locals (snd fact_sol (Inl (Statement 3, caller_ctx))))
                          (CallEdge (Some (STR ''r'')) [STR ''n''] [Minus (V (STR ''n'')) (aexp.N 1)])"

definition ctx_a2 :: "ivl list" where "ctx_a2 = ctx_rec ctx_a"
definition ctx_a1 :: "ivl list" where "ctx_a1 = ctx_rec ctx_a2"
definition ctx_b3 :: "ivl list" where "ctx_b3 = ctx_rec ctx_b"

text \<open>\<open>#ret\<close> at \<open>FunctionResult\<close> for each context -- the leak-detection query. Reads back
  through the lifted carrier: \<^const>\<open>Bot\<close> would mean the whole activation is unreachable,
  not merely an imprecise interval; here every context is reachable and exact.\<close>
lemma fact_return_ctx_a:
  "(case locals (snd fact_sol (Inl (FunctionResult (STR ''factorial''), ctx_a))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (fact_lookup d (STR ''#ret'')))
     = Some (Ivl (Fin 6) (Fin 6))"
  by eval

lemma fact_return_ctx_b:
  "(case locals (snd fact_sol (Inl (FunctionResult (STR ''factorial''), ctx_b))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (fact_lookup d (STR ''#ret'')))
     = Some (Ivl (Fin 24) (Fin 24))"
  by eval

lemma fact_return_ctx_a2:
  "(case locals (snd fact_sol (Inl (FunctionResult (STR ''factorial''), ctx_a2))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (fact_lookup d (STR ''#ret'')))
     = Some (Ivl (Fin 2) (Fin 2))"
  by eval

lemma fact_return_ctx_a1:
  "(case locals (snd fact_sol (Inl (FunctionResult (STR ''factorial''), ctx_a1))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (fact_lookup d (STR ''#ret'')))
     = Some (Ivl (Fin 1) (Fin 1))"
  by eval

text \<open>The dead \<open>return 1\<close> edge's own local state (\<open>Statement 2\<close>) is structurally
  \<^const>\<open>Bot\<close> within every \<open>n>=2\<close> context -- the actual fix the reachability lift
  delivers, not merely an imprecise interval that happens to widen away.\<close>
lemma fact_dead_branch_bot_ctx_a:
  "(locals (snd fact_sol (Inl (Statement 2, ctx_a))) :: ivl exec_dg_st lifted) = Bot"
  by eval

lemma fact_dead_branch_bot_ctx_a2:
  "(locals (snd fact_sol (Inl (Statement 2, ctx_a2))) :: ivl exec_dg_st lifted) = Bot"
  by eval

text \<open>Final acceptance value: the production check-report pipeline end to end, including
  the two \<open>main\<close>-level checks (\<open>a==6\<close>, \<open>b==24\<close>) whose precision depends on the dead
  branch never leaking into \<open>FunctionResult\<close>'s join.\<close>
lemma fact_analyse_interval_entry_state:
  "analyse_interval_entry_state fact_prog =
     [(Statement 0, Less (aexp.N 0) (V (STR ''n'')), Check_Proved),
      (Statement 4, Less (aexp.N 0) (V (STR ''r'')), Check_Proved),
      (Statement 9, bexp.Eq (V (STR ''a'')) (aexp.N 6), Check_Proved),
      (Statement 10, bexp.Eq (V (STR ''b'')) (aexp.N 24), Check_Proved)]"
  by eval

end
