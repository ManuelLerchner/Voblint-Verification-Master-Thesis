theory Example_Interval_DG_Ctx_Globals_Regression
  imports
    "Voblint_Analysis.Interval_Ctx_Entry_State_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Globals and return values across calls under entry-state context sensitivity\<close>

text \<open>
  Call/return acceptance regression for the whole-state entry-state analysis. The local
  unknown carries every VIMP variable, so a declared global crosses a call boundary in
  the same slot a local does: \<open>bump\<close> reads the global \<open>g\<close> the caller wrote before the
  call, writes it, and returns it, and \<open>main\<close> then observes both the returned value and
  the callee's update. Calling \<open>bump\<close> three times, twice with literal arguments and once
  with the global \<open>g\<close> itself as the argument, keeps three entry-state contexts apart, so
  the formal \<open>n\<close> binds exactly in each -- the third call also locks in that a
  global-valued actual argument is evaluated against the caller's real state at the call
  site, not a globals-bottomed one.
\<close>

definition gcall_prog :: imp_prog where
  "gcall_prog = program {
     global g;
     void bump(n) {
       g := g + n;
       return g
     }
     void main() {
       g := 10;
       a := bump(5);
       b := bump(4);
       __voblint_check(a == 15);
       __voblint_check(b == 19);
       __voblint_check(g == 19);
       c := bump(g);
       __voblint_check(c == 38);
       __voblint_check(g == 38)
     }
   }"

abbreviation gcall_gs :: "vname \<Rightarrow> bool" where "gcall_gs \<equiv> declared_global gcall_prog"

definition gcall_cfg :: cfg where
  "gcall_cfg = compile_prog (prog_table gcall_prog) (prog_procs gcall_prog)"

definition gcall_is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "gcall_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars gcall_prog)"

definition gcall_sol ::
  "(pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "gcall_sol = entry_state_sol_prog gcall_gs gcall_prog"

lemma gcall_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c
     (entry_state_eqs_prog gcall_gs gcall_prog)
     (cfg_exit gcall_cfg, []) \<noteq> None"
  by eval

abbreviation gcall_lookup :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "gcall_lookup s x \<equiv> lookup_resolved_st_q s (location_of gcall_gs x)"

definition gcall_ctx_first :: "ivl list" where
  "gcall_ctx_first = entry_state_route gcall_gs gcall_is_bot_pred
                       (entry_state_entered gcall_gs gcall_is_bot_pred
                          (locals (snd gcall_sol (Inl (Statement 4, []))))
                          (CallEdge (Some (STR ''a'')) [STR ''n''] [exp.N 5]))
                       (CallEdge (Some (STR ''a'')) [STR ''n''] [exp.N 5])"

definition gcall_ctx_second :: "ivl list" where
  "gcall_ctx_second = entry_state_route gcall_gs gcall_is_bot_pred
                        (entry_state_entered gcall_gs gcall_is_bot_pred
                           (locals (snd gcall_sol (Inl (Statement 5, []))))
                           (CallEdge (Some (STR ''b'')) [STR ''n''] [exp.N 4]))
                        (CallEdge (Some (STR ''b'')) [STR ''n''] [exp.N 4])"

text \<open>Two call sites, two entry-state contexts: the routed context is the entered value
  of \<open>bump\<close>'s declared formal \<open>n\<close>, so the two activations never share a solver unknown.\<close>

lemma gcall_ctx_first_eq: "gcall_ctx_first = [Ivl (Fin 5) (Fin 5)]"
  by eval

lemma gcall_ctx_second_eq: "gcall_ctx_second = [Ivl (Fin 4) (Fin 4)]"
  by eval

lemma gcall_ctx_distinct: "gcall_ctx_first \<noteq> gcall_ctx_second"
  by eval

definition gcall_ctx_third :: "ivl list" where
  "gcall_ctx_third = entry_state_route gcall_gs gcall_is_bot_pred
                       (entry_state_entered gcall_gs gcall_is_bot_pred
                          (locals (snd gcall_sol (Inl (Statement 9, []))))
                          (CallEdge (Some (STR ''c'')) [STR ''n''] [V (STR ''g'')]))
                       (CallEdge (Some (STR ''c'')) [STR ''n''] [V (STR ''g'')])"

text \<open>A third call site whose actual argument is itself the global \<open>g\<close>, not a literal.
  The routed context is the entered value of that argument, so it locks in that a call
  argument is evaluated against the caller's real state -- not a globals-bottomed one,
  as the pre-migration split local/global packaging would have forced.\<close>

lemma gcall_ctx_third_eq: "gcall_ctx_third = [Ivl (Fin 19) (Fin 19)]"
  by eval

text \<open>Callee entry, first activation: the formal \<open>n\<close> binds to the argument, and the global
  \<open>g\<close> arrives at the value \<open>main\<close> wrote before the call. A split local/global packaging
  would have had to reassemble \<open>g\<close> from a separate solver-global slot to see it here;
  the whole-state local unknown carries it directly.\<close>
lemma gcall_entry_first:
  "(case locals (snd gcall_sol (Inl (FunctionEntry (STR ''bump''), gcall_ctx_first))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (gcall_lookup d (STR ''g''), gcall_lookup d (STR ''n'')))
     = Some (Ivl (Fin 10) (Fin 10), Ivl (Fin 5) (Fin 5))"
  by eval

text \<open>Callee entry, second activation: \<open>g\<close> is the value the first activation wrote and
  returned through, so a callee global write survives the return into the next call.\<close>
lemma gcall_entry_second:
  "(case locals (snd gcall_sol (Inl (FunctionEntry (STR ''bump''), gcall_ctx_second))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (gcall_lookup d (STR ''g''), gcall_lookup d (STR ''n'')))
     = Some (Ivl (Fin 15) (Fin 15), Ivl (Fin 4) (Fin 4))"
  by eval

text \<open>Callee entry, third activation: the global-valued argument \<open>g\<close> is evaluated against
  the caller's real state before entry, so both the routed context and the entered \<open>n\<close>
  carry the caller's live value \<open>19\<close>, not \<open>bot\<close>.\<close>
lemma gcall_entry_third:
  "(case locals (snd gcall_sol (Inl (FunctionEntry (STR ''bump''), gcall_ctx_third))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (gcall_lookup d (STR ''g''), gcall_lookup d (STR ''n'')))
     = Some (Ivl (Fin 19) (Fin 19), Ivl (Fin 19) (Fin 19))"
  by eval

text \<open>Caller state after the first return: the callee's global write is visible, and the
  return-value assignment \<open>a := bump(5)\<close> landed \<open>bump\<close>'s own returned value in \<open>a\<close>.\<close>
lemma gcall_after_first_return:
  "(case locals (snd gcall_sol (Inl (Statement 5, []))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (gcall_lookup d (STR ''g''), gcall_lookup d (STR ''a'')))
     = Some (Ivl (Fin 15) (Fin 15), Ivl (Fin 15) (Fin 15))"
  by eval

text \<open>Same, after the second return.\<close>
lemma gcall_after_second_return:
  "(case locals (snd gcall_sol (Inl (Statement 8, []))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (gcall_lookup d (STR ''g''), gcall_lookup d (STR ''b'')))
     = Some (Ivl (Fin 19) (Fin 19), Ivl (Fin 19) (Fin 19))"
  by eval

text \<open>Caller state after the third return: the callee's global write is visible, and the
  return-value assignment \<open>c := bump(g)\<close> landed \<open>bump\<close>'s own returned value in \<open>c\<close>.\<close>
lemma gcall_after_third_return:
  "(case locals (snd gcall_sol (Inl (Statement 10, []))) of
      Bot \<Rightarrow> None | Lifted d \<Rightarrow> Some (gcall_lookup d (STR ''g''), gcall_lookup d (STR ''c'')))
     = Some (Ivl (Fin 38) (Fin 38), Ivl (Fin 38) (Fin 38))"
  by eval

text \<open>The production check-report pipeline end to end: all five checks are live in every
  context they are covered under and all five decide, so the returned values and the
  surviving global update are both exact at the source level, including the third call's
  global-valued argument and return.\<close>
lemma gcall_analyse_interval_entry_state:
  "analyse_interval_entry_state gcall_prog =
     [(Statement 6, exp.Eq (V (STR ''a'')) (exp.N 15), Decided Check_Proved),
      (Statement 7, exp.Eq (V (STR ''b'')) (exp.N 19), Decided Check_Proved),
      (Statement 8, exp.Eq (V (STR ''g'')) (exp.N 19), Decided Check_Proved),
      (Statement 10, exp.Eq (V (STR ''c'')) (exp.N 38), Decided Check_Proved),
      (Statement 11, exp.Eq (V (STR ''g'')) (exp.N 38), Decided Check_Proved)]"
  by eval

end
