theory Example_Interval_Call_String_Generic_Parity
  imports
    "Voblint_Analysis.Interval_Ctx_Call_String_Sound"
    Example_Interval_DG_CallString_K2
begin

section \<open>Parity: the runtime-\<open>k\<close> generic pipeline matches the hand-built K1/K2 instances\<close>

text \<open>
  \<^const>\<open>cs_call_string_sol_prog\<close> at a runtime \<open>k\<close> against
  \<^const>\<open>nest_program\<close> is the same equation system \<open>nest_1_eqs\<close>/\<open>nest_2_eqs\<close>
  solve -- same \<^const>\<open>ectx_spec\<close>, same \<^const>\<open>cs_route\<close>, same seeds -- read
  through the runtime-parameterized surface instead of two hand-instantiated
  theories. The solved values themselves are pinned in the regression corpus,
  where a shared callee is merged at depth one, separated at depth two, and
  unchanged at depth three because \<^const>\<open>nest_program\<close>'s deepest call chain
  is only two calls long.

  What stays here is the one fact the corpus cannot state. A fixture asserts
  what a single run computes; it cannot compare two runs. The theorem below is
  that comparison: at every point the two contexts exercise, the \<open>k = 2\<close>
  answer is strictly below the \<open>k = 1\<close> answer in the domain's own order, out
  of one equation system parameterised by \<open>k\<close> rather than two independently
  instantiated ones.

  At \<open>k = 1\<close> the merged context is widened and its upper bound leaves the
  declared kind's range, so every later conversion to \<^const>\<open>I32\<close> has an
  operand it cannot represent and answers \<^term>\<open>ivl_top_of I32\<close>. That is
  what the strict inequality is measured against: sound, and strictly coarser
  than the separated contexts.
\<close>

theorem cs_generic_k2_strictly_more_precise_than_k1:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs (STR ''main'') nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))) (STR ''p'')
     < nest_lookup
         (locals (snd (cs_call_string_sol_prog 1 nest_gs (STR ''main'') nest_program)
                    (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')"
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs (STR ''main'') nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))) (STR ''p'')
     < nest_lookup
         (locals (snd (cs_call_string_sol_prog 1 nest_gs (STR ''main'') nest_program)
                    (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')"
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs (STR ''main'') nest_program)
                (Inl (Statement 6, [])))) (STR ''x'')
     < nest_lookup
         (locals (snd (cs_call_string_sol_prog 1 nest_gs (STR ''main'') nest_program)
                    (Inl (Statement 6, [])))) (STR ''x'')"
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs (STR ''main'') nest_program)
                (Inl (Statement 7, [])))) (STR ''y'')
     < nest_lookup
         (locals (snd (cs_call_string_sol_prog 1 nest_gs (STR ''main'') nest_program)
                    (Inl (Statement 7, [])))) (STR ''y'')"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval+

end
