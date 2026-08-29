theory Example_Interval_Call_String_Generic_Parity
  imports
    "Voblint_Analysis.Interval_Ctx_Call_String_Sound"
    Example_Interval_DG_CallString_K2
begin

section \<open>Parity: the runtime-\<open>k\<close> generic pipeline matches the hand-built K1/K2 instances\<close>

text \<open>
  \<^const>\<open>cs_call_string_sol_prog\<close> at \<open>k = 1\<close>/\<open>k = 2\<close> against \<^const>\<open>nest_program\<close>
  is the same equation system \<open>nest_1_eqs\<close>/\<open>nest_2_eqs\<close> solve --- same
  \<^const>\<open>ectx_spec\<close>, same \<^const>\<open>cs_route\<close>, same seeds -- read through the new
  runtime-parameterized surface instead of two hand-instantiated theories.
  These lemmas witness that the generic pipeline reproduces every solved value
  \<open>Example_Interval_DG_CallString_K1\<close>/\<open>_K2\<close> pin, at the identical query
  points, with no separate proof of definitional identity between the two
  equation systems needed: both compute the same numbers.
\<close>

subsection \<open>\<open>k = 1\<close>: the merged-context widening witness\<close>

lemma cs_generic_k1_g_entry_merged:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 1 nest_gs nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')
   = Ivl (Fin 3) PlusInf"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k1_g_result_merged:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 1 nest_gs nest_program)
                (Inl (FunctionResult (STR ''g''), [Statement 2])))) (STR ''#ret'')
   = Ivl (Fin 6) PlusInf"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k1_x_after_first_return:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 1 nest_gs nest_program)
                (Inl (Statement 6, [])))) (STR ''x'')
   = Ivl (Fin 6) PlusInf"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k1_y_after_second_return:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 1 nest_gs nest_program)
                (Inl (Statement 7, [])))) (STR ''y'')
   = Ivl (Fin 6) PlusInf"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

subsection \<open>\<open>k = 2\<close>: the two activations of \<open>g\<close> stay exact and separate\<close>

lemma cs_generic_k2_g_entry_first:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))) (STR ''p'')
   = Ivl (Fin 3) (Fin 3)"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k2_g_entry_second:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))) (STR ''p'')
   = Ivl (Fin 10) (Fin 10)"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k2_g_result_first:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (FunctionResult (STR ''g''), [Statement 2, Statement 5])))) (STR ''#ret'')
   = Ivl (Fin 6) (Fin 6)"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k2_g_result_second:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (FunctionResult (STR ''g''), [Statement 2, Statement 6])))) (STR ''#ret'')
   = Ivl (Fin 20) (Fin 20)"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k2_x_after_first_return:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (Statement 6, [])))) (STR ''x'')
   = Ivl (Fin 6) (Fin 6)"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k2_y_after_second_return:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (Statement 7, [])))) (STR ''y'')
   = Ivl (Fin 20) (Fin 20)"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

text \<open>
  The precision-separation witness itself, restated against the generic
  runtime-\<open>k\<close> interface: \<open>k = 2\<close> is strictly more precise than \<open>k = 1\<close> at
  every point the two contexts \<^const>\<open>nest_program\<close> exercises, exactly
  reproducing \<open>nest_k2_strictly_more_precise_than_k1\<close> without a second,
  independently-instantiated equation system.
\<close>

theorem cs_generic_k2_strictly_more_precise_than_k1:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))) (STR ''p'')
     < nest_lookup
         (locals (snd (cs_call_string_sol_prog 1 nest_gs nest_program)
                    (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')"
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))) (STR ''p'')
     < nest_lookup
         (locals (snd (cs_call_string_sol_prog 1 nest_gs nest_program)
                    (Inl (FunctionEntry (STR ''g''), [Statement 2])))) (STR ''p'')"
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (Statement 6, [])))) (STR ''x'')
     < nest_lookup
         (locals (snd (cs_call_string_sol_prog 1 nest_gs nest_program)
                    (Inl (Statement 6, [])))) (STR ''x'')"
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 2 nest_gs nest_program)
                (Inl (Statement 7, [])))) (STR ''y'')
     < nest_lookup
         (locals (snd (cs_call_string_sol_prog 1 nest_gs nest_program)
                    (Inl (Statement 7, [])))) (STR ''y'')"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval+

subsection \<open>Runtime \<open>k\<close> beyond the historically hardcoded cases\<close>

text \<open>
  \<open>k = 3\<close> was never a K-file: this is the same generic interface, applied to
  a bound neither \<open>Example_Interval_DG_CallString_K1\<close> nor \<open>_K2\<close> ever
  hardcodes, terminating and solving exactly as \<open>k = 1\<close>/\<open>k = 2\<close> do. Since
  \<^const>\<open>nest_program\<close>'s deepest call chain is only two calls deep, \<open>k = 3\<close>
  cannot separate anything \<open>k = 2\<close> does not already -- the two \<open>g\<close> call
  strings never exceed length two -- so this witnesses genuine runtime
  parameterization, not a third hidden dispatch table entry.
\<close>

lemma cs_generic_k3_g_entry_first:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 3 nest_gs nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 5])))) (STR ''p'')
   = Ivl (Fin 3) (Fin 3)"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

lemma cs_generic_k3_g_entry_second:
  "nest_lookup
     (locals (snd (cs_call_string_sol_prog 3 nest_gs nest_program)
                (Inl (FunctionEntry (STR ''g''), [Statement 2, Statement 6])))) (STR ''p'')
   = Ivl (Fin 10) (Fin 10)"
  unfolding cs_call_string_sol_prog_def cs_call_string_sol_def cs_call_string_eqs_def
  by eval

end
