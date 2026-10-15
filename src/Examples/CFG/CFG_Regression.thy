theory CFG_Regression
  imports "Voblint_Compile.Source_To_Trace" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed graph\<close>

text \<open>The typed graph carries elaborated expressions on its edges. A variable is read
  at its own kind, with no conversion around the read; the only conversions are the ones
  C performs, here the promotion of a \<^const>\<open>U8\<close> operand to \<^const>\<open>I32\<close> and the
  conversion of the sum back to \<^const>\<open>U8\<close> at the assignment. The call result reaches
  \<open>y\<close> through the return slot, converted when the callee's frame is popped.\<close>

definition ret_prog :: imp_prog where
  "ret_prog = program { fun f() { return 300; } fun main() { x = 250; x = x + 10; y = f(); } }"

definition ret_kinds :: kind_decls where
  "ret_kinds = [(ScopedId prog_main_name (STR ''x''), U8), (ReturnId (STR ''f''), U8)]"

abbreviation x_id :: var_id where "x_id \<equiv> ScopedId (STR ''main'') (STR ''x'')"

lemma elab_cfg_edges:
  "cfg_intra_list (elab_cfg ret_prog ret_kinds) =
     [(Statement 0, EA_Ret (Some (TN U8 300)) (STR ''f''), FunctionResult (STR ''f'')),
      (Statement 1, EA_Ret None (STR ''f''), FunctionResult (STR ''f'')),
      (Statement 2, EA_Assign x_id (TN U8 250), Statement 3),
      (Statement 3, EA_Assign x_id (TCast U8 (TArith I32 AAdd (TCast I32 (TVar U8 x_id)) (TN I32 10))),
       Statement 4),
      (Statement 5, EA_Ret None (STR ''main''), FunctionResult (STR ''main'')),
      (FunctionEntry (STR ''f''), EA_Body (STR ''f''), Statement 0),
      (FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 2)]"
  "cfg_calls_list (elab_cfg ret_prog ret_kinds) =
     [(Statement 4, CallEdge (Some (ScopedId (STR ''main'') (STR ''y''))) [] [],
       FunctionEntry (STR ''f''), Statement 5)]"
  by eval+

text \<open>The program is a well-formed compiler input, so its typed runs are simulated on
  this graph.\<close>

lemma ret_prog_elab_wf:
  "gwf_compile_input exp_vars ReturnVar is_global (elab_ptable ret_prog ret_kinds) (prog_procs ret_prog)"
proof (rule elab_wf_compile_input)
  show "wf_program_compile_input ret_prog"
    unfolding gwf_compile_input_def
    by (auto simp: wf_compile_input_simps ret_prog_def split: if_splits)
qed

end
