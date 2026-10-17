theory Source_Activation_Sound
  imports "Voblint_Framework.Activation_Backbone" "Voblint_Compile.Source_To_Trace"
begin

section \<open>End-to-end source-level activation soundness\<close>

text \<open>
  A completed run of a compiled source program is collected at the result of its root
  activation. That a reachable store is collected at the node the simulation locates it at
  is \<open>source_reaches_node_collect\<close> in \<^theory>\<open>Voblint_Compile.Source_To_Trace\<close>.
\<close>

subsection \<open>Completed runs reach a procedure result\<close>

text \<open>
  A source run that has completed at the top level (residual \<^const>\<open>SKIP\<close>, empty frame stack)
  is collected at the \<^const>\<open>FunctionResult\<close> of the activation it completed.  Two structural
  facts do the work, both from the CFG layer: the located node reaches its fragment exit along
  store-preserving intra flow (\<open>compile_control_at_SKIP_exit_path\<close>), and \<^const>\<open>compiled_at\<close>
  supplies the fall-through \<^term>\<open>EA_Ret None p\<close> edge from that exit into
  \<^term>\<open>FunctionResult p\<close>.

  The witness is kept: the completing activation is the \<^emph>\<open>root\<close> one (empty frame stack, so
  \<^const>\<open>caller_of\<close> is \<^const>\<open>None\<close>), which is what pins its procedure --- see
  \<open>source_completes_node_collect_exit\<close>.  Projecting into \<^const>\<open>node_collect\<close> first would lose
  that: the collection at a \<^const>\<open>FunctionResult\<close> deliberately merges every activation of
  that procedure.
\<close>

theorem source_completes_valid_activation_trace_result:
  assumes wf: "gwf_compile_input vars ReturnVar is_global Pi ps"
    and s0: "s0 \<in> S"
    and run: "\<kappa>,Pi \<turnstile> (main_body Pi, s0, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP (), s, [])"
  shows "\<exists>t p. t \<in> \<T>\<^bsub>\<kappa>,compile_prog Pi ps,S\<^esub>
               \<and> caller_of t = None
               \<and> fst (hd (path_of t)) = cfg_entry (compile_prog Pi ps)
               \<and> sink_node t = FunctionResult p
               \<and> sink_store t = s"
proof -
  let ?g = "compile_prog Pi ps"
  from compile_prog_run_has_activation_trace[OF wf s0 run]
  obtain v stk t where sim: "Pi, ?g, prog_main_name \<turnstile> (SKIP (), s, []) \<approx> (v, s, stk)"
    and rep: "activation_trace_repr \<kappa> ?g S (v, s, stk) t" by blast
  have stk0: "stk = []" using sim by blast
  from rep stk0 have tv: "t \<in> \<T>\<^bsub>\<kappa>,?g,S\<^esub>" and sn: "sink_node t = v"
    and ss: "sink_store t = s" and sr: "stack_repr ?g [] t"
    by (auto simp: activation_trace_repr_def)
  have cof: "caller_of t = None" using stack_repr_Nil_iff[OF sr] by simp
  have hd_t: "fst (hd (path_of t)) = cfg_entry ?g"
    by (rule valid_activation_trace_caller_None_entry[OF tv cof])
  \<comment> \<open>the located node of a completed activation is its procedure's result\<close>
  from sim obtain p body_p k n where
    ca: "control_at Pi p body_p k n (SKIP ()) v" and cat: "compiled_at Pi ?g p body_p k n"
    by blast
  from cat obtain n' en E K where
    cc: "compile Pi p body_p k n = (n', en, E, K)" and Esub: "E \<subseteq> intra ?g"
    and ret: "(k, EA_Ret None p, FunctionResult p) \<in> intra ?g"
    by blast
  \<comment> \<open>the whole extension is intra flow, so it stays inside this same (root) activation\<close>
  have path_to_ret: "star (cfg_intra_step \<kappa> ?g) (sink_node t, sink_store t) (FunctionResult p, s)"
  proof -
    have a: "star (cfg_intra_step \<kappa> ?g) (sink_node t, sink_store t) (k, s)"
      using compile_control_at_SKIP_exit_path[OF ca cc Esub] sn ss by simp
    have b: "star (cfg_intra_step \<kappa> ?g) (k, s) (FunctionResult p, s)"
      by (rule intra_path_single[OF ret]) simp
    from a b show ?thesis by (rule star_trans)

  qed
  from valid_activation_trace_intra_path_extend[OF path_to_ret tv]
  obtain t' where tvar_id: "t' \<in> \<T>\<^bsub>\<kappa>,?g,S\<^esub>" and t'n:
    "sink_node t' = FunctionResult p"
    and t's: "sink_store t' = s" and t'c: "caller_of t' = caller_of t"
    and t'h: "fst (hd (path_of t')) = fst (hd (path_of t))" by blast
  show ?thesis
  proof (intro exI conjI)
    show "t' \<in> \<T>\<^bsub>\<kappa>,?g,S\<^esub>" by (rule tvar_id)
    show "caller_of t' = None" using t'c cof by simp
    show "fst (hd (path_of t')) = cfg_entry ?g" using t'h hd_t by simp
    show "sink_node t' = FunctionResult p" by (rule t'n)
    show "sink_store t' = s" by (rule t's)
  qed
qed

text \<open>Whole-program completion.  The completing activation is the root one, so it entered at
  \<^term>\<open>FunctionEntry prog_main_name\<close>; activation procedure locality
  (\<open>valid_activation_trace_entry_result_eq\<close>) then forces its result node to be
  \<^term>\<open>FunctionResult prog_main_name\<close> \<open>= cfg_exit\<close>.  No assumption about the
  \<^emph>\<open>number\<close> of declared procedures is needed: a program may call as many as it likes.\<close>

corollary source_completes_node_collect_exit:
  assumes wf: "gwf_compile_input vars ReturnVar is_global Pi ps"
    and s0: "s0 \<in> S"
    and run: "\<kappa>,Pi \<turnstile> (main_body Pi, s0, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP (), s, [])"
  shows "s \<in> \<C>\<^bsub>\<kappa>,compile_prog Pi ps,S\<^esub>
              (cfg_exit (compile_prog Pi ps))"
proof -
  let ?g = "compile_prog Pi ps"
  from source_completes_valid_activation_trace_result[OF wf s0 run]
  obtain t p where tv: "t \<in> \<T>\<^bsub>\<kappa>,?g,S\<^esub>" and hd_t:
    "fst (hd (path_of t)) = cfg_entry ?g"
    and sn: "sink_node t = FunctionResult p" and ss: "sink_store t = s" by blast
  have "fst (hd (path_of t)) = FunctionEntry prog_main_name"
    using hd_t by (simp add: compile_prog_def Let_def split: prod.splits)
  from valid_activation_trace_entry_result_eq[OF wf tv this sn] have "prog_main_name = p" .
  with sn ss tv show ?thesis
    using node_collect_I by fastforce
qed

end
