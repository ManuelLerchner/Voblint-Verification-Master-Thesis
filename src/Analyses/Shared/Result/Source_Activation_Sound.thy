theory Source_Activation_Sound
  imports "Voblint_Framework.Activation_Backbone" "Voblint_Compile.Source_To_Trace"
begin

section \<open>End-to-end source-level activation soundness\<close>

text \<open>
  A reachable store of a compiled source program is collected at the node the simulation
  locates it at, and a completed run is collected at the result of its root activation.
\<close>

subsection \<open>Monovariant source bridge into the trace collecting\<close>

text \<open>
  The context-forgetting specialisation projects the activation collector at trivial routing
  directly to \<^const>\<open>collect_sem.gnode_collect\<close> via \<open>activation_collect_le_node_collect\<close>.
\<close>

context bridge_sem
begin

theorem source_reaches_node_collect:
  assumes wf: "gwf_compile_input vars rv glob Pi ps"
    and s0: "s0 \<in> S"
    and run: "star (gpstep Pi) (main_body Pi, s0, []) (residual, s, frs)"
  shows "\<exists>v stk. Pi, compile_prog Pi ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> gnode_collect (compile_prog Pi ps) (S) v"
proof -
  let ?g = "compile_prog Pi ps"
  from source_store_in_activation_collect_of_fun
         [where f = "\<lambda>_ _ _. ()" and c\<^sub>0 = "()",
          OF wf s0 run]
  obtain v stk and t :: "'v gactivation_trace" and c where m:
    "Pi, compile_prog Pi ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
    and "activation_context_of (\<lambda>_ _ _. ()) () t = c"
    and mem: "s \<in> gactivation_collect (context_policy_of_fun (\<lambda>_ _ _. ())) () ?g S v c"
    by blast
  have "s \<in> gnode_collect (?g) (S) v"
    using mem by (rule subsetD[OF activation_collect_le_node_collect])
  then show ?thesis using m by blast
qed

end

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
  \<open>source_completes_node_collect_exit\<close>.  Projecting into \<^const>\<open>collect_sem.gnode_collect\<close> first would lose
  that: the collection at a \<^const>\<open>FunctionResult\<close> deliberately merges every activation of
  that procedure.
\<close>

context bridge_sem
begin

theorem source_completes_valid_activation_trace_result:
  assumes wf: "gwf_compile_input vars rv glob Pi ps"
    and s0: "s0 \<in> S"
    and run: "star (gpstep Pi) (main_body Pi, s0, []) (SKIP (), s, [])"
  shows "\<exists>t p. t \<in> gvalid_activation_trace (compile_prog Pi ps) (S)
               \<and> caller_of t = None
               \<and> fst (hd (path_of t)) = cfg_entry (compile_prog Pi ps)
               \<and> sink_node t = FunctionResult p
               \<and> sink_store t = s"
proof -
  let ?g = "compile_prog Pi ps"
  from source_run_has_activation_trace[OF wf s0 run]
  obtain v stk t where sim: "Pi, ?g, prog_main_name \<turnstile> (SKIP (), s, []) \<approx> (v, s, stk)"
    and rep: "gactivation_trace_repr ?g S (v, s, stk) t" by blast
  have stk0: "stk = []" using sim by blast
  from rep stk0 have tv: "t \<in> gvalid_activation_trace (?g) (S)" and sn: "sink_node t = v"
    and ss: "sink_store t = s" and sr: "stack_repr ?g [] t"
    by (auto simp: gactivation_trace_repr_def)
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
  have path_to_ret: "star (gcfg_intra_step ?g) (sink_node t, sink_store t) (FunctionResult p, s)"
  proof -
    have a: "star (gcfg_intra_step ?g) (sink_node t, sink_store t) (k, s)"
      using compile_control_at_SKIP_exit_path[OF ca cc Esub] sn ss by simp
    have b: "star (gcfg_intra_step ?g) (k, s) (FunctionResult p, s)"
      by (rule intra_path_single[OF ret]) simp
    from a b show ?thesis by (rule star_trans)

  qed
  from valid_activation_trace_intra_path_extend[OF path_to_ret tv]
  obtain t' where t'v: "t' \<in> gvalid_activation_trace (?g) (S)" and t'n: "sink_node t' = FunctionResult p"
    and t's: "sink_store t' = s" and t'c: "caller_of t' = caller_of t"
    and t'h: "fst (hd (path_of t')) = fst (hd (path_of t))" by blast
  show ?thesis
  proof (intro exI conjI)
    show "t' \<in> gvalid_activation_trace (?g) (S)" by (rule t'v)
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
  assumes wf: "gwf_compile_input vars rv glob Pi ps"
    and s0: "s0 \<in> S"
    and run: "star (gpstep Pi) (main_body Pi, s0, []) (SKIP (), s, [])"
  shows "s \<in> gnode_collect (compile_prog Pi ps) (S)
              (cfg_exit (compile_prog Pi ps))"
proof -
  let ?g = "compile_prog Pi ps"
  from source_completes_valid_activation_trace_result[OF wf s0 run]
  obtain t p where tv: "t \<in> gvalid_activation_trace (?g) (S)" and hd_t: "fst (hd (path_of t)) = cfg_entry ?g"
    and sn: "sink_node t = FunctionResult p" and ss: "sink_store t = s" by blast
  have "fst (hd (path_of t)) = FunctionEntry prog_main_name"
    using hd_t by (simp add: compile_prog_def Let_def split: prod.splits)
  from valid_activation_trace_entry_result_eq[OF wf tv this sn] have "prog_main_name = p" .
  with sn ss tv show ?thesis
    using node_collect_I by fastforce
qed

end

end
