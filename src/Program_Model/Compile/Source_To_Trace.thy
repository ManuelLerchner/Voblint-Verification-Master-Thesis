theory Source_To_Trace
  imports Procedure_Ownership Simulation_Preservation "Voblint_CFG.Activation_Trace_Collect"
begin

section \<open>A source run is an activation trace\<close>

text \<open>
  What the session is for.  A graph configuration is tied to a valid activation trace: the
  activation currently running \<^emph>\<open>is\<close> the trace, and the runtime frame stack is exactly
  its chain of callers.  Each \<^const>\<open>cfg_exec_sem.gcstep\<close> rule lines up with one \<^const>\<open>trace_sem.gvalid_activation_trace\<close>
  constructor, so advancing the graph by an edge extends the trace by a step.

  Composed with the simulation, this turns a run of the source program into a trace, and
  so turns any store the source can reach into a member of the collecting semantics at
  that node.  Those are the statements the soundness session consumes; everything else in
  this session exists to make them true.
\<close>

subsection \<open>The representation invariant\<close>

text \<open>\<open>stack_repr\<close> walks \<^const>\<open>caller_of\<close> in lockstep with the runtime 'v gframe list: each
  \<^type>\<open>gcframe\<close> \<open>(cont, dst, s)\<close> pins the caller activation \<open>caller\<close> --- its frozen store
  \<open>sink_store caller = s\<close> --- and records the concrete \<^const>\<open>calls\<close> edge that spawned the child,
  whose callee \<^term>\<open>FunctionEntry p\<close> equals the child's (path-invariant) entry node.\<close>
inductive stack_repr :: "('v, 'e) gcfg \<Rightarrow> 'v gcframe list \<Rightarrow> 'v gactivation_trace \<Rightarrow> bool" for g where
  empty [intro]: "caller_of t = None \<Longrightarrow> stack_repr g [] t"
| frame [intro]: "caller_of t = Some caller \<Longrightarrow> sink_store caller = s
          \<Longrightarrow> fst (hd (path_of t)) = FunctionEntry p
          \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
          \<Longrightarrow> stack_repr g stk caller
          \<Longrightarrow> stack_repr g ((cont, dst, s) # stk) t"


text \<open>Inversion by the shape of the runtime stack.  A frame's clause recurses on the shorter
  stack, so it stays plain \<open>[elim]\<close>; an empty stack has only one clause and is \<open>[elim!]\<close>.\<close>
inductive_cases stack_repr_NilE [elim!]: "stack_repr g [] t"
inductive_cases stack_repr_ConsE [elim]: "stack_repr g (cf # stk) t"

text \<open>\<open>gactivation_trace_repr\<close> pins a valid activation trace to a located configuration: the trace's sink is the current
  node/store, and its caller chain is the runtime stack.\<close>
locale bridge_sem = simrel_sem ev glob rv conv + collect_sem ev rv conv glob
  for ev :: "'e \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> int" and glob :: "'v \<Rightarrow> bool" and rv :: 'v
    and conv :: "'v option \<Rightarrow> int \<Rightarrow> int"
begin

definition gactivation_trace_repr ::
  "('v, 'e) gcfg \<Rightarrow> ('v \<Rightarrow> int) set \<Rightarrow> 'v gcconf \<Rightarrow> 'v gactivation_trace \<Rightarrow> bool" where
  "gactivation_trace_repr g S cf t = (case cf of (v, s, stk) \<Rightarrow>
     t \<in> gvalid_activation_trace g S \<and> sink_node t = v \<and> sink_store t = s \<and> stack_repr g stk t)"

definition glocated_activation_trace :: "('v, 'e) gcfg \<Rightarrow> ('v \<Rightarrow> int) set \<Rightarrow> 'v gcconf \<Rightarrow> bool" where
  "glocated_activation_trace g S cf = (\<exists>t. gactivation_trace_repr g S cf t)"

end

text \<open>\<open>stack_repr\<close> reads only the top \<^const>\<open>caller_of\<close> and the path-invariant entry node,
  so it transfers across activations sharing both (an \<^const>\<open>extend\<close> appends --- entry
  unchanged --- and a \<^const>\<open>Resume\<close> prepends the same activation's path --- entry
  unchanged).\<close>
lemma stack_repr_cong:
  "stack_repr g stk t1 \<Longrightarrow> caller_of t2 = caller_of t1
   \<Longrightarrow> fst (hd (path_of t2)) = fst (hd (path_of t1)) \<Longrightarrow> stack_repr g stk t2"
  by (cases rule: stack_repr.cases) auto

subsection \<open>The return step\<close>

text \<open>The load-bearing case.  A \<^const>\<open>cfg_exec_sem.gcstep\<close> return pops the top frame; \<open>stack_repr\<close>
  identifies the caller \<open>c\<close> (\<^const>\<open>caller_of\<close> recovers it) and its spawning \<^const>\<open>calls\<close>
  edge, whose callee \<^term>\<open>FunctionEntry q\<close> matches the returning \<^term>\<open>FunctionResult q\<close> by
  \<open>valid_activation_trace_entry_result_eq\<close> --- so the trace composes by \<open>gvalid_activation_trace.ret\<close>, and the combined
  store equals the \<^const>\<open>cfg_exec_sem.gcstep\<close> store.\<close>
context bridge_sem
begin

lemma activation_trace_repr_Return:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and rep: "gactivation_trace_repr (compile_prog \<Pi> ps) S
                  (FunctionResult q, tst, (cont, dst, caller) # stk) t0"
  shows "gactivation_trace_repr (compile_prog \<Pi> ps) S
           (cont, gcombine_collect dst caller tst, stk)
           (Resume (the (caller_of t0)) t0
              (path_of (the (caller_of t0)) @ [(cont, gcombine_collect dst caller tst)]))"
proof -
  let ?g = "compile_prog \<Pi> ps"
  from rep have t0v: "t0 \<in> gvalid_activation_trace (?g) (S)" and sn0: "sink_node t0 = FunctionResult q"
    and ss0: "sink_store t0 = tst"
    and stk0: "stack_repr ?g ((cont, dst, caller) # stk) t0"
    by (auto simp: gactivation_trace_repr_def)
  from stk0 obtain c p pars args where cof: "caller_of t0 = Some c"
    and ssc: "sink_store c = caller" and entryp: "fst (hd (path_of t0)) = FunctionEntry p"
    and edge: "(sink_node c, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ?g"
    and stkc: "stack_repr ?g stk c"
    by (cases rule: stack_repr.cases) auto
  have cvalid: "c \<in> gvalid_activation_trace (?g) (S)" using valid_activation_trace_caller_valid[OF t0v cof] .
  have pq: "p = q" using valid_activation_trace_entry_result_eq[OF wf t0v entryp sn0] .
  have cthe: "the (caller_of t0) = c" using cof by simp
  let ?r = "gcombine_collect dst caller tst"
  let ?t' = "Resume c t0 (path_of c @ [(cont, ?r)])"
  have edge_q: "(sink_node c, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls ?g"
    using edge pq by simp
  have valid': "?t' \<in> gvalid_activation_trace (?g) (S)"
    using gvalid_activation_trace.ret[OF t0v cof sn0 edge_q] ssc ss0 by simp
  have sn': "sink_node ?t' = cont" by (simp add: sink_node_def)
  have ss': "sink_store ?t' = ?r" by (simp add: sink_store_def)
  have entry': "fst (hd (path_of ?t')) = fst (hd (path_of c))"
    using valid_activation_trace_path_nonempty[OF cvalid] by simp
  have stk': "stack_repr ?g stk ?t'"
    using stack_repr_cong[OF stkc, of ?t'] entry' by simp
  show ?thesis
    unfolding cthe using valid' sn' ss' stk' by (simp add: gactivation_trace_repr_def)
qed

end

subsection \<open>The invariant is preserved by located CFG steps\<close>

text \<open>Each \<^const>\<open>cfg_exec_sem.gcstep\<close> rule maps to one \<^const>\<open>trace_sem.gvalid_activation_trace\<close> constructor: intra \<open>\<mapsto>\<close>
  \<^const>\<open>extend\<close>, call \<open>\<mapsto>\<close> \<^const>\<open>Call\<close>, return \<open>\<mapsto>\<close> \<^const>\<open>Resume\<close> (\<open>activation_trace_repr_Return\<close>).\<close>
context bridge_sem
begin

lemma cstep_preserves_activation_trace_repr:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and step: "gcstep (compile_prog \<Pi> ps) cf cf'"
    and rep: "gactivation_trace_repr (compile_prog \<Pi> ps) S cf t"
  shows "\<exists>t'. gactivation_trace_repr (compile_prog \<Pi> ps) S cf' t'"
  using step rep
proof (cases rule: gcstep.cases)
  case (Intra u a v s' s stk')
  let ?g = "compile_prog \<Pi> ps"
  from rep have tv: "t \<in> gvalid_activation_trace (?g) (S)" and sn: "sink_node t = u"
    and ss: "sink_store t = s"
    and str: "stack_repr ?g stk' t"
    using Intra by (auto simp: gactivation_trace_repr_def)
  have e1: "(sink_node t, a, v) \<in> intra ?g" using Intra sn by simp
  have e2: "s' \<in> gedge_step a (sink_store t)" using Intra ss by simp
  have "extend t (v, s') \<in> gvalid_activation_trace (?g) (S)" using gvalid_activation_trace.intra[OF tv e1 e2] .
  moreover have "stack_repr ?g stk' (extend t (v, s'))"
    using stack_repr_cong[OF str] valid_activation_trace_path_nonempty[OF tv] by simp
  ultimately have "gactivation_trace_repr ?g S (v, s', stk') (extend t (v, s'))"
    by (simp add: gactivation_trace_repr_def)
  then show ?thesis using Intra by auto
next
  case (Call u dst pars actuals q cont s stk')
  let ?g = "compile_prog \<Pi> ps"
  from rep have tv: "t \<in> gvalid_activation_trace (?g) (S)" and sn: "sink_node t = u"
    and ss: "sink_store t = s"
    and str: "stack_repr ?g stk' t"
    using Call by (auto simp: gactivation_trace_repr_def)
  have edge: "(sink_node t, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls ?g"
    using Call sn by simp
  let ?child = "Call t [(FunctionEntry q, gcall_enter (CallEdge dst pars actuals) s)]"
  have child_valid: "?child \<in> gvalid_activation_trace (?g) (S)"
    using gvalid_activation_trace.call[OF tv edge] ss by simp
  have "stack_repr ?g ((cont, dst, s) # stk') ?child"
  proof (rule stack_repr.frame)
    show "caller_of ?child = Some t" by simp
    show "sink_store t = s" using ss .
    show "fst (hd (path_of ?child)) = FunctionEntry q" by simp
    show "(sink_node t, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls ?g"
      using edge .
    show "stack_repr ?g stk' t" using str .
  qed
  with child_valid have "gactivation_trace_repr ?g S
      (FunctionEntry q, gcall_enter (CallEdge dst pars actuals) s,
       (cont, dst, s) # stk') ?child"
    by (simp add: gactivation_trace_repr_def sink_node_def sink_store_def)
  then show ?thesis using Call by auto
next
  case (Return q tst cont dst caller stk')
  from rep Return(1)
  have rep': "gactivation_trace_repr (compile_prog \<Pi> ps) S
                (FunctionResult q, tst, (cont, dst, caller) # stk') t" by simp
  from activation_trace_repr_Return[OF wf rep'] show ?thesis using Return(2) by auto
qed

lemma located_activation_trace_entry:
  assumes "s \<in> S"
  shows "glocated_activation_trace g S (cfg_entry g, s, [])"
proof -
  have "gactivation_trace_repr g S (cfg_entry g, s, []) (Root [(cfg_entry g, s)])"
    using assms
    by (auto simp: gactivation_trace_repr_def sink_node_def sink_store_def
      gvalid_activation_trace.root)
  then show ?thesis by (auto simp: glocated_activation_trace_def)
qed

lemma cstep_preserves_located_activation_trace:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and "glocated_activation_trace (compile_prog \<Pi> ps) S cf"
    and "gcstep (compile_prog \<Pi> ps) cf cf'"
  shows "glocated_activation_trace (compile_prog \<Pi> ps) S cf'"
proof -
  from assms(2) obtain t where "gactivation_trace_repr (compile_prog \<Pi> ps) S cf t"
    by (auto simp: glocated_activation_trace_def)
  then obtain t' where "gactivation_trace_repr (compile_prog \<Pi> ps) S cf' t'"
    using cstep_preserves_activation_trace_repr[OF wf assms(3)] by blast
  then show ?thesis by (auto simp: glocated_activation_trace_def)
qed

lemma csteps_preserve_located_activation_trace:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and "glocated_activation_trace (compile_prog \<Pi> ps) S cf"
    and "star (gcstep (compile_prog \<Pi> ps)) cf cf'"
  shows "glocated_activation_trace (compile_prog \<Pi> ps) S cf'"
  using assms(3) assms(2)
proof (induction rule: star.induct)
  case (refl a)
  then show ?case .
next
  case (step a b c)
  have "glocated_activation_trace (compile_prog \<Pi> ps) S b"
    by (rule cstep_preserves_located_activation_trace[OF wf step.prems step.hyps(1)])
  then show ?case by (rule step.IH)
qed

end

subsection \<open>The initial main activation\<close>

text \<open>The program entry \<^term>\<open>FunctionEntry prog_main_name\<close> is an ordinary \<open>csim.Base\<close>
  activation: the distinguished main procedure is declared in \<open>\<Pi>\<close> (\<open>wf_compile_input\<close>), so its
  body fragment is certified by \<open>procs_embedded_compile_prog\<close>.  One \<^term>\<open>EA_Body\<close> edge crosses
  from \<^term>\<open>FunctionEntry prog_main_name\<close> to the body entry \<open>en\<close>, where the \<open>Base\<close> activation
  simulates the source \<open>main_body \<Pi>\<close>.\<close>
context bridge_sem
begin

lemma compile_prog_main_base:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
  obtains en where
    "(FunctionEntry prog_main_name, EA_Body prog_main_name, en) \<in> intra (compile_prog \<Pi> ps)"
    "\<Pi>, compile_prog \<Pi> ps, prog_main_name \<turnstile> (main_body \<Pi>, s, []) \<approx> (en, s, [])"
proof -
  let ?g = "compile_prog \<Pi> ps"
  have pc: "procs_embedded \<Pi> ?g" by (rule procs_embedded_compile_prog[OF wf])
  have main_decl: "\<Pi> prog_main_name = Some (\<lparr>formals = [], body = (main_body \<Pi>)\<rparr>)"
    by (rule wf_compile_inputD(2)[OF wf])
  obtain k m en where
    cacc: "compiled_at \<Pi> ?g prog_main_name (body (\<lparr>formals = [], body = (main_body \<Pi>)\<rparr>)) k m"
      and ctrl: "control_at \<Pi> prog_main_name (body (\<lparr>formals = [], body = (main_body \<Pi>)\<rparr>)) k m
                   (body (\<lparr>formals = [], body = (main_body \<Pi>)\<rparr>)) en"
      and entry: "(FunctionEntry prog_main_name, EA_Body prog_main_name, en) \<in> intra ?g"
    by (rule procs_embedded_activation[OF pc main_decl])
  have bodyeq: "body (\<lparr>formals = [], body = (main_body \<Pi>)\<rparr>) = (main_body \<Pi>)" by simp
  have base: "\<Pi>, ?g, prog_main_name \<turnstile> (main_body \<Pi>, s, []) \<approx> (en, s, [])"
    by (rule csim.Base[OF ctrl[unfolded bodyeq] cacc[unfolded bodyeq]])
  from entry base show ?thesis ..
qed

end

subsection \<open>Top-level structural facts of the invariant\<close>

text \<open>A trace has no caller exactly when its activation is at the top level (empty runtime stack).\<close>
lemma stack_repr_Nil_iff:
  "stack_repr g stk t \<Longrightarrow> (stk = []) = (caller_of t = None)"
  by (cases rule: stack_repr.cases) auto

text \<open>A callerless activation carries exactly the initial context, whatever the policy ---
  the \<open>Root\<close> case never consults \<open>adm\<close>, and the \<open>Resume\<close> case only forwards to the same
  callerless ancestor. No validity is needed: the two clauses involved name no edge.\<close>
context bridge_sem
begin

lemma activation_context_rel_caller_of_None:
  "caller_of t = None
   \<Longrightarrow> gactivation_context_rel adm c\<^sub>0 g t c \<longleftrightarrow> c = c\<^sub>0"
  by (induction t) auto

end

subsection \<open>The source bridge\<close>

text \<open>Composing the initial \<open>csim.Base\<close> with \<open>csim_star\<close> (the source-to-\<^const>\<open>cfg_exec_sem.gcstep\<close>
  simulation) and the located invariant: every source run produces a matching valid
  activation trace at the simulated node.\<close>
context bridge_sem
begin

theorem source_run_has_activation_trace:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and s0: "s0 \<in> S"
    and run: "star (gpstep \<Pi>) (main_body \<Pi>, s0, []) (residual, s, frs)"
  shows "\<exists>v stk t. \<Pi>, compile_prog \<Pi> ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> gactivation_trace_repr (compile_prog \<Pi> ps) S (v, s, stk) t"
proof -
  let ?g = "compile_prog \<Pi> ps"
  have pc: "procs_embedded \<Pi> ?g" by (rule procs_embedded_compile_prog[OF wf])
  have swf: "return_safe (main_body \<Pi>)" by (rule wf_compile_input_return_safe[OF wf])
  obtain en where entry: "(FunctionEntry prog_main_name, EA_Body prog_main_name, en) \<in> intra ?g"
    and base: "\<Pi>, ?g, prog_main_name \<turnstile> (main_body \<Pi>, s0, []) \<approx> (en, s0, [])"
    by (rule compile_prog_main_base[OF wf])
  have loc0:
    "glocated_activation_trace (compile_prog \<Pi> ps) S (FunctionEntry prog_main_name, s0, [])"
    using located_activation_trace_entry[where g = "compile_prog \<Pi> ps", OF s0] by simp
  have step0: "gcstep ?g (FunctionEntry prog_main_name, s0, []) (en, s0, [])"
    by (rule cstep_body[OF entry])
  have loc_en: "glocated_activation_trace ?g S (en, s0, [])"
    by (rule cstep_preserves_located_activation_trace[OF wf loc0 step0])
  from csim_star[OF base pc swf run] obtain cf'
    where run_c: "star (gcstep ?g) (en, s0, []) cf'"
      and sim': "\<Pi>, ?g, prog_main_name \<turnstile> (residual, s, frs) \<approx> cf'"
    by blast
  obtain v s' stk where cf': "cf' = (v, s', stk)" by (cases cf')
  have seq: "s' = s" using csim_store_eq[OF sim'[unfolded cf']] by simp
  have loc_v: "glocated_activation_trace ?g S (v, s, stk)"
    using csteps_preserve_located_activation_trace[OF wf loc_en run_c] cf' seq by simp
  from loc_v obtain t where "gactivation_trace_repr ?g S (v, s, stk) t"
    by (auto simp: glocated_activation_trace_def)
  then show ?thesis using sim' cf' seq by blast
qed

text \<open>The plain projected source bridge: a reachable source store lies in the activation-trace
  collecting \<^const>\<open>ctx_sem.gactivation_collect\<close> at the simulated node, in a context the witness
  trace carries. A relational policy may leave a trace without any context, so the bridge
  asks for one: \<open>has_ctx\<close> is what \<open>gactivation_coverage\<close>'s \<open>TOTAL\<close> buys downstream, and what a
  functional policy has outright (\<open>source_store_in_activation_collect_of_fun\<close>).\<close>
theorem source_store_in_activation_collect:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and s0: "s0 \<in> S"
    and run: "star (gpstep \<Pi>) (main_body \<Pi>, s0, []) (residual, s, frs)"
    and has_ctx: "\<And>t. t \<in> gvalid_activation_trace (compile_prog \<Pi> ps) (S)
                   \<Longrightarrow> \<exists>c. gactivation_context_rel adm c\<^sub>0 (compile_prog \<Pi> ps) t c"
  shows "\<exists>v stk t c. \<Pi>, compile_prog \<Pi> ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> gactivation_trace_repr (compile_prog \<Pi> ps) S (v, s, stk) t
                   \<and> gactivation_context_rel adm c\<^sub>0 (compile_prog \<Pi> ps) t c
                   \<and> s \<in> gactivation_collect adm c\<^sub>0 (compile_prog \<Pi> ps) S v c"
proof -
  let ?g = "compile_prog \<Pi> ps"
  from source_run_has_activation_trace[OF wf s0 run] obtain v stk t
    where sim: "\<Pi>, ?g, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and rep: "gactivation_trace_repr ?g S (v, s, stk) t" by blast
  from rep have tv: "t \<in> gvalid_activation_trace (?g) (S)" and sn: "sink_node t = v"
    and ss: "sink_store t = s"
    by (auto simp: gactivation_trace_repr_def)
  from has_ctx[OF tv] obtain c where tc: "gactivation_context_rel adm c\<^sub>0 ?g t c" by blast
  have "s \<in> gactivation_collect adm c\<^sub>0 ?g S v c"
    using activation_collect_I[OF tv sn tc] ss by simp
  then show ?thesis using sim rep tc by blast
qed

text \<open>A functional policy carries \<^const>\<open>activation_context_of\<close>'s context on every valid activation trace, so it needs no
  context witness.\<close>
corollary source_store_in_activation_collect_of_fun:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and s0: "s0 \<in> S"
    and run: "star (gpstep \<Pi>) (main_body \<Pi>, s0, []) (residual, s, frs)"
  shows "\<exists>v stk t c. \<Pi>, compile_prog \<Pi> ps, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> gactivation_trace_repr (compile_prog \<Pi> ps) S (v, s, stk) t
                   \<and> activation_context_of f c\<^sub>0 t = c
                   \<and> s \<in> gactivation_collect (context_policy_of_fun f) c\<^sub>0 (compile_prog \<Pi> ps) S v c"
proof -
  let ?g = "compile_prog \<Pi> ps"
  from source_run_has_activation_trace[OF wf s0 run] obtain v stk t
    where sim: "\<Pi>, ?g, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and rep: "gactivation_trace_repr ?g S (v, s, stk) t" by blast
  from rep have tv: "t \<in> gvalid_activation_trace (?g) (S)" and sn: "sink_node t = v"
    and ss: "sink_store t = s"
    by (auto simp: gactivation_trace_repr_def)
  have tc:
    "gactivation_context_rel (context_policy_of_fun f) c\<^sub>0 ?g t (activation_context_of f c\<^sub>0 t)"
    by (simp add: activation_context_rel_of_fun_iff[OF tv])
  have "s \<in> gactivation_collect (context_policy_of_fun f) c\<^sub>0 ?g S v
              (activation_context_of f c\<^sub>0 t)"
    using activation_collect_I[OF tv sn tc] ss by simp
  then show ?thesis using sim rep by blast
qed

text \<open>The witness-free top-level result: a store reached with an empty source frame stack lies in
  the activation collecting at the fixed seed context --- no \<^type>\<open>gactivation_trace\<close> witness and no context
  existential. This is the shape a user reads for main-level program points.\<close>
theorem source_toplevel_in_activation_collect:
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
    and s0: "s0 \<in> S"
    and run: "star (gpstep \<Pi>) (main_body \<Pi>, s0, []) (residual, s, [])"
  shows "\<exists>v. \<Pi>, compile_prog \<Pi> ps, prog_main_name \<turnstile> (residual, s, []) \<approx> (v, s, [])
             \<and> s \<in> gactivation_collect adm c\<^sub>0 (compile_prog \<Pi> ps) S v c\<^sub>0"
proof -
  let ?g = "compile_prog \<Pi> ps"
  from source_run_has_activation_trace[OF wf s0 run] obtain v stk t
    where sim: "\<Pi>, ?g, prog_main_name \<turnstile> (residual, s, []) \<approx> (v, s, stk)"
      and rep: "gactivation_trace_repr ?g S (v, s, stk) t" by blast
  have stk0: "stk = []" using sim by blast
  from rep stk0 have tv: "t \<in> gvalid_activation_trace (?g) (S)" and sn: "sink_node t = v"
    and ss: "sink_store t = s" and sr: "stack_repr ?g [] t"
    by (auto simp: gactivation_trace_repr_def)
  have cof: "caller_of t = None" using stack_repr_Nil_iff[OF sr] by simp
  have covered: "gactivation_context_rel adm c\<^sub>0 ?g t c\<^sub>0"
    by (simp add: activation_context_rel_caller_of_None[OF cof])
  have "s \<in> gactivation_collect adm c\<^sub>0 ?g S v c\<^sub>0"
    using activation_collect_I[OF tv sn covered] ss by simp
  then show ?thesis using sim stk0 by blast
qed

end

section \<open>The typed instance\<close>

global_interpretation typed: bridge_sem teval tglobal ReturnVar "tconv \<kappa>"
  rewrites "vimp_sem.gpstep teval tglobal ReturnVar (tconv \<kappa>) = tpstep \<kappa>"
    and "cfg_exec_sem.gcstep teval ReturnVar (tconv \<kappa>) tglobal = tcstep \<kappa>"
    and "collect_sem.gnode_collect teval ReturnVar (tconv \<kappa>) tglobal = tnode_collect \<kappa>"
  for \<kappa> :: kenv
  by (simp_all add: tpstep_def tcstep_def tnode_collect_def)

section \<open>Typed runs reach the typed graph\<close>

text \<open>Every run of the typed program is simulated on the typed graph, and its store is
  the sink of a valid activation trace there. Both are the generic bridge at the typed
  instance; nothing about kinds enters the simulation proof.\<close>

theorem typed_source_run_has_activation_trace:
  assumes wf: "wf_program_compile_input p"
    and s0: "s0 \<in> S"
    and run: "star (tpstep \<kappa> (typed_ptable p ds))
                (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "\<exists>v stk t. typed_ptable p ds, typed_cfg p ds, prog_main_name
                      \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> typed.gactivation_trace_repr \<kappa> (typed_cfg p ds) S (v, s, stk) t"
  unfolding typed_cfg_def
  by (rule typed.source_run_has_activation_trace [OF typed_wf_compile_input [OF wf] s0 run])

text \<open>Hence every store a typed run reaches lies in the typed collecting semantics at the
  node simulating it. This is the inclusion a sound typed analysis result bounds.\<close>

theorem typed_source_reaches_node_collect:
  assumes wf: "wf_program_compile_input p"
    and s0: "s0 \<in> S"
    and run: "star (tpstep \<kappa> (typed_ptable p ds))
                (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. typed_ptable p ds, typed_cfg p ds, prog_main_name
                    \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> tnode_collect \<kappa> (typed_cfg p ds) S v"
proof -
  from typed_source_run_has_activation_trace [OF wf s0 run] obtain v stk t
    where sim: "typed_ptable p ds, typed_cfg p ds, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and rep: "typed.gactivation_trace_repr \<kappa> (typed_cfg p ds) S (v, s, stk) t"
    by blast
  from rep have "s \<in> tnode_collect \<kappa> (typed_cfg p ds) S v"
    by (auto simp: typed.gactivation_trace_repr_def typed.gnode_collect_def)
  with sim show ?thesis by blast
qed

end
