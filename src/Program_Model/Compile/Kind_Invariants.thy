theory Kind_Invariants
  imports Source_To_Trace
begin

section \<open>Typed stores stay typed\<close>

text \<open>
  Every identity other than the return slot holds a value of its kind in every store a
  valid activation trace of the typed graph reaches. Writes to a variable convert to its
  kind (\<^const>\<open>kind_conv\<close>), and a call entry resets locals to \<open>0\<close> and binds each formal to
  its actual converted to the formal's kind. The return slot
  is shared by procedures returning different kinds, so it is excluded: it holds a value
  of the returning procedure's kind, which the destination conversion re-establishes at
  the caller.
\<close>

definition in_kinds :: "kenv \<Rightarrow> store \<Rightarrow> bool" where
  "in_kinds \<kappa> t \<longleftrightarrow> (\<forall>v. v \<noteq> ReturnVar \<longrightarrow> t v \<in> ik_range (\<kappa> v))"

lemma in_kinds_update [simp]:
  "in_kinds \<kappa> t \<Longrightarrow> in_kinds \<kappa> (t(v := ik_norm (\<kappa> v) n))"
  "in_kinds \<kappa> t \<Longrightarrow> in_kinds \<kappa> (t(ReturnVar := n))"
  by (auto simp: in_kinds_def simp del: ik_range_iff)

lemma in_kinds_bind_formals:
  "in_kinds \<kappa> t \<Longrightarrow> (\<And>x n. (x, n) \<in> set (zip xs ns) \<Longrightarrow> n \<in> ik_range (\<kappa> x))
   \<Longrightarrow> in_kinds \<kappa> (bind_formals xs ns t)"
proof (induction xs arbitrary: ns t)
  case (Cons x xs)
  then show ?case
    by (cases ns) (auto simp: in_kinds_def simp del: ik_range_iff)
qed simp

lemma in_kinds_enter_state: "in_kinds \<kappa> t \<Longrightarrow> in_kinds \<kappa> (enter_state is_global t)"
  by (auto simp: in_kinds_def enter_state_def enter_frame_def simp del: ik_range_iff)

lemma in_kinds_combine_env:
  "in_kinds \<kappa> s \<Longrightarrow> in_kinds \<kappa> t \<Longrightarrow> in_kinds \<kappa> (combine_env g s t)"
  by (auto simp: in_kinds_def simp del: ik_range_iff)

subsection \<open>Graphs with typed calls\<close>

text \<open>A call edge passes typed actuals when each actual is well-typed, does not read the
  return slot, and has the kind of the formal it binds.\<close>

definition calls_in_kinds :: "kenv \<Rightarrow> (var_id, exp) gcfg \<Rightarrow> bool" where
  "calls_in_kinds \<kappa> g \<longleftrightarrow>
     (\<forall>u dst pars es v w. (u, CallEdge dst pars es, v, w) \<in> calls g \<longrightarrow>
        list_all (\<lambda>e. wt_exp \<kappa> e \<and> ReturnVar \<notin> exp_vars e) es \<and> args_ok \<kappa> pars es)"

lemma zip_map2_self: "zip xs (map2 f xs ys) = map (\<lambda>(x, y). (x, f x y)) (zip xs ys)"
proof (induction xs arbitrary: ys)
  case (Cons x xs) then show ?case by (cases ys) simp_all
qed simp

lemma in_kinds_call_enter:
  assumes t: "in_kinds \<kappa> t"
  shows "in_kinds \<kappa> (vimp.gcall_enter \<kappa> (CallEdge dst pars es) t)"
proof -
  have "n \<in> ik_range (\<kappa> x)"
    if "(x, n) \<in> set (zip pars (map2 (\<lambda>x. kind_conv \<kappa> (Some x)) pars (map (\<lambda>e. eval e t) es)))"
    for x n
    using that by (auto simp: zip_map2_self)
  then show ?thesis
    unfolding vimp.call_enter_CallEdge
    by (rule in_kinds_bind_formals[OF in_kinds_enter_state[OF t]])
qed

text \<open>The suspended activations below a trace. A return resumes one of them, so the
  invariant is carried for all of them at once.\<close>

primrec callers :: "'v gactivation_trace \<Rightarrow> 'v gactivation_trace set" where
  "callers (Root _) = {}"
| "callers (Call c _) = insert c (callers c)"
| "callers (Resume c _ _) = callers c"

lemma callers_extend [simp]: "callers (extend t x) = callers t"
  by (cases t) simp_all

lemma caller_of_callers: "caller_of t = Some c \<Longrightarrow> insert c (callers c) \<subseteq> callers t"
  by (induction t) auto

lemma valid_activation_trace_callers_in_kinds:
  assumes vimp: "calls_in_kinds \<kappa> g" and S: "\<And>s. s \<in> S \<Longrightarrow> in_kinds \<kappa> s"
    and t: "t \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
  shows "in_kinds \<kappa> (sink_store t) \<and> (\<forall>c \<in> callers t. in_kinds \<kappa> (sink_store c))"
  using t
proof (induction t rule: vimp.gvalid_activation_trace.induct)
  case (root s)
  then show ?case by (simp add: S)
next
  case (intra t a v s')
  then show ?case
    by (cases a) (auto simp: in_kinds_def split: option.splits if_splits simp del: ik_range_iff)
next
  case (call caller dst pars args p cont)
  then show ?case by (simp add: in_kinds_call_enter)
next
  case (ret callee caller p dst pars args cont)
  from ret.IH caller_of_callers [OF ret.hyps(2)]
  have "in_kinds \<kappa> (sink_store caller)" "\<forall>c \<in> callers caller. in_kinds \<kappa> (sink_store c)"
    and callee: "in_kinds \<kappa> (sink_store callee)"
    by auto
  moreover have "in_kinds \<kappa> (vimp.gcombine_collect \<kappa> dst (sink_store caller) (sink_store callee))"
    using calculation
    by (cases dst) (auto simp: vimp.gcombine_collect_def in_kinds_combine_env)
  ultimately show ?case by (simp add: sink_store_def)
qed

theorem valid_activation_trace_in_kinds:
  assumes "calls_in_kinds \<kappa> g" and "\<And>s. s \<in> S \<Longrightarrow> in_kinds \<kappa> s"
    and "t \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
  shows "in_kinds \<kappa> (sink_store t)"
  using valid_activation_trace_callers_in_kinds [OF assms] by blast

theorem node_collect_in_kinds:
  assumes "calls_in_kinds \<kappa> g" and "\<And>s. s \<in> S \<Longrightarrow> in_kinds \<kappa> s"
    and "s \<in> \<C>\<^bsub>\<kappa>,g,S\<^esub> v"
  shows "in_kinds \<kappa> s"
  using assms(3) valid_activation_trace_in_kinds [OF assms(1,2)]
  by (auto simp: vimp.gnode_collect_def)

subsection \<open>The typed graph has typed calls\<close>

text \<open>Every call edge the compiler emits comes from a \<^const>\<open>Call\<close> in a compiled body,
  with that call's destination and actuals and the callee's formals.\<close>

fun com_calls :: "('a, 'v, 'e) gcom \<Rightarrow> ('v option \<times> pname \<times> 'e list) set" where
  "com_calls (gcom.Call _ dst q es) = {(dst, q, es)}"
| "com_calls (Seq c1 c2) = com_calls c1 \<union> com_calls c2"
| "com_calls (If _ _ c1 c2) = com_calls c1 \<union> com_calls c2"
| "com_calls (While _ _ c) = com_calls c"
| "com_calls _ = {}"

lemma compile_calls_from:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, CallEdge dst pars es, v, w) \<in> K
   \<Longrightarrow> \<exists>q. (dst, q, es) \<in> com_calls c \<and> pars = call_formals \<Pi> q"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] Seq.prems(2) K by auto
next
  case (If i b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] If.prems(2) K by auto
next
  case (While i b c)
  from While.prems(1) obtain n1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and K: "K = K1"
    by (rule compile_WhileE)
  show ?case using While.IH[OF c1] While.prems(2) K by auto
qed (auto split: option.splits simp del: call_formals_def)

lemma compile_prog_calls_from:
  assumes main: "\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>"
    and e: "(u, CallEdge dst pars es, v, w) \<in> calls (compile_prog \<Pi> ps)"
  shows "\<exists>r d q. \<Pi> r = Some d \<and> (dst, q, es) \<in> com_calls (body d) \<and> pars = call_formals \<Pi> q"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = main_body \<Pi>\<rparr> n1
                  = (n2, Emain, Kmain)"
    and KC: "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  from e KC consider (P) "(u, CallEdge dst pars es, v, w) \<in> Kprocs"
    | (M) "(u, CallEdge dst pars es, v, w) \<in> Kmain"
    by auto
  then show ?thesis
  proof cases
    case P
    from compile_procs_calls_origin [OF procs P] obtain r d m m' Ep Kp where
        d: "\<Pi> r = Some d" and cp: "compile_proc \<Pi> r d m = (m', Ep, Kp)"
      and eK: "(u, CallEdge dst pars es, v, w) \<in> Kp"
      by blast
    from cp obtain Eb where
        cb: "compile \<Pi> r (body d) (Statement (m + csize (body d))) m
               = (m + csize (body d), Statement m, Eb, Kp)"
      by (rule compile_procE)
    from compile_calls_from [OF cb eK] d show ?thesis by blast
  next
    case M
    from mainc obtain Eb where
        cb: "compile \<Pi> prog_main_name (main_body \<Pi>) (Statement (n1 + csize (main_body \<Pi>))) n1
               = (n1 + csize (main_body \<Pi>), Statement n1, Eb, Kmain)"
      by (rule compile_procE) simp
    from compile_calls_from [OF cb M] main show ?thesis
      by (metis gproc_decl.select_convs(2))
  qed
qed

lemma init_stores_in_kinds: "t \<in> init_stores \<kappa> \<Longrightarrow> in_kinds \<kappa> t"
  by (auto simp: init_stores_def in_kinds_def all_in_kinds_def simp del: ik_range_iff)

subsection \<open>Runs of the elaborated program stay within their kinds\<close>

text \<open>Elaboration puts a conversion on every argument, so the call edges of the elaborated
  graph pass well-typed arguments to formals of the right kinds.\<close>

lemma com_calls_elab_com:
  "com_calls (elab_com \<G> fm \<kappa> r c)
     = (\<lambda>(dst, q, es). (map_option (resolve_var \<G> r) dst, q,
                         elab_args (resolve_var \<G> r) \<kappa> (map (resolve_var \<G> q) (fm q)) es))
       ` com_calls c"
  by (induction c) (auto simp: image_Un)

lemma call_formals_elab_ptable:
  "call_formals (elab_ptable p ds) q = map (resolve_var (declared_global p) q) (prog_formals p q)"
  by (cases "prog_table p q") (auto simp: elab_ptable_def prog_formals_def)

theorem calls_in_kinds_elab_cfg:
  assumes wf: "wf_program_compile_input p"
  shows "calls_in_kinds (kenv_of ds) (elab_cfg p ds)"
  unfolding calls_in_kinds_def
proof (intro allI impI)
  fix u dst pars es v w
  assume e: "(u, CallEdge dst pars es, v, w) \<in> calls (elab_cfg p ds)"
  from wf have src: "wf_source_program (declared_global p) (prog_table p)"
    by (simp add: gwf_compile_input_def)
  from compile_prog_calls_from [OF elab_ptable_main(1) [OF src] e [unfolded elab_cfg_def]]
  obtain r d q where d: "elab_ptable p ds r = Some d" and c: "(dst, q, es) \<in> com_calls (body d)"
    and pars: "pars = call_formals (elab_ptable p ds) q"
    by blast
  let ?\<rho> = "resolve_var (declared_global p) r"
  let ?fs = "map (resolve_var (declared_global p) q) (prog_formals p q)"
  from d c obtain es0 where es: "es = elab_args ?\<rho> (kenv_of ds) ?fs es0"
    by (auto simp: elab_ptable_def com_calls_elab_com)
  have "list_all (\<lambda>e. wt_exp (kenv_of ds) e \<and> ReturnVar \<notin> exp_vars e) es"
    using elab_args_wt [of "kenv_of ds" ?\<rho> ?fs es0] exp_vars_elab_args
      [of _ ?\<rho> "kenv_of ds" ?fs es0]
      ReturnVar_notin_range_resolve_var [of "declared_global p" r]
    unfolding es list_all_iff by blast
  moreover have "args_ok (kenv_of ds) pars es"
    using elab_args_wt [of "kenv_of ds" ?\<rho> ?fs es0]
    by (simp add: es pars call_formals_elab_ptable del: call_formals_def)
  ultimately show "list_all (\<lambda>e. wt_exp (kenv_of ds) e \<and> ReturnVar \<notin> exp_vars e) es
                     \<and> args_ok (kenv_of ds) pars es" ..
qed

text \<open>Hence a run of the elaborated program that starts from a store within its kinds keeps
  every identity other than the return slot at a value of its kind, through assignments,
  declarations, calls, returns and recursion. The premise on the initial store is explicit;
  the initial stores of the soundness theorems satisfy it (@{thm init_stores_in_kinds}).\<close>

theorem run_in_kinds:
  assumes wf: "wf_program_compile_input p"
    and s0: "in_kinds (kenv_of ds) s0"
    and run:
      "(kenv_of ds),(elab_ptable p ds) \<turnstile> (main_body (elab_ptable p ds), s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "in_kinds (kenv_of ds) s"
proof -
  from source_reaches_node_collect [OF wf _ run, of "{s0}"]
  obtain v where "s \<in> \<C>\<^bsub>kenv_of ds,elab_cfg p ds,{s0}\<^esub> v" by blast
  then show ?thesis
    using node_collect_in_kinds [OF calls_in_kinds_elab_cfg [OF wf]] s0 by blast
qed

corollary run_from_init_in_kinds:
  assumes "wf_program_compile_input p"
    and "s0 \<in> init_stores (kenv_of ds)"
    and
      "(kenv_of ds),(elab_ptable p ds) \<turnstile> (main_body (elab_ptable p ds), s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "in_kinds (kenv_of ds) s"
  using run_in_kinds [OF assms(1) init_stores_in_kinds [OF assms(2)] assms(3)] .

end
