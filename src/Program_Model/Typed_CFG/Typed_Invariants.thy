theory Typed_Invariants
  imports Typed_CFG
begin

section \<open>Typed stores stay typed\<close>

text \<open>
  Every identity other than the return slot holds a value of its kind in every store a
  valid activation trace of the typed graph reaches. Writes to a variable convert to its
  kind (\<^const>\<open>tconv\<close>), and a call entry resets locals to \<open>0\<close> and binds each formal to
  an actual that elaboration has already converted to the formal's kind. The return slot
  is shared by procedures returning different kinds, so it is excluded: it holds a value
  of the returning procedure's kind, which the destination conversion re-establishes at
  the caller.
\<close>

definition tstyped :: "kenv \<Rightarrow> tstore \<Rightarrow> bool" where
  "tstyped \<kappa> t \<longleftrightarrow> (\<forall>v. v \<noteq> ReturnVar \<longrightarrow> t v \<in> ik_range (\<kappa> v))"

lemma tstyped_styped: "tstyped \<kappa> t \<longleftrightarrow> styped \<kappa> (t(ReturnVar := 0))"
  by (auto simp: tstyped_def styped_def simp del: ik_range_iff)

lemma tstyped_update [simp]:
  "tstyped \<kappa> t \<Longrightarrow> tstyped \<kappa> (t(v := ik_norm (\<kappa> v) n))"
  "tstyped \<kappa> t \<Longrightarrow> tstyped \<kappa> (t(ReturnVar := n))"
  by (auto simp: tstyped_def simp del: ik_range_iff)

lemma teval_cong: "(\<And>v. v \<in> tvars e \<Longrightarrow> s v = t v) \<Longrightarrow> teval e s = teval e t"
  by (induction e) auto

lemma teval_tstyped_in_range:
  assumes "tstyped \<kappa> t" and "wt_texp \<kappa> e" and "ReturnVar \<notin> tvars e"
  shows "teval e t \<in> ik_range (texp_kind e)"
proof -
  have "teval e t = teval e (t(ReturnVar := 0))"
    using assms(3) by (intro teval_cong) auto
  then show ?thesis
    using teval_in_range [OF assms(2)] assms(1) by (simp add: tstyped_styped)
qed

lemma tstyped_bind_formals:
  "tstyped \<kappa> t \<Longrightarrow> (\<And>x n. (x, n) \<in> set (zip xs ns) \<Longrightarrow> n \<in> ik_range (\<kappa> x))
   \<Longrightarrow> tstyped \<kappa> (bind_formals xs ns t)"
proof (induction xs arbitrary: ns t)
  case (Cons x xs)
  then show ?case
    by (cases ns) (auto simp: tstyped_def simp del: ik_range_iff)
qed simp

lemma tstyped_enter_state: "tstyped \<kappa> t \<Longrightarrow> tstyped \<kappa> (enter_state tglobal t)"
  by (auto simp: tstyped_def enter_state_def enter_frame_def simp del: ik_range_iff)

lemma tstyped_combine_env:
  "tstyped \<kappa> s \<Longrightarrow> tstyped \<kappa> t \<Longrightarrow> tstyped \<kappa> (combine_env g s t)"
  by (auto simp: tstyped_def simp del: ik_range_iff)

subsection \<open>Graphs with typed calls\<close>

text \<open>A call edge passes typed actuals when each actual is well-typed, does not read the
  return slot, and has the kind of the formal it binds.\<close>

definition calls_typed :: "kenv \<Rightarrow> (var_id, texp) gcfg \<Rightarrow> bool" where
  "calls_typed \<kappa> g \<longleftrightarrow>
     (\<forall>u dst pars es v w. (u, CallEdge dst pars es, v, w) \<in> calls g \<longrightarrow>
        list_all (\<lambda>e. wt_texp \<kappa> e \<and> ReturnVar \<notin> tvars e) es \<and> args_ok \<kappa> pars es)"

lemma args_ok_zip:
  "args_ok \<kappa> xs es \<Longrightarrow> (x, e) \<in> set (zip xs es) \<Longrightarrow> texp_kind e = \<kappa> x"
  by (induction \<kappa> xs es rule: args_ok.induct) auto

lemma tstyped_call_enter:
  assumes typed: "calls_typed \<kappa> g" and edge: "(u, CallEdge dst pars es, v, w) \<in> calls g"
    and t: "tstyped \<kappa> t"
  shows "tstyped \<kappa> (typed.gcall_enter (CallEdge dst pars es) t)"
proof -
  from typed edge have es: "list_all (\<lambda>e. wt_texp \<kappa> e \<and> ReturnVar \<notin> tvars e) es"
    and ok: "args_ok \<kappa> pars es"
    unfolding calls_typed_def by blast+
  have "n \<in> ik_range (\<kappa> x)" if "(x, n) \<in> set (zip pars (map (\<lambda>e. teval e t) es))" for x n
  proof -
    from that obtain e where xe: "(x, e) \<in> set (zip pars es)" and n: "n = teval e t"
      by (auto simp: zip_map2)
    then have "e \<in> set es" by (auto dest: set_zip_rightD)
    with es have "wt_texp \<kappa> e" "ReturnVar \<notin> tvars e" by (auto simp: list_all_iff)
    then have "teval e t \<in> ik_range (texp_kind e)" by (intro teval_tstyped_in_range [OF t])
    then show ?thesis using args_ok_zip [OF ok xe] n by simp
  qed
  then show ?thesis
    by (simp add: typed.call_enter_CallEdge tstyped_bind_formals tstyped_enter_state t)
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

lemma valid_activation_trace_callers_tstyped:
  assumes typed: "calls_typed \<kappa> g" and S: "\<And>s. s \<in> S \<Longrightarrow> tstyped \<kappa> s"
    and t: "t \<in> typed.gvalid_activation_trace \<kappa> g S"
  shows "tstyped \<kappa> (sink_store t) \<and> (\<forall>c \<in> callers t. tstyped \<kappa> (sink_store c))"
  using t
proof (induction t rule: typed.gvalid_activation_trace.induct)
  case (root s)
  then show ?case by (simp add: S)
next
  case (intra t a v s')
  then show ?case
    by (cases a) (auto simp: tstyped_def split: option.splits if_splits simp del: ik_range_iff)
next
  case (call caller dst pars args p cont)
  then show ?case by (simp add: tstyped_call_enter [OF typed])
next
  case (ret callee caller p dst pars args cont)
  from ret.IH caller_of_callers [OF ret.hyps(2)]
  have "tstyped \<kappa> (sink_store caller)" "\<forall>c \<in> callers caller. tstyped \<kappa> (sink_store c)"
    and callee: "tstyped \<kappa> (sink_store callee)"
    by auto
  moreover have "tstyped \<kappa> (typed.gcombine_collect \<kappa> dst (sink_store caller) (sink_store callee))"
    using calculation
    by (cases dst) (auto simp: typed.gcombine_collect_def tstyped_combine_env)
  ultimately show ?case by (simp add: sink_store_def)
qed

theorem valid_activation_trace_tstyped:
  assumes "calls_typed \<kappa> g" and "\<And>s. s \<in> S \<Longrightarrow> tstyped \<kappa> s"
    and "t \<in> typed.gvalid_activation_trace \<kappa> g S"
  shows "tstyped \<kappa> (sink_store t)"
  using valid_activation_trace_callers_tstyped [OF assms] by blast

theorem tnode_collect_tstyped:
  assumes "calls_typed \<kappa> g" and "\<And>s. s \<in> S \<Longrightarrow> tstyped \<kappa> s"
    and "s \<in> tnode_collect \<kappa> g S v"
  shows "tstyped \<kappa> s"
  using assms(3) valid_activation_trace_tstyped [OF assms(1,2)]
  by (auto simp: typed.gnode_collect_def)


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

lemma com_calls_elab_com:
  "com_calls (elab_com \<G> fm \<kappa> r c)
     = (\<lambda>(dst, q, es). (map_option (resolve_var \<G> r) dst, q,
                         elab_args (resolve_var \<G> r) \<kappa> (map (resolve_var \<G> q) (fm q)) es))
       ` com_calls c"
  by (induction c) (auto simp: image_Un)

lemma call_formals_typed_ptable:
  "call_formals (typed_ptable p ds) q = map (resolve_var (declared_global p) q) (prog_formals p q)"
  by (cases "prog_table p q") (auto simp: typed_ptable_def prog_formals_def Code.abort_def)

theorem calls_typed_typed_cfg:
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
  shows "calls_typed (kenv_of ds) (typed_cfg p ds)"
  unfolding calls_typed_def
proof (intro allI impI)
  fix u dst pars es v w
  assume e: "(u, CallEdge dst pars es, v, w) \<in> calls (typed_cfg p ds)"
  from wf have src: "wf_source_program (declared_global p) (prog_table p)"
    by (simp add: gwf_compile_input_def)
  from compile_prog_calls_from [OF typed_ptable_main(1) [OF src] e [unfolded typed_cfg_def]]
  obtain r d q where d: "typed_ptable p ds r = Some d" and c: "(dst, q, es) \<in> com_calls (body d)"
    and pars: "pars = call_formals (typed_ptable p ds) q"
    by blast
  let ?\<rho> = "resolve_var (declared_global p) r"
  let ?fs = "map (resolve_var (declared_global p) q) (prog_formals p q)"
  from d c obtain es0 where es: "es = elab_args ?\<rho> (kenv_of ds) ?fs es0"
    by (auto simp: typed_ptable_def com_calls_elab_com)
  have "list_all (\<lambda>e. wt_texp (kenv_of ds) e \<and> ReturnVar \<notin> tvars e) es"
    using elab_args_wt [of "kenv_of ds" ?\<rho> ?fs es0] tvars_elab_args [of _ ?\<rho> "kenv_of ds" ?fs es0]
      ReturnVar_notin_range_resolve_var [of "declared_global p" r]
    unfolding es list_all_iff by blast
  moreover have "args_ok (kenv_of ds) pars es"
    using elab_args_wt [of "kenv_of ds" ?\<rho> ?fs es0] by (simp add: es pars call_formals_typed_ptable del: call_formals_def)
  ultimately show "list_all (\<lambda>e. wt_texp (kenv_of ds) e \<and> ReturnVar \<notin> tvars e) es
                     \<and> args_ok (kenv_of ds) pars es" ..
qed


text \<open>Hence a typed run keeps its store typed: every identity other than the return slot
  holds a value of its kind at every point of the run.\<close>

theorem typed_run_tstyped:
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and s0: "tstyped (kenv_of ds) s0"
    and run: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "tstyped (kenv_of ds) s"
proof -
  from typed_source_reaches_node_collect [OF wf _ run, of "{s0}"]
  obtain v where "s \<in> tnode_collect (kenv_of ds) (typed_cfg p ds) {s0} v" by blast
  then show ?thesis
    using tnode_collect_tstyped [OF calls_typed_typed_cfg [OF wf]] s0 by blast
qed

lemma tinit_stores_tstyped: "t \<in> tinit_stores \<kappa> \<Longrightarrow> tstyped \<kappa> t"
  by (auto simp: tinit_stores_def tstyped_def styped_def simp del: ik_range_iff)

end
