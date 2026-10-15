theory Elaborated_Compilation
  imports Source_To_Trace
begin

section \<open>Elaborated compilation: every residual names its CFG node\<close>

text \<open>Elaboration annotates each statement with the nodes the compiler emits for it.
  On an elaborated program the forward simulation is functional: the node a source
  configuration is related to is read off its residual (\<open>csim_point_compile_prog\<close>).\<close>

subsection \<open>Erasure\<close>

definition erase :: "('a, 'v, 'e) gcom \<Rightarrow> (unit, 'v, 'e) gcom" where
  "erase = map_gcom (\<lambda>_. ()) id id"

definition erase_decl :: "('a, 'v, 'e) gproc_decl \<Rightarrow> (unit, 'v, 'e) gproc_decl" where
  "erase_decl d = \<lparr>formals = formals d, body = erase (body d)\<rparr>"

definition erase_pt :: "('a, 'v, 'e) gptable \<Rightarrow> (unit, 'v, 'e) gptable" where
  "erase_pt \<Pi> = map_option erase_decl \<circ> \<Pi>"

lemma erase_simps [simp]:
  "erase (SKIP i) = SKIP ()"
  "erase (Assign i x a) = Assign () x a"
  "erase (Check i l b) = Check () l b"
  "erase (Seq c1 c2) = Seq (erase c1) (erase c2)"
  "erase (If i b c1 c2) = If () b (erase c1) (erase c2)"
  "erase (While i b c) = While () b (erase c)"
  "erase (gcom.Call i dst q args) = gcom.Call () dst q args"
  "erase (gcom.Return i e) = gcom.Return () e"
  "erase (Restore i) = Restore ()"
  "erase (Unwind i) = Unwind ()"
  by (simp_all add: erase_def option.map_id)

lemma erase_decl_simps [simp]:
  "formals (erase_decl d) = formals d" "body (erase_decl d) = erase (body d)"
  by (simp_all add: erase_decl_def)

lemma is_Restore_erase [simp]: "is_Restore (erase c) = is_Restore c"
  by (cases c) simp_all


subsection \<open>Locations and elaboration\<close>

text \<open>Compiler metadata for one statement occurrence: the node the statement starts at, the
  node control reaches once it completes, and the result node a return through it reaches.\<close>
record loc =
  loc_here :: cfg_node
  loc_done :: cfg_node
  loc_exit :: cfg_node

definition stmt_loc :: "pname \<Rightarrow> cfg_node \<Rightarrow> nat \<Rightarrow> loc" where
  "stmt_loc p k n = \<lparr>loc_here = Statement n, loc_done = k, loc_exit = FunctionResult p\<rparr>"

text \<open>Offsets are threaded exactly as \<^const>\<open>compile\<close> threads them.  A source \<^const>\<open>SKIP\<close>
  is its own node; a \<^const>\<open>SKIP\<close> branch of an \<^const>\<open>If\<close> emits no edge, so it is done at
  the continuation.  A call's exit is the callee's result node.\<close>
fun elab :: "pname \<Rightarrow> cfg_node \<Rightarrow> nat \<Rightarrow> ('a, 'v, 'e) gcom \<Rightarrow> (loc, 'v, 'e) gcom" where
  "elab p k n (SKIP _) = SKIP (stmt_loc p (Statement n) n)"
| "elab p k n (Assign _ x a) = Assign (stmt_loc p k n) x a"
| "elab p k n (VIMP_Proc.gcom.Check _ l b) = VIMP_Proc.gcom.Check (stmt_loc p k n) l b"
| "elab p k n (Seq c1 c2) =
     Seq (elab p (Statement (n + csize c1)) n c1) (elab p k (n + csize c1) c2)"
| "elab p k n (If _ b c1 c2) =
     If (stmt_loc p k n) b
       (if is_SKIP c1 then SKIP (stmt_loc p k (Suc n)) else elab p k (Suc n) c1)
       (if is_SKIP c2 then SKIP (stmt_loc p k (Suc n + csize c1))
        else elab p k (Suc n + csize c1) c2)"
| "elab p k n (While _ b c) = While (stmt_loc p k n) b (elab p (Statement n) (Suc n) c)"
| "elab p k n (gcom.Call _ dst q args) =
     gcom.Call ((stmt_loc p k n)\<lparr>loc_exit := FunctionResult q\<rparr>) dst q args"
| "elab p k n (gcom.Return _ e) = gcom.Return (stmt_loc p k n) e"
| "elab p k n (Restore _) = Restore (stmt_loc p k n)"
| "elab p k n (Unwind _) = Unwind (stmt_loc p k n)"

lemma csize_elab [simp]: "csize (elab p k n c) = csize c"
  by (induction p k n c rule: elab.induct) (simp_all, safe, simp_all)

lemma elab_eq_SKIP: "elab p k n c = SKIP a \<longleftrightarrow> (\<exists>i. c = SKIP i \<and> stmt_loc p (Statement n) n = a)"
  by (cases c) simp_all


lemma elab_source_not_Restore [simp]: "source_com c \<Longrightarrow> elab p k n c \<noteq> Restore a"
  by (cases c) simp_all

lemma csize_elab_branch [simp]:
  "csize (if is_SKIP c then SKIP x else elab p k n c) = csize c"
  by (cases "is_SKIP c") (auto simp del: csize.simps(5))

text \<open>The node a residual occupies.  A \<^const>\<open>Seq\<close> whose head is unwinding into a
  \<^const>\<open>Restore\<close> sits at the call's exit, the callee's result node.\<close>
fun point :: "(loc, 'v, 'e) gcom \<Rightarrow> cfg_node" where
  "point (SKIP a) = loc_done a"
| "point (Seq c1 c2) = (if is_Restore c2 \<and> unwinding c1 then loc_exit (stmt_ann c2) else point c1)"
| "point (Restore a) = loc_exit a"
| "point (Unwind a) = loc_exit a"
| "point c = loc_here (stmt_ann c)"

text \<open>On an elaborated fragment the residual alone fixes the node: \<^const>\<open>point\<close> reads it
  off the residual's annotation.\<close>
lemma control_at_point:
  assumes "control_at \<Pi> p c0 k n r v" "c0 = elab p k n c" "source_com c"
  shows "v = point r"
  using assms
proof (induction arbitrary: c rule: control_at.induct)
  case (SeqLeft c1 n r v c2 k)
  from SeqLeft.prems(1) obtain d1 d2 where c: "c = Seq d1 d2"
    by (cases c) simp_all
  with SeqLeft.prems have "v = point r"
    by (intro SeqLeft.IH[of d1]) simp_all
  with SeqLeft.prems c show ?case by simp
next
  case (SeqRight c2 k n c1 r v)
  from SeqRight.prems(1) obtain d1 d2 where c: "c = Seq d1 d2"
    by (cases c) simp_all
  with SeqRight.prems show ?case
    by (intro SeqRight.IH[of d2]) simp_all
next
  case (IfLeft c1 k n r v i b c2)
  from IfLeft.prems(1) obtain j d1 d2 where c: "c = If j b d1 d2"
    by (cases c) simp_all
  with IfLeft.prems IfLeft.hyps(2) have "\<not> is_SKIP d1" by auto
  with IfLeft.prems c show ?case
    by (intro IfLeft.IH[of d1]) simp_all
next
  case (IfRight c2 k n c1 r v i b)
  from IfRight.prems(1) obtain j d1 d2 where c: "c = If j b d1 d2"
    by (cases c) simp_all
  with IfRight.prems IfRight.hyps(2) have "\<not> is_SKIP d2" by auto
  moreover from IfRight.prems c have "csize c1 = csize d1"
    using csize_elab_branch[of d1 "stmt_loc p k (Suc n)" p k "Suc n"] by simp
  ultimately show ?case using IfRight.prems c
    by (intro IfRight.IH[of d2]) simp_all
next
  case (IfDone c1 j c2 i b k n)
  from IfDone.prems(1) obtain i' d1 d2 where c: "c = If i' b d1 d2"
    by (cases c) simp_all
  with IfDone.hyps IfDone.prems show ?case
    by (cases "is_SKIP d1"; cases "is_SKIP d2") (auto simp: elab_eq_SKIP stmt_loc_def)
next
  case (WhileBody c n r v i b k)
  from WhileBody.prems(1) obtain j d where c: "c = While j b d"
    by (cases c) simp_all
  with WhileBody.prems have "v = point r"
    by (intro WhileBody.IH[of d]) simp_all
  then show ?case by simp
next
  case (Skip i n k) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (Assign i x a k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (AssignDone i x a k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (Check i l b k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (CheckDone i l b k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (IfHead i b c1 c2 k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (WhileHead i b c' k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (WhileUnfolded i b c' k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (WhileDone i b c' k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (CallHead i dst q actuals k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (CallDone i dst q actuals k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
next
  case (ReturnHead i e k n) then show ?case by (cases c) (simp_all add: stmt_loc_def)
qed

subsection \<open>The simulation determines the node\<close>

text \<open>Every call annotation exits at its callee's result node.  Elaboration establishes it and
  every residual \<^const>\<open>control_at\<close> reaches inherits it.\<close>
fun calls_ok :: "(loc, 'v, 'e) gcom \<Rightarrow> bool" where
  "calls_ok (Seq c1 c2) = (calls_ok c1 \<and> calls_ok c2)"
| "calls_ok (If _ b c1 c2) = (calls_ok c1 \<and> calls_ok c2)"
| "calls_ok (While _ b c) = calls_ok c"
| "calls_ok (gcom.Call a dst q args) = (loc_exit a = FunctionResult q)"
| "calls_ok _ = True"

lemma calls_ok_elab: "calls_ok (elab p k n c)"
  by (induction p k n c rule: elab.induct) simp_all

lemma control_at_calls_ok: "control_at \<Pi> p c0 k n r v \<Longrightarrow> calls_ok c0 \<Longrightarrow> calls_ok r"
  by (induction rule: control_at.induct) simp_all

lemma calls_ok_seq_after: "calls_ok (seq_after c afters) \<Longrightarrow> calls_ok c"
  by (induction afters arbitrary: c) fastforce+

lemma point_seq_after [simp]:
  "\<not> unwinding c \<Longrightarrow> point (seq_after c afters) = point c \<and> \<not> unwinding (seq_after c afters)"
  by (induction afters arbitrary: c) simp_all

lemma pop_ready_point:
  "pop_ready w \<Longrightarrow> pop_ann w = Some i \<Longrightarrow> point w = loc_exit i \<and> \<not> unwinding w"
  by (cases w rule: pop_ready.cases) simp_all

text \<open>Every compiled body is the elaboration of a source body at its own offsets.\<close>
definition located :: "(loc, 'v, 'e) gptable \<Rightarrow> ('v, 'e) gcfg \<Rightarrow> bool" where
  "located \<Pi> g \<longleftrightarrow>
     (\<forall>p body k n. compiled_at \<Pi> g p body k n \<longrightarrow>
        (\<exists>c :: (unit, 'v, 'e) gcom. source_com c \<and> body = elab p k n c))"

lemma locatedE:
  assumes "located \<Pi> g" "compiled_at \<Pi> g p b k n"
  obtains c :: "(unit, 'v, 'e) gcom" where "source_com c" "b = elab p k n c"
  using assms unfolding located_def by blast

text \<open>On a located program the simulation names its node, \<^term>\<open>point c\<close>; that the residual is
  not unwinding is carried along for the \<^const>\<open>Restore\<close> case.\<close>
lemma csim_point:
  "\<Pi>, g, p \<turnstile> x \<approx> y \<Longrightarrow> located \<Pi> g \<Longrightarrow> fst y = point (fst x) \<and> \<not> unwinding (fst x)"
proof (induction rule: csim.induct)
  case (Base p body_p k n c v s)
  from Base.prems Base.hyps(2) obtain c0 :: "(unit, _, _) gcom" where c0: "source_com c0" "body_p = elab p k n c0"
    by (rule locatedE)
  have "v = point c"
    by (rule control_at_point[OF Base.hyps(1) c0(2) c0(1)])
  moreover have "\<not> unwinding c"
    using control_at_not_returning[OF Base.hyps(1)] unwinding_is_returning by blast
  ultimately show ?case by simp
next
  case (Nested q inner s frs v stk pc body_pc kc nc i afters cont dst args site caller)
  from Nested.IH[OF Nested.prems] show ?case by simp
next
  case (Returning w i pc body_pc kc nc afters cont dst q args site callee caller)
  from Returning.prems Returning.hyps(5) obtain c0 :: "(unit, _, _) gcom" where c0: "body_pc = elab pc kc nc c0"
    by (rule locatedE)
  have "calls_ok (seq_after (gcom.Call i dst q args) afters)"
    by (rule control_at_calls_ok[OF Returning.hyps(4)]) (simp add: c0 calls_ok_elab)
  then have "loc_exit i = FunctionResult q"
    using calls_ok_seq_after by fastforce
  with pop_ready_point[OF Returning.hyps(1,2)] show ?case by simp
qed


subsection \<open>Compilation ignores annotations\<close>

text \<open>The compiler reads neither the annotations nor anything of the table but the formals,
  so two programs with the same erasure compile to the same graph.\<close>

lemma csize_erase [simp]: "csize (erase c) = csize c"
  by (induction c) simp_all

lemma erase_eq_SKIP [simp]: "erase c = SKIP i \<longleftrightarrow> is_SKIP c"
  by (cases c) simp_all

lemma compile_erase:
  assumes "call_formals \<Pi> = call_formals \<Pi>'"
  shows "compile \<Pi> p c k n = compile \<Pi>' p (erase c) k n"
proof (induction c arbitrary: k n)
  case (Call i dst q args)
  have "call_formals \<Pi> q = call_formals \<Pi>' q" using assms by (rule fun_cong)
  then show ?case by (simp only: erase_simps compile.simps)
qed (simp_all del: call_formals_def)

lemma call_formals_erase_pt: "call_formals (erase_pt \<Pi>) = call_formals \<Pi>"
  by (rule ext) (simp add: erase_pt_def erase_decl_def split: option.split)

text \<open>Two programs with the same erasure compile to the same graph.\<close>
lemma compile_erase_cong:
  assumes "erase_pt \<Pi> = erase_pt \<Pi>'" "erase c = erase c'"
  shows "compile \<Pi> p c k n = compile \<Pi>' p c' k n"
proof -
  have "compile \<Pi> p c k n = compile (erase_pt \<Pi>) p (erase c) k n"
    by (rule compile_erase) (simp add: call_formals_erase_pt)
  also have "\<dots> = compile (erase_pt \<Pi>') p (erase c') k n"
    using assms by simp
  also have "\<dots> = compile \<Pi>' p c' k n"
    by (rule compile_erase[symmetric]) (simp add: call_formals_erase_pt)
  finally show ?thesis .
qed

lemma compile_proc_erase_cong:
  assumes "erase_pt \<Pi> = erase_pt \<Pi>'" "erase_decl d = erase_decl d'"
  shows "compile_proc \<Pi> p d n = compile_proc \<Pi>' p d' n"
proof -
  have b: "erase (body d) = erase (body d')"
    using assms(2) by (simp add: erase_decl_def)
  then have "csize (body d) = csize (body d')"
    by (metis csize_erase)
  with b show ?thesis
    by (simp add: compile_proc_def compile_erase_cong[OF assms(1) b])
qed

lemma compile_procs_erase_cong:
  assumes "erase_pt \<Pi> = erase_pt \<Pi>'"
  shows "compile_procs \<Pi> ps n = compile_procs \<Pi>' ps n"
proof (induction ps arbitrary: n)
  case (Cons q qs)
  have "map_option erase_decl (\<Pi> q) = map_option erase_decl (\<Pi>' q)"
    using fun_cong[OF assms, of q] by (simp add: erase_pt_def)
  then show ?case
    by (cases "\<Pi> q"; cases "\<Pi>' q") (simp_all add: Cons.IH compile_proc_erase_cong[OF assms])
qed simp

lemma main_body_erase_cong:
  assumes "erase_pt \<Pi> = erase_pt \<Pi>'"
  shows "erase (main_body \<Pi>) = erase (main_body \<Pi>')"
proof -
  have "map_option erase_decl (\<Pi> prog_main_name) = map_option erase_decl (\<Pi>' prog_main_name)"
    using fun_cong[OF assms, of prog_main_name] by (simp add: erase_pt_def)
  then show ?thesis
    by (cases "\<Pi> prog_main_name"; cases "\<Pi>' prog_main_name")
       (simp_all add: main_body_def erase_decl_def)
qed

lemma compile_prog_erase_cong:
  assumes "erase_pt \<Pi> = erase_pt \<Pi>'"
  shows "compile_prog \<Pi> ps = compile_prog \<Pi>' ps"
proof -
  have "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = main_body \<Pi>\<rparr> n
      = compile_proc \<Pi>' prog_main_name \<lparr>formals = [], body = main_body \<Pi>'\<rparr> n" for n
    using main_body_erase_cong[OF assms]
    by (intro compile_proc_erase_cong[OF assms]) (simp add: erase_decl_def)
  then show ?thesis
    by (simp add: compile_prog_def compile_procs_erase_cong[OF assms])
qed

subsection \<open>Elaborating a procedure table\<close>

text \<open>A table is elaborated procedure by procedure, each body at the offset at which
  \<^const>\<open>compile_procs\<close> places it, and \<open>main\<close> after all of them.\<close>

lemma erase_elab [simp]: "erase (elab p k n c) = erase c"
  by (induction p k n c rule: elab.induct) (simp_all, safe, simp_all)

definition elab_decl :: "pname \<Rightarrow> nat \<Rightarrow> ('a, 'v, 'e) gproc_decl \<Rightarrow> (loc, 'v, 'e) gproc_decl"
  where
  "elab_decl p n d =
     \<lparr>formals = formals d, body = elab p (Statement (n + csize (body d))) n (body d)\<rparr>"

lemma erase_decl_elab_decl [simp]: "erase_decl (elab_decl p n d) = erase_decl d"
  by (simp add: elab_decl_def erase_decl_def)

text \<open>Each procedure is elaborated at the offset \<^const>\<open>compile_procs\<close> places it at.\<close>
fun elab_procs :: "('a, 'v, 'e) gptable \<Rightarrow> pname list \<Rightarrow> nat \<Rightarrow> (loc, 'v, 'e) gptable" where
  "elab_procs \<Pi> [] n = Map.empty"
| "elab_procs \<Pi> (p # ps) n =
     (case \<Pi> p of
        None \<Rightarrow> elab_procs \<Pi> ps n
      | Some d \<Rightarrow> (elab_procs \<Pi> ps (Suc (n + csize (body d))))(p \<mapsto> elab_decl p n d))"

definition elab_pt :: "('a, 'v, 'e) gptable \<Rightarrow> pname list \<Rightarrow> (loc, 'v, 'e) gptable" where
  "elab_pt \<Pi> ps =
     (elab_procs \<Pi> ps 0)(prog_main_name :=
        map_option (elab_decl prog_main_name (fst (compile_procs \<Pi> ps 0))) (\<Pi> prog_main_name))"

lemma elab_procs_None: "\<Pi> p = None \<Longrightarrow> elab_procs \<Pi> ps n p = None"
  by (induction ps arbitrary: n) (auto split: option.split)

lemma elab_procs_erase:
  "map_option erase_decl (elab_procs \<Pi> ps n p)
     = (if p \<in> set ps then map_option erase_decl (\<Pi> p) else None)"
  by (induction ps arbitrary: n) (auto simp: elab_procs_None split: option.split)

lemma erase_pt_elab_pt:
  assumes "set ps = {p. \<Pi> p \<noteq> None} - {prog_main_name}"
  shows "erase_pt (elab_pt \<Pi> ps) = erase_pt \<Pi>"
proof
  fix p
  show "erase_pt (elab_pt \<Pi> ps) p = erase_pt \<Pi> p"
    using assms elab_procs_erase[of \<Pi> ps 0 p]
    by (cases "\<Pi> p") (auto simp: erase_pt_def elab_pt_def option.map_comp comp_def)
qed

subsection \<open>The compiler output is located\<close>

text \<open>The elaborated table satisfies \<^const>\<open>located\<close> for its own compiled graph, which
  is what makes the simulation functional on it.\<close>


lemma elab_procs_entry:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" "elab_procs \<Pi> ps n p = Some d'"
  shows "\<exists>d m. \<Pi> p = Some d \<and> d' = elab_decl p m d \<and> (FunctionEntry p, EA_Body p, Statement m) \<in> E"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems show ?thesis by (intro Cons.IH) simp_all
  next
    case (Some dq)
    obtain n1 Eq Kq where cq: "compile_proc \<Pi> q dq n = (n1, Eq, Kq)"
      by (rule prod_cases3)
    obtain n2 E' K' where cr: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      by (rule prod_cases3)
    have E: "E = Eq \<union> E'" using Cons.prems(1) Some cq cr by simp
    have n1: "n1 = Suc (n + csize (body dq))" using cq by blast
    show ?thesis
    proof (cases "p = q")
      case True
      then show ?thesis using Cons.prems(2) Some compile_proc_entry_edge[OF cq] E by auto
    next
      case False
      with Cons.prems(2) Some n1 have "elab_procs \<Pi> qs n1 p = Some d'" by simp
      from Cons.IH[OF cr this] show ?thesis using E by blast
    qed
  qed
qed

text \<open>The elaborated table compiles to the same graph as the source table, and every
  procedure's entry edge fixes the offset its body was elaborated at.\<close>
context bridge_sem
begin

theorem located_compile_prog:
  fixes \<Pi> :: "(unit, 'v, 'e) gptable"
  assumes wf: "gwf_compile_input vars rv glob \<Pi> ps"
  shows "located (elab_pt \<Pi> ps) (compile_prog (elab_pt \<Pi> ps) ps)"
proof -
  from wf have setps: "set ps = {p. \<Pi> p \<noteq> None} - {prog_main_name}"
    by (simp add: gwf_compile_input_def)
  have g: "compile_prog (elab_pt \<Pi> ps) ps = compile_prog \<Pi> ps"
    by (rule compile_prog_erase_cong) (rule erase_pt_elab_pt[OF setps])
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = main_body \<Pi>\<rparr> n1
                  = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps) = Eprocs \<union> Emain"
    by (rule compile_prog_intra_split)
  have entry: "\<exists>d m. \<Pi> p = Some d \<and> decl = elab_decl p m d
                 \<and> (FunctionEntry p, EA_Body p, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    if "elab_pt \<Pi> ps p = Some decl" for p decl
  proof (cases "p = prog_main_name")
    case True
    from wf have md: "\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>"
      by (simp add: gwf_compile_input_def gwf_source_program_def)
    with that True procs
    have "decl = elab_decl prog_main_name n1 \<lparr>formals = [], body = main_body \<Pi>\<rparr>"
      by (simp add: elab_pt_def)
    with True md compile_proc_entry_edge[OF mainc] EI show ?thesis by blast
  next
    case False
    with that have "elab_procs \<Pi> ps 0 p = Some decl" by (simp add: elab_pt_def)
    from elab_procs_entry[OF procs this] EI show ?thesis by blast
  qed
  show ?thesis
    unfolding located_def g
  proof (intro allI impI)
    fix p b k n
    assume "compiled_at (elab_pt \<Pi> ps) (compile_prog \<Pi> ps) p b k n"
    then obtain decl where decl: "elab_pt \<Pi> ps p = Some decl" "b = body decl"
      and ent: "(FunctionEntry p, EA_Body p, Statement n) \<in> intra (compile_prog \<Pi> ps)"
      and k: "k = Statement (n + csize b)"
      unfolding compiled_at_def by blast
    from entry[OF decl(1)] obtain d m where d: "\<Pi> p = Some d" "decl = elab_decl p m d"
      and ent': "(FunctionEntry p, EA_Body p, Statement m) \<in> intra (compile_prog \<Pi> ps)"
      by blast
    have "Statement n = Statement m"
      by (rule compile_prog_entry_out_unique[OF wf ent ent'])
    then have nm: "n = m" by simp
    from wf d(1) have "gwf_source_com vars rv \<Pi> (body d)"
      by (simp add: gwf_compile_input_def gwf_source_program_def gwf_proc_decl_def)
    then have src: "source_com (body d)" by (rule wf_source_com_source_com)
    have "b = elab p k n (body d)"
      using decl(2) d(2) k nm by (simp add: elab_decl_def)
    with src show "\<exists>c :: (unit, 'v, 'e) gcom. source_com c \<and> b = elab p k n c" by blast
  qed
qed

corollary csim_point_compile_prog:
  fixes \<Pi> :: "(unit, 'v, 'e) gptable"
  assumes "gwf_compile_input vars rv glob \<Pi> ps"
    and "elab_pt \<Pi> ps, compile_prog (elab_pt \<Pi> ps) ps, p \<turnstile> (c, s, frs) \<approx> (v, t, stk)"
  shows "v = point c"
  using csim_point[OF assms(2) located_compile_prog[OF assms(1)]] by simp

end

subsection \<open>Well-formedness ignores annotations\<close>

text \<open>Every well-formedness predicate is invariant under erasure, so an elaborated table is
  well-formed exactly when its source table is.\<close>

lemma source_com_erase [simp]: "source_com (erase c) = source_com c"
  by (induction c) simp_all

lemma no_return_erase [simp]: "no_return (erase c) = no_return c"
  by (induction c) simp_all

lemma may_fallthrough_erase [simp]: "may_fallthrough (erase c) = may_fallthrough c"
  by (induction c) simp_all

lemma may_return_none_erase [simp]: "may_return_none (erase c) = may_return_none c"
  by (induction c) simp_all

lemma may_return_value_erase [simp]: "may_return_value (erase c) = may_return_value c"
  by (induction c) simp_all

lemma value_providing_erase [simp]: "value_providing (erase c) = value_providing c"
  by (simp add: value_providing_def)

context bridge_sem
begin

lemma wf_source_com_erase: "gwf_source_com vars rv (erase_pt \<Pi>) (erase c) = gwf_source_com vars rv \<Pi> c"
  by (induction c) (simp_all add: erase_pt_def split: option.split)

end

lemma erase_pt_apply: "erase_pt \<Pi> p = map_option erase_decl (\<Pi> p)"
  by (simp add: erase_pt_def)

lemma main_body_erase_pt [simp]: "main_body (erase_pt \<Pi>) = erase (main_body \<Pi>)"
  by (cases "\<Pi> prog_main_name") (simp_all add: main_body_def erase_pt_def unit_eq)

context bridge_sem
begin

lemma wf_proc_decl_erase:
  "gwf_proc_decl vars rv glob (erase_pt \<Pi>) (erase_decl d) = gwf_proc_decl vars rv glob \<Pi> d"
  by (simp add: gwf_proc_decl_def wf_source_com_erase)

lemma wf_source_program_erase_pt:
  "gwf_source_program vars rv glob (erase_pt \<Pi>) = gwf_source_program vars rv glob \<Pi>"
proof -
  have main: "erase_pt \<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body (erase_pt \<Pi>)\<rparr>
      \<longleftrightarrow> \<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>"
  proof (cases "\<Pi> prog_main_name")
    case (Some d)
    then show ?thesis by (cases d) (simp add: erase_pt_def erase_decl_def main_body_def)
  qed (simp add: erase_pt_def)
  have procs: "(\<forall>p decl. erase_pt \<Pi> p = Some decl \<longrightarrow> gwf_proc_decl vars rv glob (erase_pt \<Pi>) decl)
      \<longleftrightarrow> (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> gwf_proc_decl vars rv glob \<Pi> decl)"
  proof
    assume l: "\<forall>p decl. erase_pt \<Pi> p = Some decl \<longrightarrow> gwf_proc_decl vars rv glob (erase_pt \<Pi>) decl"
    show "\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> gwf_proc_decl vars rv glob \<Pi> decl"
    proof (intro allI impI)
      fix p decl assume "\<Pi> p = Some decl"
      then have "gwf_proc_decl vars rv glob (erase_pt \<Pi>) (erase_decl decl)"
        using l[rule_format, of p "erase_decl decl"] by (simp add: erase_pt_apply)
      then show "gwf_proc_decl vars rv glob \<Pi> decl" by (simp only: wf_proc_decl_erase)
    qed
  qed (auto simp: erase_pt_apply wf_proc_decl_erase)
  have dom: "(\<forall>p. erase_pt \<Pi> p \<noteq> None \<longrightarrow> special_table p = None)
      \<longleftrightarrow> (\<forall>p. \<Pi> p \<noteq> None \<longrightarrow> special_table p = None)"
    by (simp add: erase_pt_def)
  show ?thesis
    unfolding gwf_source_program_def main procs dom by (simp add: wf_source_com_erase)
qed

lemma wf_compile_input_erase_pt:
  "gwf_compile_input vars rv glob (erase_pt \<Pi>) ps = gwf_compile_input vars rv glob \<Pi> ps"
  by (simp add: gwf_compile_input_def wf_source_program_erase_pt erase_pt_apply)

lemma wf_compile_input_elab_pt:
  assumes "gwf_compile_input vars rv glob \<Pi> ps"
  shows "gwf_compile_input vars rv glob (elab_pt \<Pi> ps) ps"
  using assms wf_compile_input_erase_pt[where \<Pi> = "elab_pt \<Pi> ps" and ps = ps]
    wf_compile_input_erase_pt[where \<Pi> = \<Pi> and ps = ps]
    erase_pt_elab_pt[OF wf_compile_inputD(10)[OF assms]]
  by simp

lemma compile_prog_elab_pt:
  "gwf_compile_input vars rv glob \<Pi> ps \<Longrightarrow> compile_prog (elab_pt \<Pi> ps) ps = compile_prog \<Pi> ps"
  by (rule compile_prog_erase_cong) (rule erase_pt_elab_pt[OF wf_compile_inputD(10)])

end

subsection \<open>Lifting plain runs to annotated runs\<close>

text \<open>The semantics never reads an annotation, so every step of the erased program can be
  replayed by the annotated one.\<close>

lemma erase_eq_Unwind [simp]: "erase c = Unwind u \<longleftrightarrow> (\<exists>j. c = Unwind j)"
  by (cases c) simp_all

lemma erase_eq_Restore [simp]: "erase c = Restore u \<longleftrightarrow> (\<exists>j. c = Restore j)"
  by (cases c) simp_all

text \<open>Every step of the erased program is the erasure of a step of the annotated one.  Frames
  carry no annotation, so only the command is lifted; a call enters the annotated callee body.\<close>
context bridge_sem
begin

theorem pstep_lift:
  assumes "gpstep (erase_pt \<Pi>) (erase c, s, frs) (c0', s', frs')"
  shows "\<exists>c'. gpstep \<Pi> (c, s, frs) (c', s', frs') \<and> erase c' = c0'"
  using assms
proof (induction c arbitrary: c0' s' frs')
  case (Seq c1 c2)
  from Seq.prems have "gpstep (erase_pt \<Pi>) (Seq (erase c1) (erase c2), s, frs) (c0', s', frs')"
    by simp
  then show ?case
  proof (elim SeqSE)
    fix i
    assume h: "erase c1 = SKIP i" "(c0', s', frs') = (erase c2, s, frs)"
    then obtain j where "c1 = SKIP j" by (cases c1) simp_all
    with h show ?thesis by (intro exI[of _ c2] conjI) simp_all
  next
    fix c1'' t fs
    assume eq: "(c0', s', frs') = (Seq c1'' (erase c2), t, fs)"
      and st: "gpstep (erase_pt \<Pi>) (erase c1, s, frs) (c1'', t, fs)"
    from Seq.IH(1)[OF st] obtain d where "gpstep \<Pi> (c1, s, frs) (d, t, fs)" "erase d = c1''"
      by blast
    with eq show ?thesis by (intro exI[of _ "Seq d c2"] conjI) simp_all
  next
    fix i
    assume h: "erase c1 = Unwind i" "(c0', s', frs') = (Unwind i, s, frs)"
      "\<forall>i. erase c2 \<noteq> Restore i"
    then obtain j where j: "c1 = Unwind j" by auto
    from h(3) have "\<not> is_Restore c2" by (cases c2) simp_all
    with h j show ?thesis by (intro exI[of _ "Unwind j"] conjI) (simp_all add: unit_eq)
  next
    fix j i fr dst frsa
    assume h:
      "(c0', s', frs') = (SKIP i, combine_assign dst (conv dst (s rv)) (combine_env glob fr s), frsa)"
      "erase c1 = Unwind j" "erase c2 = Restore i" "frs = Frame fr dst # frsa"
    then obtain j' i' where "c1 = Unwind j'" "c2 = Restore i'" by auto
    with h show ?thesis by (intro exI[of _ "SKIP i'"] conjI) (simp_all add: unit_eq)
  qed
next
  case (If i b c1 c2)
  from If.prems
  have step: "gpstep (erase_pt \<Pi>) (If () b (erase c1) (erase c2), s, frs) (c0', s', frs')"
    by simp
  show ?case
  proof (cases "truthy (ev b s)")
    case True
    with step have "c0' = erase c1" "s' = s" "frs' = frs" by auto
    with True show ?thesis by (intro exI[of _ c1] conjI) simp_all
  next
    case False
    with step have "c0' = erase c2" "s' = s" "frs' = frs" by auto
    with False show ?thesis by (intro exI[of _ c2] conjI) simp_all
  qed
next
  case (While i b c)
  from While.prems have "gpstep (erase_pt \<Pi>) (While () b (erase c), s, frs) (c0', s', frs')"
    by simp
  then have "c0' = erase (If i b (Seq c (While i b c)) (SKIP i))" "s' = s" "frs' = frs"
    by (auto elim: WhileSE[elim_format])
  then show ?case by (intro exI[of _ "If i b (Seq c (While i b c)) (SKIP i)"] conjI) simp_all
next
  case (Call i dst p args)
  from Call.prems have "gpstep (erase_pt \<Pi>) (gcom.Call () dst p args, s, frs) (c0', s', frs')"
    by simp
  then show ?case
  proof (elim CallSE)
    fix decl0
    assume c': "(c0', s', frs') = (Seq (body decl0) (Restore ()),
                  bind_formals (formals decl0)
                    (map2 (\<lambda>x. conv (Some x)) (formals decl0) (map (\<lambda>e. ev e s) args)) (enter_state glob s),
                  Frame s dst # frs)"
      and d0: "erase_pt \<Pi> p = Some decl0"
      and len: "length args = length (formals decl0)" and dist: "distinct (formals decl0)"
    from d0 obtain decl where d: "\<Pi> p = Some decl" "decl0 = erase_decl decl"
      by (auto simp: erase_pt_apply)
    have "gpstep \<Pi> (gcom.Call i dst p args, s, frs) (Seq (body decl) (Restore i),
               bind_formals (formals decl0)
                 (map2 (\<lambda>x. conv (Some x)) (formals decl0) (map (\<lambda>e. ev e s) args)) (enter_state glob s),
               Frame s dst # frs)"
      by (rule gpstep.Call[where decl = decl]) (use len dist d in simp_all)
    then show ?thesis
      using c' d(2) by (intro exI[of _ "Seq (body decl) (Restore i)"] conjI) simp_all
  next
    fix desc sc v x
    assume dx: "dst = Some x" and c': "(c0', s', frs') = (SKIP (), s(x := conv (Some x) v), frs)"
      and st: "special_table p = Some desc" and cl: "classify_special desc args = Some sc"
      and sr: "special_result ev sc s v"
    have step: "gpstep \<Pi> (gcom.Call i (Some x) p args, s, frs) (SKIP i, s(x := conv (Some x) v), frs)"
      by (rule gpstep.Special[OF st cl sr])
    from c' have eqs: "c0' = SKIP ()" "s' = s(x := conv (Some x) v)" "frs' = frs" by simp_all
    show ?thesis unfolding eqs dx by (rule exI[of _ "SKIP i"], rule conjI[OF step]) simp
  qed
qed auto

theorem psteps_lift:
  assumes "star (gpstep (erase_pt \<Pi>)) (c0, s, frs) (c0', s', frs')" and "erase c = c0"
  shows "\<exists>c'. star (gpstep \<Pi>) (c, s, frs) (c', s', frs') \<and> erase c' = c0'"
  using assms
proof (induction c0 s frs c0' s' frs' arbitrary: c
    rule: star.induct[of "gpstep (erase_pt \<Pi>)", split_format(complete), case_names refl step])
  case (refl c0 s frs)
  then show ?case by (intro exI[of _ c] conjI star.refl)
next
  case (step c0 s frs c1 s1 frs1 c2 s2 frs2)
  from pstep_lift[of \<Pi> c s frs c1 s1 frs1] step.hyps(1) step.prems
  obtain d where d: "gpstep \<Pi> (c, s, frs) (d, s1, frs1)" "erase d = c1"
    by blast
  from step.IH[OF d(2)] obtain c' where "star (gpstep \<Pi>) (d, s1, frs1) (c', s2, frs2)" "erase c' = c2"
    by blast
  with d(1) show ?case by (blast intro: star.step)
qed

end

lemma erase_com [simp]: "erase (c :: (unit, 'v, 'e) gcom) = c"
  by (induction c) simp_all

lemma erase_pt_proc_table [simp]: "erase_pt (\<Pi> :: (unit, 'v, 'e) gptable) = \<Pi>"
proof
  fix p
  show "erase_pt \<Pi> p = \<Pi> p"
  proof (cases "\<Pi> p")
    case (Some d)
    then show ?thesis by (cases d) (simp add: erase_pt_apply erase_decl_def)
  qed (simp add: erase_pt_apply)
qed

text \<open>The elaboration of a plain table erases back to it, so \<open>psteps_lift\<close> lifts every run of
  the plain program from \<open>main\<close> to a run of its elaboration.\<close>
context bridge_sem
begin

lemma erase_elab_pt:
  fixes \<Pi> :: "(unit, 'v, 'e) gptable"
  assumes "gwf_compile_input vars rv glob \<Pi> ps"
  shows "erase_pt (elab_pt \<Pi> ps) = \<Pi>" and "erase (main_body (elab_pt \<Pi> ps)) = main_body \<Pi>"
proof -
  show ept: "erase_pt (elab_pt \<Pi> ps) = \<Pi>"
    using erase_pt_elab_pt[OF wf_compile_inputD(10)[OF assms]] by simp
  show "erase (main_body (elab_pt \<Pi> ps)) = main_body \<Pi>"
    using main_body_erase_pt[of "elab_pt \<Pi> ps"] ept by simp
qed

end

subsection \<open>Erasing a simulation\<close>

text \<open>Annotations are invisible to the simulation too: an annotated configuration related to
  a CFG configuration erases to a plain one related to the same CFG configuration.  This is
  what lets a located result imply the plain one.\<close>

lemma erase_seq_after [simp]: "erase (seq_after c afters) = seq_after (erase c) (map erase afters)"
  by (induction afters arbitrary: c) simp_all

lemma control_at_erase:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> control_at \<Pi>' p (erase c0) k n (erase r) v"
proof (induction rule: control_at.induct)
  case (SeqLeft c1 n r v c2 k)
  then show ?case using control_at.SeqLeft[of \<Pi>' p "erase c1" n "erase r" v "erase c2" k] by simp
next
  case (SeqRight c2 k n c1 r v)
  then show ?case using control_at.SeqRight[of \<Pi>' p "erase c2" k n "erase c1" "erase r" v] by simp
next
  case (IfLeft c1 k n r v i b c2)
  then show ?case
    using control_at.IfLeft[of \<Pi>' p "erase c1" k n "erase r" v "()" b "erase c2"] by simp
next
  case (IfRight c2 k n c1 r v i b)
  then show ?case
    using control_at.IfRight[of \<Pi>' p "erase c2" k n "erase c1" "erase r" v "()" b] by simp
next
  case (IfDone c1 j c2 i b k n)
  then show ?case using control_at.IfDone[of "erase c1" "()" "erase c2" \<Pi>' p "()" b k n] by auto
next
  case (WhileBody c n r v i b k)
  then show ?case using control_at.WhileBody[of \<Pi>' p "erase c" n "erase r" v "()" b k] by simp
qed (simp_all add: control_at.intros)

lemma compiled_at_erase:
  "compiled_at \<Pi> g p body_p k n \<Longrightarrow> compiled_at (erase_pt \<Pi>) g p (erase body_p) k n"
  unfolding compiled_at_def
proof (elim exE conjE)
  fix decl n' en E K
  assume d: "\<Pi> p = Some decl" and b: "body_p = body decl"
    and c: "compile \<Pi> p body_p k n = (n', en, E, K)"
    and rest: "E \<subseteq> intra g" "K \<subseteq> calls g" "(k, EA_Ret None p, FunctionResult p) \<in> intra g"
      "(FunctionEntry p, EA_Body p, Statement n) \<in> intra g" "k = Statement (n + csize body_p)"
  have "compile (erase_pt \<Pi>) p (erase body_p) k n = compile \<Pi> p body_p k n"
    by (rule compile_erase_cong) simp_all
  with d b c rest show "\<exists>decl n' en E K. erase_pt \<Pi> p = Some decl \<and> erase body_p = body decl
      \<and> compile (erase_pt \<Pi>) p (erase body_p) k n = (n', en, E, K)
      \<and> E \<subseteq> intra g \<and> K \<subseteq> calls g \<and> (k, EA_Ret None p, FunctionResult p) \<in> intra g
      \<and> (FunctionEntry p, EA_Body p, Statement n) \<in> intra g \<and> k = Statement (n + csize (erase body_p))"
    by (intro exI[of _ "erase_decl decl"] exI conjI) (simp_all add: erase_pt_apply)
qed

lemma unwinding_erase [simp]: "unwinding (erase u) = unwinding u"
  by (induction u rule: unwinding.induct) simp_all

lemma pop_ready_erase: "pop_ready w \<Longrightarrow> pop_ready (erase w) \<and> pop_ann (erase w) = Some ()"
  by (cases w rule: pop_ready.cases) simp_all

theorem csim_erase:
  "\<Pi>, g, q \<turnstile> (c, s, frs) \<approx> cfg \<Longrightarrow> erase_pt \<Pi>, g, q \<turnstile> (erase c, s, frs) \<approx> cfg"
proof (induction "(c, s, frs)" cfg arbitrary: c s frs rule: csim.induct)
  case (Base p body_p k n c v s)
  show ?case
    by (rule csim.Base[OF control_at_erase[OF Base(1)] compiled_at_erase[OF Base(2)]])
next
  case (Nested q inner s frs v stk pc body_pc kc nc i afters cont dst args site caller)
  have c1: "control_at (erase_pt \<Pi>) pc (erase body_pc) kc nc
              (seq_after (SKIP ()) (map erase afters)) cont"
    using control_at_erase[OF Nested(3)] by simp
  have c2: "control_at (erase_pt \<Pi>) pc (erase body_pc) kc nc
              (seq_after (gcom.Call () dst q args) (map erase afters)) site"
    using control_at_erase[OF Nested(4)] by simp
  show ?case
    using csim.Nested[OF Nested(2) c1 c2 compiled_at_erase[OF Nested(5)]] by simp
next
  case (Returning w i pc body_pc kc nc afters cont dst q args site callee caller)
  have c1: "control_at (erase_pt \<Pi>) pc (erase body_pc) kc nc
              (seq_after (SKIP ()) (map erase afters)) cont"
    using control_at_erase[OF Returning(3)] by simp
  have c2: "control_at (erase_pt \<Pi>) pc (erase body_pc) kc nc
              (seq_after (gcom.Call () dst q args) (map erase afters)) site"
    using control_at_erase[OF Returning(4)] by simp
  from pop_ready_erase[OF Returning(1)]
  have "pop_ready (erase w)" "pop_ann (erase w) = Some ()" by simp_all
  then show ?case
    using csim.Returning[OF _ _ c1 c2 compiled_at_erase[OF Returning(5)]] by simp
qed

subsection \<open>The nodes a source configuration is observed at\<close>

text \<open>A source configuration reached from \<open>s0\<close> is observed at node \<open>v\<close> when some run of the
  elaboration from \<open>s0\<close> reaches an annotated configuration that erases to it, names \<open>v\<close>, and
  is related to \<open>v\<close> by the simulation.  The relation is not functional: a configuration
  reachable along two paths can be observed at two nodes.\<close>

fun at_node :: "imp_prog \<Rightarrow> store \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> cfg_node \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rhd>/ _)" [51, 51, 51, 51] 50) where
  "p, s0 \<turnstile> (r, s, frs) \<rhd> v \<longleftrightarrow>
     (\<exists>c stk. erase c = r \<and> v = point c
        \<and> declared_global p, elab_pt (prog_table p) (prog_procs p)
            \<turnstile> (main_body (elab_pt (prog_table p) (prog_procs p)), s0, []) \<rightarrow>\<^sub>p\<^sup>* (c, s, frs)
        \<and> elab_pt (prog_table p) (prog_procs p), prog_cfg p, prog_main_name
            \<turnstile> (c, s, frs) \<approx> (v, s, stk))"

text \<open>Erased, the simulation relates the plain configuration to the same node.\<close>

lemma at_node_csim:
  assumes wf: "wf_program_compile_input p" and at: "p, s0 \<turnstile> (r, s, frs) \<rhd> v"
  shows "\<exists>stk. prog_table p, prog_cfg p, prog_main_name \<turnstile> (r, s, frs) \<approx> (v, s, stk)"
proof -
  from at obtain c stk where ec: "erase c = r"
    and m: "elab_pt (prog_table p) (prog_procs p), prog_cfg p, prog_main_name
              \<turnstile> (c, s, frs) \<approx> (v, s, stk)"
    by auto
  from csim_erase [OF m] ec bridge_sem.erase_elab_pt(1) [OF wf]
  show ?thesis by auto
qed

end
