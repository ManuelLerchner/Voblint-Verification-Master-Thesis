theory Compile_Invariants
  imports VIMP_Proc_to_CFG "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Structural invariants of the procedure-aware compiler\<close>

text \<open>
  The compiler preserves procedure boundaries, separates call edges from ordinary
  control flow, and allocates disjoint statement ranges. These properties connect
  source commands to activation-local traces without exposing compiler counters to
  semantic clients.
\<close>

subsection \<open>Compiler input well-formedness\<close>

text \<open>\<open>mnm\<close> names the distinguished entry procedure, declared in \<open>\<Pi>\<close> with an empty
  formal list and body \<open>main\<close>.  The callee list \<open>ps\<close> enumerates the other declared
  procedures (\<open>dom \<Pi>\<close> minus \<open>mnm\<close>), so \<open>FunctionEntry mnm\<close> / \<open>FunctionResult mnm\<close>
  never collide with a callee's nodes, yet \<open>FunctionEntry mnm\<close> is an ordinary
  \<open>proc_activation \<Pi> mnm main\<close> activation.\<close>
definition wf_compile_input ::
  "(vname => bool) => proc_table => pname list => pname => com => bool" where
  "wf_compile_input gs \<Pi> ps mnm main \<longleftrightarrow>
     distinct ps \<and>
     set ps = {p. \<Pi> p ~= None} - {mnm} \<and>
     mnm \<notin> set ps \<and>
     wf_source_program gs \<Pi> mnm main"

declare wf_compile_input_def [wf_compile_input_simps]

lemma wf_compile_input_reserved_ret_var [dest]:
  "wf_compile_input gs \<Pi> ps mnm main \<Longrightarrow> reserved_ret_var gs"
  unfolding wf_compile_input_simps by simp


definition wf_program_compile_input :: "imp_prog => bool" where
  "wf_program_compile_input p \<longleftrightarrow>
    wf_compile_input (storage_global p prog_main_name) (prog_table p)
      (prog_procs p) prog_main_name (prog_main p)"

lemma wf_program_compile_inputD:
  "wf_program_compile_input p \<Longrightarrow>
    wf_compile_input (storage_global p prog_main_name) (prog_table p)
      (prog_procs p) prog_main_name (prog_main p)"
  by (simp add: wf_program_compile_input_def)

subsection \<open>An executable, sufficient reformulation\<close>

text \<open>
  \<open>wf_source_program\<close>'s two \<open>\<forall>p. \<Pi> p = ... \<longrightarrow> ...\<close> conjuncts range over
  \<open>\<Pi> :: pname => proc_decl option\<close>'s entire (unbounded) function domain, so
  \<^const>\<open>wf_program_compile_input\<close> cannot be exported/evaluated as literally
  stated -- Isabelle's code generator has nothing to enumerate a function's
  domain against. \<open>proc_rep\<close> is always finite in practice (\<open>prog_table p =
  map_of (proc_rep p)\<close>), so both conjuncts are provably implied by the
  corresponding \<open>list_all\<close> check over \<open>proc_rep p\<close> directly: every entry
  \<open>proc_rep p\<close> actually lists is checked, which is at least as strong as
  checking only the ones \<open>map_of\<close> would resolve a lookup to.

  \<open>wf_program_compile_input_exec\<close> only needs to be \<^emph>\<open>sufficient\<close> for the CLI
  well-formedness gate to be sound (never silently accepting a source program
  \<^const>\<open>wf_program_compile_input\<close> would reject) -- not a decision procedure
  complete in the other direction, which \<open>map_of\<close>'s first-occurrence-wins
  semantics on a \<open>proc_rep\<close> with a shadowed duplicate key would make
  materially harder to establish for no operational benefit here.
\<close>

definition wf_program_compile_input_exec :: "imp_prog => bool" where
  "wf_program_compile_input_exec p \<longleftrightarrow>
     (let procs = proc_rep p; gs = storage_global p prog_main_name; pi = map_of procs
      in reserved_ret_var gs \<and>
         distinct (prog_procs p) \<and>
         set (prog_procs p) = set (map fst procs) - {prog_main_name} \<and>
         prog_main_name \<notin> set (prog_procs p) \<and>
         pi prog_main_name = Some (proc_decl_of [] (prog_main p)) \<and>
         wf_source_com pi (prog_main p) \<and> no_return (prog_main p) \<and>
         list_all (\<lambda>(_, decl). wf_proc_decl gs pi decl) procs \<and>
         list_all (\<lambda>(q, _). special_table q = None) procs)"

lemma wf_program_compile_input_exec_sound:
  assumes "wf_program_compile_input_exec p"
  shows "wf_program_compile_input p"
proof -
  define procs where "procs = proc_rep p"
  define gs where "gs = storage_global p prog_main_name"
  define pi where "pi = map_of procs"
  have pi_eq: "pi = prog_table p"
    unfolding pi_def procs_def prog_table_def ..
  from assms have h:
    "reserved_ret_var gs"
    "distinct (prog_procs p)"
    "set (prog_procs p) = set (map fst procs) - {prog_main_name}"
    "prog_main_name \<notin> set (prog_procs p)"
    "pi prog_main_name = Some (proc_decl_of [] (prog_main p))"
    "wf_source_com pi (prog_main p)"
    "no_return (prog_main p)"
    "list_all (\<lambda>(_, decl). wf_proc_decl gs pi decl) procs"
    "list_all (\<lambda>(q, _). special_table q = None) procs"
    unfolding wf_program_compile_input_exec_def procs_def gs_def pi_def Let_def
    by simp_all
  have domain: "set (map fst procs) = {q. pi q \<noteq> None}"
    unfolding pi_def by (induction procs) auto
  have every_decl: "\<And>q decl. pi q = Some decl \<Longrightarrow> wf_proc_decl gs pi decl"
  proof -
    fix q decl assume "pi q = Some decl"
    then have "(q, decl) \<in> set procs" unfolding pi_def by (rule map_of_SomeD)
    with h(8) show "wf_proc_decl gs pi decl" by (auto simp: list_all_iff)
  qed
  have every_special: "\<And>q. pi q \<noteq> None \<Longrightarrow> special_table q = None"
  proof -
    fix q assume "pi q \<noteq> None"
    then    obtain decl where "(q, decl) \<in> set procs"
      using domain by force
    with h(9) show "special_table q = None" by (auto simp: list_all_iff)
  qed
  have wf_source_program: "wf_source_program gs pi prog_main_name (prog_main p)"
    unfolding wf_source_program_def
    using h(1) h(5) h(6) h(7) every_decl every_special by blast
  have wf_compile_input: "wf_compile_input gs pi (prog_procs p) prog_main_name (prog_main p)"
    unfolding wf_compile_input_def
    using h(2) h(3) h(4) wf_source_program
    using domain by blast
  show ?thesis
    unfolding wf_program_compile_input_def gs_def[symmetric] pi_eq[symmetric]
    using wf_compile_input .
qed

definition compile_program :: "imp_prog => cfg" where
  "compile_program p =
    compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)"

text \<open>
  \<^const>\<open>compile_prog\<close> fixes the compiler input to \<^typ>\<open>proc_table\<close> /
  \<^typ>\<open>pname list\<close> / \<^typ>\<open>com\<close> separately, so every domain that only has an
  \<^typ>\<open>imp_prog\<close> in hand needs the same three-projection wrapper
  \<^const>\<open>compile_program\<close> already provides at \<^const>\<open>prog_main_name\<close>. The
  general form below (an arbitrary entry-procedure name, not just
  \<^const>\<open>prog_main_name\<close>) is the constant every check-report/executable
  layer (Sign, Interval, Parity) actually calls; every call site in this
  project instantiates \<open>mnm\<close> at \<^const>\<open>prog_main_name\<close> in practice, but the
  parameter still matches \<^const>\<open>compile_prog\<close>'s own shape rather than
  hard-coding that choice into the compilation step itself.
\<close>

definition prog_cfg :: "pname => imp_prog => cfg" where
  "prog_cfg mnm p = compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)"

lemma compile_program_is_prog_cfg: "compile_program p = prog_cfg prog_main_name p"
  by (simp add: compile_program_def prog_cfg_def)
lemma wf_compile_input_source_program:
  "wf_compile_input gs \<Pi> ps mnm main \<Longrightarrow> wf_source_program gs \<Pi> mnm main"
  by (simp add: wf_compile_input_def)


lemma wf_program_compile_input_source:
  "wf_program_compile_input p \<Longrightarrow> wf_program_source p"
  by (simp add: wf_program_compile_input_def wf_program_source_def
      wf_compile_input_def)
lemma wf_compile_input_main_exists:
  "wf_compile_input gs \<Pi> ps mnm main \<Longrightarrow> \<Pi> mnm = Some (proc_decl_of [] main)"
  using wf_compile_input_source_program wf_source_program_main_exists by blast

lemma wf_compile_input_source_pi:
  "wf_compile_input gs \<Pi> ps mnm main \<Longrightarrow> source_pi \<Pi>"
  using wf_compile_input_source_program wf_source_program_source_pi by blast

lemma wf_compile_input_source_com:
  "wf_compile_input gs \<Pi> ps mnm main \<Longrightarrow> source_com main"
  using wf_compile_input_source_program wf_source_program_source_com by blast

lemma wf_compile_input_special_table_none:
  "wf_compile_input gs \<Pi> ps mnm main \<Longrightarrow> \<Pi> p = Some decl \<Longrightarrow> special_table p = None"
  using wf_compile_input_source_program wf_source_program_special_table_none by blast

lemma wf_compile_input_no_return:
  "wf_compile_input gs \<Pi> ps mnm main \<Longrightarrow> no_return main"
  using wf_compile_input_source_program wf_source_program_no_return by blast

lemma wf_compile_input_decl:
  "wf_compile_input gs \<Pi> ps mnm main \<Longrightarrow> \<Pi> p = Some decl
   \<Longrightarrow> wf_proc_decl gs \<Pi> decl"
  using wf_compile_input_source_program wf_source_program_decl by blast

subsection \<open>Syntactic occurrence predicates\<close>


fun returns_in :: "exp option \<Rightarrow> com \<Rightarrow> bool" where
  "returns_in e (Return e') = (e = e')"
| "returns_in e (Seq c1 c2) = (returns_in e c1 \<or> returns_in e c2)"
| "returns_in e (If _ c1 c2) = (returns_in e c1 \<or> returns_in e c2)"
| "returns_in e (While _ c) = returns_in e c"
| "returns_in e _ = False"

subsection \<open>Return edges and call-freeness\<close>

text \<open>Every source \<open>Return e\<close> in procedure \<open>p\<close> compiles to an intra edge that
  reaches \<open>FunctionResult p\<close> through \<open>EA_Ret e p\<close>.\<close>
lemma compile_return_edge:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> returns_in e c
   \<Longrightarrow> \<exists>j. (Statement j, EA_Ret e p, FunctionResult p) \<in> E"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and E: "E = E1 \<union> E2"
    by (auto simp: Let_def split: prod.splits)
  from Seq.prems(2) have "returns_in e c1 \<or> returns_in e c2" by simp
  then show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] E by auto
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> E1 \<union> E2"
    by (auto split: prod.splits)
  from If.prems(2) have "returns_in e c1 \<or> returns_in e c2" by simp
  then show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] E by auto
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (auto split: prod.splits)
  from While.prems(2) have "returns_in e c" by simp
  then show ?case using While.IH[OF c1] E by auto
next
  case (Return e') then show ?case by (auto split: if_splits)
qed auto


subsection \<open>Statement-range disjointness of distinct procedures\<close>

lemma compile_proc_frag_range:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> frag_stmts E K \<subseteq> {n..<n'}"
proof -
  assume A: "compile_proc \<Pi> p decl n = (n', E, K)"
  define r where "r = n + csize (body decl)"
  from A obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement r) n = (r, Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
                  (if falls_through (body decl)
                   then insert (Statement r, EA_Ret None p, FunctionResult p) Eb
                   else Eb)"
    and n': "n' = Suc r"
    unfolding r_def by (rule compile_procE)
  have body: "frag_stmts Eb K \<subseteq> {n..<n'}"
    using compile_frag_stmts_range[OF cb] n' compile_counter_mono[OF cb] by auto
  have lit: "frag_stmts {(FunctionEntry p, EA_Nop, Statement n),
                (Statement r, EA_Ret None p, FunctionResult p)} {} \<subseteq> {n..<n'}"
    using n' r_def compile_counter_mono[OF cb] by (auto simp: frag_stmts_def)
  \<comment> \<open>the epilogue edge may be absent, so bound \<open>E\<close> by the set that always contains it\<close>
  have Esub: "E \<subseteq> {(FunctionEntry p, EA_Nop, Statement n),
                      (Statement r, EA_Ret None p, FunctionResult p)} \<union> Eb"
    using E by (auto split: if_splits)
  have "frag_stmts E K
          \<subseteq> frag_stmts ({(FunctionEntry p, EA_Nop, Statement n),
              (Statement r, EA_Ret None p, FunctionResult p)} \<union> Eb) ({} \<union> K)"
    by (rule frag_stmts_mono[OF Esub]) simp
  also have "... = frag_stmts {(FunctionEntry p, EA_Nop, Statement n),
                (Statement r, EA_Ret None p, FunctionResult p)} {} \<union> frag_stmts Eb K"
    by (rule frag_stmts_Un)
  also have "... \<subseteq> {n..<n'}" using lit body by fastforce
  finally show ?thesis .

qed

lemma compile_procs_counter_mono:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> n \<le> n'"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and n': "n' = n2"
      by (auto split: prod.splits)
    have "n \<le> n1"
      using cp by (auto simp: compile_proc_def Let_def split: prod.splits
                        dest: compile_counter_mono)
    with Cons.IH[OF rest] n' show ?thesis by simp
  qed
qed

lemma compile_procs_frag_range:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> frag_stmts E K \<subseteq> {n..<n'}"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by (simp add: frag_stmts_def)
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
      and n': "n' = n2" and E: "E = E0 \<union> E'" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    have m1: "n \<le> n1"
      using cp by (auto simp: compile_proc_def Let_def split: prod.splits
                        dest: compile_counter_mono)
    have m2: "n1 \<le> n2" using compile_procs_counter_mono[OF rest] .
    have r0: "frag_stmts E0 K0 \<subseteq> {n..<n1}" using compile_proc_frag_range[OF cp] .
    have r': "frag_stmts E' K' \<subseteq> {n1..<n2}" using Cons.IH[OF rest] .
    have "frag_stmts E K = frag_stmts E0 K0 \<union> frag_stmts E' K'"
      unfolding E K by (rule frag_stmts_Un)
    also have "... \<subseteq> {n..<n2}" using r0 r' m1 m2 by fastforce
    finally show ?thesis unfolding n' .
  qed
qed

text \<open>Statement ranges of distinct procedures are disjoint: one fragment ends at the
  counter from which the next fragment allocates its statements.\<close>
theorem compile_procs_head_disjoint:
  assumes "compile_proc \<Pi> p decl n = (n1, E0, K0)"
    and "compile_procs \<Pi> ps n1 = (n2, E', K')"
  shows "frag_stmts E0 K0 \<inter> frag_stmts E' K' = {}"
proof -
  have "frag_stmts E0 K0 \<subseteq> {n..<n1}" using compile_proc_frag_range[OF assms(1)] .
  moreover have "frag_stmts E' K' \<subseteq> {n1..<n2}" using compile_procs_frag_range[OF assms(2)] .
  ultimately show ?thesis by fastforce
qed

subsection \<open>Public compiler invariants\<close>


text \<open>A \<open>Return\<close> fragment ignores its continuation: it emits its result edge and nothing
  else, so no node exists to carry a control flow the source does not have.\<close>
theorem inv11_return_ignores_continuation:
  "compile \<Pi> p (Return e) k n = compile \<Pi> p (Return e) k' n"
  by simp


text \<open>Return branches of the same procedure converge at \<open>FunctionResult p\<close>.\<close>
theorem inv13_multi_return_converge:
  assumes "compile \<Pi> p (If b (Return e1) (Return e2)) k n = (n', en, E, K)"
  shows "(\<exists>j. (Statement j, EA_Ret e1 p, FunctionResult p) \<in> E)
       \<and> (\<exists>j. (Statement j, EA_Ret e2 p, FunctionResult p) \<in> E)"
  using compile_return_edge[OF assms, of e1] compile_return_edge[OF assms, of e2] by simp

text \<open>A self-call targets the procedure's own entry node; its call site is an ordinary
  statement node and its continuation is the caller's own next program point.  Restricted to
  \<open>p\<close> classified as an ordinary procedure: a self-call \<^const>\<open>special_table\<close> classifies
  instead sits on an intra edge, not a \<^const>\<open>CallEdge\<close>.\<close>
theorem inv14_recursion_edge:
  assumes "special_table p = None"
  shows "(Statement n, CallEdge None (call_formals \<Pi> p) [],
    FunctionEntry p, k)
     \<in> snd (snd (snd (compile \<Pi> p (Call None p []) k n)))"
  using assms by simp

text \<open>The program entry is the entry node of the distinguished root procedure.\<close>
theorem inv16_entry_is_main:
  "cfg_entry (compile_prog \<Pi> ps mnm main) = FunctionEntry mnm"
  unfolding compile_prog_def by (simp add: Let_def split: prod.splits)


section \<open>Where each statement index came from in the source\<close>

text \<open>
  \<^const>\<open>com_stmt_post_order\<close> answers this for one fragment given the counter it
  starts at. A whole program needs those starting counters, and they are not a
  fragment-local fact: \<^const>\<open>compile_procs\<close> lays the procedures out one after another
  and \<^const>\<open>compile_prog\<close> compiles \<open>main\<close> after all of them, whatever order the source
  wrote them in.

  \<open>procs_stmt_next\<close> below is that layout and nothing else --- each declared procedure
  advances the counter past its body and past the one index \<^const>\<open>compile_proc\<close>
  reserves for the epilogue. Undeclared names advance it by nothing, matching the
  clause \<^const>\<open>compile_procs\<close> skips.
\<close>

fun procs_stmt_next :: "proc_table \<Rightarrow> pname list \<Rightarrow> nat \<Rightarrow> nat" where
  "procs_stmt_next \<Pi> [] n = n"
| "procs_stmt_next \<Pi> (p # ps) n =
     (case \<Pi> p of
        None \<Rightarrow> procs_stmt_next \<Pi> ps n
      | Some decl \<Rightarrow> procs_stmt_next \<Pi> ps (Suc (n + csize (body decl))))"

text \<open>
  The layout is the compiler's own, not a second copy of it. Without this the
  arithmetic above would be a plausible restatement that no build could catch drifting
  from \<^const>\<open>compile_procs\<close>, and every position in every procedure after the first
  would move with it.
\<close>

lemma procs_stmt_next_eq_compile_procs:
  "procs_stmt_next \<Pi> ps n = fst (compile_procs \<Pi> ps n)"
proof (induction ps arbitrary: n)
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None
    then show ?thesis using Cons by simp
  next
    case (Some decl)
    obtain n1 E K where cp: "compile_proc \<Pi> p decl n = (n1, E, K)"
      by (cases "compile_proc \<Pi> p decl n") auto
    obtain n2 E' K' where cps: "compile_procs \<Pi> ps n1 = (n2, E', K')"
      by (cases "compile_procs \<Pi> ps n1") auto
    have n1: "n1 = Suc (n + csize (body decl))"
      using cp by (simp add: compile_proc_def Let_def split: prod.splits)
    have "procs_stmt_next \<Pi> (p # ps) n = fst (compile_procs \<Pi> ps n1)"
      using Some Cons n1 by simp
    then show ?thesis using Some cp cps by simp
  qed
qed simp

text \<open>
  Each definition paired with the statement indices its body owns, in the order a
  bottom-up parser finishes them. \<open>main\<close> comes last because that is where
  \<^const>\<open>compile_prog\<close> compiles it, not because of where it appears in the source ---
  which is exactly why a front end cannot pair a flat position list against the program
  and must group by definition first.
\<close>

fun defs_stmt_post_order ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> nat \<Rightarrow> (pname \<times> cfg_node list) list"
where
  "defs_stmt_post_order \<Pi> [] n = []"
| "defs_stmt_post_order \<Pi> (p # ps) n =
     (case \<Pi> p of
        None \<Rightarrow> defs_stmt_post_order \<Pi> ps n
      | Some decl \<Rightarrow>
          (p, com_stmt_post_order n (body decl))
            # defs_stmt_post_order \<Pi> ps (Suc (n + csize (body decl))))"

definition prog_stmt_post_order :: "imp_prog \<Rightarrow> (pname \<times> cfg_node list) list" where
  "prog_stmt_post_order p =
     defs_stmt_post_order (prog_table p) (prog_procs p) 0
       @ [(prog_main_name,
           com_stmt_post_order (procs_stmt_next (prog_table p) (prog_procs p) 0)
             (prog_main p))]"

text \<open>Every definition contributes as many indices as its body has commands, so a
  caller can pair position lists against these without a length check per entry.\<close>

lemma length_defs_stmt_post_order:
  "(q, vs) \<in> set (defs_stmt_post_order \<Pi> ps n)
     \<Longrightarrow> \<exists>decl. \<Pi> q = Some decl \<and> length vs = csize (body decl)"
  by (induction ps arbitrary: n) (auto split: option.splits)

end

