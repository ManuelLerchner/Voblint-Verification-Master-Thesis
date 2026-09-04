theory Compile_Invariants
  imports Compile_Wellformed "Voblint_VIMP.VIMP_Program" "Voblint_CFG.CFG_Prune"
begin

section \<open>What a program must satisfy, and what its graph then satisfies\<close>

text \<open>
  Two things live here.  \<open>wf_compile_input\<close> is the contract a source program has to meet
  before it is worth compiling: the procedure names are distinct, the entry procedure is
  declared and takes no arguments, and every body is a well-formed source command.
  \<open>wf_program_compile_input_exec\<close> is the executable form of that contract, and the check
  the command-line tool actually runs --- the contract itself quantifies over the whole
  procedure table, which no generated code can enumerate, so the executable form walks the
  declaration list instead and is proved sufficient.

  The remaining results are about the graph that comes out: each procedure's statement
  indices form a range disjoint from every other procedure's, a source \<^const>\<open>Return\<close>
  compiles to an edge into its own \<^term>\<open>FunctionResult\<close>, and the entry node reaches the
  exit.
\<close>

subsection \<open>Compiler input well-formedness\<close>

text \<open>\<open>prog_main_name\<close> names the distinguished entry procedure, declared in \<open>\<Pi>\<close> with an
  empty formal list; \<open>main_body \<Pi>\<close> reads its body back out.  The callee list \<open>ps\<close> enumerates
  the other declared procedures (\<open>dom \<Pi>\<close> minus \<open>prog_main_name\<close>), so the entry's nodes never
  collide with a callee's, yet \<open>FunctionEntry prog_main_name\<close> is an ordinary activation of a
  declared procedure like any other.\<close>
definition wf_compile_input ::
  "(vname => bool) => proc_table => pname list => bool" where
  "wf_compile_input gs \<Pi> ps \<longleftrightarrow>
     distinct ps \<and>
     set ps = {p. \<Pi> p ~= None} - {prog_main_name} \<and>
     prog_main_name \<notin> set ps \<and>
     wf_source_program gs \<Pi>"

declare wf_compile_input_def [wf_compile_input_simps]

text \<open>The leaf definitions an executable instance unfolds to decide the contract.  No
  abstract proof unfolds them, so they only ever fire under \<open>unfolding wf_compile_input_simps\<close>.\<close>
declare
  reserved_ret_var_def [wf_compile_input_simps]
  source_exp_def [wf_compile_input_simps]
  valid_formal_def [wf_compile_input_simps]
  value_providing_def [wf_compile_input_simps]
  special_table_def [wf_compile_input_simps]
  special_pname_nondet_int_def [wf_compile_input_simps]
  special_pname_min_def [wf_compile_input_simps]
  special_pname_max_def [wf_compile_input_simps]
  ret_var_def [wf_compile_input_simps]
  prog_main_name_def [wf_compile_input_simps]
  main_body_def [wf_compile_input_simps]

lemma wf_compile_input_source_program:
  "wf_compile_input gs \<Pi> ps \<Longrightarrow> wf_source_program gs \<Pi>"
  by (simp add: wf_compile_input_def)

lemma wf_compile_inputD:
  assumes "wf_compile_input gs \<Pi> ps"
  shows "reserved_ret_var gs" and "\<Pi> prog_main_name = Some \<lparr>formals = [], body = (main_body \<Pi>)\<rparr>"
    and "wf_source_com \<Pi> (main_body \<Pi>)" and "no_return (main_body \<Pi>)"
    and "\<Pi> p = Some decl \<Longrightarrow> wf_proc_decl gs \<Pi> decl"
    and "\<Pi> p = Some decl \<Longrightarrow> special_table p = None"
    and "source_pi \<Pi>" and "source_com (main_body \<Pi>)"
    and "distinct ps" and "set ps = {p. \<Pi> p \<noteq> None} - {prog_main_name}" and "prog_main_name \<notin> set ps"
  using wf_source_programD[OF wf_compile_input_source_program[OF assms]]
    assms[unfolded wf_compile_input_def] by blast+

lemmas wf_compile_input_reserved_ret_var [dest] = wf_compile_inputD(1)

abbreviation wf_program_compile_input :: "imp_prog \<Rightarrow> bool" where
  "wf_program_compile_input p \<equiv>
    wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"

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
     (let procs = proc_rep p; gs = declared_global p; pi = map_of procs
      in reserved_ret_var gs \<and>
         distinct (prog_procs p) \<and>
         set (prog_procs p) = set (map fst procs) - {prog_main_name} \<and>
         prog_main_name \<notin> set (prog_procs p) \<and>
         pi prog_main_name = Some (\<lparr>formals = [], body = prog_main p\<rparr>) \<and>
         wf_source_com pi (prog_main p) \<and> no_return (prog_main p) \<and>
         list_all (\<lambda>(_, decl). wf_proc_decl gs pi decl) procs \<and>
         list_all (\<lambda>(q, _). special_table q = None) procs)"

lemma wf_program_compile_input_exec_sound:
  assumes "wf_program_compile_input_exec p"
  shows "wf_program_compile_input p"
proof -
  define procs where "procs = proc_rep p"
  define gs where "gs = declared_global p"
  define pi where "pi = map_of procs"
  have pi_eq: "pi = prog_table p"
    unfolding pi_def procs_def prog_table_def ..
  from assms have h:
    "reserved_ret_var gs"
    "distinct (prog_procs p)"
    "set (prog_procs p) = set (map fst procs) - {prog_main_name}"
    "prog_main_name \<notin> set (prog_procs p)"
    "pi prog_main_name = Some (\<lparr>formals = [], body = prog_main p\<rparr>)"
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
  have main_eq: "main_body pi = prog_main p" using pi_eq by simp
  have wf_source_program: "wf_source_program gs pi"
    unfolding wf_source_program_def main_eq
    using h(1) h(5) h(6) h(7) every_decl every_special by blast
  have wf_compile_input: "wf_compile_input gs pi (prog_procs p)"
    unfolding wf_compile_input_def
    using h(2) h(3) h(4) wf_source_program
    using domain by blast
  show ?thesis
    unfolding gs_def[symmetric] pi_eq[symmetric] using wf_compile_input .
qed

definition compile_program :: "imp_prog => cfg" where
  "compile_program p =
    compile_prog (prog_table p) (prog_procs p)"

text \<open>\<^const>\<open>compile_prog\<close> takes a \<^typ>\<open>proc_table\<close> and a \<^typ>\<open>pname list\<close>, so a
  domain holding only an \<^typ>\<open>imp_prog\<close> needs the two-projection wrapper below.  The entry
  name is \<^const>\<open>prog_main_name\<close> and its body is looked up, so neither is threaded through
  as a parameter.\<close>

definition prog_cfg :: "imp_prog => cfg" where
  "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"

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

subsection \<open>Public compiler invariants\<close>

text \<open>A \<open>Return\<close> fragment ignores its continuation: it emits its result edge and nothing
  else, so no node exists to carry a control flow the source does not have.\<close>
theorem compile_Return_ignores_continuation:
  "compile \<Pi> p (Return e) k n = compile \<Pi> p (Return e) k' n"
  by simp

theorem compile_multi_return_converge:
  assumes "compile \<Pi> p (If b (Return e1) (Return e2)) k n = (n', en, E, K)"
  shows "(\<exists>j. (Statement j, EA_Ret e1 p, FunctionResult p) \<in> E)
       \<and> (\<exists>j. (Statement j, EA_Ret e2 p, FunctionResult p) \<in> E)"
  using compile_return_edge[OF assms, of e1] compile_return_edge[OF assms, of e2] by simp

text \<open>A self-call targets the procedure's own entry node; its call site is an ordinary
  statement node and its continuation is the caller's own next program point.  Restricted to
  \<open>p\<close> classified as an ordinary procedure: a self-call \<^const>\<open>special_table\<close> classifies
  instead sits on an intra edge, not a \<^const>\<open>CallEdge\<close>.\<close>
theorem compile_self_call_edge:
  assumes "special_table p = None"
  shows "(Statement n, CallEdge None (call_formals \<Pi> p) [], FunctionEntry p, k)
           \<in> snd (snd (snd (compile \<Pi> p (Call None p []) k n)))"
  using assms by simp

section \<open>Where each statement index came from in the source\<close>

subsection \<open>Statement order in the source\<close>

text \<open>
  Which \<^const>\<open>Statement\<close> index \<^const>\<open>compile\<close> gives each command of a fragment, listed in
  the order a bottom-up parser completes the commands: a reduction finishes only once its
  whole right-hand side has been read, so an \<open>if\<close> is listed after both its branches and a
  loop after its body.  Every clause allocates the same index its \<^const>\<open>compile\<close>
  counterpart does: a leaf takes \<open>n\<close>; \<^const>\<open>Seq\<close> hands \<open>c2\<close> the counter \<open>c1\<close> ends at;
  \<^const>\<open>If\<close> and \<^const>\<open>While\<close> take \<open>n\<close> for the guard and start the body at \<open>Suc n\<close>.
  A front end that records one position per reduction can pair its \<open>k\<close>th position with
  this list's \<open>k\<close>th index without reproducing \<^const>\<open>compile\<close>'s counter arithmetic;
  stating the order here keeps the two from drifting.
\<close>

fun com_stmt_post_order :: "nat \<Rightarrow> com \<Rightarrow> cfg_node list" where
  "com_stmt_post_order n SKIP = [Statement n]"
| "com_stmt_post_order n (Assign x a) = [Statement n]"
| "com_stmt_post_order n (Check c) = [Statement n]"
| "com_stmt_post_order n (Seq c1 c2) =
     com_stmt_post_order n c1 @ com_stmt_post_order (n + csize c1) c2"
| "com_stmt_post_order n (If b c1 c2) =
     com_stmt_post_order (Suc n) c1 @ com_stmt_post_order (Suc n + csize c1) c2
       @ [Statement n]"
| "com_stmt_post_order n (While b c) = com_stmt_post_order (Suc n) c @ [Statement n]"
| "com_stmt_post_order n (Call dst q actuals) = [Statement n]"
| "com_stmt_post_order n (Return e) = [Statement n]"
| "com_stmt_post_order n Restore = [Statement n]"
| "com_stmt_post_order n Unwind = [Statement n]"

text \<open>The enumeration names exactly the indices the fragment allocates, each once: a
  shorter or longer list, or a repeated index, would silently misalign every position
  after it.\<close>

lemma length_com_stmt_post_order [simp]: "length (com_stmt_post_order n c) = csize c"
  by (induction c arbitrary: n) auto

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

section \<open>Connectivity of a compiled graph\<close>

text \<open>A compiled fragment's entry reaches its continuation or its procedure result along
  the structural successor relation.  Nothing downstream consumes this: a routed D/G
  system's own coverage witness is \<open>vars_cover_exec\<close>, decided per node from whether a
  caller actually published a seed, not from graph reachability.  This connectivity fact
  is instead what pins the transparent \<^const>\<open>Restore\<close>/\<^const>\<open>Unwind\<close> encoding ---
  emitting nothing for those clauses would make them dead ends and force a
  \<^const>\<open>source_com\<close> hypothesis onto the whole-program statement.\<close>

text \<open>The fragment-relative forms the compiler inductions use: an edge of a fragment
  included in the graph.\<close>
lemma cfg_reaches_intra_sub:
  "(u, a, v) \<in> E \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> cfg_reaches g u v"
  by (blast intro: cfg_reaches_intra)

lemma cfg_reaches_comb_caller_sub:
  "(c, ca, ce, k) \<in> K \<Longrightarrow> K \<subseteq> calls g \<Longrightarrow> cfg_reaches g c k"
  by (blast intro: cfg_reaches_comb_caller)

subsection \<open>Compiled entry reaches its exit or its procedure result\<close>

text \<open>\<^const>\<open>falls_through\<close> decides where a fragment's entry leads: a fragment that can
  complete normally reaches its continuation; one that cannot reaches the enclosing
  procedure's \<^term>\<open>FunctionResult\<close> along an explicit \<^const>\<open>Return\<close> edge.  The second
  direction is what lets \<open>compile_proc\<close> leave the epilogue node unallocated.\<close>
lemma compile_reaches_falls_through:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "E \<subseteq> intra g" and "K \<subseteq> calls g"
    and "falls_through c"
  shows "cfg_reaches g en k"
  using assms
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and res: "en = Statement n" "E = E1 \<union> E2" "K = K1 \<union> K2"
    by (rule compile_SeqE)
  have "cfg_reaches g (Statement n) (Statement (n + csize c1))"
    using Seq.IH(1)[OF c1] Seq.prems res by auto
  moreover have "cfg_reaches g (Statement (n + csize c1)) k"
    using Seq.IH(2)[OF c2] Seq.prems res by auto
  ultimately show ?case unfolding res(1) by (rule cfg_reaches_trans)
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and res: "en = Statement n"
      "E = {(Statement n, EA_Assume b, Statement (Suc n)),
            (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
      "K = K1 \<union> K2"
    by (rule compile_IfE)
  have b1: "cfg_reaches g (Statement n) (Statement (Suc n))"
    and b2: "cfg_reaches g (Statement n) (Statement (Suc n + csize c1))"
    using res(2) If.prems(2) by (blast intro: cfg_reaches_intra_sub)+
  from If.prems(4) consider "falls_through c1" | "falls_through c2" by auto
  then show ?case
  proof cases
    case 1
    have "cfg_reaches g (Statement (Suc n)) k" using If.IH(1)[OF c1] If.prems res 1 by auto
    with b1 show ?thesis unfolding res(1) by (rule cfg_reaches_trans)
  next
    case 2
    have "cfg_reaches g (Statement (Suc n + csize c1)) k"
      using If.IH(2)[OF c2] If.prems res 2 by auto
    with b2 show ?thesis unfolding res(1) by (rule cfg_reaches_trans)
  qed
qed (auto simp: Let_def split: prod.splits option.splits
     intro: cfg_reaches_intra_sub cfg_reaches_comb_caller_sub)

lemma compile_reaches_returns:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "E \<subseteq> intra g" and "K \<subseteq> calls g"
    and "\<not> falls_through c"
  shows "cfg_reaches g en (FunctionResult p)"
  using assms
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and res: "en = Statement n" "E = E1 \<union> E2" "K = K1 \<union> K2"
    by (rule compile_SeqE)
  show ?case
  proof (cases "falls_through c1")
    case False
    then show ?thesis using Seq.IH(1)[OF c1] Seq.prems res by auto
  next
    case True
    have "cfg_reaches g (Statement n) (Statement (n + csize c1))"
      using compile_reaches_falls_through[OF c1] Seq.prems res True by auto
    moreover have "cfg_reaches g (Statement (n + csize c1)) (FunctionResult p)"
      using Seq.IH(2)[OF c2] Seq.prems res True by auto
    ultimately show ?thesis unfolding res(1) by (rule cfg_reaches_trans)
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and res: "en = Statement n"
      "E = {(Statement n, EA_Assume b, Statement (Suc n)),
            (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
      "K = K1 \<union> K2"
    by (rule compile_IfE)
  have "cfg_reaches g (Statement n) (Statement (Suc n))"
    using res(2) If.prems(2) by (blast intro: cfg_reaches_intra_sub)
  moreover have "cfg_reaches g (Statement (Suc n)) (FunctionResult p)"
    using If.IH(1)[OF c1] If.prems res by auto
  ultimately show ?case unfolding res(1) by (rule cfg_reaches_trans)
qed (auto simp: Let_def split: prod.splits option.splits intro: cfg_reaches_intra_sub)

lemma compile_proc_reaches_result:
  assumes "compile_proc \<Pi> p decl n = (n', E, K)"
      and "E \<subseteq> intra g" "K \<subseteq> calls g"
  shows "cfg_reaches g (FunctionEntry p) (FunctionResult p)"
proof -
  let ?r = "n + csize (body decl)"
  obtain Eb where
      body: "compile \<Pi> p (body decl) (Statement ?r) n = (?r, Statement n, Eb, K)"
    and E_eq: "E = insert (FunctionEntry p, EA_Nop, Statement n)
                     (if falls_through (body decl)
                      then insert (Statement ?r, EA_Ret None p, FunctionResult p) Eb
                      else Eb)"
    by (rule compile_procE[OF assms(1)])
  have Ebg: "Eb \<subseteq> intra g" using E_eq assms(2) by (auto split: if_splits)
  have entry: "cfg_reaches g (FunctionEntry p) (Statement n)"
    using E_eq assms(2) by (blast intro: cfg_reaches_intra_sub)
  show ?thesis
  proof (cases "falls_through (body decl)")
    case True
    have "cfg_reaches g (Statement ?r) (FunctionResult p)"
      using E_eq assms(2) True using cfg_reaches_intra_sub by auto
    with compile_reaches_falls_through[OF body Ebg assms(3) True] entry show ?thesis
      by (blast intro: cfg_reaches_trans)
  next
    case False
    from compile_reaches_returns[OF body Ebg assms(3) False] entry show ?thesis
      by (rule cfg_reaches_trans[rotated])
  qed
qed

theorem compile_prog_entry_cfg_reaches_exit:
  "cfg_reaches (compile_prog \<Pi> ps)
     (cfg_entry (compile_prog \<Pi> ps)) (cfg_exit (compile_prog \<Pi> ps))"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      cmain: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1 = (n2, Emain, Kmain)"
    and g: "intra (compile_prog \<Pi> ps) = Eprocs \<union> Emain"
           "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have "cfg_reaches (compile_prog \<Pi> ps) (FunctionEntry prog_main_name) (FunctionResult prog_main_name)"
    using g by (intro compile_proc_reaches_result[OF cmain]) auto
  then show ?thesis by simp
qed

end
