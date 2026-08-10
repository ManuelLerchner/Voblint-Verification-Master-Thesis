theory VIMP_Proc_to_CFG
  imports CFG_Def "Voblint_VIMP.VIMP_Proc"
begin

section \<open>Procedure-aware CFG compilation for \<open>com\<close> programs\<close>

text \<open>
  Compile a \<open>com\<close> program directly into the two-relation procedure-aware CFG.  Nodes are
  \<open>Statement n\<close> (allocated from a counter), \<open>FunctionEntry p\<close>, and \<open>FunctionResult p\<close>.
  The compiler threads the enclosing procedure name \<open>p\<close>, so a source \<open>Return\<close> and the
  normal fall-through both reach \<open>FunctionResult p\<close> through an \<open>EA_Ret\<close> intra edge.

  Compilation is continuation passing: the node reached when a fragment falls through is an
  input, not a result.  A node therefore denotes a program point between transfer functions,
  and no fragment invents a node to hold a control flow that its own source construct does not
  have.

  Layout of one procedure \<open>p\<close> with body \<open>b\<close>:
    \<^item> \<open>FunctionEntry p --EA_Nop--> entry(b)\<close>;
    \<^item> the compiled body edges, with the epilogue node as the body's continuation;
    \<^item> \<open>epilogue --EA_Ret None p--> FunctionResult p\<close> (normal fall-through returns without a
       value);
    \<^item> each source \<open>Return e\<close> inside \<open>b\<close> compiles to \<open>--EA_Ret e p--> FunctionResult p\<close> and
       ignores its continuation, so an early return leaves no node behind.

  Control effects and their source counterparts:
    \<^item> source lexical restoration (\<open>Scope\<close> / \<open>Restore\<close>) becomes ordinary intra flow;
      \<open>Scope\<close> is represented by transparent \<open>EA_Nop\<close> brackets;
    \<^item> source \<open>Return\<close> / \<open>Unwind\<close> become an explicit \<open>EA_Ret\<close> edge into \<open>FunctionResult\<close>;
    \<^item> source activation handling becomes \<open>FunctionResult\<close> + the \<open>calls\<close>-edge continuation.

  Calls are emitted only into \<open>calls\<close>; a call never appears as an executable intra edge.
  \<open>Restore\<close> / \<open>Unwind\<close> are runtime-only (excluded by \<^const>\<open>source_com\<close>); their compile
  clauses are trivial one-node stubs that never occur for a source program.
\<close>
subsection \<open>Static allocation size\<close>

text \<open>\<open>csize c\<close> is the number of \<open>Statement\<close> indices the fragment of \<open>c\<close> allocates, fixed by
  the source syntax alone.  \<open>compile\<close> needs it before it recurses: \<open>Seq\<close> names the entry
  node of \<open>c2\<close> --- the continuation it hands to \<open>c1\<close> --- and that node is
  \<open>Statement (n + csize c1)\<close>.  \<open>compile_next_id\<close> below ties the two together, so the two
  definitions cannot drift apart silently.\<close>
fun csize :: "com \<Rightarrow> nat" where
  "csize SKIP = 1"
| "csize (Assign x a) = 1"
| "csize (Random x) = 1"
| "csize (Check c) = 1"
| "csize (Seq c1 c2) = csize c1 + csize c2"
| "csize (If b c1 c2) = 1 + csize c1 + csize c2"
| "csize (While b c) = 1 + csize c"
| "csize (Call dst q actuals) = 1"
| "csize (Return e) = 1"
| "csize Restore = 1"
| "csize Unwind = 1"

lemma csize_pos: "0 < csize c"
  by (induction c) auto

subsection \<open>Normal completion\<close>

text \<open>\<open>falls_through c\<close>: control can leave the fragment of \<open>c\<close> through its continuation, rather
  than only through an explicit \<^const>\<open>Return\<close>.  It is a syntactic over-approximation of the
  dynamic property --- \<open>While\<close> is counted as falling through because its guard may fail on the
  first test, and a branch that is never taken still contributes.  The two directions
  \<open>compile_reaches_falls_through\<close> and \<open>compile_reaches_returns\<close> turn it into the reachability
  facts the procedure wrapper needs, and \<open>compile_proc\<close> uses it to decide whether the epilogue
  node is worth allocating.\<close>
fun falls_through :: "com \<Rightarrow> bool" where
  "falls_through SKIP = True"
| "falls_through (Assign x a) = True"
| "falls_through (Random x) = True"
| "falls_through (Check c) = True"
| "falls_through (Seq c1 c2) = (falls_through c1 \<and> falls_through c2)"
| "falls_through (If b c1 c2) = (falls_through c1 \<or> falls_through c2)"
| "falls_through (While b c) = True"
| "falls_through (Call dst q actuals) = True"
| "falls_through (Return e) = False"
| "falls_through Restore = True"
| "falls_through Unwind = True"

subsection \<open>Command compilation\<close>

text \<open>\<open>compile \<Pi> p c k n\<close> returns \<open>(n', entry, intra_edges, call_edges)\<close>, allocating
  \<open>Statement\<close> indices in the counter range \<open>[n, n')\<close>.  The continuation \<open>k\<close> is an
  \<^emph>\<open>input\<close>: it is the node normal execution reaches when the fragment falls through.  A
  fragment therefore never reports an exit, and a command that cannot fall through simply
  ignores \<open>k\<close>.

  Every fragment enters at \<open>Statement n\<close>, so the entry is determined by the counter and is
  reported only for convenience.  The procedure table \<open>\<Pi>\<close> is threaded so a
  \<^const>\<open>Call\<close> can label its \<open>CallEdge\<close> with the callee's declared formals; every other
  clause ignores it.

  Consequences of handing the continuation down rather than reporting an exit:
    \<^item> \<^const>\<open>Seq\<close> needs no connecting \<open>EA_Nop\<close>: \<open>c1\<close>'s continuation \<^emph>\<open>is\<close> \<open>c2\<close>'s entry;
    \<^item> \<^const>\<open>If\<close> allocates no merge node: both branches receive the same \<open>k\<close>, and the join
      happens at \<open>k\<close>, which is the program point after the conditional;
    \<^item> \<^const>\<open>While\<close> needs no back-edge node: the body's continuation is the loop head;
    \<^item> \<^const>\<open>Return\<close> ignores \<open>k\<close> and emits only its \<open>EA_Ret\<close> edge, so no unreachable
      continuation node is invented;
    \<^item> \<^const>\<open>Call\<close> resumes at \<open>k\<close>, so the resume point is the following program point.
  \<^const>\<open>Restore\<close> and \<^const>\<open>Unwind\<close> are runtime-only (excluded by \<^const>\<open>source_com\<close>),
  so their clauses are never exercised for a source program.  They stay transparent: one node
  and a \<open>EA_Nop\<close> to the continuation, which is what a fragment whose entry and exit were the
  same node meant before the continuation became an input.  Making them dead ends instead would
  cost the unconditional form of \<open>compile_prog_entry_cfg_reaches_exit\<close> for no gain, since no
  source program reaches these clauses.\<close>

text \<open>
  A call edge into an undeclared procedure carries no formals: \<^const>\<open>Call\<close> compiles
  against whatever \<^term>\<open>\<Pi> q\<close> says at compile time, declared or not, so its formal
  list is this classifier rather than a lookup that could fail. Naming it lets lemma
  statements about compiled call edges cite \<open>call_formals\<close> instead of restating the
  case split; the \<open>[simp]\<close> tag keeps it transparent to existing automation.
\<close>
definition call_formals :: "proc_table \<Rightarrow> pname \<Rightarrow> vname list" where
  "call_formals \<Pi> q = (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> [])"

declare call_formals_def [simp]

fun compile ::
  "proc_table \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> nat
   \<Rightarrow> nat \<times> cfg_node
        \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile \<Pi> p SKIP k n =
     (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})"
| "compile \<Pi> p (Assign x a) k n =
     (Suc n, Statement n, {(Statement n, EA_Assign x a, k)}, {})"
| "compile \<Pi> p (Random x) k n =
     (Suc n, Statement n, {(Statement n, EA_Random x, k)}, {})"
| "compile \<Pi> p (Check c) k n =
     (Suc n, Statement n, {(Statement n, EA_Check c, k)}, {})"
| "compile \<Pi> p (Seq c1 c2) k n =
     (let (n1, en1, E1, K1) = compile \<Pi> p c1 (Statement (n + csize c1)) n;
          (n2, en2, E2, K2) = compile \<Pi> p c2 k (n + csize c1)
      in (n2, en1, E1 \<union> E2, K1 \<union> K2))"
| "compile \<Pi> p (If b c1 c2) k n =
     (let (n1, en1, E1, K1) = compile \<Pi> p c1 k (Suc n);
          (n2, en2, E2, K2) = compile \<Pi> p c2 k n1
      in (n2, Statement n,
          {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
            \<union> E1 \<union> E2,
          K1 \<union> K2))"
| "compile \<Pi> p (While b c) k n =
     (let (n1, en1, E1, K1) = compile \<Pi> p c (Statement n) (Suc n)
      in (n1, Statement n,
          {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1,
          K1))"
| "compile \<Pi> p (Call dst q actuals) k n =
     (Suc n, Statement n, {},
      {(Statement n,
        CallEdge dst (call_formals \<Pi> q) actuals,
        FunctionEntry q, k)})"
| "compile \<Pi> p (Return e) k n =
     (Suc n, Statement n, {(Statement n, EA_Ret e p, FunctionResult p)}, {})"
| "compile \<Pi> p Restore k n =
     (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})"
| "compile \<Pi> p Unwind k n =
     (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})"

subsection \<open>Procedure and program compilation\<close>

text \<open>A procedure wraps its body between \<open>FunctionEntry p\<close> and \<open>FunctionResult p\<close>.  The body
  is compiled with the \<^emph>\<open>epilogue\<close> node \<open>Statement r\<close> as its continuation, and the epilogue
  carries the implicit \<open>EA_Ret None p\<close>: normal fall-through returns without a value.  A value is
  published only by an explicit source \<open>Return e\<close>, which compiles to its own
  \<open>EA_Ret (Some e) p\<close> edge inside the body.

  The epilogue exists so that every edge into \<open>FunctionResult p\<close> is a return edge.  Passing
  \<open>FunctionResult p\<close> directly as the body continuation would let a trailing assignment target
  the result node, losing \<open>compile_result_target\<close>.  It is allocated \<^emph>\<open>after\<close> the body, so
  statement indices stay in source order and \<open>r\<close> lies inside the procedure's own counter
  range --- which is what keeps edge locality a statement about one fragment.

  The epilogue is wired only when the body can reach it, that is when
  \<^const>\<open>falls_through\<close> holds.  A body all of whose paths end in an explicit \<^const>\<open>Return\<close>
  leaves \<open>Statement r\<close> with no edges at all, so it is not a node of the compiled graph --- nodes
  exist extensionally, through the edges that mention them.  \<open>compile_reaches_returns\<close> supplies
  the reachability that the epilogue edge would otherwise have carried.

  The counter still advances past \<open>r\<close> in both cases.  Reserving the index costs one \<open>nat\<close> and
  keeps every \<^const>\<open>csize\<close> equation, fragment range and procedure interval independent of
  \<^const>\<open>falls_through\<close>.\<close>

definition compile_proc ::
  "proc_table \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> nat
   \<Rightarrow> nat \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile_proc \<Pi> p decl n =
     (let r = n + csize (body decl);
          (n', ben, E, K) = compile \<Pi> p (body decl) (Statement r) n
      in (Suc r,
          insert (FunctionEntry p, EA_Nop, ben)
            (if falls_through (body decl)
             then insert (Statement r, EA_Ret None p, FunctionResult p) E
             else E),
          K))"

fun compile_procs ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> nat
   \<Rightarrow> nat \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile_procs \<Pi> [] n = (n, {}, {})"
| "compile_procs \<Pi> (p # ps) n =
     (case \<Pi> p of
        None \<Rightarrow> compile_procs \<Pi> ps n
      | Some decl \<Rightarrow>
          (let (n1, E, K) = compile_proc \<Pi> p decl n;
               (n2, E', K') = compile_procs \<Pi> ps n1
           in (n2, E \<union> E', K \<union> K')))"

text \<open>The whole program: every declared procedure, plus \<open>main\<close> compiled under the
  designated main name \<open>mnm\<close> (which the well-formedness predicate keeps disjoint from
  \<open>ps\<close>).  There is no global exit: whole-program completion is \<open>FunctionResult mnm\<close>, and the
  entry is \<open>FunctionEntry mnm\<close>.\<close>

text \<open>\<open>checks\<close> is not collected by a separate counter-threading pass: it is read
  directly off the compiled edges, exactly the \<^const>\<open>EA_Check\<close> edges
  \<^const>\<open>compile\<close>'s own \<open>Check c\<close> clause emits. There is only one representation
  of "where a check sits and what it says" --- the compiled \<^const>\<open>intra\<close> set
  itself --- so this field cannot drift from it by construction, not merely by
  a separately proved agreement lemma.\<close>
definition compile_prog ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg"
where
  "compile_prog \<Pi> ps mnm main =
     (let (n1, Eprocs, Kprocs) = compile_procs \<Pi> ps 0;
          (n2, Emain, Kmain) = compile_proc \<Pi> mnm (proc_decl_of [] main) n1
      in \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm,
           checks = (\<lambda>(u, a, v). (u, ea_check_cond a))
             ` Set.filter (\<lambda>(u, a, v). is_EA_Check a) (Eprocs \<union> Emain) \<rparr>)"

subsection \<open>Allocation arithmetic and statement ranges\<close>

text \<open>A fragment allocates exactly \<open>csize c\<close> indices.  This is the obligation the forward
  numbering rests on: \<open>Seq\<close> names \<open>c2\<close>'s entry before compiling \<open>c1\<close>, so a clause allocating
  more or fewer nodes than its \<^const>\<open>csize\<close> claims would leave that continuation dangling.
  The equation subsumes the counter monotonicity used throughout the ownership lemmas.\<close>

lemma compile_next_id:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> n' = n + csize c"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and n': "n' = n2"
    by (auto simp: Let_def split: prod.splits)
  from Seq.IH(2)[OF c2] n' show ?case by simp
next
  case (If b c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)" and n': "n' = n2"
    by (auto split: prod.splits)
  from If.IH(1)[OF c1] If.IH(2)[OF c2] n' show ?case by simp
next
  case (While b c)
  then obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)" and n': "n' = n1"
    by (auto split: prod.splits)
  from While.IH[OF c1] n' show ?case by simp
qed (auto split: prod.splits option.splits)

lemma compile_fst_next_id: "fst (compile \<Pi> p c k n) = n + csize c"
  by (metis compile_next_id prod_cases4 fst_conv)

lemma compile_counter_mono:
  assumes "compile \<Pi> p c k n = (n', en, E, K)"
  shows "n \<le> n'"
  using compile_next_id[OF assms] by simp

text \<open>Every fragment enters at its base counter.  Handing the continuation down does not
  change this, which is why \<^const>\<open>SKIP\<close> keeps a node of its own instead of reporting the
  continuation as its entry.\<close>

lemma compile_entry:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> en = Statement n"
  by (induction c arbitrary: k n n' en E K rule: com.induct)
     (auto simp: Let_def split: prod.splits)

lemma compile_entry_stmt:
  assumes "compile \<Pi> p c k n = (n', en, E, K)"
  shows "\<exists>j. en = Statement j \<and> n \<le> j \<and> j < n'"
  using compile_entry[OF assms] compile_next_id[OF assms] csize_pos by auto

subsection \<open>Fragment decomposition\<close>

text \<open>The composite clauses, packaged as elimination rules.  Every consumer of \<^const>\<open>compile\<close>
  needs the same destructuring --- sub-fragments, their base counters, and the edge split ---
  and \<^const>\<open>csize\<close> makes the sub-counters explicit, so no auxiliary equation has to be
  carried along.\<close>

lemma compile_SeqE:
  assumes "compile \<Pi> p (Seq c1 c2) k n = (n', en, E, K)"
  obtains n1 E1 K1 n2 E2 K2 where
    "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    "en = Statement n" "E = E1 \<union> E2" "K = K1 \<union> K2"
proof -
  obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    by (cases "compile \<Pi> p c1 (Statement (n + csize c1)) n") auto
  obtain n2 en2 E2 K2 where
    c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    by (cases "compile \<Pi> p c2 k (n + csize c1)") auto
  have e1: "en1 = Statement n" using compile_entry[OF c1] .
  have e2: "en2 = Statement (n + csize c1)" using compile_entry[OF c2] .
  from assms c1 c2 have "en = Statement n" "E = E1 \<union> E2" "K = K1 \<union> K2"
    using e1 by (auto simp: Let_def)
  with c1 c2 e1 e2 show ?thesis by (auto intro: that)
qed

lemma compile_IfE:
  assumes "compile \<Pi> p (If b c1 c2) k n = (n', en, E, K)"
  obtains n1 E1 K1 n2 E2 K2 where
    "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    "en = Statement n"
    "E = {(Statement n, EA_Assume b, Statement (Suc n)),
          (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
    "K = K1 \<union> K2"
proof -
  obtain n1 en1 E1 K1 where c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    by (cases "compile \<Pi> p c1 k (Suc n)") auto
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have i1: "n1 = Suc n + csize c1" using compile_next_id[OF c1] by simp
  obtain n2 en2 E2 K2 where c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    by (cases "compile \<Pi> p c2 k n1") auto
  have e2: "en2 = Statement (Suc n + csize c1)" using compile_entry[OF c2] i1 by simp
  from assms c1 c2 e1 e2
  have "en = Statement n"
    "E = {(Statement n, EA_Assume b, Statement (Suc n)),
          (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
    "K = K1 \<union> K2"
    by (auto simp: Let_def)
  with c1 c2 e1 e2 i1 show ?thesis by (auto intro: that)
qed

lemma compile_WhileE:
  assumes "compile \<Pi> p (While b c) k n = (n', en, E, K)"
  obtains n1 E1 K1 where
    "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    "en = Statement n"
    "E = {(Statement n, EA_Assume b, Statement (Suc n)),
          (Statement n, EA_AssumeNot b, k)} \<union> E1"
    "K = K1"
proof -
  obtain n1 en1 E1 K1 where c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    by (cases "compile \<Pi> p c (Statement n) (Suc n)") auto
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  from assms c1 e1
  have "en = Statement n"
    "E = {(Statement n, EA_Assume b, Statement (Suc n)),
          (Statement n, EA_AssumeNot b, k)} \<union> E1"
    "K = K1"
    by (auto simp: Let_def)
  with c1 e1 show ?thesis by (auto intro: that)
qed

subsection \<open>Check-obligation soundness\<close>

text \<open>Now immediate: \<open>checks\<close> is \<^emph>\<open>defined\<close> (\<^const>\<open>compile_prog\<close>) as the projection of
  \<^const>\<open>EA_Check\<close> edges out of the compiled program's own \<^const>\<open>intra\<close> set, so every check
  the whole-program compiler records is sourced at a real \<^const>\<open>EA_Check\<close> edge by
  construction, not by a separately proved agreement between two independently computed
  passes.\<close>

corollary compile_prog_checks_sound:
  assumes "(v, ch) \<in> checks (compile_prog \<Pi> ps mnm main)"
  shows "\<exists>k'. (v, EA_Check ch, k') \<in> intra (compile_prog \<Pi> ps mnm main)"
  using assms unfolding compile_prog_def by (auto simp: Let_def split: prod.splits)

text \<open>The \<open>Statement\<close> indices a compiled fragment touches.  Sources are always freshly
  allocated, so they lie in the fragment's own counter range; a target may in addition be the
  continuation, which belongs to the enclosing construct.  \<open>kstmt\<close> names that one extra
  index, and is empty when the continuation is not a \<open>Statement\<close> node.\<close>

definition frag_stmts ::
  "(cfg_node \<times> edge_action \<times> cfg_node) set
   \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set \<Rightarrow> nat set"
where
  "frag_stmts E K =
     {j. \<exists>a v. (Statement j, a, v) \<in> E} \<union> {j. \<exists>u a. (u, a, Statement j) \<in> E}
   \<union> {j. \<exists>act ce af. (Statement j, act, ce, af) \<in> K}
   \<union> {j. \<exists>u act ce. (u, act, ce, Statement j) \<in> K}"

fun kstmt :: "cfg_node \<Rightarrow> nat set" where
  "kstmt (Statement j) = {j}"
| "kstmt (FunctionEntry q) = {}"
| "kstmt (FunctionResult q) = {}"

lemma kstmt_iff [simp]: "j \<in> kstmt v \<longleftrightarrow> v = Statement j"
  by (cases v) auto

lemma frag_stmts_empty [simp]: "frag_stmts {} {} = {}"
  by (simp add: frag_stmts_def)

lemma frag_stmts_Un:
  "frag_stmts (E1 \<union> E2) (K1 \<union> K2) = frag_stmts E1 K1 \<union> frag_stmts E2 K2"
  by (auto simp: frag_stmts_def)

lemma frag_stmts_mono:
  "E \<subseteq> E' \<Longrightarrow> K \<subseteq> K' \<Longrightarrow> frag_stmts E K \<subseteq> frag_stmts E' K'"
  by (auto simp: frag_stmts_def)

(* The four structural memberships frag_stmts_def unfolds to; downstream
   proofs cite these instead of re-unfolding the definition at each site. *)
lemma frag_stmts_E_srcI [intro]:
  "(Statement j, a, v) \<in> E \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_E_tgtI [intro]:
  "(u, a, Statement j) \<in> E \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_K_srcI:
  "(Statement j, act, ce, af) \<in> K \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_K_tgtI:
  "(u, act, ce, Statement j) \<in> K \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

text \<open>A fragment that cannot complete normally contains an explicit return edge.  This is the
  counterpart of the epilogue: where \<^const>\<open>falls_through\<close> fails, the body itself already carries
  an edge into \<^term>\<open>FunctionResult p\<close>, so the procedure keeps a return edge either way.\<close>
lemma compile_returns_edge:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> \<not> falls_through c
   \<Longrightarrow> \<exists>u e. (u, EA_Ret e p, FunctionResult p) \<in> E"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1': "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2': "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and res: "E = E1 \<union> E2"
    using Seq.prems(1) by (auto simp: Let_def split: prod.splits)
  show ?case
  proof (cases "falls_through c1")
    case False
    show ?thesis using Seq.IH(1)[OF c1' False] res by blast
  next
    case True
    have "\<not> falls_through c2" using Seq.prems(2) True by simp
    then show ?thesis using Seq.IH(2)[OF c2'] res by blast
  qed
next
  case (If b c1 c2)
  obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1': "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and res: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                    \<union> E1 \<union> E2"
    using If.prems(1) by (auto split: prod.splits)
  have "\<not> falls_through c1" using If.prems(2) by simp
  then show ?case using If.IH(1)[OF c1'] res by blast
next
  case (Return e)
  then show ?case by (auto split: prod.splits)
qed simp_all

lemma compile_frag_stmts_range:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> frag_stmts E K \<subseteq> {n..<n'} \<union> kstmt k"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and n': "n' = n2" and E: "E = E1 \<union> E2" and K: "K = K1 \<union> K2"
    by (auto simp: Let_def split: prod.splits)
  have i1: "n1 = n + csize c1" using compile_next_id[OF c1] .
  have i2: "n2 = n + csize c1 + csize c2" using compile_next_id[OF c2] by simp
  have r1: "frag_stmts E1 K1 \<subseteq> {n..<n1} \<union> {n + csize c1}" using Seq.IH(1)[OF c1] by simp
  have r2: "frag_stmts E2 K2 \<subseteq> {n + csize c1..<n2} \<union> kstmt k" using Seq.IH(2)[OF c2] .
  show ?case
    using r1 r2 i1 i2 csize_pos[of c2]
    unfolding E K n' by (simp only: frag_stmts_Un) auto
next
  case (If b c1 c2)
  from If.prems obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and n': "n' = n2"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> (E1 \<union> E2)"
    and K: "K = {} \<union> (K1 \<union> K2)"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have e2: "en2 = Statement n1" using compile_entry[OF c2] .
  have i1: "n1 = Suc n + csize c1" using compile_next_id[OF c1] .
  have i2: "n2 = n1 + csize c2" using compile_next_id[OF c2] .
  have r1: "frag_stmts E1 K1 \<subseteq> {Suc n..<n1} \<union> kstmt k" using If.IH(1)[OF c1] .
  have r2: "frag_stmts E2 K2 \<subseteq> {n1..<n2} \<union> kstmt k" using If.IH(2)[OF c2] .
  have guard: "frag_stmts {(Statement n, EA_Assume b, en1),
                           (Statement n, EA_AssumeNot b, en2)} {} \<subseteq> {n..<n2}"
    using e1 e2 i1 i2 csize_pos[of c1] csize_pos[of c2] by (auto simp: frag_stmts_def)
  have dec: "frag_stmts E K
               = frag_stmts {(Statement n, EA_Assume b, en1),
                             (Statement n, EA_AssumeNot b, en2)} {}
                 \<union> frag_stmts (E1 \<union> E2) (K1 \<union> K2)"
    unfolding E K by (rule frag_stmts_Un)
  have body: "frag_stmts (E1 \<union> E2) (K1 \<union> K2) \<subseteq> {n..<n2} \<union> kstmt k"
    using r1 r2 i1 i2 csize_pos[of c1] by (simp only: frag_stmts_Un) auto
  show ?case unfolding n' dec using guard body by blast
next
  case (While b c)
  from While.prems obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and n': "n' = n1"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    and K: "K = {} \<union> K1"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have i1: "n1 = Suc n + csize c" using compile_next_id[OF c1] .
  have r1: "frag_stmts E1 K1 \<subseteq> {Suc n..<n1} \<union> {n}" using While.IH[OF c1] by simp
  have guard: "frag_stmts {(Statement n, EA_Assume b, en1),
                           (Statement n, EA_AssumeNot b, k)} {} \<subseteq> {n..<n1} \<union> kstmt k"
    using e1 i1 csize_pos[of c] by (auto simp: frag_stmts_def)
  have dec: "frag_stmts E K
               = frag_stmts {(Statement n, EA_Assume b, en1),
                             (Statement n, EA_AssumeNot b, k)} {} \<union> frag_stmts E1 K1"
    unfolding E K by (rule frag_stmts_Un)
  show ?case unfolding n' dec using guard r1 i1 csize_pos[of c] by auto
qed (auto simp: frag_stmts_def split: option.splits)
text \<open>The procedure layout, packaged as an elimination rule: the body is compiled at \<open>n\<close> with the
  epilogue as its continuation, the entry bracket points at the body entry \<^term>\<open>Statement n\<close>,
  and the epilogue \<^term>\<open>Statement (n + csize (body decl))\<close> carries the implicit return.\<close>
lemma compile_procE:
  assumes "compile_proc \<Pi> p decl n = (n', E, K)"
  obtains Eb where
    "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
       = (n + csize (body decl), Statement n, Eb, K)"
    "E = insert (FunctionEntry p, EA_Nop, Statement n)
           (if falls_through (body decl)
            then insert (Statement (n + csize (body decl)), EA_Ret None p, FunctionResult p) Eb
            else Eb)"
    "n' = Suc (n + csize (body decl))"
proof -
  define r where "r = n + csize (body decl)"
  obtain m ben Eb Kb where
    cb: "compile \<Pi> p (body decl) (Statement r) n = (m, ben, Eb, Kb)"
    by (cases "compile \<Pi> p (body decl) (Statement r) n") auto
  have e: "ben = Statement n" using compile_entry[OF cb] .
  have i: "m = r" using compile_next_id[OF cb] unfolding r_def by simp
  from assms cb e i
  have "E = insert (FunctionEntry p, EA_Nop, Statement n)
              (if falls_through (body decl)
               then insert (Statement r, EA_Ret None p, FunctionResult p) Eb
               else Eb)"
    "K = Kb" "n' = Suc r"
    unfolding compile_proc_def r_def by (auto simp: Let_def)
  with cb e i show ?thesis unfolding r_def by (auto intro: that)

qed

subsection \<open>Finiteness\<close>

lemma compile_finite:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> finite E \<and> finite K"
  by (induction c arbitrary: k n n' en E K rule: com.induct)
     (auto simp: Let_def split: prod.splits)

lemma compile_proc_finite:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> finite E \<and> finite K"
  by (auto simp: compile_proc_def Let_def split: prod.splits dest: compile_finite)

lemma compile_procs_finite:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> finite E \<and> finite K"
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
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
      and E: "E = E0 \<union> E'" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    from compile_proc_finite[OF cp] Cons.IH[OF rest] show ?thesis
      unfolding E K by simp
  qed
qed

lemma compile_prog_finite:
  "finite (intra (compile_prog \<Pi> ps mnm main))
   \<and> finite (calls (compile_prog \<Pi> ps mnm main))"
  unfolding compile_prog_def
  by (auto simp: Let_def split: prod.splits
       dest: compile_procs_finite compile_proc_finite)

subsection \<open>Edge shapes for well-formedness\<close>

text \<open>Every emitted call edge targets a \<open>FunctionEntry\<close>; a call is never an intra edge.\<close>
lemma compile_call_ce_entry:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  by (induction c arbitrary: k n n' en E K)
     (auto simp: Let_def split: prod.splits if_splits)

text \<open>Edge endpoints: a source is always an allocated \<open>Statement\<close>; a target is an allocated
  \<open>Statement\<close>, the own \<^term>\<open>FunctionResult p\<close>, or the continuation.  The continuation
  disjunct is what continuation passing adds, and it is what lets the two \<^const>\<open>wf_cfg\<close>
  conditions below be discharged without carrying a side condition through the induction.\<close>
lemma compile_E_shape:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, a, v) \<in> E
   \<Longrightarrow> (\<exists>j. u = Statement j)
       \<and> (v = k \<or> v = FunctionResult p \<or> (\<exists>j. v = Statement j))"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and E: "E = E1 \<union> E2"
    by (auto simp: Let_def split: prod.splits)
  consider (L) "(u, a, v) \<in> E1" | (R) "(u, a, v) \<in> E2"
    using Seq.prems(2) E by auto
  then show ?case
  proof cases
    case L from Seq.IH(1)[OF c1 L] show ?thesis by auto
  next
    case R from Seq.IH(2)[OF c2 R] show ?thesis by auto
  qed
next
  case (If b c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> E1 \<union> E2"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have e2: "en2 = Statement n1" using compile_entry[OF c2] .
  consider (Guard) "(u, a, v) \<in> {(Statement n, EA_Assume b, en1),
                                 (Statement n, EA_AssumeNot b, en2)}"
    | (L) "(u, a, v) \<in> E1" | (R) "(u, a, v) \<in> E2"
    using If.prems(2) E by auto
  then show ?case
  proof cases
    case Guard then show ?thesis using e1 e2 by auto
  next
    case L from If.IH(1)[OF c1 L] show ?thesis by auto
  next
    case R from If.IH(2)[OF c2 R] show ?thesis by auto
  qed
next
  case (While b c)
  then obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  consider (Guard) "(u, a, v) \<in> {(Statement n, EA_Assume b, en1),
                                 (Statement n, EA_AssumeNot b, k)}"
    | (Body) "(u, a, v) \<in> E1"
    using While.prems(2) E by auto
  then show ?case
  proof cases
    case Guard then show ?thesis using e1 by auto
  next
    case Body from While.IH[OF c1 Body] show ?thesis by auto
  qed
qed (auto split: prod.splits option.splits)

text \<open>No intra edge enters a \<open>FunctionEntry\<close> node.  \<^const>\<open>SKIP\<close> emits an edge into its
  continuation, so at command level this depends on the continuation not being one; at
  procedure level the continuation is the epilogue and the hypothesis is immediate.\<close>
lemma compile_intra_tgt_not_entry:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "(u, a, v) \<in> E"
    and "\<forall>r. k \<noteq> FunctionEntry r"
  shows "v \<noteq> FunctionEntry q"
  using compile_E_shape[OF assms(1,2)] assms(3) by auto

text \<open>Every \<open>EA_Ret\<close> edge lands on the matching \<open>FunctionResult\<close> --- the enclosing
  procedure name in the action equals the one in the target node.\<close>
lemma compile_ret_wf:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E
   \<Longrightarrow> \<forall>r. k \<noteq> FunctionResult r \<Longrightarrow> v = FunctionResult q"
  by (induction c arbitrary: k n n' en E K)
     (auto simp: Let_def split: prod.splits if_splits)

lemma compile_proc_call_ce_entry:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  by (auto simp: compile_proc_def Let_def split: prod.splits
       dest: compile_call_ce_entry)

lemma compile_proc_intra_tgt_not_entry:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E \<Longrightarrow> v \<noteq> FunctionEntry q"
  by (auto simp: compile_proc_def Let_def split: prod.splits if_splits
       dest: compile_E_shape compile_entry)

lemma compile_proc_ret_wf:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E
   \<Longrightarrow> v = FunctionResult q"
  by (auto simp: compile_proc_def Let_def split: prod.splits if_splits
       dest: compile_ret_wf)


lemma compile_procs_call_ce_entry:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems(1) obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    from Cons.prems(2) K
    show ?thesis using compile_proc_call_ce_entry[OF cp] Cons.IH[OF rest] by auto
  qed
qed

lemma compile_procs_intra_tgt_not_entry:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E \<Longrightarrow> v \<noteq> FunctionEntry q"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems(1) obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and E: "E = E0 \<union> E'"
      by (auto split: prod.splits)
    from Cons.prems(2) E
    show ?thesis using compile_proc_intra_tgt_not_entry[OF cp] Cons.IH[OF rest] by auto
  qed
qed

lemma compile_procs_ret_wf:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E \<Longrightarrow> v = FunctionResult q"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems(1) obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and E: "E = E0 \<union> E'"
      by (auto split: prod.splits)
    from Cons.prems(2) E
    show ?thesis using compile_proc_ret_wf[OF cp] Cons.IH[OF rest] by auto
  qed
qed

subsection \<open>The compiled program is well-formed\<close>

theorem compile_prog_wf: "wf_cfg (compile_prog \<Pi> ps mnm main)"
proof -
  obtain n1 Eprocs Kprocs where
    procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)" by (metis prod_cases3)
  obtain n2 Emain Kmain where
    mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    by (metis prod_cases3)
  have g: "compile_prog \<Pi> ps mnm main =
             \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm,
              checks = (\<lambda>(u, a, v). (u, ea_check_cond a)) ` Set.filter (\<lambda>(u, a, v). is_EA_Check a) (Eprocs \<union> Emain) \<rparr>"
    unfolding compile_prog_def by (simp add: procs mainc Let_def)
  show ?thesis
    unfolding wf_cfg_def g
  proof (intro conjI allI impI)
    fix u act ce af assume "(u, act, ce, af) \<in> calls \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm,
        checks = (\<lambda>(u, a, v). (u, ea_check_cond a)) ` Set.filter (\<lambda>(u, a, v). is_EA_Check a) (Eprocs \<union> Emain)\<rparr>"
    then have "(u, act, ce, af) \<in> Kprocs \<or> (u, act, ce, af) \<in> Kmain" by simp
    then show "\<exists>p. ce = FunctionEntry p"
      using compile_procs_call_ce_entry[OF procs] compile_proc_call_ce_entry[OF mainc] by blast
  next
    fix u a v p assume "(u, a, v) \<in> intra \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm,
        checks = (\<lambda>(u, a, v). (u, ea_check_cond a)) ` Set.filter (\<lambda>(u, a, v). is_EA_Check a) (Eprocs \<union> Emain)\<rparr>"
    then have "(u, a, v) \<in> Eprocs \<or> (u, a, v) \<in> Emain" by simp
    then show "v \<noteq> FunctionEntry p"
      using compile_procs_intra_tgt_not_entry[OF procs] compile_proc_intra_tgt_not_entry[OF mainc]
      by blast
  next
    fix u e p v assume "(u, EA_Ret e p, v) \<in> intra \<lparr>intra = Eprocs \<union> Emain,
        calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm,
        checks = (\<lambda>(u, a, v). (u, ea_check_cond a)) ` Set.filter (\<lambda>(u, a, v). is_EA_Check a) (Eprocs \<union> Emain)\<rparr>"
    then have "(u, EA_Ret e p, v) \<in> Eprocs \<or> (u, EA_Ret e p, v) \<in> Emain" by simp
    then show "v = FunctionResult p"
      using compile_procs_ret_wf[OF procs] compile_proc_ret_wf[OF mainc] by blast
  qed
qed


subsection \<open>Call-entry transfer agrees with the source semantics\<close>

text \<open>The compiler emits, for a call to a declared procedure, a single \<open>CallEdge\<close> carrying
  the callee's formal parameters (looked up in the procedure table) and the actual argument
  expressions.\<close>
lemma compile_Call_calls:
  assumes "\<Pi> q = Some decl"
  shows "snd (snd (snd (compile \<Pi> p (Call dst q actuals) k n)))
           = {(Statement n, CallEdge dst (formals decl) actuals, FunctionEntry q, k)}"
  using assms by simp
text \<open>The caller-side entry transfer \<^const>\<open>call_enter\<close> on that edge produces exactly the
  callee-entry store of the source \<^const>\<open>pstep\<close> \<open>Call\<close> rule: the actuals are evaluated in the
  caller store \<open>s\<close>, the callee locals are reset by \<^const>\<open>enter_state\<close>, and the values are
  \<^const>\<open>bind_formals\<close>-bound to the formals.  The resulting store is exactly the
  source \<open>Call\<close> callee store used by the local-trace call rule.\<close>
lemma call_enter_eq_source_call_store:
  "call_enter source_global (CallEdge dst (formals decl) actuals) s
     = bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals)
       (enter_state source_global s)"
  by (simp add: call_enter_CallEdge)

text \<open>Combined: traversing the compiled call edge lands the callee at the source callee-entry
  store.\<close>
lemma compile_call_enter_eq_source:
  assumes "\<Pi> q = Some decl"
    and "(cs, CallEdge dst pars actuals, FunctionEntry q, af)
           \<in> snd (snd (snd (compile \<Pi> p (Call dst q actuals) k n)))"
  shows "call_enter source_global (CallEdge dst pars actuals) s
           = bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals)
             (enter_state source_global s)"
proof -
  from assms(2) have "pars = formals decl" by (simp add: assms(1))
  then show ?thesis by (simp add: call_enter_eq_source_call_store)
qed


subsection \<open>Return transfer agrees with the source semantics\<close>

text \<open>The \<open>EA_Ret\<close> edge publishes the return value into \<^const>\<open>ret_var\<close> exactly as the
  source \<open>Return\<close> step: \<open>Some e\<close> writes \<open>aval e\<close>, \<open>None\<close> leaves the reserved local.\<close>
lemma return_publishes_ret_var:
  assumes "pstep source_global \<Pi> (Return e, s, frs) (Unwind, s', frs)"
  shows "s' \<in> edge_step (EA_Ret e p) s"
  using assms by (cases e) auto

text \<open>The caller-side combine \<^const>\<open>combine_collect\<close> reproduces the store built by the source
  activation-frame unwind \<open>UnwindAct\<close>: callee globals kept, caller locals restored, the
  callee \<^const>\<open>ret_var\<close> written into the destination.  \<open>caller\<close> is the saved caller store in
  the activation frame, \<open>callee\<close> the callee-exit store.\<close>
lemma combine_collect_eq_source_unwind:
  assumes "pstep source_global \<Pi> (Seq Unwind Restore, callee, Frame caller dst # frs)
                    (SKIP, s', frs)"
  shows "s' = combine_collect source_global dst caller callee"
  using assms by (auto simp: combine_collect_def)

text \<open>The same combine also matches the normal-completion \<open>Restore\<close> step, which fires once the
  callee body has reduced to \<^const>\<open>SKIP\<close>: the combined store is fixed by the destination and stores.\<close>
lemma combine_collect_eq_source_restore:
  assumes "pstep source_global \<Pi> (Restore, callee, Frame caller dst # frs) (SKIP, s', frs)"
  shows "s' = combine_collect source_global dst caller callee"
  using assms by (auto simp: combine_collect_def)


end
