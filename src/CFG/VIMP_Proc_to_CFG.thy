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
    \<^item> \<^const>\<open>Seq\<close> needs no connecting \<open>EA_Nop\<close>: \<open>c1\<close>'s continuation \<^emph>\<open>is\<close> \<open>c2\<close>'s
      entry;
    \<^item> \<^const>\<open>If\<close> allocates no merge node: both branches receive the same \<open>k\<close>, and the join
      happens at \<open>k\<close>, which is the program point after the conditional;
    \<^item> \<^const>\<open>While\<close> needs no back-edge node: the body's continuation is the loop head;
    \<^item> \<^const>\<open>Return\<close> ignores \<open>k\<close> and emits only its \<open>EA_Ret\<close> edge, so no unreachable
      continuation node is invented;
    \<^item> \<^const>\<open>Call\<close> resumes at \<open>k\<close>, so the resume point is the following program point.
  \<^const>\<open>Restore\<close> and \<^const>\<open>Unwind\<close> are runtime-only (excluded by \<^const>\<open>source_com\<close>),
  so their clauses are never exercised for a source program.  They stay transparent: one node
  and a \<open>EA_Nop\<close> to the continuation.  Making them dead ends instead would cost the
  unconditional form of \<open>compile_prog_entry_cfg_reaches_exit\<close> for no gain, since no
  source program reaches these clauses.\<close>

text \<open>
  A call edge into an undeclared procedure carries no formals: \<^const>\<open>Call\<close> compiles
  against whatever \<^term>\<open>\<Pi> q\<close> says at compile time, declared or not, so its formal
  list is this classifier rather than a lookup that could fail. Naming it lets lemma
  statements about compiled call edges cite \<open>call_formals\<close> instead of restating the
  case split; the \<open>[simp]\<close> tag keeps it transparent to existing automation.
\<close>
definition call_formals :: "proc_table \<Rightarrow> pname \<Rightarrow> vname list" where
  [simp]: "call_formals \<Pi> q =
    (case \<Pi> q of
       Some decl \<Rightarrow> formals decl
     | None \<Rightarrow> Code.abort (STR ''call_formals: call to an undeclared procedure'') (\<lambda>_. []))"

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
     (case special_table q of
        Some desc \<Rightarrow>
          (case classify_special desc actuals of
             None \<Rightarrow> (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})
           | Some sc \<Rightarrow>
               (case dst of
                  Some x \<Rightarrow>
                    (Suc n, Statement n, {(Statement n, EA_Special sc x, k)}, {})
                | None \<Rightarrow>
                    (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})))
      | None \<Rightarrow>
          (Suc n, Statement n, {},
           {(Statement n,
             CallEdge dst (call_formals \<Pi> q) actuals,
             FunctionEntry q, k)}))"
| "compile \<Pi> p (Return e) k n =
     (Suc n, Statement n, {(Statement n, EA_Ret e p, FunctionResult p)}, {})"
| "compile \<Pi> p Restore k n =
     (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})"
| "compile \<Pi> p Unwind k n =
     (Suc n, Statement n, {(Statement n, EA_Nop, k)}, {})"

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

lemma set_com_stmt_post_order:
  "set (com_stmt_post_order n c) = Statement ` {n ..< n + csize c}"
proof (induction c arbitrary: n)
  case (Seq c1 c2)
  have "{n ..< n + csize c1} \<union> {n + csize c1 ..< n + csize c1 + csize c2}
          = {n ..< n + (csize c1 + csize c2)}"
    by auto
  then show ?case using Seq by (simp flip: image_Un add: add.assoc)
next
  case (If b c1 c2)
  have "insert n ({Suc n ..< Suc (n + csize c1)}
          \<union> {Suc (n + csize c1) ..< Suc (n + csize c1 + csize c2)})
          = {n ..< Suc (n + (csize c1 + csize c2))}"
    by auto
  then show ?case using If by (auto simp flip: image_Un image_insert)
next
  case (While b c)
  have "insert n {Suc n ..< Suc (n + csize c)} = {n ..< Suc (n + csize c)}" by auto
  then show ?case using While by (auto simp flip: image_insert)
qed auto

lemma distinct_com_stmt_post_order: "distinct (com_stmt_post_order n c)"
  by (induction c arbitrary: n) (auto simp: set_com_stmt_post_order)

subsection \<open>Procedure and program compilation\<close>

text \<open>A procedure wraps its body between \<open>FunctionEntry p\<close> and \<open>FunctionResult p\<close>.  The body
  is compiled with the \<^emph>\<open>epilogue\<close> node \<open>Statement r\<close> as its continuation, and the epilogue
  carries the implicit \<open>EA_Ret None p\<close>: normal fall-through returns without a value.  A value is
  published only by an explicit source \<open>Return e\<close>, which compiles to its own
  \<open>EA_Ret (Some e) p\<close> edge inside the body.

  The epilogue exists so that every edge into \<open>FunctionResult p\<close> is a return edge.  Passing
  \<open>FunctionResult p\<close> directly as the body continuation would let a trailing assignment target
  the result node.  It is allocated \<^emph>\<open>after\<close> the body, so statement indices stay in source
  order and \<open>r\<close> lies inside the procedure's own counter range --- which is what keeps edge
  locality a statement about one fragment.

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
          (n2, Emain, Kmain) = compile_proc \<Pi> mnm (\<lparr>formals = [], body = main\<rparr>) n1
      in \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm,
           checks = (\<lambda>(u, a, v). (u, ea_check_cond a))
             ` Set.filter (\<lambda>(u, a, v). is_EA_Check a) (Eprocs \<union> Emain) \<rparr>)"

text \<open>Decomposition of a whole compiled program into the callee pass and the \<open>main\<close>
  fragment.\<close>
lemma compile_prog_intra_split:
  obtains n1 Eprocs Kprocs n2 Emain Kmain where
    "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    "compile_proc \<Pi> mnm \<lparr>formals = [], body = main\<rparr> n1 = (n2, Emain, Kmain)"
    "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
    "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
proof -
  obtain n1 Eprocs Kprocs where procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    by (rule prod_cases3)
  obtain n2 Emain Kmain
    where mainc: "compile_proc \<Pi> mnm \<lparr>formals = [], body = main\<rparr> n1 = (n2, Emain, Kmain)"
    by (rule prod_cases3)
  show ?thesis
    by (rule that[OF procs mainc]) (simp_all add: compile_prog_def procs mainc Let_def)
qed

lemma cfg_entry_compile_prog [simp]:
  "cfg_entry (compile_prog \<Pi> ps mnm main) = FunctionEntry mnm"
  by (simp add: compile_prog_def Let_def split: prod.splits)

lemma cfg_exit_compile_prog [simp]:
  "cfg_exit (compile_prog \<Pi> ps mnm main) = FunctionResult mnm"
  by (simp add: cfg_exit_def)

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
     (auto simp: Let_def split: prod.splits option.splits)

subsection \<open>Fragment decomposition\<close>

text \<open>The composite clauses, packaged as elimination rules.  Every consumer of \<^const>\<open>compile\<close>
  needs the same destructuring --- sub-fragments, their base counters, and the edge split ---
  and \<^const>\<open>csize\<close> makes the sub-counters explicit, so no auxiliary equation has to be
  carried along.\<close>

lemma compile_SeqE [elim]:
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

lemma compile_IfE [elim]:
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

lemma compile_WhileE [elim]:
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

text \<open>The procedure layout, packaged the same way: the body is compiled at \<open>n\<close> with the
  epilogue as its continuation, the entry bracket points at the body entry \<^term>\<open>Statement n\<close>,
  and the epilogue \<^term>\<open>Statement (n + csize (body decl))\<close> carries the implicit return.\<close>
lemma compile_procE [elim]:
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
    by (rule prod_cases4)
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

subsection \<open>Call-source uniqueness\<close>

text \<open>
  Each compiled fragment allocates its \<open>Call\<close> leaves at distinct, freshly claimed
  \<open>Statement\<close> indices, so a compiled \<open>calls\<close> set never has two different edges out of
  the same source node.  This is a structural fact about the compiler, not about
  \<^const>\<open>wf_cfg\<close> (which is deliberately compiler-agnostic) or about any particular
  program: a hand-built CFG whose source node has two distinct outgoing call edges can
  still violate it, but no \<^const>\<open>compile_prog\<close> output can, and it is what lets a
  context-routing hook resolve the one call at a node from the source node alone.
\<close>

lemma compile_calls_source_range:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>j. u = Statement j \<and> n \<le> j \<and> j < n'"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and n': "n' = n2" and K: "K = K1 \<union> K2"
    by (auto simp: Let_def split: prod.splits)
  have i1: "n1 = n + csize c1" using compile_next_id[OF c1] .
  have i2: "n2 = n + csize c1 + csize c2" using compile_next_id[OF c2] by simp
  from Seq.prems(2) K consider (L) "(u, act, ce, af) \<in> K1" | (R) "(u, act, ce, af) \<in> K2" by auto
  then show ?case
  proof cases
    case L with Seq.IH(1)[OF c1 L] i1 i2 show ?thesis unfolding n' by auto
  next
    case R with Seq.IH(2)[OF c2 R] i1 i2 show ?thesis unfolding n' by auto
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and n': "n' = n2" and K: "K = K1 \<union> K2"
    by (auto split: prod.splits)
  have i1: "n1 = Suc n + csize c1" using compile_next_id[OF c1] by simp
  have i2: "n2 = n1 + csize c2" using compile_next_id[OF c2] .
  from If.prems(2) K consider (L) "(u, act, ce, af) \<in> K1" | (R) "(u, act, ce, af) \<in> K2" by auto
  then show ?case
  proof cases
    case L with If.IH(1)[OF c1 L] i1 i2 show ?thesis unfolding n' by auto
  next
    case R with If.IH(2)[OF c2 R] i1 i2 show ?thesis unfolding n' by auto
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and n': "n' = n1" and K: "K = K1"
    by (auto split: prod.splits)
  from While.prems(2) K have "(u, act, ce, af) \<in> K1" by simp
  with While.IH[OF c1] show ?case unfolding n' by auto
qed (auto split: prod.splits option.splits)

lemma compile_calls_source_unique:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, ca1, ce1, af1) \<in> K \<Longrightarrow> (u, ca2, ce2, af2) \<in> K
   \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      cc1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and cc2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and K: "K = K1 \<union> K2"
    by (auto simp: Let_def split: prod.splits)
  have i1: "n1 = n + csize c1" using compile_next_id[OF cc1] .
  have low: "\<And>u' act' ce' af'. (u', act', ce', af') \<in> K1 \<Longrightarrow> \<exists>j. u' = Statement j \<and> j < n1"
    using compile_calls_source_range[OF cc1] i1 by blast
  have high: "\<And>u' act' ce' af'. (u', act', ce', af') \<in> K2 \<Longrightarrow> \<exists>j. u' = Statement j \<and> n1 \<le> j"
    using compile_calls_source_range[OF cc2]
    using i1 by blast
  have not_both: "\<And>u' act1' ce1' af1' act2' ce2' af2'.
      (u', act1', ce1', af1') \<in> K1 \<Longrightarrow> (u', act2', ce2', af2') \<in> K2 \<Longrightarrow> False"
    using low high by fastforce
  from Seq.prems(2) K have m1: "(u, ca1, ce1, af1) \<in> K1 \<or> (u, ca1, ce1, af1) \<in> K2" by auto
  from Seq.prems(3) K have m2: "(u, ca2, ce2, af2) \<in> K1 \<or> (u, ca2, ce2, af2) \<in> K2" by auto
  consider (LL) "(u, ca1, ce1, af1) \<in> K1" "(u, ca2, ce2, af2) \<in> K1"
         | (RR) "(u, ca1, ce1, af1) \<in> K2" "(u, ca2, ce2, af2) \<in> K2"
         | (LR) "(u, ca1, ce1, af1) \<in> K1" "(u, ca2, ce2, af2) \<in> K2"
         | (RL) "(u, ca1, ce1, af1) \<in> K2" "(u, ca2, ce2, af2) \<in> K1"
    using m1 m2 by blast
  then show ?case
  proof cases
    case LL then show ?thesis using Seq.IH(1)[OF cc1] by blast
  next
    case RR then show ?thesis using Seq.IH(2)[OF cc2] by blast
  next
    case LR then show ?thesis using not_both by blast
  next
    case RL then show ?thesis using not_both by blast
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      cc1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and cc2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and K: "K = K1 \<union> K2"
    by (auto split: prod.splits)
  have low: "\<And>u' act' ce' af'. (u', act', ce', af') \<in> K1 \<Longrightarrow> \<exists>j. u' = Statement j \<and> j < n1"
    using compile_calls_source_range[OF cc1] by fastforce
  have high: "\<And>u' act' ce' af'. (u', act', ce', af') \<in> K2 \<Longrightarrow> \<exists>j. u' = Statement j \<and> n1 \<le> j"
    using compile_calls_source_range[OF cc2] by fastforce
  have not_both: "\<And>u' act1' ce1' af1' act2' ce2' af2'.
      (u', act1', ce1', af1') \<in> K1 \<Longrightarrow> (u', act2', ce2', af2') \<in> K2 \<Longrightarrow> False"
    using low high by fastforce
  from If.prems(2) K have m1: "(u, ca1, ce1, af1) \<in> K1 \<or> (u, ca1, ce1, af1) \<in> K2" by auto
  from If.prems(3) K have m2: "(u, ca2, ce2, af2) \<in> K1 \<or> (u, ca2, ce2, af2) \<in> K2" by auto
  consider (LL) "(u, ca1, ce1, af1) \<in> K1" "(u, ca2, ce2, af2) \<in> K1"
         | (RR) "(u, ca1, ce1, af1) \<in> K2" "(u, ca2, ce2, af2) \<in> K2"
         | (LR) "(u, ca1, ce1, af1) \<in> K1" "(u, ca2, ce2, af2) \<in> K2"
         | (RL) "(u, ca1, ce1, af1) \<in> K2" "(u, ca2, ce2, af2) \<in> K1"
    using m1 m2 by blast
  then show ?case
  proof cases
    case LL then show ?thesis using If.IH(1)[OF cc1] by blast
  next
    case RR then show ?thesis using If.IH(2)[OF cc2] by blast
  next
    case LR then show ?thesis using not_both by blast
  next
    case RL then show ?thesis using not_both by blast
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
      cc1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and K: "K = K1"
    by (auto split: prod.splits)
  from While.prems(2) K have "(u, ca1, ce1, af1) \<in> K1" by simp
  moreover from While.prems(3) K have "(u, ca2, ce2, af2) \<in> K1" by simp
  ultimately show ?case using While.IH[OF cc1] by blast
qed (auto split: prod.splits option.splits)

lemma compile_proc_counter_mono:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> n \<le> n'"
  by auto

lemma compile_proc_calls_source_range:
  assumes "compile_proc \<Pi> p decl n = (n', E, K)" and "(u, act, ce, af) \<in> K"
  shows "\<exists>j. u = Statement j \<and> n \<le> j \<and> j < n'"
proof -
  from assms(1) obtain Eb where
      body: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
               = (n + csize (body decl), Statement n, Eb, K)"
    and n': "n' = Suc (n + csize (body decl))"
    by (rule compile_procE)
  from compile_calls_source_range[OF body assms(2)] show ?thesis unfolding n' by auto
qed

lemma compile_proc_calls_source_unique:
  assumes "compile_proc \<Pi> p decl n = (n', E, K)"
    and "(u, ca1, ce1, af1) \<in> K" and "(u, ca2, ce2, af2) \<in> K"
  shows "ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
proof -
  from assms(1) obtain Eb where
    body: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
             = (n + csize (body decl), Statement n, Eb, K)"
    by (rule compile_procE)
  from compile_calls_source_unique[OF body assms(2,3)] show ?thesis .
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
    from compile_proc_counter_mono[OF cp] Cons.IH[OF rest] n' show ?thesis by simp
  qed
qed

text \<open>Every edge of a \<^const>\<open>compile_procs\<close> pass comes from one declared member's
  \<^const>\<open>compile_proc\<close> fragment, compiled at some offset inside the pass's counter range;
  conversely every declared member contributes such a fragment.  The three facts below
  are what every structural property of a pass reduces to.\<close>
lemma compile_procs_intra_origin:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "e \<in> E"
  shows "\<exists>p decl m m' Ep Kp. p \<in> set ps \<and> \<Pi> p = Some decl
           \<and> compile_proc \<Pi> p decl m = (m', Ep, Kp) \<and> n \<le> m \<and> m' \<le> n' \<and> e \<in> Ep"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have "compile_procs \<Pi> qs n = (n', E, K)" by simp
    from Cons.IH[OF this Cons.prems(2)] show ?thesis by (blast intro: list.set_intros(2))
  next
    case (Some declq)
    from Cons.prems(1) Some obtain n1 Eq Kq n2 E' K' where
        cq: "compile_proc \<Pi> q declq n = (n1, Eq, Kq)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and eq: "n' = n2" "E = Eq \<union> E'"
      by (auto split: prod.splits)
    have mono: "n \<le> n1" "n1 \<le> n2"
      using compile_proc_counter_mono[OF cq] compile_procs_counter_mono[OF rest] .
    show ?thesis
    proof (cases "e \<in> Eq")
      case True
      have "q \<in> set (q # qs) \<and> \<Pi> q = Some declq \<and> compile_proc \<Pi> q declq n = (n1, Eq, Kq)
              \<and> n \<le> n \<and> n1 \<le> n' \<and> e \<in> Eq"
        using Some cq mono(2) eq(1) True by simp
      then show ?thesis by blast
    next
      case False
      with Cons.prems(2) eq(2) have "e \<in> E'" by simp
      from Cons.IH[OF rest this] obtain p decl m m' Ep Kp where
        "p \<in> set qs" "\<Pi> p = Some decl" "compile_proc \<Pi> p decl m = (m', Ep, Kp)"
        "n1 \<le> m" "m' \<le> n2" "e \<in> Ep" by blast
      with mono(1) eq(1)
      have "p \<in> set (q # qs) \<and> \<Pi> p = Some decl \<and> compile_proc \<Pi> p decl m = (m', Ep, Kp)
              \<and> n \<le> m \<and> m' \<le> n' \<and> e \<in> Ep"
        by (auto intro: le_trans)
      then show ?thesis by blast
    qed
  qed
qed

lemma compile_procs_calls_origin:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "e \<in> K"
  shows "\<exists>p decl m m' Ep Kp. p \<in> set ps \<and> \<Pi> p = Some decl
           \<and> compile_proc \<Pi> p decl m = (m', Ep, Kp) \<and> n \<le> m \<and> m' \<le> n' \<and> e \<in> Kp"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have "compile_procs \<Pi> qs n = (n', E, K)" by simp
    from Cons.IH[OF this Cons.prems(2)] show ?thesis by (blast intro: list.set_intros(2))
  next
    case (Some declq)
    from Cons.prems(1) Some obtain n1 Eq Kq n2 E' K' where
        cq: "compile_proc \<Pi> q declq n = (n1, Eq, Kq)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and eq: "n' = n2" "K = Kq \<union> K'"
      by (auto split: prod.splits)
    have mono: "n \<le> n1" "n1 \<le> n2"
      using compile_proc_counter_mono[OF cq] compile_procs_counter_mono[OF rest] .
    show ?thesis
    proof (cases "e \<in> Kq")
      case True
      have "q \<in> set (q # qs) \<and> \<Pi> q = Some declq \<and> compile_proc \<Pi> q declq n = (n1, Eq, Kq)
              \<and> n \<le> n \<and> n1 \<le> n' \<and> e \<in> Kq"
        using Some cq mono(2) eq(1) True by simp
      then show ?thesis by blast
    next
      case False
      with Cons.prems(2) eq(2) have "e \<in> K'" by simp
      from Cons.IH[OF rest this] obtain p decl m m' Ep Kp where
        "p \<in> set qs" "\<Pi> p = Some decl" "compile_proc \<Pi> p decl m = (m', Ep, Kp)"
        "n1 \<le> m" "m' \<le> n2" "e \<in> Kp" by blast
      with mono(1) eq(1)
      have "p \<in> set (q # qs) \<and> \<Pi> p = Some decl \<and> compile_proc \<Pi> p decl m = (m', Ep, Kp)
              \<and> n \<le> m \<and> m' \<le> n' \<and> e \<in> Kp"
        by (auto intro: le_trans)
      then show ?thesis by blast
    qed
  qed
qed

lemma compile_procs_member:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "p \<in> set ps" and "\<Pi> p = Some decl"
  shows "\<exists>m m' Ep Kp. compile_proc \<Pi> p decl m = (m', Ep, Kp)
           \<and> n \<le> m \<and> m' \<le> n' \<and> Ep \<subseteq> E \<and> Kp \<subseteq> K"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have "compile_procs \<Pi> qs n = (n', E, K)" "p \<in> set qs" by auto
    then show ?thesis using Cons.IH Cons.prems(3) by blast
  next
    case (Some declq)
    from Cons.prems(1) Some obtain n1 Eq Kq n2 E' K' where
        cq: "compile_proc \<Pi> q declq n = (n1, Eq, Kq)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and eq: "n' = n2" "E = Eq \<union> E'" "K = Kq \<union> K'"
      by (auto split: prod.splits)
    have mono: "n \<le> n1" "n1 \<le> n2"
      using compile_proc_counter_mono[OF cq] compile_procs_counter_mono[OF rest] .
    show ?thesis
    proof (cases "p = q")
      case True
      with Cons.prems(3) Some have "decl = declq" by simp
      with True cq mono(2) eq
      have "compile_proc \<Pi> p decl n = (n1, Eq, Kq) \<and> n \<le> n \<and> n1 \<le> n' \<and> Eq \<subseteq> E \<and> Kq \<subseteq> K"
        by simp
      then show ?thesis by blast
    next
      case False
      with Cons.prems(2) have "p \<in> set qs" by simp
      from Cons.IH[OF rest this Cons.prems(3)] obtain m m' Ep Kp where
        "compile_proc \<Pi> p decl m = (m', Ep, Kp)" "n1 \<le> m" "m' \<le> n2" "Ep \<subseteq> E'" "Kp \<subseteq> K'"
        by blast
      with mono(1) eq
      have "compile_proc \<Pi> p decl m = (m', Ep, Kp) \<and> n \<le> m \<and> m' \<le> n' \<and> Ep \<subseteq> E \<and> Kp \<subseteq> K"
        by (auto intro: le_trans)
      then show ?thesis by blast
    qed
  qed
qed

lemma compile_procs_calls_source_range:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "(u, act, ce, af) \<in> K"
  shows "\<exists>j. u = Statement j \<and> n \<le> j \<and> j < n'"
  using compile_procs_calls_origin[OF assms] compile_proc_calls_source_range by fastforce

lemma compile_procs_calls_source_unique:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, ca1, ce1, af1) \<in> K \<Longrightarrow> (u, ca2, ce2, af2) \<in> K
   \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
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
    have not_both: "\<And>u' act1' ce1' af1' act2' ce2' af2'.
        (u', act1', ce1', af1') \<in> K0 \<Longrightarrow> (u', act2', ce2', af2') \<in> K' \<Longrightarrow> False"
      using compile_proc_calls_source_range[OF cp]
            compile_procs_calls_source_range[OF rest]
      by fastforce
    from Cons.prems(2) K have m1: "(u, ca1, ce1, af1) \<in> K0 \<or> (u, ca1, ce1, af1) \<in> K'" by auto
    from Cons.prems(3) K have m2: "(u, ca2, ce2, af2) \<in> K0 \<or> (u, ca2, ce2, af2) \<in> K'" by auto
    consider (LL) "(u, ca1, ce1, af1) \<in> K0" "(u, ca2, ce2, af2) \<in> K0"
           | (RR) "(u, ca1, ce1, af1) \<in> K'" "(u, ca2, ce2, af2) \<in> K'"
           | (LR) "(u, ca1, ce1, af1) \<in> K0" "(u, ca2, ce2, af2) \<in> K'"
           | (RL) "(u, ca1, ce1, af1) \<in> K'" "(u, ca2, ce2, af2) \<in> K0"
      using m1 m2 by blast
    then show ?thesis
    proof cases
      case LL then show ?thesis using compile_proc_calls_source_unique[OF cp] by blast
    next
      case RR then show ?thesis using Cons.IH[OF rest] by blast
    next
      case LR then show ?thesis using not_both by blast
    next
      case RL then show ?thesis using not_both by blast
    qed
  qed
qed

text \<open>Whole-program call-source uniqueness: the fact a routed-context analysis needs
  to resolve the formals of the one call at a node without ambiguity, for any
  \<^const>\<open>compile_prog\<close> output. Combines the declared-procedures pass and the \<open>main\<close>
  pass the same way the well-formedness theorem combines its own two passes.\<close>

theorem compile_prog_calls_source_unique:
  assumes "(u, ca1, ce1, af1) \<in> calls (compile_prog \<Pi> ps mnm main)"
    and "(u, ca2, ce2, af2) \<in> calls (compile_prog \<Pi> ps mnm main)"
  shows "ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm \<lparr>formals = [], body = main\<rparr> n1 = (n2, Emain, Kmain)"
    and g: "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have not_both: "\<And>u' act1' ce1' af1' act2' ce2' af2'.
      (u', act1', ce1', af1') \<in> Kprocs \<Longrightarrow> (u', act2', ce2', af2') \<in> Kmain \<Longrightarrow> False"
    using compile_procs_calls_source_range[OF procs] compile_proc_calls_source_range[OF mainc]
    by fastforce
  from assms show ?thesis unfolding g
    using compile_procs_calls_source_unique[OF procs] compile_proc_calls_source_unique[OF mainc]
      not_both by (elim UnE) (blast | (drule not_both; blast))+
qed


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

lemma frag_stmts_E_srcI [intro]:
  "(Statement j, a, v) \<in> E \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_E_tgtI [intro]:
  "(u, a, Statement j) \<in> E \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_K_srcI [intro]:
  "(Statement j, act, ce, af) \<in> K \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_K_tgtI [intro]:
  "(u, act, ce, Statement j) \<in> K \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

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
  show ?case unfolding n' dec using guard r1 i1 csize_pos[of c] by force 
qed (auto simp: frag_stmts_def split: option.splits)
subsection \<open>Finiteness\<close>

lemma compile_finite:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> finite E \<and> finite K"
  by (induction c arbitrary: k n n' en E K rule: com.induct)
     (auto simp: Let_def split: prod.splits option.splits)

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
     (auto simp: Let_def split: prod.splits if_splits option.splits)

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

text \<open>Every \<open>EA_Ret\<close> edge lands on the matching \<open>FunctionResult\<close> --- the enclosing
  procedure name in the action equals the one in the target node.\<close>
lemma compile_ret_wf:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E
   \<Longrightarrow> \<forall>r. k \<noteq> FunctionResult r \<Longrightarrow> v = FunctionResult q"
  by (induction c arbitrary: k n n' en E K)
     (auto simp: Let_def split: prod.splits if_splits option.splits)

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
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  using compile_procs_calls_origin compile_proc_call_ce_entry by blast

lemma compile_procs_intra_tgt_not_entry:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E \<Longrightarrow> v \<noteq> FunctionEntry q"
  using compile_procs_intra_origin compile_proc_intra_tgt_not_entry by blast

lemma compile_procs_ret_wf:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E \<Longrightarrow> v = FunctionResult q"
  using compile_procs_intra_origin compile_proc_ret_wf by blast

subsection \<open>The compiled program is well-formed\<close>

theorem compile_prog_wf: "wf_cfg (compile_prog \<Pi> ps mnm main)"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm \<lparr>formals = [], body = main\<rparr> n1 = (n2, Emain, Kmain)"
    and g: "intra (compile_prog \<Pi> ps mnm main) = Eprocs \<union> Emain"
           "calls (compile_prog \<Pi> ps mnm main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  show ?thesis
    unfolding wf_cfg_def g
    using compile_procs_call_ce_entry[OF procs] compile_proc_call_ce_entry[OF mainc]
      compile_procs_intra_tgt_not_entry[OF procs] compile_proc_intra_tgt_not_entry[OF mainc]
      compile_procs_ret_wf[OF procs] compile_proc_ret_wf[OF mainc]
    by (intro conjI allI impI; elim UnE) blast+
qed

end
