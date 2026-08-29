theory VIMP_Proc_to_CFG
  imports "Voblint_CFG.CFG_Def" "Voblint_VIMP.VIMP_Proc"
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

text \<open>The whole program: every declared procedure, plus \<open>main_body \<Pi>\<close> compiled under
  \<open>prog_main_name\<close> (which the well-formedness predicate keeps disjoint from \<open>ps\<close>).  There is
  no global exit: whole-program completion is \<open>FunctionResult prog_main_name\<close>, and the entry is
  \<open>FunctionEntry prog_main_name\<close>.\<close>

text \<open>\<open>checks\<close> is not collected by a separate counter-threading pass: it is read
  directly off the compiled edges, exactly the \<^const>\<open>EA_Check\<close> edges
  \<^const>\<open>compile\<close>'s own \<open>Check c\<close> clause emits. There is only one representation
  of "where a check sits and what it says" --- the compiled \<^const>\<open>intra\<close> set
  itself --- so this field cannot drift from it by construction, not merely by
  a separately proved agreement lemma.\<close>
definition compile_prog ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> cfg"
where
  "compile_prog \<Pi> ps =
     (let (n1, Eprocs, Kprocs) = compile_procs \<Pi> ps 0;
          (n2, Emain, Kmain) =
            compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = main_body \<Pi>\<rparr> n1
      in \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain,
           cfg_entry = FunctionEntry prog_main_name,
           checks = (\<lambda>(u, a, v). (u, ea_check_cond a))
             ` Set.filter (\<lambda>(u, a, v). is_EA_Check a) (Eprocs \<union> Emain) \<rparr>)"

text \<open>Decomposition of a whole compiled program into the callee pass and the \<open>main\<close>
  fragment.\<close>
lemma compile_prog_intra_split:
  obtains n1 Eprocs Kprocs n2 Emain Kmain where
    "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1 = (n2, Emain, Kmain)"
    "intra (compile_prog \<Pi> ps) = Eprocs \<union> Emain"
    "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
proof -
  obtain n1 Eprocs Kprocs where procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    by (rule prod_cases3)
  obtain n2 Emain Kmain
    where mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1 = (n2, Emain, Kmain)"
    by (rule prod_cases3)
  show ?thesis
    by (rule that[OF procs mainc]) (simp_all add: compile_prog_def procs mainc Let_def)
qed

lemma cfg_entry_compile_prog [simp]:
  "cfg_entry (compile_prog \<Pi> ps) = FunctionEntry prog_main_name"
  by (simp add: compile_prog_def Let_def split: prod.splits)

lemma cfg_exit_compile_prog [simp]:
  "cfg_exit (compile_prog \<Pi> ps) = FunctionResult prog_main_name"
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

text \<open>
  The sub-fragment projections.  Descending into one branch needs only that branch's compile
  tuple and the fact that its edges are among the enclosing fragment's; the full rules above
  additionally hand back the sibling's counter and edge sets, which such a proof binds and
  never uses --- leaving their types unconstrained --- and the exact \<open>E = ...\<close> equation, which
  it then has to weaken to a subset by hand.  These state the weaker fact directly.
\<close>

lemma compile_Seq_leftE [elim]:
  assumes "compile \<Pi> p (Seq c1 c2) k n = (n', en, E, K)"
  obtains m F L where
    "compile \<Pi> p c1 (Statement (n + csize c1)) n = (m, Statement n, F, L)"
    "F \<subseteq> E" "L \<subseteq> K"
proof -
  from assms obtain n1 E1 K1 n2 E2 K2 where
    "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    "en = Statement n" "E = E1 \<union> E2" "K = K1 \<union> K2"
    by (rule compile_SeqE)
  then show ?thesis by (intro that) auto
qed

lemma compile_Seq_rightE [elim]:
  assumes "compile \<Pi> p (Seq c1 c2) k n = (n', en, E, K)"
  obtains m F L where
    "compile \<Pi> p c2 k (n + csize c1) = (m, Statement (n + csize c1), F, L)"
    "F \<subseteq> E" "L \<subseteq> K"
proof -
  from assms obtain n1 E1 K1 n2 E2 K2 where
    "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    "en = Statement n" "E = E1 \<union> E2" "K = K1 \<union> K2"
    by (rule compile_SeqE)
  then show ?thesis by (intro that) auto
qed

lemma compile_If_leftE [elim]:
  assumes "compile \<Pi> p (If b c1 c2) k n = (n', en, E, K)"
  obtains m F L where
    "compile \<Pi> p c1 k (Suc n) = (m, Statement (Suc n), F, L)"
    "F \<subseteq> E" "L \<subseteq> K"
proof -
  from assms obtain n1 E1 K1 n2 E2 K2 where
    "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    "en = Statement n"
    "E = {(Statement n, EA_Assume b, Statement (Suc n)),
          (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
    "K = K1 \<union> K2"
    by (rule compile_IfE)
  then show ?thesis by (intro that) auto
qed

lemma compile_If_rightE [elim]:
  assumes "compile \<Pi> p (If b c1 c2) k n = (n', en, E, K)"
  obtains m F L where
    "compile \<Pi> p c2 k (Suc n + csize c1) = (m, Statement (Suc n + csize c1), F, L)"
    "F \<subseteq> E" "L \<subseteq> K"
proof -
  from assms obtain n1 E1 K1 n2 E2 K2 where
    "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    "en = Statement n"
    "E = {(Statement n, EA_Assume b, Statement (Suc n)),
          (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
    "K = K1 \<union> K2"
    by (rule compile_IfE)
  then show ?thesis by (intro that) auto
qed

lemma compile_While_bodyE [elim]:
  assumes "compile \<Pi> p (While b c) k n = (n', en, E, K)"
  obtains m F L where
    "compile \<Pi> p c (Statement n) (Suc n) = (m, Statement (Suc n), F, L)"
    "F \<subseteq> E" "L \<subseteq> K"
proof -
  from assms obtain n1 E1 K1 where
    "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    "en = Statement n"
    "E = {(Statement n, EA_Assume b, Statement (Suc n)),
          (Statement n, EA_AssumeNot b, k)} \<union> E1"
    "K = K1"
    by (rule compile_WhileE)
  then show ?thesis by (intro that) auto
qed

text \<open>A branching fragment's own two edges, for the callers that want them rather than a
  sub-fragment: the guard edges out of \<^term>\<open>Statement n\<close>, which are all the fragment adds
  beyond its branches.\<close>

lemma compile_If_assume_edges:
  assumes "compile \<Pi> p (If b c1 c2) k n = (n', en, E, K)"
  shows "(Statement n, EA_Assume b, Statement (Suc n)) \<in> E"
        "(Statement n, EA_AssumeNot b, Statement (Suc n + csize c1)) \<in> E"
proof -
  from assms obtain n1 E1 K1 n2 E2 K2 where
    "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    "en = Statement n"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, Statement (Suc n + csize c1))} \<union> E1 \<union> E2"
    "K = K1 \<union> K2"
    by (rule compile_IfE)
  show "(Statement n, EA_Assume b, Statement (Suc n)) \<in> E" using E by blast
  show "(Statement n, EA_AssumeNot b, Statement (Suc n + csize c1)) \<in> E" using E by blast
qed

lemma compile_While_assume_edges:
  assumes "compile \<Pi> p (While b c) k n = (n', en, E, K)"
  shows "(Statement n, EA_Assume b, Statement (Suc n)) \<in> E"
        "(Statement n, EA_AssumeNot b, k) \<in> E"
proof -
  from assms obtain n1 E1 K1 where
    "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    "en = Statement n"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, k)} \<union> E1"
    "K = K1"
    by (rule compile_WhileE)
  show "(Statement n, EA_Assume b, Statement (Suc n)) \<in> E" using E by blast
  show "(Statement n, EA_AssumeNot b, k) \<in> E" using E by blast
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

end
