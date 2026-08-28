theory Residual_Location
  imports VIMP_Proc_to_CFG "Voblint_CFG.CFG_Transfer"
begin

section \<open>Where a partly executed command sits in the graph\<close>

text \<open>
  Running a command part way leaves a \<^emph>\<open>residual\<close>: the piece still to execute.
  \<open>control_at\<close> relates a residual to the node the graph's program counter has reached.
  It describes control only --- store agreement is stated separately, by the simulation
  relation.

  A residual that has run down to \<^const>\<open>SKIP\<close> sits at the continuation the compiler was
  handed, not at an exit node of its own, because \<^const>\<open>compile\<close> takes the continuation
  as an input rather than allocating one.  The \<^const>\<open>falls_through\<close> premises below are
  semantic rather than proof conveniences: control reaches the second half of a
  \<^const>\<open>Seq\<close> only if the first half can complete normally, and without them the relation
  would admit positions no execution can occupy.
\<close>

subsection \<open>Located residuals\<close>

text \<open>
  Residual coverage.  For each source form the located clauses fix which node the residual
  occupies; runtime-only forms are handled as follows.
    \<^item> \<^const>\<open>SKIP\<close>, assignment, sequence (before and after left completion), conditionals,
      loops, call site, entered continuation, and explicit \<^const>\<open>Return\<close> all map to a
      compiled node or to the continuation.
    \<^item> \<^const>\<open>Restore\<close> and \<^const>\<open>Unwind\<close> are runtime-only activation markers, not
      located here: once a \<^const>\<open>Return\<close> fires the CFG control is already at \<^term>\<open>FunctionResult p\<close>
      (through the \<^term>\<open>EA_Ret\<close> edge) and the remaining activation return is discharged by the
      located executor \<open>cstep\<close>, not by a fragment node.
\<close>

inductive control_at ::
  "proc_table \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> nat \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> bool"
  for \<Pi> :: proc_table and p :: pname
where
  Skip:
    "control_at \<Pi> p SKIP k n SKIP (Statement n)"
| Assign:
    "control_at \<Pi> p (Assign x a) k n (Assign x a) (Statement n)"
| AssignDone:
    "control_at \<Pi> p (Assign x a) k n SKIP k"
| Check:
    "control_at \<Pi> p (VIMP_Proc.com.Check c) k n (VIMP_Proc.com.Check c) (Statement n)"
| CheckDone:
    "control_at \<Pi> p (VIMP_Proc.com.Check c) k n SKIP k"
| SeqLeft:
    "control_at \<Pi> p c1 (Statement (n + csize c1)) n r v \<Longrightarrow>
     control_at \<Pi> p (Seq c1 c2) k n (Seq r c2) v"
| SeqRight:
    "falls_through c1 \<Longrightarrow>
     control_at \<Pi> p c2 k (n + csize c1) r v \<Longrightarrow>
     control_at \<Pi> p (Seq c1 c2) k n r v"
| IfHead:
    "control_at \<Pi> p (If b c1 c2) k n (If b c1 c2) (Statement n)"
| IfLeft:
    "control_at \<Pi> p c1 k (Suc n) r v \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) k n r v"
| IfRight:
    "control_at \<Pi> p c2 k (Suc n + csize c1) r v \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) k n r v"
| IfDone:
    "falls_through (If b c1 c2) \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) k n SKIP k"
| WhileHead:
    "control_at \<Pi> p (While b c) k n (While b c) (Statement n)"
| WhileUnfolded:
    "control_at \<Pi> p (While b c) k n
       (If b (Seq c (While b c)) SKIP) (Statement n)"
| WhileBody:
    "control_at \<Pi> p c (Statement n) (Suc n) r v \<Longrightarrow>
     control_at \<Pi> p (While b c) k n (Seq r (While b c)) v"
| WhileDone:
    "control_at \<Pi> p (While b c) k n SKIP k"
| CallHead:
    "control_at \<Pi> p (Call dst q actuals) k n (Call dst q actuals) (Statement n)"
| CallDone:
    "control_at \<Pi> p (Call dst q actuals) k n SKIP k"
| ReturnHead:
    "control_at \<Pi> p (Return e) k n (Return e) (Statement n)"

text \<open>The two \<^const>\<open>falls_through\<close> premises above are semantic side conditions on normal
  completion, not proof conveniences.  Control enters \<open>c2\<close> of a \<^const>\<open>Seq\<close> only after \<open>c1\<close> has
  completed normally, and a conditional completes normally only through a branch that can.
  Without them the predicate admits residual locations no execution can occupy --- a conditional
  whose branches both \<^const>\<open>Return\<close> would still be allowed a \<^const>\<open>SKIP\<close> residual at its
  continuation.

  The pay-off is the converse below: a located \<^const>\<open>SKIP\<close> witnesses that its command can
  complete normally.  This is what lets \<open>compile_proc\<close> allocate the epilogue lazily, since the
  \<^term>\<open>EA_Ret None p\<close> edge is then needed exactly when some execution can reach it.\<close>
lemma control_at_SKIP_imp_falls_through:
  assumes "control_at \<Pi> p c k n SKIP v"
  shows "falls_through c"
  using assms by (induction c k n "SKIP :: com" v rule: control_at.induct) auto

subsection \<open>Initial location\<close>

text \<open>A source command is initially located at its entry node \<open>Statement n\<close>.\<close>
lemma control_at_initial:
  "source_com c \<Longrightarrow> control_at \<Pi> p c k n c (Statement n)"
proof (induction c arbitrary: k n)
  case SKIP show ?case by (rule control_at.Skip)
next
  case (Assign x a) show ?case by (rule control_at.Assign)
next
  case (Check b) show ?case by (rule control_at.Check)
next
  case (Seq c1 c2)
  have "control_at \<Pi> p c1 (Statement (n + csize c1)) n c1 (Statement n)"
    by (rule Seq.IH(1)) (use Seq.prems in simp)
  from control_at.SeqLeft[OF this] show ?case .
next
  case (If b c1 c2) show ?case by (rule control_at.IfHead)
next
  case (While b c) show ?case by (rule control_at.WhileHead)
next
  case (Call dst q actuals) show ?case by (rule control_at.CallHead)
next
  case (Return e) show ?case by (rule control_at.ReturnHead)
next
  case Restore then show ?case by simp
next
  case Unwind then show ?case by simp
qed

subsection \<open>Normal completion is located at the continuation\<close>

text \<open>A completed residual is at the continuation already, except for a source \<^const>\<open>SKIP\<close>,
  whose own node still carries one store-preserving \<^const>\<open>EA_Nop\<close> edge to it: both
  branches of a conditional are compiled with the same continuation, so a completed branch
  is at \<open>k\<close> directly.\<close>
lemma compile_control_at_SKIP_exit_path:
  "control_at \<Pi> p c0 k n SKIP v \<Longrightarrow> compile \<Pi> p c0 k n = (n', en, E, K)
   \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> intra_path g (v, s) (k, s)"
proof (induction c0 k n "SKIP :: com" v arbitrary: n' en E K rule: control_at.induct)
  case (Skip k n)
  then have "(Statement n, EA_Nop, k) \<in> intra g" by auto
  then show ?case by (rule intra_path_nop)
next
  case (SeqRight c1 c2 k n v)
  from SeqRight.prems(1) obtain n2 E2 K2 where
    c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and "E2 \<subseteq> E"
    by (rule compile_SeqE) blast
  with SeqRight.prems(2) show ?case by (intro SeqRight.hyps(3)[OF c2]) blast
next
  case (IfLeft c1 k n v b c2)
  from IfLeft.prems(1) obtain n1 E1 K1 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)" and "E1 \<subseteq> E"
    by (rule compile_IfE) blast
  with IfLeft.prems(2) show ?case by (intro IfLeft.hyps(2)[OF c1]) blast
next
  case (IfRight c2 k n c1 v b)
  from IfRight.prems(1) obtain n2 E2 K2 where
    c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and "E2 \<subseteq> E"
    by (rule compile_IfE) blast
  with IfRight.prems(2) show ?case by (intro IfRight.hyps(2)[OF c2]) blast
qed simp_all
subsection \<open>Located residuals remain source commands\<close>

lemma control_at_source_com:
  assumes "control_at \<Pi> p c0 k n r v" and "source_com c0"
  shows "source_com r"  using assms
  by (induction rule: control_at.induct) auto

lemma source_com_no_Restore:
  "source_com c \<Longrightarrow> c \<noteq> Restore"
  by (cases c) auto

end

