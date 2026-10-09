theory Residual_Location
  imports VIMP_Proc_to_CFG
begin

section \<open>Where a partly executed command sits in the graph\<close>

text \<open>
  Running a command part way leaves a \<^emph>\<open>residual\<close>: the piece still to execute.
  \<open>control_at \<Pi> p c0 k n r v\<close> states that residual \<open>r\<close> of the fragment \<open>c0\<close> --- compiled at
  offset \<open>n\<close> with continuation \<open>k\<close> --- corresponds to CFG node \<open>v\<close>.  It tracks control only;
  store agreement is the simulation relation's business.

  A command that \<^emph>\<open>reduces to\<close> \<^const>\<open>SKIP\<close> is located at the continuation \<open>k\<close>, because
  \<^const>\<open>compile\<close> takes the continuation as an input rather than allocating an exit node of
  its own.  A literal source \<^const>\<open>SKIP\<close> is the exception: it keeps its own statement node
  until its \<^term>\<open>EA_Nop\<close> edge is taken.

  The relation also locates positions no execution reaches, such as the second half of a
  \<^const>\<open>Seq\<close> whose first half always returns.  That is harmless: the compiled graph has the
  matching edges there too, since every procedure body ends at an epilogue whose return edge
  \<^const>\<open>compile_proc\<close> always emits.
\<close>

subsection \<open>Located residuals\<close>

text \<open>\<^const>\<open>Restore\<close> and \<^const>\<open>Unwind\<close> have no clause: they are runtime-only activation
  markers rather than compiled commands.  Once a \<^const>\<open>Return\<close> fires the CFG is already at
  \<^term>\<open>FunctionResult p\<close> through the \<^term>\<open>EA_Ret\<close> edge, and the activation return that
  remains is performed by \<open>cstep\<close> popping a frame, not by any fragment node.\<close>

inductive control_at ::
  "proc_table \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> nat \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> bool"
  for \<Pi> :: proc_table and p :: pname
where
  Skip [intro]:
    "control_at \<Pi> p SKIP k n SKIP (Statement n)"
| Assign [intro]:
    "control_at \<Pi> p (Assign x a) k n (Assign x a) (Statement n)"
| AssignDone [intro]:
    "control_at \<Pi> p (Assign x a) k n SKIP k"
| Check [intro]:
    "control_at \<Pi> p (VIMP_Proc.com.Check l c) k n (VIMP_Proc.com.Check l c) (Statement n)"
| CheckDone [intro]:
    "control_at \<Pi> p (VIMP_Proc.com.Check l c) k n SKIP k"
| SeqLeft [intro]:
    "control_at \<Pi> p c1 (Statement (n + csize c1)) n r v \<Longrightarrow>
     control_at \<Pi> p (Seq c1 c2) k n (Seq r c2) v"
| SeqRight [intro]:
    "control_at \<Pi> p c2 k (n + csize c1) r v \<Longrightarrow>
     control_at \<Pi> p (Seq c1 c2) k n r v"
| IfHead [intro]:
    "control_at \<Pi> p (If b c1 c2) k n (If b c1 c2) (Statement n)"
| IfLeft [intro]:
    "control_at \<Pi> p c1 k (Suc n) r v \<Longrightarrow> c1 \<noteq> SKIP \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) k n r v"
| IfRight [intro]:
    "control_at \<Pi> p c2 k (Suc n + csize c1) r v \<Longrightarrow> c2 \<noteq> SKIP \<Longrightarrow>
     control_at \<Pi> p (If b c1 c2) k n r v"
| IfDone [intro]:
    "control_at \<Pi> p (If b c1 c2) k n SKIP k"
| WhileHead [intro]:
    "control_at \<Pi> p (While b c) k n (While b c) (Statement n)"
| WhileUnfolded [intro]:
    "control_at \<Pi> p (While b c) k n
       (If b (Seq c (While b c)) SKIP) (Statement n)"
| WhileBody [intro]:
    "control_at \<Pi> p c (Statement n) (Suc n) r v \<Longrightarrow>
     control_at \<Pi> p (While b c) k n (Seq r (While b c)) v"
| WhileDone [intro]:
    "control_at \<Pi> p (While b c) k n SKIP k"
| CallHead [intro]:
    "control_at \<Pi> p (Call dst q actuals) k n (Call dst q actuals) (Statement n)"
| CallDone [intro]:
    "control_at \<Pi> p (Call dst q actuals) k n SKIP k"
| ReturnHead [intro]:
    "control_at \<Pi> p (Return e) k n (Return e) (Statement n)"


text \<open>Inversion by the shape of the fragment \<open>c0\<close>, which is what every consumer knows and
  cases on.  \<^const>\<open>Seq\<close>, \<^const>\<open>If\<close> and \<^const>\<open>While\<close> stay plain \<open>[elim]\<close> because their
  clauses recurse into a sub-fragment, and an eager rule would chase the nesting; the rest
  are \<open>[elim!]\<close>.  \<^const>\<open>Restore\<close> and \<^const>\<open>Unwind\<close> have no clause at all, so inverting
  them is outright refutation --- that is what makes \<open>control_at_not_unwind\<close> a one-liner.\<close>
inductive_cases control_at_SkipE [elim!]:    "control_at \<Pi> p SKIP k n r v"
inductive_cases control_at_AssignE [elim!]:  "control_at \<Pi> p (Assign x a) k n r v"
inductive_cases control_at_CheckE [elim!]:
  "control_at \<Pi> p (VIMP_Proc.com.Check l b) k n r v"
inductive_cases control_at_SeqE [elim]:      "control_at \<Pi> p (Seq c1 c2) k n r v"
inductive_cases control_at_IfE [elim]:       "control_at \<Pi> p (If b c1 c2) k n r v"
inductive_cases control_at_WhileE [elim]:    "control_at \<Pi> p (While b c) k n r v"
inductive_cases control_at_CallE [elim!]:
  "control_at \<Pi> p (Call dst q actuals) k n r v"
inductive_cases control_at_ReturnE [elim!]:  "control_at \<Pi> p (Return e) k n r v"
inductive_cases control_at_RestoreE [elim!]: "control_at \<Pi> p Restore k n r v"
inductive_cases control_at_UnwindE [elim!]:  "control_at \<Pi> p Unwind k n r v"


subsection \<open>Initial location\<close>

text \<open>A source command is initially located at its entry node \<open>Statement n\<close>.\<close>
lemma control_at_initial:
  "source_com c \<Longrightarrow> control_at \<Pi> p c k n c (Statement n)"
  by (induction c arbitrary: k n) auto

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
  case (SeqRight c2 k n c1 v)
  from SeqRight.prems(1) obtain n2 E2 K2 where
    c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and "E2 \<subseteq> E"
    by (rule compile_SeqE) blast
  with SeqRight.prems(2) show ?case by (intro SeqRight.hyps(2)[OF c2]) blast
next
  case (IfLeft c1 k n v b c2)
  from IfLeft.prems(1) obtain n1 E1 K1 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)" and "E1 \<subseteq> E"
    by (rule compile_If_leftE[OF _ IfLeft.hyps(3)]) blast
  with IfLeft.prems(2) show ?case by (intro IfLeft.hyps(2)[OF c1]) blast
next
  case (IfRight c2 k n c1 v b)
  from IfRight.prems(1) obtain n2 E2 K2 where
    c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and "E2 \<subseteq> E"
    by (rule compile_If_rightE[OF _ IfRight.hyps(3)]) blast
  with IfRight.prems(2) show ?case by (intro IfRight.hyps(2)[OF c2]) blast
qed simp_all

subsection \<open>Located residuals remain source commands\<close>

text \<open>Execution never introduces the runtime-only commands into a residual: whatever remains
  of a source procedure is itself source syntax.  The simulation needs this to rule out the
  frame-popping cases when it is reasoning inside a procedure body.\<close>

lemma control_at_source_com:
  assumes "control_at \<Pi> p c0 k n r v" and "source_com c0"
  shows "source_com r"  using assms
  by (induction rule: control_at.induct) auto

lemma source_com_no_Restore:
  "source_com c \<Longrightarrow> c \<noteq> Restore"
  by auto

end
