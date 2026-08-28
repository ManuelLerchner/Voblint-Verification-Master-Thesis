theory CFG_Local_Trace
  imports CFG_Def CFG_Transfer
begin

section \<open>Activation-local concrete traces\<close>

text \<open>
  An \<open>ltr\<close> represents one procedure activation and its concrete ancestry.  Its local
  path contains \<open>(cfg_node, store)\<close> pairs; structural constructors record the
  suspended caller and, after resumption, the completed callee.  Activation contexts
  are projections of this structure rather than fields stored in the trace.

  Local flow follows \<open>intra\<close>, including \<open>EA_Ret\<close> into the matching
  \<open>FunctionResult\<close>.  A \<open>calls\<close> tuple supplies the call site, callee entry, and
  continuation.  The call rule builds the parameter-bound entry store with
  \<^const>\<open>call_enter\<close>.  The resume rule combines caller locals, callee globals,
  and the return value with \<^const>\<open>combine_collect\<close>.

  The design adapts the thread-modular local-trace semantics of Schwarz and Erhard,
  \<^emph>\<open>Data Race Detection by Digest-Driven Abstract Interpretation\<close> (arXiv:2511.11055,
  2025), which builds on Schwarz et al., \<^emph>\<open>Improving Thread-Modular Abstract
  Interpretation\<close> (SAS 2021).  There a local trace is one thread's execution and
  synchronisation relates traces; here a local trace is one procedure activation and
  a return composes the completed callee into its suspended caller.
\<close>

subsection \<open>The datatype\<close>

text \<open>
  \<^item> \<open>Root p\<close> --- the main activation, with local path \<open>p\<close>.
  \<^item> \<open>Call caller p\<close> --- a callee whose local path \<open>p\<close> starts at the callee-entry store;
    \<open>caller\<close> is the exact suspended caller, frozen at the call node.
  \<^item> \<open>Resume current callee p\<close> --- the activation continued past a completed call.
    \<open>current\<close> is that activation frozen at its call node (the value that spawned \<open>callee\<close>);
    \<open>callee\<close> is the retained completed callee subtree; \<open>p\<close> is the continued path.
\<close>

datatype ltr =
    Root "(cfg_node * store) list"
  | Call (ltr_caller: ltr) "(cfg_node * store) list"
  | Resume (ltr_current: ltr) (ltr_callee: ltr) "(cfg_node * store) list"

subsection \<open>Observers\<close>

text \<open>\<open>path\<close> is the activation-local control-flow path.  \<open>sink_node\<close> and \<open>sink_store\<close>
  return its final program point and final store.\<close>

fun path :: "ltr \<Rightarrow> (cfg_node * store) list" where
  "path (Root p)       = p"
| "path (Call _ p)     = p"
| "path (Resume _ _ p) = p"

definition entry_store :: "ltr \<Rightarrow> store" where
  "entry_store t = snd (hd (path t))"

definition sink_node :: "ltr \<Rightarrow> cfg_node" where
  "sink_node t = fst (last (path t))"

definition sink_store :: "ltr \<Rightarrow> store" where
  "sink_store t = snd (last (path t))"

text \<open>\<open>caller_of\<close> recovers the creating caller of an activation.  It descends the frozen
  \<open>caller\<close> field of a \<^const>\<open>Resume\<close>, so it works uniformly for a returned callee of any
  constructor --- this is what makes nested and recursive returns compose.\<close>

fun caller_of :: "ltr \<Rightarrow> ltr option" where
  "caller_of (Root _)             = None"
| "caller_of (Call caller _)      = Some caller"
| "caller_of (Resume current _ _) = caller_of current"

subsection \<open>Extension and context projection\<close>

text \<open>\<open>extend\<close> appends one step to the innermost local path; it never touches an outer
  constructor's caller/callee fields.\<close>
fun extend :: "ltr \<Rightarrow> (cfg_node * store) \<Rightarrow> ltr" where
  "extend (Root p) x       = Root (p @ [x])"
| "extend (Call c p) x     = Call c (p @ [x])"
| "extend (Resume c d p) x = Resume c d (p @ [x])"

subsection \<open>The closure relation\<close>

text \<open>
  \<open>valid_ltr\<close> is the least set closed under four concrete operations: an initial main
  activation at \<^const>\<open>cfg_entry\<close>; an \<open>intra\<close> step; a call; and a return.  Each rule reads
  exactly the relation for its phenomenon.  \<open>intra\<close> carries no side condition --- calls are
  not \<open>intra\<close> members, so they are untraversable by typing.  \<open>call\<close> enters the callee named
  by the \<open>calls\<close> edge at the callee-entry store \<^const>\<open>enter_state\<close>.  \<open>ret\<close> matches the
  callee's \<open>FunctionResult p\<close> against the \<open>FunctionEntry p\<close> of a concrete \<open>calls\<close> edge
  leaving the caller's node, and resumes at the continuation stored in that same edge; the
  resumed state is \<^const>\<open>combine_collect\<close>.  There is no \<open>combines\<close> lookup and no scan for a
  compatible context.
\<close>

inductive_set valid_ltr :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> ltr set" for gs and g and S where
  init:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> valid_ltr gs g S"
| intra:
    "t \<in> valid_ltr gs g S
     \<Longrightarrow> (sink_node t, a, v) \<in> intra g
     \<Longrightarrow> s' \<in> edge_step a (sink_store t)
     \<Longrightarrow> extend t (v, s') \<in> valid_ltr gs g S"
| call:
    "caller \<in> valid_ltr gs g S
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
     \<Longrightarrow> Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))]
         \<in> valid_ltr gs g S"
| ret:
    "callee \<in> valid_ltr gs g S
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> sink_node callee = FunctionResult p
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
     \<Longrightarrow> Resume caller callee
           (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))])
         \<in> valid_ltr gs g S"

inductive_cases valid_ltr_RootE [elim]:
  "Root p \<in> valid_ltr gs g S"

inductive_cases valid_ltr_CallE [elim]:
  "Call caller p \<in> valid_ltr gs g S"

inductive_cases valid_ltr_ResumeE [elim]:
  "Resume caller callee p \<in> valid_ltr gs g S"

subsection \<open>Structural lemmas\<close>

lemma extend_simps [simp]:
  "path (extend t x) = path t @ [x]"
  "caller_of (extend t x) = caller_of t"
  "sink_node (extend t x) = fst x"
  "sink_store (extend t x) = snd x"
  by (cases t; auto simp: sink_node_def sink_store_def)+

lemma sink_single_simps [simp]:
  "sink_node (Root [(n, s)]) = n"
  "sink_store (Root [(n, s)]) = s"
  "sink_node (Call c [(n, s)]) = n"
  "sink_store (Call c [(n, s)]) = s"
  by (simp_all add: sink_node_def sink_store_def)

lemma valid_ltr_path_nonempty:
  "t \<in> valid_ltr gs g S \<Longrightarrow> path t \<noteq> []"
  by (induction t rule: valid_ltr.induct) auto

lemma entry_store_extend [simp]:
  assumes "path t \<noteq> []"
  shows "entry_store (extend t x) = entry_store t"
  using assms by (simp add: entry_store_def)

lemma entry_store_extend_valid:
  "t \<in> valid_ltr gs g S \<Longrightarrow> entry_store (extend t x) = entry_store t"
  by (simp add: valid_ltr_path_nonempty)

subsection \<open>Design invariants\<close>

text \<open>A valid \<^const>\<open>Call\<close> activation has a valid caller, even after intra steps have
  extended its local path.\<close>
lemma valid_ltr_Call_caller_valid:
  "u \<in> valid_ltr gs g S \<Longrightarrow> u = Call cc q \<Longrightarrow> cc \<in> valid_ltr gs g S"
proof (induction arbitrary: cc q rule: valid_ltr.induct)
  case (intra t a v s')
  from intra.prems obtain q' where "t = Call cc q'"
    by (cases t) auto
  then show ?case using intra.IH by simp
qed auto

text \<open>A valid \<^const>\<open>Resume\<close> retains its callee as a valid trace, and its frozen caller is
  forced to be exactly \<open>caller_of callee\<close> --- a return cannot invent a caller.\<close>
lemma valid_ltr_Resume_fields:
  "u \<in> valid_ltr gs g S \<Longrightarrow> u = Resume cc dd q
   \<Longrightarrow> dd \<in> valid_ltr gs g S \<and> caller_of dd = Some cc"
proof (induction arbitrary: cc dd q rule: valid_ltr.induct)
  case (intra t a v s')
  from intra.prems obtain q' where "t = Resume cc dd q'"
    by (cases t) auto
  then show ?case using intra.IH by simp
qed auto

text \<open>Every caller recovered from a valid trace by \<^const>\<open>caller_of\<close> is itself valid.\<close>
lemma valid_ltr_caller_valid:
  "t \<in> valid_ltr gs g S \<Longrightarrow> caller_of t = Some c \<Longrightarrow> c \<in> valid_ltr gs g S"
proof (induction t arbitrary: c)
  case (Root x)
  then show ?case by simp
next
  case (Call caller p)
  have "caller \<in> valid_ltr gs g S"
    using valid_ltr_Call_caller_valid[OF Call.prems(1) refl] .
  with Call.prems(2) show ?case by simp
next
  case (Resume caller callee p)
  from valid_ltr_Resume_fields[OF Resume.prems(1) refl]
  have cd: "callee \<in> valid_ltr gs g S" "caller_of callee = Some caller" by auto
  have cv: "caller \<in> valid_ltr gs g S" using Resume.IH(2)[OF cd(1)] cd(2) by simp
  from Resume.prems(2) have "caller_of caller = Some c" by simp
  then show ?case using Resume.IH(1)[OF cv] by simp
qed

text \<open>A \<^const>\<open>Root\<close> activation starts at \<^const>\<open>cfg_entry\<close>: \<open>init\<close> creates it there and
  \<open>intra\<close> only appends.\<close>
lemma valid_ltr_Root_entry:
  "u \<in> valid_ltr gs g S \<Longrightarrow> u = Root p \<Longrightarrow> fst (hd p) = cfg_entry g"
proof (induction arbitrary: p rule: valid_ltr.induct)
  case (intra t a v s')
  from intra.prems obtain p' where t: "t = Root p'" and p: "p = p' @ [(v, s')]"
    by (cases t) auto
  have "fst (hd p') = cfg_entry g" using intra.IH[OF t] .
  moreover have "p' \<noteq> []" using valid_ltr_path_nonempty[OF intra.hyps(1)] t by simp
  ultimately show ?case using p by simp
qed auto

text \<open>A \<^const>\<open>Resume\<close> extends its caller's own local path, so both share a head node.\<close>
lemma valid_ltr_Resume_path:
  "u \<in> valid_ltr gs g S \<Longrightarrow> u = Resume cc dd q \<Longrightarrow> \<exists>xs. q = path cc @ xs \<and> xs \<noteq> []"
proof (induction arbitrary: cc dd q rule: valid_ltr.induct)
  case (intra t a v s')
  from intra.prems obtain q' where t: "t = Resume cc dd q'" and q: "q = q' @ [(v, s')]"
    by (cases t) auto
  from intra.IH[OF t] obtain xs where "q' = path cc @ xs" by blast
  then show ?case using q by auto
qed auto

text \<open>A callerless activation is the root one, and its local \<^const>\<open>path\<close> starts at
  \<^const>\<open>cfg_entry\<close>.  The \<^const>\<open>Resume\<close> case needs the caller's own entry, which term
  induction supplies (the caller is a subterm) --- rule induction would only offer the callee.\<close>
lemma valid_ltr_caller_None_entry:
  "t \<in> valid_ltr gs g S \<Longrightarrow> caller_of t = None \<Longrightarrow> fst (hd (path t)) = cfg_entry g"
proof (induction t)
  case (Root p)
  then show ?case using valid_ltr_Root_entry[OF Root.prems(1) refl] by simp
next
  case (Call caller p)
  then show ?case by simp
next
  case (Resume caller callee q)
  from valid_ltr_Resume_fields[OF Resume.prems(1) refl]
  have cd: "callee \<in> valid_ltr gs g S" "caller_of callee = Some caller" by auto
  have cv: "caller \<in> valid_ltr gs g S" using Resume.IH(2)[OF cd(1)] cd(2)
    using valid_ltr_caller_valid[OF cd(1) cd(2)] by simp
  from Resume.prems(2) have "caller_of caller = None" by simp
  with Resume.IH(1)[OF cv] have hcaller: "fst (hd (path caller)) = cfg_entry g" by simp
  from valid_ltr_Resume_path[OF Resume.prems(1) refl] obtain xs where
    q: "q = path caller @ xs" by blast
  show ?case using hcaller q valid_ltr_path_nonempty[OF cv] by simp
qed

subsection \<open>Caller ancestry\<close>

text \<open>\<open>ancestors t\<close> is the \<^const>\<open>caller_of\<close> chain above \<open>t\<close>; \<open>callers t\<close> adds \<open>t\<close>
  itself and is the set a caller-chain invariant ranges over.\<close>
fun ancestors :: "ltr \<Rightarrow> ltr set" where
  "ancestors (Root _) = {}"
| "ancestors (Call caller _) = insert caller (ancestors caller)"
| "ancestors (Resume current _ _) = ancestors current"

abbreviation callers :: "ltr \<Rightarrow> ltr set" where
  "callers t \<equiv> insert t (ancestors t)"

lemma ancestors_extend [simp]: "ancestors (extend t x) = ancestors t"
  by (cases t) simp_all

lemma callers_refl: "t \<in> callers t"
  by simp

lemma ancestors_caller: "caller_of t = Some c \<Longrightarrow> callers c \<subseteq> ancestors t"
  by (induction t) auto

lemma callers_caller_subset: "caller_of t = Some c \<Longrightarrow> callers c \<subseteq> callers t"
  using ancestors_caller by blast

subsection \<open>Generic caller-chain closure\<close>

text \<open>
  A caller-chain-quantified predicate \<open>P\<close> holds along the whole \<^const>\<open>callers\<close> chain of
  every valid trace once its four \<open>valid_ltr\<close> obligations are discharged.  Each obligation
  reads its own generating trace's induction hypothesis as the whole-chain fact
  \<open>\<forall>u \<in> callers _. P u\<close>, not a single-node fact --- this is exactly what \<open>ret\<close> needs to
  recover its caller's own chain fact from the callee's.
\<close>

lemma caller_chain_closure:
  fixes P :: "ltr \<Rightarrow> bool"
  assumes Root: "\<And>s. s \<in> S \<Longrightarrow> P (Root [(cfg_entry g, s)])"
    and Intra: "\<And>t a v s'. t \<in> valid_ltr gs g S \<Longrightarrow> (\<forall>u \<in> callers t. P u)
        \<Longrightarrow> (sink_node t, a, v) \<in> intra g \<Longrightarrow> s' \<in> edge_step a (sink_store t)
        \<Longrightarrow> P (extend t (v, s'))"
    and Call: "\<And>caller dst pars args p cont. caller \<in> valid_ltr gs g S
        \<Longrightarrow> (\<forall>u \<in> callers caller. P u)
        \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> P (Call caller
                 [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
    and Ret: "\<And>callee caller p dst pars args cont. callee \<in> valid_ltr gs g S
        \<Longrightarrow> (\<forall>u \<in> callers callee. P u)
        \<Longrightarrow> caller_of callee = Some caller \<Longrightarrow> sink_node callee = FunctionResult p
        \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> P (Resume caller callee (path caller
                 @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
  shows "t \<in> valid_ltr gs g S \<Longrightarrow> \<forall>u \<in> callers t. P u"
proof (induction rule: valid_ltr.induct)
  case (init s)
  then show ?case using Root[OF init] by simp
next
  case (intra t a v s')
  then show ?case using Intra[OF intra.hyps(1) intra.IH intra.hyps(2,3)] by auto
next
  case (call caller dst pars args p cont)
  then show ?case using Call[OF call.hyps(1) call.IH call.hyps(2)] by auto
next
  case (ret callee caller p dst pars args cont)
  then show ?case
    using Ret[OF ret.hyps(1) ret.IH ret.hyps(2,3,4)] ancestors_caller[OF ret.hyps(2)] by auto
qed

subsection \<open>Stable context entry invariant\<close>

definition call_enter_store :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> cfg_node \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "call_enter_store gs g c s t \<longleftrightarrow>
     (\<exists>dst pars args p cont. (c, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<and> t = call_enter gs (CallEdge dst pars args) s)"

lemma entry_store_Resume_caller:
  "path caller \<noteq> [] \<Longrightarrow>
     entry_store (Resume caller callee (path caller @ [x])) = entry_store caller"
  by (simp add: entry_store_def hd_append)

end

