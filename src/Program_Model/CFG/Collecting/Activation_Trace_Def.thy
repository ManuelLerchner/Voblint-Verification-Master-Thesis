theory Activation_Trace_Def
  imports CFG_Def CFG_Transfer
begin

section \<open>Activation traces\<close>

text \<open>
  An \<open>activation_trace\<close> represents one procedure activation of a sequential run and its
  concrete ancestry.  Its own path contains \<open>(cfg_node, store)\<close> pairs; structural constructors record the
  suspended caller and, after resumption, the completed callee.  Activation contexts
  are projections of this structure rather than fields stored in the trace.

  Local flow follows \<open>intra\<close>, including \<open>EA_Ret\<close> into the matching
  \<open>FunctionResult\<close>.  A \<open>calls\<close> tuple supplies the call site, callee entry, and
  continuation.  The call rule builds the parameter-bound entry store with
  \<^const>\<open>call_enter\<close>.  The resume rule combines caller locals, callee globals,
  and the return value with \<^const>\<open>combine_collect\<close>.

  The shape is adapted from the local traces of Schwarz et al., \<^emph>\<open>Improving Thread-Modular
  Abstract Interpretation\<close> (SAS 2021), and Schwarz and Erhard, \<^emph>\<open>Data Race Detection
  by Digest-Driven Abstract Interpretation\<close> (arXiv:2511.11055, 2025).  Theirs is a
  multithreaded semantics: a local trace is one thread's view, in which operations of different
  threads are only partially ordered.  An activation trace is one activation of a sequential run,
  and a return composes the completed callee into its suspended caller.
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

text \<open>An \<open>activation_path\<close> lists the nodes one activation passed and the store it held at
  each.  An activation trace carries the path of its own activation, with the surrounding activations beside it rather than on it.\<close>

type_synonym activation_path = "(cfg_node \<times> store) list"

datatype activation_trace =
    Root activation_path
  | Call (activation_trace_caller: activation_trace) activation_path
  | Resume (activation_trace_current: activation_trace) (activation_trace_callee: activation_trace)
    activation_path

subsection \<open>Observers\<close>

text \<open>\<open>path_of\<close> is the activation path.  \<open>sink_node\<close> and \<open>sink_store\<close>
  return its final program point and final store.\<close>

fun path_of :: "activation_trace \<Rightarrow> activation_path" where
  "path_of (Root p)       = p"
| "path_of (Call _ p)     = p"
| "path_of (Resume _ _ p) = p"

definition entry_store :: "activation_trace \<Rightarrow> store" where
  "entry_store t = snd (hd (path_of t))"

definition sink_node :: "activation_trace \<Rightarrow> cfg_node" where
  "sink_node t = fst (last (path_of t))"

definition sink_store :: "activation_trace \<Rightarrow> store" where
  "sink_store t = snd (last (path_of t))"

text \<open>\<open>caller_of\<close> recovers the creating caller of an activation.  It descends the frozen
  \<open>caller\<close> field of a \<^const>\<open>Resume\<close>, so it works uniformly for a returned callee of any
  constructor --- this is what makes nested and recursive returns compose.\<close>

fun caller_of :: "activation_trace \<Rightarrow> activation_trace option" where
  "caller_of (Root _)             = None"
| "caller_of (Call caller _)      = Some caller"
| "caller_of (Resume current _ _) = caller_of current"

subsection \<open>Extension and context projection\<close>

text \<open>\<open>extend\<close> appends one step to the innermost local path; it never touches an outer
  constructor's caller/callee fields.\<close>
fun extend :: "activation_trace \<Rightarrow> (cfg_node * store) \<Rightarrow> activation_trace" where
  "extend (Root p) x       = Root (p @ [x])"
| "extend (Call c p) x     = Call c (p @ [x])"
| "extend (Resume c d p) x = Resume c d (p @ [x])"

subsection \<open>The closure relation\<close>

text \<open>
  \<open>valid_activation_trace\<close> is the least set closed under four concrete operations: an initial main
  activation at \<^const>\<open>cfg_entry\<close>; an \<open>intra\<close> step; a call; and a return.  Each rule reads
  exactly the relation for its phenomenon.  \<open>intra\<close> carries no side condition --- calls are
  not \<open>intra\<close> members, so they are untraversable by typing.  \<open>call\<close> enters the callee named
  by the \<open>calls\<close> edge at the callee-entry store \<^const>\<open>call_enter\<close>.  \<open>ret\<close> matches the
  callee's \<open>FunctionResult p\<close> against the \<open>FunctionEntry p\<close> of a concrete \<open>calls\<close> edge
  leaving the caller's node, and resumes at the continuation stored in that same edge; the
  resumed state is \<^const>\<open>combine_collect\<close>.  There is no \<open>combines\<close> lookup and no scan for a
  compatible context.
\<close>

inductive_set valid_activation_trace ::
    "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> activation_trace set"
    ("\<T>\<^bsub>_,_,_\<^esub>")
  for \<G> and g and S where
  root:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
| intra:
    "t \<in> \<T>\<^bsub>\<G>,g,S\<^esub>
     \<Longrightarrow> (sink_node t, a, v) \<in> intra g
     \<Longrightarrow> s' \<in> edge_step a (sink_store t)
     \<Longrightarrow> extend t (v, s') \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
| call:
    "caller \<in> \<T>\<^bsub>\<G>,g,S\<^esub>
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
     \<Longrightarrow> Call caller
           [(FunctionEntry p,
             call_enter \<G> (CallEdge dst pars args) (sink_store caller))]
         \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
| ret:
    "callee \<in> \<T>\<^bsub>\<G>,g,S\<^esub>
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> sink_node callee = FunctionResult p
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
     \<Longrightarrow> Resume caller callee
           (path_of caller
              @ [(cont, combine_collect \<G> dst
                          (sink_store caller) (sink_store callee))])
         \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"

inductive_cases valid_activation_trace_RootE [elim]:
  "Root p \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"

inductive_cases valid_activation_trace_CallE [elim]:
  "Call caller p \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"

inductive_cases valid_activation_trace_ResumeE [elim]:
  "Resume caller callee p \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"

subsection \<open>Structural lemmas\<close>

text \<open>How the three trace shapes answer the projections every later proof reads them
  through -- path, sink, caller, entry store.  Kept as \<open>simp\<close> rules so an induction over
  \<open>valid_activation_trace\<close> never has to case on the constructor merely to look up a sink.\<close>
lemma extend_simps [simp]:
  "path_of (extend t x) = path_of t @ [x]"
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

text \<open>The lemmas up to the caller-chain closure all speak about the traces of one graph
  from one set of initial stores, so the block fixes \<open>\<G>\<close>, \<open>g\<close> and \<open>S\<close> and writes
  \<open>\<T>\<close> for \<open>\<T>\<^bsub>\<G>,g,S\<^esub>\<close>.  Outside the block every lemma holds
  for arbitrary \<open>\<G>\<close>, \<open>g\<close> and \<open>S\<close>.\<close>

context
  fixes \<G> :: "vname \<Rightarrow> bool" and g :: cfg and S :: "store set"
begin

private abbreviation (input) traces :: "activation_trace set" where "traces \<equiv> \<T>\<^bsub>\<G>,g,S\<^esub>"
notation traces ("\<T>")

lemma valid_activation_trace_path_nonempty:
  "t \<in> \<T> \<Longrightarrow> path_of t \<noteq> []"
  by (induction t rule: valid_activation_trace.induct) auto

lemma entry_store_extend [simp]:
  assumes "path_of t \<noteq> []"
  shows "entry_store (extend t x) = entry_store t"
  using assms by (simp add: entry_store_def)

subsection \<open>Design invariants\<close>

text \<open>A valid \<^const>\<open>Call\<close> activation has a valid caller, even after intra steps have
  extended its local path.\<close>
lemma valid_activation_trace_Call_caller_valid:
  "u \<in> \<T> \<Longrightarrow> u = Call cc q \<Longrightarrow> cc \<in> \<T>"
proof (induction arbitrary: cc q rule: valid_activation_trace.induct)
  case (intra t a v s')
  from intra.prems obtain q' where "t = Call cc q'"
    by (cases t) auto
  then show ?case using intra.IH by simp
qed auto

text \<open>A valid \<^const>\<open>Resume\<close> retains its callee as a valid activation trace, and its frozen caller is
  forced to be exactly \<open>caller_of callee\<close> --- a return cannot invent a caller.\<close>
lemma valid_activation_trace_Resume_fields:
  "u \<in> \<T> \<Longrightarrow> u = Resume cc dd q
   \<Longrightarrow> dd \<in> \<T> \<and> caller_of dd = Some cc"
proof (induction arbitrary: cc dd q rule: valid_activation_trace.induct)
  case (intra t a v s')
  from intra.prems obtain q' where "t = Resume cc dd q'"
    by (cases t) auto
  then show ?case using intra.IH by simp
qed auto

text \<open>Every caller recovered from a valid activation trace by \<^const>\<open>caller_of\<close> is itself valid.\<close>
lemma valid_activation_trace_caller_valid:
  "t \<in> \<T> \<Longrightarrow> caller_of t = Some c \<Longrightarrow> c \<in> \<T>"
proof (induction t arbitrary: c)
  case (Root x)
  then show ?case by simp
next
  case (Call caller p)
  have "caller \<in> \<T>"
    using valid_activation_trace_Call_caller_valid[OF Call.prems(1) refl] .
  with Call.prems(2) show ?case by simp
next
  case (Resume caller callee p)
  from valid_activation_trace_Resume_fields[OF Resume.prems(1) refl]
  have cd: "callee \<in> \<T>" "caller_of callee = Some caller" by auto
  have cv: "caller \<in> \<T>" using Resume.IH(2)[OF cd(1)] cd(2) by simp
  from Resume.prems(2) have "caller_of caller = Some c" by simp
  then show ?case using Resume.IH(1)[OF cv] by simp
qed

text \<open>A \<^const>\<open>Root\<close> activation starts at \<^const>\<open>cfg_entry\<close>: \<open>root\<close> creates it there and
  \<open>intra\<close> only appends.\<close>
lemma valid_activation_trace_Root_entry:
  "u \<in> \<T> \<Longrightarrow> u = Root p \<Longrightarrow> fst (hd p) = cfg_entry g"
proof (induction arbitrary: p rule: valid_activation_trace.induct)
  case (intra t a v s')
  from intra.prems obtain p' where t: "t = Root p'" and p: "p = p' @ [(v, s')]"
    by (cases t) auto
  have "fst (hd p') = cfg_entry g" using intra.IH[OF t] .
  moreover have "p' \<noteq> []" using valid_activation_trace_path_nonempty[OF intra.hyps(1)] t by simp
  ultimately show ?case using p by simp
qed auto

text \<open>A \<^const>\<open>Resume\<close> extends its caller's own local path, so both share a head node.\<close>
lemma valid_activation_trace_Resume_path:
  "u \<in> \<T> \<Longrightarrow> u = Resume cc dd q \<Longrightarrow> \<exists>xs. q = path_of cc @ xs \<and> xs \<noteq> []"
proof (induction arbitrary: cc dd q rule: valid_activation_trace.induct)
  case (intra t a v s')
  from intra.prems obtain q' where t: "t = Resume cc dd q'" and q: "q = q' @ [(v, s')]"
    by (cases t) auto
  from intra.IH[OF t] obtain xs where "q' = path_of cc @ xs" by blast
  then show ?case using q by auto
qed auto

text \<open>A callerless activation is the root one, and its local \<^const>\<open>path_of\<close> starts at
  \<^const>\<open>cfg_entry\<close>.  The \<^const>\<open>Resume\<close> case needs the caller's own entry, which term
  induction supplies (the caller is a subterm) --- rule induction would only offer the callee.\<close>
lemma valid_activation_trace_caller_None_entry:
  "t \<in> \<T> \<Longrightarrow> caller_of t = None \<Longrightarrow> fst (hd (path_of t)) = cfg_entry g"
proof (induction t)
  case (Root p)
  then show ?case using valid_activation_trace_Root_entry[OF Root.prems(1) refl] by simp
next
  case (Call caller p)
  then show ?case by simp
next
  case (Resume caller callee q)
  from valid_activation_trace_Resume_fields[OF Resume.prems(1) refl]
  have cd: "callee \<in> \<T>" "caller_of callee = Some caller" by auto
  have cv: "caller \<in> \<T>" using Resume.IH(2)[OF cd(1)] cd(2)
    using valid_activation_trace_caller_valid[OF cd(1) cd(2)] by simp
  from Resume.prems(2) have "caller_of caller = None" by simp
  with Resume.IH(1)[OF cv] have hcaller: "fst (hd (path_of caller)) = cfg_entry g" by simp
  from valid_activation_trace_Resume_path[OF Resume.prems(1) refl] obtain xs where
    q: "q = path_of caller @ xs" by blast
  show ?case using hcaller q valid_activation_trace_path_nonempty[OF cv] by simp
qed

subsection \<open>Caller ancestry\<close>

text \<open>\<open>ancestors t\<close> is the \<^const>\<open>caller_of\<close> chain above \<open>t\<close>; \<open>callers t\<close> adds \<open>t\<close>
  itself and is the set a caller-chain invariant ranges over.\<close>
fun ancestors :: "activation_trace \<Rightarrow> activation_trace set" where
  "ancestors (Root _) = {}"
| "ancestors (Call caller _) = insert caller (ancestors caller)"
| "ancestors (Resume current _ _) = ancestors current"

abbreviation callers :: "activation_trace \<Rightarrow> activation_trace set" where
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
  every valid activation trace once its four \<open>valid_activation_trace\<close> obligations are discharged.  Each obligation
  reads its own generating trace's induction hypothesis as the whole-chain fact
  \<open>\<forall>u \<in> callers _. P u\<close>, not a single-node fact --- this is exactly what \<open>ret\<close> needs to
  recover its caller's own chain fact from the callee's.
\<close>

lemma caller_chain_closure:
  fixes P :: "activation_trace \<Rightarrow> bool"
  assumes Root: "\<And>s. s \<in> S \<Longrightarrow> P (Root [(cfg_entry g, s)])"
    and Intra: "\<And>t a v s'. t \<in> \<T> \<Longrightarrow> (\<forall>u \<in> callers t. P u)
        \<Longrightarrow> (sink_node t, a, v) \<in> intra g \<Longrightarrow> s' \<in> edge_step a (sink_store t)
        \<Longrightarrow> P (extend t (v, s'))"
    and Call: "\<And>caller dst pars args p cont. caller \<in> \<T>
        \<Longrightarrow> (\<forall>u \<in> callers caller. P u)
        \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
        \<Longrightarrow> P (Call caller
                 [(FunctionEntry p, call_enter \<G> (CallEdge dst pars args) (sink_store caller))])"
    and Ret: "\<And>callee caller p dst pars args cont. callee \<in> \<T>
        \<Longrightarrow> (\<forall>u \<in> callers callee. P u)
        \<Longrightarrow> caller_of callee = Some caller \<Longrightarrow> sink_node callee = FunctionResult p
        \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont)
           \<in> calls g
        \<Longrightarrow> P (Resume caller callee (path_of caller
                 @ [(cont, combine_collect \<G> dst (sink_store caller) (sink_store callee))]))"
  shows "t \<in> \<T> \<Longrightarrow> \<forall>u \<in> callers t. P u"
proof (induction rule: valid_activation_trace.induct)
  case (root s)
  then show ?case using Root[OF root] by simp
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

end

subsection \<open>Stable context entry invariant\<close>

text \<open>An activation's entry store is fixed once it starts: a call names the store the callee
  begins with, and resuming a caller keeps the caller's own first store rather than adopting
  the callee's.  Context policies that read the entry store rely on this -- otherwise the
  context a trace carries could change under it as the trace grows.\<close>
definition call_enter_store :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> cfg_node \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "call_enter_store \<G> g c s t \<longleftrightarrow>
     (\<exists>dst pars args p cont. (c, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<and> t = call_enter \<G> (CallEdge dst pars args) s)"

lemma entry_store_Resume_caller:
  "path_of caller \<noteq> [] \<Longrightarrow>
     entry_store (Resume caller callee (path_of caller @ [x])) = entry_store caller"
  by (simp add: entry_store_def hd_append)

end
