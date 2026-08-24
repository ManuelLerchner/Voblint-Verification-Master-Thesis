theory CFG_Local_Trace
  imports CFG_Def
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

primrec path :: "ltr \<Rightarrow> (cfg_node * store) list" where
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
primrec extend :: "ltr \<Rightarrow> (cfg_node * store) \<Rightarrow> ltr" where
  "extend (Root p) x       = Root (p @ [x])"
| "extend (Call c p) x     = Call c (p @ [x])"
| "extend (Resume c d p) x = Resume c d (p @ [x])"

text \<open>The activation context is computed from the concrete trace after the fact and is
  activation-stable: fixed when the activation is created and unchanged by the calls it
  later makes and returns from.  \<^const>\<open>Root\<close> carries the seed; a \<^const>\<open>Call\<close> routes the
  caller context on the call site and the callee-entry store --- \<open>sink_node parent\<close> is
  exactly the call site, since \<^const>\<open>extend\<close> only ever appends to the callee path and
  leaves \<open>parent\<close> frozen there; a \<^const>\<open>Resume\<close> keeps the resumed caller's own context, so
  a completed call does not repartition the caller.  Exposing the call site to \<open>enterc\<close> is
  what makes a call-site-keyed context (a k-call-string) expressible as an instance rather
  than only as a generator-side hook.\<close>
fun key :: "(cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ltr \<Rightarrow> 'c" where
  "key enterc startcontext (Root _)                  = startcontext"
| "key enterc startcontext (Call parent p)           =
     enterc (sink_node parent) (key enterc startcontext parent) (snd (hd p))"
| "key enterc startcontext (Resume current callee _) = key enterc startcontext current"

subsection \<open>Admissible context selection\<close>

text \<open>
  \<open>key\<close> fixes one context per trace by decoding the entered store exactly. \<open>ctx_key\<close>
  generalizes this: the context an activation is analyzed under is any \<open>admiss\<close>-admissible
  choice, threaded through the same recursive shape \<open>key\<close> has --- a \<^const>\<open>Call\<close> activation's
  context is admissible relative to its caller's OWN selected context, not re-derived from
  the concrete store independently at each node. This is what keeps a chosen context stable
  across a CALL/RETURN pair: the callee's context in \<^const>\<open>Resume\<close> resumes through
  \<open>current\<close>, so a completed call cannot repartition the caller, exactly as for \<open>key\<close>.

  \<open>admiss_exact enterc\<close> recovers \<open>key\<close> exactly (\<open>ctx_key_exact_iff\<close>): the deterministic
  decode is the special case where exactly one context is admissible per call.
\<close>

inductive ctx_key :: "(cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> ltr \<Rightarrow> 'c \<Rightarrow> bool"
  for admiss :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool" and startcontext :: 'c
where
  ctx_key_Root: "ctx_key admiss startcontext (Root p) startcontext"
| ctx_key_Call: "ctx_key admiss startcontext parent c
    \<Longrightarrow> admiss (sink_node parent) c (snd (hd p)) c'
    \<Longrightarrow> ctx_key admiss startcontext (Call parent p) c'"
| ctx_key_Resume: "ctx_key admiss startcontext current c
    \<Longrightarrow> ctx_key admiss startcontext (Resume current callee p) c"

inductive_cases ctx_key_RootE: "ctx_key admiss startcontext (Root p) c"
inductive_cases ctx_key_CallE: "ctx_key admiss startcontext (Call parent p) c"
inductive_cases ctx_key_ResumeE: "ctx_key admiss startcontext (Resume current callee p) c"

definition admiss_exact :: "(cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool" where
  "admiss_exact enterc u c s c' \<longleftrightarrow> c' = enterc u c s"

text \<open>The migration bridge: \<open>ctx_key\<close> at \<open>admiss_exact enterc\<close> is exactly \<open>key\<close>. This is the
  hard gate for the whole generalization --- every downstream exact instance must reduce to
  \<open>key\<close> through this lemma, not through a bespoke re-proof.\<close>
lemma ctx_key_exact_iff:
  "ctx_key (admiss_exact enterc) startcontext t c \<longleftrightarrow> key enterc startcontext t = c"
proof (induction t arbitrary: c)
  case (Root p)
  show ?case by (auto simp: admiss_exact_def elim: ctx_key_RootE intro: ctx_key_Root)
next
  case (Call parent p)
  show ?case
  proof
    assume "ctx_key (admiss_exact enterc) startcontext (Call parent p) c"
    then obtain c0 where c0: "ctx_key (admiss_exact enterc) startcontext parent c0"
      and c: "c = enterc (sink_node parent) c0 (snd (hd p))"
      by (auto simp: admiss_exact_def elim: ctx_key_CallE)
    from c0 have "key enterc startcontext parent = c0" by (simp add: Call.IH)
    with c show "key enterc startcontext (Call parent p) = c" by simp
  next
    assume "key enterc startcontext (Call parent p) = c"
    hence c: "c = enterc (sink_node parent) (key enterc startcontext parent) (snd (hd p))" by simp
    have "ctx_key (admiss_exact enterc) startcontext parent (key enterc startcontext parent)"
      by (simp add: Call.IH)
    thus "ctx_key (admiss_exact enterc) startcontext (Call parent p) c"
      using c by (auto simp: admiss_exact_def intro: ctx_key_Call)
  qed
next
  case (Resume current callee p)
  show ?case
    by (auto simp: Resume.IH[symmetric] elim: ctx_key_ResumeE intro: ctx_key_Resume)
qed

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

inductive_set valid_ltr :: "tyenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> ltr set" for \<Gamma> and gs and g and S where
  init:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> valid_ltr \<Gamma> gs g S"
| intra:
    "t \<in> valid_ltr \<Gamma> gs g S
     \<Longrightarrow> (sink_node t, a, v) \<in> intra g
     \<Longrightarrow> s' \<in> edge_step \<Gamma> a (sink_store t)
     \<Longrightarrow> extend t (v, s') \<in> valid_ltr \<Gamma> gs g S"
| call:
    "caller \<in> valid_ltr \<Gamma> gs g S
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
     \<Longrightarrow> Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))]
         \<in> valid_ltr \<Gamma> gs g S"
| ret:
    "callee \<in> valid_ltr \<Gamma> gs g S
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> sink_node callee = FunctionResult p
     \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
     \<Longrightarrow> Resume caller callee
           (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))])
         \<in> valid_ltr \<Gamma> gs g S"

inductive_cases valid_ltrE:
  "t \<in> valid_ltr \<Gamma> gs g S"

inductive_cases valid_ltr_RootE [elim]:
  "Root p \<in> valid_ltr \<Gamma> gs g S"

inductive_cases valid_ltr_CallE [elim]:
  "Call caller p \<in> valid_ltr \<Gamma> gs g S"

inductive_cases valid_ltr_ResumeE [elim]:
  "Resume caller callee p \<in> valid_ltr \<Gamma> gs g S"

subsection \<open>Structural lemmas\<close>

lemma path_extend [simp]: "path (extend t x) = path t @ [x]"
  by (cases t) auto

lemma caller_of_extend [simp]: "caller_of (extend t x) = caller_of t"
  by (cases t) auto

lemma sink_node_extend [simp]: "sink_node (extend t x) = fst x"
  by (simp add: sink_node_def)

lemma sink_store_extend [simp]: "sink_store (extend t x) = snd x"
  by (simp add: sink_store_def)

lemma sink_node_Root_single [simp]: "sink_node (Root [(n, s)]) = n"
  by (simp add: sink_node_def)

lemma sink_store_Root_single [simp]: "sink_store (Root [(n, s)]) = s"
  by (simp add: sink_store_def)

lemma sink_node_Call_single [simp]: "sink_node (Call c [(n, s)]) = n"
  by (simp add: sink_node_def)

lemma sink_store_Call_single [simp]: "sink_store (Call c [(n, s)]) = s"
  by (simp add: sink_store_def)

text \<open>Every member of \<^const>\<open>valid_ltr\<close> has a non-empty path.\<close>
lemma valid_ltr_path_nonempty:
  "t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> path t \<noteq> []"
  by (induction t rule: valid_ltr.induct) auto

lemma entry_store_extend [simp]:
  assumes "path t \<noteq> []"
  shows "entry_store (extend t x) = entry_store t"
  using assms by (simp add: entry_store_def)

lemma entry_store_extend_valid:
  "t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> entry_store (extend t x) = entry_store t"
  by (simp add: valid_ltr_path_nonempty)

subsection \<open>Caller recovery through nested returns\<close>

lemma caller_of_Resume_Call [simp]:
  "caller_of (Resume (Call m cp) callee p) = Some m"
  by simp

text \<open>The activation parent is recovered through a \<^const>\<open>Resume\<close> even after the caller has
  itself returned and been extended --- the key non-stuck property for recursion.\<close>
lemma nested_return_caller_of:
  fixes m :: ltr and cpf cpg pf :: "(cfg_node * store) list" and x :: "cfg_node * store"
  defines "f  \<equiv> Call m cpf"
  defines "g  \<equiv> Call f cpg"
  defines "f' \<equiv> Resume f g pf"
  shows "caller_of g = Some f"
    and "caller_of f' = Some m"
    and "caller_of (extend f' x) = Some m"
  by (simp_all add: f_def g_def f'_def)

subsection \<open>Design invariants\<close>

text \<open>A valid \<^const>\<open>Call\<close> activation has a valid caller, even after intra steps have
  extended its local path.\<close>
lemma valid_ltr_Call_caller_valid:
  "u \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> u = Call cc q \<Longrightarrow> cc \<in> valid_ltr \<Gamma> gs g S"
proof (induction arbitrary: cc q rule: valid_ltr.induct)
  case (intra t a v s')
  from intra.prems obtain q' where "t = Call cc q'"
    by (cases t) auto
  then show ?case using intra.IH by simp
qed auto

text \<open>A valid \<^const>\<open>Resume\<close> retains its callee as a valid trace, and its frozen caller is
  forced to be exactly \<open>caller_of callee\<close> --- a return cannot invent a caller.\<close>
lemma valid_ltr_Resume_fields:
  "u \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> u = Resume cc dd q
   \<Longrightarrow> dd \<in> valid_ltr \<Gamma> gs g S \<and> caller_of dd = Some cc"
proof (induction arbitrary: cc dd q rule: valid_ltr.induct)
  case (intra t a v s')
  from intra.prems obtain q' where "t = Resume cc dd q'"
    by (cases t) auto
  then show ?case using intra.IH by simp
qed auto

text \<open>Every caller recovered from a valid trace by \<^const>\<open>caller_of\<close> is itself valid.\<close>
lemma valid_ltr_caller_valid:
  "t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> caller_of t = Some c \<Longrightarrow> c \<in> valid_ltr \<Gamma> gs g S"
proof (induction t arbitrary: c)
  case (Root x)
  then show ?case by simp
next
  case (Call caller p)
  have "caller \<in> valid_ltr \<Gamma> gs g S"
    using valid_ltr_Call_caller_valid[OF Call.prems(1) refl] .
  with Call.prems(2) show ?case by simp
next
  case (Resume caller callee p)
  from valid_ltr_Resume_fields[OF Resume.prems(1) refl]
  have cd: "callee \<in> valid_ltr \<Gamma> gs g S" "caller_of callee = Some caller" by auto
  have cv: "caller \<in> valid_ltr \<Gamma> gs g S" using Resume.IH(2)[OF cd(1)] cd(2) by simp
  from Resume.prems(2) have "caller_of caller = Some c" by simp
  then show ?case using Resume.IH(1)[OF cv] by simp
qed

text \<open>A callerless activation is the root one, and its local \<^const>\<open>path\<close> starts at
  \<^const>\<open>cfg_entry\<close>: \<open>init\<close> is the only rule that creates a trace with no caller, \<open>intra\<close>
  appends (leaving the head fixed), and \<open>ret\<close> resumes the caller's own path.\<close>
text \<open>A \<^const>\<open>Root\<close> activation starts at \<^const>\<open>cfg_entry\<close>: \<open>init\<close> creates it there and
  \<open>intra\<close> only appends.\<close>
lemma valid_ltr_Root_entry:
  "u \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> u = Root p \<Longrightarrow> fst (hd p) = cfg_entry g"
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
  "u \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> u = Resume cc dd q \<Longrightarrow> \<exists>xs. q = path cc @ xs \<and> xs \<noteq> []"
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
  "t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> caller_of t = None \<Longrightarrow> fst (hd (path t)) = cfg_entry g"
proof (induction t)
  case (Root p)
  then show ?case using valid_ltr_Root_entry[OF Root.prems(1) refl] by simp
next
  case (Call caller p)
  then show ?case by simp
next
  case (Resume caller callee q)
  from valid_ltr_Resume_fields[OF Resume.prems(1) refl]
  have cd: "callee \<in> valid_ltr \<Gamma> gs g S" "caller_of callee = Some caller" by auto
  have cv: "caller \<in> valid_ltr \<Gamma> gs g S" using Resume.IH(2)[OF cd(1)] cd(2)
    using valid_ltr_caller_valid[OF cd(1) cd(2)] by simp
  from Resume.prems(2) have "caller_of caller = None" by simp
  with Resume.IH(1)[OF cv] have hcaller: "fst (hd (path caller)) = cfg_entry g" by simp
  from valid_ltr_Resume_path[OF Resume.prems(1) refl] obtain xs where
    q: "q = path caller @ xs" by blast
  show ?case using hcaller q valid_ltr_path_nonempty[OF cv] by simp
qed

lemma valid_ltr_Call_path_nonempty:
  "Call caller p \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> p \<noteq> []"
  using valid_ltr_path_nonempty by fastforce

subsection \<open>Caller ancestry\<close>

lemma caller_of_size: "caller_of t = Some c \<Longrightarrow> size c < size t"
  by (induction t arbitrary: c) auto

function callers :: "ltr \<Rightarrow> ltr set" where
  "callers t = insert t (case caller_of t of None \<Rightarrow> {} | Some c \<Rightarrow> callers c)"
  by pat_completeness auto
termination callers
  by (relation "measure size") (auto simp: caller_of_size)

lemma callers_refl: "t \<in> callers t"
  by (subst callers.simps) simp

lemma callers_caller_subset: "caller_of t = Some c \<Longrightarrow> callers c \<subseteq> callers t"
  by (subst (2) callers.simps) auto

lemma case_caller_subset:
  "(case caller_of t of None \<Rightarrow> {} | Some c \<Rightarrow> callers c) \<subseteq> callers t"
  by (subst (2) callers.simps) auto

lemma callers_Root: "callers (Root p) = {Root p}"
  by (subst callers.simps) simp

lemma callers_Call: "callers (Call caller p) = insert (Call caller p) (callers caller)"
  by (subst callers.simps) simp

lemma callers_extend_subset:
  "callers (extend t x) \<subseteq> insert (extend t x) (callers t)"
proof -
  have "callers (extend t x)
        = insert (extend t x) (case caller_of t of None \<Rightarrow> {} | Some c \<Rightarrow> callers c)"
    by (subst callers.simps) simp
  also have "... \<subseteq> insert (extend t x) (callers t)"
    using case_caller_subset by blast
  finally show ?thesis .
qed

lemma callers_Resume_subset:
  assumes "caller_of callee = Some caller"
  shows "callers (Resume caller callee p) \<subseteq> insert (Resume caller callee p) (callers callee)"
proof -
  have "callers (Resume caller callee p)
        = insert (Resume caller callee p)
            (case caller_of caller of None \<Rightarrow> {} | Some c \<Rightarrow> callers c)"
    by (subst callers.simps) simp
  also have "(case caller_of caller of None \<Rightarrow> {} | Some c \<Rightarrow> callers c) \<subseteq> callers caller"
    by (rule case_caller_subset)
  also have "callers caller \<subseteq> callers callee"
    using assms by (rule callers_caller_subset)
  finally show ?thesis by blast
qed
subsection \<open>Generic caller-chain closure\<close>

text \<open>
  A caller-chain-quantified predicate \<open>P\<close> holds along the whole \<^const>\<open>callers\<close> chain of
  every valid trace once its four \<open>valid_ltr\<close> obligations are discharged.  Each obligation
  reads its own generating trace's induction hypothesis as the whole-chain fact
  \<open>ALL u : callers _. P u\<close>, not a single-node fact --- this is exactly what \<open>ret\<close> needs to
  recover its caller's own chain fact from the callee's.  \<open>gamma_chain\<close> (\<open>LTR_Abstract\<close>),
  \<open>valid_ltr_path_nodes\<close>, and \<open>valid_ltr_frag_callers\<close> (\<open>Compile_Locality\<close>) instantiate this
  once instead of each repeating the \<^const>\<open>callers\<close> case dispatch below.
\<close>

lemma caller_chain_closure:
  fixes P :: "ltr \<Rightarrow> bool"
  assumes Root: "\<And>s. s \<in> S \<Longrightarrow> P (Root [(cfg_entry g, s)])"
    and Intra: "\<And>t a v s'. t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> (\<forall>u \<in> callers t. P u)
        \<Longrightarrow> (sink_node t, a, v) \<in> intra g \<Longrightarrow> s' \<in> edge_step \<Gamma> a (sink_store t)
        \<Longrightarrow> P (extend t (v, s'))"
    and Call: "\<And>caller dst pars args p cont. caller \<in> valid_ltr \<Gamma> gs g S
        \<Longrightarrow> (\<forall>u \<in> callers caller. P u)
        \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> P (Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))])"
    and Ret: "\<And>callee caller p dst pars args cont. callee \<in> valid_ltr \<Gamma> gs g S
        \<Longrightarrow> (\<forall>u \<in> callers callee. P u)
        \<Longrightarrow> caller_of callee = Some caller \<Longrightarrow> sink_node callee = FunctionResult p
        \<Longrightarrow> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> P (Resume caller callee
                 (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))]))"
  shows "t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> \<forall>u \<in> callers t. P u"
proof (induction rule: valid_ltr.induct)
  case (init s)
  then show ?case using Root[OF init] by (simp add: callers_Root)
next
  case (intra t a v s')
  show ?case
  proof (rule ballI)
    fix u assume "u \<in> callers (extend t (v, s'))"
    then have "u = extend t (v, s') \<or> u \<in> callers t"
      using callers_extend_subset by blast
    then show "P u"
    proof (rule disjE)
      assume u: "u = extend t (v, s')"
      show ?thesis unfolding u
        by (rule Intra[OF intra.hyps(1) intra.IH intra.hyps(2,3)])
    next
      assume "u \<in> callers t"
      then show ?thesis using intra.IH by blast
    qed
  qed
next
  case (call caller dst pars args p cont)
  show ?case
  proof (rule ballI)
    fix u assume "u \<in> callers (Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))])"
    then have "u = Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))]
                \<or> u \<in> callers caller"
      by (simp add: callers_Call)
    then show "P u"
    proof (rule disjE)
      assume u: "u = Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))]"
      show ?thesis unfolding u
        by (rule Call[OF call.hyps(1) call.IH call.hyps(2)])
    next
      assume "u \<in> callers caller"
      then show ?thesis using call.IH by blast
    qed
  qed
next
  case (ret callee caller p dst pars args cont)
  show ?case
  proof (rule ballI)
    fix u assume "u \<in> callers (Resume caller callee
        (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))]))"
    then have "u = Resume caller callee
        (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))])
                \<or> u \<in> callers callee"
      using callers_Resume_subset[OF ret.hyps(2)] by blast
    then show "P u"
    proof (rule disjE)
      assume u: "u = Resume caller callee
          (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))])"
      show ?thesis unfolding u
        by (rule Ret[OF ret.hyps(1) ret.IH ret.hyps(2,3,4)])
    next
      assume "u \<in> callers callee"
      then show ?thesis using ret.IH by blast
    qed
  qed
qed


subsection \<open>Required trace obligations\<close>

text \<open>(1) Call provenance: every \<^const>\<open>Call\<close> activation is justified by a concrete member
  of \<open>calls g\<close> leaving its caller's node.\<close>
lemma valid_ltr_Call_provenance:
  assumes "Call caller q \<in> valid_ltr \<Gamma> gs g S"
  shows "\<exists>dst pars args p cont. (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
proof -
  have "u \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow>
          \<forall>ca q. u = Call ca q \<longrightarrow>
            (\<exists>dst pars args p cont. (sink_node ca, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g)"
    for u
  proof (induction rule: valid_ltr.induct)
    case (intra t a v s')
    show ?case
    proof (intro allI impI)
      fix ca q assume "extend t (v, s') = Call ca q"
      then obtain q' where "t = Call ca q'" by (cases t) auto
      with intra.IH show
        "\<exists>dst pars args p cont. (sink_node ca, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
        by blast
    qed
  qed blast+
  with assms show ?thesis by blast
qed

text \<open>(2) Entry correctness: a called activation begins at the callee-entry node recorded
  by a concrete call edge.\<close>
lemma valid_ltr_Call_entry_node:
  assumes "Call caller q \<in> valid_ltr \<Gamma> gs g S"
  shows "\<exists>dst pars args p cont. (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
          \<and> fst (hd q) = FunctionEntry p"
proof -
  have "u \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow>
          \<forall>ca q. u = Call ca q \<longrightarrow>
            (\<exists>dst pars args p cont. (sink_node ca, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
               \<and> fst (hd q) = FunctionEntry p)"
    for u
  proof (induction rule: valid_ltr.induct)
    case (call caller dst pars args p cont)
    then show ?case by auto
  next
    case (intra t a v s')
    show ?case
    proof (intro allI impI)
      fix ca q assume e: "extend t (v, s') = Call ca q"
      then obtain q' where t: "t = Call ca q'" by (cases t) auto
      then have "q = q' @ [(v, s')]" using e by simp
      moreover have "q' \<noteq> []" using t intra.hyps(1) valid_ltr_Call_path_nonempty by blast
      ultimately have "hd q = hd q'" by (simp add: hd_append)
      with intra.IH t show
        "\<exists>dst pars args p cont. (sink_node ca, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
           \<and> fst (hd q) = FunctionEntry p"
        by fastforce
    qed
  qed auto
  with assms show ?thesis by blast
qed

text \<open>(3) Caller preservation under intra extension: extending a callee through \<open>intra\<close>
  does not change its structural caller.\<close>
lemmas valid_ltr_caller_preserved = caller_of_extend

text \<open>(4) Return matching: a \<^const>\<open>Resume\<close> exists only after the child reaches the matching
  \<open>FunctionResult p\<close> of a concrete call edge.\<close>
lemma valid_ltr_Resume_matching:
  assumes "Resume caller callee q \<in> valid_ltr \<Gamma> gs g S"
  shows "\<exists>dst pars args p cont. sink_node callee = FunctionResult p
          \<and> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
proof -
  have "u \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow>
          \<forall>cc dd q. u = Resume cc dd q \<longrightarrow>
            (\<exists>dst pars args p cont. sink_node dd = FunctionResult p
               \<and> (sink_node cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g)"
    for u
  proof (induction rule: valid_ltr.induct)
    case (intra t a v s')
    show ?case
    proof (intro allI impI)
      fix cc dd q assume "extend t (v, s') = Resume cc dd q"
      then obtain q' where "t = Resume cc dd q'" by (cases t) auto
      with intra.IH show
        "\<exists>dst pars args p cont. sink_node dd = FunctionResult p
           \<and> (sink_node cc, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
        by blast
    qed
  qed auto
  with assms show ?thesis by blast
qed

text \<open>(5) Continuation exactness: resuming lands the caller exactly on the continuation
  recorded in the originating call edge.  This is a property of the return transition: the
  sink of the produced \<^const>\<open>Resume\<close> is the edge's \<open>cont\<close>.  (It holds at the resume step;
  a subsequent \<open>intra\<close> step in the resumed activation moves its sink past \<open>cont\<close>, so the
  claim is stated where it is meaningful --- at the transition --- not as an
  extension-stable invariant.)\<close>
lemma valid_ltr_ret_continuation:
  assumes "callee \<in> valid_ltr \<Gamma> gs g S"
    and "caller_of callee = Some caller"
    and "sink_node callee = FunctionResult p"
    and "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  shows "sink_node (Resume caller callee
           (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))]))
         = cont"
  by (simp add: sink_node_def)

text \<open>(6) Nearest activation discipline: a \<^const>\<open>Resume\<close> resumes the callee's immediate
  caller, not an ancestor.  The frozen caller is forced to be \<open>caller_of callee\<close>.\<close>
lemma valid_ltr_Resume_immediate_caller:
  "Resume caller callee q \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> caller_of callee = Some caller"
  using valid_ltr_Resume_fields by blast

text \<open>(9) Flat CFG reduction: when \<open>calls g = {}\<close>, every valid trace is a \<^const>\<open>Root\<close>; no
  \<^const>\<open>Call\<close> or \<^const>\<open>Resume\<close> can arise.\<close>
lemma valid_ltr_flat_root:
  assumes "flat_cfg g" and "t \<in> valid_ltr \<Gamma> gs g S"
  shows "\<exists>p. t = Root p"
  using assms(2)
proof (induction rule: valid_ltr.induct)
  case (intra t a v s')
  then obtain p where "t = Root p" by blast
  then show ?case by (cases t) auto
next
  case (call caller dst pars args p cont)
  then show ?case using assms(1) by (simp add: flat_cfg_def)
next
  case (ret callee caller p dst pars args cont)
  then show ?case using assms(1) by (simp add: flat_cfg_def)
qed simp

subsection \<open>Node membership\<close>

text \<open>The nodes observed along a valid trace, and along its whole caller chain, all belong
  to \<^const>\<open>cfg_nodes\<close>.\<close>
lemma valid_ltr_path_nodes:
  "t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow>
     \<forall>u \<in> callers t. \<forall>ns \<in> set (path u). fst ns \<in> cfg_nodes g"
proof (rule caller_chain_closure)
  fix s assume "s \<in> S"
  then show "\<forall>ns \<in> set (path (Root [(cfg_entry g, s)])). fst ns \<in> cfg_nodes g"
    by (simp add: cfg_entry_in_nodes)
next
  fix t a v s' assume ch: "\<forall>u \<in> callers t. \<forall>ns \<in> set (path u). fst ns \<in> cfg_nodes g"
    and e: "(sink_node t, a, v) \<in> intra g"
  have vnode: "v \<in> cfg_nodes g" using e intra_endpoints_in_nodes by blast
  have "\<forall>ns \<in> set (path t). fst ns \<in> cfg_nodes g" using ch callers_refl by blast
  then show "\<forall>ns \<in> set (path (extend t (v, s'))). fst ns \<in> cfg_nodes g"
    using vnode by auto
next
  fix caller dst pars args p cont
  assume e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have ce: "FunctionEntry p \<in> cfg_nodes g" using e call_endpoints_in_nodes by blast
  then show "\<forall>ns \<in> set (path (Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))])).
               fst ns \<in> cfg_nodes g"
    by auto
next
  fix callee caller p dst pars args cont
  assume ch: "\<forall>u \<in> callers callee. \<forall>ns \<in> set (path u). fst ns \<in> cfg_nodes g"
    and cof: "caller_of callee = Some caller"
    and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have contn: "cont \<in> cfg_nodes g" using e call_endpoints_in_nodes by blast
  have cin: "caller \<in> callers callee" using cof callers_caller_subset callers_refl by blast
  have "\<forall>ns \<in> set (path caller). fst ns \<in> cfg_nodes g" using ch cin by blast
  then show "\<forall>ns \<in> set (path (Resume caller callee
               (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))]))).
             fst ns \<in> cfg_nodes g"
    using contn by auto
qed

text \<open>(10) Node membership: every node observed in a valid trace belongs to
  \<^const>\<open>cfg_nodes\<close>.\<close>
lemma valid_ltr_nodes_in_cfg:
  "t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> (n, s) \<in> set (path t) \<Longrightarrow> n \<in> cfg_nodes g"
  using valid_ltr_path_nodes callers_refl by fastforce

text \<open>The sink node of a valid trace is a CFG node.\<close>
lemma valid_ltr_sink_in_nodes:
  assumes "t \<in> valid_ltr \<Gamma> gs g S"
  shows "sink_node t \<in> cfg_nodes g"
proof -
  from assms have "last (path t) \<in> set (path t)"
    using valid_ltr_path_nonempty by simp
  then have "fst (last (path t)) \<in> cfg_nodes g"
    using valid_ltr_nodes_in_cfg[OF assms] by (metis prod.collapse)
  then show ?thesis by (simp add: sink_node_def)
qed

text \<open>Monotonicity and union in the initial store set (\<open>valid_ltr_mono_S\<close>, \<open>valid_ltr_eq_UN_singleton\<close>,
  \<open>valid_ltr_Un_S\<close>) live in the theory that also carries \<open>ltr_F\<close> and \<open>valid_ltr_eq_lfp\<close>, where
  \<open>valid_ltr_mono_S\<close> is proved via \<open>lfp_mono\<close> instead of rule induction.\<close>

subsection \<open>Stable context entry invariant\<close>

definition call_enter_store :: "tyenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> cfg_node \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "call_enter_store \<Gamma> gs g c s t \<longleftrightarrow>
     (\<exists>dst pars args p cont. (c, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<and> t = call_enter \<Gamma> gs (CallEdge dst pars args) s)"

lemma key_extend_nonempty:
  "path t \<noteq> [] \<Longrightarrow> key enterc startcontext (extend t x) = key enterc startcontext t"
  by (cases t) auto

lemma entry_store_Resume_caller:
  "path caller \<noteq> [] \<Longrightarrow>
     entry_store (Resume caller callee (path caller @ [x])) = entry_store caller"
  by (simp add: entry_store_def hd_append)

text \<open>For every valid callee and every activation \<open>u\<close> in its caller chain, if \<open>u\<close> was
  created by \<open>c\<close> then \<open>u\<close>'s context is \<open>c\<close>'s context routed on \<open>u\<close>'s callee-entry store, and
  \<open>u\<close> was born from a concrete call edge at \<open>c\<close>'s sink.\<close>
lemma callee_entry_invariant:
  "callee \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow>
     \<forall>u \<in> callers callee. \<forall>c. caller_of u = Some c \<longrightarrow>
       key enterc startcontext u = enterc (sink_node c) (key enterc startcontext c) (entry_store u)
       \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store u)"
proof (induction rule: valid_ltr.induct)
  case (init s)
  then show ?case by (simp add: callers_Root)
next
  case (intra t a v s')
  show ?case
  proof (intro ballI allI impI)
    fix u c assume uin: "u \<in> callers (extend t (v, s'))" and cof: "caller_of u = Some c"
    from uin have "u = extend t (v, s') \<or> u \<in> callers t"
      using callers_extend_subset by blast
    then show "key enterc startcontext u = enterc (sink_node c) (key enterc startcontext c) (entry_store u)
               \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store u)"
    proof (rule disjE)
      assume u: "u = extend t (v, s')"
      have pt: "path t \<noteq> []" using intra.hyps(1) valid_ltr_path_nonempty by blast
      have "caller_of t = Some c" using cof u by simp
      then have "key enterc startcontext t = enterc (sink_node c) (key enterc startcontext c) (entry_store t)
                 \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store t)"
        using intra.IH callers_refl by blast
      then show ?thesis using u pt by (simp add: key_extend_nonempty)
    next
      assume "u \<in> callers t"
      then show ?thesis using intra.IH cof by blast
    qed
  qed
next
  case (call caller dst pars args p cont)
  show ?case
  proof (intro ballI allI impI)
    fix u c assume uin: "u \<in> callers (Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))])"
      and cof: "caller_of u = Some c"
    from uin have "u = Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))]
                    \<or> u \<in> callers caller"
      by (simp add: callers_Call)
    then show "key enterc startcontext u = enterc (sink_node c) (key enterc startcontext c) (entry_store u)
               \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store u)"
    proof (rule disjE)
      assume u: "u = Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))]"
      have c_eq: "c = caller" using cof u by simp
      have ces: "call_enter_store \<Gamma> gs g (sink_node caller) (sink_store caller)
                   (call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))"
        unfolding call_enter_store_def using call.hyps(2) by blast
      show ?thesis using u c_eq ces by (simp add: entry_store_def)
    next
      assume "u \<in> callers caller"
      then show ?thesis using call.IH cof by blast
    qed
  qed
next
  case (ret callee caller p dst pars args cont)
  show ?case
  proof (intro ballI allI impI)
    fix u c assume uin: "u \<in> callers (Resume caller callee
        (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))]))"
      and cof: "caller_of u = Some c"
    have cvalid: "caller \<in> valid_ltr \<Gamma> gs g S"
      using ret.hyps(1) ret.hyps(2) valid_ltr_caller_valid by blast
    have pcaller: "path caller \<noteq> []" using cvalid valid_ltr_path_nonempty by blast
    from uin have "u = Resume caller callee
        (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))])
                    \<or> u \<in> callers callee"
      using callers_Resume_subset[OF ret.hyps(2)] by blast
    then show "key enterc startcontext u = enterc (sink_node c) (key enterc startcontext c) (entry_store u)
               \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store u)"
    proof (rule disjE)
      assume u: "u = Resume caller callee
          (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))])"
      have cof': "caller_of caller = Some c" using cof u by simp
      have caller_in: "caller \<in> callers callee"
        using ret.hyps(2) callers_caller_subset callers_refl by blast
      have IHc: "key enterc startcontext caller = enterc (sink_node c) (key enterc startcontext c) (entry_store caller)
                 \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store caller)"
        using ret.IH caller_in cof' by blast
      have kres: "key enterc startcontext u = key enterc startcontext caller" using u by simp
      have esres: "entry_store u = entry_store caller"
        using u pcaller by (simp add: entry_store_Resume_caller)
      show ?thesis using IHc kres esres by simp
    next
      assume "u \<in> callers callee"
      then show ?thesis using ret.IH cof by blast
    qed
  qed
qed

(* The two conjuncts of callee_entry_invariant, specialized to u = callee (via
   callers_refl) instead of quantified over every ancestor; downstream proofs
   cite these directly instead of repeating the
   [OF ..., THEN bspec, OF callers_refl, rule_format, OF ...] instantiation
   chain and then splitting the result via THEN conjunct1/2. *)
lemma callee_entry_invariant_keyD:
  assumes callee_val: "callee \<in> valid_ltr \<Gamma> gs g S"
    and cof: "caller_of callee = Some caller"
  shows "key enterc startcontext callee
           = enterc (sink_node caller) (key enterc startcontext caller) (entry_store callee)"
  using callee_entry_invariant[OF callee_val, THEN bspec, OF callers_refl, rule_format, OF cof]
  by (rule conjunct1)

lemma callee_entry_invariant_call_enterD:
  assumes callee_val: "callee \<in> valid_ltr \<Gamma> gs g S"
    and cof: "caller_of callee = Some caller"
  shows "call_enter_store \<Gamma> gs g (sink_node caller) (sink_store caller) (entry_store callee)"
  using callee_entry_invariant[OF callee_val, THEN bspec, OF callers_refl, rule_format, OF cof]
  by (rule conjunct2)

subsection \<open>Admissible context entry invariant\<close>

text \<open>The \<open>ctx_key\<close> analogue of \<open>callee_entry_invariant\<close>: not an equation, since \<open>admiss\<close> may
  relate several child contexts to a caller context, but a bidirectional characterization ---
  \<open>u\<close>'s admissible contexts are exactly those \<open>admiss\<close> reaches from some admissible context of
  its creator \<open>c\<close>, applied to \<open>u\<close>'s own callee-entry store. This is what lets a COMB argument
  construct the callee's context directly from the caller's chosen one, rather than
  rediscovering it after the fact.\<close>
lemma ctx_key_extend_nonempty:
  "path t \<noteq> [] \<Longrightarrow> ctx_key admiss startcontext (extend t x) c \<longleftrightarrow> ctx_key admiss startcontext t c"
proof (cases t)
  case (Root p)
  then show ?thesis by (auto elim: ctx_key_RootE intro: ctx_key_Root)
next
  case (Call caller p)
  assume "path t \<noteq> []"
  with Call show ?thesis
    by (auto simp: hd_append elim!: ctx_key_CallE intro: ctx_key_Call)
next
  case (Resume current callee p)
  then show ?thesis by (auto elim: ctx_key_ResumeE intro: ctx_key_Resume)
qed

lemma ctx_key_entry_invariant:
  "callee \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow>
     \<forall>u \<in> callers callee. \<forall>c. caller_of u = Some c \<longrightarrow>
       (\<forall>c2. ctx_key admiss startcontext u c2 \<longleftrightarrow>
             (\<exists>c1. ctx_key admiss startcontext c c1 \<and> admiss (sink_node c) c1 (entry_store u) c2))
       \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store u)"
proof (induction rule: valid_ltr.induct)
  case (init s)
  then show ?case by (simp add: callers_Root)
next
  case (intra t a v s')
  show ?case
  proof (intro ballI allI impI)
    fix u c assume uin: "u \<in> callers (extend t (v, s'))" and cof: "caller_of u = Some c"
    from uin have "u = extend t (v, s') \<or> u \<in> callers t"
      using callers_extend_subset by blast
    then show "(\<forall>c2. ctx_key admiss startcontext u c2 \<longleftrightarrow>
                 (\<exists>c1. ctx_key admiss startcontext c c1 \<and> admiss (sink_node c) c1 (entry_store u) c2))
               \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store u)"
    proof (rule disjE)
      assume u: "u = extend t (v, s')"
      have pt: "path t \<noteq> []" using intra.hyps(1) valid_ltr_path_nonempty by blast
      have "caller_of t = Some c" using cof u by simp
      then have IH: "(\<forall>c2. ctx_key admiss startcontext t c2 \<longleftrightarrow>
                       (\<exists>c1. ctx_key admiss startcontext c c1 \<and> admiss (sink_node c) c1 (entry_store t) c2))
                     \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store t)"
        using intra.IH callers_refl by blast
      then show ?thesis using u pt by (simp add: ctx_key_extend_nonempty entry_store_extend_valid intra.hyps(1))
    next
      assume "u \<in> callers t"
      then show ?thesis using intra.IH cof by blast
    qed
  qed
next
  case (call caller dst pars args p cont)
  show ?case
  proof (intro ballI allI impI)
    fix u c assume uin: "u \<in> callers (Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))])"
      and cof: "caller_of u = Some c"
    from uin have "u = Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))]
                    \<or> u \<in> callers caller"
      by (simp add: callers_Call)
    then show "(\<forall>c2. ctx_key admiss startcontext u c2 \<longleftrightarrow>
                 (\<exists>c1. ctx_key admiss startcontext c c1 \<and> admiss (sink_node c) c1 (entry_store u) c2))
               \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store u)"
    proof (rule disjE)
      assume u: "u = Call caller [(FunctionEntry p, call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))]"
      have c_eq: "c = caller" using cof u by simp
      have ces: "call_enter_store \<Gamma> gs g (sink_node caller) (sink_store caller)
                   (call_enter \<Gamma> gs (CallEdge dst pars args) (sink_store caller))"
        unfolding call_enter_store_def using call.hyps(2) by blast
      have iff: "\<forall>c2. ctx_key admiss startcontext u c2 \<longleftrightarrow>
                   (\<exists>c1. ctx_key admiss startcontext caller c1 \<and> admiss (sink_node caller) c1 (entry_store u) c2)"
        using u by (auto simp: entry_store_def elim!: ctx_key_CallE intro: ctx_key_Call)
      show ?thesis using u c_eq ces iff by (simp add: entry_store_def)
    next
      assume "u \<in> callers caller"
      then show ?thesis using call.IH cof by blast
    qed
  qed
next
  case (ret callee caller p dst pars args cont)
  show ?case
  proof (intro ballI allI impI)
    fix u c assume uin: "u \<in> callers (Resume caller callee
        (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))]))"
      and cof: "caller_of u = Some c"
    have cvalid: "caller \<in> valid_ltr \<Gamma> gs g S"
      using ret.hyps(1) ret.hyps(2) valid_ltr_caller_valid by blast
    have pcaller: "path caller \<noteq> []" using cvalid valid_ltr_path_nonempty by blast
    from uin have "u = Resume caller callee
        (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))])
                    \<or> u \<in> callers callee"
      using callers_Resume_subset[OF ret.hyps(2)] by blast
    then show "(\<forall>c2. ctx_key admiss startcontext u c2 \<longleftrightarrow>
                 (\<exists>c1. ctx_key admiss startcontext c c1 \<and> admiss (sink_node c) c1 (entry_store u) c2))
               \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store u)"
    proof (rule disjE)
      assume u: "u = Resume caller callee
          (path caller @ [(cont, combine_collect \<Gamma> gs dst (sink_store caller) (sink_store callee))])"
      have cof': "caller_of caller = Some c" using cof u by simp
      have caller_in: "caller \<in> callers callee"
        using ret.hyps(2) callers_caller_subset callers_refl by blast
      have IHc: "(\<forall>c2. ctx_key admiss startcontext caller c2 \<longleftrightarrow>
                   (\<exists>c1. ctx_key admiss startcontext c c1 \<and> admiss (sink_node c) c1 (entry_store caller) c2))
                 \<and> call_enter_store \<Gamma> gs g (sink_node c) (sink_store c) (entry_store caller)"
        using ret.IH caller_in cof' by blast
      have kres: "\<And>c2. ctx_key admiss startcontext u c2 \<longleftrightarrow> ctx_key admiss startcontext caller c2"
        using u by (auto elim!: ctx_key_ResumeE intro: ctx_key_Resume)
      have esres: "entry_store u = entry_store caller"
        using u pcaller by (simp add: entry_store_Resume_caller)
      show ?thesis using IHc kres esres by simp
    next
      assume "u \<in> callers callee"
      then show ?thesis using ret.IH cof by blast
    qed
  qed
qed

text \<open>Every trace has at least one admissible context, provided \<open>admiss\<close> can always continue
  --- the analysis-side analogue of \<open>route\<close> always producing some context. Needed to recover
  a callee's admissible context from its caller's, rather than merely knowing one exists in
  isolation.\<close>
lemma ctx_key_exists:
  assumes tot: "\<And>u c s. \<exists>c'. admiss u c s c'"
  shows "\<exists>c. ctx_key admiss startcontext t c"
proof (induction t)
  case (Root p)
  then show ?case by (auto intro: ctx_key_Root)
next
  case (Call parent p)
  then obtain c where c: "ctx_key admiss startcontext parent c" by blast
  from tot obtain c' where "admiss (sink_node parent) c (snd (hd p)) c'" by blast
  with c show ?case by (auto intro: ctx_key_Call)
next
  case (Resume current callee p)
  then obtain c where "ctx_key admiss startcontext current c" by blast
  then show ?case by (auto intro: ctx_key_Resume)
qed

lemma ctx_key_entry_invariant_iff:
  assumes callee_val: "callee \<in> valid_ltr \<Gamma> gs g S"
    and cof: "caller_of callee = Some caller"
  shows "ctx_key admiss startcontext callee c2 \<longleftrightarrow>
         (\<exists>c1. ctx_key admiss startcontext caller c1 \<and> admiss (sink_node caller) c1 (entry_store callee) c2)"
  using ctx_key_entry_invariant[OF callee_val, THEN bspec, OF callers_refl, rule_format, OF cof,
      THEN conjunct1]
  by metis

lemma ctx_key_entry_invariant_call_enterD:
  assumes callee_val: "callee \<in> valid_ltr \<Gamma> gs g S"
    and cof: "caller_of callee = Some caller"
  shows "call_enter_store \<Gamma> gs g (sink_node caller) (sink_store caller) (entry_store callee)"
  using ctx_key_entry_invariant[OF callee_val, THEN bspec, OF callers_refl, rule_format, OF cof]
  by (rule conjunct2)

subsection \<open>The activation-indexed context collecting\<close>

text \<open>The activation-sensitive collecting is the sink stores of valid traces reaching \<open>v\<close>
  admissibly assigned the queried context \<open>c\<close>, via \<^const>\<open>ctx_key\<close>. Exact activation
  matching --- one context per trace, computed by decoding the concrete entered store --- is
  the \<open>admiss = admiss_exact enterc\<close> instance; an \<open>admiss\<close> that ignores its concrete-store
  argument (for instance, one derived from an abstract routing result) instead lets one
  admissible context stand for every concrete execution the abstract analysis represents by
  it, without needing \<open>admiss\<close> itself to be multi-valued.\<close>

definition activation_collect ::
  "tyenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> (cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c
     \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store set" where
  "activation_collect \<Gamma> gs admiss startcontext g S v c =
     {sink_store t | t. t \<in> valid_ltr \<Gamma> gs g S \<and> sink_node t = v \<and> ctx_key admiss startcontext t c}"

lemma activation_collect_I:
  "t \<in> valid_ltr \<Gamma> gs g S \<Longrightarrow> sink_node t = v \<Longrightarrow> ctx_key admiss startcontext t c
   \<Longrightarrow> sink_store t \<in> activation_collect \<Gamma> gs admiss startcontext g S v c"
  unfolding activation_collect_def by blast

text \<open>Every collected state has a valid trace witness admissibly assigned the queried \<open>c\<close>.\<close>
lemma activation_collect_E:
  assumes "s \<in> activation_collect \<Gamma> gs admiss startcontext g S v c"
  obtains t where "t \<in> valid_ltr \<Gamma> gs g S" "sink_node t = v" "ctx_key admiss startcontext t c"
    "sink_store t = s"
  using assms unfolding activation_collect_def by blast



end
