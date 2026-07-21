theory CFG_Local_Trace
  imports CFG_Def
begin

section \<open>Activation-local concrete traces\<close>

text \<open>
  A concrete, analysis-independent reference semantics for the procedure-aware CFG.  A value
  of type \<open>ltr\<close> represents one procedure activation together with its concrete ancestry:
  its local path of \<open>(cfg_node, store)\<close> pairs, the caller it was created from, and --- once
  it has returned into a caller --- the completed callee it composed.  Local traces are the
  concrete objects; activation contexts are computed afterwards by a projection (\<open>key\<close>),
  never stored inside the trace.

  The trace rides on the two relations of \<^typ>\<open>cfg\<close>: \<open>intra\<close> for context-preserving
  extension (including \<open>EA_Ret\<close> reaching \<open>FunctionResult p\<close>) and \<open>calls\<close> for entering a
  callee and for recovering the continuation at return.  There is no call/return matching
  side relation and no exit node: a \<open>calls\<close> edge already names the callee entry and the
  continuation, and a return is an ordinary \<open>intra\<close> step into \<open>FunctionResult p\<close>.

  Semantic boundary.  The trace represents only procedure-activation structure.  Lexical
  scopes are compiled into \<open>intra\<close> control flow and are not activations.  The intended
  correspondence for the later compiler proof (not proved here) is: a source
  \<open>ActivationFrame\<close> corresponds to \<open>Call\<close>/\<open>Resume\<close> structure; a source \<open>LexicalFrame\<close>
  to \<open>intra\<close> execution; a source \<open>Unwind\<close> to the path to \<open>EA_Ret\<close> / \<open>FunctionResult\<close>.

  Call-entry and return-value transfer are the established concrete primitives:
  \<^const>\<open>enter_state\<close> (globals preserved, locals reset to zero) at a call, and
  \<^const>\<open>combine_collect\<close> (callee globals, caller locals, callee \<open>ret_var\<close> written into
  the destination) at a return.  Actual-to-formal parameter binding is not performed in the
  trace kernel; it is compiled into \<open>intra\<close> edges and belongs to the compiler stage.
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
  | Call ltr "(cfg_node * store) list"
  | Resume ltr ltr "(cfg_node * store) list"

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
  caller context on the callee-entry store; a \<^const>\<open>Resume\<close> keeps the resumed caller's own
  context, so a completed call does not repartition the caller.\<close>
fun key :: "('c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ltr \<Rightarrow> 'c" where
  "key enterc seedc (Root _)                  = seedc"
| "key enterc seedc (Call parent p)           = enterc (key enterc seedc parent) (snd (hd p))"
| "key enterc seedc (Resume current callee _) = key enterc seedc current"

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

inductive_set valid_ltr :: "cfg \<Rightarrow> store set \<Rightarrow> ltr set" for g S where
  init:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> valid_ltr g S"
| intra:
    "t \<in> valid_ltr g S
     \<Longrightarrow> (sink_node t, a, v) \<in> intra g
     \<Longrightarrow> edge_step a (sink_store t) = Some s'
     \<Longrightarrow> extend t (v, s') \<in> valid_ltr g S"
| call:
    "caller \<in> valid_ltr g S
     \<Longrightarrow> (sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g
     \<Longrightarrow> Call caller [(FunctionEntry p, enter_state (sink_store caller))] \<in> valid_ltr g S"
| ret:
    "callee \<in> valid_ltr g S
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> sink_node callee = FunctionResult p
     \<Longrightarrow> (sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g
     \<Longrightarrow> Resume caller callee
           (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])
         \<in> valid_ltr g S"

inductive_cases valid_ltrE:
  "t \<in> valid_ltr g S"

inductive_cases valid_ltr_RootE [elim]:
  "Root p \<in> valid_ltr g S"

inductive_cases valid_ltr_CallE [elim]:
  "Call caller p \<in> valid_ltr g S"

inductive_cases valid_ltr_ResumeE [elim]:
  "Resume caller callee p \<in> valid_ltr g S"

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
  "t \<in> valid_ltr g S \<Longrightarrow> path t \<noteq> []"
  by (induction t rule: valid_ltr.induct) auto

lemma entry_store_extend [simp]:
  assumes "path t \<noteq> []"
  shows "entry_store (extend t x) = entry_store t"
  using assms by (simp add: entry_store_def)

lemma entry_store_extend_valid:
  "t \<in> valid_ltr g S \<Longrightarrow> entry_store (extend t x) = entry_store t"
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
  "u \<in> valid_ltr g S \<Longrightarrow> u = Call cc q \<Longrightarrow> cc \<in> valid_ltr g S"
proof (induction arbitrary: cc q rule: valid_ltr.induct)
  case (intra t a v s')
  from intra.prems obtain q' where "t = Call cc q'"
    by (cases t) auto
  then show ?case using intra.IH by simp
qed auto

text \<open>A valid \<^const>\<open>Resume\<close> retains its callee as a valid trace, and its frozen caller is
  forced to be exactly \<open>caller_of callee\<close> --- a return cannot invent a caller.\<close>
lemma valid_ltr_Resume_fields:
  "u \<in> valid_ltr g S \<Longrightarrow> u = Resume cc dd q
   \<Longrightarrow> dd \<in> valid_ltr g S \<and> caller_of dd = Some cc"
proof (induction arbitrary: cc dd q rule: valid_ltr.induct)
  case (intra t a v s')
  from intra.prems obtain q' where "t = Resume cc dd q'"
    by (cases t) auto
  then show ?case using intra.IH by simp
qed auto

text \<open>Every caller recovered from a valid trace by \<^const>\<open>caller_of\<close> is itself valid.\<close>
lemma valid_ltr_caller_valid:
  "t \<in> valid_ltr g S \<Longrightarrow> caller_of t = Some c \<Longrightarrow> c \<in> valid_ltr g S"
proof (induction t arbitrary: c)
  case (Root x)
  then show ?case by simp
next
  case (Call caller p)
  have "caller \<in> valid_ltr g S"
    using valid_ltr_Call_caller_valid[OF Call.prems(1) refl] .
  with Call.prems(2) show ?case by simp
next
  case (Resume caller callee p)
  from valid_ltr_Resume_fields[OF Resume.prems(1) refl]
  have cd: "callee \<in> valid_ltr g S" "caller_of callee = Some caller" by auto
  have cv: "caller \<in> valid_ltr g S" using Resume.IH(2)[OF cd(1)] cd(2) by simp
  from Resume.prems(2) have "caller_of caller = Some c" by simp
  then show ?case using Resume.IH(1)[OF cv] by simp
qed

lemma caller_of_unique:
  "caller_of t = Some c1 \<Longrightarrow> caller_of t = Some c2 \<Longrightarrow> c1 = c2"
  by simp

lemma valid_ltr_Call_path_nonempty:
  "Call caller p \<in> valid_ltr g S \<Longrightarrow> p \<noteq> []"
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
    by (subst callers.simps) (simp add: caller_of_extend)
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

subsection \<open>Required trace obligations\<close>

text \<open>(1) Call provenance: every \<^const>\<open>Call\<close> activation is justified by a concrete member
  of \<open>calls g\<close> leaving its caller's node.\<close>
lemma valid_ltr_Call_provenance:
  assumes "Call caller q \<in> valid_ltr g S"
  shows "\<exists>dst args p cont. (sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g"
proof -
  have "u \<in> valid_ltr g S \<Longrightarrow>
          \<forall>ca q. u = Call ca q \<longrightarrow>
            (\<exists>dst args p cont. (sink_node ca, CallEdge dst args, FunctionEntry p, cont) \<in> calls g)"
    for u
  proof (induction rule: valid_ltr.induct)
    case (intra t a v s')
    show ?case
    proof (intro allI impI)
      fix ca q assume "extend t (v, s') = Call ca q"
      then obtain q' where "t = Call ca q'" by (cases t) auto
      with intra.IH show
        "\<exists>dst args p cont. (sink_node ca, CallEdge dst args, FunctionEntry p, cont) \<in> calls g"
        by blast
    qed
  qed auto
  with assms show ?thesis by blast
qed

text \<open>(2) Entry correctness: a called activation begins at the callee-entry node recorded
  by a concrete call edge.\<close>
lemma valid_ltr_Call_entry_node:
  assumes "Call caller q \<in> valid_ltr g S"
  shows "\<exists>dst args p cont. (sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g
          \<and> fst (hd q) = FunctionEntry p"
proof -
  have "u \<in> valid_ltr g S \<Longrightarrow>
          \<forall>ca q. u = Call ca q \<longrightarrow>
            (\<exists>dst args p cont. (sink_node ca, CallEdge dst args, FunctionEntry p, cont) \<in> calls g
               \<and> fst (hd q) = FunctionEntry p)"
    for u
  proof (induction rule: valid_ltr.induct)
    case (call caller dst args p cont)
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
        "\<exists>dst args p cont. (sink_node ca, CallEdge dst args, FunctionEntry p, cont) \<in> calls g
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
  assumes "Resume caller callee q \<in> valid_ltr g S"
  shows "\<exists>dst args p cont. sink_node callee = FunctionResult p
          \<and> (sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g"
proof -
  have "u \<in> valid_ltr g S \<Longrightarrow>
          \<forall>cc dd q. u = Resume cc dd q \<longrightarrow>
            (\<exists>dst args p cont. sink_node dd = FunctionResult p
               \<and> (sink_node cc, CallEdge dst args, FunctionEntry p, cont) \<in> calls g)"
    for u
  proof (induction rule: valid_ltr.induct)
    case (intra t a v s')
    show ?case
    proof (intro allI impI)
      fix cc dd q assume "extend t (v, s') = Resume cc dd q"
      then obtain q' where "t = Resume cc dd q'" by (cases t) auto
      with intra.IH show
        "\<exists>dst args p cont. sink_node dd = FunctionResult p
           \<and> (sink_node cc, CallEdge dst args, FunctionEntry p, cont) \<in> calls g"
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
  assumes "callee \<in> valid_ltr g S"
    and "caller_of callee = Some caller"
    and "sink_node callee = FunctionResult p"
    and "(sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g"
  shows "sink_node (Resume caller callee
           (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))]))
         = cont"
  by (simp add: sink_node_def)

text \<open>(6) Nearest activation discipline: a \<^const>\<open>Resume\<close> resumes the callee's immediate
  caller, not an ancestor.  The frozen caller is forced to be \<open>caller_of callee\<close>.\<close>
lemma valid_ltr_Resume_immediate_caller:
  "Resume caller callee q \<in> valid_ltr g S \<Longrightarrow> caller_of callee = Some caller"
  using valid_ltr_Resume_fields by blast

text \<open>(9) Flat CFG reduction: when \<open>calls g = {}\<close>, every valid trace is a \<^const>\<open>Root\<close>; no
  \<^const>\<open>Call\<close> or \<^const>\<open>Resume\<close> can arise.\<close>
lemma valid_ltr_flat_root:
  assumes "flat_cfg g" and "t \<in> valid_ltr g S"
  shows "\<exists>p. t = Root p"
  using assms(2)
proof (induction rule: valid_ltr.induct)
  case (intra t a v s')
  then obtain p where "t = Root p" by blast
  then show ?case by (cases t) auto
next
  case (call caller dst args p cont)
  then show ?case using assms(1) by (simp add: flat_cfg_def)
next
  case (ret callee caller p dst args cont)
  then show ?case using assms(1) by (simp add: flat_cfg_def)
qed simp

subsection \<open>Node membership\<close>

text \<open>The nodes observed along a valid trace, and along its whole caller chain, all belong
  to \<^const>\<open>cfg_nodes\<close>.\<close>
lemma valid_ltr_path_nodes:
  "t \<in> valid_ltr g S \<Longrightarrow>
     \<forall>u \<in> callers t. \<forall>ns \<in> set (path u). fst ns \<in> cfg_nodes g"
proof (induction rule: valid_ltr.induct)
  case (init s)
  then show ?case by (simp add: callers_Root cfg_entry_in_nodes)
next
  case (intra t a v s')
  have vnode: "v \<in> cfg_nodes g" using intra.hyps(2) intra_endpoints_in_nodes by blast
  show ?case
  proof (intro ballI)
    fix u ns assume uin: "u \<in> callers (extend t (v, s'))" and nsin: "ns \<in> set (path u)"
    from uin have "u = extend t (v, s') \<or> u \<in> callers t"
      using callers_extend_subset by blast
    then show "fst ns \<in> cfg_nodes g"
    proof
      assume u: "u = extend t (v, s')"
      have "ns \<in> set (path t) \<or> ns = (v, s')" using nsin u by auto
      then show ?thesis using intra.IH callers_refl vnode by auto
    next
      assume "u \<in> callers t"
      then show ?thesis using intra.IH nsin by blast
    qed
  qed
next
  case (call caller dst args p cont)
  have ce: "FunctionEntry p \<in> cfg_nodes g"
    using call.hyps(2) call_endpoints_in_nodes by blast
  show ?case
  proof (intro ballI)
    fix u ns assume uin: "u \<in> callers (Call caller [(FunctionEntry p, enter_state (sink_store caller))])"
      and nsin: "ns \<in> set (path u)"
    from uin have "u = Call caller [(FunctionEntry p, enter_state (sink_store caller))]
                    \<or> u \<in> callers caller"
      by (simp add: callers_Call)
    then show "fst ns \<in> cfg_nodes g"
    proof
      assume "u = Call caller [(FunctionEntry p, enter_state (sink_store caller))]"
      then show ?thesis using nsin ce by auto
    next
      assume "u \<in> callers caller"
      then show ?thesis using call.IH nsin by blast
    qed
  qed
next
  case (ret callee caller p dst args cont)
  have contn: "cont \<in> cfg_nodes g" using ret.hyps(4) call_endpoints_in_nodes by blast
  have cin: "caller \<in> callers callee"
    using ret.hyps(2) callers_caller_subset callers_refl by blast
  show ?case
  proof (intro ballI)
    fix u ns
    assume uin: "u \<in> callers (Resume caller callee
                    (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))]))"
      and nsin: "ns \<in> set (path u)"
    from uin have "u = Resume caller callee
                     (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])
                    \<or> u \<in> callers callee"
      using callers_Resume_subset[OF ret.hyps(2)] by blast
    then show "fst ns \<in> cfg_nodes g"
    proof
      assume u: "u = Resume caller callee
                   (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])"
      have "ns \<in> set (path caller) \<or> fst ns = cont" using nsin u by auto
      then show ?thesis using ret.IH cin contn by auto
    next
      assume "u \<in> callers callee"
      then show ?thesis using ret.IH nsin by blast
    qed
  qed
qed

text \<open>(10) Node membership: every node observed in a valid trace belongs to
  \<^const>\<open>cfg_nodes\<close>.\<close>
lemma valid_ltr_nodes_in_cfg:
  "t \<in> valid_ltr g S \<Longrightarrow> (n, s) \<in> set (path t) \<Longrightarrow> n \<in> cfg_nodes g"
  using valid_ltr_path_nodes callers_refl by fastforce

subsection \<open>Stable context entry invariant\<close>

definition call_enter_store :: "cfg \<Rightarrow> cfg_node \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "call_enter_store g c s t \<longleftrightarrow>
     (\<exists>dst args p cont. (c, CallEdge dst args, FunctionEntry p, cont) \<in> calls g)
     \<and> t = enter_state s"

lemma key_extend_nonempty:
  "path t \<noteq> [] \<Longrightarrow> key enterc seedc (extend t x) = key enterc seedc t"
  by (cases t) auto

lemma entry_store_Resume_caller:
  "path caller \<noteq> [] \<Longrightarrow>
     entry_store (Resume caller callee (path caller @ [x])) = entry_store caller"
  by (simp add: entry_store_def hd_append)

text \<open>For every valid callee and every activation \<open>u\<close> in its caller chain, if \<open>u\<close> was
  created by \<open>c\<close> then \<open>u\<close>'s context is \<open>c\<close>'s context routed on \<open>u\<close>'s callee-entry store, and
  \<open>u\<close> was born from a concrete call edge at \<open>c\<close>'s sink.\<close>
lemma callee_entry_invariant:
  "callee \<in> valid_ltr g S \<Longrightarrow>
     \<forall>u \<in> callers callee. \<forall>c. caller_of u = Some c \<longrightarrow>
       key enterc seedc u = enterc (key enterc seedc c) (entry_store u)
       \<and> call_enter_store g (sink_node c) (sink_store c) (entry_store u)"
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
    then show "key enterc seedc u = enterc (key enterc seedc c) (entry_store u)
               \<and> call_enter_store g (sink_node c) (sink_store c) (entry_store u)"
    proof
      assume u: "u = extend t (v, s')"
      have pt: "path t \<noteq> []" using intra.hyps(1) valid_ltr_path_nonempty by blast
      have "caller_of t = Some c" using cof u by simp
      then have "key enterc seedc t = enterc (key enterc seedc c) (entry_store t)
                 \<and> call_enter_store g (sink_node c) (sink_store c) (entry_store t)"
        using intra.IH callers_refl by blast
      then show ?thesis using u pt by (simp add: key_extend_nonempty)
    next
      assume "u \<in> callers t"
      then show ?thesis using intra.IH cof by blast
    qed
  qed
next
  case (call caller dst args p cont)
  show ?case
  proof (intro ballI allI impI)
    fix u c assume uin: "u \<in> callers (Call caller [(FunctionEntry p, enter_state (sink_store caller))])"
      and cof: "caller_of u = Some c"
    from uin have "u = Call caller [(FunctionEntry p, enter_state (sink_store caller))]
                    \<or> u \<in> callers caller"
      by (simp add: callers_Call)
    then show "key enterc seedc u = enterc (key enterc seedc c) (entry_store u)
               \<and> call_enter_store g (sink_node c) (sink_store c) (entry_store u)"
    proof
      assume u: "u = Call caller [(FunctionEntry p, enter_state (sink_store caller))]"
      have c_eq: "c = caller" using cof u by simp
      have ces: "call_enter_store g (sink_node caller) (sink_store caller)
                   (enter_state (sink_store caller))"
        unfolding call_enter_store_def using call.hyps(2) by blast
      show ?thesis using u c_eq ces by (simp add: entry_store_def)
    next
      assume "u \<in> callers caller"
      then show ?thesis using call.IH cof by blast
    qed
  qed
next
  case (ret callee caller p dst args cont)
  show ?case
  proof (intro ballI allI impI)
    fix u c assume uin: "u \<in> callers (Resume caller callee
        (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))]))"
      and cof: "caller_of u = Some c"
    have cvalid: "caller \<in> valid_ltr g S"
      using ret.hyps(1) ret.hyps(2) valid_ltr_caller_valid by blast
    have pcaller: "path caller \<noteq> []" using cvalid valid_ltr_path_nonempty by blast
    from uin have "u = Resume caller callee
        (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])
                    \<or> u \<in> callers callee"
      using callers_Resume_subset[OF ret.hyps(2)] by blast
    then show "key enterc seedc u = enterc (key enterc seedc c) (entry_store u)
               \<and> call_enter_store g (sink_node c) (sink_store c) (entry_store u)"
    proof
      assume u: "u = Resume caller callee
          (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])"
      have cof': "caller_of caller = Some c" using cof u by simp
      have caller_in: "caller \<in> callers callee"
        using ret.hyps(2) callers_caller_subset callers_refl by blast
      have IHc: "key enterc seedc caller = enterc (key enterc seedc c) (entry_store caller)
                 \<and> call_enter_store g (sink_node c) (sink_store c) (entry_store caller)"
        using ret.IH caller_in cof' by blast
      have kres: "key enterc seedc u = key enterc seedc caller" using u by simp
      have esres: "entry_store u = entry_store caller"
        using u pcaller by (simp add: entry_store_Resume_caller)
      show ?thesis using IHc kres esres by simp
    next
      assume "u \<in> callers callee"
      then show ?thesis using ret.IH cof by blast
    qed
  qed
qed

subsection \<open>The activation-indexed context collecting\<close>

text \<open>The activation-sensitive collecting is the sink stores of valid traces reaching \<open>v\<close>
  whose activation context is \<open>c\<close>.\<close>

definition activation_collect ::
  "('c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store set" where
  "activation_collect enterc seedc g S v c =
     {sink_store t | t. t \<in> valid_ltr g S \<and> sink_node t = v \<and> key enterc seedc t = c}"

subsection \<open>Witness: nested returns resume the immediate caller\<close>

text \<open>A two-level program \<open>main -> f -> g\<close> where \<open>g\<close> returns into \<open>f\<close> and \<open>f\<close> returns into
  \<open>main\<close>.  It exercises every rule and shows \<open>g\<close>'s return resumes \<open>f\<close> (the nearest
  activation), while \<open>f\<close>'s return recovers \<open>main\<close> through the resumed \<open>f\<close>.\<close>

definition mn :: pname where "mn = ''main''"
definition pf :: pname where "pf = ''f''"
definition pg :: pname where "pg = ''g''"

definition nest_cfg :: cfg where
  "nest_cfg =
     \<lparr> intra =
         { (FunctionEntry pg, EA_Ret None pg, FunctionResult pg),
           (Statement 200,    EA_Ret None pf, FunctionResult pf) },
       calls =
         { (FunctionEntry mn, CallEdge None [], FunctionEntry pf, Statement 100),
           (FunctionEntry pf, CallEdge None [], FunctionEntry pg, Statement 200) },
       cfg_entry = FunctionEntry mn \<rparr>"

lemmas nest_defs = nest_cfg_def mn_def pf_def pg_def

lemma nested_valid_ltr_example:
  assumes s0: "s0 \<in> S"
  shows "\<exists>main0 f0 g1 f' final.
           g1 \<in> valid_ltr nest_cfg S \<and> caller_of g1 = Some f0
         \<and> f' \<in> valid_ltr nest_cfg S \<and> caller_of f' = Some main0
         \<and> final \<in> valid_ltr nest_cfg S \<and> sink_node final = Statement 100"
proof -
  define main0 where "main0 = Root [(cfg_entry nest_cfg, s0)]"
  have main_mem: "main0 \<in> valid_ltr nest_cfg S"
    unfolding main0_def by (rule valid_ltr.init[OF s0])
  have m_sn: "sink_node main0 = FunctionEntry mn"
    by (simp add: main0_def nest_defs)
  have ecall_f: "(sink_node main0, CallEdge None [], FunctionEntry pf, Statement 100) \<in> calls nest_cfg"
    by (simp add: m_sn nest_defs)
  define f0 where "f0 = Call main0 [(FunctionEntry pf, enter_state (sink_store main0))]"
  have f_mem: "f0 \<in> valid_ltr nest_cfg S"
    unfolding f0_def by (rule valid_ltr.call[OF main_mem ecall_f])
  have f_sn: "sink_node f0 = FunctionEntry pf" by (simp add: f0_def)
  have ecall_g: "(sink_node f0, CallEdge None [], FunctionEntry pg, Statement 200) \<in> calls nest_cfg"
    by (simp add: f_sn nest_defs)
  define g0 where "g0 = Call f0 [(FunctionEntry pg, enter_state (sink_store f0))]"
  have g_mem: "g0 \<in> valid_ltr nest_cfg S"
    unfolding g0_def by (rule valid_ltr.call[OF f_mem ecall_g])
  have g_sn: "sink_node g0 = FunctionEntry pg" by (simp add: g0_def)
  have eRg: "(sink_node g0, EA_Ret None pg, FunctionResult pg) \<in> intra nest_cfg"
    by (simp add: g_sn nest_defs)
  have stRg: "edge_step (EA_Ret None pg) (sink_store g0) = Some (sink_store g0)"
    by simp
  define g1 where "g1 = extend g0 (FunctionResult pg, sink_store g0)"
  have g1_mem: "g1 \<in> valid_ltr nest_cfg S"
    unfolding g1_def by (rule valid_ltr.intra[OF g_mem eRg stRg])
  have g1_sn: "sink_node g1 = FunctionResult pg" by (simp add: g1_def)
  have g1_caller: "caller_of g1 = Some f0" by (simp add: g1_def g0_def)
  \<comment> \<open>g returns into f (the immediate caller), not main\<close>
  define f' where
    "f' = Resume f0 g1 (path f0 @ [(Statement 200, combine_collect None (sink_store f0) (sink_store g1))])"
  have f'_mem: "f' \<in> valid_ltr nest_cfg S"
    unfolding f'_def
    by (rule valid_ltr.ret[OF g1_mem g1_caller g1_sn], simp add: f_sn nest_defs)
  have f'_sn: "sink_node f' = Statement 200" by (simp add: f'_def sink_node_def)
  have f'_caller: "caller_of f' = Some main0" by (simp add: f'_def f0_def)
  have eRf: "(sink_node f', EA_Ret None pf, FunctionResult pf) \<in> intra nest_cfg"
    by (simp add: f'_sn nest_defs)
  have stRf: "edge_step (EA_Ret None pf) (sink_store f') = Some (sink_store f')"
    by simp
  define f2 where "f2 = extend f' (FunctionResult pf, sink_store f')"
  have f2_mem: "f2 \<in> valid_ltr nest_cfg S"
    unfolding f2_def by (rule valid_ltr.intra[OF f'_mem eRf stRf])
  have f2_sn: "sink_node f2 = FunctionResult pf" by (simp add: f2_def)
  have f2_caller: "caller_of f2 = Some main0" by (simp add: f2_def f'_def f0_def)
  have ecall_f2: "(sink_node main0, CallEdge None [], FunctionEntry pf, Statement 100) \<in> calls nest_cfg"
    by (simp add: m_sn nest_defs)
  define final where
    "final = Resume main0 f2 (path main0 @ [(Statement 100, combine_collect None (sink_store main0) (sink_store f2))])"
  have final_mem: "final \<in> valid_ltr nest_cfg S"
    unfolding final_def by (rule valid_ltr.ret[OF f2_mem f2_caller f2_sn ecall_f2])
  have final_sn: "sink_node final = Statement 100" by (simp add: final_def sink_node_def)
  from g1_mem g1_caller f'_mem f'_caller final_mem final_sn show ?thesis by blast
qed

subsection \<open>Witness: multiple return paths into one result\<close>

text \<open>Procedure \<open>pf\<close> reaches \<open>FunctionResult pf\<close> through two distinct intra branches;
  \<open>main\<close> calls it with continuation \<open>Statement 100\<close>.  Both branches resume through that same
  continuation.\<close>

definition bpos :: bexp where "bpos = Less (BaseN (AExp.N 0)) (BaseN (AExp.V ''Gx''))"

definition mret_cfg :: cfg where
  "mret_cfg =
     \<lparr> intra =
         { (FunctionEntry pf, EA_Assume bpos,    Statement 0),
           (Statement 0,      EA_Ret None pf,    FunctionResult pf),
           (FunctionEntry pf, EA_AssumeNot bpos, Statement 1),
           (Statement 1,      EA_Ret None pf,    FunctionResult pf) },
       calls =
         { (FunctionEntry mn, CallEdge None [], FunctionEntry pf, Statement 100) },
       cfg_entry = FunctionEntry mn \<rparr>"

lemmas mret_defs = mret_cfg_def mn_def pf_def bpos_def

lemma multi_return_join:
  "\<exists>t1 t2 c1 c2.
      t1 \<in> valid_ltr mret_cfg UNIV \<and> t2 \<in> valid_ltr mret_cfg UNIV \<and> t1 \<noteq> t2
    \<and> sink_node t1 = FunctionResult pf \<and> sink_node t2 = FunctionResult pf
    \<and> caller_of t1 = Some c1 \<and> caller_of t2 = Some c2
    \<and> Resume c1 t1 (path c1 @ [(Statement 100, combine_collect None (sink_store c1) (sink_store t1))])
        \<in> valid_ltr mret_cfg UNIV
    \<and> Resume c2 t2 (path c2 @ [(Statement 100, combine_collect None (sink_store c2) (sink_store t2))])
        \<in> valid_ltr mret_cfg UNIV"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)(''Gx'' := 1)"
  define s1 :: store where "s1 = (\<lambda>_. 0)"
  define r0 where "r0 = Root [(cfg_entry mret_cfg, s0)]"
  define r1 where "r1 = Root [(cfg_entry mret_cfg, s1)]"

  \<comment> \<open>positive branch through Statement 0\<close>
  have R0: "r0 \<in> valid_ltr mret_cfg UNIV" unfolding r0_def by (rule valid_ltr.init) simp
  have m0: "sink_node r0 = FunctionEntry mn" by (simp add: r0_def mret_defs)
  have ec0: "(sink_node r0, CallEdge None [], FunctionEntry pf, Statement 100) \<in> calls mret_cfg"
    by (simp add: m0 mret_defs)
  define k0 where "k0 = Call r0 [(FunctionEntry pf, enter_state (sink_store r0))]"
  have K0: "k0 \<in> valid_ltr mret_cfg UNIV" unfolding k0_def by (rule valid_ltr.call[OF R0 ec0])
  have k0_sn: "sink_node k0 = FunctionEntry pf" by (simp add: k0_def)
  have k0_ss: "sink_store k0 = enter_state s0" by (simp add: k0_def r0_def)
  have eA0: "(sink_node k0, EA_Assume bpos, Statement 0) \<in> intra mret_cfg"
    by (simp add: k0_sn mret_defs)
  have stA0: "edge_step (EA_Assume bpos) (sink_store k0) = Some (sink_store k0)"
    by (simp add: k0_ss s0_def mret_defs enter_state_def is_global_def)
  define c0 where "c0 = extend k0 (Statement 0, sink_store k0)"
  have C0: "c0 \<in> valid_ltr mret_cfg UNIV" unfolding c0_def by (rule valid_ltr.intra[OF K0 eA0 stA0])
  have c0_sn: "sink_node c0 = Statement 0" by (simp add: c0_def)
  have eR0: "(sink_node c0, EA_Ret None pf, FunctionResult pf) \<in> intra mret_cfg"
    by (simp add: c0_sn mret_defs)
  have stR0: "edge_step (EA_Ret None pf) (sink_store c0) = Some (sink_store c0)" by simp
  define t1 where "t1 = extend c0 (FunctionResult pf, sink_store c0)"
  have T1: "t1 \<in> valid_ltr mret_cfg UNIV" unfolding t1_def by (rule valid_ltr.intra[OF C0 eR0 stR0])

  \<comment> \<open>negative branch through Statement 1\<close>
  have R1: "r1 \<in> valid_ltr mret_cfg UNIV" unfolding r1_def by (rule valid_ltr.init) simp
  have m1: "sink_node r1 = FunctionEntry mn" by (simp add: r1_def mret_defs)
  have ec1: "(sink_node r1, CallEdge None [], FunctionEntry pf, Statement 100) \<in> calls mret_cfg"
    by (simp add: m1 mret_defs)
  define k1 where "k1 = Call r1 [(FunctionEntry pf, enter_state (sink_store r1))]"
  have K1: "k1 \<in> valid_ltr mret_cfg UNIV" unfolding k1_def by (rule valid_ltr.call[OF R1 ec1])
  have k1_sn: "sink_node k1 = FunctionEntry pf" by (simp add: k1_def)
  have k1_ss: "sink_store k1 = enter_state s1" by (simp add: k1_def r1_def)
  have eA1: "(sink_node k1, EA_AssumeNot bpos, Statement 1) \<in> intra mret_cfg"
    by (simp add: k1_sn mret_defs)
  have stA1: "edge_step (EA_AssumeNot bpos) (sink_store k1) = Some (sink_store k1)"
    by (simp add: k1_ss s1_def mret_defs enter_state_def is_global_def)
  define c1 where "c1 = extend k1 (Statement 1, sink_store k1)"
  have C1: "c1 \<in> valid_ltr mret_cfg UNIV" unfolding c1_def by (rule valid_ltr.intra[OF K1 eA1 stA1])
  have c1_sn: "sink_node c1 = Statement 1" by (simp add: c1_def)
  have eR1: "(sink_node c1, EA_Ret None pf, FunctionResult pf) \<in> intra mret_cfg"
    by (simp add: c1_sn mret_defs)
  have stR1: "edge_step (EA_Ret None pf) (sink_store c1) = Some (sink_store c1)" by simp
  define t2 where "t2 = extend c1 (FunctionResult pf, sink_store c1)"
  have T2: "t2 \<in> valid_ltr mret_cfg UNIV" unfolding t2_def by (rule valid_ltr.intra[OF C1 eR1 stR1])

  have sn1: "sink_node t1 = FunctionResult pf" by (simp add: t1_def)
  have sn2: "sink_node t2 = FunctionResult pf" by (simp add: t2_def)
  have ct1: "caller_of t1 = Some r0" by (simp add: t1_def c0_def k0_def)
  have ct2: "caller_of t2 = Some r1" by (simp add: t2_def c1_def k1_def)

  \<comment> \<open>distinct: the two branches traverse different nodes\<close>
  have neq: "t1 \<noteq> t2"
    by (simp add: t1_def t2_def c0_def c1_def k0_def k1_def)

  have res1: "Resume r0 t1
      (path r0 @ [(Statement 100, combine_collect None (sink_store r0) (sink_store t1))])
        \<in> valid_ltr mret_cfg UNIV"
    by (rule valid_ltr.ret[OF T1 ct1 sn1 ec0])
  have res2: "Resume r1 t2
      (path r1 @ [(Statement 100, combine_collect None (sink_store r1) (sink_store t2))])
        \<in> valid_ltr mret_cfg UNIV"
    by (rule valid_ltr.ret[OF T2 ct2 sn2 ec1])

  from T1 T2 neq sn1 sn2 ct1 ct2 res1 res2 show ?thesis by blast
qed

subsection \<open>Witness: recursion nesting\<close>

text \<open>A self-recursive procedure \<open>pr\<close>: at its entry it returns (\<open>Gx <= 0\<close>) or calls itself
  (\<open>Gx > 0\<close>) at continuation \<open>Statement 200\<close>.  Two activations of \<open>pr\<close> are distinct and
  correctly nested via \<^const>\<open>caller_of\<close>.\<close>

definition pr :: pname where "pr = ''r''"

definition rec_cfg :: cfg where
  "rec_cfg =
     \<lparr> intra =
         { (FunctionEntry pr, EA_AssumeNot bpos, Statement 0),
           (Statement 0,      EA_Ret None pr,    FunctionResult pr),
           (FunctionEntry pr, EA_Assume bpos,    Statement 1) },
       calls =
         { (Statement 1, CallEdge None [], FunctionEntry pr, Statement 200) },
       cfg_entry = FunctionEntry pr \<rparr>"

lemmas rec_defs = rec_cfg_def pr_def bpos_def

lemma recursion_nesting:
  "\<exists>outer inner.
      outer \<in> valid_ltr rec_cfg UNIV \<and> inner \<in> valid_ltr rec_cfg UNIV
    \<and> outer \<noteq> inner
    \<and> caller_of inner = Some outer
    \<and> caller_of outer = None
    \<and> sink_node outer = Statement 1
    \<and> sink_node inner = FunctionEntry pr"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)(''Gx'' := 1)"
  define root where "root = Root [(cfg_entry rec_cfg, s0)]"
  have R: "root \<in> valid_ltr rec_cfg UNIV" unfolding root_def by (rule valid_ltr.init) simp
  have rt_sn: "sink_node root = FunctionEntry pr" by (simp add: root_def rec_defs)
  have eA: "(sink_node root, EA_Assume bpos, Statement 1) \<in> intra rec_cfg"
    by (simp add: rt_sn rec_defs)
  have stepA: "edge_step (EA_Assume bpos) (sink_store root) = Some (sink_store root)"
    by (simp add: root_def rec_defs s0_def enter_state_def is_global_def)
  define outer where "outer = extend root (Statement 1, sink_store root)"
  have OUTER: "outer \<in> valid_ltr rec_cfg UNIV"
    unfolding outer_def by (rule valid_ltr.intra[OF R eA stepA])
  have so: "sink_node outer = Statement 1" by (simp add: outer_def)
  have ecall: "(sink_node outer, CallEdge None [], FunctionEntry pr, Statement 200) \<in> calls rec_cfg"
    by (simp add: so rec_defs)
  define inner where "inner = Call outer [(FunctionEntry pr, enter_state (sink_store outer))]"
  have INNER: "inner \<in> valid_ltr rec_cfg UNIV"
    unfolding inner_def by (rule valid_ltr.call[OF OUTER ecall])
  have si: "sink_node inner = FunctionEntry pr" by (simp add: inner_def)
  have ci: "caller_of inner = Some outer" by (simp add: inner_def)
  have co: "caller_of outer = None" by (simp add: outer_def root_def)
  have neq: "outer \<noteq> inner" by (simp add: outer_def inner_def)
  from OUTER INNER neq ci co so si show ?thesis by blast
qed

end

