theory CFG_Local_Trace
  imports CFG_Collect_Trace
begin

section \<open>Activation-local concrete traces\<close>

text \<open>
  A concrete, analysis-independent reference semantics for compiled, stack-disciplined
  CFGs.  A value of type \<open>ltr\<close> represents one procedure activation together with its
  concrete ancestry: its local path of \<open>(program point, store)\<close> pairs, the caller it was
  created from, and --- once it has returned into a caller --- the completed callee it
  composed.  This is the sequential interprocedural analogue of Schwarz et al.'s local-trace
  architecture: local traces are the concrete objects, and contexts are computed afterwards
  by a projection (\<open>key\<close>), never stored inside the trace.

  The correspondence to Schwarz et al. (https://arxiv.org/pdf/2108.07613) is one of philosophy, not terminology.  Their local
  trace is an ego thread's partial-order view of a concurrent execution, with observers
  \<open>sink\<close>, \<open>loc\<close>, \<open>id\<close> and operations \<open>init\<close>, \<open>new\<close>, and edge extension.  The
  constructor and observer names used here (\<open>Root\<close>, \<open>Call\<close>, \<open>Resume\<close>, \<open>path\<close>,
  \<open>entry_store\<close>, \<open>caller_of\<close>, \<open>key\<close>) are this formalization's, not the paper's:
  \<open>Call\<close> is the sequential analogue of \<open>new\<close> but binds formal parameters via
  \<open>edge_step (EA_Enter ...)\<close> rather than allocating a fresh thread identity, and
  \<open>Resume\<close> and \<open>caller_of\<close> are new machinery for well-bracketed procedure returns with no
  paper counterpart.  \<open>path\<close> is an activation-local CFG control-flow path, not the paper's
  partial-order local trace.

  This theory introduces only the datatype, its observers, the extension/creation
  operations, the context projection, and the closure relation \<open>valid_ltr\<close>, together
  with their basic structural lemmas.  It changes no existing collecting definition and is not
  yet referenced by the pipeline.
\<close>

subsection \<open>The datatype\<close>

text \<open>
  \<^item> \<open>Root p\<close> --- the main activation, with local path \<open>p\<close>.
  \<^item> \<open>Call caller p\<close> --- a callee whose local path \<open>p\<close> starts at the parameter-bound entry
    store; \<open>caller\<close> is the exact suspended caller, frozen at the call node.
  \<^item> \<open>Resume caller callee p\<close> --- a caller continued past a completed call.  \<open>caller\<close> is the
    frozen caller at its call node (exactly the value that spawned \<open>callee\<close>, possibly itself a
    \<open>Call\<close> or a nested \<open>Resume\<close>); \<open>callee\<close> is the retained completed callee subtree (so
    \<open>key\<close> can read its context for a general return map); \<open>p\<close> is the caller's continued
    path.
\<close>

datatype ltr =
    Root "(pp * store) list"
  | Call ltr "(pp * store) list"
  | Resume ltr ltr "(pp * store) list"

subsection \<open>Observers\<close>

text \<open>\<open>path\<close> is the activation-local control-flow path (a list of \<open>(program point, store)\<close>
  pairs), not a partial-order trace.  \<open>sink_node\<close> and \<open>sink_store\<close> split into its two
  components what a paper-style \<open>sink\<close> observer returns as a pair --- the final program point
  (the paper's \<open>loc\<close>) and the final store.\<close>

primrec path :: "ltr \<Rightarrow> (pp * store) list" where
  "path (Root p)       = p"
| "path (Call _ p)     = p"
| "path (Resume _ _ p) = p"

definition entry_store :: "ltr \<Rightarrow> store" where
  "entry_store t = snd (hd (path t))"

text \<open>\<open>entry_store\<close> reads the head of the path, so it is a primitive observer only of a
  non-empty path.  Every semantic use is under \<open>valid_ltr\<close>, where \<open>valid_ltr_path_nonempty\<close>
  guarantees non-emptiness; on malformed \<open>ltr\<close> values outside \<open>valid_ltr\<close> its value is left
  unspecified.  Encoding non-empty paths in the datatype is deferred technical debt for a later
  stage; it is not needed for the closure relation.\<close>

definition sink_node :: "ltr \<Rightarrow> pp" where
  "sink_node t = fst (last (path t))"

definition sink_store :: "ltr \<Rightarrow> store" where
  "sink_store t = snd (last (path t))"

text \<open>
  \<open>caller_of\<close> recovers the creating caller of an activation.  It descends the frozen
  \<open>caller\<close> field of a \<^const>\<open>Resume\<close>, so it works uniformly for a returned callee of any
  constructor.  This is what makes nested and recursive returns compose: an activation that
  itself called and returned is a \<^const>\<open>Resume\<close>, and its caller is still recovered.
\<close>
fun caller_of :: "ltr \<Rightarrow> ltr option" where
  "caller_of (Root _)            = None"
| "caller_of (Call caller _)     = Some caller"
| "caller_of (Resume caller _ _) = caller_of caller"

subsection \<open>Extension and context projection\<close>

text \<open>\<open>extend\<close> appends one step to the innermost local path; it never touches an
  outer constructor's caller/callee fields.\<close>
primrec extend :: "ltr \<Rightarrow> (pp * store) \<Rightarrow> ltr" where
  "extend (Root p) x       = Root (p @ [x])"
| "extend (Call c p) x     = Call c (p @ [x])"
| "extend (Resume c d p) x = Resume c d (p @ [x])"

text \<open>The context is computed from the concrete trace after the fact.  A call routes the
  caller context on the bound callee-entry store; a return combines the caller and callee
  contexts.  Routing the context only at a call is this formalization's Goblint adaptation
  (Goblint's \<open>context\<close> is call-only) and is not part of the cited local-trace paper, which
  concerns thread-modular concurrency rather than procedure contexts.  A \<^const>\<open>Resume\<close>
  retains the full callee subtree precisely so \<open>combc\<close> can read \<open>key callee\<close>.\<close>
fun key :: "('c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ltr \<Rightarrow> 'c" where
  "key enterc combc seedc (Root _)                  = seedc"
| "key enterc combc seedc (Call parent p)           = enterc (key enterc combc seedc parent) (snd (hd p))"
| "key enterc combc seedc (Resume caller callee _)  = combc (key enterc combc seedc caller) (key enterc combc seedc callee)"

subsection \<open>The closure relation\<close>

text \<open>
  \<open>valid_ltr\<close> is the least set closed under four concrete operations: an initial main
  activation, an intra step, a call, and a return.  No rule permits an arbitrary callee root:
  a callee exists only because a concrete caller took a concrete \<^const>\<open>EA_Enter\<close> edge, and
  its entry store is the \<^const>\<open>edge_step\<close> result, retaining \<^const>\<open>bind_formals\<close>.  The extra
  combine premise in \<open>call\<close> matches the CFG stack machine, which requires both an enter edge
  and its matching combine triple.  The \<open>ret\<close> rule takes an arbitrary completed \<open>callee\<close> and
  recovers its caller by \<^const>\<open>caller_of\<close>, not by matching the callee's outer constructor, so
  it composes nested and recursive returns.
\<close>
inductive_set valid_ltr :: "cfg \<Rightarrow> store set \<Rightarrow> ltr set" for g S where
  init:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> valid_ltr g S"
| intra:
    "t \<in> valid_ltr g S
     \<Longrightarrow> (sink_node t, a, v) \<in> edges g
     \<Longrightarrow> \<not> is_enter_action a
     \<Longrightarrow> edge_step a (sink_store t) = Some s'
     \<Longrightarrow> extend t (v, s') \<in> valid_ltr g S"
| call:
    "caller \<in> valid_ltr g S
     \<Longrightarrow> (sink_node caller, EA_Enter xs es, fe) \<in> edges g
     \<Longrightarrow> (sink_node caller, ex, ret, dst) \<in> combines g
     \<Longrightarrow> edge_step (EA_Enter xs es) (sink_store caller) = Some se
     \<Longrightarrow> Call caller [(fe, se)] \<in> valid_ltr g S"
| ret:
    "callee \<in> valid_ltr g S
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> (sink_node caller, sink_node callee, v, dst) \<in> combines g
     \<Longrightarrow> r = combine_collect dst (sink_store caller) (sink_store callee)
     \<Longrightarrow> Resume caller callee (path caller @ [(v, r)]) \<in> valid_ltr g S"

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

text \<open>Every member of \<^const>\<open>valid_ltr\<close> has a non-empty path.\<close>
lemma valid_ltr_path_nonempty:
  "t \<in> valid_ltr g S \<Longrightarrow> path t \<noteq> []"
  by (induction t rule: valid_ltr.induct) auto

text \<open>\<^const>\<open>extend\<close> preserves the entry store when the path is non-empty (in particular for
  any \<^const>\<open>valid_ltr\<close> member).\<close>
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

text \<open>
  The activation parent is recovered through a \<^const>\<open>Resume\<close> even after the caller has itself
  returned and been extended.  This is the key non-stuck property for recursion: at a nested
  return \<open>ret f'\<close>, where \<open>f' = Resume (Call m cpf) g pf\<close> is a caller that already called and
  resumed, \<^const>\<open>caller_of\<close> still yields \<open>m\<close>.  Matching a bare \<open>Call\<close> callee would exclude this
  case.
\<close>
lemma nested_return_caller_of:
  fixes m :: ltr and cpf cpg pf :: "(pp * store) list" and x :: "pp * store"
  defines "f  \<equiv> Call m cpf"
  defines "g  \<equiv> Call f cpg"
  defines "f' \<equiv> Resume f g pf"
  shows "caller_of g = Some f"
    and "caller_of f' = Some m"
    and "caller_of (extend f' x) = Some m"
  by (simp_all add: f_def g_def f'_def)

subsection \<open>Design invariants\<close>

text \<open>The invariants of the convergence document are theorems of \<^const>\<open>valid_ltr\<close>, not merely
  constructor comments.  A valid \<^const>\<open>Call\<close> has a valid caller (the caller survives the
  callee's own intra steps); a valid \<^const>\<open>Resume\<close> retains its callee as a valid trace and
  cannot invent its frozen caller --- the caller is forced to be \<open>caller_of callee\<close>; every
  caller \<^const>\<open>caller_of\<close> recovers from a valid trace is valid; \<^const>\<open>caller_of\<close> is uniquely
  determined; \<^const>\<open>extend\<close> cannot change ancestry (\<open>caller_of_extend\<close> above); and every
  \<^const>\<open>Call\<close> activation has a non-empty path.\<close>

text \<open>A valid \<^const>\<open>Call\<close> activation has a valid caller, even after intra steps have extended
  its local path.\<close>
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

subsection \<open>A worked nested example\<close>

text \<open>
  A two-level program \<open>main \<rightarrow> f \<rightarrow> g\<close> where \<open>g\<close> returns into \<open>f\<close> and \<open>f\<close> returns into \<open>main\<close>.
  It exercises every rule of \<^const>\<open>valid_ltr\<close> (\<open>init\<close>, \<open>call\<close> twice, \<open>intra\<close>, \<open>ret\<close> twice) and
  reaches \<open>main\<close>'s return node without getting stuck: the second return recovers its caller
  \<open>main\<close> from the resumed \<open>f'\<close> through \<^const>\<open>caller_of\<close>.  It is stated over hypotheses on
  \<^const>\<open>edges\<close> and \<^const>\<open>combines\<close> rather than a fixed graph, isolating the datatype's return
  structure from CFG encoding details.
\<close>
lemma nested_valid_ltr_example:
  fixes g :: cfg and s0 :: store and nf ng gx fr mr :: pp
  assumes s0: "s0 \<in> S"
    and E1: "(cfg_entry g, EA_Enter [] [], nf) \<in> edges g"
    and E2: "(nf, EA_Enter [] [], ng) \<in> edges g"
    and E3: "(ng, EA_Nop, gx) \<in> edges g"
    and Cf: "(cfg_entry g, fr, mr, None) \<in> combines g"
    and Cg: "(nf, gx, fr, None) \<in> combines g"
  defines "e1 \<equiv> enter_state s0"
  defines "e2 \<equiv> enter_state e1"
  defines "main0 \<equiv> Root [(cfg_entry g, s0)]"
  defines "f0 \<equiv> Call main0 [(nf, e1)]"
  defines "g0 \<equiv> Call f0 [(ng, e2)]"
  defines "g1 \<equiv> extend g0 (gx, e2)"
  defines "r1 \<equiv> combine_collect None e1 e2"
  defines "f' \<equiv> Resume f0 g1 (path f0 @ [(fr, r1)])"
  defines "r2 \<equiv> combine_collect None s0 r1"
  shows "Resume main0 f' (path main0 @ [(mr, r2)]) \<in> valid_ltr g S"
proof -
  note sn = sink_node_def sink_store_def
  note es = bind_formals_def is_enter_action_def
  have m_sn: "sink_node main0 = cfg_entry g" "sink_store main0 = s0"
    by (simp_all add: sn main0_def)
  have main_mem: "main0 \<in> valid_ltr g S"
    unfolding main0_def by (rule valid_ltr.init[OF s0])
  have f_sn: "sink_node f0 = nf" "sink_store f0 = e1"
    by (simp_all add: sn f0_def)
  have f_mem: "f0 \<in> valid_ltr g S"
    unfolding f0_def
    by (rule valid_ltr.call[OF main_mem, where xs="[]" and es="[]" and ex=fr and ret=mr and dst=None])
       (simp_all add: m_sn E1 Cf es e1_def)
  have g_sn: "sink_node g0 = ng" "sink_store g0 = e2"
    by (simp_all add: sn g0_def)
  have g_mem: "g0 \<in> valid_ltr g S"
    unfolding g0_def
    by (rule valid_ltr.call[OF f_mem, where xs="[]" and es="[]" and ex=gx and ret=fr and dst=None])
       (simp_all add: f_sn E2 Cg es e2_def)
  have g1_sn: "sink_node g1 = gx" "sink_store g1 = e2"
    by (simp_all add: g1_def)
  have g1_mem: "g1 \<in> valid_ltr g S"
    unfolding g1_def
    by (rule valid_ltr.intra[OF g_mem, where a=EA_Nop])
       (simp_all add: g_sn E3 es)
  have g1_caller: "caller_of g1 = Some f0"
    by (simp add: g1_def g0_def)
  have f'_mem: "f' \<in> valid_ltr g S"
    unfolding f'_def
    by (rule valid_ltr.ret[OF g1_mem g1_caller, where v=fr and dst=None])
       (simp_all add: f_sn g1_sn Cg r1_def)
  have f'_sn: "sink_node f' = fr" "sink_store f' = r1"
    by (simp_all add: sn f'_def f0_def)
  have f'_caller: "caller_of f' = Some main0"
    by (simp add: f'_def f0_def)
  show ?thesis
    by (rule valid_ltr.ret[OF f'_mem f'_caller, where v=mr and dst=None])
       (simp_all add: m_sn f'_sn Cf r2_def)
qed

section \<open>Inclusion in the broad collecting semantics\<close>

text \<open>
  Every activation-local sink is a state of the broad graph collecting semantics
  \<^const>\<open>cfg_collect\<close>: the sink store of a valid trace at its sink node is collected there.
  This is the Stage-2 semantic obligation --- the local semantics does not admit stores the
  broad semantics rejects.  The proof reduces a valid trace to a \<^const>\<open>cfg_witness\<close> derivation,
  reusing the existing equivalence \<open>cfg_collect = {s. cfg_witness ...}\<close>.  The context
  projection \<open>key\<close> plays no role here: the inclusion establishes the sink state, and the
  context filter is a trivial outer restriction (\<open>ltr_ctx_collect_le_cfg_collect\<close>).
\<close>

subsection \<open>The caller chain\<close>

text \<open>
  The \<open>ret\<close> rule recovers its caller structurally by \<^const>\<open>caller_of\<close>, not as a recursive
  premise, so \<^const>\<open>valid_ltr\<close> rule induction supplies a witness for the callee but not for the
  recovered caller.  \<open>callers t\<close> is the finite \<^const>\<open>caller_of\<close> ancestry of \<open>t\<close> (itself and every
  recovered caller); proving the witness property along the whole chain closes that gap, because the
  caller a return composes lies in the callee's chain.  Termination descends \<open>size\<close>, since
  \<^const>\<open>caller_of\<close> strictly shrinks the trace.
\<close>

lemma caller_of_size: "caller_of t = Some c \<Longrightarrow> size c < size t"
  by (induction t arbitrary: c) auto

function callers :: "ltr \<Rightarrow> ltr set" where
  "callers t = insert t (case caller_of t of None \<Rightarrow> {} | Some c \<Rightarrow> callers c)"
  by pat_completeness auto
termination callers
  by (relation "measure size") (auto simp: caller_of_size)

text \<open>\<open>callers.simps\<close> is recursive; never leave it in a simp set (it rewrites \<open>callers c\<close> on
  its own right-hand side and loops).  These structural facts are what the induction consumes.\<close>

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

subsection \<open>Sink states are broad witnesses\<close>

text \<open>The witness property holds at every activation of the caller chain.  Rule induction over
  \<^const>\<open>valid_ltr\<close>: \<open>init\<close> is a \<^const>\<open>cfg_witness\<close> entry; \<open>intra\<close> and \<open>call\<close> append one edge
  (\<^const>\<open>edge_step\<close> agrees with \<^const>\<open>edge_collect\<close> on a singleton); \<open>ret\<close> discharges the broad
  \<^const>\<open>cfg_witness\<close> combine directly from the frozen caller and retained callee --- no re-rooting,
  no reconstruction --- because both witnesses come from the callee's chain.\<close>

lemma callers_witness:
  "t \<in> valid_ltr g S \<Longrightarrow> \<forall>u \<in> callers t. cfg_witness g S (sink_node u) (sink_store u)"
proof (induction rule: valid_ltr.induct)
  case (init s)
  then show ?case
    by (simp add: callers_Root sink_node_def sink_store_def cfg_witness.entry)
next
  case (intra t a v s')
  show ?case
  proof
    fix u assume "u \<in> callers (extend t (v, s'))"
    then have "u = extend t (v, s') \<or> u \<in> callers t"
      using callers_extend_subset by blast
    then show "cfg_witness g S (sink_node u) (sink_store u)"
    proof
      assume u: "u = extend t (v, s')"
      have wt: "cfg_witness g S (sink_node t) (sink_store t)"
        using intra.IH callers_refl by blast
      have "s' \<in> edge_collect a {sink_store t}"
        using intra.hyps(4) by (simp add: edge_collect_single)
      then have "cfg_witness g S v s'"
        using cfg_witness.edge[OF intra.hyps(2) wt] by blast
      then show ?thesis using u by simp
    next
      assume "u \<in> callers t"
      then show ?thesis using intra.IH by blast
    qed
  qed
next
  case (call caller xs es fe ex ret dst se)
  show ?case
  proof
    fix u assume "u \<in> callers (Call caller [(fe, se)])"
    then have "u = Call caller [(fe, se)] \<or> u \<in> callers caller"
      by (simp add: callers_Call)
    then show "cfg_witness g S (sink_node u) (sink_store u)"
    proof
      assume u: "u = Call caller [(fe, se)]"
      have wc: "cfg_witness g S (sink_node caller) (sink_store caller)"
        using call.IH callers_refl by blast
      have "se \<in> edge_collect (EA_Enter xs es) {sink_store caller}"
        using call.hyps(4) by (simp add: edge_collect_single)
      then have "cfg_witness g S fe se"
        using cfg_witness.edge[OF call.hyps(2) wc] by blast
      then show ?thesis using u by (simp add: sink_node_def sink_store_def)
    next
      assume "u \<in> callers caller"
      then show ?thesis using call.IH by blast
    qed
  qed
next
  case (ret callee caller v dst r)
  show ?case
  proof
    fix u assume "u \<in> callers (Resume caller callee (path caller @ [(v, r)]))"
    then have "u = Resume caller callee (path caller @ [(v, r)]) \<or> u \<in> callers callee"
      using callers_Resume_subset[OF ret.hyps(2)] by blast
    then show "cfg_witness g S (sink_node u) (sink_store u)"
    proof
      assume u: "u = Resume caller callee (path caller @ [(v, r)])"
      have wcaller: "cfg_witness g S (sink_node caller) (sink_store caller)"
        using ret.IH callers_caller_subset[OF ret.hyps(2)] callers_refl by blast
      have wcallee: "cfg_witness g S (sink_node callee) (sink_store callee)"
        using ret.IH callers_refl by blast
      have "cfg_witness g S v r"
        using cfg_witness.combine[OF ret.hyps(3) wcaller wcallee ret.hyps(4)] .
      then show ?thesis using u by (simp add: sink_node_def sink_store_def)
    next
      assume "u \<in> callers callee"
      then show ?thesis using ret.IH by blast
    qed
  qed
qed

lemma valid_ltr_sink_witness:
  "t \<in> valid_ltr g S \<Longrightarrow> cfg_witness g S (sink_node t) (sink_store t)"
  using callers_witness callers_refl by blast

theorem valid_ltr_sink_in_cfg_collect:
  "t \<in> valid_ltr g S \<Longrightarrow> sink_store t \<in> cfg_collect g S (sink_node t)"
  using valid_ltr_sink_witness cfg_witness_in_cfg_collect by blast

subsection \<open>Internal context projection\<close>

text \<open>The internal activation-sensitive projection: the sink stores of valid traces reaching \<open>v\<close>
  whose context key is \<open>c\<close>.  It is Stage-2 scaffolding under a distinct name; the public
  \<open>cfg_collect_ctx_act\<close> is untouched until Stage 4.  Its inclusion in \<^const>\<open>cfg_collect\<close> is
  immediate from the key-free sink inclusion: the \<open>key\<close> filter only removes traces.\<close>

definition ltr_ctx_collect ::
  "('c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> store set" where
  "ltr_ctx_collect enterc combc seedc g S v c =
     {sink_store t | t. t \<in> valid_ltr g S \<and> sink_node t = v \<and> key enterc combc seedc t = c}"

theorem ltr_ctx_collect_le_cfg_collect:
  "ltr_ctx_collect enterc combc seedc g S v c \<subseteq> cfg_collect g S v"
  unfolding ltr_ctx_collect_def using valid_ltr_sink_in_cfg_collect by fastforce

end
