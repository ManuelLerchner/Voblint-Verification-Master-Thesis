theory LTR_Activation_Context
  imports LTR_Def
begin

section \<open>Activation context selection and context-indexed collecting\<close>

text \<open>
  The activation context is computed from the concrete trace after the fact and is
  activation-stable: fixed when the activation is created and unchanged by the calls it
  later makes and returns from.  \<^const>\<open>Root\<close> carries the seed; a \<^const>\<open>Call\<close> routes the
  caller context on the call site and the callee-entry store --- \<open>sink_node parent\<close> is
  exactly the call site, since \<^const>\<open>extend\<close> only ever appends to the callee path and
  leaves \<open>parent\<close> frozen there; a \<^const>\<open>Resume\<close> keeps the resumed caller's own context, so
  a completed call does not repartition the caller.  Exposing the call site to \<open>enterc\<close> is
  what makes a call-site-keyed context (a k-call-string) expressible as an instance rather
  than only as a generator-side hook.\<close>
fun key :: "(cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ltr \<Rightarrow> 'c" where
  "key enterc initial_ctx (Root _)                  = initial_ctx"
| "key enterc initial_ctx (Call parent p)           =
     enterc (sink_node parent) (key enterc initial_ctx parent) (snd (hd p))"
| "key enterc initial_ctx (Resume current callee _) = key enterc initial_ctx current"

text \<open>\<open>key\<close> fixes one context per trace by decoding the entered store exactly: a
  \<^const>\<open>Call\<close> activation's context is derived from its caller's OWN selected context,
  not re-derived from the concrete store independently at each node. This is what keeps a
  chosen context stable across a CALL/RETURN pair: the callee's context in \<^const>\<open>Resume\<close>
  resumes through \<open>current\<close>, so a completed call cannot repartition the caller.

  \<open>key\<close> is the deterministic special case: a total function from the entered store to a
  context, never a relation admitting several contexts for one concrete activation. The
  unit and call-site/k-call-string routing instances are exactly this shape, and the
  executable routed solver's own \<open>route\<close> is typed to return a single context, not a set.
  The entry-state instance is not: a call may answer several overlapping alternatives, each
  covering the same concrete activation and routing it to its own context, so its concrete
  semantics is stated directly over \<open>trace_context\<close>/\<open>call_context_rel\<close> rather than over
  \<open>key\<close>. \<open>key\<close> is therefore not the primary semantics; it is the deterministic
  compatibility witness for the functional case, connected to \<open>trace_context\<close> via
  \<open>call_context_rel_of_fun\<close> and \<open>trace_context_of_fun_iff\<close>.\<close>



lemma key_extend_nonempty:
  "path t \<noteq> [] \<Longrightarrow> key enterc initial_ctx (extend t x) = key enterc initial_ctx t"
  by (cases t) (auto simp: hd_append)


subsection \<open>Admissible callee contexts, relationally\<close>

text \<open>
  An analysis's entry operation answers a \<^emph>\<open>list\<close> of alternatives and its context
  selector is applied to each, so one concrete call may be admitted in several contexts.
  \<open>call_context_rel\<close> is the semantic shape of that whole-call protocol: given the call
  site, the caller's own context, the call's information, the caller store and the entered
  store, it says which callee contexts may describe this transition.  Both stores are
  arguments so an instance can tie the chosen context to one alternative whose continuation
  half covers the caller and whose entry half covers the entered store, never mixing two.

  A functional policy --- the unit context, a k-call-string --- is the graph of a function,
  \<open>call_context_rel_of_fun\<close>.  The abstract selector an analysis actually runs stays a
  function of the abstract entry value; only the trace semantics is relational.
\<close>

type_synonym 'c call_context_rel =
  "cfg_node \<Rightarrow> 'c \<Rightarrow> call_info \<Rightarrow> store \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool"

definition call_context_rel_of_fun ::
  "(cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> 'c call_context_rel"
where
  "call_context_rel_of_fun f u ctx ci caller entered ctx' \<longleftrightarrow> ctx' = f u ctx entered"

lemma call_context_rel_of_fun_iff [simp]:
  "call_context_rel_of_fun f u ctx ci caller entered ctx' \<longleftrightarrow> ctx' = f u ctx entered"
  by (simp add: call_context_rel_of_fun_def)

text \<open>
  \<open>admits_call_context gs g R u ctx p s es ctx'\<close>: from node \<open>u\<close> in context \<open>ctx\<close> with store
  \<open>s\<close>, some \<open>calls\<close> edge of \<open>g\<close> enters \<open>p\<close> with exactly the store \<open>es\<close>, and \<open>R\<close> admits
  \<open>ctx'\<close> for that edge.  It is \<^const>\<open>call_enter_store\<close> with the callee and the admitted
  context made explicit.  Naming the edge by its effect rather than assuming it unique keeps
  the semantics honest on a graph with two call edges leaving one node, exactly as
  \<open>valid_ltr.ret\<close> does.
\<close>

definition admits_call_context ::
  "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> 'c call_context_rel
     \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> pname \<Rightarrow> store \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool"
where
  "admits_call_context gs g R u ctx p s es ctx' \<longleftrightarrow>
     (\<exists>dst pars args cont.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<and> es = call_enter gs (CallEdge dst pars args) s
        \<and> R u ctx (call_info_of (CallEdge dst pars args) p) s es ctx')"

lemma admits_call_contextI:
  assumes "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "R u ctx (call_info_of (CallEdge dst pars args) p) s
           (call_enter gs (CallEdge dst pars args) s) ctx'"
  shows "admits_call_context gs g R u ctx p s (call_enter gs (CallEdge dst pars args) s) ctx'"
  using assms unfolding admits_call_context_def by blast

lemma admits_call_contextE:
  assumes "admits_call_context gs g R u ctx p s es ctx'"
  obtains dst pars args cont
    where "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
      and "es = call_enter gs (CallEdge dst pars args) s"
      and "R u ctx (call_info_of (CallEdge dst pars args) p) s es ctx'"
  using assms unfolding admits_call_context_def by blast

lemma admits_call_context_call_enter_storeD:
  "admits_call_context gs g R u ctx p s es ctx' \<Longrightarrow> call_enter_store gs g u s es"
  unfolding admits_call_context_def call_enter_store_def by blast

lemma admits_call_context_of_fun:
  "admits_call_context gs g (call_context_rel_of_fun f) u ctx p s es ctx'
     \<longleftrightarrow> (\<exists>dst pars args cont.
           (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
           \<and> es = call_enter gs (CallEdge dst pars args) s)
       \<and> ctx' = f u ctx es"
  unfolding admits_call_context_def by auto

text \<open>
  \<open>trace_context gs R startcontext g t ctx\<close>: the trace \<open>t\<close> may carry context \<open>ctx\<close>.  A root
  carries \<open>startcontext\<close>; a call carries any context admitted for its creating transition,
  computed from the caller's own carried context; a resumed caller keeps what it carried.
\<close>

inductive trace_context ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'c call_context_rel \<Rightarrow> 'c \<Rightarrow> cfg \<Rightarrow> ltr \<Rightarrow> 'c \<Rightarrow> bool"
  for gs :: "vname \<Rightarrow> bool" and R :: "'c call_context_rel" and startcontext :: 'c and g :: cfg
where
  Root: "trace_context gs R startcontext g (Root xs) startcontext"
| Call:
    "trace_context gs R startcontext g parent ctx
     \<Longrightarrow> admits_call_context gs g R (sink_node parent) ctx p (sink_store parent) es ctx'
     \<Longrightarrow> trace_context gs R startcontext g (Call parent ((FunctionEntry p, es) # xs)) ctx'"
| Resume:
    "trace_context gs R startcontext g current ctx
     \<Longrightarrow> trace_context gs R startcontext g (Resume current callee xs) ctx"

declare trace_context.intros [intro]

inductive_cases trace_context_RootE [elim!]:
  "trace_context gs R startcontext g (Root xs) ctx"

inductive_cases trace_context_CallE [elim]:
  "trace_context gs R startcontext g (Call parent xs) ctx"

inductive_cases trace_context_ResumeE [elim]:
  "trace_context gs R startcontext g (Resume current callee xs) ctx"

lemma trace_context_Root_iff [simp]:
  "trace_context gs R startcontext g (Root xs) ctx \<longleftrightarrow> ctx = startcontext"
  by blast

lemma trace_context_Resume_iff [simp]:
  "trace_context gs R startcontext g (Resume current callee xs) ctx
     \<longleftrightarrow> trace_context gs R startcontext g current ctx"
  by blast

lemma trace_context_Call_Nil [simp]:
  "\<not> trace_context gs R startcontext g (Call parent []) ctx"
  by blast

text \<open>The carried context of a called activation depends on its caller and its entry
  record only: the rest of the local path is irrelevant, which is what makes an intra step
  context-preserving.\<close>
lemma trace_context_Call_iff:
  "trace_context gs R startcontext g (Call parent ((n, es) # xs)) ctx'
     \<longleftrightarrow> (\<exists>ctx p. n = FunctionEntry p
           \<and> trace_context gs R startcontext g parent ctx
           \<and> admits_call_context gs g R (sink_node parent) ctx p (sink_store parent) es ctx')"
  by blast

lemma trace_context_extend:
  assumes "path t \<noteq> []"
  shows "trace_context gs R startcontext g (extend t x) ctx
           \<longleftrightarrow> trace_context gs R startcontext g t ctx"
proof (cases t)
  case (Call parent xs)
  then obtain n es ys where "xs = (n, es) # ys" using assms by (cases xs) auto
  then show ?thesis using Call by (simp add: trace_context_Call_iff)
qed simp_all

subsection \<open>Context entry invariant\<close>

text \<open>A called activation carries exactly the contexts admitted for the transition from its
  immediate caller, each computed from a context the caller itself carries.  Stated as an
  equivalence: forwards, a RETURN argument recovers the caller's slot from the callee's;
  backwards, it re-enters the callee at a context derived from whichever slot the resumed
  caller is being placed in.\<close>
lemma trace_context_caller_entry:
  assumes "callee \<in> valid_ltr gs g S"
  shows "\<forall>u \<in> callers callee. \<forall>c. caller_of u = Some c
       \<longrightarrow> (\<exists>p es. hd (path u) = (FunctionEntry p, es)
             \<and> (\<forall>ctx'. trace_context gs R startcontext g u ctx'
                  \<longleftrightarrow> (\<exists>ctx. trace_context gs R startcontext g c ctx
                        \<and> admits_call_context gs g R (sink_node c) ctx p (sink_store c) es ctx')))"
proof -
  define P where "P u \<longleftrightarrow> (\<forall>c. caller_of u = Some c
       \<longrightarrow> (\<exists>p es. hd (path u) = (FunctionEntry p, es)
             \<and> (\<forall>ctx'. trace_context gs R startcontext g u ctx'
                  \<longleftrightarrow> (\<exists>ctx. trace_context gs R startcontext g c ctx
                        \<and> admits_call_context gs g R (sink_node c) ctx p (sink_store c) es ctx'))))"
    for u
  have "\<forall>u \<in> callers callee. P u"
  proof (rule caller_chain_closure[OF _ _ _ _ assms])
    fix s show "P (Root [(cfg_entry g, s)])" by (simp add: P_def)
  next
    fix t a v s' assume t: "t \<in> valid_ltr gs g S" and IH: "\<forall>u \<in> callers t. P u"
    have "path t \<noteq> []" using valid_ltr_path_nonempty[OF t] .
    with IH[THEN bspec, OF callers_refl] show "P (extend t (v, s'))"
      by (simp add: P_def trace_context_extend hd_append)
  next
    fix caller dst pars args p cont
    show "P (Call caller
        [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
      unfolding P_def by (auto simp: trace_context_Call_iff)
  next
    fix callee caller p dst pars args cont
    assume cv: "callee \<in> valid_ltr gs g S" and IH: "\<forall>u \<in> callers callee. P u"
      and cof: "caller_of callee = Some caller"
    have "path caller \<noteq> []"
      using valid_ltr_path_nonempty[OF valid_ltr_caller_valid[OF cv cof]] .
    moreover have "P caller" using IH ancestors_caller[OF cof] by blast
    ultimately show "P (Resume caller callee
        (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
      by (simp add: P_def hd_append)
  qed
  then show ?thesis unfolding P_def .
qed

lemma trace_context_caller_entryE:
  assumes "callee \<in> valid_ltr gs g S" and "caller_of callee = Some caller"
    and "trace_context gs R startcontext g callee ctx'"
  obtains ctx p where "hd (path callee) = (FunctionEntry p, entry_store callee)"
    and "trace_context gs R startcontext g caller ctx"
    and "admits_call_context gs g R (sink_node caller) ctx p (sink_store caller)
           (entry_store callee) ctx'"
proof -
  from trace_context_caller_entry[OF assms(1), THEN bspec, OF callers_refl,
      rule_format, OF assms(2)]
  obtain p es where hd: "hd (path callee) = (FunctionEntry p, es)"
    and iff: "\<forall>ctx'. trace_context gs R startcontext g callee ctx'
         \<longleftrightarrow> (\<exists>ctx. trace_context gs R startcontext g caller ctx
               \<and> admits_call_context gs g R (sink_node caller) ctx p (sink_store caller) es ctx')"
    by force
  have "es = entry_store callee" using hd by (simp add: entry_store_def)
  with hd iff assms(3) show thesis using that by blast
qed

lemma trace_context_caller_entryI:
  assumes "callee \<in> valid_ltr gs g S" and "caller_of callee = Some caller"
    and "hd (path callee) = (FunctionEntry p, entry_store callee)"
    and "trace_context gs R startcontext g caller ctx"
    and "admits_call_context gs g R (sink_node caller) ctx p (sink_store caller)
           (entry_store callee) ctx'"
  shows "trace_context gs R startcontext g callee ctx'"
proof -
  from trace_context_caller_entry[OF assms(1), THEN bspec, OF callers_refl,
      rule_format, OF assms(2)]
  obtain p' es where hd: "hd (path callee) = (FunctionEntry p', es)"
    and iff: "\<forall>ctx'. trace_context gs R startcontext g callee ctx'
         \<longleftrightarrow> (\<exists>ctx. trace_context gs R startcontext g caller ctx
               \<and> admits_call_context gs g R (sink_node caller) ctx p' (sink_store caller) es ctx')"
    by force
  have "p' = p" and "es = entry_store callee" using hd assms(3) by simp_all
  with iff assms(4,5) show ?thesis by blast
qed

text \<open>A functional policy carries exactly \<^const>\<open>key\<close>'s context on every valid trace.  The
  restriction to valid traces is what supplies the call edge the relational clause names.\<close>
lemma trace_context_of_fun_iff:
  assumes "t \<in> valid_ltr gs g S"
  shows "trace_context gs (call_context_rel_of_fun f) startcontext g t ctx
           \<longleftrightarrow> key f startcontext t = ctx"
proof -
  define P where "P u \<longleftrightarrow> (\<forall>ctx. trace_context gs (call_context_rel_of_fun f) startcontext g u ctx
                                \<longleftrightarrow> key f startcontext u = ctx)" for u
  have "\<forall>u \<in> callers t. P u"
  proof (rule caller_chain_closure[OF _ _ _ _ assms])
    fix s show "P (Root [(cfg_entry g, s)])" by (simp add: P_def eq_commute)
  next
    fix t a v s' assume t: "t \<in> valid_ltr gs g S" and IH: "\<forall>u \<in> callers t. P u"
    have "path t \<noteq> []" using valid_ltr_path_nonempty[OF t] .
    with IH[THEN bspec, OF callers_refl] show "P (extend t (v, s'))"
      by (simp add: P_def key_extend_nonempty trace_context_extend)
  next
    fix caller dst pars args p cont
    assume IH: "\<forall>u \<in> callers caller. P u"
      and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    have Pc: "P caller" using IH callers_refl by blast
    show "P (Call caller
        [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
      unfolding P_def trace_context_Call_iff admits_call_context_of_fun
      using Pc[unfolded P_def] e by auto
  next
    fix callee caller p dst pars args cont
    assume IH: "\<forall>u \<in> callers callee. P u" and cof: "caller_of callee = Some caller"
    have "P caller" using IH ancestors_caller[OF cof] by blast
    then show "P (Resume caller callee
        (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
      by (simp add: P_def)
  qed
  then show ?thesis unfolding P_def using callers_refl by blast
qed

subsection \<open>Context entry invariant\<close>

text \<open>Every ancestor of a valid trace is itself valid: \<open>caller_chain_closure\<close>'s own
  four cases are exactly \<^const>\<open>valid_ltr\<close>'s four introduction rules, so the closure fact
  and validity coincide.\<close>

lemma callers_valid:
  assumes "callee \<in> valid_ltr gs g S" and "u \<in> callers callee"
  shows "u \<in> valid_ltr gs g S"
proof -
  have "\<forall>u \<in> callers callee. u \<in> valid_ltr gs g S"
  proof (rule caller_chain_closure[OF _ _ _ _ assms(1)], goal_cases Root Intra Call Ret)
    case (Root s) then show ?case by (rule valid_ltr.init)
  next
    case (Intra t a v s') then show ?case by (blast intro: valid_ltr.intra)
  next
    case (Call caller dst pars args p cont) then show ?case by (blast intro: valid_ltr.call)
  next
    case (Ret callee caller p dst pars args cont) then show ?case by (blast intro: valid_ltr.ret)
  qed
  then show ?thesis using assms(2) by blast
qed

text \<open>The context of an activation is exactly what \<open>enterc\<close> computes from its immediate
  caller's own context and the callee-entry store.  This is what lets a RETURN argument
  construct the callee's context directly from the caller's chosen one, rather than
  rediscovering it after the fact. A special case of \<open>trace_context_caller_entry\<close> at
  the functional relation \<^const>\<open>call_context_rel_of_fun\<close>, where \<open>trace_context_of_fun_iff\<close>
  pins both sides' witness context to \<^const>\<open>key\<close> and \<open>admits_call_context_of_fun\<close> reads off
  the \<open>enterc\<close>-equation and the call-edge witness in one step.\<close>

lemma key_entry_invariant:
  assumes "callee \<in> valid_ltr gs g S"
  shows "\<forall>u \<in> callers callee. \<forall>c. caller_of u = Some c \<longrightarrow>
       key enterc initial_ctx u = enterc (sink_node c) (key enterc initial_ctx c) (entry_store u)
       \<and> call_enter_store gs g (sink_node c) (sink_store c) (entry_store u)"
proof (intro ballI allI impI)
  fix u c assume mem: "u \<in> callers callee" and cof: "caller_of u = Some c"
  have uv: "u \<in> valid_ltr gs g S" using callers_valid[OF assms mem] .
  have cv: "c \<in> valid_ltr gs g S" using valid_ltr_caller_valid[OF uv cof] .
  have tc_u: "trace_context gs (call_context_rel_of_fun enterc) initial_ctx g u
                (key enterc initial_ctx u)"
    by (simp only: trace_context_of_fun_iff[OF uv])
  obtain p ctx where hd: "hd (path u) = (FunctionEntry p, entry_store u)"
    and tc_c: "trace_context gs (call_context_rel_of_fun enterc) initial_ctx g c ctx"
    and adm: "admits_call_context gs g (call_context_rel_of_fun enterc) (sink_node c) ctx p
                (sink_store c) (entry_store u) (key enterc initial_ctx u)"
    by (rule trace_context_caller_entryE[OF uv cof tc_u])
  have key_c: "key enterc initial_ctx c = ctx"
    using tc_c by (simp only: trace_context_of_fun_iff[OF cv])
  have adm': "key enterc initial_ctx u = enterc (sink_node c) ctx (entry_store u)"
    using adm unfolding admits_call_context_of_fun by simp
  have key_eq: "key enterc initial_ctx u
                  = enterc (sink_node c) (key enterc initial_ctx c) (entry_store u)"
    unfolding key_c using adm' .
  show "key enterc initial_ctx u
          = enterc (sink_node c) (key enterc initial_ctx c) (entry_store u)
        \<and> call_enter_store gs g (sink_node c) (sink_store c) (entry_store u)"
    using key_eq admits_call_context_call_enter_storeD[OF adm] by (intro conjI)
qed

lemma key_entry_invariant_eq:
  assumes "callee \<in> valid_ltr gs g S" and "caller_of callee = Some caller"
  shows "key enterc initial_ctx callee
         = enterc (sink_node caller) (key enterc initial_ctx caller) (entry_store callee)"
  using key_entry_invariant[OF assms(1), THEN bspec, OF callers_refl, rule_format, OF assms(2),
      THEN conjunct1] .

lemma key_entry_invariant_call_enterD [dest]:
  assumes "callee \<in> valid_ltr gs g S" and "caller_of callee = Some caller"
  shows "call_enter_store gs g (sink_node caller) (sink_store caller) (entry_store callee)"
  using key_entry_invariant[OF assms(1), THEN bspec, OF callers_refl, rule_format, OF assms(2)]
  by (rule conjunct2)

subsection \<open>Conditional totality\<close>

text \<open>
  A relation may admit no context at all, and then every context-indexed collection is
  empty --- true, and useless.  \<open>call_context_total_on cover R gs g\<close> rules that out exactly
  where it matters: at every call edge, every store the claimed \<open>cover\<close> admits at the call
  site has some admissible callee context.  A dead call site owes nothing.  The graph of a
  function is total outright.
\<close>

definition call_context_total_on ::
  "(cfg_node \<Rightarrow> 'c \<Rightarrow> store set) \<Rightarrow> 'c call_context_rel \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> bool"
where
  "call_context_total_on cover R gs g \<longleftrightarrow>
     (\<forall>u dst pars args p cont ctx s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<longrightarrow> s \<in> cover u ctx
        \<longrightarrow> (\<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) p) s
                      (call_enter gs (CallEdge dst pars args) s) ctx'))"

lemma call_context_total_onE:
  assumes "call_context_total_on cover R gs g"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "s \<in> cover u ctx"
  obtains ctx' where "admits_call_context gs g R u ctx p s
                        (call_enter gs (CallEdge dst pars args) s) ctx'"
  using assms unfolding call_context_total_on_def
  by (blast intro: admits_call_contextI)

lemma call_context_total_on_of_fun [simp]:
  "call_context_total_on cover (call_context_rel_of_fun f) gs g"
  unfolding call_context_total_on_def call_context_rel_of_fun_def by blast

subsection \<open>The activation-indexed context collecting\<close>

text \<open>The activation-sensitive collecting is the sink stores of valid traces reaching \<open>v\<close>
  that may carry the queried context \<open>c\<close>.  One trace may carry several contexts, so the
  buckets of one node cover its stores without partitioning them.\<close>

definition activation_collect ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'c call_context_rel \<Rightarrow> 'c
     \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store set" where
  "activation_collect gs R startcontext g S v c =
     {sink_store t | t. t \<in> valid_ltr gs g S \<and> sink_node t = v
                        \<and> trace_context gs R startcontext g t c}"

lemma activation_collect_I [intro]:
  "t \<in> valid_ltr gs g S \<Longrightarrow> sink_node t = v \<Longrightarrow> trace_context gs R startcontext g t c
   \<Longrightarrow> sink_store t \<in> activation_collect gs R startcontext g S v c"
  unfolding activation_collect_def by blast

text \<open>Every collected state has a valid trace witness carrying the queried \<open>c\<close>.\<close>
lemma activation_collect_E [elim]:
  assumes "s \<in> activation_collect gs R startcontext g S v c"
  obtains t where "t \<in> valid_ltr gs g S" "sink_node t = v"
    "trace_context gs R startcontext g t c" "sink_store t = s"
  using assms unfolding activation_collect_def by blast

text \<open>Under a functional policy the buckets are \<^const>\<open>key\<close>'s fibres.\<close>
lemma activation_collect_of_fun:
  "activation_collect gs (call_context_rel_of_fun f) startcontext g S v c =
     {sink_store t | t. t \<in> valid_ltr gs g S \<and> sink_node t = v \<and> key f startcontext t = c}"
  unfolding activation_collect_def
  by (auto simp: trace_context_of_fun_iff)


end

