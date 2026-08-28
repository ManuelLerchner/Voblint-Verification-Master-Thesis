theory Activation_Context
  imports CFG_Local_Trace
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
  "key enterc startcontext (Root _)                  = startcontext"
| "key enterc startcontext (Call parent p)           =
     enterc (sink_node parent) (key enterc startcontext parent) (snd (hd p))"
| "key enterc startcontext (Resume current callee _) = key enterc startcontext current"

text \<open>\<open>key\<close> fixes one context per trace by decoding the entered store exactly: a
  \<^const>\<open>Call\<close> activation's context is derived from its caller's OWN selected context,
  not re-derived from the concrete store independently at each node. This is what keeps a
  chosen context stable across a CALL/RETURN pair: the callee's context in \<^const>\<open>Resume\<close>
  resumes through \<open>current\<close>, so a completed call cannot repartition the caller.

  Every live routing instance (unit, call-site/k-call-string, entry-state) is exactly this
  shape --- a total function from the entered store to a context, never a relation admitting
  several contexts for one concrete activation --- and the executable routed solver's own
  \<open>route\<close> is typed to return a single context, not a set. \<open>key\<close> is therefore stated as
  the deterministic primitive directly, rather than as the exact-decode specialization of a
  more general admissibility relation.\<close>

lemma key_extend_nonempty:
  "path t \<noteq> [] \<Longrightarrow> key enterc startcontext (extend t x) = key enterc startcontext t"
  by (cases t) (auto simp: hd_append)

subsection \<open>Context entry invariant\<close>

text \<open>The context of an activation is exactly what \<open>enterc\<close> computes from its immediate
  caller's own context and the callee-entry store.  This is what lets a COMB argument
  construct the callee's context directly from the caller's chosen one, rather than
  rediscovering it after the fact.\<close>
lemma key_entry_invariant:
  assumes "callee \<in> valid_ltr gs g S"
  shows "\<forall>u \<in> callers callee. \<forall>c. caller_of u = Some c \<longrightarrow>
       key enterc startcontext u = enterc (sink_node c) (key enterc startcontext c) (entry_store u)
       \<and> call_enter_store gs g (sink_node c) (sink_store c) (entry_store u)"
proof -
  define P where "P u \<longleftrightarrow> (\<forall>c. caller_of u = Some c \<longrightarrow>
       key enterc startcontext u = enterc (sink_node c) (key enterc startcontext c) (entry_store u)
       \<and> call_enter_store gs g (sink_node c) (sink_store c) (entry_store u))" for u
  have "\<forall>u \<in> callers callee. P u"
  proof (rule caller_chain_closure[OF _ _ _ _ assms])
    fix s show "P (Root [(cfg_entry g, s)])" by (simp add: P_def)
  next
    fix t a v s' assume t: "t \<in> valid_ltr gs g S" and IH: "\<forall>u \<in> callers t. P u"
    have "path t \<noteq> []" using valid_ltr_path_nonempty[OF t] .
    with IH[THEN bspec, OF callers_refl] show "P (extend t (v, s'))"
      by (simp add: P_def key_extend_nonempty)
  next
    fix caller dst pars args p cont
    assume "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    then show "P (Call caller
        [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
      unfolding P_def by (auto simp: entry_store_def call_enter_store_def) blast
  next
    fix callee caller p dst pars args cont
    assume cv: "callee \<in> valid_ltr gs g S" and IH: "\<forall>u \<in> callers callee. P u"
      and cof: "caller_of callee = Some caller"
    have "path caller \<noteq> []"
      using valid_ltr_path_nonempty[OF valid_ltr_caller_valid[OF cv cof]] .
    moreover have "P caller" using IH ancestors_caller[OF cof] by blast
    ultimately show "P (Resume caller callee
        (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
      by (simp add: P_def entry_store_Resume_caller)
  qed
  then show ?thesis unfolding P_def .
qed

lemma key_entry_invariant_eq:
  assumes "callee \<in> valid_ltr gs g S" and "caller_of callee = Some caller"
  shows "key enterc startcontext callee
         = enterc (sink_node caller) (key enterc startcontext caller) (entry_store callee)"
  using key_entry_invariant[OF assms(1), THEN bspec, OF callers_refl, rule_format, OF assms(2),
      THEN conjunct1] .

lemma key_entry_invariant_call_enterD:
  assumes "callee \<in> valid_ltr gs g S" and "caller_of callee = Some caller"
  shows "call_enter_store gs g (sink_node caller) (sink_store caller) (entry_store callee)"
  using key_entry_invariant[OF assms(1), THEN bspec, OF callers_refl, rule_format, OF assms(2)]
  by (rule conjunct2)

subsection \<open>The activation-indexed context collecting\<close>

text \<open>The activation-sensitive collecting is the sink stores of valid traces reaching \<open>v\<close>
  whose activation \<^const>\<open>key\<close> is exactly the queried context \<open>c\<close>.\<close>

definition activation_collect ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> 'c
     \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store set" where
  "activation_collect gs enterc startcontext g S v c =
     {sink_store t | t. t \<in> valid_ltr gs g S \<and> sink_node t = v \<and> key enterc startcontext t = c}"

lemma activation_collect_I [intro]:
  "t \<in> valid_ltr gs g S \<Longrightarrow> sink_node t = v \<Longrightarrow> key enterc startcontext t = c
   \<Longrightarrow> sink_store t \<in> activation_collect gs enterc startcontext g S v c"
  unfolding activation_collect_def by blast

text \<open>Every collected state has a valid trace witness whose activation key is the queried \<open>c\<close>.\<close>
lemma activation_collect_E [elim]:
  assumes "s \<in> activation_collect gs enterc startcontext g S v c"
  obtains t where "t \<in> valid_ltr gs g S" "sink_node t = v" "key enterc startcontext t = c"
    "sink_store t = s"
  using assms unfolding activation_collect_def by blast


end
