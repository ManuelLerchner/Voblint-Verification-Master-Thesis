theory LTR_Collect
  imports CFG_Local_Trace
begin

section \<open>Local-trace collecting semantics\<close>

text \<open>
  The stack-faithful concrete carrier of a compiled program is the local-trace set
  \<^const>\<open>valid_ltr\<close>.  This theory presents it as a least fixed point of an explicit
  monotone set transformer \<open>ltr_F\<close>, and defines the plain and keyed forgetful
  projections of a trace set to a program point.

  \<open>ltr_F\<close> has exactly the four clauses of \<^const>\<open>valid_ltr\<close> (root, intra step,
  call, return).  The return clause mirrors \<open>valid_ltr.ret\<close> literally: it demands
  \<open>callee \<in> T\<close> together with \<open>caller_of callee = Some caller\<close>, and nothing more.
  It does not add \<open>caller \<in> T\<close> as a premise, so a return still recovers its caller
  from the completed callee's own activation ancestry, never by an independent
  choice. The caller is recovered structurally through \<^const>\<open>caller_of\<close>.

  No solver, DG, or abstract-domain theory is imported.  This is a pure CFG-layer
  semantic theory, sitting directly above \<^theory>\<open>Voblint_CFG.CFG_Local_Trace\<close>.
\<close>

subsection \<open>The constructor transformer\<close>

definition ltr_F :: "cfg \<Rightarrow> store set \<Rightarrow> ltr set \<Rightarrow> ltr set" where
  "ltr_F g S T =
      {Root [(cfg_entry g, s)] | s. s \<in> S}
    \<union> {extend t (v, s') | t a v s'.
          t \<in> T \<and> (sink_node t, a, v) \<in> edges g \<and>
          \<not> is_enter_action a \<and> edge_step a (sink_store t) = Some s'}
    \<union> {Call caller [(fe, se)] | caller xs es fe ex ret dst se.
          caller \<in> T \<and>
          (sink_node caller, EA_Enter xs es, fe) \<in> edges g \<and>
          (sink_node caller, ex, ret, dst) \<in> combines g \<and>
          edge_step (EA_Enter xs es) (sink_store caller) = Some se}
    \<union> {Resume caller callee (path caller @ [(v, r)]) | callee caller v dst r.
          callee \<in> T \<and> caller_of callee = Some caller \<and>
          (sink_node caller, sink_node callee, v, dst) \<in> combines g \<and>
          r = combine_collect dst (sink_store caller) (sink_store callee)}"

subsection \<open>Monotonicity\<close>

lemma ltr_F_mono: "mono (ltr_F g S)"
proof (rule monoI)
  fix T T' :: "ltr set"
  assume "T \<subseteq> T'"
  then show "ltr_F g S T \<subseteq> ltr_F g S T'"
    unfolding ltr_F_def by blast
qed

lemma ltr_F_lfp_fold:
  "x \<in> ltr_F g S (lfp (ltr_F g S)) \<Longrightarrow> x \<in> lfp (ltr_F g S)"
  by (subst lfp_unfold[OF ltr_F_mono]) assumption

subsection \<open>Fixed-point characterization\<close>

text \<open>\<open>ltr_F\<close> maps \<^const>\<open>valid_ltr\<close> into itself: each of its four summands is discharged by
  the corresponding \<^const>\<open>valid_ltr\<close> introduction rule.  With \<open>lfp_lowerbound\<close> this gives one
  inclusion.\<close>
lemma ltr_F_valid_ltr_closed:
  "ltr_F g S (valid_ltr g S) \<subseteq> valid_ltr g S"
  unfolding ltr_F_def
  by (blast intro: valid_ltr.intros)

lemma lfp_ltr_F_subset_valid_ltr:
  "lfp (ltr_F g S) \<subseteq> valid_ltr g S"
  by (rule lfp_lowerbound) (rule ltr_F_valid_ltr_closed)

text \<open>The converse follows by \<^const>\<open>valid_ltr\<close> rule induction: every constructor step lands in
  \<open>ltr_F g S (lfp (ltr_F g S))\<close> using the induction hypotheses, then folds back into the least
  fixed point.  The \<open>ret\<close> case needs only the callee hypothesis, matching the transformer's
  return clause.\<close>
lemma valid_ltr_subset_lfp:
  "valid_ltr g S \<subseteq> lfp (ltr_F g S)"
proof
  fix t assume "t \<in> valid_ltr g S"
  then show "t \<in> lfp (ltr_F g S)"
  proof (induction rule: valid_ltr.induct)
    case (init s)
    have "Root [(cfg_entry g, s)] \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using init by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (intra t a v s')
    have "extend t (v, s') \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using intra.hyps intra.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (call caller xs es fe ex ret dst se)
    have "Call caller [(fe, se)] \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using call.hyps call.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (ret callee caller v dst r)
    have "Resume caller callee (path caller @ [(v, r)]) \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using ret.hyps ret.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  qed
qed

theorem valid_ltr_eq_lfp:
  "valid_ltr g S = lfp (ltr_F g S)"
  by (rule antisym[OF valid_ltr_subset_lfp lfp_ltr_F_subset_valid_ltr])

subsection \<open>Forgetful projections\<close>

text \<open>\<open>ltr_collect\<close> is the plain collecting view: the sink stores of valid traces reaching \<open>v\<close>.
  \<open>ltr_collect_keyed\<close> filters those by an arbitrary trace reader \<open>key\<close>.  The key type is not
  required finite, and a keyed bucket is not claimed to be an exact activation identity.\<close>

definition ltr_collect :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> store set" where
  "ltr_collect g S v =
     {sink_store t | t. t \<in> valid_ltr g S \<and> sink_node t = v}"

definition ltr_collect_keyed ::
  "(ltr \<Rightarrow> 'c) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> store set" where
  "ltr_collect_keyed keyf g S v c =
     {sink_store t | t. t \<in> valid_ltr g S \<and> sink_node t = v \<and> keyf t = c}"

lemma ltr_collect_I:
  "t \<in> valid_ltr g S \<Longrightarrow> sink_store t \<in> ltr_collect g S (sink_node t)"
  unfolding ltr_collect_def by blast

lemma ltr_collect_keyed_le_collect:
  "ltr_collect_keyed keyf g S v c \<subseteq> ltr_collect g S v"
  unfolding ltr_collect_keyed_def ltr_collect_def by blast

subsection \<open>Projection laws\<close>

text \<open>The keyed buckets exactly tile the plain view: every trace has a key, so ranging over all
  keys recovers the unfiltered collecting.  This holds for any total key with no finiteness
  assumption --- it says only that each trace lands in some bucket, not that a bucket preserves
  activation precision.\<close>
theorem ltr_collect_keyed_Union:
  "(\<Union>c. ltr_collect_keyed keyf g S v c) = ltr_collect g S v"
  unfolding ltr_collect_keyed_def ltr_collect_def by blast



subsection \<open>Activation-keyed projection\<close>

theorem activation_collect_eq_ltr_collect_keyed:
  "activation_collect enterc seedc g S v c
     = ltr_collect_keyed (key enterc seedc) g S v c"
  unfolding activation_collect_def ltr_collect_keyed_def by simp

subsection \<open>Matched returns\<close>

text \<open>Every reachable \<^const>\<open>Resume\<close> preserves the caller recovered from its completed callee.\<close>
theorem valid_ltr_Resume_caller_matched:
  "Resume caller callee p \<in> valid_ltr g S \<Longrightarrow> caller_of callee = Some caller"
  using valid_ltr_Resume_fields by blast

subsection \<open>Witnesses\<close>

text \<open>Three concrete traces reaching their expected \<open>ltr_collect\<close> projection: an
  intraprocedural step, a single matched call/return, and a nested matched call/return.  Each is
  stated over hypotheses on \<^const>\<open>edges\<close> and \<^const>\<open>combines\<close>, isolating the return structure
  from CFG encoding details.\<close>

text \<open>A single intra step reaches the collecting view at the target node.\<close>
lemma ltr_collect_intra_witness:
  fixes g :: cfg and s0 :: store and v :: pp
  assumes s0: "s0 \<in> S"
      and E: "(cfg_entry g, EA_Nop, v) \<in> edges g"
  shows "s0 \<in> ltr_collect g S v"
proof -
  let ?r = "Root [(cfg_entry g, s0)]"
  have r_mem: "?r \<in> valid_ltr g S" using s0 by (rule valid_ltr.init)
  have r_sn: "sink_node ?r = cfg_entry g" "sink_store ?r = s0"
    by (simp_all add: sink_node_def sink_store_def)
  have step_mem: "extend ?r (v, s0) \<in> valid_ltr g S"
    by (rule valid_ltr.intra[OF r_mem, where a = EA_Nop])
       (simp_all add: r_sn E is_enter_action_def)
  from ltr_collect_I[OF step_mem] show ?thesis
    by (simp add: sink_node_def sink_store_def)
qed

text \<open>One call and its matched return.  The returned caller \<open>main\<close> is recovered from the
  completed callee by \<^const>\<open>caller_of\<close>, not selected independently.\<close>
lemma ltr_collect_call_return_witness:
  fixes g :: cfg and s0 :: store and nf fx mr :: pp
  assumes s0: "s0 \<in> S"
      and E1: "(cfg_entry g, EA_Enter [] [], nf) \<in> edges g"
      and E2: "(nf, EA_Nop, fx) \<in> edges g"
      and Cf: "(cfg_entry g, fx, mr, None) \<in> combines g"
  shows "combine_collect None s0 (enter_state s0) \<in> ltr_collect g S mr"
proof -
  let ?main = "Root [(cfg_entry g, s0)]"
  have main_mem: "?main \<in> valid_ltr g S" using s0 by (rule valid_ltr.init)
  have m_sn: "sink_node ?main = cfg_entry g" "sink_store ?main = s0"
    by (simp_all add: sink_node_def sink_store_def)
  let ?f0 = "Call ?main [(nf, enter_state s0)]"
  have f0_mem: "?f0 \<in> valid_ltr g S"
    by (rule valid_ltr.call[OF main_mem, where xs = "[]" and es = "[]"
                            and ex = fx and ret = mr and dst = None])
       (simp_all add: m_sn E1 Cf is_enter_action_def bind_formals_def)
  have f0_sn: "sink_node ?f0 = nf" "sink_store ?f0 = enter_state s0"
    by (simp_all add: sink_node_def sink_store_def)
  let ?f1 = "extend ?f0 (fx, enter_state s0)"
  have f1_mem: "?f1 \<in> valid_ltr g S"
    by (rule valid_ltr.intra[OF f0_mem, where a = EA_Nop])
       (simp_all add: f0_sn E2 is_enter_action_def)
  have f1_caller: "caller_of ?f1 = Some ?main" by simp
  have f1_sn: "sink_node ?f1 = fx" "sink_store ?f1 = enter_state s0"
    by (simp_all add: sink_node_def sink_store_def)
  have res_mem:
    "Resume ?main ?f1 (path ?main @ [(mr, combine_collect None s0 (enter_state s0))])
       \<in> valid_ltr g S"
    by (rule valid_ltr.ret[OF f1_mem f1_caller, where v = mr and dst = None])
       (simp_all add: Cf sink_node_def sink_store_def)
  from ltr_collect_I[OF res_mem] show ?thesis
    by (simp add: sink_node_def sink_store_def)
qed

text \<open>A nested call \<open>main \<rightarrow> f \<rightarrow> g\<close> with both returns matched.  \<open>g\<close> returns into \<open>f\<close> and
  \<open>f\<close> into \<open>main\<close>; the outer return recovers \<open>main\<close> from the already-resumed \<open>f\<close> through
  \<^const>\<open>caller_of\<close>.  Built on \<open>nested_valid_ltr_example\<close>.\<close>
lemma ltr_collect_nested_witness:
  fixes g :: cfg and s0 :: store and nf ng gx fr mr :: pp
  assumes s0: "s0 \<in> S"
      and E1: "(cfg_entry g, EA_Enter [] [], nf) \<in> edges g"
      and E2: "(nf, EA_Enter [] [], ng) \<in> edges g"
      and E3: "(ng, EA_Nop, gx) \<in> edges g"
      and Cf: "(cfg_entry g, fr, mr, None) \<in> combines g"
      and Cg: "(nf, gx, fr, None) \<in> combines g"
  shows "combine_collect None s0
           (combine_collect None (enter_state s0) (enter_state (enter_state s0)))
         \<in> ltr_collect g S mr"
  using ltr_collect_I[OF nested_valid_ltr_example[OF s0 E1 E2 E3 Cf Cg]]
  by (simp add: sink_node_def sink_store_def)

end
