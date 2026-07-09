theory Exec_Sign_Cmp_Seed_Sound
  imports Exec_Sign_Cmp_Seed_Enter
begin

section \<open>The clean transfer is sound over the local read (R_read)\<close>

text \<open>
  Stage 2 (\<open>clean_transfer_unsound\<close>) showed \<^const>\<open>sign_etf_clean\<close> violates the
  \<^emph>\<open>Obs\<close>-quantified contract \<^locale>\<open>sound_effectful_transfer\<close>: its assign obligation
  quantifies the incoming store over \<open>\<lbrakk>sg (Inl u) \<squnion> glob_env sg\<rbrakk>\<close> (local \<squnion> global),
  and the clean image drops a callee-entry global read.

  The Goblint-faithful reformulation quantifies the same obligation over the
  \<^emph>\<open>local\<close> read \<open>\<lbrakk>sg (Inl u)\<rbrakk>\<close> (\<^bold>\<open>R_read\<close>, \<^const>\<open>route_read_cmp\<close> --- Goblint's
  \<open>man.local\<close> \<open>D.t\<close>).  The clean transfer satisfies \<^emph>\<open>that\<close> contract
  \<^bold>\<open>unconditionally\<close>: \<open>f (sg (Inl u))\<close> soundly steps the concretisation of the local
  slot, because the base transfer \<^const>\<open>sign_tf\<close> is sound on any abstract state
  (\<^const>\<open>sound_transfer\<close>), applied here to the local slot.  The seed's role
  (\<open>seed_clean_sound_on_prog2\<close>) is to make that local slot soundly over-approximate
  the stores reaching the callee entry --- \<^emph>\<open>including\<close> the caller's globals --- so
  the clean spine then propagates soundly reading only the local.
\<close>

subsection \<open>The clean edge tree is the base transfer applied to the local slot\<close>

lemma apply_etf_sign_etf_clean:
  "apply_etf sign_etf_clean a u = clean_edge_tree (apply_tf sign_tf a) u"
  unfolding sign_etf_clean_def clean_etf_of_transfer_def by (cases a) simp_all

lemma etf_full_apply_etf_clean:
  "etf_full (apply_etf sign_etf_clean a u) sg = apply_tf sign_tf a (sg (Inl u))"
  by (simp add: apply_etf_sign_etf_clean etf_full_clean_edge_tree)

lemma clean_collecting_full_eq:
  "etf_collecting_full (clean_edge_tree f u) sg = f (sg (Inl u)) \<squnion> glob_env sg"
  by (simp add: etf_collecting_full_def etf_full_clean_edge_tree)

subsection \<open>Edge-collect soundness over the local read\<close>

text \<open>
  The core certified fact: on the concretisation of the \<^emph>\<open>local\<close> slot, the concrete
  edge step is over-approximated by the clean transfer's reassembled result.  It
  reduces directly to the base @{thm sign_sound_tf.edge_collect_apply_tf_sound} with
  the local slot \<open>sg (Inl u)\<close> as the abstract state --- no published-global read,
  no \<open>\<squnion> g\<close>.
\<close>

lemma clean_edge_collect_rread:
  "edge_collect a \<lbrakk>sg (Inl u)\<rbrakk> \<subseteq> \<lbrakk>etf_full (apply_etf sign_etf_clean a u) sg\<rbrakk>"
  unfolding etf_full_apply_etf_clean
  by (rule sign_sound_tf.edge_collect_apply_tf_sound)

subsection \<open>The five R_read transfer obligations\<close>

text \<open>
  The \<^locale>\<open>sound_effectful_transfer\<close> contract, restated with each premise
  quantified over the local read \<open>\<lbrakk>sg (Inl u)\<rbrakk>\<close> instead of \<open>\<lbrakk>sg (Inl u) \<squnion> glob_env sg\<rbrakk>\<close>.
  All five hold for the clean transfer with no side condition.
\<close>

lemma clean_rread_nop:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>"
  shows "s \<in> \<lbrakk>etf_collecting_full (etf_nop sign_etf_clean u) sg\<rbrakk>"
proof -
  have "sg (Inl u) \<le> etf_collecting_full (etf_nop sign_etf_clean u) sg"
    by (simp add: sign_etf_clean_def clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using assms gamma_state_mono by blast
qed

lemma clean_rread_assign:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>"
  shows "s(x := IMP2_Expr.aval e s) \<in> \<lbrakk>etf_collecting_full (etf_assign sign_etf_clean x e u) sg\<rbrakk>"
proof -
  have base: "s(x := IMP2_Expr.aval e s) \<in> \<lbrakk>tf_assign sign_tf x e (sg (Inl u))\<rbrakk>"
    using sound_transfer.tf_sound_assign[OF sign_is_sound_transfer] assms by blast
  have "tf_assign sign_tf x e (sg (Inl u)) \<le> etf_collecting_full (etf_assign sign_etf_clean x e u) sg"
    by (simp add: sign_etf_clean_def clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using base gamma_state_mono by blast
qed

lemma clean_rread_assume:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>" and "IMP2_Expr.bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full (etf_assume sign_etf_clean b u) sg\<rbrakk>"
proof -
  have base: "s \<in> \<lbrakk>tf_assume sign_tf b (sg (Inl u))\<rbrakk>"
    using sound_transfer.tf_sound_assume[OF sign_is_sound_transfer] assms by blast
  have "tf_assume sign_tf b (sg (Inl u)) \<le> etf_collecting_full (etf_assume sign_etf_clean b u) sg"
    by (simp add: sign_etf_clean_def clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using base gamma_state_mono by blast
qed

lemma clean_rread_assume_not:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>" and "\<not> IMP2_Expr.bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full (etf_assume_not sign_etf_clean b u) sg\<rbrakk>"
proof -
  have base: "s \<in> \<lbrakk>tf_assume_not sign_tf b (sg (Inl u))\<rbrakk>"
    using sound_transfer.tf_sound_assume_not[OF sign_is_sound_transfer] assms by blast
  have "tf_assume_not sign_tf b (sg (Inl u)) \<le> etf_collecting_full (etf_assume_not sign_etf_clean b u) sg"
    by (simp add: sign_etf_clean_def clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using base gamma_state_mono by blast
qed

lemma clean_rread_enter:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>etf_collecting_full (etf_enter sign_etf_clean u) sg\<rbrakk>"
proof -
  have base: "enter_state s \<in> \<lbrakk>tf_enter sign_tf (sg (Inl u))\<rbrakk>"
    using sound_transfer.tf_sound_enter[OF sign_is_sound_transfer] assms by blast
  have "tf_enter sign_tf (sg (Inl u)) \<le> etf_collecting_full (etf_enter sign_etf_clean u) sg"
    by (simp add: sign_etf_clean_def clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using base gamma_state_mono by blast
qed

section \<open>Flat collecting soundness of the clean spine over the local read\<close>

text \<open>
  The R_read analogue of @{thm sign_sound_tf.cfg_witness_gamma}: a family \<open>sg\<close> whose
  local slots satisfy the natural post-fixpoint bounds --- the clean per-edge
  result \<open>etf_full (apply_etf sign_etf_clean a u) sg\<close> bounded by the successor
  \<^emph>\<open>local\<close> slot \<open>sg (Inl w)\<close>, a combine bound, and an entry seed bound --- soundly
  over-approximates \<^const>\<open>cfg_collect\<close> at \<^emph>\<open>the local slot\<close>.  The conclusion is
  \<open>\<lbrakk>sg (Inl v)\<rbrakk>\<close> (R_read), \<^emph>\<open>not\<close> \<open>\<lbrakk>sg (Inl v) \<squnion> glob_env sg\<rbrakk>\<close> (Obs): the clean spine
  never rejoins the published global.  \<open>combine_le\<close> abstracts the procedure-return
  combine as a discharged side condition (the concrete run supplies it).
\<close>

lemma clean_cfg_witness_rread:
  assumes step_le: "\<And>u a w. (u, a, w) \<in> edges g
      \<Longrightarrow> etf_full (apply_etf sign_etf_clean a u) sg \<le> sg (Inl w)"
    and combine_le: "\<And>c ex ret s t. (c, ex, ret) \<in> combines g
      \<Longrightarrow> s \<in> \<lbrakk>sg (Inl c)\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl ex)\<rbrakk> \<Longrightarrow> <s|t> \<in> \<lbrakk>sg (Inl ret)\<rbrakk>"
    and entry_le: "S \<subseteq> \<lbrakk>sg (Inl (cfg_entry g))\<rbrakk>"
    and wit: "cfg_witness g S v st"
  shows "st \<in> \<lbrakk>sg (Inl v)\<rbrakk>"
proof -
  from wit entry_le show "st \<in> \<lbrakk>sg (Inl v)\<rbrakk>"
  proof (induction rule: cfg_witness.induct)
    case (entry v s S)
    then show ?case by (auto simp: subset_eq)
  next
    case (edge u a v S s t)
    have su: "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>" using edge.IH edge.prems by blast
    have "t \<in> \<lbrakk>etf_full (apply_etf sign_etf_clean a u) sg\<rbrakk>"
      using edge.hyps su clean_edge_collect_rread edge_collect_mono by blast
    thus ?case using step_le[OF edge.hyps(1)] gamma_state_mono by blast
  next
    case (combine c ex v S s t)
    have "s \<in> \<lbrakk>sg (Inl c)\<rbrakk>" using combine.IH(1) combine.prems by blast
    moreover have "t \<in> \<lbrakk>sg (Inl ex)\<rbrakk>" using combine.IH(2) combine.prems by blast
    ultimately show ?case by (rule combine_le[OF combine.hyps(1)])
  qed
qed

theorem clean_cfg_collect_rread:
  assumes step_le: "\<And>u a w. (u, a, w) \<in> edges g
      \<Longrightarrow> etf_full (apply_etf sign_etf_clean a u) sg \<le> sg (Inl w)"
    and combine_le: "\<And>c ex ret s t. (c, ex, ret) \<in> combines g
      \<Longrightarrow> s \<in> \<lbrakk>sg (Inl c)\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl ex)\<rbrakk> \<Longrightarrow> <s|t> \<in> \<lbrakk>sg (Inl ret)\<rbrakk>"
    and entry_le: "S \<subseteq> \<lbrakk>sg (Inl (cfg_entry g))\<rbrakk>"
  shows "cfg_collect g S v \<subseteq> \<lbrakk>sg (Inl v)\<rbrakk>"
proof
  fix st assume a: "st \<in> cfg_collect g S v"
  have w: "cfg_witness g S v st"
    using a by (simp add: cfg_collect_eq_paths cfg_collect_paths_def)
  show "st \<in> \<lbrakk>sg (Inl v)\<rbrakk>"
    by (rule clean_cfg_witness_rread[OF step_le combine_le entry_le w])
qed

section \<open>Context-sliced collecting soundness over the local read (R_read)\<close>

text \<open>
  The context-sensitive statement the migration targets: the clean spine's
  \<^emph>\<open>per-context\<close> local slot \<open>sg (Inl (v, ctx))\<close> soundly over-approximates the
  context-sliced collecting semantics \<^const>\<open>cfg_collect_ctx\<close> --- Goblint's
  \<open>(node, context)\<close> unknown.  It instantiates the read-agnostic trace backbone
  \<open>post_fixpoint_sound_at_ctx_semantic_generic\<close> with \<^bold>\<open>both\<close> the observation
  read \<open>renv\<close> and the routing read \<open>rread\<close> set to \<^const>\<open>route_read_cmp\<close> (the local
  slot).  Two consequences, each dissolving an obstruction the retain spine hit:

    \<^item> \<^bold>\<open>No \<open>'g :: finite\<close>.\<close>  \<^const>\<open>route_read_cmp\<close> never touches an \<open>Inr\<close> slot, so
      the global-key type is unconstrained.  The \<open>Keyed_Retain_EnterMono\<close>
      obstruction (A) --- \<^typ>\<open>sign st\<close> is not \<^class>\<open>finite\<close>, so
      \<^const>\<open>side_env_cmp\<close> does not type-apply --- is gone: the value-keyed context
      needs no finite quotient.
    \<^item> \<^bold>\<open>ENTER_MONO over the local read.\<close>  The entering store is quantified over
      \<open>\<lbrakk>sg (Inl (cl, ctx))\<rbrakk>\<close>, the precise per-context local --- not the coarse
      published global that dominated the Obs read (obstruction B).  Where two
      value-distinct activations share a context under the retain run, seeding the
      local separates them into point contexts (\<open>kgen_rread_contexts_points\<close>).
\<close>

text \<open>An edge step is sound under a local (R_read) post-fixpoint bound: the base
  transfer over the local slot dominates the successor local slot.\<close>

lemma clean_edge_ctx_of_bound:
  assumes bound: "apply_tf sign_tf a A \<le> B"
    and s: "s \<in> \<lbrakk>A\<rbrakk>"
    and step: "edge_step a s = Some s'"
  shows "s' \<in> \<lbrakk>B\<rbrakk>"
proof -
  have m: "s' \<in> edge_collect a {s}" using step by (simp add: edge_collect_single)
  have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>A\<rbrakk>" using s edge_collect_mono by blast
  also have "... \<subseteq> \<lbrakk>apply_tf sign_tf a A\<rbrakk>" by (rule sign_sound_tf.edge_collect_apply_tf_sound)
  also have "... \<subseteq> \<lbrakk>B\<rbrakk>" using gamma_state_mono[OF bound] by blast
  finally show ?thesis using m by blast
qed

text \<open>
  The per-trace kernel: instantiate the generic backbone at \<open>renv = rread =
  route_read_cmp\<close>.  \<open>EDGE_BOUND\<close> is the local post-fixpoint bound (the clean
  transfer writes to the local slot); \<open>ENTER_MONO\<close> reads the routing context from
  the local slot; \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> are the seed obligations (the callee-entry
  local over-approximates the reaching stores of the context, globals included);
  \<open>COMB\<close> is the procedure-return combine.  All reads are the local slot.
\<close>

theorem clean_ctx_trace_rread:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> sign abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> sign abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf sign_tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> <last tau|last rho> \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sg (Inl (cl, ctx))))"
    and wit: "trace_witness g S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof -
  have "last tr \<in> \<lbrakk>route_read_cmp sg (v, ctx)\<rbrakk>"
  proof (rule post_fixpoint_sound_at_ctx_semantic_generic
      [where renv = route_read_cmp and rread = route_read_cmp and rt = rt
         and \<sigma> = sg and dg = dg and cmp = cmp and entdg = entdg and S = S and g = g])
    show "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>route_read_cmp sg (cfg_entry g, ctx)\<rbrakk>"
      using ENTRY by (simp add: route_read_cmp_def)
  next
    show "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>route_read_cmp sg (v, ctx)\<rbrakk>"
      using PROC_ENTRY by (simp add: route_read_cmp_def)
  next
    fix ctx u a v tr' s'
    assume e: "(u, a, v) \<in> edges g" and st: "edge_step a (last tr') = Some s'"
      and lt: "last tr' \<in> \<lbrakk>route_read_cmp sg (u, ctx)\<rbrakk>"
    show "s' \<in> \<lbrakk>route_read_cmp sg (v, ctx)\<rbrakk>"
      using clean_edge_ctx_of_bound[OF EDGE_BOUND[OF e] _ st] lt
      by (simp add: route_read_cmp_def)
  next
    fix ctx cl ex v tau rho
    assume c: "(cl, ex, v) \<in> combines g"
      and ct: "last tau \<in> \<lbrakk>route_read_cmp sg (cl, ctx)\<rbrakk>"
      and ce: "last rho \<in> \<lbrakk>route_read_cmp sg (ex, rt cl ctx (route_read_cmp sg (cl, ctx)))\<rbrakk>"
    show "<last tau|last rho> \<in> \<lbrakk>route_read_cmp sg (v, ctx)\<rbrakk>"
      using COMB[OF c] ct ce by (simp add: route_read_cmp_def)
  next
    show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx" using DG_INTRA .
  next
    show "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau" using DG_RETURN .
  next
    show "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)" using DG_CALLEE .
  next
    show "\<And>ctx cl s. s \<in> \<lbrakk>route_read_cmp sg (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (route_read_cmp sg (cl, ctx)))"
      using ENTER_MONO by (simp add: route_read_cmp_def)
  next
    show "trace_witness g S v tr" by (rule wit)
  next
    show "cmp (dg tr) ctx" by (rule compat)
  qed
  thus ?thesis by (simp add: route_read_cmp_def)
qed

text \<open>
  The set-level context-sliced soundness: every store reaching \<open>v\<close> along a trace
  whose digest is \<open>cmp\<close>-compatible with \<open>ctx\<close> lies in the concretisation of the
  \<^emph>\<open>local\<close> slot at \<open>(v, ctx)\<close>.  The conclusion \<open>\<lbrakk>sg (Inl (v, ctx))\<rbrakk>\<close> is R_read;
  the coarse published global never enters it.
\<close>

theorem clean_ctx_collect_rread:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> sign abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> sign abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf sign_tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> <last tau|last rho> \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sg (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof -
  have tr_sound: "\<And>tr. trace_witness g S v tr \<Longrightarrow> cmp (dg tr) ctx \<Longrightarrow> last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  proof -
    fix tr assume w: "trace_witness g S v tr" and c: "cmp (dg tr) ctx"
    show "last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
      by (rule clean_ctx_trace_rread
          [where sg = sg and rt = rt and dg = dg and cmp = cmp and entdg = entdg and g = g and S = S,
           OF ENTRY PROC_ENTRY EDGE_BOUND COMB DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO w c])
  qed
  show ?thesis
    unfolding cfg_collect_ctx_def alpha_ctx_def cfg_collect_trace_def
    using tr_sound by auto
qed

section \<open>Executable reduction: discharging the digest-propagation obligations\<close>

text \<open>
  For any \<^emph>\<open>head\<close> digest --- one reading only the head store of the current
  activation, \<^const>\<open>head_digest\<close> --- the three digest-propagation obligations
  (\<open>DG_INTRA\<close> / \<open>DG_RETURN\<close> / \<open>DG_CALLEE\<close>) of \<open>clean_ctx_collect_rread\<close> are
  discharged generically (program- and value-independent).  What remains is exactly
  the run-specific bundle: the seed soundness (\<open>ENTRY\<close> / \<open>PROC_ENTRY\<close>), the local
  post-fixpoint bounds (\<open>EDGE_BOUND\<close> / \<open>COMB\<close>), and the value-digest routing
  (\<open>ENTER_MONO\<close>, over the local read).  This is the R_read analogue of the retain
  spine's \<open>..._if_post_fixpoint\<close> reduction --- and, unlike it, needs no
  \<open>'c :: finite\<close> (the conclusion is the local slot, not \<^const>\<open>side_env_cmp\<close>).
\<close>

theorem clean_ctx_collect_rread_head:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> sign abs_state"
    and f :: "store \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> sign abs_state \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (head_digest f [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (head_digest f [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf sign_tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> <last tau|last rho> \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (f (enter_state s)) (rt cl ctx (sg (Inl (cl, ctx))))"
  shows "cfg_collect_ctx (head_digest f) cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule clean_ctx_collect_rread
      [where dg = "head_digest f" and entdg = "\<lambda>s. f (enter_state s)" and rt = rt
         and sg = sg and cmp = cmp and g = g and S = S])
  show "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (head_digest f [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    by (rule ENTRY)
next
  show "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (head_digest f [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule PROC_ENTRY)
next
  show "\<And>ctx u a v. (u, a, v) \<in> edges g \<Longrightarrow> apply_tf sign_tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    by (rule EDGE_BOUND)
next
  show "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> <last tau|last rho> \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule COMB)
next
  show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (head_digest f (tr @ [s'])) ctx \<Longrightarrow> cmp (head_digest f tr) ctx"
    by (rule head_digest_DG_INTRA)
next
  show "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> head_digest f (tau @ tl rho @ [<last tau|last rho>]) = head_digest f tau"
    by (rule head_digest_DG_RETURN)
next
  show "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> head_digest f rho = f (enter_state (last tau))"
    by (simp add: head_digest_def)
next
  show "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk> \<Longrightarrow> cmp (f (enter_state s)) (rt cl ctx (sg (Inl (cl, ctx))))"
    by (rule ENTER_MONO)
qed

section \<open>Executable seeded-clean run on the two-call program\<close>

text \<open>
  The Goblint-faithful spine end to end on \<^const>\<open>kgen_prog\<close>
  (\<open>f(){G:=G+G}; main(){G:=0; f(); G:=1; f()}\<close>): the \<^emph>\<open>seeded\<close> generator
  \<^const>\<open>side_cfg_T_eff_cmp_seed_st\<close> with the faithful seed \<^const>\<open>restrict_global_st\<close>,
  the \<^emph>\<open>clean\<close> transfer \<^const>\<open>sign_etf_clean_st\<close>, and the R_read combine
  \<^const>\<open>kgen_combine_rread\<close>, fed to the vendored side solver.
\<close>

definition kgen_seed_clean_eqs :: "(pp \<times> sign st, sign st, sign st) eqsT" where
  "kgen_seed_clean_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. kgen_combine_rread cc ex c)
     restrict_global_st kgen_cfg sign_etf_clean_st bot cinit_sign_st"

definition kgen_seed_clean_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "kgen_seed_clean_solution = TD_side_always_join_Interp_solve kgen_seed_clean_eqs (cfg_exit kgen_cfg, bot)"

lemma kgen_seed_clean_runs: "fst kgen_seed_clean_solution \<noteq> {}"
  unfolding kgen_seed_clean_solution_def kgen_seed_clean_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>
  The seed puts the caller's global into the callee-entry \<^emph>\<open>local\<close>: the caller-local
  slots at the two call sites (pp 4, pp 7) are the points \<^const>\<open>SZero\<close> and
  \<^const>\<open>SPos\<close> --- the clean transfer read them, not the published slot.
\<close>

lemma kgen_seed_clean_caller_locals:
  "lookup_st (snd kgen_seed_clean_solution (Inl (4, bot::sign st))) ''G'' = SZero
   \<and> lookup_st (snd kgen_seed_clean_solution (Inl (7, bot::sign st))) ''G'' = SPos"
  unfolding kgen_seed_clean_solution_def kgen_seed_clean_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>The two activations land in separate point contexts \<open>{G:SZero}\<close>, \<open>{G:SPos}\<close>.\<close>

lemma kgen_seed_clean_precision:
  "lookup_st (snd kgen_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SZero
   \<and> lookup_st (snd kgen_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SPos)])))) ''G'' = SPos"
  unfolding kgen_seed_clean_solution_def kgen_seed_clean_eqs_def kgen_cfg_def kgen_ec_def
    kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

section \<open>Precision witnesses: the global-derived context split\<close>

text \<open>
  The two-call program \<open>kgen_cfg\<close> calls a procedure at two sites where the global
  \<open>G\<close> holds value-distinct signs.  Under the \<^emph>\<open>retain\<close> run the two activations
  share one keyed context slot, joining to the non-point \<^const>\<open>SNonNeg\<close>
  (\<open>retain_keyed_merged_G\<close>) --- the \<open>fctx\<close> obstruction.  Under the seeded-clean /
  R_read run they land in \<^emph>\<open>separate point contexts\<close> \<open>{G:SZero}\<close> and \<open>{G:SPos}\<close>
  (\<open>kgen_rread_contexts_points\<close>): the global-derived context split the retain read
  could not express.
\<close>

lemma sign_strict_precision: "SZero < SNonNeg" "SPos < SNonNeg" "SZero \<noteq> SPos"
  by eval+

text \<open>
  \<^bold>\<open>Strict precision, machine-backed.\<close>  The seeded-clean context slots are
  \<^emph>\<open>strictly\<close> below the retain merged slot: the first call context reads \<open>G = SZero\<close>,
  the second \<open>G = SPos\<close>, each a point strictly under the retain \<^const>\<open>SNonNeg\<close>.  The
  \<^const>\<open>SNonNeg\<close> obstruction (\<open>read_admits_two_point_classes\<close>) is gone.
\<close>

theorem rread_strictly_sharper_than_retain:
  "lookup_st (snd kgen_rread_solution (Inr (Abs_st (SBot, SBot, [(''G'', SZero)])))) ''G'' = SZero
   \<and> lookup_st (snd kgen_rread_solution (Inr (Abs_st (SBot, SBot, [(''G'', SPos)])))) ''G'' = SPos
   \<and> lookup_st (snd kgen_retain_solution (Inr kgen_ctx_merged)) ''G'' = SNonNeg
   \<and> SZero < SNonNeg \<and> SPos < SNonNeg"
  using kgen_rread_contexts_points retain_keyed_merged_G sign_strict_precision by simp

text \<open>
  \<^bold>\<open>What is certified.\<close>  The clean (Goblint-sequential) transfer, which reads only
  the local slot, is \<^emph>\<open>sound\<close> when soundness is measured against the local read:
  the five per-edge obligations (\<open>clean_rread_*\<close>) hold unconditionally; the flat
  theorem \<open>clean_cfg_collect_rread\<close> lifts them to \<^const>\<open>cfg_collect\<close>; and
  \<open>clean_ctx_collect_rread\<close> gives the context-sensitive statement against
  \<^const>\<open>cfg_collect_ctx\<close> with the conclusion at the per-context local slot
  \<open>sg (Inl (v, ctx))\<close>.  This is the read split the \<open>Keyed_Retain_EnterMono\<close>
  obstruction identified as the fix, and it clears \<^emph>\<open>both\<close> obstructions the retain
  spine hit: no \<open>'g :: finite\<close> quotient (the local read ignores \<open>Inr\<close>), and
  \<open>ENTER_MONO\<close> over the local read (decoupled from the coarse published global).
  The retain (\<open>\<squnion> g\<close>) / \<^const>\<open>side_env_cmp\<close> spine is untouched --- it remains the
  sound conservative baseline for the Obs conclusion.

  \<^bold>\<open>The entry invariant, explicitly.\<close>  \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> are exactly
  \<^emph>\<open>callee-entry local \<sqsupseteq> context-specific caller stores\<close> (globals included): every
  store reaching the entry in context \<open>ctx\<close> lies in \<open>\<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>\<close>.
  The Goblint-faithful seed \<open>side_cfg_T_eff_cmp_seed_st\<close> with
  \<^const>\<open>restrict_global_st\<close> establishes it per context
  (\<open>seed_clean_sound_on_prog2\<close>).  \<open>EDGE_BOUND\<close> then propagates it reading only the
  local, and \<open>clean_ctx_collect_rread\<close> concludes soundness --- \<^emph>\<open>without\<close> the
  \<open>local \<squnion> global\<close> recovery.

  \<^bold>\<open>Remaining obligation.\<close>  Discharging \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> / \<open>EDGE_BOUND\<close> /
  \<open>COMB\<close> / \<open>ENTER_MONO\<close> for the concrete executable seeded run \<open>seed_clean_sol\<close>
  through the \<open>_st\<close> and keyed bridges is the executable-reduction slice; the
  precision witnesses (\<open>kgen_rread_contexts_points\<close>, \<open>seed_clean_sound_on_prog2\<close>)
  already show the run meets them on the two-call program.
\<close>

end
