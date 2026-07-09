theory Clean_RRead_Sound
  imports TD_Side_Eff_Cmp_Sound
begin

section \<open>The clean (sequential-faithful) transfer over the local read (R_read)\<close>

text \<open>
  The Goblint-sequential transfer reads only the \<^emph>\<open>local\<close> slot \<open>sg (Inl u)\<close>
  (\<^bold>\<open>R_read\<close>, \<^const>\<open>route_read_cmp\<close> --- Goblint's \<open>man.local\<close> \<open>D.t\<close>) and never rejoins
  the published global (\<^const>\<open>glob_env\<close>).  This theory builds that transfer from an
  arbitrary base @{locale sound_transfer} \<open>tf\<close> and certifies its R_read soundness at
  every program point and every context.  The domain enters only through
  \<open>tf :: 'a::sound_domain domain_transfer\<close>: @{locale sound_transfer} instances (Sign,
  Interval, ...) obtain the whole spine by interpretation.
\<close>

subsection \<open>The clean edge tree and the clean transfer record\<close>

text \<open>
  A clean edge writes the base transfer's result to the local slot and publishes its
  global projection to the flow-insensitive slot; the collecting image re-reads only
  the old global (\<^const>\<open>etf_collecting_full\<close>), so the clean transfer sees no
  callee-entry global through the transfer itself --- that is the seed's job.
\<close>

definition clean_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> 'u \<Rightarrow> ('u, unit, 'a abs_state) strategy_tree" where
  "clean_edge_tree f u = QueryL u (\<lambda>su. let res = f su in Side () (restrict_global res) (Answer res))"

lemma restrict_global_le': "restrict_global s \<le> s"
  by (simp add: restrict_global_def le_fun_def)

lemma etf_full_clean_edge_tree: "etf_full (clean_edge_tree f u) sg = f (sg (Inl u))"
  unfolding clean_edge_tree_def etf_full_def all_sides_def traverse_rhs_def
  by (simp add: Let_def sup.absorb1 restrict_global_le')

definition clean_etf_of_transfer ::
  "'a::bounded_semilattice_sup_bot domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer" where
  "clean_etf_of_transfer tf = \<lparr>
     etf_nop = clean_edge_tree (apply_tf tf EA_Nop),
     etf_assign = (\<lambda>x e. clean_edge_tree (apply_tf tf (EA_Assign x e))),
     etf_assume = (\<lambda>b. clean_edge_tree (apply_tf tf (EA_Assume b))),
     etf_assume_not = (\<lambda>b. clean_edge_tree (apply_tf tf (EA_AssumeNot b))),
     etf_enter = clean_edge_tree (apply_tf tf EA_Enter),
     etf_combine = unit_combine_tree \<rparr>"

subsection \<open>Denotation of the clean transfer: the base transfer on the local slot\<close>

lemma clean_collecting_full_eq:
  "etf_collecting_full (clean_edge_tree f u) sg = f (sg (Inl u)) \<squnion> glob_env sg"
  by (simp add: etf_collecting_full_def etf_full_clean_edge_tree)

lemma apply_etf_clean_etf:
  "apply_etf (clean_etf_of_transfer tf) a u = clean_edge_tree (apply_tf tf a) u"
  unfolding clean_etf_of_transfer_def by (cases a) simp_all

lemma etf_full_apply_etf_clean:
  "etf_full (apply_etf (clean_etf_of_transfer tf) a u) sg = apply_tf tf a (sg (Inl u))"
  by (simp add: apply_etf_clean_etf etf_full_clean_edge_tree)

context sound_transfer
begin

subsection \<open>Edge-collect soundness over the local read\<close>

text \<open>
  On the concretisation of the \<^emph>\<open>local\<close> slot the concrete edge step is
  over-approximated by the clean transfer's reassembled result.  It reduces to
  @{thm edge_collect_apply_tf_sound} with the local slot as the abstract state ---
  no published-global read, no \<open>\<squnion> g\<close>.
\<close>

lemma clean_edge_collect_rread:
  "edge_collect a \<lbrakk>sg (Inl u)\<rbrakk> \<subseteq> \<lbrakk>etf_full (apply_etf (clean_etf_of_transfer tf) a u) sg\<rbrakk>"
  unfolding etf_full_apply_etf_clean
  by (rule edge_collect_apply_tf_sound)

subsection \<open>The five R_read transfer obligations\<close>

text \<open>
  The @{locale sound_effectful_transfer} contract with each premise quantified over
  the local read \<open>\<lbrakk>sg (Inl u)\<rbrakk>\<close> instead of \<open>\<lbrakk>sg (Inl u) \<squnion> glob_env sg\<rbrakk>\<close>.  All five
  hold for the clean transfer with no side condition.
\<close>

lemma clean_rread_nop:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>"
  shows "s \<in> \<lbrakk>etf_collecting_full (etf_nop (clean_etf_of_transfer tf) u) sg\<rbrakk>"
proof -
  have "sg (Inl u) \<le> etf_collecting_full (etf_nop (clean_etf_of_transfer tf) u) sg"
    by (simp add: clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using assms gamma_state_mono by blast
qed

lemma clean_rread_assign:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>"
  shows "s(x := IMP2_Expr.aval e s) \<in> \<lbrakk>etf_collecting_full (etf_assign (clean_etf_of_transfer tf) x e u) sg\<rbrakk>"
proof -
  have base: "s(x := IMP2_Expr.aval e s) \<in> \<lbrakk>tf_assign tf x e (sg (Inl u))\<rbrakk>"
    using tf_sound_assign assms by blast
  have "tf_assign tf x e (sg (Inl u)) \<le> etf_collecting_full (etf_assign (clean_etf_of_transfer tf) x e u) sg"
    by (simp add: clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using base gamma_state_mono by blast
qed

lemma clean_rread_assume:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>" and "IMP2_Expr.bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full (etf_assume (clean_etf_of_transfer tf) b u) sg\<rbrakk>"
proof -
  have base: "s \<in> \<lbrakk>tf_assume tf b (sg (Inl u))\<rbrakk>"
    using tf_sound_assume assms by blast
  have "tf_assume tf b (sg (Inl u)) \<le> etf_collecting_full (etf_assume (clean_etf_of_transfer tf) b u) sg"
    by (simp add: clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using base gamma_state_mono by blast
qed

lemma clean_rread_assume_not:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>" and "\<not> IMP2_Expr.bval b s"
  shows "s \<in> \<lbrakk>etf_collecting_full (etf_assume_not (clean_etf_of_transfer tf) b u) sg\<rbrakk>"
proof -
  have base: "s \<in> \<lbrakk>tf_assume_not tf b (sg (Inl u))\<rbrakk>"
    using tf_sound_assume_not assms by blast
  have "tf_assume_not tf b (sg (Inl u)) \<le> etf_collecting_full (etf_assume_not (clean_etf_of_transfer tf) b u) sg"
    by (simp add: clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using base gamma_state_mono by blast
qed

lemma clean_rread_enter:
  assumes "s \<in> \<lbrakk>sg (Inl u)\<rbrakk>"
  shows "enter_state s \<in> \<lbrakk>etf_collecting_full (etf_enter (clean_etf_of_transfer tf) u) sg\<rbrakk>"
proof -
  have base: "enter_state s \<in> \<lbrakk>tf_enter tf (sg (Inl u))\<rbrakk>"
    using tf_sound_enter assms by blast
  have "tf_enter tf (sg (Inl u)) \<le> etf_collecting_full (etf_enter (clean_etf_of_transfer tf) u) sg"
    by (simp add: clean_etf_of_transfer_def clean_collecting_full_eq)
  thus ?thesis using base gamma_state_mono by blast
qed

subsection \<open>Flat collecting soundness over the local read\<close>

text \<open>
  A family \<open>sg\<close> whose local slots satisfy the natural post-fixpoint bounds --- the
  clean per-edge result bounded by the successor \<^emph>\<open>local\<close> slot \<open>sg (Inl w)\<close>, a
  combine bound, and an entry seed bound --- soundly over-approximates
  \<^const>\<open>cfg_collect\<close> at the local slot.  The conclusion \<open>\<lbrakk>sg (Inl v)\<rbrakk>\<close> is R_read,
  never \<open>\<lbrakk>sg (Inl v) \<squnion> glob_env sg\<rbrakk>\<close>.  \<open>combine_le\<close> abstracts the procedure-return
  combine (Goblint \<open>Spec.combine\<close>) as a discharged side condition.
\<close>

lemma clean_cfg_witness_rread:
  assumes step_le: "\<And>u a w. (u, a, w) \<in> edges g
      \<Longrightarrow> etf_full (apply_etf (clean_etf_of_transfer tf) a u) sg \<le> sg (Inl w)"
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
    have "t \<in> \<lbrakk>etf_full (apply_etf (clean_etf_of_transfer tf) a u) sg\<rbrakk>"
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
      \<Longrightarrow> etf_full (apply_etf (clean_etf_of_transfer tf) a u) sg \<le> sg (Inl w)"
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

subsection \<open>Context-sliced collecting soundness over the local read\<close>

text \<open>
  An edge step is sound under a local (R_read) post-fixpoint bound: the base
  transfer over the local slot dominates the successor local slot.
\<close>

lemma clean_edge_ctx_of_bound:
  assumes bound: "apply_tf tf a A \<le> B"
    and s: "s \<in> \<lbrakk>A\<rbrakk>"
    and step: "edge_step a s = Some s'"
  shows "s' \<in> \<lbrakk>B\<rbrakk>"
proof -
  have m: "s' \<in> edge_collect a {s}" using step by (simp add: edge_collect_single)
  have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>A\<rbrakk>" using s edge_collect_mono by blast
  also have "... \<subseteq> \<lbrakk>apply_tf tf a A\<rbrakk>" by (rule edge_collect_apply_tf_sound)
  also have "... \<subseteq> \<lbrakk>B\<rbrakk>" using gamma_state_mono[OF bound] by blast
  finally show ?thesis using m by blast
qed

text \<open>
  The per-trace kernel: instantiate @{thm post_fixpoint_sound_at_ctx_semantic_generic}
  at \<open>renv = rread = route_read_cmp\<close>.  \<open>EDGE_BOUND\<close> is the local post-fixpoint bound;
  \<open>ENTER_MONO\<close> reads the routing context from the local slot (Goblint \<open>Spec.context\<close>);
  \<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> are the seed obligations (Goblint \<open>Spec.enter\<close>); \<open>COMB\<close> is the
  procedure-return combine (Goblint \<open>Spec.combine\<close>).  All reads are the local slot.
\<close>

theorem clean_ctx_trace_rread:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
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
  Set-level context-sliced soundness: every store reaching \<open>v\<close> along a trace whose
  digest is \<open>cmp\<close>-compatible with \<open>ctx\<close> lies in the concretisation of the
  \<^emph>\<open>local\<close> slot at \<open>(v, ctx)\<close> --- the R_read analogue of \<^const>\<open>cfg_collect_ctx\<close>.
\<close>

theorem clean_ctx_collect_rread:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
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

subsection \<open>Executable reduction: discharging the digest-propagation obligations\<close>

text \<open>
  For any \<^emph>\<open>head\<close> digest --- reading only the head store of the current activation,
  \<^const>\<open>head_digest\<close> --- the three digest-propagation obligations (\<open>DG_INTRA\<close> /
  \<open>DG_RETURN\<close> / \<open>DG_CALLEE\<close>) are discharged generically.  What remains is the
  run-specific bundle: the seed soundness (\<open>ENTRY\<close> / \<open>PROC_ENTRY\<close>, Goblint
  \<open>Spec.enter\<close>), the local post-fixpoint bounds (\<open>EDGE_BOUND\<close> / \<open>COMB\<close>, Goblint
  \<open>Spec.combine\<close>), and the value-digest routing (\<open>ENTER_MONO\<close>, Goblint
  \<open>Spec.context\<close>).  No \<open>'c :: finite\<close> is needed: the conclusion is the local slot.
\<close>

theorem clean_ctx_collect_rread_head:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and f :: "store \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (head_digest f [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (head_digest f [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
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
  show "\<And>ctx u a v. (u, a, v) \<in> edges g \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
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

end

end
