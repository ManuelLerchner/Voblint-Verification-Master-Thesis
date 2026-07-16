theory Clean_RRead_Sound
  imports TD_Side_Eff_Cmp_Sound "Voblint_Analysis.Local_DG"
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
     etf_enter = (\<lambda>xs es. clean_edge_tree (apply_tf tf (EA_Enter xs es))),
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
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
      \<in> \<lbrakk>etf_collecting_full (etf_enter (clean_etf_of_transfer tf) xs es u) sg\<rbrakk>"
proof -
  have base: "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s)
      \<in> \<lbrakk>tf_enter tf xs es (sg (Inl u))\<rbrakk>"
    using tf_sound_enter assms by blast
  have "tf_enter tf xs es (sg (Inl u))
      \<le> etf_collecting_full (etf_enter (clean_etf_of_transfer tf) xs es u) sg"
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
    and combine_le: "\<And>c ex ret dst s t. (c, ex, ret, dst) \<in> combines g
      \<Longrightarrow> s \<in> \<lbrakk>sg (Inl c)\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl ex)\<rbrakk> \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl ret)\<rbrakk>"
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
    case (combine c ex v dst S s t u)
    have "s \<in> \<lbrakk>sg (Inl c)\<rbrakk>" using combine.IH(1) combine.prems by blast
    moreover have "t \<in> \<lbrakk>sg (Inl ex)\<rbrakk>" using combine.IH(2) combine.prems by blast
    ultimately have "combine_collect dst s t \<in> \<lbrakk>sg (Inl v)\<rbrakk>"
      by (rule combine_le[OF combine.hyps(1)])
    thus ?case using combine.hyps(4) by simp
  qed
qed

theorem clean_cfg_collect_rread:
  assumes step_le: "\<And>u a w. (u, a, w) \<in> edges g
      \<Longrightarrow> etf_full (apply_etf (clean_etf_of_transfer tf) a u) sg \<le> sg (Inl w)"
    and combine_le: "\<And>c ex ret dst s t. (c, ex, ret, dst) \<in> combines g
      \<Longrightarrow> s \<in> \<lbrakk>sg (Inl c)\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl ex)\<rbrakk> \<Longrightarrow> combine_collect dst s t \<in> \<lbrakk>sg (Inl ret)\<rbrakk>"
    and entry_le: "S \<subseteq> \<lbrakk>sg (Inl (cfg_entry g))\<rbrakk>"
  shows "cfg_collect g S v \<subseteq> \<lbrakk>sg (Inl v)\<rbrakk>"
proof
  fix st assume a: "st \<in> cfg_collect g S v"
  have w: "cfg_witness g S v st"
    using a by (simp add: cfg_collect_eq_paths cfg_collect_paths_def)
  show "st \<in> \<lbrakk>sg (Inl v)\<rbrakk>"
    by (rule clean_cfg_witness_rread[OF step_le combine_le entry_le w])
qed

subsection \<open>Discharging the return combine from an abstract bound\<close>

text \<open>
  \<open>combine_abs_bound_sound\<close> (in \<^theory>\<open>Voblint_Analysis.Constraint_System\<close>)
  reduces the raw \<open>combine_le\<close> / \<open>COMB\<close> premise (the concrete return combine
  \<open><s|t> \<in> \<lbrakk>sg (Inl ret)\<rbrakk>\<close>) to an abstract bound
  \<open>combine_collect_abs dst sc se \<le> sr\<close> on the reassembled continuation.  On the
  rehydrating combine (\<^const>\<open>combine_abs\<close> at the return slot) that bound holds by
  construction, so no \<open><s|t>\<close> obligation is exposed to the caller.
\<close>


text \<open>
  Flat collecting soundness with the return combine as an abstract bound
  \<open>combine_bound\<close> instead of the raw semantic \<open>combine_le\<close>: no \<open><s|t>\<close> obligation is
  exposed to the caller.  The bound \<open>\<langle>sg (Inl c)|sg (Inl ex)\<rangle> \<le> sg (Inl ret)\<close> is the
  same order-theoretic shape as \<open>step_le\<close>, checkable against a post-solution.
\<close>

theorem clean_cfg_collect_rread_bound:
  assumes step_le: "\<And>u a w. (u, a, w) \<in> edges g
      \<Longrightarrow> etf_full (apply_etf (clean_etf_of_transfer tf) a u) sg \<le> sg (Inl w)"
    and combine_bound: "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g
      \<Longrightarrow> combine_collect_abs dst (sg (Inl c)) (sg (Inl ex)) \<le> sg (Inl ret)"
    and entry_le: "S \<subseteq> \<lbrakk>sg (Inl (cfg_entry g))\<rbrakk>"
  shows "cfg_collect g S v \<subseteq> \<lbrakk>sg (Inl v)\<rbrakk>"
proof (rule clean_cfg_collect_rread[OF step_le _ entry_le])
  fix c ex ret dst s t
  assume "(c, ex, ret, dst) \<in> combines g" and "s \<in> \<lbrakk>sg (Inl c)\<rbrakk>" and "t \<in> \<lbrakk>sg (Inl ex)\<rbrakk>"
  have bound: "combine_collect_abs dst (sg (Inl c)) (sg (Inl ex)) \<le> sg (Inl ret)"
    by (rule combine_bound[OF \<open>(c, ex, ret, dst) \<in> combines g\<close>])
  show "combine_collect dst s t \<in> \<lbrakk>sg (Inl ret)\<rbrakk>"
    using \<open>s \<in> \<lbrakk>sg (Inl c)\<rbrakk>\<close> \<open>t \<in> \<lbrakk>sg (Inl ex)\<rbrakk>\<close>
    by (rule combine_abs_bound_sound[OF bound])
qed

subsection \<open>Context-sliced collecting soundness over the local read\<close>

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
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB: "\<And>ctx cl ex v dst tau rho. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> combine_collect dst (last tau) (last rho) \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho dst. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
    and DG_CALLEE: "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sg (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  \<comment> \<open>The clean single-domain context theorem is a corollary of the DG endpoint at the
      local-only adapter instance (\<open>Local_DG\<close>): same premises, same conclusion, with the
      trivial Side component discharged once inside the adapter.\<close>
  using assms by (rule clean_ctx_collect_rread_via_dg)

text \<open>
  Context-sliced collecting soundness with the return combine as an abstract bound
  \<open>COMB_BOUND\<close> instead of the raw semantic \<open>COMB\<close>.  The bound is on the reassembled
  caller continuation \<^term>\<open>\<langle>sg (Inl (cl, ctx))|sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rangle>\<close>
  --- caller local at \<open>ctx\<close>, callee exit under the value-derived context --- which
  the rehydrating combine (\<^const>\<open>combine_abs\<close> at the return slot) meets by
  construction and the strip combine cannot once a returned global is read back.
\<close>

theorem clean_ctx_collect_rread_bound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB_BOUND: "\<And>ctx cl ex v dst. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> combine_collect_abs dst (sg (Inl (cl, ctx))) (sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))) \<le> sg (Inl (v, ctx))"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho dst. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = dg tau"
    and DG_CALLEE: "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sg (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule clean_ctx_collect_rread
      [where sg = sg and rt = rt and dg = dg and cmp = cmp and entdg = entdg and g = g and S = S,
       OF ENTRY PROC_ENTRY EDGE_BOUND _ DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO])
  fix ctx cl ex v dst tau rho
  assume c: "(cl, ex, v, dst) \<in> combines g"
    and ct: "last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>"
    and ce: "last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>"
  show "combine_collect dst (last tau) (last rho) \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule combine_abs_bound_sound[OF COMB_BOUND[OF c] ct ce])
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
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (head_digest f [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB: "\<And>ctx cl ex v dst tau rho. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> combine_collect dst (last tau) (last rho) \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and WF_ENTER: "\<And>u xs es w. (u, EA_Enter xs es, w) \<in> edges g \<Longrightarrow> local_formals xs"
    and FINV: "\<And>st x v. \<not> is_global x \<Longrightarrow> f (st(x := v)) = f st"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (f (enter_state s)) (rt cl ctx (sg (Inl (cl, ctx))))"
  shows "cfg_collect_ctx (head_digest f) cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule clean_ctx_collect_rread
      [where dg = "head_digest f" and entdg = "\<lambda>s. f (enter_state s)" and rt = rt
         and sg = sg and cmp = cmp and g = g and S = S])
  show "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (head_digest f [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    by (rule ENTRY)
next
  show "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (head_digest f [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule PROC_ENTRY)
next
  show "\<And>ctx u a v. (u, a, v) \<in> edges g \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    by (rule EDGE_BOUND)
next
  show "\<And>ctx cl ex v dst tau rho. (cl, ex, v, dst) \<in> combines g \<Longrightarrow> last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>
        \<Longrightarrow> combine_collect dst (last tau) (last rho) \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule COMB)
next
  show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (head_digest f (tr @ [s'])) ctx \<Longrightarrow> cmp (head_digest f tr) ctx"
    by (rule head_digest_DG_INTRA)
next
  show "\<And>tau rho dst. tau \<noteq> [] \<Longrightarrow> head_digest f (tau @ tl rho @ [combine_collect dst (last tau) (last rho)]) = head_digest f tau"
    by (rule head_digest_DG_RETURN)
next
  show "\<And>cl tau rho. rho \<noteq> [] \<Longrightarrow> call_enter_store g cl (last tau) (hd rho) \<Longrightarrow> head_digest f rho = f (enter_state (last tau))"
    by (rule head_digest_DG_CALLEE[OF _ _ WF_ENTER FINV, unfolded o_def])
next
  show "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk> \<Longrightarrow> cmp (f (enter_state s)) (rt cl ctx (sg (Inl (cl, ctx))))"
    by (rule ENTER_MONO)
qed

text \<open>
  The executable head-digest reduction with the return combine as an abstract bound.
  Combines the generic digest-propagation discharge with \<open>COMB_BOUND\<close>: the only
  return obligation is now the order-theoretic \<open>combine_abs\<close> bound, checkable against
  a post-solution --- no raw \<open><s|t>\<close> assumption survives.  This is the fully reduced
  clean+rehydrate return contract, the R_read analogue of the keyed
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>.
\<close>

theorem clean_ctx_collect_rread_head_bound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and f :: "store \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (head_digest f [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cfg_entry g, ctx))\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s xs es. (cfg_entry g, EA_Enter xs es, v) \<in> edges g
        \<Longrightarrow> s \<in> edge_collect (EA_Enter xs es) S
        \<Longrightarrow> cmp (head_digest f [s]) ctx \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    and EDGE_BOUND: "\<And>ctx u a v. (u, a, v) \<in> edges g
        \<Longrightarrow> apply_tf tf a (sg (Inl (u, ctx))) \<le> sg (Inl (v, ctx))"
    and COMB_BOUND: "\<And>ctx cl ex v dst. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> combine_collect_abs dst (sg (Inl (cl, ctx))) (sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))) \<le> sg (Inl (v, ctx))"
    and WF_ENTER: "\<And>u xs es w. (u, EA_Enter xs es, w) \<in> edges g \<Longrightarrow> local_formals xs"
    and FINV: "\<And>st x v. \<not> is_global x \<Longrightarrow> f (st(x := v)) = f st"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>
        \<Longrightarrow> cmp (f (enter_state s)) (rt cl ctx (sg (Inl (cl, ctx))))"
  shows "cfg_collect_ctx (head_digest f) cmp g S v ctx \<subseteq> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
proof (rule clean_ctx_collect_rread_head
      [where sg = sg and f = f and rt = rt and cmp = cmp and g = g and S = S,
       OF ENTRY PROC_ENTRY EDGE_BOUND _ WF_ENTER FINV ENTER_MONO])
  fix ctx cl ex v dst tau rho
  assume c: "(cl, ex, v, dst) \<in> combines g"
    and ct: "last tau \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>"
    and ce: "last rho \<in> \<lbrakk>sg (Inl (ex, rt cl ctx (sg (Inl (cl, ctx)))))\<rbrakk>"
  show "combine_collect dst (last tau) (last rho) \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
    by (rule combine_abs_bound_sound[OF COMB_BOUND[OF c] ct ce])
qed

end

end
