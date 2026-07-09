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

text \<open>
  \<^bold>\<open>What is certified.\<close>  The clean (Goblint-sequential) transfer, which reads only
  the local slot, is \<^emph>\<open>sound\<close> when soundness is measured against the local read:
  the five per-edge obligations (\<open>clean_rread_*\<close>) hold unconditionally, and the
  flat collecting theorem \<open>clean_cfg_collect_rread\<close> lifts them --- under the natural
  local post-fixpoint bounds --- to \<^const>\<open>cfg_collect\<close>.  This is the read split the
  \<open>Exec_Sign_Cmp_Keyed_Retain_EnterMono\<close> obstruction identified as the fix: the
  soundness conclusion is stated over R_read (\<open>sg (Inl v)\<close>), decoupled from the
  coarse published global that dominated the Obs read.  The retain (\<open>\<squnion> g\<close>) spine
  remains the sound baseline for the Obs conclusion.

  \<^bold>\<open>Remaining obligation.\<close>  Lifting this to the context-sliced \<^const>\<open>cfg_collect_ctx\<close>
  --- and connecting it to the executable seeded run through the \<open>_st\<close> and keyed
  bridges --- is the next slice.  The entry seed bound \<open>entry_le\<close> is exactly what the
  Goblint-faithful seed \<open>side_cfg_T_eff_cmp_seed_st\<close> with \<^const>\<open>restrict_global_st\<close>
  establishes per context (\<open>seed_clean_sound_on_prog2\<close>).
\<close>

end
