theory Sign_Local_Effects
  imports Sign_Transfer Voblint_Core.TD_Side_CFG
begin

section \<open>Sign local-effectful invariants\<close>

subsection \<open>Local-effectful tree invariants\<close>

text \<open>
  When @{const local_edge_action} holds, Sign edge transfers are compatible with
  @{const local_edge_tree}: assign/assume preserve globals and depend only on local
  slots of the source unknown.  Nop uses the identity and satisfies
  @{const local_edge_invariant} only.
\<close>

lemma aval_sign_restrict_su:
  assumes ng: "\<not> aexp_mentions_global a"
  shows "aval_sign a (su \<squnion> g) = aval_sign a ((restrict_local su) \<squnion> g)"
  using ng
proof (induction a)
  case (N n)
  then show ?case by simp
next
  case (V x)
  then show ?case
    by (cases "is_global x") (auto simp: restrict_local_def sup_fun_def)
next
  case (Plus a b)
  then show ?case by (simp add: sup_fun_def)
next
  case (Minus a b)
  then show ?case by (simp add: sup_fun_def)
next
  case (Times a b)
  then show ?case by (simp add: sup_fun_def)
qed

lemma aval_sign_restrict_local_bot:
  assumes ng: "\<not> aexp_mentions_global a"
    and lb: "local_bot_on_locals g"
  shows "aval_sign a ((restrict_local su) \<squnion> g) = aval_sign a (restrict_local su)"
  using ng lb
proof (induction a)
  case (N n)
  then show ?case by simp
next
  case (V x)
  then show ?case
    unfolding local_bot_on_locals_def restrict_local_def sup_fun_def
    by (auto split: if_split_asm)
next
  case (Plus a b)
  then show ?case by (simp add: sup_fun_def)
next
  case (Minus a b)
  then show ?case by (simp add: sup_fun_def)
next
  case (Times a b)
  then show ?case by (simp add: sup_fun_def)
qed

lemma assign_sign_local_edge_invariant:
  assumes gl: "\<not> is_global x" and ng: "\<not> aexp_mentions_global e"
  shows "local_edge_invariant (assign_sign x e)"
  unfolding local_edge_invariant_def assign_sign_def
proof (intro allI impI)
  fix su :: "sign abs_state"
  fix g :: "sign abs_state"
  assume lb: "local_bot_on_locals g"
  show "(restrict_local su \<squnion> g)(x := aval_sign e (restrict_local su \<squnion> g)) =
        restrict_local ((restrict_local su)(x := aval_sign e (restrict_local su))) \<squnion> g"
  proof (rule ext)
    fix y
    show "((restrict_local su \<squnion> g)(x := aval_sign e (restrict_local su \<squnion> g))) y =
          (restrict_local ((restrict_local su)(x := aval_sign e (restrict_local su))) \<squnion> g) y"
    proof (cases "y = x")
      case True
      then show ?thesis
        using gl lb aval_sign_restrict_local_bot[OF ng lb, of su]
        unfolding restrict_local_def local_bot_on_locals_def sup_fun_def by simp
    next
      case False
      then show ?thesis
        using lb unfolding restrict_local_def local_bot_on_locals_def sup_fun_def by auto
    qed
  qed
qed

lemma assign_sign_le_etf_collecting_full_local:
  assumes gl: "\<not> is_global x" and ng: "\<not> aexp_mentions_global e"
    and inr: "\<And>g. local_bot_on_locals (\<sigma> (Inr g))"
  shows "assign_sign x e (side_env \<sigma> u) \<le>
         etf_collecting_full (local_edge_tree (assign_sign x e) u) \<sigma>"
proof -
  have gb: "local_bot_on_locals (glob_env \<sigma>)"
    using inr by (rule glob_env_local_bot)
  have eq: "assign_sign x e (side_env \<sigma> u) =
      restrict_local (assign_sign x e (restrict_local (\<sigma> (Inl u)))) \<squnion>
      restrict_global (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>"
  proof (rule ext)
    fix y
    show "(assign_sign x e (side_env \<sigma> u)) y =
          ((restrict_local (assign_sign x e (restrict_local (\<sigma> (Inl u)))) \<squnion>
            restrict_global (\<sigma> (Inl u)) \<squnion> glob_env \<sigma>) y)"
    proof (cases "y = x")
      case True
      have aval_eq: "aval_sign e (\<sigma> (Inl u) \<squnion> glob_env \<sigma>) =
          aval_sign e (restrict_local (\<sigma> (Inl u)))"
        using aval_sign_restrict_su[OF ng, of "\<sigma> (Inl u)" "glob_env \<sigma>"]
          aval_sign_restrict_local_bot[OF ng gb, of "\<sigma> (Inl u)"]
        by simp
      then show ?thesis
        using True gl gb
        unfolding assign_sign_def side_env_def restrict_local_def restrict_global_def
          local_bot_on_locals_def sup_fun_def
        by simp
    next
      case False
      then show ?thesis
        using gb
        unfolding assign_sign_def side_env_def restrict_local_def restrict_global_def
          local_bot_on_locals_def sup_fun_def
        by auto
    qed
  qed
  show ?thesis
    unfolding etf_collecting_full_local_edge_tree eq by simp
qed

lemma afilter_sign_local_edge_invariant:
  assumes ng: "\<not> aexp_mentions_global e"
  shows "local_edge_invariant (\<lambda>\<sigma>. afilter_sign e a \<sigma>)"
  using ng
proof (induction e arbitrary: a)
  case (N n)
  then show ?case
    unfolding local_edge_invariant_def restrict_local_def local_bot_on_locals_def sup_fun_def
    by auto
next
  case (V x)
  then show ?case
    unfolding local_edge_invariant_def sign_backward_domain.afilter.simps
      restrict_local_def local_bot_on_locals_def sup_fun_def
    by (auto split: if_split_asm)
next
  case (Plus e1 e2)
  then have ng1: "\<not> aexp_mentions_global e1" and ng2: "\<not> aexp_mentions_global e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals g"
    let ?suL = "restrict_local su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    have inv2: "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> g) =
        restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g"
      using local_edge_invariantD[OF Plus.IH(2)[OF ng2, of "aval_sign e2 ?suL"] lb] .
    have s2_local: "restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) =
        afilter_sign e2 (aval_sign e2 ?suL) ?suL"
    proof -
      have "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> bot) =
          restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> bot"
        using Plus.IH(2)[OF ng2, of "aval_sign e2 ?suL"]
        unfolding local_edge_invariant_def local_bot_on_locals_def
        by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
      then show ?thesis by simp
    qed
    have inv1: "afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g) =
        restrict_local (afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF Plus.IH(1)[OF ng1] lb] .
    show "afilter_sign (Plus e1 e2) a (?suL \<squnion> g) =
          restrict_local (afilter_sign (Plus e1 e2) a ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local
      by (simp add: Let_def case_prod_beta inv_conservative_def)
  qed
next
  case (Minus e1 e2)
  then have ng1: "\<not> aexp_mentions_global e1" and ng2: "\<not> aexp_mentions_global e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals g"
    let ?suL = "restrict_local su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    have inv2: "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> g) =
        restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g"
      using local_edge_invariantD[OF Minus.IH(2)[OF ng2] lb] .
    have s2_local: "restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) =
        afilter_sign e2 (aval_sign e2 ?suL) ?suL"
    proof -
      have "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> bot) =
          restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> bot"
        using Minus.IH(2)[OF ng2, of "aval_sign e2 ?suL"]
        unfolding local_edge_invariant_def local_bot_on_locals_def
        by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
      then show ?thesis by simp
    qed
    have inv1: "afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g) =
        restrict_local (afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF Minus.IH(1)[OF ng1] lb] .
    show "afilter_sign (Minus e1 e2) a (?suL \<squnion> g) =
          restrict_local (afilter_sign (Minus e1 e2) a ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local by (simp add: inv_conservative_def)
  qed
next
  case (Times e1 e2)
  then have ng1: "\<not> aexp_mentions_global e1" and ng2: "\<not> aexp_mentions_global e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals g"
    let ?suL = "restrict_local su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    have inv2: "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> g) =
        restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g"
      using local_edge_invariantD[OF Times.IH(2)[OF ng2] lb] .
    have s2_local: "restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) =
        afilter_sign e2 (aval_sign e2 ?suL) ?suL"
    proof -
      have "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> bot) =
          restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> bot"
        using Times.IH(2)[OF ng2, of "aval_sign e2 ?suL"]
        unfolding local_edge_invariant_def local_bot_on_locals_def
        by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
      then show ?thesis by simp
    qed
    have inv1: "afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g) =
        restrict_local (afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local (afilter_sign e2 (aval_sign e2 ?suL) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF Times.IH(1)[OF ng1] lb] .
    show "afilter_sign (Times e1 e2) a (?suL \<squnion> g) =
          restrict_local (afilter_sign (Times e1 e2) a ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local
      by (simp add: Let_def case_prod_beta inv_conservative_def)
  qed
qed

lemma bfilter_sign_local_edge_invariant:
  assumes ng: "\<not> bexp_mentions_global b"
  shows "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b res \<sigma>)"
  using ng
proof (induction b arbitrary: res)
  case (Bc b)
  show ?case
    by (simp add: id_local_edge_invariant)
next
  case (Not b)
  then show ?case
    by (simp add: sign_backward_domain.bfilter.simps)
next
  case (And b1 b2)
  then have ng1: "\<not> bexp_mentions_global b1" and ng2: "\<not> bexp_mentions_global b2"
    by auto
  show ?case
  proof (cases res)
    case True
    have inv2: "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b2 True \<sigma>)"
      using And.IH(2)[OF ng2, of True] .
    have inv1: "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b1 True \<sigma>)"
      using And.IH(1)[OF ng1, of True] .
    show ?thesis
      using True local_edge_invariant_comp[OF inv1 inv2]
      by (simp add: sign_backward_domain.bfilter.simps)
  next
    case False
    have inv1: "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b1 False \<sigma>)"
      using And.IH(1)[OF ng1, of False] .
    have inv2: "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b2 False \<sigma>)"
      using And.IH(2)[OF ng2, of False] .
    have inv: "local_edge_invariant (\<lambda>su. bfilter_sign b1 False su \<squnion> bfilter_sign b2 False su)"
      by (rule local_edge_invariant_sup[OF inv1 inv2])
    show ?thesis
      using False inv
      unfolding local_edge_invariant_def
      by (simp add: sign_backward_domain.bfilter.simps fun_eq_iff)
  qed
next
  case (Or b1 b2)
  then have ng1: "\<not> bexp_mentions_global b1" and ng2: "\<not> bexp_mentions_global b2"
    by auto
  show ?case
  proof (cases res)
    case True
    have inv1: "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b1 True \<sigma>)"
      using Or.IH(1)[OF ng1, of True] .
    have inv2: "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b2 True \<sigma>)"
      using Or.IH(2)[OF ng2, of True] .
    have inv: "local_edge_invariant (\<lambda>su. bfilter_sign b1 True su \<squnion> bfilter_sign b2 True su)"
      by (rule local_edge_invariant_sup[OF inv1 inv2])
    show ?thesis
      using True inv
      unfolding local_edge_invariant_def
      by (simp add: sign_backward_domain.bfilter.simps fun_eq_iff)
  next
    case False
    have inv2: "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b2 False \<sigma>)"
      using Or.IH(2)[OF ng2, of False] .
    have inv1: "local_edge_invariant (\<lambda>\<sigma>. bfilter_sign b1 False \<sigma>)"
      using Or.IH(1)[OF ng1, of False] .
    show ?thesis
      using False local_edge_invariant_comp[OF inv1 inv2]
      by (simp add: sign_backward_domain.bfilter.simps)
  qed
next
  case (Less e1 e2)
  then have ng1: "\<not> aexp_mentions_global e1" and ng2: "\<not> aexp_mentions_global e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals g"
    let ?suL = "restrict_local su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    define p where "p = inv_less_sign res (aval_sign e1 ?suL) (aval_sign e2 ?suL)"
    have inv2: "afilter_sign e2 (snd p) (?suL \<squnion> g) =
        restrict_local (afilter_sign e2 (snd p) ?suL) \<squnion> g"
      using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng2, of "snd p"] lb] .
    have s2_local: "restrict_local (afilter_sign e2 (snd p) ?suL) = afilter_sign e2 (snd p) ?suL"
      using local_edge_invariant_local_result[OF afilter_sign_local_edge_invariant[OF ng2, of "snd p"], of su] .
    have inv1: "afilter_sign e1 (fst p)
          (restrict_local (afilter_sign e2 (snd p) ?suL) \<squnion> g) =
        restrict_local (afilter_sign e1 (fst p)
          (restrict_local (afilter_sign e2 (snd p) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng1, of "fst p"] lb] .
    show "bfilter_sign (Less e1 e2) res (?suL \<squnion> g) =
          restrict_local (bfilter_sign (Less e1 e2) res ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local
      unfolding p_def
      by (simp add: Let_def case_prod_beta)
  qed
next
  case (Eq e1 e2)
  then have ng1: "\<not> aexp_mentions_global e1" and ng2: "\<not> aexp_mentions_global e2"
    by auto
  show ?case
  proof (cases res)
    case False
    then show ?thesis
      by (simp add: id_local_edge_invariant)
  next
    case True
    show ?thesis
      using True
      unfolding local_edge_invariant_def
    proof (intro allI impI)
      fix su :: "sign abs_state"
      fix g :: "sign abs_state"
      assume lb: "local_bot_on_locals g"
      let ?suL = "restrict_local su"
      have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
        using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
      have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
        using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
      define a where "a = meet_sign (aval_sign e1 ?suL) (aval_sign e2 ?suL)"
      have inv2: "afilter_sign e2 a (?suL \<squnion> g) =
          restrict_local (afilter_sign e2 a ?suL) \<squnion> g"
        using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng2, of a] lb] .
      have s2_local: "restrict_local (afilter_sign e2 a ?suL) = afilter_sign e2 a ?suL"
        using local_edge_invariant_local_result[OF afilter_sign_local_edge_invariant[OF ng2, of a], of su] .
      have inv1: "afilter_sign e1 a
            (restrict_local (afilter_sign e2 a ?suL) \<squnion> g) =
          restrict_local (afilter_sign e1 a
            (restrict_local (afilter_sign e2 a ?suL))) \<squnion> g"
        using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng1, of a] lb] .
      show "bfilter_sign (Eq e1 e2) res (?suL \<squnion> g) =
            restrict_local (bfilter_sign (Eq e1 e2) res ?suL) \<squnion> g"
        using True av1 av2 inv2 inv1 s2_local
        unfolding a_def
        by (simp add: Let_def)
    qed
  qed
qed

lemma assume_sign_local_edge_invariant:
  assumes ng: "\<not> bexp_mentions_global b"
  shows "local_edge_invariant (assume_sign b)"
  unfolding assume_sign_def using bfilter_sign_local_edge_invariant[OF ng] by simp

lemma assume_not_sign_local_edge_invariant:
  assumes ng: "\<not> bexp_mentions_global b"
  shows "local_edge_invariant (assume_not_sign b)"
  unfolding assume_not_sign_def using bfilter_sign_local_edge_invariant[OF ng] by simp

lemma sign_tf_local_edge_invariant:
  assumes loc: "local_edge_action a"
  shows "local_edge_invariant (apply_tf sign_tf a)"
  using loc
proof (cases a)
  case EA_Nop
  then show ?thesis
    unfolding \<open>a = EA_Nop\<close> apply_tf.simps
    by (auto intro: id_local_edge_invariant)
next
  case (EA_Assign x e)
  from loc \<open>a = EA_Assign x e\<close> have gl: "\<not> is_global x"
    by (simp add: local_edge_action.simps)
  from loc \<open>a = EA_Assign x e\<close> have ng: "\<not> aexp_mentions_global e"
    by (simp add: local_edge_action.simps)
  then show ?thesis
    using assign_sign_local_edge_invariant[OF gl ng]
    unfolding \<open>a = EA_Assign x e\<close> apply_tf.simps sign_tf_def by simp
next
  case (EA_Assume b)
  from loc \<open>a = EA_Assume b\<close> have ng: "\<not> bexp_mentions_global b"
    by (simp add: local_edge_action.simps)
  then show ?thesis
    unfolding \<open>a = EA_Assume b\<close> apply_tf.simps
    by (simp add: sign_tf_def; rule assume_sign_local_edge_invariant)
next
  case (EA_AssumeNot b)
  from loc \<open>a = EA_AssumeNot b\<close> have ng: "\<not> bexp_mentions_global b"
    by (simp add: local_edge_action.simps)
  then show ?thesis
    unfolding \<open>a = EA_AssumeNot b\<close> apply_tf.simps
    by (simp add: sign_tf_def; rule assume_not_sign_local_edge_invariant)
next
  case (EA_Ret e p)
  show ?thesis
  proof (cases e)
    case None
    then show ?thesis
      unfolding EA_Ret apply_tf.simps by (auto intro: id_local_edge_invariant)
  next
    case (Some e)
    have gl: "\<not> is_global ret_var"
      using loc unfolding EA_Ret Some by simp
    have ng: "\<not> aexp_mentions_global e"
      using loc unfolding EA_Ret Some by simp
    show ?thesis
      unfolding EA_Ret Some apply_tf.simps sign_tf_def
      by (simp add: sign_tf_def; rule assign_sign_local_edge_invariant[OF gl ng])
  qed
qed

end
