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
  assumes ng: "\<not> exp_mentions_global gs a"
  shows "aval_sign a (su \<squnion> g) = aval_sign a ((restrict_local_for gs su) \<squnion> g)"
  using ng
proof (induction a)
  case (N n)
  then show ?case by simp
next
  case (V x)
  then show ?case
    by (cases "gs x") (auto simp: restrict_local_for_def sup_fun_def)
next
  case (Plus a b)
  then show ?case by (simp add: sup_fun_def)
next
  case (Minus a b)
  then show ?case by (simp add: sup_fun_def)
next
  case (Times a b)
  then show ?case by (simp add: sup_fun_def)
next
  case (Less a b)
  then show ?case by simp
next
  case (Eq a b)
  then show ?case by simp
next
  case (Not a)
  then show ?case by simp
next
  case (And a b)
  then show ?case by simp
next
  case (Or a b)
  then show ?case by simp
qed

lemma aval_sign_restrict_local_bot:
  assumes ng: "\<not> exp_mentions_global gs a"
    and lb: "local_bot_on_locals gs g"
  shows "aval_sign a ((restrict_local_for gs su) \<squnion> g) = aval_sign a (restrict_local_for gs su)"
  using ng lb
proof (induction a)
  case (N n)
  then show ?case by simp
next
  case (V x)
  then show ?case
    unfolding local_bot_on_locals_def restrict_local_for_def sup_fun_def
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
next
  case (Less a b)
  then show ?case by simp
next
  case (Eq a b)
  then show ?case by simp
next
  case (Not a)
  then show ?case by simp
next
  case (And a b)
  then show ?case by simp
next
  case (Or a b)
  then show ?case by simp
qed

lemma assign_sign_local_edge_invariant [intro]:
  assumes gl: "\<not> gs x" and ng: "\<not> exp_mentions_global gs e"
  shows "local_edge_invariant gs (assign_sign x e)"
  unfolding local_edge_invariant_def assign_sign_def
proof (intro allI impI)
  fix su :: "sign abs_state"
  fix g :: "sign abs_state"
  assume lb: "local_bot_on_locals gs g"
  show "(restrict_local_for gs su \<squnion> g)(x := aval_sign e (restrict_local_for gs su \<squnion> g)) =
        restrict_local_for gs ((restrict_local_for gs su)(x := aval_sign e (restrict_local_for gs su))) \<squnion> g"
  proof (rule ext)
    fix y
    show "((restrict_local_for gs su \<squnion> g)(x := aval_sign e (restrict_local_for gs su \<squnion> g))) y =
          (restrict_local_for gs ((restrict_local_for gs su)(x := aval_sign e (restrict_local_for gs su))) \<squnion> g) y"
    proof (cases "y = x")
      case True
      then show ?thesis
        using gl lb aval_sign_restrict_local_bot[OF ng lb, of su]
        unfolding restrict_local_for_def local_bot_on_locals_def sup_fun_def by simp
    next
      case False
      then show ?thesis
        using lb unfolding restrict_local_for_def local_bot_on_locals_def sup_fun_def by auto
    qed
  qed
qed

lemma afilter_sign_local_edge_invariant:
  assumes ng: "\<not> exp_mentions_global gs e"
  shows "local_edge_invariant gs (\<lambda>\<sigma>. afilter_sign e a \<sigma>)"
  using ng
proof (induction e arbitrary: a)
  case (N n)
  then show ?case
    unfolding local_edge_invariant_def restrict_local_for_def local_bot_on_locals_def sup_fun_def
    by auto
next
  case (V x)
  then show ?case
    unfolding local_edge_invariant_def sign_backward_domain.afilter.simps
      restrict_local_for_def local_bot_on_locals_def sup_fun_def
    by (auto split: if_split_asm)
next
  case (Plus e1 e2)
  then have ng1: "\<not> exp_mentions_global gs e1" and ng2: "\<not> exp_mentions_global gs e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals gs g"
    let ?suL = "restrict_local_for gs su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    have inv2: "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> g) =
        restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g"
      using local_edge_invariantD[OF Plus.IH(2)[OF ng2, of "aval_sign e2 ?suL"] lb] .
    have s2_local: "restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) =
        afilter_sign e2 (aval_sign e2 ?suL) ?suL"
    proof -
      have "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> bot) =
          restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> bot"
        using Plus.IH(2)[OF ng2, of "aval_sign e2 ?suL"]
        unfolding local_edge_invariant_def local_bot_on_locals_def
        by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
      then show ?thesis by simp
    qed
    have inv1: "afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g) =
        restrict_local_for gs (afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF Plus.IH(1)[OF ng1] lb] .
    show "afilter_sign (Plus e1 e2) a (?suL \<squnion> g) =
          restrict_local_for gs (afilter_sign (Plus e1 e2) a ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local
      by (simp add: Let_def case_prod_beta inv_conservative_def)
  qed
next
  case (Minus e1 e2)
  then have ng1: "\<not> exp_mentions_global gs e1" and ng2: "\<not> exp_mentions_global gs e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals gs g"
    let ?suL = "restrict_local_for gs su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    have inv2: "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> g) =
        restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g"
      using local_edge_invariantD[OF Minus.IH(2)[OF ng2] lb] .
    have s2_local: "restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) =
        afilter_sign e2 (aval_sign e2 ?suL) ?suL"
    proof -
      have "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> bot) =
          restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> bot"
        using Minus.IH(2)[OF ng2, of "aval_sign e2 ?suL"]
        unfolding local_edge_invariant_def local_bot_on_locals_def
        by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
      then show ?thesis by simp
    qed
    have inv1: "afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g) =
        restrict_local_for gs (afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF Minus.IH(1)[OF ng1] lb] .
    show "afilter_sign (Minus e1 e2) a (?suL \<squnion> g) =
          restrict_local_for gs (afilter_sign (Minus e1 e2) a ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local by (simp add: inv_conservative_def)
  qed
next
  case (Times e1 e2)
  then have ng1: "\<not> exp_mentions_global gs e1" and ng2: "\<not> exp_mentions_global gs e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals gs g"
    let ?suL = "restrict_local_for gs su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    have inv2: "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> g) =
        restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g"
      using local_edge_invariantD[OF Times.IH(2)[OF ng2] lb] .
    have s2_local: "restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) =
        afilter_sign e2 (aval_sign e2 ?suL) ?suL"
    proof -
      have "afilter_sign e2 (aval_sign e2 ?suL) (?suL \<squnion> bot) =
          restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> bot"
        using Times.IH(2)[OF ng2, of "aval_sign e2 ?suL"]
        unfolding local_edge_invariant_def local_bot_on_locals_def
        by (drule_tac x=su in spec, drule_tac x=bot in spec, simp)
      then show ?thesis by simp
    qed
    have inv1: "afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL) \<squnion> g) =
        restrict_local_for gs (afilter_sign e1 (aval_sign e1 ?suL)
          (restrict_local_for gs (afilter_sign e2 (aval_sign e2 ?suL) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF Times.IH(1)[OF ng1] lb] .
    show "afilter_sign (Times e1 e2) a (?suL \<squnion> g) =
          restrict_local_for gs (afilter_sign (Times e1 e2) a ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local
      by (simp add: Let_def case_prod_beta inv_conservative_def)
  qed
next
  case (Less e1 e2)
  then show ?case
    unfolding local_edge_invariant_def restrict_local_for_def local_bot_on_locals_def sup_fun_def
    by (auto simp: sign_backward_domain.afilter.simps)
next
  case (Eq e1 e2)
  then show ?case
    unfolding local_edge_invariant_def restrict_local_for_def local_bot_on_locals_def sup_fun_def
    by (auto simp: sign_backward_domain.afilter.simps)
next
  case (Not e)
  then show ?case
    unfolding local_edge_invariant_def restrict_local_for_def local_bot_on_locals_def sup_fun_def
    by (auto simp: sign_backward_domain.afilter.simps)
next
  case (And e1 e2)
  then show ?case
    unfolding local_edge_invariant_def restrict_local_for_def local_bot_on_locals_def sup_fun_def
    by (auto simp: sign_backward_domain.afilter.simps)
next
  case (Or e1 e2)
  then show ?case
    unfolding local_edge_invariant_def restrict_local_for_def local_bot_on_locals_def sup_fun_def
    by (auto simp: sign_backward_domain.afilter.simps)
qed

text \<open>
  \<open>N\<close>/\<open>V\<close>/\<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close> have no Boolean-shaped narrowing operator of
  their own, so \<open>bfilter\<close> falls back to the same \<open>inv_eq (\<not>res)\<close> against the
  abstract constant \<open>0\<close> for all five (see \<open>bfilter\<close>'s own comment in
  \<^theory>\<open>Voblint_Core.Abstract_Domain\<close>). Proved once here, generically in
  \<open>e\<close>, so the induction below cites it per arithmetic constructor instead of
  repeating the \<open>afilter_sign_local_edge_invariant\<close> chain five times.
\<close>
lemma bfilter_sign_default_local_edge_invariant:
  assumes ng: "\<not> exp_mentions_global gs e"
    and default_eq: "\<And>\<sigma>. bfilter_sign e res \<sigma> =
        (let (a1, a2) = inv_eq_sign (\<not> res) (aval_sign e \<sigma>) (aval_sign (N 0) \<sigma>) in afilter_sign e a1 \<sigma>)"
  shows "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign e res \<sigma>)"
  unfolding local_edge_invariant_def
proof (intro allI impI)
  fix su g :: "sign abs_state"
  assume lb: "local_bot_on_locals gs g"
  let ?suL = "restrict_local_for gs su"
  have av: "aval_sign e (?suL \<squnion> g) = aval_sign e ?suL"
    using aval_sign_restrict_local_bot[OF ng lb, of su] .
  define p where "p = inv_eq_sign (\<not> res) (aval_sign e ?suL) (aval_sign (N 0) ?suL)"
  have inv: "afilter_sign e (fst p) (?suL \<squnion> g) = restrict_local_for gs (afilter_sign e (fst p) ?suL) \<squnion> g"
    using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng, of "fst p"] lb] .
  show "bfilter_sign e res (?suL \<squnion> g) = restrict_local_for gs (bfilter_sign e res ?suL) \<squnion> g"
    using av inv unfolding default_eq p_def by (simp add: Let_def case_prod_beta)
qed

lemma bfilter_sign_local_edge_invariant:
  assumes ng: "\<not> exp_mentions_global gs b"
  shows "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b res \<sigma>)"
  using ng
proof (induction b arbitrary: res)
  case (N n)
  have eq: "\<And>\<sigma>. bfilter_sign (N n) res \<sigma> =
      (let (a1, a2) = inv_eq_sign (\<not> res) (aval_sign (N n) \<sigma>) (aval_sign (N 0) \<sigma>) in afilter_sign (N n) a1 \<sigma>)"
    by (simp add: sign_backward_domain.bfilter.simps)
  show ?case
    using bfilter_sign_default_local_edge_invariant[OF N.prems eq] .
next
  case (V x)
  have eq: "\<And>\<sigma>. bfilter_sign (V x) res \<sigma> =
      (let (a1, a2) = inv_eq_sign (\<not> res) (aval_sign (V x) \<sigma>) (aval_sign (N 0) \<sigma>) in afilter_sign (V x) a1 \<sigma>)"
    by (simp add: sign_backward_domain.bfilter.simps)
  show ?case
    using bfilter_sign_default_local_edge_invariant[OF V.prems eq] .
next
  case (Plus b1 b2)
  have eq: "\<And>\<sigma>. bfilter_sign (Plus b1 b2) res \<sigma> =
      (let (a1, a2) = inv_eq_sign (\<not> res) (aval_sign (Plus b1 b2) \<sigma>) (aval_sign (N 0) \<sigma>)
       in afilter_sign (Plus b1 b2) a1 \<sigma>)"
    by (simp add: sign_backward_domain.bfilter.simps)
  show ?case
    using bfilter_sign_default_local_edge_invariant[OF Plus.prems(1) eq] .
next
  case (Minus b1 b2)
  have eq: "\<And>\<sigma>. bfilter_sign (Minus b1 b2) res \<sigma> =
      (let (a1, a2) = inv_eq_sign (\<not> res) (aval_sign (Minus b1 b2) \<sigma>) (aval_sign (N 0) \<sigma>)
       in afilter_sign (Minus b1 b2) a1 \<sigma>)"
    by (simp add: sign_backward_domain.bfilter.simps)
  show ?case
    using bfilter_sign_default_local_edge_invariant[OF Minus.prems(1) eq] .
next
  case (Times b1 b2)
  have eq: "\<And>\<sigma>. bfilter_sign (Times b1 b2) res \<sigma> =
      (let (a1, a2) = inv_eq_sign (\<not> res) (aval_sign (Times b1 b2) \<sigma>) (aval_sign (N 0) \<sigma>)
       in afilter_sign (Times b1 b2) a1 \<sigma>)"
    by (simp add: sign_backward_domain.bfilter.simps)
  show ?case
    using bfilter_sign_default_local_edge_invariant[OF Times.prems(1) eq] .
next
  case (Not b)
  then show ?case
    by (simp add: sign_backward_domain.bfilter.simps)
next
  case (And b1 b2)
  then have ng1: "\<not> exp_mentions_global gs b1" and ng2: "\<not> exp_mentions_global gs b2"
    by auto
  show ?case
  proof (cases res)
    case True
    have inv2: "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b2 True \<sigma>)"
      using And.IH(2)[OF ng2, of True] .
    have inv1: "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b1 True \<sigma>)"
      using And.IH(1)[OF ng1, of True] .
    show ?thesis
      using True local_edge_invariant_comp[OF inv1 inv2]
      by (simp add: sign_backward_domain.bfilter.simps)
  next
    case False
    have inv1: "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b1 False \<sigma>)"
      using And.IH(1)[OF ng1, of False] .
    have inv2: "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b2 False \<sigma>)"
      using And.IH(2)[OF ng2, of False] .
    have inv: "local_edge_invariant gs (\<lambda>su. bfilter_sign b1 False su \<squnion> bfilter_sign b2 False su)"
      using And.IH(1,2) local_edge_invariant_sup ng1 ng2 by blast
    show ?thesis
      using False inv
      unfolding local_edge_invariant_def
      by (simp add: sign_backward_domain.bfilter.simps fun_eq_iff)
  qed
next
  case (Or b1 b2)
  then have ng1: "\<not> exp_mentions_global gs b1" and ng2: "\<not> exp_mentions_global gs b2"
    by auto
  show ?case
  proof (cases res)
    case True
    have inv1: "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b1 True \<sigma>)"
      using Or.IH(1)[OF ng1, of True] .
    have inv2: "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b2 True \<sigma>)"
      using Or.IH(2)[OF ng2, of True] .
    have inv: "local_edge_invariant gs (\<lambda>su. bfilter_sign b1 True su \<squnion> bfilter_sign b2 True su)"
      using Or.IH(1,2) local_edge_invariant_sup ng1 ng2 by blast
    show ?thesis
      using True inv
      unfolding local_edge_invariant_def
      by (simp add: sign_backward_domain.bfilter.simps fun_eq_iff)
  next
    case False
    have inv2: "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b2 False \<sigma>)"
      using Or.IH(2)[OF ng2, of False] .
    have inv1: "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b1 False \<sigma>)"
      using Or.IH(1)[OF ng1, of False] .
    show ?thesis
      using False local_edge_invariant_comp[OF inv1 inv2]
      by (simp add: sign_backward_domain.bfilter.simps)
  qed
next
  case (Less e1 e2)
  then have ng1: "\<not> exp_mentions_global gs e1" and ng2: "\<not> exp_mentions_global gs e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals gs g"
    let ?suL = "restrict_local_for gs su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    define p where "p = inv_less_sign res (aval_sign e1 ?suL) (aval_sign e2 ?suL)"
    have inv2: "afilter_sign e2 (snd p) (?suL \<squnion> g) =
        restrict_local_for gs (afilter_sign e2 (snd p) ?suL) \<squnion> g"
      using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng2, of "snd p"] lb] .
    have s2_local: "restrict_local_for gs (afilter_sign e2 (snd p) ?suL) = afilter_sign e2 (snd p) ?suL"
      using local_edge_invariant_local_result[OF afilter_sign_local_edge_invariant[OF ng2, of "snd p"], of su] .
    have inv1: "afilter_sign e1 (fst p)
          (restrict_local_for gs (afilter_sign e2 (snd p) ?suL) \<squnion> g) =
        restrict_local_for gs (afilter_sign e1 (fst p)
          (restrict_local_for gs (afilter_sign e2 (snd p) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng1, of "fst p"] lb] .
    show "bfilter_sign (Less e1 e2) res (?suL \<squnion> g) =
          restrict_local_for gs (bfilter_sign (Less e1 e2) res ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local
      unfolding p_def
      by (simp add: Let_def case_prod_beta)
  qed
next
  case (Eq e1 e2)
  then have ng1: "\<not> exp_mentions_global gs e1" and ng2: "\<not> exp_mentions_global gs e2"
    by auto
  show ?case
    unfolding local_edge_invariant_def
  proof (intro allI impI)
    fix su :: "sign abs_state"
    fix g :: "sign abs_state"
    assume lb: "local_bot_on_locals gs g"
    let ?suL = "restrict_local_for gs su"
    have av1: "aval_sign e1 (?suL \<squnion> g) = aval_sign e1 ?suL"
      using aval_sign_restrict_local_bot[OF ng1 lb, of su] .
    have av2: "aval_sign e2 (?suL \<squnion> g) = aval_sign e2 ?suL"
      using aval_sign_restrict_local_bot[OF ng2 lb, of su] .
    define p where "p = inv_eq_sign res (aval_sign e1 ?suL) (aval_sign e2 ?suL)"
    have inv2: "afilter_sign e2 (snd p) (?suL \<squnion> g) =
        restrict_local_for gs (afilter_sign e2 (snd p) ?suL) \<squnion> g"
      using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng2, of "snd p"] lb] .
    have s2_local: "restrict_local_for gs (afilter_sign e2 (snd p) ?suL) = afilter_sign e2 (snd p) ?suL"
      using local_edge_invariant_local_result[OF afilter_sign_local_edge_invariant[OF ng2, of "snd p"], of su] .
    have inv1: "afilter_sign e1 (fst p)
          (restrict_local_for gs (afilter_sign e2 (snd p) ?suL) \<squnion> g) =
        restrict_local_for gs (afilter_sign e1 (fst p)
          (restrict_local_for gs (afilter_sign e2 (snd p) ?suL))) \<squnion> g"
      using local_edge_invariantD[OF afilter_sign_local_edge_invariant[OF ng1, of "fst p"] lb] .
    show "bfilter_sign (Eq e1 e2) res (?suL \<squnion> g) =
          restrict_local_for gs (bfilter_sign (Eq e1 e2) res ?suL) \<squnion> g"
      using av1 av2 inv2 inv1 s2_local
      unfolding p_def
      by (simp add: Let_def case_prod_beta)
  qed
qed

lemma special_sign_local_edge_invariant [intro]:
  assumes gl: "\<not> gs x" and ng: "\<not> special_mentions_global gs sc"
  shows "local_edge_invariant gs (special_sign sc x)"
  unfolding local_edge_invariant_def
proof (intro allI impI)
  fix su :: "sign abs_state"
  fix g :: "sign abs_state"
  assume lb: "local_bot_on_locals gs g"
  show "special_sign sc x (restrict_local_for gs su \<squnion> g) =
        restrict_local_for gs (special_sign sc x (restrict_local_for gs su)) \<squnion> g"
  proof (cases sc)
    case Nondet_Int
    show ?thesis
      unfolding Nondet_Int special_sign.simps
    proof (rule ext)
      fix y
      show "((restrict_local_for gs su \<squnion> g)(x := STop)) y =
            (restrict_local_for gs ((restrict_local_for gs su)(x := STop)) \<squnion> g) y"
      proof (cases "y = x")
        case True
        then show ?thesis
          using gl lb
          unfolding restrict_local_for_def local_bot_on_locals_def sup_fun_def by simp
      next
        case False
        then show ?thesis
          using lb unfolding restrict_local_for_def local_bot_on_locals_def sup_fun_def by auto
      qed
    qed
  next
    case (Min a b)
    with ng have nga: "\<not> exp_mentions_global gs a" and ngb: "\<not> exp_mentions_global gs b"
      by simp_all
    show ?thesis
      unfolding Min special_sign.simps
    proof (rule ext)
      fix y
      show "((restrict_local_for gs su \<squnion> g)
              (x := sign_min (aval_sign a (restrict_local_for gs su \<squnion> g))
                              (aval_sign b (restrict_local_for gs su \<squnion> g)))) y =
            (restrict_local_for gs
              ((restrict_local_for gs su)
                (x := sign_min (aval_sign a (restrict_local_for gs su))
                                (aval_sign b (restrict_local_for gs su)))) \<squnion> g) y"
      proof (cases "y = x")
        case True
        then show ?thesis
          using gl lb aval_sign_restrict_local_bot[OF nga lb, of su]
                aval_sign_restrict_local_bot[OF ngb lb, of su]
          unfolding restrict_local_for_def local_bot_on_locals_def sup_fun_def by simp
      next
        case False
        then show ?thesis
          using lb unfolding restrict_local_for_def local_bot_on_locals_def sup_fun_def by auto
      qed
    qed
  next
    case (Max a b)
    with ng have nga: "\<not> exp_mentions_global gs a" and ngb: "\<not> exp_mentions_global gs b"
      by simp_all
    show ?thesis
      unfolding Max special_sign.simps
    proof (rule ext)
      fix y
      show "((restrict_local_for gs su \<squnion> g)
              (x := sign_max (aval_sign a (restrict_local_for gs su \<squnion> g))
                              (aval_sign b (restrict_local_for gs su \<squnion> g)))) y =
            (restrict_local_for gs
              ((restrict_local_for gs su)
                (x := sign_max (aval_sign a (restrict_local_for gs su))
                                (aval_sign b (restrict_local_for gs su)))) \<squnion> g) y"
      proof (cases "y = x")
        case True
        then show ?thesis
          using gl lb aval_sign_restrict_local_bot[OF nga lb, of su]
                aval_sign_restrict_local_bot[OF ngb lb, of su]
          unfolding restrict_local_for_def local_bot_on_locals_def sup_fun_def by simp
      next
        case False
        then show ?thesis
          using lb unfolding restrict_local_for_def local_bot_on_locals_def sup_fun_def by auto
      qed
    qed
  qed
qed

text \<open>
  Restricted to non-branch actions: \<open>EA_Assume\<close>/\<open>EA_AssumeNot\<close> are excluded
  by \<open>nb\<close> (\<^const>\<open>is_branch_action\<close>) rather than proved, since a local guard's
  plain \<open>branch\<close> field still collapses to whole-state \<open>bot\<close> on a definite
  contradiction (M1's \<open>branch\<close> is only a compatibility projection of
  \<open>branch_lifted\<close>) -- the ordinary local/global frame property genuinely
  fails for it even when the guard mentions no global. The lifted counterpart,
  \<open>sign_tf_branch_local_edge_invariant_lifted\<close> below, covers those two cases
  instead, against \<open>branch_lifted_sign\<close>.
\<close>
lemma sign_tf_local_edge_invariant:
  assumes loc: "local_edge_action gs a" and nb: "\<not> is_branch_action a"
  shows "local_edge_invariant gs (apply_tf (sign_tf_for gs) a)"
  using loc nb
  apply (cases a)
  unfolding sign_tf_for_def exp_mentions_global_def apply_tf.simps
  by (auto simp: skip_sign_def[abs_def] return_sign_def[abs_def] event_sign_def[abs_def]
      id_local_edge_invariant
      intro: assign_sign_local_edge_invariant special_sign_local_edge_invariant
      split: option.splits)

text \<open>
  \<open>EA_Assume\<close>/\<open>EA_AssumeNot\<close>'s counterpart to \<open>sign_tf_local_edge_invariant\<close>,
  against \<open>branch_lifted_sign\<close> instead of the plain \<open>branch_sign\<close>: since
  \<open>branch_lifted\<close>'s feasibility gate (\<open>is_bot\<close>/\<open>tobool\<close> of \<open>aval_abs\<close>) and its
  \<open>bfilter\<close> fallback both only inspect \<open>aval_sign b\<close>, a guard mentioning no
  global evaluates identically on the full and locally-restricted input
  (\<open>aval_sign_restrict_local_bot\<close>) -- so the feasibility decision, and hence
  which branch of \<open>branch_lifted\<close>'s case split fires, agrees between the two;
  the \<open>Lifted\<close> case then reduces to \<open>bfilter_sign_local_edge_invariant\<close>,
  already proved above.
\<close>
lemma branch_lifted_sign_local_edge_invariant_lifted:
  assumes ng: "\<not> exp_mentions_global gs b"
  shows "local_edge_invariant_lifted gs (branch_lifted_sign b pol)"
  unfolding local_edge_invariant_lifted_def
proof (intro allI impI)
  fix su g :: "sign abs_state"
  assume lb: "local_bot_on_locals gs g"
  let ?suL = "restrict_local_for gs su"
  have av: "aval_sign b (?suL \<squnion> g) = aval_sign b ?suL"
    using aval_sign_restrict_local_bot[OF ng lb, of su] .
  have inv: "bfilter_sign b pol (?suL \<squnion> g) = restrict_local_for gs (bfilter_sign b pol ?suL) \<squnion> g"
    using local_edge_invariantD[OF bfilter_sign_local_edge_invariant[OF ng] lb] .
  show "branch_lifted_sign b pol (?suL \<squnion> g) =
        map_lift (%r. restrict_local_for gs r \<squnion> g) (branch_lifted_sign b pol ?suL)"
    unfolding sign_backward_domain.branch_lifted_def av
    by (simp only: inv split: option.splits) simp
qed

subsection \<open>Regression: dead vs. reachable local branch against a live global\<close>

text \<open>
  Concrete witness for the branch-Deadcode distinction \<^const>\<open>local_branch_tree\<close>
  restores. \<open>sign_regression_local_branch_dead\<close>: a locally-restricted guard that
  is definitely infeasible collapses the whole reconstructed tree to
  \<^const>\<open>Bot\<close> -- for \<^emph>\<open>any\<close> value of \<open>\<sigma>\<close>'s global slot (it never even appears
  in the hypotheses), so a live named global is never rewritten or reassembled
  into a spurious reachable result. This is exactly the scenario the pre-M1
  whole-state-\<^const>\<open>bot\<close> encoding got wrong: \<open>x\<close> known \<open>SZero\<close> locally, guard
  \<open>V x\<close> asserted truthy (\<open>pol = True\<close>), definitely contradictory; \<open>G\<close>
  (classified global by \<open>gs\<close>) may be live at any value in \<open>\<sigma>\<close>'s Inr slot.
  \<open>sign_regression_local_branch_reach\<close> is the companion feasible case: \<open>x\<close>
  unconstrained (\<open>STop\<close>), so \<open>tobool\<close> cannot decide feasibility and
  \<^const>\<open>local_branch_tree\<close> falls through to \<^const>\<open>bfilter_sign\<close>, reassembling
  the narrowed local result with the \<^emph>\<open>caller's\<close> live global
  (\<^const>\<open>glob_env\<close> \<open>\<sigma>\<close>) unchanged -- old globals are preserved, not
  recomputed from \<open>su\<close>.
\<close>

definition sign_regression_gs :: "vname => bool" where
  "sign_regression_gs y = (y = STR ''G'')"

definition sign_regression_su_dead :: "sign abs_state" where
  "sign_regression_su_dead = (%_. SBot)(STR ''x'' := SZero)"

lemma sign_regression_branch_lifted_dead:
  "branch_lifted_sign (V (STR ''x'')) True
     (restrict_local_for sign_regression_gs sign_regression_su_dead) = Bot"
  unfolding sign_regression_su_dead_def sign_regression_gs_def restrict_local_for_def
  by (simp add: sign_backward_domain.branch_lifted_def fun_upd_def)

theorem sign_regression_local_branch_dead:
  fixes u :: pp and \<sigma> :: "pp + unit => sign abs_state lifted"
  assumes hu: "\<sigma> (Inl u) = Lifted sign_regression_su_dead"
  shows "etf_collecting_full_lift
           (local_branch_tree sign_regression_gs
              (branch_lifted_sign (V (STR ''x'')) True) u) \<sigma>
         = Bot"
proof (rule local_branch_tree_dead)
  show "\<sigma> (Inl u) = Lifted sign_regression_su_dead" by (rule hu)
next
  show "branch_lifted_sign (V (STR ''x'')) True
          (restrict_local_for sign_regression_gs sign_regression_su_dead) = Bot"
    by (rule sign_regression_branch_lifted_dead)
qed

definition sign_regression_su_reach :: "sign abs_state" where
  "sign_regression_su_reach = (%_. SBot)(STR ''x'' := STop)"

lemma sign_regression_branch_lifted_reach:
  "branch_lifted_sign (V (STR ''x'')) True
     (restrict_local_for sign_regression_gs sign_regression_su_reach) =
   Lifted (bfilter_sign (V (STR ''x'')) True
     (restrict_local_for sign_regression_gs sign_regression_su_reach))"
  unfolding sign_regression_su_reach_def sign_regression_gs_def restrict_local_for_def
  by (simp add: sign_backward_domain.branch_lifted_def fun_upd_def is_bottom_sign_def)

theorem sign_regression_local_branch_reach:
  fixes u :: pp and \<sigma> :: "pp + unit => sign abs_state lifted"
  assumes hu: "\<sigma> (Inl u) = Lifted sign_regression_su_reach"
  shows "etf_collecting_full_lift
           (local_branch_tree sign_regression_gs
              (branch_lifted_sign (V (STR ''x'')) True) u) \<sigma>
         = assemble_local_global
             (Lifted
               (restrict_local_for sign_regression_gs
                  (bfilter_sign (V (STR ''x'')) True
                    (restrict_local_for sign_regression_gs sign_regression_su_reach))
                \<squnion> restrict_global_for sign_regression_gs sign_regression_su_reach))
             (glob_env \<sigma>)"
proof (rule local_branch_tree_reach)
  show "\<sigma> (Inl u) = Lifted sign_regression_su_reach" by (rule hu)
next
  show "branch_lifted_sign (V (STR ''x'')) True
          (restrict_local_for sign_regression_gs sign_regression_su_reach) =
        Lifted (bfilter_sign (V (STR ''x'')) True
          (restrict_local_for sign_regression_gs sign_regression_su_reach))"
    by (rule sign_regression_branch_lifted_reach)
qed

end


