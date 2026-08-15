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
  assumes ng: "\<not> aexp_mentions_global gs a"
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
qed

lemma aval_sign_restrict_local_bot:
  assumes ng: "\<not> aexp_mentions_global gs a"
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
qed

lemma assign_sign_local_edge_invariant [intro]:
  assumes gl: "\<not> gs x" and ng: "\<not> aexp_mentions_global gs e"
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
  assumes ng: "\<not> aexp_mentions_global gs e"
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
  then have ng1: "\<not> aexp_mentions_global gs e1" and ng2: "\<not> aexp_mentions_global gs e2"
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
  then have ng1: "\<not> aexp_mentions_global gs e1" and ng2: "\<not> aexp_mentions_global gs e2"
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
  then have ng1: "\<not> aexp_mentions_global gs e1" and ng2: "\<not> aexp_mentions_global gs e2"
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
qed

lemma bfilter_sign_local_edge_invariant:
  assumes ng: "\<not> bexp_mentions_global gs b"
  shows "local_edge_invariant gs (\<lambda>\<sigma>. bfilter_sign b res \<sigma>)"
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
  then have ng1: "\<not> bexp_mentions_global gs b1" and ng2: "\<not> bexp_mentions_global gs b2"
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
  then have ng1: "\<not> bexp_mentions_global gs b1" and ng2: "\<not> bexp_mentions_global gs b2"
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
  then have ng1: "\<not> aexp_mentions_global gs e1" and ng2: "\<not> aexp_mentions_global gs e2"
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
  then have ng1: "\<not> aexp_mentions_global gs e1" and ng2: "\<not> aexp_mentions_global gs e2"
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
    with ng have nga: "\<not> aexp_mentions_global gs a" and ngb: "\<not> aexp_mentions_global gs b"
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
    with ng have nga: "\<not> aexp_mentions_global gs a" and ngb: "\<not> aexp_mentions_global gs b"
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

lemma sign_tf_local_edge_invariant:
  assumes loc: "local_edge_action gs a"
  shows "local_edge_invariant gs (apply_tf (sign_tf_for gs) a)"
  using loc
  apply (cases a)
  unfolding sign_tf_for_def aexp_mentions_global_def apply (auto simp: 
      intro: assign_sign_local_edge_invariant
             bfilter_sign_local_edge_invariant
             special_sign_local_edge_invariant
             id_local_edge_invariant
      split: option.splits)
  apply (auto simp: local_edge_invariant_def skip_sign_def return_sign_def event_sign_def)
  by (metis aexp_mentions_global_def assign_sign_local_edge_invariant
      local_edge_invariant_def)
 
 

end

