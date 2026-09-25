theory Congruence_Warrowing
  imports Congruence_Lattice "Voblint_Exec.Exec_St_Reachability"
begin

section \<open>Type-class warrowing for the TD warrowing solver\<close>

text \<open>
  Congruence follows Sign's and Parity's own choice
  (\<open>Sign_Lattice\<close>, \<open>Parity_Domain\<close>): the vendored \<open>widening\<close>/
  \<open>narrowing\<close> classes require only the four upper/bracket laws below, not a
  termination proof, so a domain whose lattice is already well behaved gets
  a conservative instance rather than an invented acceleration mechanism.
  Widening is plain join; narrowing is the trivial left projection, which
  discharges \<open>narrow_ge\<close>/\<open>narrow_le\<close> immediately from \<open>b <= a\<close> without
  needing anything about congruence's own structure.
\<close>

definition narrow_congruence_td :: "congruence => congruence => congruence" where
  "narrow_congruence_td a b = a"

instantiation congruence :: warrowing
begin

definition widen_congruence :: "congruence => congruence => congruence" where
  "widen (a :: congruence) b = join_congruence a b"

definition narrow_congruence :: "congruence => congruence => congruence" where
  "narrow (a :: congruence) b = narrow_congruence_td a b"

instance proof intro_classes
  fix a b :: congruence
  show "a <= widen a b"
    unfolding widen_congruence_def by (rule join_congruence_ub1)
  show "b <= widen a b"
    unfolding widen_congruence_def by (rule join_congruence_ub2)
  show "b <= a \<Longrightarrow> b <= narrow a b"
    unfolding narrow_congruence_def narrow_congruence_td_def by simp
  show "b <= a \<Longrightarrow> narrow a b <= a"
    unfolding narrow_congruence_def narrow_congruence_td_def by simp
qed

end

section \<open>Numeric domain instance\<close>

text \<open>\<open>numeric_domain\<close> extends \<open>executable_domain\<close>, which includes the solver's
  \<open>warrowing\<close>, so the instance follows the widening and narrowing above.\<close>

instantiation congruence :: numeric_domain
begin

definition gamma_abs_congruence [simp]:
  "\<gamma> (a :: congruence) = gamma_congruence a"

definition is_empty_congruence [simp]:
  "is_empty (a :: congruence) = is_bottom_congruence a"

definition to_string_congruence [simp]:
  "to_string (a :: congruence) =
     (if is_top_congruence a then sym_top else string_of_congruence a)"

instance
proof intro_classes
  show "\<gamma> (bot :: congruence) = {}"
    unfolding bot_congruence_def by simp
next
  show "\<gamma> (top :: congruence) = UNIV"
    by simp
next
  fix a b :: congruence
  assume "a <= b"
  then show "\<gamma> a \<subseteq> \<gamma> b"
    unfolding less_eq_congruence_iff_gamma
    by simp
next
  fix a :: congruence
  show "is_empty a \<longleftrightarrow> \<gamma> a = {}"
    by (simp add: is_bottom_congruence_correct)
qed

end

lemma to_string_congruence_regression:
  "to_string (top :: congruence) = STR ''<top>''"
  "to_string (mk_congruence 1 2) = STR ''1+2<int>''"
  by eval+

end
