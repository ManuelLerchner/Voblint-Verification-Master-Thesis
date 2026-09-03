theory Nonrelational_Reachability
  imports Nonrelational_State Reachability_Lift
begin

section \<open>Reachability for pointwise abstract stores\<close>

text \<open>
  Pointwise stores and structural reachability are independent domain
  constructions. This theory composes them: unreachable points denote no
  concrete store, and reachable payloads use \<^const>\<open>gamma_state\<close>.
  The logical witness-empty predicate agrees with that composed
  concretization; a concrete executable state representation supplies a
  finite implementation of it (\<open>resolved_st_q_is_bot_for\<close>, downstream in the
  \<open>Voblint_Exec\<close> session), since \<open>is_empty_state_lift\<close> below inherits
  \<^const>\<open>is_empty_state\<close>'s non-executable quantifier over \<^typ>\<open>vname\<close> on its
  \<open>Lifted\<close> case.
\<close>

subsection \<open>Composed concretization\<close>

abbreviation gamma_state_lift ::
  "'a::sound_domain abs_state lifted \<Rightarrow> store set" where
  "gamma_state_lift \<equiv> gamma_lift gamma_state"

fun is_empty_state_lift ::
  "'a::executable_domain abs_state lifted \<Rightarrow> bool" where
  "is_empty_state_lift Bot = True"
| "is_empty_state_lift (Lifted \<sigma>) = is_empty_state \<sigma>"

lemma is_empty_state_lift_iff:
  "is_empty_state_lift s \<longleftrightarrow> gamma_state_lift s = {}"
  by (cases s) (simp_all add: is_empty_state_iff_gamma_state_empty)

text \<open>
  \<open>Reachability_Lift\<close>'s generic \<open>gamma_normalize_lift\<close>/\<open>normalize_lift_mono\<close>/
  \<open>normalized_lift_sup\<close> specialized to \<open>is_empty_state\<close>: each generic side
  condition (concretization agreement, downward closure) is discharged by
  \<open>is_empty_state_iff_gamma_state_empty\<close>/\<open>is_empty_state_antimono\<close>. The first
  is tagged \<open>[simp]\<close>, unlike the generic version, because its side condition
  is now a closed fact rather than a further proof obligation.
\<close>

lemma gamma_state_normalize_lift [simp]:
  "gamma_state_lift (normalize_lift is_empty_state \<sigma>) = \<lbrakk>\<sigma>\<rbrakk>"
  by (rule gamma_normalize_lift) (rule is_empty_state_iff_gamma_state_empty)

lemma normalize_state_lift_mono [intro]:
  fixes \<sigma>1 \<sigma>2 :: "'a::sound_domain abs_state"
  assumes le: "\<sigma>1 \<le> \<sigma>2"
  shows "normalize_lift is_empty_state \<sigma>1 \<le> normalize_lift is_empty_state \<sigma>2"
  by (rule normalize_lift_mono[OF le]) (rule is_empty_state_antimono[OF le])

lemma normalized_state_lift_sup [intro]:
  fixes s1 s2 :: "'a::sound_domain abs_state lifted"
  assumes n1: "normalized_lift is_empty_state s1" and n2: "normalized_lift is_empty_state s2"
  shows "normalized_lift is_empty_state (s1 \<squnion> s2)"
  by (rule normalized_lift_sup[OF is_empty_state_antimono n1 n2])

subsection \<open>The normalization invariant\<close>

text \<open>
  After normalization, structural and semantic deadness coincide: a
  \<open>normalized_lift\<close>-disciplined value can no longer disagree with its own
  \<open>is_empty_state_lift\<close> reading, because normalization is exactly what rules
  out a live-looking \<open>Lifted\<close> payload that is secretly witness-bottom.
\<close>

lemma normalized_state_lift_bot_iff [simp]:
  "normalized_lift is_empty_state s \<Longrightarrow> is_empty_state_lift s \<longleftrightarrow> s = Bot"
  by (cases s) simp_all

subsection \<open>Join\<close>

text \<open>
  \<open>gamma_state_supI1\<close>/\<open>gamma_state_supI2\<close> lifted through \<^const>\<open>gamma_state_lift\<close>:
  a witness on one side of a lifted join survives it, whether the other side
  is \<^const>\<open>Bot\<close> (the join's identity) or a competing \<^const>\<open>Lifted\<close> payload.
\<close>

lemma gamma_state_lift_supI1 [intro]:
  "s \<in> gamma_state_lift x \<Longrightarrow> s \<in> gamma_state_lift (x \<squnion> y)"
  for x y :: "'a::sound_domain abs_state lifted"
  by (cases x; cases y) auto

lemma gamma_state_lift_supI2 [intro]:
  "s \<in> gamma_state_lift y \<Longrightarrow> s \<in> gamma_state_lift (x \<squnion> y)"
  for x y :: "'a::sound_domain abs_state lifted"
  by (cases x; cases y) auto

end
