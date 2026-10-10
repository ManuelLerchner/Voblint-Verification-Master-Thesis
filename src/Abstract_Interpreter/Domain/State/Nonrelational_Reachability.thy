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
  finite implementation of it (\<open>default_st_is_bot_for\<close>, downstream in the
  \<open>Voblint_Exec\<close> session), since \<open>is_empty_state_lift\<close> below inherits
  \<^const>\<open>is_empty_state\<close>'s non-executable quantifier over \<^typ>\<open>vname\<close> on its
  \<open>Lifted\<close> case.
\<close>

subsection \<open>Composed concretization\<close>

text \<open>A lifted pointwise state is one more kind of state, so \<open>\<gamma> d\<close> covers it too.
  \<open>\<gamma>\<^sub>\<bottom> _\<close> stays as input syntax that fixes the lifted type where nothing else does.\<close>

abbreviation (input) gamma_state_lift ::
  "'a::numeric_domain abs_state lifted \<Rightarrow> store set" ("\<gamma>\<^sub>\<bottom>") where
  "gamma_state_lift \<equiv> gamma_lift gamma_state"

adhoc_overloading gamma_S == "gamma_lift gamma_state"

fun is_empty_state_lift ::
  "'a::executable_domain abs_state lifted \<Rightarrow> bool" where
  "is_empty_state_lift Bot = True"
| "is_empty_state_lift (Lifted d) = is_empty_state d"

lemma is_empty_state_lift_iff:
  "is_empty_state_lift s \<longleftrightarrow> \<gamma>\<^sub>\<bottom> s = {}"
  by (cases s) (simp_all add: is_empty_state_iff_gamma_state_empty)

lemma exact_emptiness_is_empty_state_lift:
  "exact_emptiness is_empty_state_lift
     (gamma_lift gamma_state :: 'a::numeric_domain abs_state lifted \<Rightarrow> store set)"
  by (rule exact_emptinessI) (rule is_empty_state_lift_iff)

text \<open>
  \<open>Reachability_Lift\<close>'s generic \<open>gamma_normalize_lift\<close>/\<open>normalize_lift_mono\<close>/
  \<open>normalized_lift_sup\<close> specialized to \<open>is_empty_state\<close>: each generic side
  condition (concretization agreement, downward closure) is discharged by
  \<open>is_empty_state_iff_gamma_state_empty\<close>/\<open>is_empty_state_antimono\<close>. The first
  is tagged \<open>[simp]\<close>, unlike the generic version, because its side condition
  is now a closed fact rather than a further proof obligation.
\<close>

lemma gamma_state_normalize_lift [simp]:
  "\<gamma>\<^sub>\<bottom> (normalize_lift is_empty_state d) = \<gamma> d"
  by (rule gamma_normalize_lift) (rule is_empty_state_iff_gamma_state_empty)

text \<open>Collapsing a witness-bottom payload changes what a value says about
  itself, never what it represents. Every public result adapter routes its
  solved values through \<^const>\<open>canonicalize_lift\<close> before publishing them, so
  this is what lets such an adapter's soundness argument ignore the collapse
  entirely.\<close>

lemma gamma_state_canonicalize_lift [simp]:
  "\<gamma>\<^sub>\<bottom> (canonicalize_lift is_empty_state d) = \<gamma>\<^sub>\<bottom> d"
  by (cases d) simp_all

lemma normalize_state_lift_mono [intro]:
  fixes d1 d2 :: "'a::numeric_domain abs_state"
  assumes le: "d1 \<le> d2"
  shows "normalize_lift is_empty_state d1 \<le> normalize_lift is_empty_state d2"
  by (rule normalize_lift_mono[OF le]) (rule is_empty_state_antimono[OF le])

lemma normalized_state_lift_sup [intro]:
  fixes s1 s2 :: "'a::numeric_domain abs_state lifted"
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
  "s \<in> \<gamma>\<^sub>\<bottom> x \<Longrightarrow> s \<in> \<gamma>\<^sub>\<bottom> (x \<squnion> y)"
  for x y :: "'a::numeric_domain abs_state lifted"
  by (cases x; cases y) auto

lemma gamma_state_lift_supI2 [intro]:
  "s \<in> \<gamma>\<^sub>\<bottom> y \<Longrightarrow> s \<in> \<gamma>\<^sub>\<bottom> (x \<squnion> y)"
  for x y :: "'a::numeric_domain abs_state lifted"
  by (cases x; cases y) auto

subsection \<open>Carrying a transfer's soundness through the lift\<close>

text \<open>
  A pure transfer's soundness fact carries over the \<^const>\<open>transfer_lift\<close>
  wrapper by one case split: \<^const>\<open>Bot\<close>'s concretization is empty, and a
  \<^const>\<open>normalize_lift\<close> collapse to \<^const>\<open>Bot\<close> only ever fires when
  \<open>empty_pred\<close> holds, whose concretization is empty by assumption. Three shapes
  cover every use --- a collecting inclusion, a membership, and a binary
  membership for a combine --- so no consumer repeats the bottom argument.
\<close>

lemma transfer_lift_sound_collect:
  assumes step: "\<And>d'. C (\<gamma> d') \<subseteq> \<gamma> (f d')"
    and Cempty: "C {} = {}"
    and empty_pred_sound: "\<And>d'. empty_pred d' \<Longrightarrow> \<gamma> d' = {}"
  shows "C (\<gamma>\<^sub>\<bottom> d) \<subseteq> \<gamma>\<^sub>\<bottom> (transfer_lift empty_pred f d)"
proof (cases d)
  case Bot
  then show ?thesis by (simp add: Cempty)
next
  case (Lifted d')
  have "C (\<gamma> d') \<subseteq> \<gamma> (f d')" by (rule step)
  then show ?thesis
    using Lifted empty_pred_sound[of "f d'"] by (auto simp: normalize_lift_def)
qed

lemma transfer_lift_sound_mem:
  assumes step: "\<And>d'. s \<in> \<gamma> d' \<Longrightarrow> h s \<in> \<gamma> (f d')"
    and empty_pred_sound: "\<And>d'. empty_pred d' \<Longrightarrow> \<gamma> d' = {}"
    and s: "s \<in> \<gamma>\<^sub>\<bottom> d"
  shows "h s \<in> \<gamma>\<^sub>\<bottom> (transfer_lift empty_pred f d)"
proof (cases d)
  case Bot
  then show ?thesis using s by simp
next
  case (Lifted d')
  with s have "s \<in> \<gamma> d'" by simp
  then have hs: "h s \<in> \<gamma> (f d')" by (rule step)
  then have "\<not> empty_pred (f d')" using empty_pred_sound by auto
  with Lifted hs show ?thesis by simp
qed

lemma transfer_lift2_sound_mem:
  assumes step: "\<And>d1' d2'. s \<in> \<gamma> d1' \<Longrightarrow> t \<in> \<gamma> d2' \<Longrightarrow> h s t \<in> \<gamma> (f d1' d2')"
    and empty_pred_sound: "\<And>d'. empty_pred d' \<Longrightarrow> \<gamma> d' = {}"
    and s: "s \<in> \<gamma>\<^sub>\<bottom> d1"
    and t: "t \<in> \<gamma>\<^sub>\<bottom> d2"
  shows "h s t \<in> \<gamma>\<^sub>\<bottom> (transfer_lift2 empty_pred f d1 d2)"
proof (cases d1)
  case Bot
  then show ?thesis using s by simp
next
  case (Lifted d1')
  show ?thesis
  proof (cases d2)
    case Bot
    then show ?thesis using t by simp
  next
    case (Lifted d2')
    with \<open>d1 = Lifted d1'\<close> s t have "s \<in> \<gamma> d1'" "t \<in> \<gamma> d2'" by simp_all
    then have hst: "h s t \<in> \<gamma> (f d1' d2')" by (rule step)
    then have "\<not> empty_pred (f d1' d2')" using empty_pred_sound by auto
    with \<open>d1 = Lifted d1'\<close> Lifted hst show ?thesis by simp
  qed
qed

end
