theory Nonrelational_Reachability
  imports Nonrelational_State Reachability_Lift
begin

section \<open>Reachability for pointwise abstract stores\<close>

text \<open>
  Pointwise stores and structural reachability are independent domain
  constructions. This theory composes them: unreachable points denote no
  concrete store, and reachable payloads use \<^const>\<open>gamma_state\<close>.
  The executable bottom test agrees with that composed concretization.
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

subsection \<open>The normalization invariant\<close>

text \<open>
  After normalization, structural and semantic deadness coincide: a
  \<open>normalized_lift\<close>-disciplined value can no longer disagree with its own
  \<open>is_empty_state_lift\<close> reading, because normalization is exactly what rules
  out a live-looking \<open>Lifted\<close> payload that is secretly witness-bottom.
\<close>

lemma normalized_state_lift_bot_iff:
  "normalized_lift is_empty_state s \<Longrightarrow> is_empty_state_lift s \<longleftrightarrow> s = Bot"
  by (cases s) simp_all

end
