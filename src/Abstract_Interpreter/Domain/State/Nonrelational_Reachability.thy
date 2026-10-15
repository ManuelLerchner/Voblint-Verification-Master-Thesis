theory Nonrelational_Reachability
  imports Nonrelational_State Reachability_Lift
begin

section \<open>Reachability for pointwise abstract stores\<close>

text \<open>
  Pointwise stores and structural reachability are independent domain
  constructions. This theory composes them: unreachable points denote no
  concrete store, and reachable payloads use \<^const>\<open>gamma_state\<close>.
  A lifted pointwise state is one more kind of state, so \<open>\<gamma> d\<close> covers it too.
\<close>

adhoc_overloading gamma_S == "gamma_lift gamma_state"

end
