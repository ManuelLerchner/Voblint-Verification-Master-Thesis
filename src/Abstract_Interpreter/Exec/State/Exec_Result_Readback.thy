theory Exec_Result_Readback
  imports Exec_St_Transfer "Voblint_Domain.Reachability_Lift"
begin

section \<open>Normalizing a solved local unknown\<close>

text \<open>
  \<open>readback_result_value\<close> is the sole entry point from the executable solver
  substrate into the result boundary: it relabels the local unknown exactly
  as the solver stores it (an \<^typ>\<open>'a resolved_st_q lifted\<close>) into a
  \<^typ>\<open>'a abs_state lifted\<close>, \<^const>\<open>Bot\<close> becoming \<^const>\<open>Bot\<close> and
  \<^const>\<open>Lifted\<close> becoming \<^const>\<open>Lifted\<close> of the projected state. It is a
  purely structural conversion with no bottom test of its own.

  This is a normalization boundary, not a totalization one. Which program points
  a published result answers for is the solve's own covered key set; nothing here
  adds a point the solver never reached. A covered key whose stored value is
  \<^const>\<open>Bot\<close> stays a key and reports \<^const>\<open>Bot\<close>, so coverage and
  reachability are separate properties of a result.

  Semantic deadness is normalized \<^emph>\<open>before\<close> this point, not here:
  \<^const>\<open>canonicalize_lift\<close> is the boundary that collapses a witness-bottom
  \<^const>\<open>Lifted\<close> payload to \<^const>\<open>Bot\<close>, and every public result adapter
  routes its raw solver value through \<open>canonicalize_lift\<close> first, so
  \<open>readback_result_value\<close> itself never needs the declared globals as a list, nor
  \<^class>\<open>executable_domain\<close>'s executable witness-bottom test.
\<close>

fun readback_result_value ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('a::bot) resolved_st_q lifted \<Rightarrow> 'a abs_state lifted"
where
  "readback_result_value \<G> Bot = Bot"
| "readback_result_value \<G> (Lifted s) = Lifted (fun_of_resolved_st_q_for \<G> s)"
end
