theory Exec_Result_Abs
  imports Default_St_Transfer "Voblint_Domain.Reachability_Lift"
begin

section \<open>A solved local unknown as an abstract state\<close>

text \<open>
  \<open>result_value_to_abs\<close> turns a solved local unknown into a result value: it is the sole
  entry point from the executable solver substrate into the result boundary,
  and it relabels the local unknown exactly as the solver stores it (an
  \<^typ>\<open>'a default_st lifted\<close>) into a \<^typ>\<open>'a abs_state lifted\<close>,
  \<^const>\<open>Bot\<close> becoming \<^const>\<open>Bot\<close> and \<^const>\<open>Lifted\<close>
  becoming \<^const>\<open>Lifted\<close> of the function the state represents. It is a
  purely structural conversion with no bottom test of its own.

  The conversion normalizes a value; it does not totalize the table. Which program
  points a result answers for is the solve's own covered key set; nothing here
  adds a point the solver never reached. A covered key whose stored value is
  \<^const>\<open>Bot\<close> stays a key and reports \<^const>\<open>Bot\<close>, so coverage and
  reachability are separate properties of a result.

  Semantic deadness is normalized \<^emph>\<open>before\<close> this point, not here:
  \<^const>\<open>canonicalize_lift\<close> is the boundary that collapses a witness-bottom
  \<^const>\<open>Lifted\<close> payload to \<^const>\<open>Bot\<close>, and every public result adapter
  routes its raw solver value through \<open>canonicalize_lift\<close> first, so
  \<open>result_value_to_abs\<close> itself never needs the declared globals as a list, nor
  \<^class>\<open>executable_domain\<close>'s executable witness-bottom test.
\<close>

fun result_value_to_abs ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('a::bot) default_st lifted \<Rightarrow> 'a abs_state lifted"
where
  "result_value_to_abs \<G> Bot = Bot"
| "result_value_to_abs \<G> (Lifted s) = Lifted (default_st_to_fun \<G> s)"
end
