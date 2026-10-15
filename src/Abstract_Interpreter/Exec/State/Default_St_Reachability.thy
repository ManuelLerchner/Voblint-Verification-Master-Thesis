theory Default_St_Reachability
  imports Default_St_Transfer "Voblint_Domain.Nonrelational_Reachability"
begin

unbundle default_st_syntax

text \<open>
  A lifted state reads back pointwise under the lift: \<^const>\<open>Bot\<close> stays
  \<^const>\<open>Bot\<close>, and a \<^const>\<open>Lifted\<close> state becomes \<^const>\<open>Lifted\<close> of the
  function it represents. This is how a solved local unknown, stored as an
  \<^typ>\<open>('k, 'a) gdefault_st lifted\<close>, enters the result boundary. The readback
  performs no bottom test. \<^const>\<open>canonicalize_lift\<close> collapses a
  witness-bottom payload to \<^const>\<open>Bot\<close> before it, and coverage stays a
  property of the solve: a covered key whose value is \<^const>\<open>Bot\<close> remains a
  key.
\<close>

adhoc_overloading readback == "\<lambda>\<G>. map_lift (default_st_to_fun \<G>)"

end
