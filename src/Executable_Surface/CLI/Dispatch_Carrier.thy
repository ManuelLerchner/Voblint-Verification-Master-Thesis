theory Dispatch_Carrier
  imports
    Voblint_Analysis_Sign.Sign_Entry
    Voblint_Analysis_Interval.Interval_Entry
    Voblint_Analysis_Int.Int_Entry
    Voblint_Analysis_Parity.Parity_Entry
    Voblint_Analysis_Congruence.Congruence_Entry
begin

section \<open>One value type wide enough for every domain's report\<close>

text \<open>
  A report crosses the dispatcher without its caller knowing which analysis
  produced it, so the per-check state has to have one type. \<open>abstract_value\<close> is
  that type: a tagged union with one constructor per selectable domain, and
  \<open>tag_states\<close> attaches a domain's tag to every state in a report, leaving the
  verdicts and the unreachable flag untouched.

  This is handwritten and stays handwritten. The datatype names each domain's
  own abstract state type, which is domain content rather than registration, so
  it is the one part of the dispatch surface the registry does not describe. The
  generated tables read it.
\<close>

datatype abstract_value =
    SignValue sign
  | IntervalValue ivl
  | IntDomValue int_dom
  | ParityValue parity
  | CongruenceValue congruence

definition tag_states ::
    "('s \<Rightarrow> abstract_value) \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> 's abs_state) list
       \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list" where
  "tag_states tag = map (\<lambda>(u, c, r, unreachable, s). (u, c, r, unreachable, tag \<circ> s))"

end
