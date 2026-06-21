theory Exec_Sign_Run
  imports Exec_St Sign_Domain "TD.TD_side_upd_rule"
begin

section \<open>Codegen probe: does sign st execute?\<close>

text \<open>
  Minimal checks that the executable abstract state sign st evaluates under the
  code generator: lookup / update / sup / order / equality on concrete values.
\<close>

value "lookup_st (update_st (bot :: sign st) ''x'' SPos) ''x''"
value "lookup_st (update_st (bot :: sign st) ''x'' SPos) ''y''"
value "(update_st (bot :: sign st) ''x'' SPos) \<squnion> (update_st bot ''x'' SNeg)"
value "(update_st (bot :: sign st) ''x'' SPos) = (update_st bot ''x'' SPos)"
value "(update_st (bot :: sign st) ''x'' SPos) \<le> (update_st bot ''x'' STop)"

section \<open>Running the vendored TD_side solver on a sign st equation system\<close>

text \<open>
  A two-point equation system over sign st: P0 answers the state x |-> SPos, P1
  queries P0 and propagates it.  Solved by the always-join (precise) update rule
  via the vendored global interpretation, code-generated and evaluated.
\<close>

datatype pp = P0 | P1 | P2
datatype glob = G0

text \<open>
  Assignment transfer at sign st: evaluate e abstractly in the current state
  (lookup_st gives the vname => sign view) and store the result at v.
\<close>

abbreviation assign_st :: "sign st \<Rightarrow> vname \<Rightarrow> aexp \<Rightarrow> sign st" where
  "assign_st s v e \<equiv> update_st s v (aval_sign e (lookup_st s))"

text \<open>
  Program  x := 1;  y := x + x.  Forward equations seeded from bot at entry; the
  analysis derives the signs -- it does not assert them.
\<close>

fun sign_eqs :: "pp \<Rightarrow> (pp, glob, sign st) strategy_tree" where
  "sign_eqs P0 = Answer bot"
| "sign_eqs P1 = QueryL P0 (\<lambda>s. Answer (assign_st s ''x'' (BaseN (AExp.N 1))))"
| "sign_eqs P2 = QueryL P1 (\<lambda>s. Answer
     (assign_st s ''y'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.V ''x'')))))"

definition sign_solution :: "pp set \<times> (pp + glob \<Rightarrow> sign st)" where
  "sign_solution = TD_side_always_join_Interp_solve sign_eqs P2"

value "lookup_st (snd sign_solution (Inl P2)) ''x''"
value "lookup_st (snd sign_solution (Inl P2)) ''y''"
value "lookup_st (snd sign_solution (Inl P0)) ''x''"
value "lookup_st (snd sign_solution (Inl P1)) ''x''"
value "fst sign_solution"

end
