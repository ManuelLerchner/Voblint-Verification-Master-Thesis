theory Exec_Sign_Run
  imports Voblint_Core.Exec_St Voblint_Analysis.Sign_Domain "TD.TD_side_upd_rule"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
section \<open>Codegen probe: does sign resolved_st_q execute?\<close>

instance sign :: bounded_warrowing ..


abbreviation sign_lookup :: "sign resolved_st_q => vname => sign" where
  "sign_lookup s x == lookup_resolved_st_q s (location_of is_global x)"

abbreviation sign_update :: "sign resolved_st_q => vname => sign => sign resolved_st_q" where
  "sign_update s x a == update_resolved_st_q s (location_of is_global x) a"

text \<open>
  Minimal checks that the executable abstract state sign resolved_st_q evaluates under the
  code generator: lookup / update / sup / order / equality on concrete values.
\<close>

value "sign_lookup (sign_update (bot :: sign resolved_st_q) ''x'' SPos) ''x''"
value "sign_lookup (sign_update (bot :: sign resolved_st_q) ''x'' SPos) ''y''"
value "(sign_update (bot :: sign resolved_st_q) ''x'' SPos) \<squnion> (sign_update bot ''x'' SNeg)"
value "(sign_update (bot :: sign resolved_st_q) ''x'' SPos) = (sign_update bot ''x'' SPos)"
value "(sign_update (bot :: sign resolved_st_q) ''x'' SPos) \<le> (sign_update bot ''x'' STop)"

section \<open>Running the vendored TD_side solver on a sign resolved_st_q equation system\<close>

text \<open>
  A two-point equation system over sign resolved_st_q: P0 answers the state x |-> SPos, P1
  queries P0 and propagates it.  Solved by the always-join (precise) update rule
  via the vendored global interpretation, code-generated and evaluated.
\<close>

datatype pp = P0 | P1 | P2
datatype glob = G0

text \<open>
  Assignment transfer at sign resolved_st_q: evaluate e abstractly in the current state
  (sign_lookup gives the vname => sign view) and store the result at v.
\<close>

abbreviation assign_st :: "sign resolved_st_q \<Rightarrow> vname \<Rightarrow> aexp \<Rightarrow> sign resolved_st_q" where
  "assign_st s v e \<equiv> sign_update s v (aval_sign e (sign_lookup s))"

text \<open>
  Program  x := 1;  y := x + x.  Forward equations seeded from bot at entry; the
  analysis derives the signs -- it does not assert them.
\<close>

fun sign_eqs :: "pp \<Rightarrow> (pp, glob, sign resolved_st_q) strategy_tree" where
  "sign_eqs P0 = Answer bot"
| "sign_eqs P1 = QueryL P0 (\<lambda>s. Answer (assign_st s ''x'' (N 1)))"
| "sign_eqs P2 = QueryL P1 (\<lambda>s. Answer
     (assign_st s ''y'' (Plus (V ''x'') (V ''x''))))"

definition sign_solution :: "pp set \<times> (pp + glob \<Rightarrow> sign resolved_st_q)" where
  "sign_solution = TD_side_always_join_Interp_solve sign_eqs P2"

value "sign_lookup (snd sign_solution (Inl P2)) ''x''"
value "sign_lookup (snd sign_solution (Inl P2)) ''y''"
value "sign_lookup (snd sign_solution (Inl P0)) ''x''"
value "sign_lookup (snd sign_solution (Inl P1)) ''x''"
value "fst sign_solution"

end


