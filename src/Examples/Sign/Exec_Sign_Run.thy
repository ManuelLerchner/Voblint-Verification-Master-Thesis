theory Exec_Sign_Run
  imports Voblint_Core.Exec_St Voblint_Analysis.Sign_Domain "TD.TD_side_upd_rule"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
section \<open>Codegen probe: does sign resolved_st_q execute?\<close>

instance sign :: bounded_warrowing ..


text \<open>This probe has no source program to declare globals, so it fixes a
  trivial classifier (nothing is global) once and threads it explicitly,
  rather than reintroducing name-based detection.\<close>
abbreviation probe_gs :: "vname \<Rightarrow> bool" where
  "probe_gs \<equiv> (\<lambda>_. False)"

abbreviation sign_lookup :: "sign resolved_st_q => vname => sign" where
  "sign_lookup s x == lookup_resolved_st_q s (location_of probe_gs x)"

abbreviation sign_update :: "sign resolved_st_q => vname => sign => sign resolved_st_q" where
  "sign_update s x a == update_resolved_st_q s (location_of probe_gs x) a"

text \<open>
  Minimal checks that the executable abstract state sign resolved_st_q evaluates under the
  code generator: lookup / update / sup / order / equality on concrete values.
\<close>

value "sign_lookup (sign_update (bot :: sign resolved_st_q) (STR ''x'') SPos) (STR ''x'')"
value "sign_lookup (sign_update (bot :: sign resolved_st_q) (STR ''x'') SPos) (STR ''y'')"
value "(sign_update (bot :: sign resolved_st_q) (STR ''x'') SPos) \<squnion> (sign_update bot (STR ''x'') SNeg)"
value "(sign_update (bot :: sign resolved_st_q) (STR ''x'') SPos) = (sign_update bot (STR ''x'') SPos)"
value "(sign_update (bot :: sign resolved_st_q) (STR ''x'') SPos) \<le> (sign_update bot (STR ''x'') STop)"

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

abbreviation assign_st :: "sign resolved_st_q \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> sign resolved_st_q" where
  "assign_st s v e \<equiv> sign_update s v (aval_sign e (sign_lookup s))"

text \<open>
  Program  x := 1;  y := x + x.  Forward equations seeded from bot at entry; the
  analysis derives the signs -- it does not assert them.
\<close>

fun sign_eqs :: "pp \<Rightarrow> (pp, glob, sign resolved_st_q) strategy_tree" where
  "sign_eqs P0 = answer bot"
| "sign_eqs P1 = do { s \<leftarrow> read_local P0; answer (assign_st s (STR ''x'') (N 1)) }"
| "sign_eqs P2 = do {
     s \<leftarrow> read_local P1;
     answer (assign_st s (STR ''y'') (Plus (V (STR ''x'')) (V (STR ''x''))))
   }"

definition sign_solution :: "pp set \<times> (pp + glob \<Rightarrow> sign resolved_st_q)" where
  "sign_solution = TD_side_always_join_Interp_solve sign_eqs P2"

value "sign_lookup (snd sign_solution (Inl P2)) (STR ''x'')"
value "sign_lookup (snd sign_solution (Inl P2)) (STR ''y'')"
value "sign_lookup (snd sign_solution (Inl P0)) (STR ''x'')"
value "sign_lookup (snd sign_solution (Inl P1)) (STR ''x'')"
value "fst sign_solution"

end


