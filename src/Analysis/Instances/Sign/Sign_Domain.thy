theory Sign_Domain
  imports Sign_Local_Effects Sign_Print
begin

hide_const (open) Update_rules.N

section \<open>Sign domain compatibility facade\<close>

text \<open>
  This theory preserves the historical sign-domain import surface.  The
  implementation lives in responsibility-focused theories for the lattice,
  arithmetic, backward filtering, transfer functions, printing, and local
  effectful invariants used by the mixed side solver.
\<close>

subsection \<open>Executable examples\<close>

value "sign_of_int (-5)"
value "sign_of_int 0"
value "sign_of_int 3"

value "(SNeg::sign) + SPos"
value "(SPos::sign) - SPos"
value "(SNeg::sign) * SNeg"
value "(SZero::sign) * STop"

value "join_sign SNeg SPos"
value "join_sign SNeg SZero"
value "join_sign SPos SZero"

value "string_of_sign STop"
value "string_of_sign SNonPos"

value "aval_sign (Times (N (-2)) (N 3)) (\<lambda>_. SBot)"
value "aval_sign (Plus (V ''x'') (V ''x'')) ((\<lambda>_. SBot)(''x'' := SPos))"

value "assign_sign ''x'' (N 1) (\<lambda>_. SBot) ''x''"

text \<open>Backward guard refinement is the abstract spec @{const assume_sign}.
  Its executable mirror @{text assume_sign_st} on @{text "sign st"} is defined and
  demonstrated in theory @{text Sign_Exec}.\<close>

end

