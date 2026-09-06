theory Sign_Domain
  imports Sign_Transfer
begin

hide_const (open) Update_rules.N

section \<open>Integrated Sign domain\<close>

text \<open>This theory provides one import surface for the Sign lattice, arithmetic,
  backward filtering, transfer functions, printing, and local-effect invariants.\<close>

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
value "aval_sign (Plus (V (STR ''x'')) (V (STR ''x''))) ((\<lambda>_. SBot)((STR ''x'') := SPos))"

value "assign_sign (STR ''x'') (N 1) (\<lambda>_. SBot) (STR ''x'')"

text \<open>Backward guard refinement is the abstract spec @{const bfilter_sign}.
  Its executable mirror @{text bfilter_sign_st} on @{text "sign st"} is defined and
  demonstrated in theory @{text Sign_Exec}.\<close>

end

