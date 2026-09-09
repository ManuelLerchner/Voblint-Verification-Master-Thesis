theory Example_Sign_Domain_Ops
  imports "Voblint_Analysis_Sign.Sign_Transfer"
begin

section \<open>What the sign operations compute on small inputs\<close>

text \<open>Executable demonstrations of the sign lattice and its arithmetic: abstraction of a
  concrete integer, the four abstract operations, the join, printing, expression evaluation
  under a store, and one assignment.  Each is a \<open>value\<close> rather than a proved equation,
  so this theory pins nothing --- it is the worked example the lattice theories omit.
  Backward guard refinement is the abstract spec \<^const>\<open>bfilter_sign\<close>; its executable
  mirror on \<open>sign st\<close> is demonstrated in \<open>Sign_Exec\<close>.\<close>

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

end
