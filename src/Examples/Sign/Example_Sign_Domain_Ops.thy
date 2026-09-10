theory Example_Sign_Domain_Ops
  imports "Voblint_Analysis_Sign.Sign_Transfer"
begin

section \<open>What the sign operations compute on small inputs\<close>

text \<open>
  The sign lattice and its arithmetic on concrete inputs, each pinned as a proved
  equation: abstraction of an integer, the four abstract operations, the join, printing,
  expression evaluation under a store, and one assignment.  Together they fix both what
  the seven-element lattice decides --- a negative times a negative is \<open>SPos\<close>, a zero
  absorbs everything --- and where it has to give up: a negative plus a positive, and a
  difference of two positives, are \<open>STop\<close>.  Backward guard refinement is the abstract
  spec \<^const>\<open>bfilter_sign\<close>; its executable mirror on \<open>sign st\<close> is demonstrated in
  \<open>Sign_Exec\<close>.
\<close>

lemma sign_of_int_regression:
  "sign_of_int (-5) = SNeg"
  "sign_of_int 0 = SZero"
  "sign_of_int 3 = SPos"
  by eval+

lemma sign_arithmetic_regression:
  "(SNeg::sign) + SPos = STop"
  "(SPos::sign) - SPos = STop"
  "(SNeg::sign) * SNeg = SPos"
  "(SZero::sign) * STop = SZero"
  by eval+

lemma join_sign_regression:
  "join_sign SNeg SPos = STop"
  "join_sign SNeg SZero = SNonPos"
  "join_sign SPos SZero = SNonNeg"
  by eval+

lemma string_of_sign_regression:
  "string_of_sign STop = ''Top''"
  "string_of_sign SNonPos = ''NonPositive''"
  by eval+

lemma aval_sign_regression:
  "aval_sign (Times (N (-2)) (N 3)) (\<lambda>_. SBot) = SNeg"
  "aval_sign (Plus (V (STR ''x'')) (V (STR ''x'')))
     ((\<lambda>_. SBot)((STR ''x'') := SPos)) = SPos"
  by eval+

lemma assign_sign_regression:
  "assign_sign (STR ''x'') (N 1) (\<lambda>_. SBot) (STR ''x'') = SPos"
  by eval

end
