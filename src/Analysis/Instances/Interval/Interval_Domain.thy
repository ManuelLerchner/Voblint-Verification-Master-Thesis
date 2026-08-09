theory Interval_Domain
  imports Interval_Warrowing Interval_Print
begin

hide_const (open) Update_rules.N

section \<open>Integrated Interval domain\<close>

text \<open>This theory provides one import surface for interval bounds, lattice structure,
  widening, narrowing, arithmetic, backward filtering, transfers, and printing.\<close>

subsection \<open>Executable examples\<close>

value "(Fin 3 :: eint) + Fin (-1)"
value "(PlusInf :: eint) + Fin 100"
value "(Fin 5 :: eint) - Fin 3"
value "(Fin 0 :: eint) - PlusInf"

value "Ivl (Fin 1) (Fin 3) + Ivl (Fin 2) (Fin 5)"
value "Ivl (Fin 5) (Fin 10) - Ivl (Fin 1) (Fin 3)"
value "Ivl (Fin (-2)) (Fin 3) * Ivl (Fin (-1)) (Fin 4)"

value "join_ivl (Ivl (Fin 1) (Fin 3)) (Ivl (Fin 2) (Fin 5))"
value "widen_ivl_core (Ivl (Fin 0) (Fin 1)) (Ivl (Fin 0) (Fin 2))"
value "widen_ivl_core (Ivl (Fin 1) (Fin 3)) (Ivl (Fin 0) (Fin 3))"
value "meet_ivl (Ivl (Fin 0) (Fin 10)) (Ivl (Fin 3) (Fin 7))"

value "string_of_eint MinInf"
value "string_of_eint PlusInf"
value "string_of_ivl (Ivl (Fin (-3)) PlusInf)"

value "aval_ivl (Minus (V (STR ''x'')) (N 1)) ((\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 5) (Fin 10)))"
value "(assume_ivl (Less (V (STR ''x'')) (N 5)) ((\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 0) (Fin 10)))) (STR ''x'')"

end

