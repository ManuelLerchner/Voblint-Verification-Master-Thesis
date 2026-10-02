theory Interval_Domain
  imports Interval_Transfer
begin

section \<open>Integrated Interval domain\<close>

text \<open>This theory provides one import surface for interval bounds, lattice structure,
  widening, narrowing, arithmetic, backward filtering, transfers, and printing.\<close>

subsection \<open>Executable examples\<close>

lemma "(Fin 3 :: eint) + Fin (-1) = Fin 2" by eval
lemma "(PlusInf :: eint) + Fin 100 = PlusInf" by eval
lemma "(Fin 5 :: eint) - Fin 3 = Fin 2" by eval
lemma "(Fin 0 :: eint) - PlusInf = MinInf" by eval

lemma "Ivl (Fin 1) (Fin 3) + Ivl (Fin 2) (Fin 5) = Ivl (Fin 3) (Fin 8)" by eval
lemma "Ivl (Fin 5) (Fin 10) - Ivl (Fin 1) (Fin 3) = Ivl (Fin 2) (Fin 9)" by eval
lemma "Ivl (Fin (-2)) (Fin 3) * Ivl (Fin (-1)) (Fin 4) = Ivl (Fin (- 8)) (Fin 12)" by eval

lemma "join_ivl (Ivl (Fin 1) (Fin 3)) (Ivl (Fin 2) (Fin 5)) = Ivl (Fin 1) (Fin 5)" by eval
lemma "widen_ivl_core (Ivl (Fin 0) (Fin 1)) (Ivl (Fin 0) (Fin 2)) = Ivl (Fin 0) PlusInf" by eval
lemma "widen_ivl_core (Ivl (Fin 1) (Fin 3)) (Ivl (Fin 0) (Fin 3)) = Ivl MinInf (Fin 3)" by eval
lemma "Ivl (Fin 0) (Fin 10) \<sqinter> Ivl (Fin 3) (Fin 7) = Ivl (Fin 3) (Fin 7)" by eval

lemma "string_of_eint MinInf = STR ''-<infinity>''" by eval
lemma "string_of_eint PlusInf = STR ''+<infinity>''" by eval
lemma "string_of_ivl (Ivl (Fin (-3)) PlusInf) = STR ''[-3,+<infinity>]''" by eval

lemma "aval_ivl (Minus (V (STR ''x'')) (N 1))
      ((\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 5) (Fin 10)))
    = Ivl (Fin 4) (Fin 9)"
  by eval
lemma "(bfilter_ivl (Less (V (STR ''x'')) (N 5)) True
         ((\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 0) (Fin 10)))) (STR ''x'')
    = Ivl (Fin 0) (Fin 4)"
  by eval

end
