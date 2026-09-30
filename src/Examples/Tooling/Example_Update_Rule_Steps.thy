theory Example_Update_Rule_Steps
  imports
    "Voblint_Solver.Globals_Rule"
    "Voblint_Analysis_Interval.Interval_Warrowing"
begin

section \<open>One global under the five update rules, contribution by contribution\<close>

text \<open>
  The update rules differ only in how they merge a side contribution into a global
  unknown. Feeding the same contributions to each rule, outside any solver run, shows
  that difference directly: the values below are what the vendored rules compute,
  selected through \<^const>\<open>update_global_of\<close> and instantiated at the interval domain.
\<close>

datatype example_origin = Origin_A | Origin_B

text \<open>A rule answers \<^const>\<open>None\<close> when the global keeps its value, so the value after a
  step is the previous one in that case.\<close>
fun update_steps ::
    "globals_rule \<Rightarrow> 'd::{bounded_semilattice_sup_bot,warrowing}
       \<Rightarrow> ('x, unit, 'd) ug_state_with_gas \<Rightarrow> ('x \<times> 'd) list \<Rightarrow> 'd list" where
  "update_steps r d st [] = []"
| "update_steps r d st ((orig, c) # cs) =
     (let (upd, st') = update_global_of r d orig () c st;
          d' = (case upd of None \<Rightarrow> d | Some d'' \<Rightarrow> d'')
      in d' # update_steps r d' st' cs)"

definition example_contribs :: "(example_origin \<times> ivl) list" where
  "example_contribs =
     [(Origin_A, Ivl (Fin 0) (Fin 3)), (Origin_B, Ivl (Fin 4) (Fin 4)),
      (Origin_A, Ivl (Fin 1) (Fin 1)), (Origin_A, Ivl (Fin 0) (Fin 8))]"

lemma update_rules_example:
  "map (\<lambda>r. update_steps r \<bottom> init_ug_state_with_gas example_contribs)
     [Globals_Join, Globals_Per_Origin, Globals_Warrow, Globals_Warrow_Per_Origin,
      Globals_Bounded_Narrowing 5] =
   [[Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 8)],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 1) (Fin 4), Ivl (Fin 0) (Fin 8)],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) PlusInf, Ivl (Fin 0) (Fin 4), Ivl (Fin 0) PlusInf],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) PlusInf],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) PlusInf]]"
  by code_simp

end
