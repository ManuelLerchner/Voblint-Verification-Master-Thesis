(* src/Examples/Tooling/Example_Update_Rule_Steps.thy *)
lemma update_rules_example:
  "map (\<lambda>r. update_steps r \<bottom> init_ug_state_with_gas example_contribs)
     [Globals_Join, Globals_Per_Origin, Globals_Warrow, Globals_Warrow_Per_Origin,
      Globals_Bounded_Narrowing 5] =
   [[Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 8)],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 1) (Fin 4), Ivl (Fin 0) (Fin 8)],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) PlusInf, Ivl (Fin 0) (Fin 4), Ivl (Fin 0) PlusInf],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) PlusInf],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) PlusInf]]"
