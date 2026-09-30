(* src/Examples/Tooling/Example_Update_Rule_Steps.thy *)
lemma update_rules_example:
  "map (\<lambda>r. update_steps r \<bottom> init_basic_ug_state example_contribs)
     [Globals_Join, Globals_Per_Origin, Globals_Warrow, Globals_Warrow_Per_Origin] =
   [[Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 8)],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 1) (Fin 4), Ivl (Fin 0) (Fin 8)],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) PlusInf, Ivl (Fin 0) (Fin 4), Ivl (Fin 0) PlusInf],
    [Ivl (Fin 0) (Fin 3), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) (Fin 4), Ivl (Fin 0) PlusInf]]"
