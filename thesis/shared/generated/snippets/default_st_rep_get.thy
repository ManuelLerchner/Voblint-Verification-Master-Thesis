(* src/Abstract_Interpreter/Exec/State/Default_St_Base.thy *)
fun default_st_rep_get ::
  "('a::bot) default_st_rep => location => 'a" where
  "default_st_rep_get (dl, dg, ps) loc =
     (case map_of ps loc of
        Some a => a
      | None => (case loc of
          Local_Location x => dl
        | Global_Location x => dg))"
