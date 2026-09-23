(* src/Abstract_Interpreter/Exec/State/Exec_St_Base.thy *)
fun lookup_resolved_st ::
  "('a::bot) resolved_st => location => 'a" where
  "lookup_resolved_st (dl, dg, ps) loc =
     (case map_of ps loc of
        Some a => a
      | None => (case loc of
          Local_Location x => dl
        | Global_Location x => dg))"
