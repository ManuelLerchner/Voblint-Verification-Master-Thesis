(* src/Abstract_Interpreter/Exec/State/Default_St_Base.thy *)
fun default_st_rep_get ::
  "('a::bot) default_st_rep => location => 'a" where
  "default_st_rep_get (l, g) (Local_Location x) = default_dict_get l x"
| "default_st_rep_get (l, g) (Global_Location x) = default_dict_get g x"
