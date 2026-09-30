(* src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy *)
fun caller_of :: "activation_trace \<Rightarrow> activation_trace option" where
  "caller_of (Root _)             = None"
| "caller_of (Call caller _)      = Some caller"
| "caller_of (Resume current _ _) = caller_of current"
