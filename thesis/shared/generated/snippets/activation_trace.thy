(* src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy *)
datatype activation_trace =
    Root activation_path
  | Call (activation_trace_caller: activation_trace) activation_path
  | Resume (activation_trace_current: activation_trace) (activation_trace_callee: activation_trace)
    activation_path
