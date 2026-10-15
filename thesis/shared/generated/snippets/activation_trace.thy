(* src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy *)
datatype 'v gactivation_trace =
    Root "'v gactivation_path"
  | Call (activation_trace_caller: "'v gactivation_trace") "'v gactivation_path"
  | Resume (activation_trace_current: "'v gactivation_trace")
    (activation_trace_callee: "'v gactivation_trace") "'v gactivation_path"
