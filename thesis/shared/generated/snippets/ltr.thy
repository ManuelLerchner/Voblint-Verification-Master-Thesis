(* src/Program_Model/CFG/Collecting/LTR_Def.thy *)
datatype ltr =
    Root trace
  | Call (ltr_caller: ltr) trace
  | Resume (ltr_current: ltr) (ltr_callee: ltr) trace
