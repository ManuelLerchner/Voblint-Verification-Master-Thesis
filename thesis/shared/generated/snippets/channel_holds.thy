(* src/Abstract_Interpreter/Framework/Cooperation/Analysis_Query.thy *)
definition channel_holds :: "('q \<Rightarrow> 'r) \<Rightarrow> store \<Rightarrow> bool" where
  "channel_holds ch s \<longleftrightarrow> (\<forall>q. answer_holds q (ch q) s)"
