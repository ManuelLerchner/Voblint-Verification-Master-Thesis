(* src/Abstract_Interpreter/Framework/Cooperation/Analysis_Query.thy *)
definition oracle_holds :: "('q \<Rightarrow> 'r) \<Rightarrow> store \<Rightarrow> bool" where
  "oracle_holds ask s \<longleftrightarrow> (\<forall>q. answer_holds q (ask q) s)"
