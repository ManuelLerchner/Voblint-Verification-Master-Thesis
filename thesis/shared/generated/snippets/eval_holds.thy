(* src/Abstract_Interpreter/Framework/Cooperation/Analysis_Query.thy *)
fun eval_holds :: "query \<Rightarrow> answer \<Rightarrow> store \<Rightarrow> bool" where
  "eval_holds (EvalInt e) a s \<longleftrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> gamma_query_lift gamma_int_dom a"
