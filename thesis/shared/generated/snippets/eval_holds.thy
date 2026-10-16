(* src/Abstract_Interpreter/Framework/Cooperation/Analysis_Query.thy *)
fun eval_holds :: "query \<Rightarrow> answer \<Rightarrow> store \<Rightarrow> bool" where
  "eval_holds (EvalInt e) a s \<longleftrightarrow> eval e s \<in> gamma_answer a"
