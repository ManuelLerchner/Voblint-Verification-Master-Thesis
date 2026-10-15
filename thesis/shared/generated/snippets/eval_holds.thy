(* src/Abstract_Interpreter/Framework/Cooperation/Analysis_Query.thy *)
fun geval_holds :: "('e \<Rightarrow> 's \<Rightarrow> int) \<Rightarrow> 'e gquery \<Rightarrow> answer \<Rightarrow> 's \<Rightarrow> bool" where
  "geval_holds ev (EvalInt e) a s \<longleftrightarrow> ev e s \<in> gamma_answer a"
