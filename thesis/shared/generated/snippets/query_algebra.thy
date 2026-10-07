(* src/Abstract_Interpreter/Framework/Cooperation/Analysis_Query.thy *)
locale query_algebra =
  fixes answer_holds :: "'q \<Rightarrow> 'r::{semilattice_inf, order_top} \<Rightarrow> store \<Rightarrow> bool"
  assumes top_sound: "answer_holds q \<top> s"
      and inf_sound: "\<lbrakk>answer_holds q a s; answer_holds q b s\<rbrakk> \<Longrightarrow> answer_holds q (a \<sqinter> b) s"
