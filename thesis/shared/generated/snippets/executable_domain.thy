(* src/Abstract_Interpreter/Domain/Abstract_Domain.thy *)
class executable_domain = bounded_semilattice_sup_bot + order_top +
  fixes is_empty :: "'a \<Rightarrow> bool"
  fixes to_string :: "'a \<Rightarrow> String.literal"
