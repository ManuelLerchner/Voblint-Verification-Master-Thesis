(* src/Abstract_Interpreter/Domain/Abstract_Domain.thy *)
class executable_domain = warrowing +
  fixes is_empty :: "'a::{bounded_semilattice_sup_bot, order_top} \<Rightarrow> bool"
  fixes to_string :: "'a \<Rightarrow> String.literal"
