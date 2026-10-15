(* src/Abstract_Interpreter/Domain/Lattice/Kind_Lifted.thy *)
class ik_domain = numeric_domain +
  fixes widen_ik :: "ikind \<Rightarrow> 'a::{bounded_semilattice_sup_bot, order_top} \<Rightarrow> 'a \<Rightarrow> 'a"
    and narrow_ik :: "ikind \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and empty_ik :: "ikind \<Rightarrow> 'a \<Rightarrow> bool"
  assumes widen_ik_ge1: "a \<le> widen_ik k a b"
    and widen_ik_ge2: "b \<le> widen_ik k a b"
    and narrow_ik_ge: "b \<le> a \<Longrightarrow> b \<le> narrow_ik k a b"
    and narrow_ik_le: "b \<le> a \<Longrightarrow> narrow_ik k a b \<le> a"
    and empty_ik_correct: "empty_ik k a \<longleftrightarrow> \<gamma> a \<inter> ik_range k = {}"
