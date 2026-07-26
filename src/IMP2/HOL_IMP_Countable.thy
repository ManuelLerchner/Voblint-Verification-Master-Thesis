theory HOL_IMP_Countable
  imports "HOL-Library.Countable" "HOL-IMP.AExp" "HOL-IMP.BExp"
          "Deriving.Compare_Order_Instances"
begin

text \<open>A separate theory keeps the two countability instances from sharing generated arity facts.\<close>

instance AExp.aexp :: countable
  by countable_datatype

instance BExp.bexp :: countable
  by countable_datatype

text \<open>These structural orders make the wrapped expression types executable.
  Keeping them here prevents their generated comparator names from colliding with the
  extended expression types.\<close>
derive linorder "AExp.aexp"
derive linorder "BExp.bexp"

end
