(* ~~/src/HOL/Lattices.thy *)
class semilattice_sup = order + sup +
  assumes sup_ge1 [simp]: "x \<le> x \<squnion> y"
  and sup_ge2 [simp]: "y \<le> x \<squnion> y"
  and sup_least: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
