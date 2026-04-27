theory Scratch
  imports Main
begin

(* Knaster-Tarski: every monotone function on a complete lattice has a fixed point.
   This is the mathematical backbone of abstract interpretation. *)
lemma knaster_tarski:
  fixes f :: "'a::complete_lattice => 'a"
  assumes mono: "mono f"
  shows "EX x. f x = x"
proof -
  let ?a = "Inf {x. f x <= x}"
  have fa_le: "f ?a <= ?a"
  proof (rule Inf_greatest)
    fix x
    assume mem: "x : {x. f x <= x}"
    have h1: "f x <= x" using mem by simp
    have h2: "?a <= x" using mem by (rule Inf_lower)
    have h3: "f ?a <= f x" by (rule monoD[OF mono h2])
    show "f ?a <= x" using h3 h1 by simp
  qed
  have a_le_fa: "?a <= f ?a"
  proof (rule Inf_lower)
    have "f (f ?a) <= f ?a" by (rule monoD[OF mono fa_le])
    thus "f ?a : {x. f x <= x}" by simp
  qed
  have "f ?a = ?a" by (rule order_antisym[OF fa_le a_le_fa])
  thus ?thesis by metis
qed

(* Cantor's diagonal argument: no function 'a => 'a set is surjective. *)
theorem cantor: "~ surj (f :: 'a => 'a set)"
proof
  assume surj: "surj f"
  obtain y where hy: "f y = {x. x ~: f x}"
    using surj by (metis surj_def)
  show False by (metis hy mem_Collect_eq)
qed

end
