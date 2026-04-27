theory Goblint_Formalization
  imports
    "HOL-IMP.Com"
    "HOL-IMP.Big_Step"
begin

(* ---------------------------------------------------------------
   HOL-IMP provides (from ~/Isabelle2025-2/src/HOL/IMP/):
     Com.thy          -- IMP syntax: com datatype (SKIP, Assign, Seq, If, While)
     AExp/BExp.thy    -- arithmetic/boolean expressions + aval/bval
     Big_Step.thy     -- big-step operational semantics  (c, s) => t
     Small_Step.thy   -- small-step semantics
     ACom.thy         -- annotated commands (for analysis results)
     Abs_Int*.thy     -- abstract interpretation framework
     Complete_Lattice.thy -- complete lattice + lfp/gfp (basis of AI)
   --------------------------------------------------------------- *)


(* --- Example program: in-place variable swap using a temp --- *)

definition swap_prog :: com where
  "swap_prog = (''tmp'' ::= V ''x'';; ''x'' ::= V ''y'';; ''y'' ::= V ''tmp'')"


(* The program always terminates. Proved by constructing the derivation
   with a schematic final state (rule exI makes ?t fresh/schematic). *)
lemma swap_terminates: "EX t. big_step (swap_prog, s) t"
  unfolding swap_prog_def
  apply (rule exI)
  apply (rule Seq, rule Seq, rule Assign, rule Assign, simp, rule Assign)
  done

(* If the program terminates at t, then x and y are swapped.
   Proved by case analysis on the big-step derivation. *)
lemma swap_swaps:
  assumes h: "big_step (swap_prog, s) t"
  shows "t ''x'' = s ''y'' & t ''y'' = s ''x''"
  using h unfolding swap_prog_def
  by (auto elim!: big_step.cases)

end
