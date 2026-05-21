section \<open>Example: Sign Analysis of a Simple IMP2 Program\<close>

text \<open>\label{sec:example-sign}\<close>

theory Example_Sign_Analysis
  imports Sign_Domain IMP2_to_CFG TD_Interface
begin

text \<open>
  Sign analysis of a tiny IMP2 program.  The lemmas and definitions in
  @{text \<open>TD_Interface\<close>} and @{text \<open>Pipeline.thy\<close>} use @{const td_analyse} on
  @{typ \<open>sign abs_state\<close>} as intended; nothing forces a separate model for proof.

  Executable @{command value} for @{const TD_plain_Interp_solve} is different: the
  AFP refined solver compares abstract answers for convergence, which in generated
  code needs @{class equal} on the tree range type.  Isabelle does not provide
  executable equality on @{typ \<open>vname \<Rightarrow> sign\<close>}.  So we still evaluate numbers on a
  pair @{typ \<open>sign \<times> sign\<close>} with hand-written strategy trees (as in AFP
  @{verbatim \<open>TD.Example\<close>}).  A finite-map (or finfun on a finite variable type)
  @{typ \<open>'a abs_state\<close>} would make @{command value} on @{const td_analyse} feasible.
\<close>

definition example_prog :: com where
  "example_prog = (''x'' ::= N 5) ;; (''y'' ::= Plus (V ''x'') (V ''x''))"

subsection \<open>Real pipeline (type-checked)\<close>

text \<open>Same @{const td_analyse} / @{const make_rhs_tree} stack as the rest of the
  session; @{command term} checks the composition without executing it.\<close>

term "td_analyse example_prog sign_tf
        ((\<squnion>) :: sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state)
        (bot :: sign abs_state)
        (\<lambda>_. STop) (cfg_exit (to_cfg example_prog))"

term "make_rhs_tree (to_cfg example_prog) sign_tf
        ((\<squnion>) :: sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state)
        (bot :: sign abs_state)
        (\<lambda>_. STop) (cfg_exit (to_cfg example_prog))"

text \<open>\<^verbatim>\<open>x := 5;
y := x + x\<close>\<close>


subsection \<open>CFG inspection\<close>

text \<open>Inspect @{const compile} / @{const to_cfg} for @{const example_prog}.
  The @{const compile} function allocates program points starting from 0.
  Each statement gets entry/exit nodes connected by a labelled edge;
  sequential composition inserts a @{const EA_Nop} splice edge.
\<close>

value "compile example_prog 0"
(*  (4, 0, 3,
     {(0, EA_Assign ''x'' (N 5), 1),
      (1, EA_Nop, 2),
      (2, EA_Assign ''y'' (Plus (V ''x'') (V ''x'')), 3)})  *)

value "cfg_entry (to_cfg example_prog)"   \<comment> \<open>0\<close>
value "cfg_exit  (to_cfg example_prog)"   \<comment> \<open>3\<close>
value "edges (to_cfg example_prog)"


subsection \<open>Sign Transfer Functions --- Spot Checks\<close>

text \<open>These calls exercise the project transfer functions.\<close>

value "aval_sign (N 5) (\<lambda>_. SBot)"
\<comment> \<open>@{const SPos}: literal 5 is positive\<close>

value "aval_sign (Plus (V ''x'') (V ''x'')) (\<lambda>v. if v = ''x'' then SPos else SBot)"
\<comment> \<open>@{const SPos}: positive + positive\<close>

value "assign_sign ''x'' (N 5) (\<lambda>_. STop)"
\<comment> \<open>@{const SPos} at @{term \<open>''x''\<close>}, other variables @{const STop}\<close>

value "assign_sign ''y'' (Plus (V ''x'') (V ''x'')) ((\<lambda>_. STop)(''x'' := SPos))"
\<comment> \<open>@{const SPos} at @{term \<open>''y''\<close>}\<close>


subsection \<open>Abstract Domain for the Example\<close>

text \<open>
  The program uses exactly @{term \<open>''x''\<close>} and @{term \<open>''y''\<close>}, so we represent
  abstract states as pairs @{typ \<open>sign \<times> sign\<close>} (first component is @{term \<open>''x''\<close>},
  second @{term \<open>''y''\<close>}).  This type has @{class equal}, satisfying the TD solver's
  executable convergence check.
\<close>

datatype ss = SS (fst_ss: sign) (snd_ss: sign)

instantiation ss :: order
begin

definition less_eq_ss where "x \<le> y \<longleftrightarrow> fst_ss x \<le> fst_ss y \<and> snd_ss x \<le> snd_ss y"
definition less_ss where "(x::ss) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance
proof (intro_classes)
  fix x y z :: ss
  show "x \<le> x"
    by (simp add: less_eq_ss_def sign_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (meson less_eq_ss_def order.trans)
  
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: less_eq_ss_def order_class.order_eq_iff ss.expand)
 
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_ss_def)
qed

end

instantiation ss :: bot
begin

definition bot_ss_def: "bot_class.bot = SS SBot SBot"

instance ..

end

text \<open>Decode a pair as a variable map (other variables map to @{const SBot}).\<close>

definition to_sigma :: "ss \<Rightarrow> vname \<Rightarrow> sign" where
  "to_sigma s v =
   (if v = ''x'' then fst_ss s else if v = ''y'' then snd_ss s else SBot)"

text \<open>Assignment on pairs via the real @{const assign_sign} on @{const to_sigma}.\<close>

definition tf_assign_ss :: "vname \<Rightarrow> aexp \<Rightarrow> ss \<Rightarrow> ss" where
  "tf_assign_ss x a s =
     (let \<sigma>' = assign_sign x a (to_sigma s) in SS (\<sigma>' ''x'') (\<sigma>' ''y''))"

value "tf_assign_ss ''x'' (N 5)                              (SS STop STop)"
\<comment> \<open>(@{const SPos}, @{const STop})\<close>

value "tf_assign_ss ''y'' (Plus (V ''x'') (V ''x'')) (SS SPos STop)"
\<comment> \<open>(@{const SPos}, @{const SPos})\<close>


subsection \<open>Equation System as Strategy Trees\<close>

text \<open>
  The CFG for @{const example_prog} is
  PP0 @{text \<open>--[x := 5]-->\<close>} PP1 @{text \<open>--[nop]-->\<close>} PP2 @{text \<open>--[y := x+x]-->\<close>} PP3.
  We encode right-hand sides as strategy trees; the initial pair @{term \<open>(STop, STop)\<close>}
  is an unconstrained input abstraction at the entry.
\<close>

datatype PP = PP0 | PP1 | PP2 | PP3

fun constr_sys :: "PP \<Rightarrow> (PP, ss) strategy_tree" where
  "constr_sys PP0 = Answer (SS STop STop)"
| "constr_sys PP1 = Query PP0 (\<lambda>s. Answer (tf_assign_ss ''x'' (N 5) s))"
| "constr_sys PP2 = Query PP1 (\<lambda>s. Answer s)"
| "constr_sys PP3 = Query PP2 (\<lambda>s. Answer (tf_assign_ss ''y'' (Plus (V ''x'') (V ''x'')) s))"


subsection \<open>Solving with TD\_plain\<close>

text \<open>
  Querying the exit node @{term PP3} drives the solver backwards through
  predecessors.  The domain is finite, so no widening is required.
\<close>

definition solution :: "PP \<Rightarrow> ss" where
  "solution pp =
     (case (TD_plain_Interp_solve constr_sys PP3) pp of None \<Rightarrow> bot | Some v \<Rightarrow> v)"

value "solution PP0"   \<comment> \<open>(@{const STop}, @{const STop}) --- entry\<close>
value "solution PP1"   \<comment> \<open>(@{const SPos}, @{const STop}) --- after @{term \<open>''x'' ::= N 5\<close>}\<close>
value "solution PP2"   \<comment> \<open>unchanged through @{const EA_Nop}\<close>
value "solution PP3"   \<comment> \<open>both variables positive\<close>

text \<open>
  Querying @{term PP0} alone touches only the entry node: nodes @{term PP1}--@{term PP3}
  are never evaluated.
\<close>

definition solution_from_entry :: "PP \<Rightarrow> ss" where
  "solution_from_entry pp =
     (case (TD_plain_Interp_solve constr_sys PP0) pp of None \<Rightarrow> bot | Some v \<Rightarrow> v)"

value "(solution_from_entry PP0, solution_from_entry PP1,
        solution_from_entry PP2, solution_from_entry PP3)"
\<comment> \<open>Nested @{typ \<open>ss * (ss * (ss * ss))\<close>}; the trailing @{const SBot}, @{const SBot} are one @{typ ss}.\<close>

value "[solution_from_entry PP0, solution_from_entry PP1,
        solution_from_entry PP2, solution_from_entry PP3]"
\<comment> \<open>same four @{typ ss} values in a list (easier to read than nested pairs)\<close>

end
