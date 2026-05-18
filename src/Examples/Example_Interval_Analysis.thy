section \<open>Example: Interval Analysis of a Simple IMP2 Program\<close>

text \<open>\label{sec:example-interval}\<close>

theory Example_Interval_Analysis
  imports Interval_Domain IMP2_to_CFG TD_Interface
begin

text \<open>
  Interval analysis of the same toy program used for the sign example:
  \<^verbatim>\<open>x := 5; y := x + x\<close>.  The interval domain produces a tight result
  \<^verbatim>\<open>x \<in> [5,5], y \<in> [10,10]\<close>; the precise @{const ivl_plus} (proven sound)
  yields a singleton interval for the sum even though it could safely
  over-approximate.
\<close>

definition example_prog :: com where
  "example_prog = (''x'' ::= N 5) ;; (''y'' ::= Plus (V ''x'') (V ''x''))"


subsection \<open>Real pipeline (type-checked)\<close>

term "td_analyse example_prog ivl_tf
        ((\<squnion>) :: ivl abs_state \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state)
        (bot :: ivl abs_state)
        (\<lambda>_. ivl_top) (cfg_exit (to_cfg example_prog))"


subsection \<open>Transfer-function spot checks\<close>

value "aval_ivl (N 5) (\<lambda>_. ivl_bot)"
\<comment> \<open>singleton \<^verbatim>\<open>[5,5]\<close>\<close>

value "aval_ivl (Plus (V ''x'') (V ''x''))
                (\<lambda>v. if v = ''x'' then Ivl (Fin 5) (Fin 5) else ivl_top)"
\<comment> \<open>singleton \<^verbatim>\<open>[10,10]\<close>\<close>

value "assign_ivl ''x'' (N 5) (\<lambda>_. ivl_top) ''x''"
\<comment> \<open>\<^verbatim>\<open>[5,5]\<close>\<close>


subsection \<open>Pair abstract state for executable equality\<close>

text \<open>
  As in the sign example we project the two-variable map to a pair so that
  @{class equal} is available and the TD solver can compare convergence.
\<close>

datatype iss = ISS (fst_iss: ivl) (snd_iss: ivl)

instantiation iss :: order
begin

definition less_eq_iss where
  "x \<le> y \<longleftrightarrow> fst_iss x \<le> fst_iss y \<and> snd_iss x \<le> snd_iss y"
definition less_iss where
  "(x::iss) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance
proof (intro_classes)
  fix x y z :: iss
  show "x \<le> x" by (simp add: less_eq_iss_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (meson less_eq_iss_def order.trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: less_eq_iss_def order_class.order_eq_iff iss.expand)
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_iss_def)
qed

end

instantiation iss :: bot
begin

definition bot_iss_def: "bot_class.bot = ISS ivl_bot ivl_bot"

instance ..

end


text \<open>Decode a pair as a variable map; other variables are bottom.\<close>

definition to_sigma_ivl :: "iss \<Rightarrow> vname \<Rightarrow> ivl" where
  "to_sigma_ivl s v =
   (if v = ''x'' then fst_iss s else if v = ''y'' then snd_iss s else ivl_bot)"

definition tf_assign_iss :: "vname \<Rightarrow> aexp \<Rightarrow> iss \<Rightarrow> iss" where
  "tf_assign_iss x a s =
     (let \<sigma>' = assign_ivl x a (to_sigma_ivl s) in ISS (\<sigma>' ''x'') (\<sigma>' ''y''))"

value "tf_assign_iss ''x'' (N 5)                              (ISS ivl_top ivl_top)"
\<comment> \<open>x = [5,5], y = top\<close>

value "tf_assign_iss ''y'' (Plus (V ''x'') (V ''x''))
                            (ISS (Ivl (Fin 5) (Fin 5)) ivl_top)"
\<comment> \<open>x = [5,5], y = [10,10]\<close>


subsection \<open>Equation system as strategy trees\<close>

datatype PP = PP0 | PP1 | PP2 | PP3

fun constr_sys :: "PP \<Rightarrow> (PP, iss) strategy_tree" where
  "constr_sys PP0 = Answer (ISS ivl_top ivl_top)"
| "constr_sys PP1 = Query PP0 (\<lambda>s. Answer (tf_assign_iss ''x'' (N 5) s))"
| "constr_sys PP2 = Query PP1 (\<lambda>s. Answer s)"
| "constr_sys PP3 = Query PP2
       (\<lambda>s. Answer (tf_assign_iss ''y'' (Plus (V ''x'') (V ''x'')) s))"


subsection \<open>Solving with TD\_plain\<close>

definition solution :: "PP \<Rightarrow> iss" where
  "solution pp =
     (case (TD_plain_Interp_solve constr_sys PP3) pp of None \<Rightarrow> bot | Some v \<Rightarrow> v)"

value "solution PP0"   \<comment> \<open>x = top, y = top --- entry\<close>
value "solution PP1"   \<comment> \<open>x = [5,5], y = top --- after \<^verbatim>\<open>x := 5\<close>\<close>
value "solution PP2"   \<comment> \<open>unchanged across nop\<close>
value "solution PP3"   \<comment> \<open>x = [5,5], y = [10,10]\<close>

value "[solution PP0, solution PP1, solution PP2, solution PP3]"


subsection \<open>Asserted expected outputs\<close>

text \<open>Mechanical checks that the solver computes the expected intervals.\<close>

lemma solution_PP0: "solution PP0 = ISS ivl_top ivl_top"
  by eval

lemma solution_PP1:
  "solution PP1 = ISS (Ivl (Fin 5) (Fin 5)) ivl_top"
  by eval

lemma solution_PP2:
  "solution PP2 = ISS (Ivl (Fin 5) (Fin 5)) ivl_top"
  by eval

lemma solution_PP3:
  "solution PP3 = ISS (Ivl (Fin 5) (Fin 5)) (Ivl (Fin 10) (Fin 10))"
  by eval

end
