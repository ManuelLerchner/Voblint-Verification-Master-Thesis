theory Example_Order_Asks_Interval
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.Analysis_Run"
begin

text \<open>
  Cooperation in the direction from a numeric analysis to the relational one.
  Each branch assigns separated constants, so at \<open>y = \<dots>\<close> the order analysis
  asks how the new value compares with \<open>x\<close>, Interval answers \<open>x <= y\<close> with the
  exact \<open>1\<close>, and the order analysis records the pair. Both branches record it,
  so it survives the join. Interval's own join gives \<open>x \<in> [0, 20]\<close> and
  \<open>y \<in> [10, 30]\<close>, which overlap; the order analysis alone never learns the
  pair, because it answers only comparisons between variables whose order it
  already records. Run together, the check is proved.
\<close>

definition order_asks_prog :: imp_prog where
  "order_asks_prog =
     program {
       fun main() {
         if (0 < c) {
           x = 0;
           y = 10;
         } else {
           x = 20;
           y = 30;
         }
         __voblint_check(x <= y);
       }
     }"

definition order_asks_verdicts where
  "order_asks_verdicts ds =
     (case run_voblint (Analysis_Config ds Globals_Warrow Ctx_None) order_asks_prog of
        Analysed res \<Rightarrow> Some (map check_verdict (report_checks res))
      | Malformed_Program \<Rightarrow> None)"

lemma order_asks_interval_alone:
  "order_asks_verdicts [Interval_Analysis] = Some [Decided Check_Unknown]"
  by eval

lemma order_asks_order_alone:
  "order_asks_verdicts [Order_Analysis] = Some [Decided Check_Unknown]"
  by eval

lemma order_asks_needs_both:
  "order_asks_verdicts [Interval_Analysis, Order_Analysis] = Some [Decided Check_Proved]"
  by eval

end
