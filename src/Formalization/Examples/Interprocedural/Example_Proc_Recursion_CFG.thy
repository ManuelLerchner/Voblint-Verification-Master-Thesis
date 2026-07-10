section \<open>Example: recursive procedure CFG layout\<close>

theory Example_Proc_Recursion_CFG
  imports "Voblint_CFG.IMP2_Proc_to_CFG" "Voblint_IMP2.IMP2_Notation"
begin

text \<open>
  Source-level regression for procedure layout.  The procedure list is known
  before any body is compiled, so calls may target the current procedure, a
  later procedure, or a mutually recursive sibling.
\<close>

definition proc_layout_regression_prog :: imp_prog where
  "proc_layout_regression_prog = \<lbrakk>
     int G;
     void f() {
       if (G < 1) { f() } else { G := G }
     }
     void g() { h() }
     void h() { g() }
     void inc() { G := G + 1 }
     void main() { f(); g(); inc() }
   \<rbrakk>"

definition proc_layout_regression_cfg :: cfg where
  "proc_layout_regression_cfg =
     compile_prog (prog_table proc_layout_regression_prog)
       (prog_procs proc_layout_regression_prog)
       (prog_main proc_layout_regression_prog)"

lemma proc_layout_regression_direct_recursion:
  "(1, EA_Enter, 0) \<in> edges proc_layout_regression_cfg \<and>
   (1, 5, 2) \<in> combines proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

lemma proc_layout_regression_mutual_recursion:
  "(6, EA_Enter, 8) \<in> edges proc_layout_regression_cfg \<and>
   (8, EA_Enter, 6) \<in> edges proc_layout_regression_cfg \<and>
   (6, 9, 7) \<in> combines proc_layout_regression_cfg \<and>
   (8, 7, 9) \<in> combines proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

lemma proc_layout_regression_forward_call:
  "(6, EA_Enter, 8) \<in> edges proc_layout_regression_cfg \<and>
   (6, 9, 7) \<in> combines proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

lemma proc_layout_regression_ordinary_call:
  "(16, EA_Enter, 10) \<in> edges proc_layout_regression_cfg \<and>
   (16, 11, 17) \<in> combines proc_layout_regression_cfg"
  unfolding proc_layout_regression_cfg_def proc_layout_regression_prog_def by eval

lemma proc_layout_regression_regions:
  "compile_prog_regions (prog_table proc_layout_regression_prog)
     (prog_procs proc_layout_regression_prog)
     (prog_main proc_layout_regression_prog) =
   [(None, [12, 13, 14, 15, 16, 17]),
    (Some ''f'', [0, 1, 2, 3, 4, 5]),
    (Some ''g'', [6, 7]),
    (Some ''h'', [8, 9]),
    (Some ''inc'', [10, 11])]"
  unfolding proc_layout_regression_prog_def by eval

end
