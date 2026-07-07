theory Example_Interval_Recursion_Digest
  imports
    "Voblint_Analysis.Value_Digest_Reader"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Digest_Keyed_Writer_Sound"
    "Voblint_Analysis.Solver_Menu"
    "Voblint_Analysis.Interval_Side_Soundness"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_CFG.IMP2_Proc_to_CFG"
    "Voblint_IMP2.IMP2_Notation"
begin

section \<open>A recursive interval analysis and the depth-digest goal\<close>

text \<open>
  A recursive procedure counts a global \<open>G\<close> up to 3.  This example demonstrates why recursion
  is hard for a context-free numeric analysis, and states the digest that would fix it --- with
  an honest account of what is and is not executable in the current solver.
\<close>

subsection \<open>The recursive program\<close>

definition rec_prog :: imp_prog where
  "rec_prog = \<lbrakk>
     int G;
     void p() {
       if (G < 3) { G := G + 1; p() } else { G := G }
     }
     void main() {
       G := 0;
       p()
     }
   \<rbrakk>"

definition rec_cfg :: cfg where
  "rec_cfg = compile_prog (prog_table rec_prog) (prog_procs rec_prog) (prog_main rec_prog)"

definition rec_eqs :: "(pp, unit, ivl st) eqsT" where
  "rec_eqs = side_cfg_T_eff_st rec_cfg ivl_etf_st bot cinit_ivl_st ()"

subsection \<open>Context-free solvers cannot analyse it well\<close>

text \<open>
  \<^bold>\<open>Plain join.\<close>  \<^const>\<open>TD_side_always_join_Interp_solve\<close> \<^emph>\<open>does not terminate\<close> on this program:
  the global \<open>G\<close> climbs \<open>0, 1, 2, \<dots>\<close> through the recursive calls, all merged into one
  flow-insensitive slot, and the executable solver loops (an \<open>Interrupt_Breakdown\<close> under
  \<open>by eval\<close>).  No lemma below evaluates it.

  \<^bold>\<open>Widening.\<close>  Apinis warrowing terminates --- but only by widening \<open>G\<close> to the top interval.
\<close>

definition rec_warrow_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl st)" where
  "rec_warrow_sol = TD_side_warrowing_apinis_Interp_solve rec_eqs (cfg_exit rec_cfg)"

lemma rec_warrowing_widens_to_top:
  "lookup_st (snd rec_warrow_sol (Inr ())) ''G'' = Ivl MinInf PlusInf"
  unfolding rec_warrow_sol_def rec_eqs_def rec_cfg_def by eval

subsection \<open>The depth digest that would recover precision\<close>

text \<open>
  The intended fix is a digest keyed on the recursion variable: project \<open>G\<close> to a finite depth
  bucket, giving each recursion depth its own context and its own global partition.  With
  \<open>[k, k] \<mapsto> Rk\<close> for \<open>k \<in> {0,1,2,3}\<close>, each depth would keep \<open>G\<close> at its exact value --- full
  precision, and finitely many contexts, so the join solver would terminate.

  \<^bold>\<open>Status (open).\<close>  The value-digest generator keys global \<^emph>\<open>writes\<close> by the write-point digest,
  but the recursive self-\<^emph>\<open>call\<close> is not split into a fresh per-depth context, so the executable
  digest solve still climbs \<open>G\<close> without bound and breaks down under \<open>by eval\<close> --- the same
  executable wall as \<open>docs/OPEN_PROBLEMS.md\<close> P11 (per-origin widening).  Making per-depth call
  contexts materialise for a self-call is the open item; the digest \<^emph>\<open>codomain\<close> and \<^emph>\<open>decode\<close>
  below record the intended design.
\<close>

datatype rmode = R0 | R1 | R2 | R3 | RTop

instance rmode :: finite
proof
  show "finite (UNIV :: rmode set)"
  proof (rule finite_subset[of _ "{R0, R1, R2, R3, RTop}"])
    show "(UNIV :: rmode set) \<subseteq> {R0, R1, R2, R3, RTop}" using rmode.exhaust by blast
    show "finite {R0, R1, R2, R3, RTop}" by simp
  qed
qed

text \<open>The ``good digest'': every reachable depth \<open>[k,k]\<close> gets its own bucket \<open>Rk\<close>.\<close>
definition rdec :: "ivl \<Rightarrow> rmode" where
  "rdec i = (case i of Ivl l u \<Rightarrow>
     if l = Fin 0 \<and> u = Fin 0 then R0
     else if l = Fin 1 \<and> u = Fin 1 then R1
     else if l = Fin 2 \<and> u = Fin 2 then R2
     else if l = Fin 3 \<and> u = Fin 3 then R3
     else RTop)"

text \<open>The decode does separate the four depths --- the precision is there in principle, waiting
  on per-depth call contexts.\<close>
lemma rdec_separates_depths:
  "rdec (Ivl (Fin 0) (Fin 0)) = R0 \<and> rdec (Ivl (Fin 1) (Fin 1)) = R1
   \<and> rdec (Ivl (Fin 2) (Fin 2)) = R2 \<and> rdec (Ivl (Fin 3) (Fin 3)) = R3
   \<and> rdec (Ivl (Fin 0) (Fin 3)) = RTop"
  by (simp add: rdec_def)

end
