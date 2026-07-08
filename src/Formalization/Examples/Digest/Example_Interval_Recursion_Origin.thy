theory Example_Interval_Recursion_Origin
  imports
    "Voblint_Analysis.Origin_Lift"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Interval_Side_Soundness"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_CFG.IMP2_Proc_to_CFG"
    "Voblint_IMP2.IMP2_Notation"
begin

section \<open>Per-origin widening on the recursive interval program\<close>

text \<open>
  A companion to \<open>Example_Interval_Recursion_Digest\<close>.  The same recursive procedure
  counts a global \<open>G\<close> up to 3.  There the digest keyed \<open>G\<close> by its value and still lost
  precision; here we test the other candidate fix --- \<^emph>\<open>per-origin widening\<close>
  (\<^theory>\<open>Voblint_Analysis.Origin_Lift\<close>): each write origin keeps its own cell, widening
  is pointwise per origin, and a read collapses the cells.

  The headline, sealed by \<open>eval\<close>, is again a genuine wall, and the origin lift pins down
  \<^emph>\<open>where\<close> the precision is lost: per-origin widening separates the recursion's writes into
  their own cells and terminates, but the read \<^emph>\<open>collapses across origins\<close> before every
  transfer, so the recursive edge's own climbing contribution is fed back into its next
  input.  The monotone self-loop survives the origin split, and \<open>G\<close> still widens to the
  top interval --- the same result as monovariant warrowing.
\<close>

subsection \<open>The recursive program (shared with the digest example)\<close>

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

subsection \<open>Monovariant warrowing widens \<open>G\<close> to the top interval\<close>

definition rec_warrow_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl st)" where
  "rec_warrow_sol = TD_side_warrowing_apinis_Interp_solve rec_eqs (cfg_exit rec_cfg)"

lemma rec_warrowing_widens_to_top:
  "lookup_st (snd rec_warrow_sol (Inr ())) ''G'' = Ivl MinInf PlusInf"
  unfolding rec_warrow_sol_def rec_eqs_def rec_cfg_def by eval

subsection \<open>Per-origin widening: origin = the program point that writes\<close>

text \<open>\<open>org_of = id\<close> gives one origin per equation unknown (program point).  The lifted
  system runs under the same Apinis warrowing solver; with finitely many origins it
  terminates, so \<open>eval\<close> computes the result.\<close>

definition rec_po_sol ::
  "pp set \<times> (pp + unit \<Rightarrow> (pp, ivl st) origin_st)" where
  "rec_po_sol = TD_side_per_origin_widen_solve id rec_eqs (cfg_exit rec_cfg)"

definition rec_po_read :: "pp + unit \<Rightarrow> ivl st" where
  "rec_po_read k = collapse_origins (snd rec_po_sol k)"

text \<open>The observable \<open>G\<close> under per-origin widening is \<^emph>\<open>the same\<close> top interval as under
  monovariant warrowing: separating the write origins does not break the self-loop,
  because the read collapses them back together before the increment transfer.\<close>
theorem rec_per_origin_still_widens_to_top:
  "lookup_st (rec_po_read (Inr ())) ''G'' = Ivl MinInf PlusInf"
  unfolding rec_po_read_def rec_po_sol_def rec_eqs_def rec_cfg_def
  by eval

text \<open>The two disciplines agree on \<open>G\<close>: per-origin widening is no more precise here.\<close>
theorem rec_per_origin_matches_monovariant:
  "lookup_st (rec_po_read (Inr ())) ''G''
   = lookup_st (snd rec_warrow_sol (Inr ())) ''G''"
  unfolding rec_po_read_def rec_po_sol_def rec_warrow_sol_def rec_eqs_def rec_cfg_def
  by eval

text \<open>
  \<^bold>\<open>Where the information is lost.\<close>  Per-origin widening keeps each write site's
  contribution separate under a terminating solve --- that part works.  But the transfer
  reads \<^const>\<open>collapse_origins\<close>, the join over \<^emph>\<open>all\<close> origins, including the recursive
  edge's own cell.  So at recursion depth \<open>k\<close> the increment reads \<open>[0,k]\<close> (already merged),
  writes \<open>[1,k+1]\<close> to its single origin cell, and that cell climbs unbounded --- widened to
  top.  Recovering per-depth precision would need the \<^emph>\<open>reads\<close> to stay origin-separated too
  (a relational, per-origin transfer), not just the widening; that is beyond a value-domain
  lift and is the real content of \<open>docs/OPEN_PROBLEMS.md\<close> P11.
\<close>

subsection \<open>GraphViz of the per-origin (collapsed) analysis\<close>

text \<open>The per-node collapsed intervals rendered as an analysis-annotated CFG.  Each node
  carries \<^const>\<open>collapse_origins\<close> of its per-origin cells, so \<open>G\<close> shows the widened
  \<open>[-inf, +inf]\<close> at the recursive slot --- visibly identical to the monovariant render.\<close>

definition rec_po_dot :: String.literal where
  "rec_po_dot = annotated_dot_of_prog_lit
     (prog_table rec_prog) (prog_procs rec_prog) (prog_main rec_prog) rec_po_read"

text \<open>@{command ML_val} \<open>writeln (@{code rec_po_dot})\<close> emits the DOT source.\<close>

ML_val \<open>writeln (@{code rec_po_dot})\<close>

end
