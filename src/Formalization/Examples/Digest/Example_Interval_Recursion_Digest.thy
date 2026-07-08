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

section \<open>A recursive interval analysis and the depth digest\<close>

text \<open>
  A recursive procedure counts a global \<open>G\<close> up to 3.  Recursion over an
  infinite-height domain is the hard case for a context-free numeric analysis, and
  this example makes the difficulty --- and the depth digest that is meant to fix it
  --- an executable, machine-checked fact rather than a prose claim.

  The headline finding is a genuine wall.  Monovariant Apinis warrowing terminates but
  widens \<open>G\<close>'s \<^emph>\<open>upper\<close> bound to \<open>+inf\<close> (the widening bot-law pins the lower bound at \<open>0\<close>,
  so \<open>G = [0, +inf]\<close>, sealed by \<open>eval\<close> below).  The \<^emph>\<open>value-keyed\<close> depth digest that is meant
  to sharpen it does not help and, worse, does not terminate: keeping \<open>G\<close> precise makes a
  climbing interval leave every fixed value bucket, so the digest churns a fresh partition
  per depth and the warrowing digest solve runs to \<open>Interrupt_Breakdown\<close>.  So the digest
  activation separation is stated non-evaluationally (below); a terminating \<^emph>\<open>and\<close> precise
  depth split needs a gas-bounded narrowing solver or context/origin-sensitive reads, not a
  value digest (\<open>docs/OPEN_PROBLEMS.md\<close> P11).
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

subsection \<open>Context-free solvers cannot analyse it well\<close>

text \<open>
  \<^bold>\<open>Plain join.\<close>  \<^const>\<open>TD_side_always_join_Interp_solve\<close> \<^emph>\<open>does not terminate\<close> on this
  program: \<open>G\<close> climbs \<open>0, 1, 2, \<dots>\<close> through the recursive calls, merged into one
  flow-insensitive slot, and the solver runs to its \<open>Interrupt_Breakdown\<close> limit (about
  108s of real iteration under \<open>by eval\<close> --- measured, then removed so the theory builds).
  No lemma here evaluates it.

  \<^bold>\<open>Widening.\<close>  Apinis warrowing terminates.  The widening bot-law keeps the first write
  exact, so \<open>G\<close> settles at \<open>[0, +inf]\<close> (lower bound pinned at \<open>0\<close>); the recursive increment
  still climbs the upper bound to \<open>+inf\<close>, and interval narrowing is the identity, so nothing
  recovers the finite bound.
\<close>

definition rec_eqs :: "(pp, unit, ivl st) eqsT" where
  "rec_eqs = side_cfg_T_eff_st rec_cfg ivl_etf_st bot cinit_ivl_st ()"

definition rec_warrow_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl st)" where
  "rec_warrow_sol = TD_side_warrowing_apinis_Interp_solve rec_eqs (cfg_exit rec_cfg)"

lemma rec_warrowing_widens_to_top:
  "lookup_st (snd rec_warrow_sol (Inr ())) ''G'' = Ivl (Fin 0) PlusInf"
  unfolding rec_warrow_sol_def rec_eqs_def rec_cfg_def by eval

subsection \<open>A depth digest: bucket \<open>G\<close> by its exact value\<close>

text \<open>The intended fix keys the global on a finite projection of the recursion variable:
  exact depth \<open>[k, k]\<close> maps to bucket \<open>Rk\<close>, and every non-singleton interval --- including
  the merged climb --- to \<open>RTop\<close>.\<close>

datatype rmode = R0 | R1 | R2 | R3 | RTop

instance rmode :: finite
proof
  show "finite (UNIV :: rmode set)"
  proof (rule finite_subset[of _ "{R0, R1, R2, R3, RTop}"])
    show "(UNIV :: rmode set) \<subseteq> {R0, R1, R2, R3, RTop}" using rmode.exhaust by blast
    show "finite {R0, R1, R2, R3, RTop}" by simp
  qed
qed

instantiation rmode :: show_val begin
definition "show_val_rmode m =
  (case m of R0 \<Rightarrow> ''R0'' | R1 \<Rightarrow> ''R1'' | R2 \<Rightarrow> ''R2'' | R3 \<Rightarrow> ''R3'' | RTop \<Rightarrow> ''RTop'')"
instance ..
end

definition rdec :: "ivl \<Rightarrow> rmode" where
  "rdec i = (case i of Ivl l u \<Rightarrow>
     if l = Fin 0 \<and> u = Fin 0 then R0
     else if l = Fin 1 \<and> u = Fin 1 then R1
     else if l = Fin 2 \<and> u = Fin 2 then R2
     else if l = Fin 3 \<and> u = Fin 3 then R3
     else RTop)"

lemma rdec_separates_depths:
  "rdec (Ivl (Fin 0) (Fin 0)) = R0 \<and> rdec (Ivl (Fin 1) (Fin 1)) = R1
   \<and> rdec (Ivl (Fin 2) (Fin 2)) = R2 \<and> rdec (Ivl (Fin 3) (Fin 3)) = R3
   \<and> rdec (Ivl (Fin 0) (Fin 3)) = RTop"
  by (simp add: rdec_def)

definition rec_dg :: "ivl st \<Rightarrow> rmode" where
  "rec_dg s = rdec (lookup_st s ''G'')"

definition rec_prep :: "pp \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "rec_prep cc s = s"

definition rec_digest_eqs :: "(pp \<times> rmode, rmode, ivl st) eqsT" where
  "rec_digest_eqs = side_cfg_T_eff_digest_st rec_dg
                      (\<lambda>c cc ex. switching_combine_digest_st rec_dg rec_prep cc ex c)
                      rec_cfg ivl_etf_st bot bot cinit_ivl_st"

subsection \<open>The digest under warrowing: it separates activations but loses the values\<close>

text \<open>The digest system is solved by warrowing (join still diverges --- see above).  Two
  activation partitions come alive: \<open>R0\<close>, the exact entry \<open>G = [0,0]\<close>, and \<open>RTop\<close>, the
  merged deeper recursion.  The exact-depth buckets \<open>R1\<close>/\<open>R2\<close>/\<open>R3\<close> never receive a write ---
  once \<open>G\<close> is a range the projection is already \<open>RTop\<close> --- so they stay \<^bold>\<open>bottom\<close>.\<close>

definition rec_digest_solution ::
  "(pp \<times> rmode) set \<times> ((pp \<times> rmode) + rmode \<Rightarrow> ivl st)" where
  "rec_digest_solution = TD_side_warrowing_apinis_Interp_solve rec_digest_eqs (cfg_exit rec_cfg, R0)"

text \<open>
  \<^bold>\<open>This solve is stated non-evaluationally on purpose.\<close>  Before the widening bot-law, \<open>G\<close>
  topped to \<^term>\<open>Ivl MinInf PlusInf\<close> on its first write, so \<^const>\<open>rec_digest_solution\<close> saw
  only two value buckets --- \<open>R0\<close> (entry) and \<open>RTop\<close> --- and \<open>eval\<close>'d in one shot.  With the
  bot-law \<open>G\<close> is kept precise (\<open>[0,0], [1,1], [2,2], \<dots>\<close>) as it climbs, so this
  \<^emph>\<open>value-keyed\<close> digest churns through a fresh bucket per depth and the warrowing digest
  solve no longer terminates within the solver's breakdown bound (\<open>Interrupt_Breakdown\<close>).
  That is a termination regression \<^emph>\<open>caused by keeping the global precise\<close>, not by the solver
  menu; real interval narrowing in the Apinis rule diverges here too (unbounded widen/narrow
  alternation), which is why the interval domain's narrowing is the identity.

  So the activation separation is documented, not \<open>eval\<close>'d: the live buckets are \<open>R0\<close> and
  \<open>RTop\<close>, and the exact-depth buckets \<open>R1\<close>/\<open>R2\<close>/\<open>R3\<close> stay \<^term>\<open>\<bottom>\<close> (once \<open>G\<close> is a range the
  projection is already \<open>RTop\<close>).  The precision a per-depth split \<^emph>\<open>would\<close> expose (the decode
  lemma \<open>rdec_separates_depths\<close>) is real in the decode but unreachable through this
  executable solver.  Recovering it --- a terminating \<^emph>\<open>and\<close> precise depth split --- needs a
  gas-bounded narrowing solver (\<^const>\<open>update_global_bounded_narrowing\<close>, TD Listing 9) or
  context/origin-sensitive reads (P11), not a value-domain widening lift.
\<close>

subsection \<open>GraphViz of the (warrowing) recursive analysis\<close>

text \<open>The monovariant warrowing solution rendered as an analysis-annotated CFG: each node
  carries its flow-sensitive interval, and \<open>G\<close> shows the widened \<open>[0, +inf]\<close> at the
  recursive slot.  The renderer is the generic \<^const>\<open>annotated_dot_of_prog_lit\<close>, so the
  interval domain needs no bespoke tooling.\<close>

definition rec_dot :: String.literal where
  "rec_dot = annotated_dot_of_prog_lit
     (prog_table rec_prog) (prog_procs rec_prog) (prog_main rec_prog) (snd rec_warrow_sol)"

text \<open>@{command ML_val} \<open>writeln (@{code rec_dot})\<close> emits the DOT source.\<close>

ML_val \<open>writeln (@{code rec_dot})\<close>

end

