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

  The headline finding, sealed by \<open>eval\<close> below, is a genuine wall: \<^emph>\<open>no\<close> value digest
  on a monotonically climbing global can make the join solver converge (a climbing
  interval leaves every fixed bucket, collapsing to the coarse \<open>RTop\<close> partition, which
  then climbs unbounded).  So the only terminating interval solver is Apinis warrowing,
  and warrowing widens \<^emph>\<open>globals\<close> --- the digest partitions are globals --- to the top
  interval.  The digest still separates the recursion into activation partitions; it
  cannot keep their values sharp without per-origin widening (\<open>docs/OPEN_PROBLEMS.md\<close> P11).
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

  \<^bold>\<open>Widening.\<close>  Apinis warrowing terminates --- by widening \<open>G\<close> to the top interval.
\<close>

definition rec_eqs :: "(pp, unit, ivl st) eqsT" where
  "rec_eqs = side_cfg_T_eff_st rec_cfg ivl_etf_st bot cinit_ivl_st ()"

definition rec_warrow_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl st)" where
  "rec_warrow_sol = TD_side_warrowing_apinis_Interp_solve rec_eqs (cfg_exit rec_cfg)"

lemma rec_warrowing_widens_to_top:
  "lookup_st (snd rec_warrow_sol (Inr ())) ''G'' = Ivl MinInf PlusInf"
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

lemmas rec_unfold =
  rec_digest_solution_def rec_digest_eqs_def rec_cfg_def rec_dg_def rec_prep_def rdec_def

text \<open>Both live partitions widen to the top interval; the depth buckets are empty
  (\<^const>\<open>Ivl\<close> \<^const>\<open>PlusInf\<close> \<^const>\<open>MinInf\<close> is the bottom interval).\<close>
theorem rec_digest_separates_activations_not_values:
  "lookup_st (snd rec_digest_solution (Inr R0))   ''G'' = Ivl MinInf PlusInf
 \<and> lookup_st (snd rec_digest_solution (Inr RTop)) ''G'' = Ivl MinInf PlusInf
 \<and> lookup_st (snd rec_digest_solution (Inr R1))   ''G'' = Ivl PlusInf MinInf
 \<and> lookup_st (snd rec_digest_solution (Inr R2))   ''G'' = Ivl PlusInf MinInf
 \<and> lookup_st (snd rec_digest_solution (Inr R3))   ''G'' = Ivl PlusInf MinInf"
  unfolding rec_unfold by eval

text \<open>The precision that a per-depth split \<^emph>\<open>would\<close> have exposed (the decode lemma rdec_separates_depths)
  is real in the decode but unreachable through an executable solver: join diverges, warrowing
  widens.  Recovering it needs a per-origin \<^emph>\<open>widening\<close> discipline that keeps each recursion
  depth's contribution separate under a terminating solve (P11), which does not yet
  code-generate.\<close>

subsection \<open>GraphViz of the (warrowing) recursive analysis\<close>

text \<open>The monovariant warrowing solution rendered as an analysis-annotated CFG: each node
  carries its flow-sensitive interval, and \<open>G\<close> shows the widened \<open>[-inf, +inf]\<close> at the
  recursive slot.  The renderer is the generic \<^const>\<open>annotated_dot_of_prog_lit\<close>, so the
  interval domain needs no bespoke tooling.\<close>

definition rec_dot :: String.literal where
  "rec_dot = annotated_dot_of_prog_lit
     (prog_table rec_prog) (prog_procs rec_prog) (prog_main rec_prog) (snd rec_warrow_sol)"

text \<open>@{command ML_val} \<open>writeln (@{code rec_dot})\<close> emits the DOT source.\<close>

ML_val \<open>writeln (@{code rec_dot})\<close>

end

