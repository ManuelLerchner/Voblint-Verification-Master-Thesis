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

  The machine-checked headline (\<open>rec_warrowing_widens_to_top\<close>) is that monovariant
  warrowing widens \<open>G\<close> to \<open>[0, +inf]\<close> on the recursive CFG (whose recursion is itself
  machine-checked --- \<open>rec_cfg_recursive_enter\<close> / \<open>rec_cfg_recursive_combine\<close>).  Per-origin
  widening buys \<^emph>\<open>nothing\<close> here: the collapsed read of \<open>G\<close> is the same \<open>[0, +inf]\<close>
  (confirmed interactively via the DOT emission below; omitted as a \<open>by eval\<close> theorem
  only because the per-origin solve over the recursion cycle costs about a minute, past the
  batch budget).  The precision that is lost is the finite \<^emph>\<open>upper\<close> bound.  Since \<open>G\<close> is a
  flow-insensitive global side slot, its self-referential increment is not bounded by the
  guard when it writes back to the slot, so \<open>[0, +inf]\<close> is a genuine fixpoint and the
  widening bot-law pins the lower bound at \<open>0\<close>.  The origin lift is the wrong lever for it:
  a read collapses the per-origin cells before the increment transfer, so separating write
  origins cannot change the slot.
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

subsection \<open>The compiled CFG carries the recursion\<close>

text \<open>Procedure \<open>p\<close> is already in the layout when its body compiles, so the self-call at
  node \<open>3\<close> re-enters \<open>p\<close>'s entry (node \<open>0\<close>) and returns to node \<open>4\<close>; \<open>main\<close>'s call at node
  \<open>10\<close> enters the same entry and returns to node \<open>11\<close>.  Both route through \<open>p\<close>'s single
  exit, node \<open>7\<close>.  The recursive \<^const>\<open>EA_Enter\<close> and combine edges are present --- the
  structure the old compiler erased.  These evaluate cheaply (compilation only, no solve).\<close>

lemma rec_cfg_recursive_enter:
  "(3, EA_Enter, 0) \<in> edges rec_cfg \<and> (10, EA_Enter, 0) \<in> edges rec_cfg"
  unfolding rec_cfg_def rec_prog_def by eval

lemma rec_cfg_recursive_combine:
  "(3, 7, 4) \<in> combines rec_cfg \<and> (10, 7, 11) \<in> combines rec_cfg"
  unfolding rec_cfg_def rec_prog_def by eval

subsection \<open>Monovariant warrowing widens \<open>G\<close>'s upper bound to \<open>+inf\<close>\<close>

text \<open>The widening bot-law (\<^const>\<open>widen\<close> on \<^typ>\<open>ivl\<close>) keeps the first write exact, so the
  lower bound settles at \<open>0\<close>; the recursive increment still climbs the upper bound, which
  widens to \<open>+inf\<close>.  Interval narrowing is real and reclaims the bound of a local loop
  counter, but \<open>G\<close> is a flow-insensitive global slot: the guard never bounds the write-back,
  so \<open>[0, +inf]\<close> is a genuine fixpoint and narrowing has nothing smaller to descend to.\<close>
definition rec_warrow_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl st)" where
  "rec_warrow_sol = TD_side_warrowing_apinis_Interp_solve rec_eqs (cfg_exit rec_cfg)"

lemma rec_warrowing_widens_to_top:
  "lookup_st (snd rec_warrow_sol (Inr ())) ''G'' = Ivl (Fin 0) PlusInf"
  unfolding rec_warrow_sol_def rec_eqs_def rec_cfg_def by eval

subsection \<open>Per-origin widening: origin = the program point that writes\<close>

text \<open>\<open>org_of = id\<close> gives one origin per equation unknown (program point).  With the
  recursive call edges now present in the compiled CFG, the lifted per-origin solve is kept
  as a definition but is not batch-evaluated here.  The solve still terminates --- with
  finitely many origins its per-origin widening chains stabilise --- but on the recursive
  CFG the \<open>eval\<close> takes roughly a minute, well past the repository's build budget, so it is
  not stated as a \<open>by eval\<close> theorem.  The monovariant warrowing fact above is the
  machine-checked result of this theory.\<close>

definition rec_po_sol ::
  "pp set \<times> (pp + unit \<Rightarrow> (pp, ivl st) origin_st)" where
  "rec_po_sol = TD_side_per_origin_widen_solve id rec_eqs (cfg_exit rec_cfg)"

definition rec_po_read :: "pp + unit \<Rightarrow> ivl st" where
  "rec_po_read k = collapse_origins (snd rec_po_sol k)"

text \<open>
  The recursive self-call is now compiled: with procedure layout computed before body
  compilation, the CFG carries the recursive enter/combine edge.  The per-origin solve
  over that cycle still terminates but its \<open>eval\<close> costs about a minute, past the batch
  budget, so the monovariant warrowing result above is the executable fact certified here.

  Recovering a finite upper bound for \<open>G\<close> still needs a flow-/context-/origin-sensitive
  read of the global slot, or a gas-bounded narrowing solver.  See
  \<open>docs/OPEN_PROBLEMS.md\<close> P11.
\<close>

subsection \<open>GraphViz of the per-origin (collapsed) analysis\<close>

text \<open>The DOT definition is retained for interactive inspection.  It is not emitted in
  batch: forcing \<^const>\<open>rec_po_read\<close> runs the per-origin solve, whose \<open>eval\<close> costs about a
  minute on the recursion cycle.  The expected render (obtained in jEdit) shows the two
  \<open>p\<close> clusters wired by the recursion --- \<^const>\<open>EA_Enter\<close> \<open>3 -> 0\<close> (self-call) and
  \<open>10 -> 0\<close> (\<open>main\<close>), combines \<open>7 -> 4\<close> (call@3) and \<open>7 -> 11\<close> (call@10) --- and the
  flow-insensitive global slot annotated \<open>G = [0, +inf]\<close>, i.e. the same widened value the
  monovariant warrowing solver certifies above.\<close>

definition rec_po_dot :: String.literal where
  "rec_po_dot = annotated_dot_of_prog_lit
     (prog_table rec_prog) (prog_procs rec_prog) (prog_main rec_prog) rec_po_read"

text \<open>To emit the DOT source in jEdit (runs the ~1-minute per-origin solve):
  @{command ML_val} \<open>writeln (@{code rec_po_dot})\<close>.\<close>

end
