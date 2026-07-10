section \<open>Guarded recursion the seeded-clean solver diverges on: a non-canonical \<open>\<bottom>\<close> bug\<close>

theory Example_Interval_Recursion_Divergence
  imports
    Voblint_Formalization.Exec_Ivl_Cmp_Seed_Clean_Run
begin

text \<open>
  \<^bold>\<open>Minimal reproducer\<close> for the seeded-clean interval spine diverging on a bounded
  recursive procedure.  \<open>f\<close> guards its self-call by \<open>G < 1\<close>, so concrete execution does
  \<open>G = 0\<close> then \<open>G = 1\<close> and stops --- \<open>G\<close> never reaches \<open>2\<close>.  The compiled CFG carries the
  recursion (self \<^const>\<open>EA_Enter\<close> plus combine), reachable only through the guarded true
  branch.

  \<^bold>\<open>Root cause (settled by a \<open>\<sigma>\<close>-tap on the live solve).\<close>  The divergence is \<^emph>\<open>not\<close> a
  solver-scheduling, equality, or context-scheme problem, and it is \<^emph>\<open>not\<close> semantically
  justified.  It is an \<^bold>\<open>interval-domain normalization bug\<close>: empty intervals are not
  canonicalised.  An empty interval is any \<^term>\<open>Ivl (Fin l) (Fin u)\<close> with \<open>l > u\<close>; the
  domain has infinitely many such representations, all denoting \<open>\<bottom>\<close>, and the executable
  arithmetic does not collapse them.  The recursion walks this staircase:

    \<^item> context \<open>[1,1]\<close>: the guard \<open>G < 1\<close> correctly kills it to \<open>Ivl (Fin 1) (Fin 0)\<close> (an
      empty interval), so the branch is dead;
    \<^item> but the following \<open>G := G + 1\<close> is applied pointwise to the bounds:
      \<open>[1,0] + [1,1] = [2,1]\<close> --- \<^emph>\<open>another\<close> empty interval, a \<^emph>\<open>different\<close> representation
      of \<open>\<bottom>\<close> (\<open>rdiv_incr_walks_bot\<close>, \<open>rdiv_walk_is_empty\<close>, \<open>rdiv_walk_not_canonical\<close>);
    \<^item> \<^const>\<open>restrict_global_st\<close> turns that into a fresh calling context \<open>[2,1]\<close>
      (\<open>rdiv_new_context_from_bot\<close>), whose activation increments to \<open>[3,1]\<close>, and so on
      without bound.

  The tapped solve makes this explicit: at the recursive-call node the stored value runs
  \<open>[1,1], [2,1], [3,1], \<dots>, [687,1], \<dots>\<close> --- an infinite ascending chain of distinct
  \<^emph>\<open>empty\<close> intervals, each spawning a new (dead) context.  Because the \<^typ>\<open>ivl\<close> equality
  is structural, these all count as different unknowns, so the solver never terminates.
  Widening is the wrong fix (it hides a normalization defect); the fix is to canonicalise
  empty intervals to \<open>\<bottom>\<close> in the arithmetic/assign transfer.  This theory records the
  finite facts executably and never invokes the diverging solve.
\<close>

subsection \<open>The program and its compiled CFG\<close>

definition rdiv_prog :: imp_prog where
  "rdiv_prog = \<lbrakk>
     int G;
     void f() {
       if (G < 1) { G := G + 1; f() } else { G := G }
     }
     void main() {
       G := 0;
       f()
     }
   \<rbrakk>"

definition rdiv_cfg :: cfg where
  "rdiv_cfg = compile_prog (prog_table rdiv_prog) (prog_procs rdiv_prog) (prog_main rdiv_prog)"

definition rdiv_edges :: "(pp \<times> edge_action \<times> pp) list" where
  "rdiv_edges = cfg_edges_list rdiv_cfg"

definition rdiv_ea :: "pp \<Rightarrow> pp \<Rightarrow> edge_action" where
  "rdiv_ea a b = (case filter (\<lambda>(u, ea, v). u = a \<and> v = b) rdiv_edges of
                    (_, ea, _) # _ \<Rightarrow> ea | [] \<Rightarrow> EA_Nop)"

text \<open>The recursion is present and reachable only through the guarded true branch:
  node 0 assumes \<open>G < 1\<close> on \<open>0 \<rightarrow> 1\<close> (true) and its negation on \<open>0 \<rightarrow> 5\<close> (false); the
  guarded body \<open>1 \<rightarrow> 2 \<rightarrow> 3\<close> reaches the recursive call at node 3, whose \<^const>\<open>EA_Enter\<close>
  re-enters \<open>f\<close>'s entry (node 0) with combine \<open>(3, 7, 4)\<close>.\<close>

lemma rdiv_true_branch_is_guard:
  "(case rdiv_ea 0 1 of EA_Assume _ \<Rightarrow> True | _ \<Rightarrow> False)"
  unfolding rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval

lemma rdiv_false_branch_is_guard:
  "(case rdiv_ea 0 5 of EA_AssumeNot _ \<Rightarrow> True | _ \<Rightarrow> False)"
  unfolding rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval

lemma rdiv_body_increments:
  "(case rdiv_ea 1 2 of EA_Assign x _ \<Rightarrow> x = ''G'' | _ \<Rightarrow> False)"
  unfolding rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval

lemma rdiv_recursion_present:
  "(3, EA_Enter, 0) \<in> edges rdiv_cfg \<and> (3, 7, 4) \<in> combines rdiv_cfg"
  unfolding rdiv_cfg_def rdiv_prog_def by eval

lemma rdiv_recursive_call_guarded:
  "(0, rdiv_ea 0 1, 1) \<in> edges rdiv_cfg
   \<and> (1, rdiv_ea 1 2, 2) \<in> edges rdiv_cfg
   \<and> (2, EA_Nop, 3) \<in> edges rdiv_cfg"
  unfolding rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval

subsection \<open>The finite boundaries: guard sound, increment on \<open>\<bottom>\<close> broken\<close>

definition rdiv_seedG :: "Int.int \<Rightarrow> ivl st" where
  "rdiv_seedG k = restrict_global_st (update_st (bot::ivl st) ''G'' (Ivl (Fin k) (Fin k)))"

definition rdiv_after_guard :: "Int.int \<Rightarrow> ivl st" where
  "rdiv_after_guard k = ivl_tf_st (rdiv_ea 0 1) (rdiv_seedG k)"

definition rdiv_after_incr :: "Int.int \<Rightarrow> ivl st" where
  "rdiv_after_incr k = ivl_tf_st (rdiv_ea 1 2) (rdiv_after_guard k)"

text \<open>Boundaries in the initial context are exact: seed \<open>[0,0]\<close>, guard passes, increment
  to \<open>[1,1]\<close>, recursive context \<open>[1,1]\<close>.\<close>
lemma rdiv_b1_entry:      "lookup_st (rdiv_seedG 0) ''G'' = Ivl (Fin 0) (Fin 0)"
  unfolding rdiv_seedG_def by eval
lemma rdiv_b2_guard0:     "lookup_st (rdiv_after_guard 0) ''G'' = Ivl (Fin 0) (Fin 0)"
  unfolding rdiv_after_guard_def rdiv_seedG_def rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval
lemma rdiv_b3_incr0:      "lookup_st (rdiv_after_incr 0) ''G'' = Ivl (Fin 1) (Fin 1)"
  unfolding rdiv_after_incr_def rdiv_after_guard_def rdiv_seedG_def rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval
lemma rdiv_b4_reccontext: "lookup_st (restrict_global_st (rdiv_after_incr 0)) ''G'' = Ivl (Fin 1) (Fin 1)"
  unfolding rdiv_after_incr_def rdiv_after_guard_def rdiv_seedG_def rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval

text \<open>In the recursive context \<open>[1,1]\<close> the guard \<^emph>\<open>correctly\<close> kills the branch to the empty
  interval \<open>Ivl (Fin 1) (Fin 0)\<close> (\<open>l > u\<close>).\<close>
lemma rdiv_b5_guard1_bot: "lookup_st (rdiv_after_guard 1) ''G'' = Ivl (Fin 1) (Fin 0)"
  unfolding rdiv_after_guard_def rdiv_seedG_def rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval

text \<open>\<^bold>\<open>The failing boundary.\<close>  The increment is then applied to that empty interval and,
  because bounds are added pointwise with no emptiness check, walks to a \<^emph>\<open>new\<close> empty
  interval \<open>[2,1]\<close> instead of staying \<open>\<bottom>\<close>.\<close>
lemma rdiv_incr_walks_bot: "lookup_st (rdiv_after_incr 1) ''G'' = Ivl (Fin 2) (Fin 1)"
  unfolding rdiv_after_incr_def rdiv_after_guard_def rdiv_seedG_def rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval

text \<open>\<open>[2,1]\<close> denotes the empty set (so it is semantically \<open>\<bottom>\<close>)\<dots>\<close>
lemma rdiv_walk_is_empty: "gamma_ivl (Ivl (Fin 2) (Fin 1)) = {}"
  by (auto simp: eint_le.simps)

text \<open>\<dots>yet it is not the canonical \<open>\<bottom>\<close>, and differs from the next step's \<open>[3,1]\<close>, so the
  structural \<^typ>\<open>ivl\<close> equality keeps them apart.\<close>
lemma rdiv_walk_not_canonical: "(Ivl (Fin 2) (Fin 1) :: ivl) \<noteq> Ivl PlusInf MinInf"
  by simp
lemma rdiv_walk_distinct_reps: "(Ivl (Fin 2) (Fin 1) :: ivl) \<noteq> Ivl (Fin 3) (Fin 1)"
  by simp

text \<open>Consequently the recursion fabricates a fresh calling context from a dead \<open>\<bottom>\<close>:
  the context generated after the (killed) recursive activation is \<^emph>\<open>not\<close> the entry
  context of that activation --- a new unknown, ad infinitum.\<close>
lemma rdiv_new_context_from_bot:
  "restrict_global_st (rdiv_after_incr 1) \<noteq> rdiv_seedG 1"
  unfolding rdiv_after_incr_def rdiv_after_guard_def rdiv_seedG_def rdiv_ea_def rdiv_edges_def rdiv_cfg_def rdiv_prog_def by eval

subsection \<open>The state equality itself is denotational (so this is not an equality defect)\<close>

text \<open>\<^const>\<open>update_st\<close> prepends, so re-writing \<open>G\<close> grows the representation while the
  denotation is unchanged; the executable state equality still identifies the two.  The
  divergence is therefore located squarely in the \<^emph>\<open>interval\<close> normalization, not in the
  state quotient's equality.\<close>
lemma rdiv_state_eq_denotational:
  "HOL.equal (update_st (update_st (bot::ivl st) ''G'' (Ivl (Fin 1) (Fin 1))) ''G'' (Ivl (Fin 1) (Fin 1)))
             (update_st (bot::ivl st) ''G'' (Ivl (Fin 1) (Fin 1))) = True"
  by eval

end
