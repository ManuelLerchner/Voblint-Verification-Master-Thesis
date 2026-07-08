theory Origin_Lift
  imports Origin_State Solver_Menu
begin

section \<open>Per-origin widening as an equation-system transform\<close>

text \<open>
  Per-origin widening keeps every write origin's contribution to a shared slot in its
  own cell and widens those cells independently, so a value that is stable per origin is
  never widened away even while the merged value climbs.  Here it is realised without
  touching the vendored solver or the edge-transfer framework: a \<^emph>\<open>thin adapter\<close> lifts the
  value domain of an existing equation system from \<open>'d\<close> to \<^typ>\<open>('o, 'd) origin_st\<close>.

  \<^item> \<^bold>\<open>read\<close> --- every \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> collapses the origin map it reads back
    to a plain \<open>'d\<close> before handing it to the original transfer, so transfers are unchanged.
  \<^item> \<^bold>\<open>write\<close> --- every \<^const>\<open>Answer\<close>/\<^const>\<open>Side\<close> injects its \<open>'d\<close> at the origin of the
    equation being evaluated, so a contribution only touches its own cell.

  The lifted system is then handed to the ordinary Apinis warrowing solver, whose
  pointwise widening on \<^typ>\<open>('o, 'd) origin_st\<close> is exactly per-origin widening.  No new
  solver and no new code generator: \<open>eval\<close> runs it directly.
\<close>

subsection \<open>Injecting a contribution at one origin\<close>

definition inject_origin :: "'o \<Rightarrow> 'd::bot \<Rightarrow> ('o, 'd) origin_st" where
  "inject_origin org d = update_origin \<bottom> org d"

lemma lookup_inject_origin [simp]:
  "lookup_origin (inject_origin org d) k = (if k = org then d else \<bottom>)"
  by (cases "k = org") (simp_all add: inject_origin_def)

lemma collapse_inject_origin [simp]:
  "collapse_origins (inject_origin org (d :: 'd::bounded_semilattice_sup_bot)) = d"
proof (rule antisym)
  show "collapse_origins (inject_origin org d) \<le> d"
    by (rule collapse_least) simp
  show "d \<le> collapse_origins (inject_origin org d)"
    using lookup_le_collapse[of "inject_origin org d" org] by simp
qed

subsection \<open>Lifting a strategy tree to the origin-indexed domain\<close>

primrec lift_tree ::
  "'o \<Rightarrow> ('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree
      \<Rightarrow> ('x, 'g, ('o, 'd) origin_st) strategy_tree" where
  "lift_tree org (Answer d) = Answer (inject_origin org d)"
| "lift_tree org (QueryL y f) = QueryL y (\<lambda>ov. lift_tree org (f (collapse_origins ov)))"
| "lift_tree org (QueryG y f) = QueryG y (\<lambda>ov. lift_tree org (f (collapse_origins ov)))"
| "lift_tree org (Side y d t) = Side y (inject_origin org d) (lift_tree org t)"

definition origin_lift_eqs ::
  "('x \<Rightarrow> 'o) \<Rightarrow> ('x, 'g, 'd::bounded_semilattice_sup_bot) eqsT
     \<Rightarrow> ('x, 'g, ('o, 'd) origin_st) eqsT" where
  "origin_lift_eqs org_of T = (\<lambda>x. lift_tree (org_of x) (T x))"

subsection \<open>The per-origin widening solver variant\<close>

text \<open>
  \<open>org_of\<close> assigns each equation unknown its origin.  Using the unknown itself
  (\<open>org_of = id\<close>) gives one origin per program point / context, the finest origin split
  that still code-generates.  The reader collapses on every access, so a slot's
  observable value is \<^const>\<open>collapse_origins\<close> of its per-origin cells.
\<close>

definition TD_side_per_origin_widen_solve ::
  "('x \<Rightarrow> 'o) \<Rightarrow> ('x, 'g, 'd::bounded_warrowing) eqsT \<Rightarrow> 'x
     \<Rightarrow> 'x set \<times> ('x + 'g \<Rightarrow> ('o, 'd) origin_st)" where
  "TD_side_per_origin_widen_solve org_of T v =
     TD_side_warrowing_apinis_Interp_solve (origin_lift_eqs org_of T) v"

text \<open>Read one slot's collapsed (observable) value under the per-origin widening solve.\<close>
definition read_per_origin ::
  "('x \<Rightarrow> 'o) \<Rightarrow> ('x, 'g, 'd::bounded_warrowing) eqsT \<Rightarrow> 'x \<Rightarrow> ('x + 'g) \<Rightarrow> 'd" where
  "read_per_origin org_of T v k =
     collapse_origins (snd (TD_side_per_origin_widen_solve org_of T v) k)"

end
