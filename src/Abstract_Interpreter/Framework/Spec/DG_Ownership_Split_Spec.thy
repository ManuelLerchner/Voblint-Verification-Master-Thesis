theory DG_Ownership_Split_Spec
  imports "Voblint_Framework.MCP_Spec" Transfer_Algebra "Voblint_Domain.Nonrelational_Reachability"
    State_Restriction "Voblint_Solver.Strategy_Program_Fold"
begin

section \<open>Publishing the global halves of an entry's alternatives\<close>

text \<open>
  An entry transfer answers a list of alternatives, each a pair of a caller
  continuation and a callee entry state, rather than one successor value. What an
  analysis that keeps its globals on a shared unknown publishes for one call is the
  join, over every alternative, of both halves' global projections \<open>rg\<close>: a
  continuation carries global information as much as its callee entry does.
\<close>

definition ownership_split_enter_sides ::
  "('d \<Rightarrow> 'd) \<Rightarrow> ('d::bounded_semilattice_sup_bot) enter_result list \<Rightarrow> 'd"
where
  "ownership_split_enter_sides rg pairs =
     (\<Squnion>(cont, entry)\<leftarrow>pairs. rg cont \<squnion> rg entry)"

lemma ownership_split_enter_sides_Nil [simp]:
  "ownership_split_enter_sides rg [] = bot"
  by (simp add: ownership_split_enter_sides_def)

lemma ownership_split_enter_sides_Cons [simp]:
  "ownership_split_enter_sides rg ((cont, entry) # pairs)
     = rg cont \<squnion> rg entry \<squnion> ownership_split_enter_sides rg pairs"
  by (simp add: ownership_split_enter_sides_def)

text \<open>
  What the joint publication bounds, and what it is bounded by. The two member
  rules are what a soundness proof reaches for once it has selected a covering
  alternative: that pair's two halves are each below what the call published, so
  a concretization taken against the published global still contains them. They
  stay untagged --- their conclusions are bare inequalities in \<open>rg\<close> and would
  broaden proof search wherever a \<open>\<le>\<close> goal appears.
\<close>

lemma ownership_split_enter_sides_le_iff:
  "ownership_split_enter_sides rg pairs \<le> g
     \<longleftrightarrow> (\<forall>(cont, entry) \<in> set pairs. rg cont \<le> g \<and> rg entry \<le> g)"
  by (induction pairs) auto

end
