(* vendor/td-verification/Basics_side.thy *)
abbreviation part_post_solution ::
    "('x,'g,'d::bounded_semilattice_sup_bot) eqsT \<Rightarrow> 'x \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'x set \<Rightarrow> bool" where
  "part_post_solution T x sigma vars \<equiv>
    x \<in> vars \<and> (\<forall>u \<in> vars.
    dep\<^sub>L T sigma u \<subseteq> vars \<and>
    eq T u sigma \<le> sigma (Inl u) \<and>
    sides_of_rhs (T u) sigma \<le> sigma)"
