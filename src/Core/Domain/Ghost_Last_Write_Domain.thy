theory Ghost_Last_Write_Domain
  imports Abstract_Domain "Voblint_CFG.LTR_Last_Write"
begin

section \<open>Abstract carrier for the last-writer ghost fact\<close>

text \<open>
  Section 6 of \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> chooses a finite flat lattice over
  \<^typ>\<open>cfg_node\<close> as the ghost carrier for \<open>last_writer\<close>: bottom for "no write observed", a
  precise value for one known writer, and a top element for "conflicting or unknown writer",
  matching real Goblint's join-to-unknown behaviour on divergent facts (\<open>c2poAnalysis.ml:246\<close>)
  rather than a hard drop.  \<open>'a flat_top\<close> is the standard three-point flat-with-top
  construction; it is generic in \<open>'a\<close> so it is not tied to \<^typ>\<open>cfg_node\<close> specifically.
\<close>

subsection \<open>The flat-with-top lattice\<close>

datatype 'a flat_top = FBot | FVal 'a | FTop

instantiation flat_top :: (type) ord
begin
definition less_eq_flat_top :: "'a flat_top \<Rightarrow> 'a flat_top \<Rightarrow> bool" where
  "less_eq_flat_top a b \<longleftrightarrow> a = b \<or> a = FBot \<or> b = FTop"
definition less_flat_top :: "'a flat_top \<Rightarrow> 'a flat_top \<Rightarrow> bool" where
  "less_flat_top a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
instance ..
end

instance flat_top :: (type) order
proof
  fix x y z :: "'a flat_top"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_flat_top_def)
  show "x \<le> x" by (simp add: less_eq_flat_top_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) (auto simp: less_eq_flat_top_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) (auto simp: less_eq_flat_top_def)
qed

instantiation flat_top :: (type) bot
begin
definition bot_flat_top :: "'a flat_top" where "bot_flat_top = FBot"
instance ..
end

instance flat_top :: (type) order_bot
  by intro_classes (simp add: less_eq_flat_top_def bot_flat_top_def)

instantiation flat_top :: (type) sup
begin
definition sup_flat_top :: "'a flat_top \<Rightarrow> 'a flat_top \<Rightarrow> 'a flat_top" where
  "sup_flat_top a b = (if a \<le> b then b else if b \<le> a then a else FTop)"
instance ..
end

instance flat_top :: (type) semilattice_sup
proof
  fix x y z :: "'a flat_top"
  show "x \<le> x \<squnion> y" by (cases x; cases y) (auto simp: sup_flat_top_def less_eq_flat_top_def)
  show "y \<le> x \<squnion> y" by (cases x; cases y) (auto simp: sup_flat_top_def less_eq_flat_top_def)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) (auto simp: sup_flat_top_def less_eq_flat_top_def)
qed

instance flat_top :: (type) bounded_semilattice_sup_bot ..

subsection \<open>Concretization of the flat-with-top lattice\<close>

text \<open>\<open>FBot\<close> is the ordinary analysis bottom --- "no information", the join identity, and the
  value at an unreached program point --- exactly the role \<^const>\<open>bot\<close> already plays for every
  other Voblint domain (e.g.\ sign's \<open>Sign_Bot\<close> means "unreached", not "the value zero"; zero is
  its own constructor).  A genuine "no write occurred" \<^emph>\<open>fact\<close> at a reached program point is a
  value of the carrier, \<^term>\<open>FVal None\<close> once instantiated at \<open>'a = cfg_node option\<close> below ---
  not \<^term>\<open>FBot\<close>.  Conflating the two would be unsound: joining a path that never wrote \<open>g\<close>
  with a path that wrote it at \<open>W\<close> must not settle on "definitely \<open>W\<close>", since the first path's
  own executions never touched \<open>g\<close> via \<open>W\<close>.  Keeping \<^term>\<open>FBot\<close> as pure "no information" makes
  \<open>gamma_lw\<close> monotone (\<^term>\<open>FBot\<close> concretizes to the empty set, a subset of everything) and
  keeps a real no-write-vs-write join going to \<^term>\<open>FTop\<close>, as it must.\<close>

definition gamma_lw :: "'a flat_top \<Rightarrow> 'a set" where
  "gamma_lw v = (case v of FBot \<Rightarrow> {} | FVal w \<Rightarrow> {w} | FTop \<Rightarrow> UNIV)"

lemma gamma_lw_mono: "a \<le> b \<Longrightarrow> gamma_lw a \<subseteq> gamma_lw b"
  unfolding gamma_lw_def less_eq_flat_top_def by (cases a; cases b) auto

lemma gamma_lw_sup_ub1: "gamma_lw a \<subseteq> gamma_lw (a \<squnion> b)"
  using gamma_lw_mono[OF sup_ge1] .

lemma gamma_lw_sup_ub2: "gamma_lw b \<subseteq> gamma_lw (a \<squnion> b)"
  using gamma_lw_mono[OF sup_ge2] .

lemma gamma_lw_bot: "gamma_lw bot = {}"
  by (simp add: gamma_lw_def bot_flat_top_def)

lemma gamma_lw_top: "gamma_lw FTop = UNIV"
  by (simp add: gamma_lw_def)

subsection \<open>The last-writer ghost carrier\<close>

text \<open>One flat-with-top slot per \<^typ>\<open>vname\<close>, exactly the shape section 6 chooses:
  \<open>'g_dl = vname => cfg_node_opt\<close>, instantiated at \<open>cfg_node option\<close> so \<^term>\<open>FVal None\<close> is a
  genuine domain value ("no write, precisely") distinct from \<^term>\<open>bot\<close> ("no information").
  Order, bottom, and join lift pointwise from \<^typ>\<open>cfg_node option flat_top\<close> via the generic
  \<open>bounded_semilattice_sup_bot\<close> function instance already established in
  \<^theory>\<open>Voblint_Core.Abstract_Domain\<close>, exactly the way \<^typ>\<open>'a abs_state\<close> does for an ordinary
  value domain --- no separate lifting lemmas are needed here either.\<close>

type_synonym ghost_lw = "vname \<Rightarrow> cfg_node option flat_top"

definition gamma_lw_state :: "ghost_lw \<Rightarrow> vname \<Rightarrow> cfg_node option set" where
  "gamma_lw_state w x = gamma_lw (w x)"

subsection \<open>Which variable an edge writes, as a function\<close>

text \<open>\<open>edge_writes\<close> (\<open>LTR_Last_Write\<close>) is a boolean test against a queried variable;
  \<open>edge_write_var\<close> is the same fact as the (at most one) variable an action actually names,
  which is what a transfer function needs to seed a single ghost slot at one edge.\<close>

fun edge_write_var :: "edge_action \<Rightarrow> vname option" where
  "edge_write_var (EA_Assign y _) = Some y"
| "edge_write_var (EA_Random y) = Some y"
| "edge_write_var (EA_Ret _ _) = Some ret_var"
| "edge_write_var EA_Nop = None"
| "edge_write_var (EA_Assume _) = None"
| "edge_write_var (EA_AssumeNot _) = None"

lemma edge_write_var_writes: "edge_writes a x \<longleftrightarrow> edge_write_var a = Some x"
  by (cases a) auto

lemma edge_write_var_None_no_write: "edge_write_var a = None \<Longrightarrow> \<not> edge_writes a x"
  using edge_write_var_writes by (cases a) auto

subsection \<open>The seed step\<close>

text \<open>\<open>ghost_step\<close> is the ghost analogue of a value transfer's own \<open>dgs_assign\<close>: on an edge
  action \<open>a\<close> reaching node \<open>v\<close>, the ghost slot for the written variable (if any) is set precisely
  to \<^term>\<open>FVal (Some v)\<close>, computed directly from the edge's own target --- not routed from
  elsewhere.  This is the pointwise/simultaneous shape section 6 and section 7 both need: the
  base component's own transfer is untouched, and the ghost update reads only this one edge.\<close>

definition ghost_step :: "edge_action \<Rightarrow> cfg_node \<Rightarrow> ghost_lw \<Rightarrow> ghost_lw" where
  "ghost_step a v w = (case edge_write_var a of None \<Rightarrow> w | Some x \<Rightarrow> w(x := FVal (Some v)))"

subsection \<open>Soundness of the seed step against the trace-level specification\<close>

text \<open>The local update is sound against \<open>last_writer\<close> at every step, given the edge actually
  fired at the CFG's own edge relation and the CFG is edge-action functional (the same
  \<open>cfg_intra_functional\<close> hypothesis \<open>LTR_Last_Write\<close> needs for its own characterization
  lemmas).  This is the ghost-carrier half of design-gate item 3.\<close>

theorem ghost_step_sound:
  assumes fn: "cfg_intra_functional g"
    and e: "(fst (last p), a, v) \<in> intra g"
    and p: "p \<noteq> []"
    and ok: "last_writer g x p \<in> gamma_lw_state w x"
  shows "last_writer g x (p @ [(v, s')]) \<in> gamma_lw_state (ghost_step a v w) x"
proof (cases "edge_write_var a")
  case None
  have nw: "\<not> edge_writes a x" using None by (rule edge_write_var_None_no_write)
  have "\<not> last_write_step g (fst (last p)) v x"
  proof
    assume "last_write_step g (fst (last p)) v x"
    then obtain a' where a': "(fst (last p), a', v) \<in> intra g" "edge_writes a' x"
      unfolding last_write_step_def by blast
    have "a' = a" using fn e a'(1) unfolding cfg_intra_functional_def by blast
    with a'(2) nw show False by simp
  qed
  then have "last_writer g x (p @ [(v, s')]) = last_writer g x p"
    using last_writer_snoc_no_write[OF p] by simp
  moreover have "ghost_step a v w x = w x" using None unfolding ghost_step_def by simp
  ultimately show ?thesis using ok unfolding gamma_lw_state_def by simp
next
  case (Some y)
  show ?thesis
  proof (cases "x = y")
    case True
    have wr: "edge_writes a x" using Some True edge_write_var_writes by simp
    have "last_write_step g (fst (last p)) v x"
      unfolding last_write_step_def using e wr by blast
    then have "last_writer g x (p @ [(v, s')]) = Some v"
      using last_writer_snoc_write[OF p] by simp
    moreover have "ghost_step a v w x = FVal (Some v)"
      using Some True unfolding ghost_step_def by simp
    ultimately show ?thesis unfolding gamma_lw_state_def gamma_lw_def by simp
  next
    case False
    have nw: "\<not> edge_writes a x"
      using Some False edge_write_var_writes by (metis option.inject)
    have "\<not> last_write_step g (fst (last p)) v x"
    proof
      assume "last_write_step g (fst (last p)) v x"
      then obtain a' where a': "(fst (last p), a', v) \<in> intra g" "edge_writes a' x"
        unfolding last_write_step_def by blast
      have "a' = a" using fn e a'(1) unfolding cfg_intra_functional_def by blast
      with a'(2) nw show False by simp
    qed
    then have "last_writer g x (p @ [(v, s')]) = last_writer g x p"
      using last_writer_snoc_no_write[OF p] by simp
    moreover have "ghost_step a v w x = w x"
      using Some False unfolding ghost_step_def by simp
    ultimately show ?thesis using ok unfolding gamma_lw_state_def by simp
  qed
qed

text \<open>The trace-level counterpart, phrased directly against \<^const>\<open>valid_ltr\<close>'s \<open>intra\<close>
  rule: seeding the ghost state at an executed edge stays sound for \<^const>\<open>trace_last_writer\<close>
  on the extended trace.\<close>

theorem ghost_step_sound_trace:
  assumes fn: "cfg_intra_functional g"
    and t: "t \<in> valid_ltr gs g S"
    and e: "(sink_node t, a, v) \<in> intra g" and s': "s' \<in> edge_step a (sink_store t)"
    and ok: "trace_last_writer g x t \<in> gamma_lw_state w x"
  shows "trace_last_writer g x (extend t (v, s')) \<in> gamma_lw_state (ghost_step a v w) x"
proof -
  have p: "path t \<noteq> []" using t by (rule valid_ltr_path_nonempty)
  have e': "(fst (last (path t)), a, v) \<in> intra g" using e by (simp add: sink_node_def)
  have ok': "last_writer g x (path t) \<in> gamma_lw_state w x"
    using ok unfolding trace_last_writer_def .
  have "last_writer g x (path t @ [(v, s')]) \<in> gamma_lw_state (ghost_step a v w) x"
    using ghost_step_sound[OF fn e' p ok'] .
  then show ?thesis unfolding trace_last_writer_def by simp
qed

end
