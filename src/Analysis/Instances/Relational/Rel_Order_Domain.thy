theory Rel_Order_Domain
  imports "Voblint_Core.DG_Soundness"
begin

section \<open>A minimal relational carrier for \<^const>\<open>sound_dg_spec\<close>\<close>

text \<open>
  \<open>relc\<close> tracks a finite set of known pairwise-ordered variables, \<open>(x, y)\<close>
  meaning \<open>x \<le> y\<close> at every store the value describes.  No closure: two known
  facts \<open>x \<le> y\<close> and \<open>y \<le> z\<close> do not automatically yield \<open>x \<le> z\<close> in this
  carrier.  This is deliberately the least amount of relational structure that
  is still relational (a pair of variables, not one) and not \<open>abs_state\<close>
  (no \<open>vname \<Rightarrow> 'a\<close> function type anywhere in the carrier).

  The purpose of this file is not a useful analysis.  It demonstrates that a
  non-\<open>abs_state\<close> carrier discharges \<^locale>\<open>sound_dg_spec\<close> with zero
  changes to the DG framework.
  Every transfer below is deliberately the most imprecise sound choice
  (forget on assign, havoc on call) except for a precise \<open>assume\<close>/
  \<open>assume_not\<close> pair, which is enough to make the carrier genuinely
  relational.
\<close>

subsection \<open>The carrier and its lattice\<close>

datatype relc = Bot | RelC (relc_pairs: "(vname \<times> vname) set")

text \<open>Order is reverse inclusion on the constraint set: more known pairs is
  more information, hence lower (more precise) in the abstract-interpretation
  order.  \<open>sup\<close> keeps only the pairs both sides agree on.

  \<open>bot\<close> is a separate explicit constructor rather than \<open>RelC UNIV\<close> (the
  most-constrained set, "every pair known ordered"): representing \<open>UNIV\<close>
  forces the code generator to use the \<open>Coset\<close> branch of HOL's executable-set
  representation, and the stock library does not give every set operation
  (subset test among them) a code equation for every \<open>Set\<close>/\<open>Coset\<close>
  combination over an infinite element type such as \<open>vname\<close> -- confirmed
  directly: \<open>RelC UNIV\<close> batch-checked and even unit-tested via \<open>value\<close>
  cleanly, but running it through the solver raised \<open>exception Match\<close> in
  the generated code the first time a genuine \<open>Coset\<close>/\<open>Coset\<close> combination
  arose. Keeping \<open>RelC\<close>'s field always finite avoids the gap entirely: no
  value this file ever constructs is a \<open>Coset\<close>.\<close>

instantiation relc :: bounded_semilattice_sup_bot
begin

fun less_eq_relc :: "relc \<Rightarrow> relc \<Rightarrow> bool" where
  "less_eq_relc Bot _ = True"
| "less_eq_relc (RelC _) Bot = False"
| "less_eq_relc (RelC a) (RelC b) = (b \<subseteq> a)"

definition less_relc :: "relc \<Rightarrow> relc \<Rightarrow> bool" where
  "less_relc a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

fun sup_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where
  "sup_relc Bot b = b"
| "sup_relc a Bot = a"
| "sup_relc (RelC a) (RelC b) = RelC (a \<inter> b)"

definition bot_relc :: relc where
  "bot_relc = Bot"

instance
proof intro_classes
  fix x y z :: relc
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_relc_def)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) auto
  show "x \<le> x \<squnion> y" by (cases x; cases y) auto
  show "y \<le> x \<squnion> y" by (cases x; cases y) auto
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" by (cases x; cases y; cases z) auto
  show "bot \<le> x" by (cases x) (simp_all add: bot_relc_def)
qed

end

text \<open>The vendored TD solver's \<open>TD_side_upd_rule\<close> locale fixes its equation
  value type at sort \<open>{bounded_semilattice_sup_bot, warrowing}\<close> uniformly --
  every update rule in the solver menu needs it, not only the \<open>warrow\<close>
  entry, even on a loop-free equation system where widening is never
  actually invoked.  \<open>widen = sup\<close> reuses the join laws already proved
  above; \<open>narrow a b = b\<close> is the simplest sound choice ("accept the
  incoming value, refine nothing") -- consistent with this file's own
  no-closure, no-normalization scope.\<close>

instantiation relc :: warrowing
begin

definition widen_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where
  "widen_relc a b = a \<squnion> b"

definition narrow_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where
  "narrow_relc a b = b"

instance
proof intro_classes
  fix a b :: relc
  show "a \<le> a \<nabla> b" by (simp add: widen_relc_def)
  show "b \<le> a \<nabla> b" by (simp add: widen_relc_def)
  show "b \<le> a \<Longrightarrow> b \<le> a \<Delta> b" by (simp add: narrow_relc_def)
  show "b \<le> a \<Longrightarrow> a \<Delta> b \<le> a" by (simp add: narrow_relc_def)
qed

end

text \<open>Registers the sort intersection under its named synonym -- the vendored
  solver's \<open>TD_side_upd_rule\<close> locale is generated against \<open>bounded_warrowing\<close>
  by name, not the raw \<open>{bounded_semilattice_sup_bot, warrowing}\<close> sort, and
  Isabelle does not compose that registration automatically from the two
  separate instances above.  \<^type>\<open>dg_state\<close> already carries the same
  explicit step generically (\<open>DG_Framework\<close>) once its component types
  have it.\<close>
instance relc :: bounded_warrowing ..

text \<open>\<open>top_relc\<close> is the empty-relation-set top element: vacuously true of
  every pair, so its concretization is \<open>UNIV\<close> (\<open>gamma_rel_top\<close>).\<close>
definition top_relc :: relc where
  "top_relc = RelC {}"

subsection \<open>Concretization\<close>

fun gamma_rel :: "relc \<Rightarrow> store set" where
  "gamma_rel Bot = {}"
| "gamma_rel (RelC ps) = {s. \<forall>(x, y) \<in> ps. s x \<le> s y}"

text \<open>
  Executable membership reader for downstream examples. \<open>Bot\<close> answers
  \<open>True\<close> for every pair: its concretization is empty, so every fact holds
  of it vacuously, and it never needs to materialize \<open>UNIV\<close>.
\<close>
fun relc_has :: "vname \<Rightarrow> vname \<Rightarrow> relc \<Rightarrow> bool" where
  "relc_has x y Bot = True"
| "relc_has x y (RelC ps) = ((x, y) \<in> ps)"

text \<open>Pretty-printer, the \<open>relc\<close> analogue of Interval's \<open>string_of_ivl\<close> for
  GraphViz/console display.  \<open>vname \<times> vname\<close> is \<open>linorder\<close> (via
  \<open>HOL-Library.Product_Lexorder\<close>, already imported transitively by every
  file in this session that touches \<^typ>\<open>cfg\<close>), so \<^const>\<open>sorted_list_of_set\<close>
  gives a deterministic, executable enumeration -- the same device this
  project already relies on for CFG edge sets.\<close>

fun string_of_pairs :: "(vname \<times> vname) list \<Rightarrow> string" where
  "string_of_pairs [] = ''''"
| "string_of_pairs [(x, y)] = String.explode x @ ''<='' @ String.explode y"
| "string_of_pairs ((x, y) # p # ps) =
     String.explode x @ ''<='' @ String.explode y @ '', '' @ string_of_pairs (p # ps)"

definition string_of_relc :: "relc \<Rightarrow> string" where
  "string_of_relc d =
     (case d of
        Bot \<Rightarrow> ''BOT''
      | RelC ps \<Rightarrow>
          (if ps = {} then ''(no known relations)''
           else string_of_pairs (sorted_list_of_set ps)))"

definition gammaDG_rel :: "relc \<Rightarrow> relc \<Rightarrow> store set" where
  "gammaDG_rel d g = gamma_rel d \<inter> gamma_rel g"

lemma gamma_rel_top [simp]: "gamma_rel top_relc = UNIV"
  unfolding top_relc_def by simp

lemma gammaDG_rel_top [simp]: "gammaDG_rel top_relc top_relc = UNIV"
  unfolding gammaDG_rel_def by simp

lemma gamma_rel_mono:
  assumes "d \<le> d'"
  shows "gamma_rel d \<subseteq> gamma_rel d'"
  using assms by (cases d; cases d') auto

lemma gammaDG_rel_mono:
  assumes "d \<le> d'" "g \<le> g'"
  shows "gammaDG_rel d g \<subseteq> gammaDG_rel d' g'"
  using gamma_rel_mono[OF assms(1)] gamma_rel_mono[OF assms(2)]
  unfolding gammaDG_rel_def by blast

subsection \<open>Forgetting a variable -- the one lemma every imprecise fallback reuses\<close>

fun forget_relc :: "vname \<Rightarrow> relc \<Rightarrow> relc" where
  "forget_relc x Bot = Bot"
| "forget_relc x (RelC ps) = RelC {(a, b) \<in> ps. a \<noteq> x \<and> b \<noteq> x}"

lemma forget_relc_sound[intro]:
  assumes "s \<in> gamma_rel d"
  shows "s(x := v) \<in> gamma_rel (forget_relc x d)"
  using assms by (cases d) auto

subsection \<open>The one precise transfer: recognizing a bare-variable strict order test\<close>

definition assume_step :: "exp \<Rightarrow> relc \<Rightarrow> relc" where
  "assume_step b d =
     (case d of
        Bot \<Rightarrow> Bot
      | RelC ps \<Rightarrow>
          (case b of
             Less (V x) (V y) \<Rightarrow> RelC (insert (x, y) ps)
           | _ \<Rightarrow> RelC ps))"

lemma assume_step_sound[intro]:
  assumes "s \<in> gamma_rel d" "truthy (aval b s)"
  shows "s \<in> gamma_rel (assume_step b d)"
proof (cases d)
  case Bot
  with assms(1) show ?thesis by simp
next
  case (RelC ps)
  note d_eq = RelC
  show ?thesis
  proof (cases "\<exists>x y. b = Less (V x) (V y)")
    case True
    then obtain x y where xy: "b = Less (V x) (V y)" by blast
    have "s x < s y" using assms(2) xy by (simp split: if_splits)
    then show ?thesis using assms(1) d_eq unfolding assume_step_def d_eq xy by auto
  next
    case False
    then show ?thesis
      using assms(1) d_eq unfolding assume_step_def d_eq
      by (auto split: exp.splits exp.splits)
  qed
qed

text \<open>The negated-guard counterpart: \<open>\<not>(x < y)\<close> is \<open>y \<le> x\<close>, the mirror image
  of \<open>assume_step\<close>'s one precise case, recorded on the false branch instead
  of discarded.  Every other shape falls back exactly as \<open>assume_step\<close>
  does.\<close>

definition assume_not_step :: "exp \<Rightarrow> relc \<Rightarrow> relc" where
  "assume_not_step b d =
     (case d of
        Bot \<Rightarrow> Bot
      | RelC ps \<Rightarrow>
          (case b of
             Less (V x) (V y) \<Rightarrow> RelC (insert (y, x) ps)
           | _ \<Rightarrow> RelC ps))"

lemma assume_not_step_sound[intro]:
  assumes "s \<in> gamma_rel d" "\<not> truthy (aval b s)"
  shows "s \<in> gamma_rel (assume_not_step b d)"
proof (cases d)
  case Bot
  with assms(1) show ?thesis by simp
next
  case (RelC ps)
  note d_eq = RelC
  show ?thesis
  proof (cases "\<exists>x y. b = Less (V x) (V y)")
    case True
    then obtain x y where xy: "b = Less (V x) (V y)" by blast
    have "\<not> s x < s y" using assms(2) xy by (simp split: if_splits)
    then show ?thesis using assms(1) d_eq unfolding assume_not_step_def d_eq xy by auto
  next
    case False
    then show ?thesis
      using assms(1) d_eq unfolding assume_not_step_def d_eq
      by (auto split: exp.splits exp.splits)
  qed
qed

subsection \<open>The transfer functions\<close>

text \<open>Every step except the two precise \<open>assume\<close>/\<open>assume_not\<close> cases above
  is sound by forgetting or by leaving the carrier untouched -- deliberately
  imprecise: no closure, no normalization, havoc-based calls.\<close>

definition dgs_skip_rel :: "relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_skip_rel d g = (g, d)"

definition dgs_assign_rel :: "vname \<Rightarrow> exp \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_assign_rel x e d g = (forget_relc x g, forget_relc x d)"

definition dgs_body_rel :: "pname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_body_rel p d g = (g, d)"

text \<open>
  \<open>return\<close> reuses the same forget-based imprecision \<open>dgs_assign_rel\<close> already
  applies to every ordinary assignment: with an expression, forget \<open>ret_var\<close>;
  without one, behave like \<open>skip\<close>.
\<close>
definition dgs_return_rel :: "exp option \<Rightarrow> pname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_return_rel e p d g = (case e of None \<Rightarrow> dgs_skip_rel d g | Some a \<Rightarrow> dgs_assign_rel ret_var a d g)"

definition dgs_special_rel :: "special_call \<Rightarrow> vname \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_special_rel sc x d g = (forget_relc x g, forget_relc x d)"

text \<open>A check observes its condition but never refines the state, matching
  \<open>dgs_skip_rel\<close>'s own imprecision.\<close>
definition dgs_event_rel :: "analysis_event \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_event_rel ev d g = (g, d)"

text \<open>
  \<open>assume_step\<close>/\<open>assume_not_step\<close> stay separate, genuinely asymmetric
  operations (\<open>x < y\<close> vs.\ its mirror \<open>y \<le> x\<close> insert different pairs, not
  the same formula under a polarity flag); only the interface-level dispatch
  consolidates into one @{text tf_branch}-shaped operation.
\<close>
definition branch_step_rel :: "exp \<Rightarrow> bool \<Rightarrow> relc \<Rightarrow> relc" where
  "branch_step_rel b pol d = (if pol then assume_step b d else assume_not_step b d)"

definition dgs_branch_rel :: "exp \<Rightarrow> bool \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_branch_rel b pol d g = (g, branch_step_rel b pol d)"

definition dgs_enter_rel :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_enter_rel ci dc g = (top_relc, top_relc)"

text \<open>
  The caller continuation is the identity.  This carrier discards every caller
  relation at its environment merge anyway, so there is no call-side
  invalidation for a continuation to express: filtering before a merge that
  already returns \<^const>\<open>top_relc\<close> would be indistinguishable from not filtering.
  Keeping it identity leaves this instance the least interesting sound one, which
  is its purpose.
\<close>
definition dgs_caller_cont_rel :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc" where
  "dgs_caller_cont_rel ci dc g = dc"

definition dgs_combine_env_rel :: "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "dgs_combine_env_rel ci dc de g = (top_relc, top_relc)"

definition dgs_combine_assign_rel ::
  "call_info \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc \<Rightarrow> relc \<times> relc"
where
  "dgs_combine_assign_rel ci de g merged = merged"

text \<open>
  Unlike the local-only domains, this one really uses the global channel:
  \<^const>\<open>dgs_special_rel\<close> forgets the assigned name on both halves, and entry
  and the environment merge reset the shared relation to \<^const>\<open>top_relc\<close>.
  Its transfers are therefore written as a read-compute-publish sequence.

  \<open>rel_transfer\<close> is the adapter that turns one of this file's
  \<open>d \<Rightarrow> g \<Rightarrow> (g, d)\<close> operations into a manager transfer: query the shared
  relation, run the operation, publish its global half, answer with its local
  half. That pairing shape used to be the only interface; here it survives as
  one domain's private convenience, which is the point.
\<close>

definition rel_transfer ::
  "(relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc) \<Rightarrow> ('x,'k,relc,relc) man_transfer"
where
  "rel_transfer f m =
     do {
       g \<leftarrow> man_global m;
       let r = f (man_local m) g;
       _ \<leftarrow> man_sideg m (fst r);
       sp_return (snd r)
     }"

definition rel_combine_transfer ::
  "(relc \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc) \<Rightarrow> ('x,'k,relc,relc) man_combine_transfer"
where
  "rel_combine_transfer f m de =
     do {
       g \<leftarrow> man_global m;
       let r = f (man_local m) de g;
       _ \<leftarrow> man_sideg m (fst r);
       sp_return (snd r)
     }"

text \<open>The observations of a compiled \<open>rel_transfer\<close>: its answer is the operation's
  local half, and what it publishes at the routed key is the global half. These are
  what \<^locale>\<open>sound_dg_spec\<close> is stated against.\<close>

lemma traverse_rel_transfer [simp]:
  "locals (traverse_rhs (transfer_tree (rel_transfer f) src gk) \<tau>)
     = snd (f (locals (\<tau> src)) (globs (\<tau> (Inr gk))))"
  by (cases src)
     (simp_all add: transfer_tree_def dg_edge_tree_man_def rel_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc
        Let_def)

lemma sides_rel_transfer [simp]:
  "globs (sides_of_rhs (transfer_tree (rel_transfer f) src gk) \<tau> (Inr gk))
     = fst (f (locals (\<tau> src)) (globs (\<tau> (Inr gk))))"
  by (cases src)
     (simp_all add: transfer_tree_def dg_edge_tree_man_def rel_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc
        Let_def)

definition rel_order_spec :: "('x,'k,relc,relc) dg_spec" where
  "rel_order_spec = default_local_dg_spec\<lparr>
     dgs_skip := rel_transfer dgs_skip_rel,
     dgs_assign := (\<lambda>x e. rel_transfer (dgs_assign_rel x e)),
     dgs_special := (\<lambda>sc x. rel_transfer (dgs_special_rel sc x)),
     dgs_branch := (\<lambda>b pol. rel_transfer (dgs_branch_rel b pol)),
     dgs_body := (\<lambda>p. rel_transfer (dgs_body_rel p)),
     dgs_return := (\<lambda>e p. rel_transfer (dgs_return_rel e p)),
     dgs_enter := (\<lambda>ci. rel_transfer (dgs_enter_rel ci)),
     dgs_event := (\<lambda>ev. rel_transfer (dgs_event_rel ev)),
     dgs_combine_env := (\<lambda>ci. rel_combine_transfer (dgs_combine_env_rel ci))
   \<rparr>"

text \<open>The unknown and global-key types occur only inside this specification's transfer
  programs, never in an argument that builds it, so it has no most general ML type and
  cannot be a generated value. It is a construction-time description, unfolded where it
  is used.\<close>
declare rel_order_spec_def [code_unfold]

named_theorems rel_order_simps

declare
  dgs_branch_rel_def     [rel_order_simps]
  branch_step_rel_def    [rel_order_simps]
  dgs_skip_rel_def       [rel_order_simps]
  dgs_body_rel_def       [rel_order_simps]
  dgs_return_rel_def     [rel_order_simps]
  dgs_event_rel_def      [rel_order_simps]
  rel_order_spec_def     [rel_order_simps]
  gammaDG_rel_def        [rel_order_simps]
  dgs_assign_rel_def     [rel_order_simps]
  dgs_special_rel_def    [rel_order_simps]

subsection \<open>Per-edge soundness\<close>

lemma dgs_skip_rel_sound[intro]:
  "edge_collect EA_Nop (gammaDG_rel d g) \<subseteq>
     (case dgs_skip_rel d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
  unfolding dgs_skip_rel_def by simp

lemma dgs_assign_rel_sound[intro]:
  "edge_collect (EA_Assign x e) (gammaDG_rel d g) \<subseteq>
     (case dgs_assign_rel x e d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof -
  have "edge_collect (EA_Assign x e) (gammaDG_rel d g)
      = {s(x := aval e s) | s. s \<in> gammaDG_rel d g}"
    by simp
  also have "... \<subseteq> gamma_rel (forget_relc x d) \<inter> gamma_rel (forget_relc x g)"
    using forget_relc_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    unfolding dgs_assign_rel_def gammaDG_rel_def by simp
qed

lemma dgs_special_rel_sound[intro]:
  "edge_collect (EA_Special sc x) (gammaDG_rel d g) \<subseteq>
     (case dgs_special_rel sc x d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof -
  have "edge_collect (EA_Special sc x) (gammaDG_rel d g)
      \<subseteq> {s(x := v) | s v. s \<in> gammaDG_rel d g}"
    by (cases sc) auto
  also have "... \<subseteq> gamma_rel (forget_relc x d) \<inter> gamma_rel (forget_relc x g)"
    using forget_relc_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    unfolding dgs_special_rel_def gammaDG_rel_def by simp
qed

lemma dgs_branch_rel_sound_True[intro]:
  "edge_collect (EA_Assume b) (gammaDG_rel d g) \<subseteq>
     (case dgs_branch_rel b True d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof -
  have "edge_collect (EA_Assume b) (gammaDG_rel d g)
      = {s. s \<in> gammaDG_rel d g \<and> truthy (aval b s)}"
    by simp
  also have "... \<subseteq> gamma_rel (assume_step b d) \<inter> gamma_rel g"
    using assume_step_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    unfolding dgs_branch_rel_def branch_step_rel_def gammaDG_rel_def by simp
qed

lemma dgs_branch_rel_sound_False[intro]:
  "edge_collect (EA_AssumeNot b) (gammaDG_rel d g) \<subseteq>
     (case dgs_branch_rel b False d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof -
  have "edge_collect (EA_AssumeNot b) (gammaDG_rel d g)
      = {s. s \<in> gammaDG_rel d g \<and> \<not> truthy (aval b s)}"
    by simp
  also have "... \<subseteq> gamma_rel (assume_not_step b d) \<inter> gamma_rel g"
    using assume_not_step_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    unfolding dgs_branch_rel_def branch_step_rel_def gammaDG_rel_def by simp
qed

lemma dgs_ret_rel_sound[intro]:
  "edge_collect (EA_Ret e p) (gammaDG_rel d g) \<subseteq>
     (case dgs_return_rel e p d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
proof (cases e)
  case None
  then show ?thesis
    by (simp add: dgs_return_rel_def dgs_skip_rel_def)
next
  case (Some a)
  have "edge_collect (EA_Ret (Some a) p) (gammaDG_rel d g)
      = {s(ret_var := aval a s) | s. s \<in> gammaDG_rel d g}"
    by simp
  also have "... \<subseteq> gamma_rel (forget_relc ret_var d) \<inter> gamma_rel (forget_relc ret_var g)"
    using forget_relc_sound unfolding gammaDG_rel_def by blast
  finally show ?thesis
    using Some
    by (simp add: dgs_return_rel_def dgs_assign_rel_def gammaDG_rel_def)
qed

text \<open>The edge dispatch as one pure pairing operation, so the specification's
  compiled step reduces to \<^const>\<open>rel_transfer\<close> of it.\<close>

fun rel_step_for :: "edge_action \<Rightarrow> relc \<Rightarrow> relc \<Rightarrow> relc \<times> relc" where
  "rel_step_for EA_Nop = dgs_skip_rel"
| "rel_step_for (EA_Assign x e) = dgs_assign_rel x e"
| "rel_step_for (EA_Special sc x) = dgs_special_rel sc x"
| "rel_step_for (EA_Assume b) = dgs_branch_rel b True"
| "rel_step_for (EA_AssumeNot b) = dgs_branch_rel b False"
| "rel_step_for (EA_Ret e p) = dgs_return_rel e p"
| "rel_step_for (EA_Check cnd) = dgs_event_rel (Check_Event cnd)"

lemma dg_spec_step_rel_order_spec [simp]:
  "dg_spec_step rel_order_spec a = rel_transfer (rel_step_for a)"
  unfolding rel_order_spec_def by (cases a) simp_all

lemma dgs_enter_rel_order_spec [simp]:
  "dgs_enter rel_order_spec ci = rel_transfer (dgs_enter_rel ci)"
  unfolding rel_order_spec_def by simp

lemma step_sound_rel:
  "edge_collect a (gammaDG_rel d g) \<subseteq>
     (case rel_step_for a d g of (g', d') \<Rightarrow> gammaDG_rel d' g')"
  by (cases a) (auto simp add: rel_order_simps split: option.splits)

subsection \<open>Call-entry and combine soundness -- havoc-based, both trivial via \<open>top_relc\<close>\<close>

text \<open>The composed return pipeline: \<open>caller_cont\<close> and \<open>combine_assign\<close> are the
  defaults, so the whole combine is the environment merge, which resets both halves
  to \<^const>\<open>top_relc\<close>.\<close>

lemma dg_spec_combine_transfer_rel_order_spec [simp]:
  "dg_spec_combine_transfer rel_order_spec ci = rel_combine_transfer (dgs_combine_env_rel ci)"
  unfolding dg_spec_combine_transfer_def dgs_combine_def rel_order_spec_def
  by (intro ext)
     (simp add: local_transfer_def local_combine_transfer_def man_with_local_def
        rel_combine_transfer_def)

lemma traverse_rel_combine [simp]:
  "locals (traverse_rhs (combine_transfer_tree (rel_combine_transfer f) src_cc src_ex gk) \<tau>)
     = snd (f (locals (\<tau> src_cc)) (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def rel_combine_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc Let_def)

lemma sides_rel_combine [simp]:
  "globs (sides_of_rhs (combine_transfer_tree (rel_combine_transfer f) src_cc src_ex gk)
            \<tau> (Inr gk))
     = fst (f (locals (\<tau> src_cc)) (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def rel_combine_transfer_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc Let_def)

subsection \<open>The interpretation\<close>

interpretation rel_order: sound_dg_spec rel_order_spec gammaDG_rel is_global
proof unfold_locales
  fix d d' :: relc and g g' :: relc
  show "d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> gammaDG_rel d g \<subseteq> gammaDG_rel d' g'"
    by (rule gammaDG_rel_mono)
next
  fix a and \<tau> :: "'a + 'b \<Rightarrow> (relc, relc) dg_state" and src gk
  show "edge_collect a (gammaDG_rel (locals (\<tau> src)) (globs (\<tau> (Inr gk))))
          \<subseteq> gammaDG_rel (locals (traverse_rhs (dg_spec_edge_tree rel_order_spec a src gk) \<tau>))
              (globs (sides_of_rhs (dg_spec_edge_tree rel_order_spec a src gk) \<tau> (Inr gk)))"
    using step_sound_rel[of a "locals (\<tau> src)" "globs (\<tau> (Inr gk))"]
    by (simp add: dg_spec_edge_tree_def split: prod.splits)
next
  fix s and \<tau> :: "'a + 'b \<Rightarrow> (relc, relc) dg_state" and src gk ci
  show "s \<in> gammaDG_rel (locals (\<tau> src)) (globs (\<tau> (Inr gk))) \<Longrightarrow>
          call_enter is_global (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
            \<in> gammaDG_rel
                (locals (traverse_rhs (transfer_tree (dgs_enter rel_order_spec ci) src gk) \<tau>))
                (globs (sides_of_rhs (transfer_tree (dgs_enter rel_order_spec ci) src gk)
                          \<tau> (Inr gk)))"
    by (simp add: dgs_enter_rel_def)
next
  fix s t and \<tau> :: "'a + 'b \<Rightarrow> (relc, relc) dg_state" and src_cc src_ex gk ci
  show "\<lbrakk>s \<in> gammaDG_rel (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk)));
         t \<in> gammaDG_rel (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk)))\<rbrakk> \<Longrightarrow>
          combine_collect is_global (ci_dst ci) s t
            \<in> gammaDG_rel
                (locals (traverse_rhs
                   (dg_spec_combine_tree rel_order_spec ci src_cc src_ex gk) \<tau>))
                (globs (sides_of_rhs
                   (dg_spec_combine_tree rel_order_spec ci src_cc src_ex gk) \<tau> (Inr gk)))"
    by (simp add: dg_spec_combine_tree_def dg_spec_combine_transfer_rel_order_spec
        dgs_combine_env_rel_def)
qed

end
