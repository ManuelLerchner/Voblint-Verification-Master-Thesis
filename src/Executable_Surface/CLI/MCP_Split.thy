theory MCP_Split
  imports MCP_Analyses
begin

section \<open>The registered analyses with program globals on the shared channel\<close>

text \<open>
  The ownership-split placement recombines local and global information and
  projects a state onto its local part, its global part, or one named global. On the combined
  state they are defined field by field, so a carrier that splits is a type class
  closed under the constructors the combined state is built from. A pointwise field
  splits by the location each name is stored at; the relational field relates
  variables across the split and stays wholly local.
\<close>

class ownership_split = order_bot +
  fixes split_cmb :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and split_rl :: "'a \<Rightarrow> 'a"
    and split_global_at :: "vname \<Rightarrow> 'a \<Rightarrow> 'a"
    and split_rg :: "'a \<Rightarrow> 'a"
    and split_free :: "vname list \<Rightarrow> 'a"
  assumes split_cmb_mono: "d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> split_cmb d g \<le> split_cmb d' g'"
    and split_recombine: "split_cmb (split_rl x) (split_rg x) = x"
    and split_cmb_rl: "split_cmb (split_rl x) g = split_cmb x g"
    and split_rl_cmb: "split_rl (split_cmb d g) = split_rl d"
    and split_global_at_mono: "d \<le> d' \<Longrightarrow> split_global_at n d \<le> split_global_at n d'"
    and split_free_ge: "n \<notin> set R \<Longrightarrow> split_global_at n d \<le> split_free R"
    and split_global_at_bot: "split_global_at n bot = bot"

text \<open>
  \<open>split_free R\<close> is the global half a transfer reads in place of every global
  outside \<open>R\<close>: it claims nothing about those names and leaves the names in \<open>R\<close>
  to the values actually read.
\<close>

instantiation default_st :: ("{order_bot, order_top}") ownership_split
begin

definition split_cmb_default_st :: "'a default_st \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st" where
  "split_cmb_default_st = combine_default_st"

definition split_rl_default_st :: "'a default_st \<Rightarrow> 'a default_st" where
  "split_rl_default_st = restrict_local_default_st"

definition split_rg_default_st :: "'a default_st \<Rightarrow> 'a default_st" where
  "split_rg_default_st = restrict_global_default_st"

definition split_global_at_default_st :: "vname \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st" where
  "split_global_at_default_st x d =
     (bot\<langle>(Global_Location x) := (d\<langle>(Global_Location x)\<rangle>)\<rangle>)"

definition split_free_default_st :: "vname list \<Rightarrow> 'a default_st" where
  "split_free_default_st R = \<llangle>(bot, []), (top, map (\<lambda>x. (x, bot)) R)\<rrangle>"

lemma split_free_default_st_get:
  "(split_free R :: 'a default_st)\<langle>loc\<rangle> =
     (case loc of Global_Location x \<Rightarrow> if x \<in> set R then bot else top | _ \<Rightarrow> bot)"
  by (cases loc) (simp_all add: split_free_default_st_def map_of_map_restrict
      restrict_map_def)

instance
proof
  fix d d' g g' :: "'a default_st"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb d g \<le> split_cmb d' g'"
    by (auto simp: split_cmb_default_st_def le_default_st_iff split: location.split)
next
  fix n :: vname and R and d :: "'a default_st"
  assume "n \<notin> set R"
  then show "split_global_at n d \<le> split_free R"
    by (auto simp: le_default_st_iff split_global_at_default_st_def split_free_default_st_get
        split: location.split)
next
  fix n :: vname
  show "split_global_at n (bot :: 'a default_st) = bot"
    by (rule default_st_eqI) (simp add: split_global_at_default_st_def)
qed (auto simp: split_cmb_default_st_def split_rl_default_st_def split_rg_default_st_def
    split_global_at_default_st_def le_default_st_iff)

end

instantiation relc :: ownership_split
begin

definition split_cmb_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where "split_cmb_relc d g = d"
definition split_rl_relc :: "relc \<Rightarrow> relc" where "split_rl_relc d = d"
definition split_rg_relc :: "relc \<Rightarrow> relc" where "split_rg_relc d = bot"

definition split_global_at_relc :: "vname \<Rightarrow> relc \<Rightarrow> relc" where
  "split_global_at_relc x d = bot"

definition split_free_relc :: "vname list \<Rightarrow> relc" where "split_free_relc R = bot"

instance
  by standard (simp_all add: split_cmb_relc_def split_rl_relc_def split_rg_relc_def
      split_global_at_relc_def split_free_relc_def)

end

instantiation analysis_product :: (ownership_split, ownership_split) ownership_split
begin

definition split_cmb_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_cmb_analysis_product d g =
     Product (split_cmb (pleft d) (pleft g)) (split_cmb (pright d) (pright g))"

definition split_rl_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_rl_analysis_product d = Product (split_rl (pleft d)) (split_rl (pright d))"

definition split_rg_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_rg_analysis_product d = Product (split_rg (pleft d)) (split_rg (pright d))"

definition split_global_at_analysis_product ::
  "vname \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_global_at_analysis_product x d =
     Product (split_global_at x (pleft d)) (split_global_at x (pright d))"

definition split_free_analysis_product :: "vname list \<Rightarrow> ('a, 'b) analysis_product" where
  "split_free_analysis_product R = Product (split_free R) (split_free R)"

instance
proof
  fix d d' g g' :: "('a, 'b) analysis_product"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb d g \<le> split_cmb d' g'"
    by (simp add: split_cmb_analysis_product_def less_eq_analysis_product_def split_cmb_mono)
next
  fix x g :: "('a, 'b) analysis_product"
  show "split_cmb (split_rl x) (split_rg x) = x"
    by (cases x) (simp add: split_cmb_analysis_product_def split_rl_analysis_product_def
        split_rg_analysis_product_def split_recombine)
  show "split_cmb (split_rl x) g = split_cmb x g"
    by (simp add: split_cmb_analysis_product_def split_rl_analysis_product_def split_cmb_rl)
next
  fix d g :: "('a, 'b) analysis_product"
  show "split_rl (split_cmb d g) = split_rl d"
    by (simp add: split_cmb_analysis_product_def split_rl_analysis_product_def split_rl_cmb)
next
  fix d d' :: "('a, 'b) analysis_product" and x
  assume "d \<le> d'"
  then show "split_global_at x d \<le> split_global_at x d'"
    by (simp add: split_global_at_analysis_product_def less_eq_analysis_product_def
      split_global_at_mono)
next
  fix n :: vname and R and d :: "('a, 'b) analysis_product"
  assume "n \<notin> set R"
  then show "split_global_at n d \<le> split_free R"
    by (simp add: split_global_at_analysis_product_def split_free_analysis_product_def
        less_eq_analysis_product_def split_free_ge)
next
  fix n :: vname
  show "split_global_at n (bot :: ('a, 'b) analysis_product) = bot"
    by (simp add: split_global_at_analysis_product_def bot_analysis_product_def
        split_global_at_bot)
qed

end

text \<open>
  An unreachable point stays unreachable whatever global it is recombined with, and
  a reachable point recombined with a global nothing has published yet reads the
  global half at its bottom.
\<close>

instantiation lifted :: ("{ownership_split, semilattice_sup}") ownership_split
begin

definition split_cmb_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "split_cmb_lifted d g = (case d of Bot \<Rightarrow> Bot
     | Lifted a \<Rightarrow> Lifted (split_cmb a (case g of Bot \<Rightarrow> bot | Lifted b \<Rightarrow> b)))"

definition split_rl_lifted :: "'a lifted \<Rightarrow> 'a lifted" where
  "split_rl_lifted = map_lift split_rl"

definition split_rg_lifted :: "'a lifted \<Rightarrow> 'a lifted" where
  "split_rg_lifted = map_lift split_rg"

definition split_global_at_lifted :: "vname \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "split_global_at_lifted x = map_lift (split_global_at x)"

definition split_free_lifted :: "vname list \<Rightarrow> 'a lifted" where
  "split_free_lifted R = Lifted (split_free R)"

instance
proof
  fix d d' g g' :: "'a lifted"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb d g \<le> split_cmb d' g'"
    by (cases d; cases d'; cases g; cases g')
       (auto simp: split_cmb_lifted_def intro: split_cmb_mono)
next
  fix x g :: "'a lifted"
  show "split_cmb (split_rl x) (split_rg x) = x"
    by (cases x) (simp_all add: split_cmb_lifted_def split_rl_lifted_def split_rg_lifted_def
        split_recombine)
  show "split_cmb (split_rl x) g = split_cmb x g"
    by (cases x) (simp_all add: split_cmb_lifted_def split_rl_lifted_def split_cmb_rl)
next
  fix d g :: "'a lifted"
  show "split_rl (split_cmb d g) = split_rl d"
    by (cases d) (simp_all add: split_cmb_lifted_def split_rl_lifted_def split_rl_cmb)
next
  fix d d' :: "'a lifted" and x
  assume "d \<le> d'"
  then show "split_global_at x d \<le> split_global_at x d'"
    by (cases d; cases d') (simp_all add: split_global_at_lifted_def split_global_at_mono)
next
  fix n :: vname and R and d :: "'a lifted"
  assume "n \<notin> set R"
  then show "split_global_at n d \<le> split_free R"
    by (cases d) (simp_all add: split_global_at_lifted_def split_free_lifted_def split_free_ge)
next
  fix n :: vname
  show "split_global_at n (bot :: 'a lifted) = bot"
    by (simp add: split_global_at_lifted_def)
qed

end

lemma split_cmb_Bot [simp]:
  "split_cmb (Bot :: 'a::{ownership_split, semilattice_sup} lifted) g = Bot"
  by (simp add: split_cmb_lifted_def)

subsection \<open>Reading a keyed recombination back\<close>

text \<open>
  A keyed point's state is its local half recombined with the solved environment
  over the declared globals. Read back, every local comes from the point and every
  declared global from that global's own unknown. The lemmas below establish this
  for one field and lift it through the fields of the combined state.
\<close>

lemma split_global_at_default_st_get [simp]:
  "((split_global_at x d)\<langle>loc\<rangle>) =
     (if loc = Global_Location x then (d\<langle>loc\<rangle>) else bot)"
  by (auto simp: split_global_at_default_st_def)

lemma view_of_default_st_get:
  "(view_of split_global_at xs E acc :: 'a::{bounded_semilattice_sup_bot, order_top} default_st)\<langle>loc\<rangle>
     = acc\<langle>loc\<rangle> \<squnion> (case loc of Global_Location y \<Rightarrow> if y \<in> set xs then (E y)\<langle>loc\<rangle> else bot
                       | Local_Location y \<Rightarrow> bot)"
  unfolding view_of_def
  by (induction xs arbitrary: acc)
     (auto simp: split_global_at_default_st_def ac_simps split: location.split)

text \<open>The value a lifted state carries, \<open>bot\<close> when unreachable.\<close>

fun lift_val :: "'a::bot lifted \<Rightarrow> 'a" where
  "lift_val Bot = bot"
| "lift_val (Lifted a) = a"

lemma lift_val_sup:
  "lift_val (a \<squnion> b) = lift_val a \<squnion> lift_val (b :: 'a::bounded_semilattice_sup_bot lifted)"
  by (cases a; cases b) simp_all

lemma split_cmb_Lifted:
  "split_cmb (Lifted a) g = Lifted (split_cmb a (lift_val (g :: 'a::{ownership_split, semilattice_sup} lifted)))"
  by (cases g) (simp_all add: split_cmb_lifted_def)

lemma lift_val_view_of:
  "lift_val (view_of split_global_at xs E acc :: 'a::{ownership_split, bounded_semilattice_sup_bot} lifted)
     = view_of split_global_at xs (\<lambda>y. lift_val (E y)) (lift_val acc)"
  unfolding view_of_def
proof (induction xs arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  have "lift_val (split_global_at x (E x)) = split_global_at x (lift_val (E x))"
    by (cases "E x") (simp_all add: split_global_at_lifted_def split_global_at_bot)
  with Cons show ?case by (simp add: lift_val_sup)
qed

text \<open>A map between carriers that commutes with the split operations, such as the
  projection onto one field of a product. Read-back facts proved for a field lift
  along it.\<close>

locale split_hom =
  fixes f :: "'a::{ownership_split, bounded_semilattice_sup_bot}
              \<Rightarrow> 'b::{ownership_split, bounded_semilattice_sup_bot}"
  assumes hom_cmb: "f (split_cmb a b) = split_cmb (f a) (f b)"
    and hom_rl: "f (split_rl a) = split_rl (f a)"
    and hom_at: "f (split_global_at x a) = split_global_at x (f a)"
    and hom_sup: "f (a \<squnion> b) = f a \<squnion> f b"
    and hom_bot: "f bot = bot"
begin

lemma hom_view_of:
  "f (view_of split_global_at xs E acc) = view_of split_global_at xs (\<lambda>y. f (E y)) (f acc)"
  unfolding view_of_def by (induction xs arbitrary: acc) (simp_all add: hom_sup hom_at)

lemma lift_get_hom: "lift_get f x = f (lift_val x)"
  by (cases x) (simp_all add: hom_bot)

end

text \<open>
  The read-back of one field of a keyed recombination: a local reads from the point,
  a declared global from the field of that global's unknown.
\<close>

lemma keyed_field_read:
  fixes f :: "'a::{ownership_split, bounded_semilattice_sup_bot}
              \<Rightarrow> 'c::{ownership_split, bounded_semilattice_sup_bot} lifted"
    and E :: "vname \<Rightarrow> 'a lifted"
  assumes hom: "split_hom f" and fa: "f a = Lifted st"
  shows "lift_get f (split_cmb (Lifted a) (full_view split_global_at xs E))
    = Lifted (split_cmb st (view_of split_global_at xs (\<lambda>y. lift_val (lift_get f (E y))) bot))"
proof -
  interpret split_hom f by (rule hom)
  have "lift_get f (split_cmb (Lifted a) (full_view split_global_at xs E))
      = split_cmb (f a) (view_of split_global_at xs (\<lambda>y. lift_get f (E y)) bot)"
    by (simp add: split_cmb_Lifted full_view_def hom_cmb hom_view_of hom_bot lift_val_view_of
        lift_get_hom)
  then show ?thesis
    using fa by (simp add: split_cmb_Lifted lift_val_view_of)
qed

lemma keyed_field_gamma:
  fixes f ::
    "'a::{ownership_split, bounded_semilattice_sup_bot} \<Rightarrow> 'c::numeric_domain default_st lifted"
    and E :: "vname \<Rightarrow> 'a lifted"
  assumes hom: "split_hom f" and fa: "f a = Lifted st" and G: "\<And>y. \<G> y \<longleftrightarrow> y \<in> set xs"
  shows "s \<in> gamma_lift (default_st_gamma \<G>) (lift_get f (split_cmb (Lifted a) (full_view split_global_at xs E)))
    \<longleftrightarrow> (\<forall>y. s y \<in> \<gamma> (if y \<in> set xs then (lift_val (lift_get f (E y)))\<langle>Global_Location y\<rangle>
                         else st\<langle>Local_Location y\<rangle>))"
  by (simp add: keyed_field_read[OF hom fa] gamma_lift_def default_st_gamma_def gamma_state_def
      default_st_to_fun_def location_of_def G split_cmb_default_st_def view_of_default_st_get)

lemma default_st_gamma_iff:
  "s \<in> default_st_gamma \<G> st \<longleftrightarrow> (\<forall>y. s y \<in> \<gamma> (st\<langle>location_of \<G> y\<rangle>))"
  by (simp add: default_st_gamma_def gamma_state_def default_st_to_fun_def)

text \<open>
  The frame law for one field: a store the transfer's result describes, agreeing
  outside the written names with a store the point described, is described by the
  result's locals and written globals together with the environment elsewhere.
\<close>

lemma keyed_field_mix:
  fixes f ::
    "'a::{ownership_split, bounded_semilattice_sup_bot} \<Rightarrow> 'c::numeric_domain default_st lifted"
  assumes hom: "split_hom f" and G: "\<And>y. \<G> y \<longleftrightarrow> y \<in> set xs"
    and s:
      "s \<in> gamma_lift (default_st_gamma \<G>) (lift_get f (split_cmb l0 (full_view split_global_at xs e)))"
    and s': "s' \<in> gamma_lift (default_st_gamma \<G>) (lift_get f r)"
    and fr: "\<forall>x. \<G> x \<longrightarrow> x \<notin> set W \<longrightarrow> s' x = s x"
  shows "s' \<in> gamma_lift (default_st_gamma \<G>) (lift_get f (split_cmb (split_rl r)
           (full_view split_global_at xs (\<lambda>x. if x \<in> set W then split_global_at x r else e x))))"
proof -
  interpret split_hom f by (rule hom)
  obtain ri where r: "r = Lifted ri" using s' by (cases r) simp_all
  obtain stR where fr_i: "f ri = Lifted stR" using s' r by (cases "f ri") simp_all
  obtain a0 where l0: "l0 = Lifted a0" using s by (cases l0) simp_all
  obtain st0 where fa0: "f a0 = Lifted st0"
    using s l0 by (cases "f a0") (simp_all add: split_cmb_Lifted hom_cmb)
  have rl: "split_rl r = Lifted (split_rl ri)" by (simp add: r split_rl_lifted_def)
  have frl: "f (split_rl ri) = Lifted (split_rl stR)" by (simp add: hom_rl fr_i split_rl_lifted_def)
  have s'R: "\<forall>y. s' y \<in> \<gamma> (stR\<langle>location_of \<G> y\<rangle>)"
    using s' by (simp add: r fr_i default_st_gamma_iff)
  have s0: "\<forall>y. s y \<in> \<gamma> (if y \<in> set xs then (lift_val (lift_get f (e y)))\<langle>Global_Location y\<rangle>
                       else st0\<langle>Local_Location y\<rangle>)"
    using s by (simp add: l0 keyed_field_gamma[OF hom fa0 G])
  show ?thesis
    unfolding rl keyed_field_gamma[OF hom frl G]
  proof
    fix y
    show "s' y \<in> \<gamma> (if y \<in> set xs then (lift_val (lift_get f
        (if y \<in> set W then split_global_at y r else e y)))\<langle>Global_Location y\<rangle>
        else (split_rl stR)\<langle>Local_Location y\<rangle>)"
    proof (cases "y \<in> set xs")
      case False
      then show ?thesis using s'R[rule_format, of y]
        by (simp add: G location_of_def split_rl_default_st_def)
    next
      case xs: True
      show ?thesis
      proof (cases "y \<in> set W")
        case True
        then show ?thesis using xs s'R[rule_format, of y]
          by (simp add: G location_of_def r split_global_at_lifted_def hom_at fr_i)
      next
        case False
        then show ?thesis using xs s0[rule_format, of y] fr G by simp
      qed
    qed
  qed
qed

text \<open>A state is described by its local half recombined with its own cuts.\<close>

lemma keyed_field_init:
  fixes f ::
    "'a::{ownership_split, bounded_semilattice_sup_bot} \<Rightarrow> 'c::numeric_domain default_st lifted"
  assumes hom: "split_hom f" and G: "\<And>y. \<G> y \<longleftrightarrow> y \<in> set xs"
  shows "gamma_lift (default_st_gamma \<G>) (lift_get f (Lifted i))
    \<subseteq> gamma_lift (default_st_gamma \<G>) (lift_get f (split_cmb (Lifted i)
         (full_view split_global_at xs (\<lambda>x. split_global_at x (Lifted i)))))"
proof
  interpret split_hom f by (rule hom)
  fix s assume s: "s \<in> gamma_lift (default_st_gamma \<G>) (lift_get f (Lifted i))"
  then obtain st where fi: "f i = Lifted st" by (cases "f i") simp_all
  show "s \<in> gamma_lift (default_st_gamma \<G>) (lift_get f (split_cmb (Lifted i)
      (full_view split_global_at xs (\<lambda>x. split_global_at x (Lifted i)))))"
    using s unfolding keyed_field_gamma[OF hom fi G]
    by (auto simp: fi default_st_gamma_iff location_of_def G split_global_at_lifted_def hom_at
        split: if_splits)
qed

text \<open>
  Each numeric field of the combined state is reached through a slot that commutes
  with the split operations, because they are defined field by field.
\<close>

lemma split_hom_pleft: "split_hom (pleft :: ('a::{ownership_split, bounded_semilattice_sup_bot},
    'b::{ownership_split, bounded_semilattice_sup_bot}) analysis_product \<Rightarrow> 'a)"
  by unfold_locales
     (simp_all add: split_cmb_analysis_product_def split_rl_analysis_product_def
       split_global_at_analysis_product_def sup_analysis_product_def bot_analysis_product_def)

lemma split_hom_pright: "split_hom (pright :: ('a::{ownership_split, bounded_semilattice_sup_bot},
    'b::{ownership_split, bounded_semilattice_sup_bot}) analysis_product \<Rightarrow> 'b)"
  by unfold_locales
     (simp_all add: split_cmb_analysis_product_def split_rl_analysis_product_def
       split_global_at_analysis_product_def sup_analysis_product_def bot_analysis_product_def)

lemma split_hom_comp: "split_hom f \<Longrightarrow> split_hom g \<Longrightarrow> split_hom (f \<circ> g)"
  unfolding split_hom_def by simp

lemma split_hom_slots:
  "split_hom slot1" "split_hom slot2" "split_hom slot3" "split_hom slot4" "split_hom slot5"
  "split_hom slot6" "split_hom slot7"
proof -
  note h = split_hom_comp split_hom_pleft split_hom_pright
  have eqs: "slot1 = pleft" "slot2 = pleft \<circ> pright" "slot3 = pleft \<circ> pright \<circ> pright"
    "slot4 = pleft \<circ> pright \<circ> pright \<circ> pright"
    "slot5 = pleft \<circ> pright \<circ> pright \<circ> pright \<circ> pright"
    "slot6 = pleft \<circ> pright \<circ> pright \<circ> pright \<circ> pright \<circ> pright"
    "slot7 = pleft \<circ> pright \<circ> pright \<circ> pright \<circ> pright \<circ> pright \<circ> pright"
    by (simp_all add: fun_eq_iff)
  show "split_hom slot1" "split_hom slot2" "split_hom slot3" "split_hom slot4" "split_hom slot5"
    "split_hom slot6" "split_hom slot7"
    unfolding eqs by (intro h)+
qed

text \<open>The relational field keeps its whole state locally, so recombining leaves it alone.\<close>

lemma slot8_keyed:
  "lift_get slot8 (split_cmb (split_rl r) g) = lift_get slot8 (r :: mcp_st lifted)"
  by (cases r) (simp_all add: split_cmb_Lifted split_rl_lifted_def split_cmb_analysis_product_def
      split_rl_analysis_product_def split_cmb_relc_def split_rl_relc_def)

lemma slot8_keyed_init:
  "lift_get slot8 (split_cmb (Lifted i) g) = slot8 (i :: mcp_st)"
  by (simp add: split_cmb_Lifted split_cmb_analysis_product_def split_cmb_relc_def)

lemma part_gamma_keyed_mix:
  assumes G: "\<And>y. \<G> y \<longleftrightarrow> y \<in> set xs"
    and s: "s \<in> part_gamma \<G> a (split_cmb l0 (full_view split_global_at xs e))"
    and s': "s' \<in> part_gamma \<G> a r"
    and fr: "\<forall>x. \<G> x \<longrightarrow> x \<notin> set W \<longrightarrow> s' x = s x"
  shows "s' \<in> part_gamma \<G> a (split_cmb (split_rl r)
           (full_view split_global_at xs (\<lambda>x. if x \<in> set W then split_global_at x r else e x)))"
  using s s'
  by (cases a rule: analysis_domain_cases)
     (simp_all only: part_gamma.simps slot8_keyed,
      (rule keyed_field_mix[OF split_hom_slots(1) G _ _ fr]
        keyed_field_mix[OF split_hom_slots(2) G _ _ fr]
        keyed_field_mix[OF split_hom_slots(3) G _ _ fr]
          keyed_field_mix[OF split_hom_slots(4) G _ _ fr]
        keyed_field_mix[OF split_hom_slots(5) G _ _ fr]
          keyed_field_mix[OF split_hom_slots(6) G _ _ fr]
        keyed_field_mix[OF split_hom_slots(7) G _ _ fr]; assumption)+)

lemma part_gamma_keyed_init:
  assumes G: "\<And>y. \<G> y \<longleftrightarrow> y \<in> set xs"
  shows "part_gamma \<G> a (Lifted i) \<subseteq> part_gamma \<G> a (split_cmb (Lifted i)
           (full_view split_global_at xs (\<lambda>x. split_global_at x (Lifted i))))"
  by (cases a rule: analysis_domain_cases)
     (simp_all only: part_gamma.simps slot8_keyed_init,
      (rule keyed_field_init[OF split_hom_slots(1) G] keyed_field_init[OF split_hom_slots(2) G]
        keyed_field_init[OF split_hom_slots(3) G] keyed_field_init[OF split_hom_slots(4) G]
        keyed_field_init[OF split_hom_slots(5) G] keyed_field_init[OF split_hom_slots(6) G]
        keyed_field_init[OF split_hom_slots(7) G] | simp)+)

subsection \<open>The registration\<close>

text \<open>
  The keyed placement: each declared global at its own unknown \<open>global_of x\<close>,
  read and published by name. The combined analysis owes it what it owes the
  whole-state placement, plus the carrier laws above.
\<close>

lemma mcp_keyed_dg_analysis:
  fixes buffer_key :: 'k and global_of :: "vname \<Rightarrow> 'k"
  assumes seed_ne: "\<And>v ctx. seed v ctx \<noteq> buffer_key"
    and seed_ne_global: "\<And>v ctx n. seed v ctx \<noteq> global_of n"
  shows "dg_analysis (mcp_comp (activation as)) (mcp_emp (activation as)) mcp_rd
    (mcp_init (activation as)) buffer_key global_of seed
    (TD_side_rule_Interp_solve r)
    (TD_side_rule_Interp.solve_dom TYPE('k) TYPE((mcp_st lifted, mcp_st lifted) dg_state) r)
    \<bottom> (mcp_classify (activation as)) (mcp_gamma_v (activation as))
    (mcp_empty_v (activation as)) (TD_side_rule_Interp_solve_c r)
    (\<lambda>p c. keyed_split_spec (declared_global p) (declared_global_vars p)
       split_cmb split_rl split_global_at split_free c)
    (\<lambda>p d e. split_cmb d (full_view split_global_at (declared_global_vars p) e))
    (\<lambda>\<G>. split_rl) (\<lambda>\<G> d. Bot)
    (\<lambda>\<G> p. map (\<lambda>x. (x, split_global_at x (Lifted (mcp_init (activation as)))))
       (declared_global_vars p))"
proof (rule dg_analysis_keyedI[OF td_certified_solver],
    goal_cases CompSound EnterSingle CmbMono CmbRl RlCmb CmbBot RgMono RgFree Mix InitView
    EmptyRd EmptyVSound SeedNe SeedNeGlobal ClProved ClRefuted BotState Init)
  case (CompSound p)
  have eq: "mcp_gamma (map (part_gamma (declared_global p)) (activation as))
      = (\<lambda>d. gamma_lift (mcp_gamma_v (activation as)) (map_lift (mcp_rd (declared_global p)) d))"
    by (rule ext) (rule mcp_gamma_rd[OF activation_ne])
  show ?case using mcp_comp_sound[of "activation as" p] unfolding eq by simp
next
  case (EnterSingle p ci d)
  show ?case
    using single_entryD[OF single_entry_mcp_comp[OF activation_ne],
        of as "declared_global p" p
          "ls_channel (mcp_comp (activation as) (declared_global p) p) d" ci "(d, d)"]
    by (simp add: dg_pipeline.comp_entry_def)
next
  case (CmbMono d d' g g') then show ?case by (rule split_cmb_mono)
next
  case (CmbRl x g) show ?case by (rule split_cmb_rl)
next
  case (RlCmb d g) show ?case by (rule split_rl_cmb)
next
  case (CmbBot g) show ?case by simp
next
  case (RgMono x v v') then show ?case by (rule split_global_at_mono)
next
  case (RgFree x R v) then show ?case by (rule split_free_ge)
next
  case (Mix p l0 e r s s' W)
  note eq = mcp_gamma_rd[OF activation_ne, symmetric]
  show ?case
    using Mix unfolding eq mcp_gamma_def
    by (auto intro: part_gamma_keyed_mix[where xs = "declared_global_vars p"])
next
  case (InitView p)
  note eq = mcp_gamma_rd[OF activation_ne, symmetric]
  show ?case
    unfolding eq mcp_gamma_def
    using part_gamma_keyed_init[where xs = "declared_global_vars p" and \<G> = "declared_global p"]
    by fastforce
next
  case (EmptyRd p s) show ?case by (rule mcp_emp_rd)
next
  case EmptyVSound show ?case by (rule sound_emptiness_mcp)
next
  case (SeedNe v ctx) show ?case by (rule seed_ne)
next
  case (SeedNeGlobal v ctx n) show ?case by (rule seed_ne_global)
next
  case (ClProved e d s) then show ?case by (rule mcp_classify_proved)
next
  case (ClRefuted e d s) then show ?case by (rule mcp_classify_refuted)
next
  case BotState show ?case by (rule mcp_gamma_v_bot[OF activation_ne])
next
  case (Init p) show ?case by (rule mcp_init_sound)
qed

text \<open>
  The three context policies again, with each program global at its own unknown.
\<close>

global_interpretation mcp_split_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    Analysis_Buffer Analysis_Global Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((vname, unit) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>p c. keyed_split_spec (declared_global p) (declared_global_vars p)
       split_cmb split_rl split_global_at split_free c"
    "\<lambda>p d e. split_cmb d (full_view split_global_at (declared_global_vars p) e)"
    "\<lambda>\<G>. split_rl" "\<lambda>\<G> d. Bot"
    "\<lambda>\<G> p. map (\<lambda>x. (x, split_global_at x (Lifted (mcp_init (activation as)))))
       (declared_global_vars p)"
  for as r
  by (rule mcp_keyed_dg_analysis) simp_all

global_interpretation mcp_split_es_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    Analysis_Buffer Analysis_Global Activation_Seed "mcp_formals_route (activation as)"
      mcp_root_ctx
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((vname, mcp_ctx) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>p c. keyed_split_spec (declared_global p) (declared_global_vars p)
       split_cmb split_rl split_global_at split_free c"
    "\<lambda>p d e. split_cmb d (full_view split_global_at (declared_global_vars p) e)"
    "\<lambda>\<G>. split_rl" "\<lambda>\<G> d. Bot"
    "\<lambda>\<G> p. map (\<lambda>x. (x, split_global_at x (Lifted (mcp_init (activation as)))))
       (declared_global_vars p)"
  for as r
  by (rule mcp_keyed_dg_analysis) simp_all

global_interpretation mcp_split_cs_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    Analysis_Buffer Analysis_Global Activation_Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((vname, cfg_node list) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>p c. keyed_split_spec (declared_global p) (declared_global_vars p)
       split_cmb split_rl split_global_at split_free c"
    "\<lambda>p d e. split_cmb d (full_view split_global_at (declared_global_vars p) e)"
    "\<lambda>\<G>. split_rl" "\<lambda>\<G> d. Bot"
    "\<lambda>\<G> p. map (\<lambda>x. (x, split_global_at x (Lifted (mcp_init (activation as)))))
       (declared_global_vars p)"
  for as k r
  by (rule mcp_keyed_dg_analysis) simp_all

end
