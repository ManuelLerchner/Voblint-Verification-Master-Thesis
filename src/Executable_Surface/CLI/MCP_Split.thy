theory MCP_Split
  imports "Voblint_CLI.MCP"
begin

section \<open>The registered analyses with program globals on the shared channel\<close>

text \<open>
  The keyed placement recombines a point's state with the solved globals and projects
  a state onto its local half or onto one global. On the combined state these
  operations are defined field by field, so a carrier that splits is a type class
  closed under the constructors the combined state is built from. The operations are
  told which globals the placement owns: an owned global is read from its own unknown,
  and every other variable, a global no unknown owns included, stays in the point's
  state. A pointwise field splits by the location each variable is stored at; the order
  field relates variables across the split and stays wholly local.
\<close>

class split_key = infinite_key +
  fixes key_of_var :: "var_id \<Rightarrow> 'a"
  assumes inj_key_of_var: "inj key_of_var"

instantiation var_id :: split_key
begin

definition key_of_var_var_id :: "var_id \<Rightarrow> var_id" where "key_of_var_var_id x = x"

instance by standard (simp add: key_of_var_var_id_def inj_def)

end

lemma key_of_var_var_id [simp]: "(key_of_var :: var_id \<Rightarrow> var_id) x = x"
  by (simp add: key_of_var_var_id_def)

text \<open>
  A carrier whose state splits into a chosen list of globals and the rest.
  \<open>split_cmb gs d g\<close> takes the globals in \<open>gs\<close> from \<open>g\<close> and everything else from \<open>d\<close>;
  \<open>split_rl gs\<close> forgets the globals in \<open>gs\<close>. \<open>split_free R\<close> is the global half a
  transfer reads in place of every global outside \<open>R\<close>: it claims nothing about those
  names and leaves the names in \<open>R\<close> to the values actually read.
\<close>

class ownership_split = order_bot +
  fixes split_cmb :: "var_id list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and split_rl :: "var_id list \<Rightarrow> 'a \<Rightarrow> 'a"
    and split_global_at :: "var_id \<Rightarrow> 'a \<Rightarrow> 'a"
    and split_free :: "var_id list \<Rightarrow> 'a"
  assumes split_cmb_mono: "d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> split_cmb gs d g \<le> split_cmb gs d' g'"
    and split_cmb_rl: "split_cmb gs (split_rl gs x) g = split_cmb gs x g"
    and split_rl_cmb: "split_rl gs (split_cmb gs d g) = split_rl gs d"
    and split_global_at_mono: "d \<le> d' \<Longrightarrow> split_global_at n d \<le> split_global_at n d'"
    and split_free_ge: "n \<notin> set R \<Longrightarrow> split_global_at n d \<le> split_free R"
    and split_global_at_bot: "split_global_at n bot = bot"

instantiation gdefault_st :: (split_key, "{order_bot, order_top}") ownership_split
begin

definition split_cmb_gdefault_st ::
    "var_id list \<Rightarrow> ('a, 'b) gdefault_st \<Rightarrow> ('a, 'b) gdefault_st \<Rightarrow> ('a, 'b) gdefault_st" where
  "split_cmb_gdefault_st gs d g =
     fold (\<lambda>x a. a\<langle>Global_Location (key_of_var x) := g\<langle>Global_Location (key_of_var x)\<rangle>\<rangle>) gs d"

definition split_rl_gdefault_st :: "var_id list \<Rightarrow> ('a, 'b) gdefault_st \<Rightarrow> ('a, 'b) gdefault_st" where
  "split_rl_gdefault_st gs d = fold (\<lambda>x a. a\<langle>Global_Location (key_of_var x) := bot\<rangle>) gs d"

definition split_global_at_gdefault_st :: "var_id \<Rightarrow> ('a, 'b) gdefault_st \<Rightarrow> ('a, 'b) gdefault_st"
  where
  "split_global_at_gdefault_st x d =
     bot\<langle>Global_Location (key_of_var x) := d\<langle>Global_Location (key_of_var x)\<rangle>\<rangle>"

definition split_free_gdefault_st :: "var_id list \<Rightarrow> ('a, 'b) gdefault_st" where
  "split_free_gdefault_st R = \<llangle>(bot, []), (top, map (\<lambda>x. (key_of_var x, bot)) R)\<rrangle>"

lemma split_cmb_gdefault_st_get:
  "(split_cmb gs d g :: ('a, 'b) gdefault_st)\<langle>loc\<rangle> =
     (if loc \<in> (\<lambda>x. Global_Location (key_of_var x)) ` set gs then g\<langle>loc\<rangle> else d\<langle>loc\<rangle>)"
  unfolding split_cmb_gdefault_st_def by (induction gs arbitrary: d) auto

lemma split_rl_gdefault_st_get:
  "(split_rl gs d :: ('a, 'b) gdefault_st)\<langle>loc\<rangle> =
     (if loc \<in> (\<lambda>x. Global_Location (key_of_var x)) ` set gs then bot else d\<langle>loc\<rangle>)"
  unfolding split_rl_gdefault_st_def by (induction gs arbitrary: d) auto

lemma map_of_map_const_key:
  "map_of (map (\<lambda>x. (f x, b)) R) k = (if k \<in> f ` set R then Some b else None)"
  by (induction R) auto

lemma split_free_gdefault_st_get:
  "(split_free R :: ('a, 'b) gdefault_st)\<langle>loc\<rangle> =
     (case loc of Global_Location x \<Rightarrow> if x \<in> key_of_var ` set R then bot else top | _ \<Rightarrow> bot)"
  by (cases loc) (auto simp: split_free_gdefault_st_def map_of_map_const_key)

instance
proof
  fix gs and d d' g g' :: "('a, 'b) gdefault_st"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb gs d g \<le> split_cmb gs d' g'"
    by (auto simp: le_default_st_iff split_cmb_gdefault_st_get)
next
  fix gs and x g :: "('a, 'b) gdefault_st"
  show "split_cmb gs (split_rl gs x) g = split_cmb gs x g"
    by (rule default_st_eqI) (simp add: split_cmb_gdefault_st_get split_rl_gdefault_st_get)
next
  fix gs and d g :: "('a, 'b) gdefault_st"
  show "split_rl gs (split_cmb gs d g) = split_rl gs d"
    by (rule default_st_eqI) (simp add: split_cmb_gdefault_st_get split_rl_gdefault_st_get)
next
  fix n and d d' :: "('a, 'b) gdefault_st"
  assume "d \<le> d'"
  then show "split_global_at n d \<le> split_global_at n d'"
    by (auto simp: le_default_st_iff split_global_at_gdefault_st_def)
next
  fix n :: var_id and R and d :: "('a, 'b) gdefault_st"
  assume "n \<notin> set R"
  then have "key_of_var n \<notin> key_of_var ` set R"
    using inj_key_of_var by (auto dest: injD)
  then show "split_global_at n d \<le> split_free R"
    by (auto simp: le_default_st_iff split_global_at_gdefault_st_def split_free_gdefault_st_get
        split: glocation.split)
next
  fix n :: var_id
  show "split_global_at n (bot :: ('a, 'b) gdefault_st) = bot"
    by (rule default_st_eqI) (simp add: split_global_at_gdefault_st_def)
qed

end

instantiation order_rel :: (type) ownership_split
begin

definition split_cmb_order_rel :: "var_id list \<Rightarrow> 'a order_rel \<Rightarrow> 'a order_rel \<Rightarrow> 'a order_rel" where
  "split_cmb_order_rel gs d g = d"
definition split_rl_order_rel :: "var_id list \<Rightarrow> 'a order_rel \<Rightarrow> 'a order_rel" where
  "split_rl_order_rel gs d = d"
definition split_global_at_order_rel :: "var_id \<Rightarrow> 'a order_rel \<Rightarrow> 'a order_rel" where
  "split_global_at_order_rel x d = bot"
definition split_free_order_rel :: "var_id list \<Rightarrow> 'a order_rel" where
  "split_free_order_rel R = bot"

instance
  by standard (simp_all add: split_cmb_order_rel_def split_rl_order_rel_def
      split_global_at_order_rel_def split_free_order_rel_def)

end

instantiation analysis_product :: (ownership_split, ownership_split) ownership_split
begin

definition split_cmb_analysis_product ::
  "var_id list \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product"
    where
  "split_cmb_analysis_product gs d g =
     Product (split_cmb gs (pleft d) (pleft g)) (split_cmb gs (pright d) (pright g))"

definition split_rl_analysis_product ::
  "var_id list \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_rl_analysis_product gs d = Product (split_rl gs (pleft d)) (split_rl gs (pright d))"

definition split_global_at_analysis_product ::
  "var_id \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_global_at_analysis_product x d =
     Product (split_global_at x (pleft d)) (split_global_at x (pright d))"

definition split_free_analysis_product :: "var_id list \<Rightarrow> ('a, 'b) analysis_product" where
  "split_free_analysis_product R = Product (split_free R) (split_free R)"

instance
proof
  fix gs and d d' g g' :: "('a, 'b) analysis_product"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb gs d g \<le> split_cmb gs d' g'"
    by (simp add: split_cmb_analysis_product_def less_eq_analysis_product_def split_cmb_mono)
next
  fix gs and x g :: "('a, 'b) analysis_product"
  show "split_cmb gs (split_rl gs x) g = split_cmb gs x g"
    by (simp add: split_cmb_analysis_product_def split_rl_analysis_product_def split_cmb_rl)
next
  fix gs and d g :: "('a, 'b) analysis_product"
  show "split_rl gs (split_cmb gs d g) = split_rl gs d"
    by (simp add: split_cmb_analysis_product_def split_rl_analysis_product_def split_rl_cmb)
next
  fix x :: var_id and d d' :: "('a, 'b) analysis_product"
  assume "d \<le> d'"
  then show "split_global_at x d \<le> split_global_at x d'"
    by (simp add: split_global_at_analysis_product_def less_eq_analysis_product_def
      split_global_at_mono)
next
  fix n :: var_id and R and d :: "('a, 'b) analysis_product"
  assume "n \<notin> set R"
  then show "split_global_at n d \<le> split_free R"
    by (simp add: split_global_at_analysis_product_def split_free_analysis_product_def
        less_eq_analysis_product_def split_free_ge)
next
  fix n :: var_id
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

definition split_cmb_lifted :: "var_id list \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "split_cmb_lifted gs d g = (case d of Bot \<Rightarrow> Bot
     | Lifted a \<Rightarrow> Lifted (split_cmb gs a (case g of Bot \<Rightarrow> bot | Lifted b \<Rightarrow> b)))"

definition split_rl_lifted :: "var_id list \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "split_rl_lifted gs = map_lift (split_rl gs)"

definition split_global_at_lifted :: "var_id \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "split_global_at_lifted x = map_lift (split_global_at x)"

definition split_free_lifted :: "var_id list \<Rightarrow> 'a lifted" where
  "split_free_lifted R = Lifted (split_free R)"

instance
proof
  fix gs and d d' g g' :: "'a lifted"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb gs d g \<le> split_cmb gs d' g'"
    by (cases d; cases d'; cases g; cases g')
       (auto simp: split_cmb_lifted_def intro: split_cmb_mono)
next
  fix gs and x g :: "'a lifted"
  show "split_cmb gs (split_rl gs x) g = split_cmb gs x g"
    by (cases x) (simp_all add: split_cmb_lifted_def split_rl_lifted_def split_cmb_rl)
next
  fix gs and d g :: "'a lifted"
  show "split_rl gs (split_cmb gs d g) = split_rl gs d"
    by (cases d) (simp_all add: split_cmb_lifted_def split_rl_lifted_def split_rl_cmb)
next
  fix x :: var_id and d d' :: "'a lifted"
  assume "d \<le> d'"
  then show "split_global_at x d \<le> split_global_at x d'"
    by (cases d; cases d') (simp_all add: split_global_at_lifted_def split_global_at_mono)
next
  fix n :: var_id and R and d :: "'a lifted"
  assume "n \<notin> set R"
  then show "split_global_at n d \<le> split_free R"
    by (cases d) (simp_all add: split_global_at_lifted_def split_free_lifted_def split_free_ge)
next
  fix n :: var_id
  show "split_global_at n (bot :: 'a lifted) = bot"
    by (simp add: split_global_at_lifted_def)
qed

end

lemma split_cmb_Bot [simp]:
  "split_cmb gs (Bot :: 'a::{ownership_split, semilattice_sup} lifted) g = Bot"
  by (simp add: split_cmb_lifted_def)

subsection \<open>Reading a keyed recombination back\<close>

text \<open>
  A keyed point's state is its own state recombined with the solved environment over
  the owned globals. Read back, every owned global comes from that global's own unknown
  and every other variable from the point. The lemmas below establish this for one
  field and lift it through the fields of the combined state.
\<close>

lemma view_of_default_st_get:
  "(view_of split_global_at xs E acc
      :: (var_id, 'a::{bounded_semilattice_sup_bot, order_top}) gdefault_st)\<langle>loc\<rangle>
     = acc\<langle>loc\<rangle> \<squnion> (case loc of Global_Location y \<Rightarrow> if y \<in> set xs then (E y)\<langle>loc\<rangle> else bot
                       | Local_Location y \<Rightarrow> bot)"
  unfolding view_of_def
  by (induction xs arbitrary: acc)
     (auto simp: split_global_at_gdefault_st_def ac_simps split: glocation.split)

text \<open>The value a lifted state carries, \<open>bot\<close> when unreachable.\<close>

fun lift_val :: "'a::bot lifted \<Rightarrow> 'a" where
  "lift_val Bot = bot"
| "lift_val (Lifted a) = a"

lemma lift_val_sup:
  "lift_val (a \<squnion> b) = lift_val a \<squnion> lift_val (b :: 'a::bounded_semilattice_sup_bot lifted)"
  by (cases a; cases b) simp_all

lemma split_cmb_Lifted:
  "split_cmb gs (Lifted a) g
     = Lifted (split_cmb gs a (lift_val (g :: 'a::{ownership_split, semilattice_sup} lifted)))"
  by (cases g) (simp_all add: split_cmb_lifted_def)

lemma lift_val_view_of:
  "lift_val (view_of split_global_at xs E acc
       :: 'a::{ownership_split, bounded_semilattice_sup_bot} lifted)
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
  assumes hom_cmb: "f (split_cmb gs a b) = split_cmb gs (f a) (f b)"
    and hom_rl: "f (split_rl gs a) = split_rl gs (f a)"
    and hom_at: "f (split_global_at x a) = split_global_at x (f a)"
    and hom_sup: "f (a \<squnion> b) = f a \<squnion> f b"
    and hom_bot: "f bot = bot"
begin

lemma hom_view_of:
  "f (view_of split_global_at xs E acc) = view_of split_global_at xs (\<lambda>y. f (E y)) (f acc)"
  unfolding view_of_def by (induction xs arbitrary: acc) (simp_all add: hom_sup hom_at)

lemma lift_get_hom: "lift_get f x = f (lift_val x)"
  by (cases x) (simp_all add: hom_bot lift_get_def)

end

text \<open>
  The read-back of one field of a keyed recombination: an owned global reads from the
  field of that global's unknown, every other variable from the point.
\<close>

lemma keyed_field_read:
  fixes f :: "'a::{ownership_split, bounded_semilattice_sup_bot}
              \<Rightarrow> 'c::{ownership_split, bounded_semilattice_sup_bot} lifted"
    and E :: "var_id \<Rightarrow> 'a lifted"
  assumes hom: "split_hom f" and fa: "f a = Lifted st"
  shows "lift_get f (split_cmb gs (Lifted a) (full_view split_global_at xs E))
    = Lifted (split_cmb gs st (view_of split_global_at xs (\<lambda>y. lift_val (lift_get f (E y))) bot))"
proof -
  interpret split_hom f by (rule hom)
  have "lift_get f (split_cmb gs (Lifted a) (full_view split_global_at xs E))
      = split_cmb gs (f a) (view_of split_global_at xs (\<lambda>y. lift_get f (E y)) bot)"
    by (simp add: split_cmb_Lifted full_view_def hom_cmb hom_view_of hom_bot lift_val_view_of
        lift_get_hom)
  then show ?thesis
    using fa by (simp add: split_cmb_Lifted lift_val_view_of)
qed

text \<open>
  A typed field of a keyed recombination describes a store when every owned global
  lies in what its unknown publishes and every other variable in what the point holds.
\<close>

lemma keyed_field_gamma:
  fixes f :: "'a::{ownership_split, bounded_semilattice_sup_bot} \<Rightarrow> 'c::kind_int_domain tst lifted"
    and E :: "var_id \<Rightarrow> 'a lifted"
  assumes hom: "split_hom f" and fa: "f a = Lifted st"
  shows "s \<in> gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global)
             (lift_get f (split_cmb gs (Lifted a) (full_view split_global_at gs E))))
    \<longleftrightarrow> in_kinds \<kappa> s \<and> (\<forall>y. s y \<in> gamma_kd (if is_global y \<and> y \<in> set gs
                            then (lift_val (lift_get f (E y)))\<langle>Global_Location y\<rangle>
                            else st\<langle>nonrel_loc y\<rangle>))"
  by (auto simp: keyed_field_read[OF hom fa] gamma_tabs_def default_st_to_fun_def location_of_def
      split_cmb_gdefault_st_get view_of_default_st_get image_iff)

text \<open>
  The frame law for one field: a store the transfer's result describes, agreeing
  outside the written globals with a store the point described, is described by the
  result's own variables and written globals together with the environment elsewhere.
\<close>

lemma keyed_field_mix:
  fixes f :: "'a::{ownership_split, bounded_semilattice_sup_bot} \<Rightarrow> 'c::kind_int_domain tst lifted"
  assumes hom: "split_hom f"
    and s: "s \<in> gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global)
               (lift_get f (split_cmb gs l0 (full_view split_global_at gs e))))"
    and s': "s' \<in> gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get f r))"
    and fr: "\<forall>x. is_global x \<longrightarrow> x \<notin> set W \<longrightarrow> s' x = s x"
  shows "s' \<in> gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global)
           (lift_get f (split_cmb gs (split_rl gs r)
              (full_view split_global_at gs (\<lambda>x. if x \<in> set W then split_global_at x r else e x)))))"
proof -
  interpret split_hom f by (rule hom)
  obtain ri where r: "r = Lifted ri" using s' by (cases r) (simp_all add: lift_get_def)
  obtain stR where fr_i: "f ri = Lifted stR" using s' r
    by (cases "f ri") (simp_all add: lift_get_def)
  obtain a0 where l0: "l0 = Lifted a0" using s by (cases l0) (simp_all add: lift_get_def)
  obtain st0 where fa0: "f a0 = Lifted st0"
    using s l0 by (cases "f a0") (simp_all add: split_cmb_Lifted hom_cmb lift_get_def)
  have rl: "split_rl gs r = Lifted (split_rl gs ri)" by (simp add: r split_rl_lifted_def)
  have frl: "f (split_rl gs ri) = Lifted (split_rl gs stR)"
    by (simp add: hom_rl fr_i split_rl_lifted_def)
  have s'R: "in_kinds \<kappa> s'" "\<And>y. s' y \<in> gamma_kd (stR\<langle>nonrel_loc y\<rangle>)"
    using s' by (simp_all add: r fr_i lift_get_def gamma_tabs_def default_st_to_fun_def)
  have s0: "\<And>y. s y \<in> gamma_kd (if is_global y \<and> y \<in> set gs
               then (lift_val (lift_get f (e y)))\<langle>Global_Location y\<rangle> else st0\<langle>nonrel_loc y\<rangle>)"
    using s by (simp add: l0 keyed_field_gamma[OF hom fa0])
  show ?thesis
    unfolding rl keyed_field_gamma[OF hom frl]
  proof (intro conjI allI)
    show "in_kinds \<kappa> s'" by (rule s'R(1))
  next
    fix y
    show "s' y \<in> gamma_kd (if is_global y \<and> y \<in> set gs
        then (lift_val (lift_get f (if y \<in> set W then split_global_at y r else e y)))\<langle>Global_Location y\<rangle>
        else (split_rl gs stR)\<langle>nonrel_loc y\<rangle>)"
    proof (cases "is_global y \<and> y \<in> set gs")
      case False
      then show ?thesis using s'R(2)[of y]
        by (auto simp: location_of_def split_rl_gdefault_st_get image_iff)
    next
      case owned: True
      show ?thesis
      proof (cases "y \<in> set W")
        case True
        then show ?thesis using owned s'R(2)[of y]
          by (simp add: location_of_def r split_global_at_lifted_def hom_at fr_i lift_get_def
              split_global_at_gdefault_st_def)
      next
        case False
        then show ?thesis using owned s0[of y] fr by simp
      qed
    qed
  qed
qed

text \<open>A state is described by itself recombined with its own cuts.\<close>

lemma keyed_field_init:
  fixes f :: "'a::{ownership_split, bounded_semilattice_sup_bot} \<Rightarrow> 'c::kind_int_domain tst lifted"
  assumes hom: "split_hom f"
  shows "gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get f (Lifted i)))
    \<subseteq> gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get f (split_cmb gs (Lifted i)
         (full_view split_global_at gs (\<lambda>x. split_global_at x (Lifted i))))))"
proof
  interpret split_hom f by (rule hom)
  fix s
  assume s:
    "s \<in> gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get f (Lifted i)))"
  then obtain st where fi: "f i = Lifted st" by (cases "f i") (simp_all add: lift_get_def)
  show "s \<in> gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get f (split_cmb gs (Lifted i)
      (full_view split_global_at gs (\<lambda>x. split_global_at x (Lifted i))))))"
    using s unfolding keyed_field_gamma[OF hom fi]
    by (auto simp: fi lift_get_def gamma_tabs_def default_st_to_fun_def location_of_def
        split_global_at_lifted_def hom_at split_global_at_gdefault_st_def) (metis (full_types))
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

lemma split_hom_tslots:
  "split_hom (slot1 :: mcp_st \<Rightarrow> _)" "split_hom (slot2 :: mcp_st \<Rightarrow> _)"
  "split_hom (slot3n :: mcp_st \<Rightarrow> _)" "split_hom (slot3o :: mcp_st \<Rightarrow> _)"
  "split_hom (slot3f :: mcp_st \<Rightarrow> _)" "split_hom (slot4 :: mcp_st \<Rightarrow> _)"
  "split_hom (slot5 :: mcp_st \<Rightarrow> _)"
proof -
  note h = split_hom_comp split_hom_pleft split_hom_pright
  have eqs: "(slot1 :: mcp_st \<Rightarrow> _) = pleft" "(slot2 :: mcp_st \<Rightarrow> _) = pleft \<circ> pright"
    "(slot3n :: mcp_st \<Rightarrow> _) = pleft \<circ> pleft \<circ> pright \<circ> pright"
    "(slot3o :: mcp_st \<Rightarrow> _) = pleft \<circ> pright \<circ> pleft \<circ> pright \<circ> pright"
    "(slot3f :: mcp_st \<Rightarrow> _) = pright \<circ> pright \<circ> pleft \<circ> pright \<circ> pright"
    "(slot4 :: mcp_st \<Rightarrow> _) = pleft \<circ> pright \<circ> pright \<circ> pright"
    "(slot5 :: mcp_st \<Rightarrow> _) = pleft \<circ> pright \<circ> pright \<circ> pright \<circ> pright"
    by (simp_all add: fun_eq_iff)
  show "split_hom (slot1 :: mcp_st \<Rightarrow> _)" "split_hom (slot2 :: mcp_st \<Rightarrow> _)"
    "split_hom (slot3n :: mcp_st \<Rightarrow> _)" "split_hom (slot3o :: mcp_st \<Rightarrow> _)"
    "split_hom (slot3f :: mcp_st \<Rightarrow> _)" "split_hom (slot4 :: mcp_st \<Rightarrow> _)"
    "split_hom (slot5 :: mcp_st \<Rightarrow> _)"
    unfolding eqs by (intro h)+
qed

text \<open>The order field keeps its whole state at the point, so recombining leaves it alone.\<close>

lemma split_order_lifted [simp]:
  "split_cmb gs (d :: 'v order_rel lifted) g = d" "split_rl gs (d :: 'v order_rel lifted) = d"
  by (cases d; simp add: split_cmb_lifted_def split_cmb_order_rel_def split_rl_lifted_def
      split_rl_order_rel_def)+

lemma slot6_keyed:
  "lift_get slot6 (split_cmb gs (split_rl gs r) g) = lift_get slot6 (r :: mcp_st lifted)"
  by (cases r) (simp_all add: split_cmb_Lifted split_rl_lifted_def split_cmb_analysis_product_def
      split_rl_analysis_product_def lift_get_def split_rl_order_rel_def map_lift_def
      split: lifted.split)

lemma slot6_keyed_init: "lift_get slot6 (split_cmb gs (Lifted i) g) = slot6 (i :: mcp_st)"
  by (simp add: split_cmb_Lifted split_cmb_analysis_product_def lift_get_def)

text \<open>Each analysis reads its own field of the combined state.\<close>

lemma val_gamma_slot:
  "gamma_lift (val_gamma \<kappa> Interval) (map_lift (mcp_rd is_global) x)
     = gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get slot1 x))"
  "gamma_lift (val_gamma \<kappa> Congruence) (map_lift (mcp_rd is_global) x)
     = gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get slot2 x))"
  "gamma_lift (val_gamma \<kappa> (Ana_Int Refine_Never)) (map_lift (mcp_rd is_global) x)
     = gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get slot3n x))"
  "gamma_lift (val_gamma \<kappa> (Ana_Int Refine_Once)) (map_lift (mcp_rd is_global) x)
     = gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get slot3o x))"
  "gamma_lift (val_gamma \<kappa> (Ana_Int Refine_Fixpoint)) (map_lift (mcp_rd is_global) x)
     = gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get slot3f x))"
  "gamma_lift (val_gamma \<kappa> Sign) (map_lift (mcp_rd is_global) x)
     = gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get slot4 x))"
  "gamma_lift (val_gamma \<kappa> Parity) (map_lift (mcp_rd is_global) x)
     = gamma_lift (gamma_tabs \<kappa>) (map_lift (default_st_to_fun is_global) (lift_get slot5 x))"
  "gamma_lift (val_gamma \<kappa> Order) (map_lift (mcp_rd is_global) x)
     = gamma_ord_lift \<kappa> (lift_get slot6 x)"
  by (cases x; simp add: mcp_rd_def lift_get_def)+

lemma part_gamma_keyed_mix:
  assumes s: "s \<in> gamma_lift (val_gamma \<kappa> a) (map_lift (mcp_rd is_global)
                 (split_cmb gs l0 (full_view split_global_at gs e)))"
    and s': "s' \<in> gamma_lift (val_gamma \<kappa> a) (map_lift (mcp_rd is_global) r)"
    and fr: "\<forall>x. is_global x \<longrightarrow> x \<notin> set W \<longrightarrow> s' x = s x"
  shows "s' \<in> gamma_lift (val_gamma \<kappa> a) (map_lift (mcp_rd is_global) (split_cmb gs (split_rl gs r)
           (full_view split_global_at gs (\<lambda>x. if x \<in> set W then split_global_at x r else e x))))"
  using s s'
  by (cases a rule: analysis_cases)
     (simp_all only: val_gamma_slot slot6_keyed,
      (rule keyed_field_mix[OF split_hom_tslots(1) _ _ fr]
        keyed_field_mix[OF split_hom_tslots(2) _ _ fr]
        keyed_field_mix[OF split_hom_tslots(3) _ _ fr]
        keyed_field_mix[OF split_hom_tslots(4) _ _ fr]
        keyed_field_mix[OF split_hom_tslots(5) _ _ fr]
        keyed_field_mix[OF split_hom_tslots(6) _ _ fr]
        keyed_field_mix[OF split_hom_tslots(7) _ _ fr]; assumption)+)

lemma part_gamma_keyed_init:
  "gamma_lift (val_gamma \<kappa> a) (map_lift (mcp_rd is_global) (Lifted i))
     \<subseteq> gamma_lift (val_gamma \<kappa> a) (map_lift (mcp_rd is_global) (split_cmb gs (Lifted i)
         (full_view split_global_at gs (\<lambda>x. split_global_at x (Lifted i)))))"
  by (cases a rule: analysis_cases)
     (simp_all only: val_gamma_slot slot6_keyed_init,
      (rule keyed_field_init[OF split_hom_tslots(1)] keyed_field_init[OF split_hom_tslots(2)]
        keyed_field_init[OF split_hom_tslots(3)] keyed_field_init[OF split_hom_tslots(4)]
        keyed_field_init[OF split_hom_tslots(5)] keyed_field_init[OF split_hom_tslots(6)]
        keyed_field_init[OF split_hom_tslots(7)] | simp add: lift_get_def)+)

subsection \<open>The registration\<close>

text \<open>
  The keyed placement: each owned global at its own unknown \<open>Analysis_Global x\<close>, read
  and published by name. A run owns the program's declared globals. The combined
  analysis owes it what it owes the whole-state placement, plus the carrier laws
  above.
\<close>

definition declared_globals :: "imp_prog \<Rightarrow> var_id list" where
  "declared_globals p = map GlobalId (declared_global_vars p)"

lemma mcp_cs_keyed:
  "gdg_analysis
    eval ReturnVar (\<lambda>_. kind_conv (kenv_of ds)) (\<lambda>_. is_global) (\<lambda>_. init_stores (kenv_of ds))
    (mcp_comp sem ds (activation_of as)) (mcp_emp (activation_of as)) mcp_rd
    (mcp_init ds (activation_of as))
    Analysis_Buffer Analysis_Global Activation_Seed
    (TD_side_rule_Interp_solve r)
    (TD_side_rule_Interp.solve_dom TYPE((var_id, 'c) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r)
    \<bottom> (mcp_classify sem ds (activation_of as)) (mcp.act_gamma ds (activation_of as))
    (mcp_empty_v (activation_of as))
    (TD_side_rule_Interp_solve_c r)
    (\<lambda>p c. gkeyed_split_spec exp_vars ReturnVar is_global (split_cmb gs) (split_rl gs)
       split_global_at split_free c)
    (\<lambda>p d e. split_cmb gs d (full_view split_global_at gs e)) (\<lambda>\<G>. split_rl gs) (\<lambda>\<G> d. Bot)
    (\<lambda>\<G> p. map (\<lambda>x. (x, split_global_at x (Lifted (mcp_init ds (activation_of as))))) gs)
    (\<lambda>p ci d e. split_cmb gs d (view_of split_global_at (gcall_global_reads exp_vars is_global (ci_args ci))
       e (split_free (gcall_global_reads exp_vars is_global (ci_args ci)))))
    (\<lambda>p. elab_cfg p ds) (\<lambda>_. FunctionEntry prog_main_name)"
proof (rule gdg_analysis_keyedI[OF td_certified_solver], goal_cases CompSound EnterSingle CmbMono
    CmbRl RlCmb CmbBot RgMono RgFree Mix InitView EmptyRd EmptyV SeedNe SeedNeGlobal ClProved
    ClRefuted BotState InitSound PEntry FinIntra FinCalls CallsUnique)
  case (CompSound p)
  have eq: "mcp_gamma (map (mcp.part_gamma ds is_global) (activation_of as))
      = (\<lambda>d. gamma_lift (mcp.act_gamma ds (activation_of as)) (map_lift (mcp_rd is_global) d))"
    by (rule ext) (rule mcp.mcp_gamma_rd[OF activation_of_ne])
  show ?case
    using mcp.mcp_comp_sound[OF distinct_activation_of activation_of_ne, where sem = sem and ds = ds
        and p = p, of as]
    unfolding eq by simp
next
  case (EnterSingle p ci d)
  show ?case
    using single_entryD[OF mcp.single_entry_mcp_comp[OF activation_of_ne],
        of sem ds as is_global p
          "ls_channel (mcp_comp sem ds (activation_of as) is_global p) d" ci "(d, d)"]
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
  note eq = mcp.mcp_gamma_rd[OF activation_of_ne, symmetric]
  show ?case
    using Mix unfolding eq mcp_gamma_def by (auto intro: part_gamma_keyed_mix)
next
  case (InitView p)
  note eq = mcp.mcp_gamma_rd[OF activation_of_ne, symmetric]
  show ?case
    unfolding eq mcp_gamma_def using part_gamma_keyed_init by fastforce
next
  case (EmptyRd p s) show ?case by (rule mcp.mcp_emp_rd)
next
  case EmptyV show ?case by (rule mcp.sound_emptiness_mcp)
next
  case (SeedNe v ctx) show ?case by simp
next
  case (SeedNeGlobal v ctx n) show ?case by simp
next
  case (ClProved c d s) then show ?case by (intro mcp.mcp_classify_proved)
next
  case (ClRefuted c d s) then show ?case by (intro mcp.mcp_classify_refuted)
next
  case BotState show ?case by (rule mcp.act_gamma_bot[OF activation_of_ne])
next
  case (InitSound p) show ?case by (rule mcp_init_sound)
next
  case (PEntry p) show ?case by (simp add: elab_cfg_def)
next
  case (FinIntra p) show ?case by (simp add: elab_cfg_def compile_prog_finite)
next
  case (FinCalls p) show ?case by (simp add: elab_cfg_def compile_prog_finite)
next
  case (CallsUnique p) show ?case by (rule elab_cfg_calls_source_unique)
qed

text \<open>The two context policies again, with each owned global at its own unknown.\<close>

global_interpretation mcp_split: gdg_analysis
    eval ReturnVar "\<lambda>_. kind_conv (kenv_of ds)" "\<lambda>_. is_global" "\<lambda>_. init_stores (kenv_of ds)"
    "mcp_comp sem ds (activation_of as)" "mcp_emp (activation_of as)" mcp_rd
    "mcp_init ds (activation_of as)"
    Analysis_Buffer Analysis_Global Activation_Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((var_id, cfg_node list) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify sem ds (activation_of as)" "mcp.act_gamma ds (activation_of as)"
    "mcp_empty_v (activation_of as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>p c. gkeyed_split_spec exp_vars ReturnVar is_global (split_cmb gs) (split_rl gs)
       split_global_at split_free c"
    "\<lambda>p d e. split_cmb gs d (full_view split_global_at gs e)" "\<lambda>\<G>. split_rl gs" "\<lambda>\<G> d. Bot"
    "\<lambda>\<G> p. map (\<lambda>x. (x, split_global_at x (Lifted (mcp_init ds (activation_of as))))) gs"
    "\<lambda>p ci d e. split_cmb gs d (view_of split_global_at (gcall_global_reads exp_vars is_global (ci_args ci))
       e (split_free (gcall_global_reads exp_vars is_global (ci_args ci))))"
    "\<lambda>p. elab_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for sem ds as r k gs
  by (rule mcp_cs_keyed)

global_interpretation mcp_split_es: gdg_analysis
    eval ReturnVar "\<lambda>_. kind_conv (kenv_of ds)" "\<lambda>_. is_global" "\<lambda>_. init_stores (kenv_of ds)"
    "mcp_comp sem ds (activation_of as)" "mcp_emp (activation_of as)" mcp_rd
    "mcp_init ds (activation_of as)"
    Analysis_Buffer Analysis_Global Activation_Seed "mcp_route (activation_of as)" mcp_root_ctx
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((var_id, mcp_ctx) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify sem ds (activation_of as)" "mcp.act_gamma ds (activation_of as)"
    "mcp_empty_v (activation_of as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>p c. gkeyed_split_spec exp_vars ReturnVar is_global (split_cmb gs) (split_rl gs)
       split_global_at split_free c"
    "\<lambda>p d e. split_cmb gs d (full_view split_global_at gs e)" "\<lambda>\<G>. split_rl gs" "\<lambda>\<G> d. Bot"
    "\<lambda>\<G> p. map (\<lambda>x. (x, split_global_at x (Lifted (mcp_init ds (activation_of as))))) gs"
    "\<lambda>p ci d e. split_cmb gs d (view_of split_global_at (gcall_global_reads exp_vars is_global (ci_args ci))
       e (split_free (gcall_global_reads exp_vars is_global (ci_args ci))))"
    "\<lambda>p. elab_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for sem ds as r gs
  by (rule mcp_cs_keyed)

text \<open>Every store that reaches a node lies in a state the solve files there, as for the
  whole-state placement (\<open>mcp_cs_node_sound\<close>).\<close>

lemma mcp_split_node_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "mcp_split.terminates sem ds as k r gs is_global p"
  shows "reaching ds p v \<subseteq> (\<Union>ctx. mcp.act_gamma ds (activation_of as)
           (mcp_split.state_at sem ds as k r gs is_global p ctx v))"
  using mcp_split.gfun_route_result_node_sound
      [OF elab_cfg_def _ elab_wf_compile_input[OF wf] solves, of "cs_context k" v]
  by (simp add: node_collect_def cs_route_def cs_context_def)

lemma mcp_split_es_node_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "mcp_split_es.terminates sem ds as r gs is_global p"
  shows "reaching ds p v \<subseteq> (\<Union>ctx. mcp.act_gamma ds (activation_of as)
           (mcp_split_es.state_at sem ds as r gs is_global p ctx v))"
proof
  fix s assume "s \<in> reaching ds p v"
  then obtain ctx :: mcp_ctx where "s \<in> ctx_sem.gactivation_collect eval ReturnVar (kind_conv (kenv_of ds))
      is_global (mcp_split_es.admitted_contexts sem ds as r gs is_global p) mcp_root_ctx
      (elab_cfg p ds) (init_stores (kenv_of ds)) v ctx"
    using mcp_split_es.gentry_state_node_collect_eq_Union_of_terminates
        [OF elab_cfg_def elab_wf_compile_input[OF wf] solves, of v]
    by (auto simp: node_collect_def)
  then have "s \<in> gamma_lift (mcp.act_gamma ds (activation_of as))
      (lookup_table (mcp_split_es.result sem ds as r gs is_global p) v ctx)"
    using mcp_split_es.gentry_state_lookup_sound_of_terminates
        [OF elab_cfg_def elab_wf_compile_input[OF wf] solves, of v ctx]
    by blast
  then show "s \<in> (\<Union>ctx. mcp.act_gamma ds (activation_of as)
      (mcp_split_es.state_at sem ds as r gs is_global p ctx v))"
    by (intro UN_I[of ctx]) (auto simp: mcp_split_es.state_at_unfold split: lifted.splits)
qed

end
