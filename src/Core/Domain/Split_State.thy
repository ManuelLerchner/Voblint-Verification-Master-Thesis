theory Split_State
  imports Abstract_Domain "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Split local/global abstract states\<close>

text \<open>
  A split abstract state keeps the local and the global half of an abstract
  store in two separate components with independent value types:
  \<^typ>\<open>'l abs_state\<close> for locals and \<^typ>\<open>'g abs_state\<close> for globals.  Each
  component is a total \<open>vname => _\<close> map; well-formedness (\<open>wf_split\<close>) pins
  the off-domain half of each component to \<open>bot\<close>.

  At the homogeneous instance \<open>'l = 'g\<close> the split representation is
  isomorphic to the plain state \<^typ>\<open>'a abs_state\<close>: \<open>merge_state\<close> and
  \<open>split_state\<close> are mutually inverse between well-formed split states and
  plain states (\<open>merge_state_bij\<close>), the order transports both ways
  (\<open>merge_state_le_iff\<close>), lattice operations commute with the conversions,
  and the split concretization \<open>gamma_split\<close> agrees with
  \<^const>\<open>gamma_state\<close> under the isomorphism.
\<close>

type_synonym ('l, 'g) split_state = "'l abs_state \<times> 'g abs_state"


subsection \<open>Placement interface\<close>

text \<open>
  Placement controls which abstract component constrains a location.  It is
  independent of source storage: a location can be constrained by the local
  component, the side component, both components, or neither component.
\<close>

locale state_placement =
  fixes keep_local :: "'loc => bool"
    and publish_side :: "'loc => bool"
begin

definition placement_complete :: bool where
  "placement_complete \<longleftrightarrow>
    (\<forall>loc. keep_local loc \<or> publish_side loc)"

definition placement_disjoint :: bool where
  "placement_disjoint \<longleftrightarrow>
    (\<forall>loc. \<not> (keep_local loc \<and> publish_side loc))"

definition wf_components ::
    "('loc => 'l::bot) => ('loc => 'g::bot) => bool" where
  "wf_components local side \<longleftrightarrow>
    (\<forall>loc. \<not> keep_local loc \<longrightarrow> local loc = bot) \<and>
    (\<forall>loc. \<not> publish_side loc \<longrightarrow> side loc = bot)"

definition gamma_components ::
    "('loc => 'l::sound_domain) => ('loc => 'g::sound_domain)
      => ('loc => int) set" where
  "gamma_components local side =
    {s. \<forall>loc.
      (keep_local loc \<longrightarrow> s loc \<in> gamma (local loc)) \<and>
      (publish_side loc \<longrightarrow> s loc \<in> gamma (side loc))}"

lemma gamma_componentsD_local [dest]:
  assumes "s \<in> gamma_components local side" and "keep_local loc"
  shows "s loc \<in> gamma (local loc)"
  using assms unfolding gamma_components_def by blast

lemma gamma_componentsD_side [dest]:
  assumes "s \<in> gamma_components local side" and "publish_side loc"
  shows "s loc \<in> gamma (side loc)"
  using assms unfolding gamma_components_def by blast


lemma gamma_componentsD_covered:
  assumes complete: placement_complete
    and member: "s \<in> gamma_components local side"
  shows "s loc \<in> gamma (local loc) \<or> s loc \<in> gamma (side loc)"
  using complete member
  unfolding placement_complete_def gamma_components_def by blast
lemma gamma_components_update_unconstrained:
  assumes "s \<in> gamma_components local side"
    and "\<not> keep_local loc"
    and "\<not> publish_side loc"
  shows "s(loc := value) \<in> gamma_components local side"
  using assms unfolding gamma_components_def by auto

end


context state_placement
begin

lemma wf_components_bot:
  "wf_components (bot :: 'loc => 'l::bot) (bot :: 'loc => 'g::bot)"
  unfolding wf_components_def bot_fun_def by simp

lemma wf_components_sup:
  fixes local1 local2 :: "'loc => 'l::bounded_semilattice_sup_bot"
    and side1 side2 :: "'loc => 'g::bounded_semilattice_sup_bot"
  assumes "wf_components local1 side1" and "wf_components local2 side2"
  shows "wf_components (local1 \<squnion> local2) (side1 \<squnion> side2)"
  using assms unfolding wf_components_def by (simp add: sup_fun_def)

end

definition project_component ::
  "('loc => bool) => ('loc => 'a::bot) => 'loc => 'a" where
  "project_component placed state =
     (\<lambda>loc. if placed loc then state loc else bot)"

definition sequential_keep_local :: "'loc => bool" where
  "sequential_keep_local loc = True"

definition sequential_publish_side :: "'loc => bool" where
  "sequential_publish_side loc = False"

definition classic_keep_local :: "(vname => bool) => vname => bool" where
  "classic_keep_local storage loc = (\<not> storage loc)"

definition classic_publish_side :: "(vname => bool) => vname => bool" where
  "classic_publish_side storage loc = storage loc"



lemma sequential_placement_complete [simp]:
  "state_placement.placement_complete
    sequential_keep_local sequential_publish_side"
  unfolding state_placement.placement_complete_def
    sequential_keep_local_def sequential_publish_side_def by simp

lemma classic_placement_complete [simp]:
  "state_placement.placement_complete
    (classic_keep_local storage) (classic_publish_side storage)"
  unfolding state_placement.placement_complete_def
    classic_keep_local_def classic_publish_side_def by simp

lemma classic_placement_disjoint [simp]:
  "state_placement.placement_disjoint
    (classic_keep_local storage) (classic_publish_side storage)"
  unfolding state_placement.placement_disjoint_def
    classic_keep_local_def classic_publish_side_def by simp



subsection \<open>Well-formedness\<close>

definition wf_split :: "('l::bot, 'g::bot) split_state \<Rightarrow> bool" where
  "wf_split lg \<longleftrightarrow>
     (\<forall>x. is_global x \<longrightarrow> fst lg x = bot) \<and>
     (\<forall>x. \<not> is_global x \<longrightarrow> snd lg x = bot)"

lemma wf_splitI:
  "(\<And>x. is_global x \<Longrightarrow> L x = bot) \<Longrightarrow> (\<And>x. \<not> is_global x \<Longrightarrow> G x = bot)
   \<Longrightarrow> wf_split (L, G)"
  unfolding wf_split_def by simp

lemma wf_split_bot: "wf_split (bot, bot)"
  unfolding wf_split_def bot_fun_def by simp

lemma wf_split_sup:
  fixes lg1 lg2 ::
    "('l::bounded_semilattice_sup_bot, 'g::bounded_semilattice_sup_bot) split_state"
  assumes "wf_split lg1" and "wf_split lg2"
  shows "wf_split (fst lg1 \<squnion> fst lg2, snd lg1 \<squnion> snd lg2)"
  using assms unfolding wf_split_def by (simp add: sup_fun_def)

subsection \<open>Conversions\<close>

definition merge_state :: "('a, 'a) split_state \<Rightarrow> 'a abs_state" where
  "merge_state lg = (\<lambda>x. if is_global x then snd lg x else fst lg x)"

definition split_state :: "('a::bot) abs_state \<Rightarrow> ('a, 'a) split_state" where
  "split_state \<sigma> =
     ((\<lambda>x. if is_global x then bot else \<sigma> x),
      (\<lambda>x. if is_global x then \<sigma> x else bot))"

definition wf_split_for ::
  "(vname => bool) => ('l::bot, 'g::bot) split_state => bool" where
  "wf_split_for gs lg \<longleftrightarrow>
     (ALL x. gs x --> fst lg x = bot) &
     (ALL x. ~ gs x --> snd lg x = bot)"

definition merge_state_for ::
  "(vname => bool) => ('a, 'a) split_state => 'a abs_state" where
  "merge_state_for gs lg = (%x. if gs x then snd lg x else fst lg x)"

definition split_state_for ::
  "(vname => bool) => ('a::bot) abs_state => ('a, 'a) split_state" where
  "split_state_for gs \<sigma> =
     ((%x. if gs x then bot else \<sigma> x),
      (%x. if gs x then \<sigma> x else bot))"

lemma wf_components_classic_iff:
  "state_placement.wf_components
      (classic_keep_local storage) (classic_publish_side storage)
      (fst split) (snd split)
    \<longleftrightarrow> wf_split_for storage split"
  unfolding state_placement.wf_components_def classic_keep_local_def
    classic_publish_side_def wf_split_for_def by simp

lemma merge_split_for [simp]:
  "merge_state_for gs (split_state_for gs \<sigma>) = \<sigma>"
  unfolding merge_state_for_def split_state_for_def
  by (rule ext) simp

lemma wf_split_split_state_for:
  "wf_split_for gs (split_state_for gs \<sigma>)"
  unfolding wf_split_for_def split_state_for_def
  by simp


lemma fst_split_state:
  "fst (split_state \<sigma>) x = (if is_global x then bot else \<sigma> x)"
  unfolding split_state_def by simp

lemma snd_split_state:
  "snd (split_state \<sigma>) x = (if is_global x then \<sigma> x else bot)"
  unfolding split_state_def by simp

lemma wf_split_split_state: "wf_split (split_state \<sigma>)"
  unfolding wf_split_def split_state_def by simp

subsection \<open>Isomorphism at the homogeneous instance\<close>

lemma merge_split_id [simp]: "merge_state (split_state \<sigma>) = \<sigma>"
  unfolding merge_state_def split_state_def by (rule ext) simp

lemma split_merge_id:
  assumes wf: "wf_split lg"
  shows "split_state (merge_state lg) = lg"
  using wf unfolding wf_split_def split_state_def merge_state_def
  by (cases lg) (auto simp: fun_eq_iff)

lemma merge_state_bij:
  "bij_betw (merge_state :: ('a::bot, 'a) split_state \<Rightarrow> 'a abs_state)
     {lg. wf_split lg} UNIV"
proof (rule bij_betw_byWitness[where f' = split_state])
  show "\<forall>lg \<in> {lg. wf_split lg}. split_state (merge_state lg) = lg"
    by (simp add: split_merge_id)
  show "\<forall>\<sigma> \<in> UNIV. merge_state (split_state \<sigma>) = \<sigma>" by simp
  show "merge_state ` {lg. wf_split lg} \<subseteq> UNIV" by simp
  show "split_state ` UNIV \<subseteq> {lg. wf_split lg}"
    using wf_split_split_state by auto
qed

subsection \<open>Order transport\<close>

lemma merge_state_mono:
  fixes lg1 lg2 :: "('a::ord, 'a) split_state"
  assumes "fst lg1 \<le> fst lg2" and "snd lg1 \<le> snd lg2"
  shows "merge_state lg1 \<le> merge_state lg2"
  using assms unfolding merge_state_def le_fun_def by simp

lemma split_state_mono1:
  fixes sigma1 sigma2 :: "('a::order_bot) abs_state"
  assumes "sigma1 \<le> sigma2"
  shows "fst (split_state sigma1) \<le> fst (split_state sigma2)"
  using assms unfolding split_state_def le_fun_def by simp

lemma split_state_mono2:
  fixes sigma1 sigma2 :: "('a::order_bot) abs_state"
  assumes "sigma1 \<le> sigma2"
  shows "snd (split_state sigma1) \<le> snd (split_state sigma2)"
  using assms unfolding split_state_def le_fun_def by simp

lemma merge_state_le_iff:
  fixes lg1 lg2 :: "('a::order_bot, 'a) split_state"
  assumes wf1: "wf_split lg1"
  shows "merge_state lg1 \<le> merge_state lg2 \<longleftrightarrow>
         fst lg1 \<le> fst lg2 \<and> snd lg1 \<le> snd lg2"
proof (rule iffI)
  assume le: "merge_state lg1 \<le> merge_state lg2"
  have l: "fst lg1 x \<le> fst lg2 x" for x
  proof (cases "is_global x")
    case True
    then have "fst lg1 x = bot" using wf1 unfolding wf_split_def by simp
    then show ?thesis by simp
  next
    case False
    with le_funD[OF le, of x] show ?thesis unfolding merge_state_def by simp
  qed
  have g: "snd lg1 x \<le> snd lg2 x" for x
  proof (cases "is_global x")
    case True
    with le_funD[OF le, of x] show ?thesis unfolding merge_state_def by simp
  next
    case False
    then have "snd lg1 x = bot" using wf1 unfolding wf_split_def by simp
    then show ?thesis by simp
  qed
  show "fst lg1 \<le> fst lg2 \<and> snd lg1 \<le> snd lg2"
    using l g by (auto simp: le_fun_def)
next
  assume "fst lg1 \<le> fst lg2 \<and> snd lg1 \<le> snd lg2"
  then show "merge_state lg1 \<le> merge_state lg2"
    using merge_state_mono by blast
qed

subsection \<open>Lattice-operation transport\<close>

lemma merge_state_bot: "merge_state (bot, bot) = (bot :: 'a::bot abs_state)"
  unfolding merge_state_def bot_fun_def by (simp add: fun_eq_iff)

lemma merge_state_sup:
  fixes L1 L2 G1 G2 :: "'a::semilattice_sup abs_state"
  shows "merge_state (L1 \<squnion> L2, G1 \<squnion> G2)
         = merge_state (L1, G1) \<squnion> merge_state (L2, G2)"
  unfolding merge_state_def sup_fun_def by (rule ext) simp

lemma split_state_bot: "split_state (bot :: 'a::bot abs_state) = (bot, bot)"
  unfolding split_state_def bot_fun_def by simp

lemma split_state_sup:
  fixes sigma1 sigma2 :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "split_state (sigma1 \<squnion> sigma2) =
         (fst (split_state sigma1) \<squnion> fst (split_state sigma2),
          snd (split_state sigma1) \<squnion> snd (split_state sigma2))"
  unfolding split_state_def sup_fun_def by (simp add: fun_eq_iff)



end
