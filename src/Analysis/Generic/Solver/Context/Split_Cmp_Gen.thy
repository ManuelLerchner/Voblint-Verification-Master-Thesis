theory Split_Cmp_Gen
  imports Call_Spec_Generator Clean_RRead_Sound
begin

section \<open>Stage 1B: the CMP generator over the split state representation\<close>

text \<open>
  Threads the split local/global representation of
  \<^theory>\<open>Voblint_Analysis.Split_State\<close> through the generic CMP equation
  generator at the homogeneous instance \<open>'l = 'g = 'a\<close>.  The migration
  boundary is exactly where the \<open>vname => 'a\<close> structure of an abstract state
  is inspected:
  \<^item> the per-edge and combine tree bodies (\<^const>\<open>unit_edge_tree\<close> /
    \<^const>\<open>unit_combine_tree\<close>, built from \<^const>\<open>restrict_local\<close> /
    \<^const>\<open>restrict_global\<close>), and
  \<^item> the generator's entry-seed decomposition of \<open>s0\<close>.
  Everything else in the CMP pipeline (\<^const>\<open>side_rhs_fold_ctx\<close>, the
  \<^const>\<open>map_ltree\<close> / \<^const>\<open>map_gtree\<close> routing, \<^const>\<open>side_env_cmp\<close>) is opaque in
  the state type and needs no change.

  Every split-shaped artefact is proven \<^emph>\<open>equal\<close> to its homogeneous original,
  so the migrated generator produces literally the same equation system:
  post-fixpoints coincide and every existing theorem about the CMP pipeline
  applies unchanged.
\<close>

subsection \<open>Split components of the state conversions\<close>

lemma fst_split_state_restrict: "fst (split_state \<sigma>) = restrict_local \<sigma>"
  by (simp add: split_state_eq_restrict)

lemma snd_split_state_restrict: "snd (split_state \<sigma>) = restrict_global \<sigma>"
  by (simp add: split_state_eq_restrict)

text \<open>
  The split-level call combine is the pair image of the abstract combine
  \<open>\<langle>_|_\<rangle>\<close>: pair surgery on the split side, \<^const>\<open>combine_abs\<close> on the
  homogeneous side.
\<close>

lemma combine_split_split_state:
  fixes A B :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "combine_split (split_state A) (split_state B) = split_state \<langle>A|B\<rangle>"
proof -
  have cab: "\<langle>A|B\<rangle> = restrict_local A \<squnion> restrict_global B"
    unfolding combine_abs_def restrict_combine ..
  show ?thesis
    unfolding combine_split_def split_state_eq_restrict cab
    by (simp add: restrict_local_combine_eq restrict_global_combine_eq)
qed

subsection \<open>Split-shaped effectful trees\<close>

text \<open>
  Tree bodies that compute over the split representation: the transfer result
  is split once, the global component is published as the \<open>Side\<close> contribution
  and the local component is the \<open>Answer\<close>.  Both trees are extensionally equal
  to their \<open>restrict\<close>-based originals, so all shape lemmas
  (\<open>traverse_*\<close>, \<open>sides_*\<close>, \<open>etf_full_*\<close>) transport by rewriting.
\<close>

definition split_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "split_edge_tree f u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>gl.
       let sp = split_state (f (su \<squnion> gl)) in
       Side () (snd sp) (Answer (fst sp))))"

lemma split_edge_tree_eq_unit:
  "split_edge_tree f u = unit_edge_tree f u"
  unfolding split_edge_tree_def unit_edge_tree_def
  by (simp add: Let_def split_state_eq_restrict)

definition split_combine_tree ::
  "pp \<Rightarrow> pp \<Rightarrow> (pp, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
where
  "split_combine_tree cc ex =
     QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>gl.
       let sp = combine_split (split_state (sc \<squnion> gl)) (split_state (se \<squnion> gl)) in
       Side () (snd sp) (Answer (fst sp)))))"

lemma split_combine_tree_eq_unit:
  "split_combine_tree cc ex = unit_combine_tree cc ex"
  unfolding split_combine_tree_def unit_combine_tree_def
  by (simp add: Let_def combine_split_def split_state_eq_restrict
        restrict_local_combine_eq restrict_global_combine_eq)

subsection \<open>Split effectful-transfer factory\<close>

definition split_etf_of_transfer ::
  "'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "split_etf_of_transfer tf = \<lparr>
    etf_nop        = (\<lambda>u. split_edge_tree (apply_tf tf EA_Nop) u),
    etf_assign     = (\<lambda>x e u. split_edge_tree (apply_tf tf (EA_Assign x e)) u),
    etf_assume     = (\<lambda>b u. split_edge_tree (apply_tf tf (EA_Assume b)) u),
    etf_assume_not = (\<lambda>b u. split_edge_tree (apply_tf tf (EA_AssumeNot b)) u),
    etf_enter      = (\<lambda>u. split_edge_tree (apply_tf tf EA_Enter) u),
    etf_combine    = split_combine_tree
  \<rparr>"

theorem split_etf_of_transfer_eq_unit:
  "split_etf_of_transfer tf = unit_etf_of_transfer tf"
  unfolding split_etf_of_transfer_def unit_etf_of_transfer_def
  by (simp add: fun_eq_iff split_edge_tree_eq_unit split_combine_tree_eq_unit)

corollary sound_effectful_transfer_split_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes "sound_transfer tf"
  shows "sound_effectful_transfer (split_etf_of_transfer tf)"
  unfolding split_etf_of_transfer_eq_unit
  by (rule sound_effectful_transfer_unit_of_transfer[OF assms])

subsection \<open>The split-seeded CMP generator\<close>

text \<open>
  \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> with the entry-seed decomposition of \<open>s0\<close>
  expressed through \<^const>\<open>split_state\<close>: the local component seeds the entry
  accumulator, the global component is the entry \<open>Side\<close> publication.
\<close>

definition side_cfg_T_eff_cmp_split_seed ::
  "('c \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> ('c \<Rightarrow> 'a abs_state) \<Rightarrow> cfg
   \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_cmp_split_seed gkey cmb frame_seed g etf bot0 s0 =
     (\<lambda>(v, c).
        let s0sp = split_state s0;
            acc0 = (if v = cfg_entry g then bot0 \<squnion> fst s0sp else bot0)
                   \<squnion> (if is_frame_entry g v then frame_seed c else \<bottom>);
            intra = map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey c)
                            (map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u)))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (snd s0sp) t else t)"

theorem side_cfg_T_eff_cmp_split_seed_eq:
  "side_cfg_T_eff_cmp_split_seed gkey cmb frame_seed g etf bot0 s0
   = side_cfg_T_eff_cmp_seed gkey cmb frame_seed g etf bot0 s0"
  unfolding side_cfg_T_eff_cmp_split_seed_def side_cfg_T_eff_cmp_seed_def
  by (simp add: Let_def fst_split_state_restrict snd_split_state_restrict
        cong: if_cong)

corollary side_cfg_T_eff_cmp_split_seed_const:
  "side_cfg_T_eff_cmp_split_seed gkey cmb (\<lambda>_. fr) g etf bot0 s0
   = side_cfg_T_eff_cmp gkey cmb g etf fr bot0 s0"
  by (simp add: side_cfg_T_eff_cmp_split_seed_eq side_cfg_T_eff_cmp_seed_const)

text \<open>
  Post-fixpoints of the migrated generator are exactly those of the original:
  executable transports and all existing soundness theorems apply unchanged.
\<close>

lemma part_post_solution_split_seed_iff:
  "part_post_solution (side_cfg_T_eff_cmp_split_seed gkey cmb fs g etf bot0 s0) x \<sigma> vars
   \<longleftrightarrow> part_post_solution (side_cfg_T_eff_cmp_seed gkey cmb fs g etf bot0 s0) x \<sigma> vars"
  by (simp add: side_cfg_T_eff_cmp_split_seed_eq)

section \<open>Stage 1C: the remaining tree factories over the split representation\<close>

text \<open>
  The split image of a pair-of-restrictions combine reassembles to the
  homogeneous combine idiom --- the workhorse for the \<open>local\<close> tree below.
\<close>

lemma merge_combine_split:
  fixes A B :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "merge_state (combine_split (split_state A) (split_state B))
         = restrict_local A \<squnion> restrict_global B"
  by (simp add: combine_split_split_state combine_abs_def restrict_combine[symmetric])

subsection \<open>Retain and clean edge trees\<close>

text \<open>
  \<^const>\<open>retain_edge_tree\<close> and \<^const>\<open>clean_edge_tree\<close> deliberately answer the
  \<^emph>\<open>whole\<close> transfer result --- the local unknown carries the flow-sensitive
  copy of the globals (the \<open>Inr\<close> slot is flow-insensitive: all writes joined).
  In split terms the \<open>Answer\<close> payload is a \<^emph>\<open>reassembled pair\<close>
  (\<^term>\<open>merge_state rsp\<close>), not the local component alone: at independent
  \<open>('l, 'g)\<close> lattices these transfers need pair-valued local unknowns.  The
  split phrasing is still exact --- \<open>merge_state (split_state res) = res\<close> is the
  Stage 1A isomorphism --- so both migrate with definitional equality.
\<close>

definition split_retain_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "split_retain_edge_tree f u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>gl.
       let rsp = split_state (f (su \<squnion> gl)) in
       Side () (snd rsp) (Answer (merge_state rsp))))"

lemma split_retain_edge_tree_eq:
  "split_retain_edge_tree f u = retain_edge_tree f u"
  unfolding split_retain_edge_tree_def retain_edge_tree_def
  by (simp add: Let_def snd_split_state_restrict)

definition split_clean_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'u \<Rightarrow> ('u, unit, 'a abs_state) strategy_tree"
where
  "split_clean_edge_tree f u =
     QueryL u (\<lambda>su.
       let rsp = split_state (f su) in
       Side () (snd rsp) (Answer (merge_state rsp)))"

lemma split_clean_edge_tree_eq:
  "split_clean_edge_tree f u = clean_edge_tree f u"
  unfolding split_clean_edge_tree_def clean_edge_tree_def
  by (simp add: Let_def snd_split_state_restrict)

subsection \<open>Local-only edge tree\<close>

text \<open>
  \<^const>\<open>local_edge_tree\<close> computes on the local half and passes the globals
  stored in the local slot through unchanged: in split terms, the \<open>Answer\<close>
  is \<^const>\<open>combine_split\<close> of the split result (locals) with the split input
  (pass-through globals), reassembled.
\<close>

definition split_local_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "split_local_edge_tree f u =
     QueryL u (\<lambda>su.
       let sp = split_state su;
           rsp = split_state (f (fst sp))
       in Answer (merge_state (combine_split rsp sp)))"

lemma split_local_edge_tree_eq:
  "split_local_edge_tree f u = local_edge_tree f u"
  unfolding split_local_edge_tree_def local_edge_tree_def
  by (simp add: Let_def fst_split_state_restrict merge_combine_split)

definition split_mixed_etf_edge_tree ::
  "'a::sound_domain domain_transfer \<Rightarrow> edge_action \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "split_mixed_etf_edge_tree tf a u =
    (if local_edge_action a then split_local_edge_tree (apply_tf tf a) u
     else split_edge_tree (apply_tf tf a) u)"

lemma split_mixed_etf_edge_tree_eq:
  "split_mixed_etf_edge_tree tf a u = mixed_etf_edge_tree tf a u"
  unfolding split_mixed_etf_edge_tree_def mixed_etf_edge_tree_def
  by (simp add: split_local_edge_tree_eq split_edge_tree_eq_unit)

subsection \<open>Context-routed combine tree\<close>

definition split_combine_tree_ctx ::
  "('c \<Rightarrow> 'a abs_state \<Rightarrow> 'c) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'c
   \<Rightarrow> (pp \<times> 'c, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
where
  "split_combine_tree_ctx ec cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG () (\<lambda>gl. QueryL (ex, ec ctx (sc \<squnion> gl)) (\<lambda>se.
       let sp = combine_split (split_state (sc \<squnion> gl)) (split_state (se \<squnion> gl)) in
       Side () (snd sp) (Answer (fst sp)))))"

lemma split_combine_tree_ctx_eq:
  "split_combine_tree_ctx ec cc ex ctx = unit_combine_tree_ctx ec cc ex ctx"
  unfolding split_combine_tree_ctx_def unit_combine_tree_ctx_def
  by (simp add: Let_def combine_split_def split_state_eq_restrict
        restrict_local_combine_eq restrict_global_combine_eq)

subsection \<open>Remaining transfer factories\<close>

definition split_retain_etf_of_transfer ::
  "'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "split_retain_etf_of_transfer tf = \<lparr>
    etf_nop        = (\<lambda>u. split_retain_edge_tree (apply_tf tf EA_Nop) u),
    etf_assign     = (\<lambda>x e u. split_retain_edge_tree (apply_tf tf (EA_Assign x e)) u),
    etf_assume     = (\<lambda>b u. split_retain_edge_tree (apply_tf tf (EA_Assume b)) u),
    etf_assume_not = (\<lambda>b u. split_retain_edge_tree (apply_tf tf (EA_AssumeNot b)) u),
    etf_enter      = (\<lambda>u. split_retain_edge_tree (apply_tf tf EA_Enter) u),
    etf_combine    = split_combine_tree
  \<rparr>"

theorem split_retain_etf_of_transfer_eq:
  "split_retain_etf_of_transfer tf = retain_etf_of_transfer tf"
  unfolding split_retain_etf_of_transfer_def retain_etf_of_transfer_def
  by (simp add: fun_eq_iff split_retain_edge_tree_eq split_combine_tree_eq_unit)

corollary sound_effectful_transfer_split_retain:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes "sound_transfer tf"
  shows "sound_effectful_transfer (split_retain_etf_of_transfer tf)"
  unfolding split_retain_etf_of_transfer_eq
  by (rule sound_effectful_transfer_retain_of_transfer[OF assms])

definition split_mixed_etf_of_transfer ::
  "'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "split_mixed_etf_of_transfer tf = \<lparr>
    etf_nop        = split_mixed_etf_edge_tree tf EA_Nop,
    etf_assign     = (\<lambda>x e. split_mixed_etf_edge_tree tf (EA_Assign x e)),
    etf_assume     = (\<lambda>b. split_mixed_etf_edge_tree tf (EA_Assume b)),
    etf_assume_not = (\<lambda>b. split_mixed_etf_edge_tree tf (EA_AssumeNot b)),
    etf_enter      = split_mixed_etf_edge_tree tf EA_Enter,
    etf_combine    = split_combine_tree
  \<rparr>"

theorem split_mixed_etf_of_transfer_eq:
  "split_mixed_etf_of_transfer tf = mixed_etf_of_transfer tf"
  unfolding split_mixed_etf_of_transfer_def mixed_etf_of_transfer_def
  by (simp add: fun_eq_iff split_mixed_etf_edge_tree_eq split_combine_tree_eq_unit)

corollary sound_effectful_transfer_split_mixed:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes st: "sound_transfer tf"
  assumes loc_inv: "\<And>a. local_edge_action a \<Longrightarrow>
      local_edge_invariant (apply_tf tf a)"
  shows "sound_effectful_transfer (split_mixed_etf_of_transfer tf)"
  unfolding split_mixed_etf_of_transfer_eq
  by (rule sound_effectful_transfer_mixed_of_transfer[OF st loc_inv])

definition split_clean_etf_of_transfer ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "split_clean_etf_of_transfer tf = \<lparr>
    etf_nop        = split_clean_edge_tree (apply_tf tf EA_Nop),
    etf_assign     = (\<lambda>x e. split_clean_edge_tree (apply_tf tf (EA_Assign x e))),
    etf_assume     = (\<lambda>b. split_clean_edge_tree (apply_tf tf (EA_Assume b))),
    etf_assume_not = (\<lambda>b. split_clean_edge_tree (apply_tf tf (EA_AssumeNot b))),
    etf_enter      = split_clean_edge_tree (apply_tf tf EA_Enter),
    etf_combine    = split_combine_tree
  \<rparr>"

theorem split_clean_etf_of_transfer_eq:
  "split_clean_etf_of_transfer tf = clean_etf_of_transfer tf"
  unfolding split_clean_etf_of_transfer_def clean_etf_of_transfer_def
  by (simp add: fun_eq_iff split_clean_edge_tree_eq split_combine_tree_eq_unit)

subsection \<open>Monovariant generator seed\<close>

text \<open>
  The monovariant RHS builder \<^const>\<open>make_side_rhs_tree_eff\<close> decomposes \<open>s0\<close>
  exactly like the CMP generator; the split phrasing and equality mirror
  \<^const>\<open>side_cfg_T_eff_cmp_split_seed\<close>.
\<close>

definition split_make_side_rhs_tree_eff ::
  "cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a abs_state) strategy_tree"
where
  "split_make_side_rhs_tree_eff g etf bot0 s0 gseed v =
     (let s0sp = split_state s0;
          acc0 = (if v = cfg_entry g then bot0 \<squnion> fst s0sp else bot0);
          t    = side_rhs_fold_eff etf acc0
                   (predecessor_list g v) (combine_predecessor_list g v)
      in if v = cfg_entry g then Side gseed (snd s0sp) t else t)"

lemma split_make_side_rhs_tree_eff_eq:
  "split_make_side_rhs_tree_eff g etf bot0 s0 gseed v
   = make_side_rhs_tree_eff g etf bot0 s0 gseed v"
  unfolding split_make_side_rhs_tree_eff_def make_side_rhs_tree_eff_def
  by (simp add: Let_def fst_split_state_restrict snd_split_state_restrict
        cong: if_cong)

corollary side_cfg_T_eff_split_eq:
  "split_make_side_rhs_tree_eff g etf bot0 s0 gseed
   = side_cfg_T_eff g etf bot0 s0 gseed"
  by (simp add: fun_eq_iff split_make_side_rhs_tree_eff_eq side_cfg_T_eff_def)

subsection \<open>Specification-level split generator\<close>

context goblint_analysis_spec
begin

definition spec_generator_split ::
  "cfg \<Rightarrow> (unit, 'a) effectful_domain_transfer \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "spec_generator_split g etf bot0 s0 =
     side_cfg_T_eff_cmp_split_seed gkey (spec_cmb etf) entry_seed g etf bot0 s0"

theorem spec_generator_split_eq:
  "spec_generator_split g etf bot0 s0 = spec_generator g etf bot0 s0"
  unfolding spec_generator_split_def spec_generator_def
  by (rule side_cfg_T_eff_cmp_split_seed_eq)

lemma part_post_solution_spec_split_iff:
  "part_post_solution (spec_generator_split g etf bot0 s0) x \<sigma> vars
   \<longleftrightarrow> part_post_solution (spec_generator g etf bot0 s0) x \<sigma> vars"
  by (simp add: spec_generator_split_eq)

end

end
