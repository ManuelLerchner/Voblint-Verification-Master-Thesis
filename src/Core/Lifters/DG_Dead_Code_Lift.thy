theory DG_Dead_Code_Lift
  imports Voblint_Core.DG_Soundness
begin

section \<open>Dead code as a specification transformer\<close>

text \<open>
  Goblint's \<open>DeadCodeLifter\<close> as a verified functor: \<open>dead_code_lift\<close> maps any
  analysis record to one whose local carrier distinguishes \<open>Bot\<close>, "control
  cannot reach here", from \<open>Lifted d\<close>, "reachable, described by \<open>d\<close>".  Every
  field propagates \<open>Bot\<close> strictly and delegates live states to the wrapped
  record; global effects on a dead input are inert.  The one theorem,
  \<open>dead_code_lift_sound\<close>, upgrades soundness of the wrapped record to
  soundness of the lifted one at \<open>lift_gamma\<close>, which sends \<open>Bot\<close> to the
  empty store set.  The functor is reachability-only: it never converts a
  live state whose concretization happens to be empty into \<open>Bot\<close> -- that
  normalization needs an emptiness oracle and is a separate layer.
\<close>

definition lift_gamma ::
  "('dl \<Rightarrow> 'dg \<Rightarrow> store set) \<Rightarrow> 'dl lifted \<Rightarrow> 'dg \<Rightarrow> store set" where
  "lift_gamma gammaDG d g = (case d of Bot \<Rightarrow> {} | Lifted x \<Rightarrow> gammaDG x g)"

lemma lift_gamma_simps [simp]:
  "lift_gamma gammaDG Bot g = {}"
  "lift_gamma gammaDG (Lifted x) g = gammaDG x g"
  by (simp_all add: lift_gamma_def)

text \<open>One combinator covers the eight step-shaped fields: they all share the
  \<open>'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl\<close> arity, so lifting is a single case split.\<close>

definition lift_dg_step ::
  "('dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl) \<Rightarrow> 'dl lifted \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl lifted" where
  "lift_dg_step f d g = (case d of Bot \<Rightarrow> (g, Bot) | Lifted x \<Rightarrow> apsnd Lifted (f x g))"

lemma lift_dg_step_simps [simp]:
  "lift_dg_step f Bot g = (g, Bot)"
  "lift_dg_step f (Lifted x) g = apsnd Lifted (f x g)"
  by (simp_all add: lift_dg_step_def)

definition dead_code_lift ::
  "('dl, 'dg) dg_spec \<Rightarrow> ('dl lifted, 'dg) dg_spec" where
  "dead_code_lift S = (|
    dgs_skip       = lift_dg_step (dgs_skip S),
    dgs_assign     = (\<lambda>x e. lift_dg_step (dgs_assign S x e)),
    dgs_special    = (\<lambda>sc x. lift_dg_step (dgs_special S sc x)),
    dgs_branch     = (\<lambda>b pol. lift_dg_step (dgs_branch S b pol)),
    dgs_body       = (\<lambda>p. lift_dg_step (dgs_body S p)),
    dgs_return     = (\<lambda>e p. lift_dg_step (dgs_return S e p)),
    dgs_enter      = (\<lambda>ci. lift_dg_step (dgs_enter S ci)),
    dgs_event      = (\<lambda>ev. lift_dg_step (dgs_event S ev)),
    dgs_caller_cont    = (\<lambda>ci dc g. map_lift (\<lambda>x. dgs_caller_cont S ci x g) dc),
    dgs_combine_env    = (\<lambda>ci dc de g.
      case (dc, de) of
        (Lifted x, Lifted y) \<Rightarrow> apsnd Lifted (dgs_combine_env S ci x y g)
      | _ \<Rightarrow> (g, Bot)),
    dgs_combine_assign = (\<lambda>ci de g m.
      case (de, snd m) of
        (Lifted y, Lifted z) \<Rightarrow> apsnd Lifted (dgs_combine_assign S ci y g (fst m, z))
      | _ \<Rightarrow> (fst m, Bot))
  |)"

subsection \<open>Field equations\<close>

lemma dg_spec_step_dead_code_lift [simp]:
  "dg_spec_step (dead_code_lift S) a = lift_dg_step (dg_spec_step S a)"
  by (cases a) (simp_all add: dead_code_lift_def)

lemma dgs_enter_dead_code_lift [simp]:
  "dgs_enter (dead_code_lift S) ci = lift_dg_step (dgs_enter S ci)"
  by (simp add: dead_code_lift_def)

lemma dgs_caller_cont_dead_code_lift [simp]:
  "dgs_caller_cont (dead_code_lift S) ci dc g
     = map_lift (\<lambda>x. dgs_caller_cont S ci x g) dc"
  by (simp add: dead_code_lift_def)

text \<open>The two combine stages compose to the strict lift of the wrapped
  record's composed combine: dead on either side, delegating otherwise.\<close>

lemma dgs_combine_dead_code_lift [simp]:
  "dgs_combine (dead_code_lift S) ci dc de g =
     (case (dc, de) of
        (Lifted x, Lifted y) \<Rightarrow> apsnd Lifted (dgs_combine S ci x y g)
      | _ \<Rightarrow> (g, Bot))"
  by (cases dc; cases de)
     (simp_all add: dgs_combine_def dead_code_lift_def apsnd_def map_prod_def
        split: prod.splits)

subsection \<open>Soundness preservation\<close>

theorem dead_code_lift_sound:
  assumes sound: "sound_dg_spec S gammaDG gs"
  shows "sound_dg_spec (dead_code_lift S) (lift_gamma gammaDG) gs"
proof (rule sound_dg_spec.intro)
  interpret sound_dg_spec S gammaDG gs by (rule sound)
  show "\<And>d d' g g'. d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow>
      lift_gamma gammaDG d g \<subseteq> lift_gamma gammaDG d' g'"
    by (rename_tac d d' g g', case_tac d; case_tac d')
       (auto dest: gammaDG_mono[THEN subsetD])
  show "\<And>a d g. edge_collect a (lift_gamma gammaDG d g) \<subseteq>
      (case dg_spec_step (dead_code_lift S) a d g of
         (g', d') \<Rightarrow> lift_gamma gammaDG d' g')"
    by (rename_tac a d g, case_tac d)
       (auto simp: case_prod_beta dest: step_sound_fs[THEN subsetD])
  show "\<And>s dc g ci. s \<in> lift_gamma gammaDG dc g \<Longrightarrow>
      s \<in> lift_gamma gammaDG (dgs_caller_cont (dead_code_lift S) ci dc g) g"
    by (rename_tac s dc g ci, case_tac dc) (auto intro: caller_cont_sound)
  show "\<And>s dcont g t de ci. s \<in> lift_gamma gammaDG dcont g \<Longrightarrow>
      t \<in> lift_gamma gammaDG de g \<Longrightarrow>
      combine_collect gs (ci_dst ci) s t \<in>
        (case dgs_combine (dead_code_lift S) ci dcont de g of
           (g', d') \<Rightarrow> lift_gamma gammaDG d' g')"
    by (rename_tac s dcont g t de ci, case_tac dcont; case_tac de)
       (auto simp: case_prod_beta dest: combine_sound_fs)
  show "\<And>s dc g ci. s \<in> lift_gamma gammaDG dc g \<Longrightarrow>
      call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in>
        (case dgs_enter (dead_code_lift S) ci dc g of
           (g', d') \<Rightarrow> lift_gamma gammaDG d' g')"
    by (rename_tac s dc g ci, case_tac dc)
       (auto simp: case_prod_beta dest: enter_sound_fs)
qed

subsection \<open>Soundness sees only the composed operations\<close>


text \<open>The five obligations mention \<^const>\<open>dg_spec_step\<close>, \<^const>\<open>dgs_caller_cont\<close>,
  \<^const>\<open>dgs_combine\<close> and \<^const>\<open>dgs_enter\<close> and nothing else, so two records
  agreeing on those four are interchangeable inside \<^locale>\<open>sound_dg_spec\<close> --
  even when a raw field (say, an unnormalized \<open>dgs_combine_env\<close> stage)
  differs.\<close>

lemma sound_dg_spec_cong:
  assumes step: "\<And>a d g. dg_spec_step S' a d g = dg_spec_step S a d g"
    and cont: "\<And>ci dc g. dgs_caller_cont S' ci dc g = dgs_caller_cont S ci dc g"
    and comb: "\<And>ci dc de g. dgs_combine S' ci dc de g = dgs_combine S ci dc de g"
    and enter: "\<And>ci dc g. dgs_enter S' ci dc g = dgs_enter S ci dc g"
    and sound: "sound_dg_spec S gammaDG gs"
  shows "sound_dg_spec S' gammaDG gs"
proof -
  interpret sound_dg_spec S gammaDG gs by (rule sound)
  show ?thesis
  proof (rule sound_dg_spec.intro)
    show "\<And>d d' g g'. d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> gammaDG d g \<subseteq> gammaDG d' g'"
      by (rule gammaDG_mono)
  qed (simp_all add: step cont comb enter
        step_sound caller_cont_sound combine_sound enter_sound)
qed

subsection \<open>Normalization as a separate layer\<close>

text \<open>
  \<open>dead_code_normalize\<close> additionally collapses a transfer output whose inner
  state a caller-supplied \<open>empty_pred\<close> certifies empty to \<open>Bot\<close>.  It
  renormalizes exactly the fields that produce a fresh transfer output --
  the eight step-shaped fields and \<open>dgs_combine_assign\<close> -- and leaves the
  pass-through fields \<open>dgs_caller_cont\<close> and \<open>dgs_combine_env\<close> alone, the
  same sites the concrete lifted records normalize at.  Soundness needs
  exactness of the predicate against the concretization: an empty verdict
  must mean an empty store set.
\<close>

definition renormalize :: "('dl \<Rightarrow> bool) \<Rightarrow> 'dl lifted \<Rightarrow> 'dl lifted" where
  "renormalize empty_pred d = do { x <- d; normalize_lift empty_pred x }"

lemma renormalize_simps [simp]:
  "renormalize empty_pred Bot = Bot"
  "renormalize empty_pred (Lifted x) = normalize_lift empty_pred x"
  by (simp_all add: renormalize_def)

definition dead_code_normalize ::
  "('dl \<Rightarrow> bool) \<Rightarrow> ('dl lifted, 'dg) dg_spec \<Rightarrow> ('dl lifted, 'dg) dg_spec" where
  "dead_code_normalize empty_pred S = S(|
    dgs_skip       := (\<lambda>d g. apsnd (renormalize empty_pred) (dgs_skip S d g)),
    dgs_assign     := (\<lambda>x e d g. apsnd (renormalize empty_pred) (dgs_assign S x e d g)),
    dgs_special    := (\<lambda>sc x d g. apsnd (renormalize empty_pred) (dgs_special S sc x d g)),
    dgs_branch     := (\<lambda>b pol d g. apsnd (renormalize empty_pred) (dgs_branch S b pol d g)),
    dgs_body       := (\<lambda>p d g. apsnd (renormalize empty_pred) (dgs_body S p d g)),
    dgs_return     := (\<lambda>e p d g. apsnd (renormalize empty_pred) (dgs_return S e p d g)),
    dgs_enter      := (\<lambda>ci d g. apsnd (renormalize empty_pred) (dgs_enter S ci d g)),
    dgs_event      := (\<lambda>ev d g. apsnd (renormalize empty_pred) (dgs_event S ev d g)),
    dgs_combine_assign :=
      (\<lambda>ci de g m. apsnd (renormalize empty_pred) (dgs_combine_assign S ci de g m))
  |)"

lemma dg_spec_step_dead_code_normalize [simp]:
  "dg_spec_step (dead_code_normalize empty_pred S) a d g
     = apsnd (renormalize empty_pred) (dg_spec_step S a d g)"
  by (cases a) (simp_all add: dead_code_normalize_def)

lemma dgs_enter_dead_code_normalize [simp]:
  "dgs_enter (dead_code_normalize empty_pred S) ci d g
     = apsnd (renormalize empty_pred) (dgs_enter S ci d g)"
  by (simp add: dead_code_normalize_def)

lemma dgs_caller_cont_dead_code_normalize [simp]:
  "dgs_caller_cont (dead_code_normalize empty_pred S) ci dc g
     = dgs_caller_cont S ci dc g"
  by (simp add: dead_code_normalize_def)

lemma dgs_combine_dead_code_normalize [simp]:
  "dgs_combine (dead_code_normalize empty_pred S) ci dc de g
     = apsnd (renormalize empty_pred) (dgs_combine S ci dc de g)"
  by (simp add: dgs_combine_def dead_code_normalize_def)

lemma lift_gamma_renormalize:
  assumes exact: "\<And>x g. empty_pred x \<Longrightarrow> gammaDG x g = {}"
  shows "lift_gamma gammaDG (renormalize empty_pred d) g = lift_gamma gammaDG d g"
  by (cases d) (auto simp: normalize_lift_def exact)

theorem dead_code_normalize_sound:
  assumes sound: "sound_dg_spec S (lift_gamma gammaDG) gs"
    and exact: "\<And>x g. empty_pred x \<Longrightarrow> gammaDG x g = {}"
  shows "sound_dg_spec (dead_code_normalize empty_pred S) (lift_gamma gammaDG) gs"
proof -
  interpret sound_dg_spec S "lift_gamma gammaDG" gs by (rule sound)
  show ?thesis
  proof (rule sound_dg_spec.intro)
    show "\<And>d d' g g'. d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow>
        lift_gamma gammaDG d g \<subseteq> lift_gamma gammaDG d' g'"
      by (rule gammaDG_mono)
  qed (simp_all add: case_prod_beta lift_gamma_renormalize[OF exact]
        step_sound_fs caller_cont_sound combine_sound_fs enter_sound_fs)
qed

subsection \<open>Preserving an executable commute\<close>

text \<open>
  A record over an executable carrier corresponds to a semantic record when
  the four composed operations commute with a pair of local/global readback
  functions.  Both lifter stages preserve that correspondence: the pure lift
  along the functorial \<^const>\<open>map_lift\<close> of the local readback, and
  normalization whenever the two emptiness tests agree across the readback.
  A domain therefore proves its commute once, for its unlifted core, and
  every lifted variant's commute is these two theorems -- the growth is
  instances plus lifters, not instances times lifters.
\<close>

locale dg_spec_commute =
  fixes Floc :: "'e \<Rightarrow> 'dl"
    and Fglob :: "'ge \<Rightarrow> 'dg"
    and S_st :: "('e, 'ge) dg_spec"
    and S :: "('dl, 'dg) dg_spec"
  assumes step_commute:
      "map_prod Fglob Floc (dg_spec_step S_st a d g)
         = dg_spec_step S a (Floc d) (Fglob g)"
    and cont_commute:
      "Floc (dgs_caller_cont S_st ci dc g)
         = dgs_caller_cont S ci (Floc dc) (Fglob g)"
    and combine_commute:
      "map_prod Fglob Floc (dgs_combine S_st ci dc de g)
         = dgs_combine S ci (Floc dc) (Floc de) (Fglob g)"
    and enter_commute:
      "map_prod Fglob Floc (dgs_enter S_st ci dc g)
         = dgs_enter S ci (Floc dc) (Fglob g)"

text \<open>A commute fact transports across composed-operation agreement on
  either record, the same characterize-don't-rebuild move
  \<open>sound_dg_spec_cong\<close> makes for soundness: a lifter's naturality theorem
  gives commute for its own construction, and these two lemmas carry it
  onto a frozen record that only agrees with that construction composedly.\<close>

lemma dg_spec_commute_cong_left:
  assumes step: "\<And>a d g. dg_spec_step S_st' a d g = dg_spec_step S_st a d g"
    and cont: "\<And>ci dc g. dgs_caller_cont S_st' ci dc g = dgs_caller_cont S_st ci dc g"
    and comb: "\<And>ci dc de g. dgs_combine S_st' ci dc de g = dgs_combine S_st ci dc de g"
    and enter: "\<And>ci dc g. dgs_enter S_st' ci dc g = dgs_enter S_st ci dc g"
    and commute: "dg_spec_commute Floc Fglob S_st S"
  shows "dg_spec_commute Floc Fglob S_st' S"
proof -
  interpret dg_spec_commute Floc Fglob S_st S by (rule commute)
  show ?thesis
  proof (rule dg_spec_commute.intro)
    show "\<And>a d g. map_prod Fglob Floc (dg_spec_step S_st' a d g)
        = dg_spec_step S a (Floc d) (Fglob g)"
      by (simp add: step step_commute)
    show "\<And>ci dc g. Floc (dgs_caller_cont S_st' ci dc g)
        = dgs_caller_cont S ci (Floc dc) (Fglob g)"
      by (simp add: cont cont_commute)
    show "\<And>ci dc de g. map_prod Fglob Floc (dgs_combine S_st' ci dc de g)
        = dgs_combine S ci (Floc dc) (Floc de) (Fglob g)"
      by (simp add: comb combine_commute)
    show "\<And>ci dc g. map_prod Fglob Floc (dgs_enter S_st' ci dc g)
        = dgs_enter S ci (Floc dc) (Fglob g)"
      by (simp add: enter enter_commute)
  qed
qed

lemma dg_spec_commute_cong_right:
  assumes step: "\<And>a d g. dg_spec_step S' a d g = dg_spec_step S a d g"
    and cont: "\<And>ci dc g. dgs_caller_cont S' ci dc g = dgs_caller_cont S ci dc g"
    and comb: "\<And>ci dc de g. dgs_combine S' ci dc de g = dgs_combine S ci dc de g"
    and enter: "\<And>ci dc g. dgs_enter S' ci dc g = dgs_enter S ci dc g"
    and commute: "dg_spec_commute Floc Fglob S_st S"
  shows "dg_spec_commute Floc Fglob S_st S'"
proof -
  interpret dg_spec_commute Floc Fglob S_st S by (rule commute)
  show ?thesis
  proof (rule dg_spec_commute.intro)
    show "\<And>a d g. map_prod Fglob Floc (dg_spec_step S_st a d g)
        = dg_spec_step S' a (Floc d) (Fglob g)"
      by (simp add: step[symmetric] step_commute)
    show "\<And>ci dc g. Floc (dgs_caller_cont S_st ci dc g)
        = dgs_caller_cont S' ci (Floc dc) (Fglob g)"
      by (simp add: cont[symmetric] cont_commute)
    show "\<And>ci dc de g. map_prod Fglob Floc (dgs_combine S_st ci dc de g)
        = dgs_combine S' ci (Floc dc) (Floc de) (Fglob g)"
      by (simp add: comb[symmetric] combine_commute)
    show "\<And>ci dc g. map_prod Fglob Floc (dgs_enter S_st ci dc g)
        = dgs_enter S' ci (Floc dc) (Fglob g)"
      by (simp add: enter[symmetric] enter_commute)
  qed
qed

theorem dead_code_lift_commute:
  assumes commute: "dg_spec_commute Floc Fglob S_st S"
  shows "dg_spec_commute (map_lift Floc) Fglob
           (dead_code_lift S_st) (dead_code_lift S)"
proof (rule dg_spec_commute.intro)
  interpret dg_spec_commute Floc Fglob S_st S by (rule commute)
  show "\<And>a d g. map_prod Fglob (map_lift Floc)
      (dg_spec_step (dead_code_lift S_st) a d g)
        = dg_spec_step (dead_code_lift S) a (map_lift Floc d) (Fglob g)"
    by (rename_tac a d g, case_tac d)
       (simp_all add: step_commute[symmetric] apsnd_def map_prod_def
          split: prod.splits)
  show "\<And>ci dc g. map_lift Floc (dgs_caller_cont (dead_code_lift S_st) ci dc g)
        = dgs_caller_cont (dead_code_lift S) ci (map_lift Floc dc) (Fglob g)"
    by (rename_tac ci dc g, case_tac dc) (simp_all add: cont_commute)
  show "\<And>ci dc de g. map_prod Fglob (map_lift Floc)
      (dgs_combine (dead_code_lift S_st) ci dc de g)
        = dgs_combine (dead_code_lift S) ci (map_lift Floc dc) (map_lift Floc de)
            (Fglob g)"
    by (rename_tac ci dc de g, case_tac dc; case_tac de)
       (simp_all add: combine_commute[symmetric] apsnd_def map_prod_def
          split: prod.splits)
  show "\<And>ci dc g. map_prod Fglob (map_lift Floc)
      (dgs_enter (dead_code_lift S_st) ci dc g)
        = dgs_enter (dead_code_lift S) ci (map_lift Floc dc) (Fglob g)"
    by (rename_tac ci dc g, case_tac dc)
       (simp_all add: enter_commute[symmetric] apsnd_def map_prod_def
          split: prod.splits)
qed

lemma map_lift_renormalize:
  assumes exact: "\<And>x. empty_st x \<longleftrightarrow> empty_sem (Floc x)"
  shows "map_lift Floc (renormalize empty_st d)
           = renormalize empty_sem (map_lift Floc d)"
  by (cases d) (simp_all add: normalize_lift_def exact)

theorem dead_code_normalize_commute:
  assumes commute: "dg_spec_commute (map_lift Floc) Fglob S_st S"
    and exact: "\<And>x. empty_st x \<longleftrightarrow> empty_sem (Floc x)"
  shows "dg_spec_commute (map_lift Floc) Fglob
           (dead_code_normalize empty_st S_st) (dead_code_normalize empty_sem S)"
proof (rule dg_spec_commute.intro)
  interpret dg_spec_commute "map_lift Floc" Fglob S_st S by (rule commute)
  have ren: "\<And>d. map_lift Floc (renormalize empty_st d)
                 = renormalize empty_sem (map_lift Floc d)"
    by (rule map_lift_renormalize) (rule exact)
  show "\<And>a d g. map_prod Fglob (map_lift Floc)
      (dg_spec_step (dead_code_normalize empty_st S_st) a d g)
        = dg_spec_step (dead_code_normalize empty_sem S) a (map_lift Floc d)
            (Fglob g)"
    by (simp add: step_commute[symmetric] ren
          apsnd_def map_prod_def split: prod.splits)
  show "\<And>ci dc g. map_lift Floc
      (dgs_caller_cont (dead_code_normalize empty_st S_st) ci dc g)
        = dgs_caller_cont (dead_code_normalize empty_sem S) ci (map_lift Floc dc)
            (Fglob g)"
    by (simp add: cont_commute)
  show "\<And>ci dc de g. map_prod Fglob (map_lift Floc)
      (dgs_combine (dead_code_normalize empty_st S_st) ci dc de g)
        = dgs_combine (dead_code_normalize empty_sem S) ci (map_lift Floc dc)
            (map_lift Floc de) (Fglob g)"
    by (simp add: combine_commute[symmetric] ren
          apsnd_def map_prod_def split: prod.splits)
  show "\<And>ci dc g. map_prod Fglob (map_lift Floc)
      (dgs_enter (dead_code_normalize empty_st S_st) ci dc g)
        = dgs_enter (dead_code_normalize empty_sem S) ci (map_lift Floc dc)
            (Fglob g)"
    by (simp add: enter_commute[symmetric] ren
          apsnd_def map_prod_def split: prod.splits)
qed

end
