theory TD_Side_Tree
  imports TD_Side_CFG "Voblint_CFG.CFG_Transfer" Strategy_Tree_Monad
begin

section \<open>Side IP solver: constraint system construction and denotation\<close>

text \<open>
  Each equation right-hand side folds three contribution families: ordinary
  CFG edges, procedure-entry transfers, and return/combine transfers.  The
  accumulator joins their local results, while each strategy tree may emit
  side contributions to named global slots.

  A return/combine tree joins caller locals with callee-exit globals.  Its local
  result flows to the resume point, and its global result flows through side
  effects.
\<close>

subsection \<open>Effectful fold over contribution trees\<close>

text \<open>
  The generic fold composes a list of contribution trees with
  @{const seqcomp_tree}.  \<open>side_contribution_trees\<close> assembles the three
  source families in their executable order; both construction and denotation
  use that same list.
\<close>

fun fold_rhs_trees ::
  "'a::bounded_semilattice_sup_bot
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> ('k, 'g, 'a) strategy_tree"
where
  "fold_rhs_trees acc [] = Answer acc"
| "fold_rhs_trees acc (t # ts) =
     seqcomp_tree t (\<lambda>res. fold_rhs_trees (acc \<squnion> res) ts)"

subsection \<open>Buffered publication: fold Side-free contributions, publish once\<close>

text \<open>
  Voblint issue #121: a merge node folds several predecessor edge trees, and
  each edge historically published its own \<^const>\<open>Side\<close> as soon as it was
  evaluated (\<^const>\<open>unit_edge_tree\<close>). Because the vendored solver threads its
  global state \<open>\<sigma>\<close> synchronously through one RHS evaluation, later siblings
  can observe -- and, for the aggregate-gated warrowing update rule, spuriously
  destabilize on -- an earlier sibling's just-published, still mid-evaluation
  contribution. \<^const>\<open>fold_rhs_trees\<close> itself never calls \<^const>\<open>Side\<close>; only
  its elements do, so folding \<^emph>\<open>Side-free\<close> contribution trees (each
  answering the full unsplit local/global result instead of splitting and
  publishing it) and splitting \<^emph>\<open>once\<close> after the fold reproduces the
  identical declarative \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> value --
  \<open>buffered_matches_local\<close>/\<open>buffered_matches_global\<close> below -- while emitting
  exactly one \<^const>\<open>Side\<close> per RHS evaluation.
\<close>

lemma map_lift_restrict_local_for_join [simp]:
  "map_lift (restrict_local_for gs) (a \<squnion> b)
     = map_lift (restrict_local_for gs) a \<squnion> map_lift (restrict_local_for gs) b"
  by (cases a; cases b) simp_all

lemma map_lift_restrict_global_for_join [simp]:
  "map_lift (restrict_global_for gs) (a \<squnion> b)
     = map_lift (restrict_global_for gs) a \<squnion> map_lift (restrict_global_for gs) b"
  by (cases a; cases b) simp_all

definition publish_split_lifted ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('x,unit,'a::sound_domain abs_state lifted) strategy_tree
   \<Rightarrow> ('x,unit,'a abs_state lifted) strategy_tree" where
  "publish_split_lifted gs t = seqcomp_tree t
     (\<lambda>res. depend_on () (map_lift (restrict_global_for gs) res)
              (answer (map_lift (restrict_local_for gs) res)))"

lemma sides_of_rhs_fold_rhs_trees_bot:
  fixes cs :: "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree list"
  assumes "\<And>c \<sigma>. c \<in> set cs \<Longrightarrow> sides_of_rhs c \<sigma> = \<bottom>"
  shows "sides_of_rhs (fold_rhs_trees acc cs) \<sigma> = \<bottom>"
  using assms
proof (induction cs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  then show ?case by simp
qed

lemma buffered_matches_local:
  fixes cs :: "('x,unit,'a::sound_domain abs_state lifted) strategy_tree list"
  assumes side_free: "\<And>c. c \<in> set cs \<Longrightarrow> \<forall>\<sigma>. sides_of_rhs c \<sigma> = \<bottom>"
  shows "traverse_rhs (publish_split_lifted gs (fold_rhs_trees \<bottom> cs)) \<sigma>
       = map_lift (restrict_local_for gs) (traverse_rhs (fold_rhs_trees \<bottom> cs) \<sigma>)"
  unfolding publish_split_lifted_def by simp

lemma buffered_matches_global:
  fixes cs :: "('x,unit,'a::sound_domain abs_state lifted) strategy_tree list"
  assumes side_free: "\<And>c. c \<in> set cs \<Longrightarrow> \<forall>\<sigma>. sides_of_rhs c \<sigma> = \<bottom>"
  shows "sides_of_rhs (publish_split_lifted gs (fold_rhs_trees \<bottom> cs)) \<sigma> (Inr ())
       = map_lift (restrict_global_for gs) (traverse_rhs (fold_rhs_trees \<bottom> cs) \<sigma>)"
  unfolding publish_split_lifted_def
  using side_free
  by (simp add: sides_of_rhs_fold_rhs_trees_bot)

text \<open>
  \<open>traverse_fold_rhs_trees_char\<close> characterizes \<^const>\<open>fold_rhs_trees\<close>'s
  \<^const>\<open>traverse_rhs\<close> value as a fold over each list element's own,
  fixed-\<open>\<sigma>\<close> \<^const>\<open>traverse_rhs\<close> value -- used both by \<open>buffered_matches_*\<close>
  above and, via \<open>fold_rhs_trees_map_join_char\<close> below, to transport per-edge
  correspondence facts to a whole contribution-list fold for the buffering
  construction further down this theory.
\<close>

lemma foldr_sup_seed_swap:
  fixes h :: "'t \<Rightarrow> 'd::semilattice_sup"
  shows "foldr (\<lambda>t acc'. h t \<squnion> acc') ts (a \<squnion> b) = a \<squnion> foldr (\<lambda>t acc'. h t \<squnion> acc') ts b"
  by (induction ts) (simp_all add: ac_simps)

lemma traverse_fold_rhs_trees_char:
  "traverse_rhs (fold_rhs_trees acc ts) \<sigma>
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts acc"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "traverse_rhs (fold_rhs_trees acc (t # ts)) \<sigma>
          = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts (acc \<squnion> traverse_rhs t \<sigma>)"
    using Cons.IH by simp
  also have "\<dots> = traverse_rhs t \<sigma> \<squnion> foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') ts acc"
    by (simp add: sup_commute[of acc] foldr_sup_seed_swap)
  finally show ?case by simp
qed

lemma fold_rhs_trees_map_join_char:
  "traverse_rhs (fold_rhs_trees acc (map f xs)) \<sigma>
     = foldr (\<lambda>x acc'. traverse_rhs (f x) \<sigma> \<squnion> acc') xs acc"
proof (induction xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (simp add: sup_commute[of acc] foldr_sup_seed_swap)
qed

lemma sides_of_rhs_fold_rhs_trees_char:
  fixes ts :: "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree list"
  shows "sides_of_rhs (fold_rhs_trees acc ts) \<sigma> z
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> z \<squnion> acc') ts \<bottom>"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  then show ?case by simp
qed

lemma dep_aux_fold_rhs_trees_char:
  "dep_aux \<sigma> (fold_rhs_trees acc ts) = (\<Union>t\<in>set ts. dep_aux \<sigma> t)"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  then show ?case by simp
qed

definition side_contribution_trees ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> exp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a abs_state lifted) strategy_tree list"
where
  "side_contribution_trees etf es ens cs =
     map (\<lambda>(u, a). apply_etf etf a u) es @
     map (\<lambda>(cl, fs, as). etf_enter etf fs as cl) ens @
     map (\<lambda>(cc, dst, ex). etf_combine_collect etf dst cc ex) cs"

definition side_rhs_fold_eff ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state lifted
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> exp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list
   \<Rightarrow> (pp, 'g, 'a abs_state lifted) strategy_tree"
where
  "side_rhs_fold_eff etf acc es ens cs =
     fold_rhs_trees acc (side_contribution_trees etf es ens cs)"

lemma side_rhs_fold_eff_Nil [simp]:
  "side_rhs_fold_eff etf acc [] [] [] = Answer acc"
  by (simp add: side_rhs_fold_eff_def side_contribution_trees_def)

lemma side_rhs_fold_eff_edge [simp]:
  "side_rhs_fold_eff etf acc ((u, a) # es) ens cs =
   seqcomp_tree (apply_etf etf a u)
     (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) es ens cs)"
  by (simp add: side_rhs_fold_eff_def side_contribution_trees_def)

lemma side_rhs_fold_eff_entry [simp]:
  "side_rhs_fold_eff etf acc [] ((cl, fs, as) # ens) cs =
   seqcomp_tree (etf_enter etf fs as cl)
     (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) [] ens cs)"
  by (simp add: side_rhs_fold_eff_def side_contribution_trees_def)

lemma side_rhs_fold_eff_combine [simp]:
  "side_rhs_fold_eff etf acc [] [] ((cc, dst, ex) # cs) =
   seqcomp_tree (etf_combine_collect etf dst cc ex)
     (\<lambda>res. side_rhs_fold_eff etf (acc \<squnion> res) [] [] cs)"
  by (simp add: side_rhs_fold_eff_def side_contribution_trees_def)

lemmas side_rhs_fold_eff_simps =
  side_rhs_fold_eff_Nil side_rhs_fold_eff_edge
  side_rhs_fold_eff_entry side_rhs_fold_eff_combine

text \<open>The callee-entry seed list: each incoming call at callee entry \<open>v\<close> contributes its
  formals/actuals so the fold can invoke \<^const>\<open>etf_enter\<close> on the caller state.\<close>
definition entry_seed_list :: "cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> vname list \<times> exp list) list" where
  "entry_seed_list g v =
     map (\<lambda>(c, ca). case ca of CallEdge dst fs as \<Rightarrow> (c, fs, as)) (entry_call_list g v)"

text \<open>
  The fold seed is the lifted bottom, not a lifted domain value: a program
  point with no live predecessor contribution is unreachable, not reachable
  at the domain's bottom -- \<^const>\<open>Bot\<close> is \<open>fold_rhs_trees\<close>' join identity, so
  it never forces reachability the way embedding a genuine domain seed \<open>bot0\<close>
  as \<open>Lifted bot0\<close> would. Only the entry point starts genuinely reachable,
  seeded at the initial store.
\<close>

definition make_side_rhs_tree_eff ::
  "(vname => bool) \<Rightarrow> cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a abs_state lifted) strategy_tree"
where
  "make_side_rhs_tree_eff gs g etf bot0 s0 gseed v =
     (let acc0 = (if v = cfg_entry g then Lifted (bot0 \<squnion> restrict_local_for gs s0) else Bot);
          t    = side_rhs_fold_eff etf acc0
                   (intra_predecessor_list g v) (entry_seed_list g v)
                   (return_call_list g v)
      in if v = cfg_entry g then depend_on gseed (Lifted (restrict_global_for gs s0)) t else t)"

definition side_cfg_T_eff ::
  "(vname => bool) \<Rightarrow> cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g
   \<Rightarrow> (pp, 'g, 'a abs_state lifted) eqsT"
where
  "side_cfg_T_eff gs g etf bot0 s0 gseed = make_side_rhs_tree_eff gs g etf bot0 s0 gseed"

subsection \<open>Buffered generator: fold Side-free contributions, publish once (issue #121)\<close>

text \<open>
  \<open>make_side_rhs_tree_eff_buffered\<close> mirrors \<^const>\<open>make_side_rhs_tree_eff\<close>
  exactly, but (a) seeds the entry accumulator \<^emph>\<open>unsplit\<close> (\<open>Lifted (bot0 \<squnion>
  s0)\<close>, not \<^const>\<open>restrict_local_for\<close>-restricted) and (b) wraps the whole
  fold -- at every node, not only the entry -- with a single trailing split
  (\<open>depend_on gseed ... (answer ...)\<close>) instead of relying on each
  \<open>etf\<close>-supplied tree to publish its own \<^const>\<open>Side\<close>. This is sound
  \<^emph>\<open>only\<close> when \<open>etf\<close>'s own \<open>apply_etf\<close>/\<open>etf_enter\<close>/\<open>etf_combine_collect\<close> trees are
  themselves Side-free and unsplit (e.g. built from \<open>unit_edge_contribution\<close>
  rather than \<^const>\<open>unit_edge_tree\<close>) -- \<open>side_contribution_trees\<close> is reused
  unchanged, since it is agnostic to which kind of tree \<open>etf\<close> supplies.
\<close>

text \<open>
  \<open>side_publish\<close> is \<^const>\<open>depend_on\<close> in statement position: publish \<open>val\<close>
  under \<open>key\<close> and continue with the trivial local answer. It lets the fold's
  result flow through one \<open>do\<close>-block -- compute, publish the global
  projection, return the local projection -- instead of exposing the
  \<open>seqcomp_tree\<close>/\<open>depend_on\<close> continuation-passing shape at the call site.
\<close>

abbreviation side_publish ::
  "'g \<Rightarrow> 'd::bot \<Rightarrow> ('x, 'g, 'd) strategy_tree"
where
  "side_publish key val \<equiv> depend_on key val (answer bot)"

definition make_side_rhs_tree_eff_buffered ::
  "(vname => bool) \<Rightarrow> cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'a abs_state lifted) strategy_tree"
where
  "make_side_rhs_tree_eff_buffered gs g etf bot0 s0 gseed v =
     (let acc0 = (if v = cfg_entry g then Lifted (bot0 \<squnion> s0) else Bot);
          t    = fold_rhs_trees acc0
                   (side_contribution_trees etf
                      (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))
      in do {
        res \<leftarrow> t;
        side_publish gseed (map_lift (restrict_global_for gs) res);
        answer (map_lift (restrict_local_for gs) res)
      })"

definition side_cfg_T_eff_buffered ::
  "(vname => bool) \<Rightarrow> cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g
   \<Rightarrow> (pp, 'g, 'a abs_state lifted) eqsT"
where
  "side_cfg_T_eff_buffered gs g etf bot0 s0 gseed = make_side_rhs_tree_eff_buffered gs g etf bot0 s0 gseed"

text \<open>
  Correspondence theorem: given per-tree hypotheses relating an
  \<open>etf_old\<close> (each of whose \<open>apply_etf\<close>/\<open>etf_enter\<close>/\<open>etf_combine_collect\<close> trees
  splits and publishes its own unsplit result, e.g. via
  \<^const>\<open>unit_edge_tree\<close>) to an \<open>etf_new\<close> (the corresponding Side-free,
  unsplit counterpart, e.g. \<open>unit_edge_contribution\<close>) -- exactly the four
  facts already proved per-edge for Interval's \<open>unit_edge_tree\<close>/
  \<open>unit_edge_contribution\<close> pair -- the buffered generator over \<open>etf_new\<close>
  has the identical \<^const>\<open>traverse_rhs\<close>/\<^const>\<open>sides_of_rhs\<close> value as the
  original generator over \<open>etf_old\<close>, at \<open>bot0 = bot\<close> (every current call
  site's actual argument). Specialized to \<open>'g = unit\<close>, matching every
  current \<open>side_cfg_T_eff\<close> caller.
\<close>

lemma make_side_rhs_tree_eff_buffered_correspondence:
  fixes etf_old etf_new :: "(unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer"
  assumes edge_t: "\<And>a u \<sigma>. traverse_rhs (apply_etf etf_old a u) \<sigma>
                    = map_lift (restrict_local_for gs) (traverse_rhs (apply_etf etf_new a u) \<sigma>)"
    and edge_s: "\<And>a u \<sigma>. sides_of_rhs (apply_etf etf_old a u) \<sigma> (Inr ())
                    = map_lift (restrict_global_for gs) (traverse_rhs (apply_etf etf_new a u) \<sigma>)"
    and edge_free: "\<And>a u \<sigma>. sides_of_rhs (apply_etf etf_new a u) \<sigma> = \<bottom>"
    and enter_t: "\<And>fs as cl \<sigma>. traverse_rhs (etf_enter etf_old fs as cl) \<sigma>
                    = map_lift (restrict_local_for gs) (traverse_rhs (etf_enter etf_new fs as cl) \<sigma>)"
    and enter_s: "\<And>fs as cl \<sigma>. sides_of_rhs (etf_enter etf_old fs as cl) \<sigma> (Inr ())
                    = map_lift (restrict_global_for gs) (traverse_rhs (etf_enter etf_new fs as cl) \<sigma>)"
    and enter_free: "\<And>fs as cl \<sigma>. sides_of_rhs (etf_enter etf_new fs as cl) \<sigma> = \<bottom>"
    and comb_t: "\<And>dst cc ex \<sigma>. traverse_rhs (etf_combine_collect etf_old dst cc ex) \<sigma>
                    = map_lift (restrict_local_for gs) (traverse_rhs (etf_combine_collect etf_new dst cc ex) \<sigma>)"
    and comb_s: "\<And>dst cc ex \<sigma>. sides_of_rhs (etf_combine_collect etf_old dst cc ex) \<sigma> (Inr ())
                    = map_lift (restrict_global_for gs) (traverse_rhs (etf_combine_collect etf_new dst cc ex) \<sigma>)"
    and comb_free: "\<And>dst cc ex \<sigma>. sides_of_rhs (etf_combine_collect etf_new dst cc ex) \<sigma> = \<bottom>"
  shows "traverse_rhs (make_side_rhs_tree_eff_buffered gs g etf_new bot s0 () v) \<sigma>
          = traverse_rhs (make_side_rhs_tree_eff gs g etf_old bot s0 () v) \<sigma>"
    (is ?T)
    and "sides_of_rhs (make_side_rhs_tree_eff_buffered gs g etf_new bot s0 () v) \<sigma> (Inr ())
          = sides_of_rhs (make_side_rhs_tree_eff gs g etf_old bot s0 () v) \<sigma> (Inr ())"
    (is ?S)
proof -
  define cs :: "(pp, unit, 'a abs_state lifted) strategy_tree list"
    where "cs = side_contribution_trees etf_new
                  (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)"
  have cs_old_eq: "side_contribution_trees etf_old
                     (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)
                 = map (\<lambda>(u,a). apply_etf etf_old a u) (intra_predecessor_list g v)
                   @ map (\<lambda>(cl,fs,as). etf_enter etf_old fs as cl) (entry_seed_list g v)
                   @ map (\<lambda>(cc,dst,ex). etf_combine_collect etf_old dst cc ex) (return_call_list g v)"
    unfolding side_contribution_trees_def by simp
  have cs_new_eq: "cs = map (\<lambda>(u,a). apply_etf etf_new a u) (intra_predecessor_list g v)
                   @ map (\<lambda>(cl,fs,as). etf_enter etf_new fs as cl) (entry_seed_list g v)
                   @ map (\<lambda>(cc,dst,ex). etf_combine_collect etf_new dst cc ex) (return_call_list g v)"
    unfolding cs_def side_contribution_trees_def by simp
  have free: "\<And>c \<sigma>'. c \<in> set cs \<Longrightarrow> sides_of_rhs c \<sigma>' = \<bottom>"
    unfolding cs_new_eq using edge_free enter_free comb_free by (auto split: prod.splits)
  let ?acc0new = "if v = cfg_entry g then Lifted (bot \<squnion> s0) else Bot"
  have acc0_split: "map_lift (restrict_local_for gs) ?acc0new = (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_for gs s0) else Bot)"
    by (cases "v = cfg_entry g") (simp_all add: restrict_local_for_join)
  have tvT: "traverse_rhs (fold_rhs_trees ?acc0new cs) \<sigma>
       = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs ?acc0new"
    by (rule traverse_fold_rhs_trees_char)
  have seed_swap: "foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs ?acc0new
       = ?acc0new \<squnion> foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs \<bottom>"
    using foldr_sup_seed_swap[of _ _ "?acc0new" \<bottom>] by fastforce
  have map_join_local: "map_lift (restrict_local_for gs)
        (foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs \<bottom>)
     = foldr (\<lambda>t acc'. map_lift (restrict_local_for gs) (traverse_rhs t \<sigma>) \<squnion> acc') cs \<bottom>"
    by (induction cs) simp_all
  have map_join_global: "map_lift (restrict_global_for gs)
        (foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs \<bottom>)
     = foldr (\<lambda>t acc'. map_lift (restrict_global_for gs) (traverse_rhs t \<sigma>) \<squnion> acc') cs \<bottom>"
    by (induction cs) simp_all
  have edge_seg_t:
    "foldr (\<lambda>t acc'. map_lift (restrict_local_for gs) (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(u,a). apply_etf etf_new a u) xs) seed
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') (map (\<lambda>(u,a). apply_etf etf_old a u) xs) seed"
    for xs :: "(pp \<times> edge_action) list" and seed
    by (induction xs arbitrary: seed) (auto simp: edge_t split: prod.splits)
  have enter_seg_t:
    "foldr (\<lambda>t acc'. map_lift (restrict_local_for gs) (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(cl,fs,as). etf_enter etf_new fs as cl) xs) seed
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') (map (\<lambda>(cl,fs,as). etf_enter etf_old fs as cl) xs) seed"
    for xs :: "(pp \<times> vname list \<times> exp list) list" and seed
    by (induction xs arbitrary: seed) (auto simp: enter_t split: prod.splits)
  have comb_seg_t:
    "foldr (\<lambda>t acc'. map_lift (restrict_local_for gs) (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(cc,dst,ex). etf_combine_collect etf_new dst cc ex) xs) seed
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') (map (\<lambda>(cc,dst,ex). etf_combine_collect etf_old dst cc ex) xs) seed"
    for xs :: "(pp \<times> vname option \<times> pp) list" and seed
    by (induction xs arbitrary: seed) (auto simp: comb_t split: prod.splits)
  have elem_local: "foldr (\<lambda>t acc'. map_lift (restrict_local_for gs) (traverse_rhs t \<sigma>) \<squnion> acc') cs \<bottom>
       = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc')
           (side_contribution_trees etf_old
              (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    unfolding cs_new_eq cs_old_eq foldr_append edge_seg_t enter_seg_t comb_seg_t by (rule refl)
  have edge_seg_s:
    "foldr (\<lambda>t acc'. map_lift (restrict_global_for gs) (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(u,a). apply_etf etf_new a u) xs) seed
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc') (map (\<lambda>(u,a). apply_etf etf_old a u) xs) seed"
    for xs :: "(pp \<times> edge_action) list" and seed
    by (induction xs arbitrary: seed) (auto simp: edge_s split: prod.splits)
  have enter_seg_s:
    "foldr (\<lambda>t acc'. map_lift (restrict_global_for gs) (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(cl,fs,as). etf_enter etf_new fs as cl) xs) seed
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc') (map (\<lambda>(cl,fs,as). etf_enter etf_old fs as cl) xs) seed"
    for xs :: "(pp \<times> vname list \<times> exp list) list" and seed
    by (induction xs arbitrary: seed) (auto simp: enter_s split: prod.splits)
  have comb_seg_s:
    "foldr (\<lambda>t acc'. map_lift (restrict_global_for gs) (traverse_rhs t \<sigma>) \<squnion> acc')
       (map (\<lambda>(cc,dst,ex). etf_combine_collect etf_new dst cc ex) xs) seed
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc') (map (\<lambda>(cc,dst,ex). etf_combine_collect etf_old dst cc ex) xs) seed"
    for xs :: "(pp \<times> vname option \<times> pp) list" and seed
    by (induction xs arbitrary: seed) (auto simp: comb_s split: prod.splits)
  have elem_global: "foldr (\<lambda>t acc'. map_lift (restrict_global_for gs) (traverse_rhs t \<sigma>) \<squnion> acc') cs \<bottom>
       = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc')
           (side_contribution_trees etf_old
              (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    unfolding cs_new_eq cs_old_eq foldr_append edge_seg_s enter_seg_s comb_seg_s by (rule refl)
  have told_sides_char: "sides_of_rhs
        (fold_rhs_trees \<bottom> (side_contribution_trees etf_old
              (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))) \<sigma> (Inr ())
     = foldr (\<lambda>t acc'. sides_of_rhs t \<sigma> (Inr ()) \<squnion> acc')
         (side_contribution_trees etf_old
            (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    by (rule sides_of_rhs_fold_rhs_trees_char)
  have told_traverse_char: "traverse_rhs
        (fold_rhs_trees \<bottom> (side_contribution_trees etf_old
              (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))) \<sigma>
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc')
         (side_contribution_trees etf_old
            (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    by (rule traverse_fold_rhs_trees_char)
  define t_old where "t_old = side_rhs_fold_eff etf_old
        (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_for gs s0) else Bot)
        (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)"
  have t_old_sides_indep: "sides_of_rhs t_old \<sigma> (Inr ())
     = sides_of_rhs
         (fold_rhs_trees \<bottom> (side_contribution_trees etf_old
            (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))) \<sigma> (Inr ())"
    unfolding t_old_def side_rhs_fold_eff_def sides_of_rhs_fold_rhs_trees_char
    by simp
  have t_old_traverse: "traverse_rhs t_old \<sigma>
     = foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc')
         (side_contribution_trees etf_old
            (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v))
         (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_for gs s0) else Bot)"
    unfolding t_old_def side_rhs_fold_eff_def traverse_fold_rhs_trees_char by simp
  have buffered_traverse: "traverse_rhs (make_side_rhs_tree_eff_buffered gs g etf_new bot s0 () v) \<sigma>
       = map_lift (restrict_local_for gs) (foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs ?acc0new)"
    unfolding make_side_rhs_tree_eff_buffered_def Let_def cs_def[symmetric]
    by (simp add: traverse_seqcomp tvT)
  have buffered_sides: "sides_of_rhs (make_side_rhs_tree_eff_buffered gs g etf_new bot s0 () v) \<sigma> (Inr ())
       = map_lift (restrict_global_for gs) (foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc') cs ?acc0new)"
    unfolding make_side_rhs_tree_eff_buffered_def Let_def cs_def[symmetric]
    by (simp add: sides_of_rhs_seqcomp_at sides_of_rhs_fold_rhs_trees_bot[OF free] tvT)
  have old_traverse: "traverse_rhs (make_side_rhs_tree_eff gs g etf_old bot s0 () v) \<sigma>
       = traverse_rhs t_old \<sigma>"
    unfolding make_side_rhs_tree_eff_def Let_def t_old_def side_rhs_fold_eff_def
    by (simp add: traverse_seqcomp)
  have old_sides: "sides_of_rhs (make_side_rhs_tree_eff gs g etf_old bot s0 () v) \<sigma> (Inr ())
       = (if v = cfg_entry g then Lifted (restrict_global_for gs s0) else Bot)
         \<squnion> sides_of_rhs t_old \<sigma> (Inr ())"
    unfolding make_side_rhs_tree_eff_def Let_def t_old_def side_rhs_fold_eff_def
    by (smt (verit) all_sides.simps(4) all_sides_eq_sides_Inr_unit
        bot_lifted_def sup_bot.left_neutral)
  have restrict_local_acc0: "map_lift (restrict_local_for gs) ?acc0new
       = (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_for gs s0) else Bot)"
    by (rule acc0_split)
  have restrict_global_acc0: "map_lift (restrict_global_for gs) ?acc0new
       = (if v = cfg_entry g then Lifted (restrict_global_for gs s0) else Bot)"
    by (cases "v = cfg_entry g") (simp_all add: restrict_global_for_join)
  have t_old_traverse_seed_swap: "traverse_rhs t_old \<sigma>
       = (if v = cfg_entry g then Lifted (bot \<squnion> restrict_local_for gs s0) else Bot)
         \<squnion> foldr (\<lambda>t acc'. traverse_rhs t \<sigma> \<squnion> acc')
             (side_contribution_trees etf_old
                (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)) \<bottom>"
    unfolding t_old_traverse
    using foldr_sup_seed_swap[of "\<lambda>t. traverse_rhs t \<sigma>"
            "side_contribution_trees etf_old
               (intra_predecessor_list g (cfg_entry g)) (entry_seed_list g (cfg_entry g))
               (return_call_list g (cfg_entry g))"
            "Lifted (bot \<squnion> restrict_local_for gs s0)" "\<bottom>"]
    by simp
  have T: ?T
    unfolding buffered_traverse old_traverse seed_swap
    using elem_local map_join_local t_old_traverse_seed_swap by auto
   have S: ?S
    unfolding buffered_sides old_sides seed_swap
    using elem_global map_join_global t_old_sides_indep told_sides_char
    by auto
  from T S show ?T ?S by simp_all
qed

fun fold_rhs_values ::
  "'a::bounded_semilattice_sup_bot
   \<Rightarrow> ('k + 'g \<Rightarrow> 'a)
   \<Rightarrow> ('k, 'g, 'a) strategy_tree list
   \<Rightarrow> 'a"
where
  "fold_rhs_values acc \<sigma> [] = acc"
| "fold_rhs_values acc \<sigma> (t # ts) =
     fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts"

definition side_acc_eff ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state lifted
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state lifted)
   \<Rightarrow> (pp \<times> edge_action) list
   \<Rightarrow> (pp \<times> vname list \<times> exp list) list
   \<Rightarrow> (pp \<times> vname option \<times> pp) list \<Rightarrow> 'a abs_state lifted"
where
  "side_acc_eff etf acc \<sigma> es ens cs =
     fold_rhs_values acc \<sigma> (side_contribution_trees etf es ens cs)"

lemma side_acc_eff_Nil [simp]:
  "side_acc_eff etf acc \<sigma> [] [] [] = acc"
  by (simp add: side_acc_eff_def side_contribution_trees_def)

lemma side_acc_eff_edge [simp]:
  "side_acc_eff etf acc \<sigma> ((u, a) # es) ens cs =
   side_acc_eff etf (acc \<squnion> traverse_rhs (apply_etf etf a u) \<sigma>) \<sigma> es ens cs"
  by (simp add: side_acc_eff_def side_contribution_trees_def)

lemma side_acc_eff_entry [simp]:
  "side_acc_eff etf acc \<sigma> [] ((cl, fs, as) # ens) cs =
   side_acc_eff etf (acc \<squnion> traverse_rhs (etf_enter etf fs as cl) \<sigma>) \<sigma> [] ens cs"
  by (simp add: side_acc_eff_def side_contribution_trees_def)

lemma side_acc_eff_combine [simp]:
  "side_acc_eff etf acc \<sigma> [] [] ((cc, dst, ex) # cs) =
   side_acc_eff etf
     (acc \<squnion> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma>) \<sigma> [] [] cs"
  by (simp add: side_acc_eff_def side_contribution_trees_def)

lemma traverse_fold_rhs_trees:
  "traverse_rhs (fold_rhs_trees acc ts) \<sigma> = fold_rhs_values acc \<sigma> ts"
  by (induction ts arbitrary: acc) (simp_all add: traverse_seqcomp)

lemma traverse_side_rhs_fold_eff:
  "traverse_rhs (side_rhs_fold_eff etf acc es ens cs) \<sigma> =
   side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_rhs_fold_eff_def side_acc_eff_def
  by (rule traverse_fold_rhs_trees)

lemma eq_side_cfg_T_eff:
  "eq (side_cfg_T_eff gs g etf bot0 s0 gseed) v \<sigma> =
     side_acc_eff etf
       (if v = cfg_entry g then Lifted (bot0 \<squnion> restrict_local_for gs s0) else Bot)
       \<sigma> (intra_predecessor_list g v) (entry_seed_list g v) (return_call_list g v)"
  unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
  by (simp add: traverse_side_rhs_fold_eff Let_def)


subsection \<open>Per-edge contributions and their folded join\<close>

text \<open>
  Each incoming CFG edge contributes the transfer of its source unknown to the
  target equation.  The transfer depends on the source point and edge action;
  the target point selects the equation that receives the contribution.
  \<open>edge_constraint_tree\<close> exposes this contribution as a strategy tree.
\<close>

definition edge_constraint_tree ::
  "('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp, 'g, 'a abs_state lifted) strategy_tree"
where
  "edge_constraint_tree etf u a v = apply_etf etf a u"

lemma traverse_edge_constraint_tree:
  "traverse_rhs (edge_constraint_tree etf u a v) \<sigma>
   = traverse_rhs (apply_etf etf a u) \<sigma>"
  by (simp add: edge_constraint_tree_def)

text \<open>
  The folded accumulator is the least upper bound of the seed and every
  contribution tree.  The contribution lemmas expose each source family, while
  \<open>side_acc_eff_least\<close> proves that any common upper bound dominates the
  complete fold.
\<close>

lemma acc_le_fold_rhs_values:
  "acc \<le> fold_rhs_values acc \<sigma> ts"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "acc \<le> acc \<squnion> traverse_rhs t \<sigma>" by (rule sup_ge1)
  also have "... \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts"
    by (rule Cons.IH)
  finally show ?case by simp
qed

lemma fold_rhs_values_member:
  assumes "t \<in> set ts"
  shows "traverse_rhs t \<sigma> \<le> fold_rhs_values acc \<sigma> ts"
  using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons u ts)
  show ?case
  proof (cases "t = u")
    case True
    have "traverse_rhs t \<sigma> \<le> acc \<squnion> traverse_rhs t \<sigma>" by (rule sup_ge2)
    also have "... \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts"
      by (rule acc_le_fold_rhs_values)
    finally show ?thesis using True by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then show ?thesis using Cons.IH by simp
  qed
qed

lemma fold_rhs_values_least:
  assumes "acc \<le> b"
    and "\<And>t. t \<in> set ts \<Longrightarrow> traverse_rhs t \<sigma> \<le> b"
  shows "fold_rhs_values acc \<sigma> ts \<le> b"
  using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have step: "acc \<squnion> traverse_rhs t \<sigma> \<le> b"
    using Cons.prems by simp
  have rest: "\<And>u. u \<in> set ts \<Longrightarrow> traverse_rhs u \<sigma> \<le> b"
    using Cons.prems(2) by simp
  show ?case by (simp add: Cons.IH[OF step rest])
qed

lemma acc_le_side_acc_eff:
  "acc \<le> side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_acc_eff_def
  by (rule acc_le_fold_rhs_values)

lemma side_acc_eff_edge_contributes:
  assumes "(u, a) \<in> set es"
  shows "traverse_rhs (apply_etf etf a u) \<sigma> \<le> side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_member)
  unfolding side_contribution_trees_def
  using assms by force

lemma side_acc_eff_enter_contributes:
  assumes "(cl, fs, as) \<in> set ens"
  shows "traverse_rhs (etf_enter etf fs as cl) \<sigma> \<le> side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_member)
  unfolding side_contribution_trees_def
  using assms by force

lemma side_acc_eff_combine_contributes:
  assumes "(cc, dst, ex) \<in> set cs"
  shows "traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> es ens cs"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_member)
  unfolding side_contribution_trees_def
  using assms by force

lemma side_acc_eff_nil_enter_contributes:
  assumes "(cl, fs, as) \<in> set ens"
  shows "traverse_rhs (etf_enter etf fs as cl) \<sigma> \<le> side_acc_eff etf acc \<sigma> [] ens cs"
  by (rule side_acc_eff_enter_contributes[OF assms])

lemma side_acc_eff_nil_nil_combine_contributes:
  assumes "(cc, dst, ex) \<in> set cs"
  shows "traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> [] [] cs"
  by (rule side_acc_eff_combine_contributes[OF assms])

lemma side_acc_eff_nil_combine_contributes:
  assumes "(cc, dst, ex) \<in> set cs"
  shows "traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma> \<le> side_acc_eff etf acc \<sigma> [] ens cs"
  by (rule side_acc_eff_combine_contributes[OF assms])

lemma side_acc_eff_least:
  assumes "acc \<le> b"
    and "\<And>u a. (u, a) \<in> set es \<Longrightarrow> traverse_rhs (apply_etf etf a u) \<sigma> \<le> b"
    and "\<And>c fs as. (c, fs, as) \<in> set ens \<Longrightarrow> traverse_rhs (etf_enter etf fs as c) \<sigma> \<le> b"
    and "\<And>cc ex dst. (cc, dst, ex) \<in> set cs \<Longrightarrow> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma> \<le> b"
  shows "side_acc_eff etf acc \<sigma> es ens cs \<le> b"
  unfolding side_acc_eff_def
  apply (rule fold_rhs_values_least[OF assms(1)])
  unfolding side_contribution_trees_def
  using assms(2-4)
  by (auto split: prod.splits)

lemma side_acc_eff_nil_nil_least:
  assumes "acc \<le> b"
    and "\<And>cc dst ex. (cc, dst, ex) \<in> set cs \<Longrightarrow> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma> \<le> b"
  shows "side_acc_eff etf acc \<sigma> [] [] cs \<le> b"
  by (rule side_acc_eff_least[OF assms(1)]) (auto intro: assms(2))

lemma side_acc_eff_nil_least:
  assumes "acc \<le> b"
    and "\<And>c fs as. (c, fs, as) \<in> set ens \<Longrightarrow> traverse_rhs (etf_enter etf fs as c) \<sigma> \<le> b"
    and "\<And>cc ex dst. (cc, dst, ex) \<in> set cs \<Longrightarrow> traverse_rhs (etf_combine_collect etf dst cc ex) \<sigma> \<le> b"
  shows "side_acc_eff etf acc \<sigma> [] ens cs \<le> b"
  by (rule side_acc_eff_least[OF assms(1)]) (auto intro: assms(2-3))

subsection \<open>Contribution bounds at the interprocedural CFG\<close>

text \<open>
  Every incoming ordinary edge, procedure-entry transfer, and return/combine
  transfer contributes to its target equation.  The entry equation additionally
  covers the initial local state and publishes the initial global state through
  the distinguished global seed.
\<close>

lemma cfg_edge_contributes_to_eq:
  fixes g :: cfg
  assumes "finite (intra g)" and "(u, a, v) \<in> intra g"
  shows "traverse_rhs (edge_constraint_tree etf u a v) \<sigma>
         \<le> eq (side_cfg_T_eff gs g etf bot0 s0 gseed) v \<sigma>"
proof -
  have "(u, a) \<in> set (intra_predecessor_list g v)"
    using assms by (simp add: intra_predecessors_def)
  then show ?thesis
    unfolding traverse_edge_constraint_tree eq_side_cfg_T_eff
    by (rule side_acc_eff_edge_contributes)
qed

lemma cfg_enter_contributes_to_eq:
  fixes g :: cfg
  assumes "finite (calls g)" and "(cl, CallEdge dst fs as, v, k) \<in> calls g"
  shows "traverse_rhs (etf_enter etf fs as cl) \<sigma>
         \<le> eq (side_cfg_T_eff gs g etf bot0 s0 gseed) v \<sigma>"
proof -
  have "(cl, fs, as) \<in> set (entry_seed_list g v)"
    using assms
    by (force simp: entry_seed_list_def entry_calls_def image_iff)
  then show ?thesis
    unfolding eq_side_cfg_T_eff
    by (rule side_acc_eff_enter_contributes)
qed

lemma cfg_combine_contributes_to_eq:
  fixes g :: cfg
  assumes "finite (calls g)" and "(cc, CallEdge dst fs as, FunctionEntry p, v) \<in> calls g"
  shows "traverse_rhs (etf_combine_collect etf dst cc (FunctionResult p)) \<sigma>
         \<le> eq (side_cfg_T_eff gs g etf bot0 s0 gseed) v \<sigma>"
proof -
  have "(cc, dst, FunctionResult p) \<in> set (return_call_list g v)"
    using assms(2) by (force simp: set_return_call_list[OF assms(1)] return_calls_def)
  then show ?thesis
    unfolding eq_side_cfg_T_eff
    by (rule side_acc_eff_combine_contributes)
qed

lemma entry_local_seed_le_eq:
  fixes g :: cfg
  shows "Lifted (restrict_local_for gs s0)
           \<le> eq (side_cfg_T_eff gs g etf bot0 s0 gseed) (cfg_entry g) \<sigma>"
proof -
  have "Lifted (restrict_local_for gs s0) \<le> Lifted (bot0 \<squnion> restrict_local_for gs s0)"
    by (simp add: sup_ge2)
  also have "\<dots> \<le> side_acc_eff etf (Lifted (bot0 \<squnion> restrict_local_for gs s0)) \<sigma>
                    (intra_predecessor_list g (cfg_entry g))
                    (entry_seed_list g (cfg_entry g))
                    (return_call_list g (cfg_entry g))"
    by (rule acc_le_side_acc_eff)
  finally show ?thesis unfolding eq_side_cfg_T_eff by simp
qed

lemma entry_global_seed_le_sides:
  "Lifted (restrict_global_for gs s0)
   \<le> sides_of_rhs (side_cfg_T_eff gs g etf bot0 s0 gseed (cfg_entry g)) \<sigma> (Inr gseed)"
  unfolding side_cfg_T_eff_def make_side_rhs_tree_eff_def
  by (simp add: Let_def)

subsection \<open>Relabelling local unknowns for context indexing\<close>

text \<open>
  Context-sensitivity reindexes the local unknown \<open>pp\<close> to \<open>pp \<times> 'c\<close>.  A
  per-edge tree \<open>apply_etf etf a u\<close> queries only the single predecessor \<open>u\<close>, and a
  combine tree \<open>etf_combine_collect etf dst cc ex\<close> queries the caller \<open>cc\<close> and the callee exit
  \<open>ex\<close>; so the context routing of either is captured by a position-aware
  relabelling \<open>h :: pp \<Rightarrow> pp \<times> 'c\<close> of the \<open>QueryL\<close> targets (intra: \<open>u \<mapsto> (u, c)\<close>;
  combine: caller \<open>\<mapsto> (cc, c)\<close>, callee \<open>\<mapsto> (ex, c')\<close>).  \<open>map_ltree\<close> performs that
  relabelling; \<open>traverse_rhs_map_ltree\<close> shows it commutes with the denotation under
  the matching \<open>map_sum\<close>-pullback of the unknown environment, so a context-indexed
  equation system's denotation is the original one read against the relabelled
  environment.  Globals (\<open>QueryG\<close> / \<open>Side\<close>) are untouched.
\<close>

primrec map_ltree ::
  "('x \<Rightarrow> 'y) \<Rightarrow> ('x, 'g, 'd) strategy_tree \<Rightarrow> ('y, 'g, 'd) strategy_tree" where
  "map_ltree h (Answer d) = Answer d"
| "map_ltree h (QueryL y f) = QueryL (h y) (\<lambda>d. map_ltree h (f d))"
| "map_ltree h (QueryG y f) = QueryG y (\<lambda>d. map_ltree h (f d))"
| "map_ltree h (Side y d t) = Side y d (map_ltree h t)"

lemma traverse_rhs_map_ltree:
  "traverse_rhs (map_ltree h t) \<sigma> = traverse_rhs t (\<lambda>z. \<sigma> (map_sum h id z))"
  by (induction t) auto



subsection \<open>General context-indexed equation system\<close>

text \<open>
  The equation for \<open>(v, c)\<close> statically relabels ordinary-edge and entry trees to
  context \<open>c\<close>.  Return/combine trees come from the supplied builder \<open>cmb\<close>, which
  may route the callee-exit query through a context computed from the caller state.
  Keeping \<open>cmb\<close> explicit separates context routing from the domain transfer record.
\<close>


definition side_cfg_T_eff_ctx ::
  "(vname => bool)
   \<Rightarrow> ('c \<Rightarrow> vname option \<Rightarrow> pp \<Rightarrow> pp
     \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state lifted) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> ('g, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'g
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state lifted) eqsT"
where
  "side_cfg_T_eff_ctx gs cmb g etf bot0 s0 gseed =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then Lifted (bot0 \<squnion> restrict_local_for gs s0) else Bot);
            intra = map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u))
                        (intra_predecessor_list g v);
            enter = map (\<lambda>(cl, fs, as). map_ltree (\<lambda>w. (w, c)) (etf_enter etf fs as cl))
                        (entry_seed_list g v);
            comb  = map (\<lambda>(cc, dst, ex). cmb c dst cc ex) (return_call_list g v);
            t = fold_rhs_trees acc0 (intra @ enter @ comb)
        in if v = cfg_entry g then depend_on gseed (Lifted (restrict_global_for gs s0)) t else t)"


text \<open>
  Denotation of the context-indexed equation system at \<open>(v, c)\<close>, mirroring
  \<open>eq_side_cfg_T_eff\<close>: the entry \<open>Side\<close> wrapper is denotation-transparent, so the
  value of the unknown is the \<open>fold_rhs_values\<close> fold over the intra (relabelled) and
  combine (instance \<open>cmb\<close>) trees.  This is the form the soundness chain reads.
\<close>

lemma eq_side_cfg_T_eff_ctx:
  "eq (side_cfg_T_eff_ctx gs cmb g etf bot0 s0 gseed) (v, ctx) \<sigma> =
     fold_rhs_values
       (if v = cfg_entry g then Lifted (bot0 \<squnion> restrict_local_for gs s0) else Bot) \<sigma>
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
            (intra_predecessor_list g v)
        @ map (\<lambda>(cl, fs, as). map_ltree (\<lambda>w. (w, ctx)) (etf_enter etf fs as cl))
            (entry_seed_list g v)
        @ map (\<lambda>(cc, dst, ex). cmb ctx dst cc ex) (return_call_list g v))"
  unfolding side_cfg_T_eff_ctx_def
  by (simp add: traverse_fold_rhs_trees Let_def)


subsection \<open>Bounds on the context fold\<close>

text \<open>
  The seed and every contributing tree lie below the context fold.  Monotonicity
  follows separately in the seed and in the unknown environment.  The uniform
  tree list makes these properties independent of the contribution source.
\<close>

lemma fold_rhs_values_mono_seed:
  fixes acc1 acc2 :: "'a::bounded_semilattice_sup_bot"
  shows "acc1 \<le> acc2 \<Longrightarrow> fold_rhs_values acc1 \<sigma> ts \<le> fold_rhs_values acc2 \<sigma> ts"
proof (induction ts arbitrary: acc1 acc2)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using Cons.IH[OF sup_mono[OF Cons.prems order_refl]] by (simp add: sup_fun_def)
qed

lemma fold_rhs_values_ge_acc:
  fixes acc :: "'a::bounded_semilattice_sup_bot"
  shows "acc \<le> fold_rhs_values acc \<sigma> ts"
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have "acc \<le> acc \<squnion> traverse_rhs t \<sigma>" by simp
  also have "\<dots> \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>) \<sigma> ts" by (rule Cons.IH)
  finally show ?case by simp
qed

lemma traverse_le_fold_rhs_values:
  fixes acc :: "'a::bounded_semilattice_sup_bot"
  shows "t \<in> set ts \<Longrightarrow> traverse_rhs t \<sigma> \<le> fold_rhs_values acc \<sigma> ts"
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t' ts)
  show ?case
  proof (cases "t = t'")
    case True
    have "traverse_rhs t \<sigma> \<le> acc \<squnion> traverse_rhs t' \<sigma>" using True by simp
    also have "\<dots> \<le> fold_rhs_values (acc \<squnion> traverse_rhs t' \<sigma>) \<sigma> ts"
      by (rule fold_rhs_values_ge_acc)
    finally show ?thesis by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then have "traverse_rhs t \<sigma> \<le> fold_rhs_values (acc \<squnion> traverse_rhs t' \<sigma>) \<sigma> ts"
      by (rule Cons.IH)
    then show ?thesis by simp
  qed
qed

lemma fold_rhs_values_mono_sigma:
  fixes acc :: "'a::bounded_semilattice_sup_bot"
  assumes tree_mono:
    "\<And>t s1 s2. t \<in> set ts \<Longrightarrow> s1 \<le> s2 \<Longrightarrow> traverse_rhs t s1 \<le> traverse_rhs t s2"
  assumes sig: "\<sigma>1 \<le> \<sigma>2"
  shows "fold_rhs_values acc \<sigma>1 ts \<le> fold_rhs_values acc \<sigma>2 ts"
  using tree_mono
proof (induction ts arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons t ts)
  have hd_le: "traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2"
    using Cons.prems[of t] sig by simp
  have step1:
    "fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>1 ts
       \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>2 ts"
    by (rule Cons.IH) (use Cons.prems in simp)
  have step2:
    "fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>1) \<sigma>2 ts
       \<le> fold_rhs_values (acc \<squnion> traverse_rhs t \<sigma>2) \<sigma>2 ts"
    by (rule fold_rhs_values_mono_seed[OF sup_mono[OF order_refl hd_le]])
  show ?case using order_trans[OF step1 step2] by simp
qed

text \<open>
  A post-solution bounds every contribution tree at \<open>(v, c)\<close> by that local
  unknown.  This extracts ordinary-edge, entry, and return/combine bounds from
  the single equation post-fixpoint.
\<close>

lemma post_sol_tree_le_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state lifted"
  assumes post:
    "eq (side_cfg_T_eff_ctx gs cmb g etf bot0 s0 gseed) (v, ctx) \<sigma> \<le> \<sigma> (Inl (v, ctx))"
  assumes mem:
    "t \<in> set (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                  (intra_predecessor_list g v)
              @ map (\<lambda>(cl, fs, as). map_ltree (\<lambda>w. (w, ctx)) (etf_enter etf fs as cl))
                  (entry_seed_list g v)
              @ map (\<lambda>(cc, dst, ex). cmb ctx dst cc ex) (return_call_list g v))"
  shows "traverse_rhs t \<sigma> \<le> \<sigma> (Inl (v, ctx))"
proof -
  have "traverse_rhs t \<sigma>
          \<le> eq (side_cfg_T_eff_ctx gs cmb g etf bot0 s0 gseed) (v, ctx) \<sigma>"
    unfolding eq_side_cfg_T_eff_ctx by (rule traverse_le_fold_rhs_values[OF mem])
  then show ?thesis using post by (rule order_trans)
qed


end
