theory CFG_Path_Bridge
  imports CFG_Compound_Paths
begin

(* Path soundness, lfp-path equivalence, compile_path_small_step. *)

lemma cfg_collect_step:
  assumes e: "(u, a, v) : edges g"
  shows "edge_collect a (cfg_collect g S u) \<subseteq> cfg_collect g S v"
proof -
  have lfp: "cfg_collect g S = cfg_collect_F g S (cfg_collect g S)"
    using cfg_collect_lfp_unfold by presburger
  have "edge_collect a (cfg_collect g S u) \<subseteq> collect_pp g (cfg_collect g S) v"
    unfolding collect_pp_def using e by blast
  also have "collect_pp g (cfg_collect g S) v \<subseteq> cfg_collect g S v"
    by (metis UnCI cfg_collect_F_def lfp subsetI)
  finally show ?thesis .
qed

lemma path_sound_cfg_collect_aux:
  assumes p: "g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
  shows "edges_collect es (cfg_collect g S u) \<subseteq> cfg_collect g S v"
proof (insert p, induction es arbitrary: u v)
  case Nil
  then have "u = v" by (cases rule: cfg_path.cases) simp_all
  then show ?case by simp
next
  case (Cons e es')
  assume p: "g \<turnstile> u \<longrightarrow>\<^bsub>(e # es')\<^esub> v"
  obtain a w where ew: "e = (a, w)" by (cases e) auto
  from p ew obtain ed: "(u, a, w) \<in> edges g" and p2: "g \<turnstile> w \<longrightarrow>\<^bsub>es'\<^esub> v"
    by (cases rule: cfg_path.cases) auto
  have step_edge: "edge_collect a (cfg_collect g S u) \<subseteq> cfg_collect g S w"
    by (rule cfg_collect_step[OF ed])
  have IH: "edges_collect es' (cfg_collect g S w) \<subseteq> cfg_collect g S v"
    by (rule Cons.IH[OF p2])
  have "edges_collect es' (edge_collect a (cfg_collect g S u))
        \<subseteq> edges_collect es' (cfg_collect g S w)"
    by (rule edges_collect_mono_strong[OF step_edge])
  also have "\<dots> \<subseteq> cfg_collect g S v"
    by (rule IH)
  finally show ?case unfolding ew edges_collect.simps .
qed  

lemma path_sound_cfg_collect:
  assumes es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v"
  shows "edges_collect es S \<subseteq> cfg_collect g S v"
proof -
  have ent: "S \<subseteq> cfg_collect g S (cfg_entry g)"
  proof -
    have "cfg_collect g S (cfg_entry g) = cfg_collect_F g S (cfg_collect g S) (cfg_entry g)"
      using cfg_collect_lfp_unfold by simp
    then show ?thesis unfolding cfg_collect_F_def by auto
  qed
  have "edges_collect es S \<subseteq> edges_collect es (cfg_collect g S (cfg_entry g))"
    by (rule edges_collect_mono_strong[OF ent])
  also have "\<dots> \<subseteq> cfg_collect g S v"
    by (rule path_sound_cfg_collect_aux[OF es])
  finally show ?thesis .
qed

(* Per-pp lfp <-> path-based equality.

   Both formulations of CFG collecting agree at every program point, not
   just the exit.  Used by the small-step pipeline soundness chain:
   `pipeline_invariant_sound` is stated in lfp form (`cfg_collect`); the
   small-step bridge talks about CFG paths (= `cfg_collect_paths`). *)
theorem cfg_collect_eq_cfg_collect_paths:
  "cfg_collect g S v = cfg_collect_paths g S v"
proof (rule order_antisym)
  show "cfg_collect g S v \<subseteq> cfg_collect_paths g S v"
    by (rule cfg_collect_le_paths)
  show "cfg_collect_paths g S v \<subseteq> cfg_collect g S v"
  proof
    fix x assume "x \<in> cfg_collect_paths g S v"
    then obtain es where
      es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v" and
      x:  "x \<in> edges_collect es S"
      unfolding cfg_collect_paths_def by blast
    from path_sound_cfg_collect[OF es] x
    show "x \<in> cfg_collect g S v" by blast
  qed
qed

lemma compile_path_small_step:
  assumes es: "(to_cfg c) \<turnstile> (cfg_entry (to_cfg c)) \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg c))"
    and s: "s \<in> S"
    and t: "t \<in> edges_collect es {s}"
  shows "(c, s) \<rightarrow>* (SKIP, t)"
  using assms
proof (induction c arbitrary: es s t S rule: com.induct)
  case SKIP
  obtain n' en ex E where comp: "compile SKIP 0 = (n', en, ex, E)"
    and en: "cfg_entry (to_cfg SKIP) = en"
    and ex: "cfg_exit (to_cfg SKIP) = ex"
    and E: "edges (to_cfg SKIP) = E"
    by (rule to_cfg_compile)
  from comp have en_ex: "en = 0" "ex = 1" "E = {(0, EA_Nop, 1)}" by auto
  with E have edges: "edges (to_cfg SKIP) = {(0, EA_Nop, 1)}" by simp
  from SKIP.prems(1) en ex en_ex have p: "(to_cfg SKIP) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> 1" by simp
  have es_eq: "es = [(EA_Nop, 1)]"
    by (rule cfg_path_singleton_edge[OF edges _ p]) simp
  with SKIP.prems(3) show ?case by auto
next
  case (Assign x a)
  obtain n' en ex E where comp: "compile (x ::= a) 0 = (n', en, ex, E)"
    and en: "cfg_entry (to_cfg (x ::= a)) = en"
    and ex: "cfg_exit (to_cfg (x ::= a)) = ex"
    and E: "edges (to_cfg (x ::= a)) = E"
    by (rule to_cfg_compile)
  from comp have en_ex: "en = 0" "ex = 1" "E = {(0, EA_Assign x a, 1)}" by auto
  with E have edges: "edges (to_cfg (x ::= a)) = {(0, EA_Assign x a, 1)}" by simp
  from Assign.prems(1) en ex en_ex have p: "(to_cfg (x ::= a)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> 1" by simp
  have es_eq: "es = [(EA_Assign x a, 1)]"
    by (rule cfg_path_singleton_edge[OF edges _ p]) simp
  with Assign.prems(3) have teq: "t = s(x := aval a s)" by auto
  show ?case unfolding teq by (blast intro: star.step Assign)
next
  case (Seq c1 c2)
  obtain n1 en1 ex1 E1 where
        c1_0: "compile c1 0 = (n1, en1, ex1, E1)"
    and en1_eq: "cfg_entry (to_cfg c1) = en1"
    and ex1_eq: "cfg_exit  (to_cfg c1) = ex1"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and en20_eq: "cfg_entry (to_cfg c2) = en20"
    and ex20_eq: "cfg_exit  (to_cfg c2) = ex20"
    by (rule to_cfg_compile)
  have c2_n: "compile c2 n1 = (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0, of n1] by simp
  have en_seq: "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    and ex_seq: "cfg_exit  (to_cfg (c1 ;; c2)) = ex20 + n1"
    using cfg_edges_entry_exit_Seq[OF c1_0 c2_n] by auto
  from Seq.prems(1) en_seq ex_seq
    have p: "(to_cfg (c1 ;; c2)) \<turnstile> en1 \<longrightarrow>\<^bsub>es\<^esub> (ex20 + n1)" by simp
  from cfg_path_Seq_iff[OF c1_0 c2_0, THEN iffD1, OF p] obtain es1 es2 where
        es_split: "es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2"
    and p1: "(to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1"
    and p2: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    by blast
  from p1 en1_eq ex1_eq
    have p1': "(to_cfg c1) \<turnstile> (cfg_entry (to_cfg c1)) \<longrightarrow>\<^bsub>es1\<^esub> (cfg_exit (to_cfg c1))" by simp
  from p2 en20_eq ex20_eq
    have p2': "(to_cfg c2) \<turnstile> (cfg_entry (to_cfg c2)) \<longrightarrow>\<^bsub>es2\<^esub> (cfg_exit (to_cfg c2))" by simp

  have collect_eq: "edges_collect es {s} = edges_collect es2 (edges_collect es1 {s})"
  proof -
    have "edges_collect es {s}
          = edges_collect ((EA_Nop, en20 + n1) # offset_path n1 es2) (edges_collect es1 {s})"
      unfolding es_split by (rule edges_collect_append)
    also have "\<dots> = edges_collect (offset_path n1 es2) (edges_collect es1 {s})" by simp
    also have "\<dots> = edges_collect es2 (edges_collect es1 {s})" by simp
    finally show ?thesis .
  qed
  from Seq.prems(3) collect_eq have t_in: "t \<in> edges_collect es2 (edges_collect es1 {s})" by simp
  from t_in obtain s2 where
        s2_in: "s2 \<in> edges_collect es1 {s}"
    and t_in2: "t \<in> edges_collect es2 {s2}"
    by (rule edges_collect_memberE)

  have step1: "(c1, s) \<rightarrow>* (SKIP, s2)"
    using Seq.IH(1)[OF p1' singletonI s2_in] .
  have step2: "(c2, s2) \<rightarrow>* (SKIP, t)"
    using Seq.IH(2)[OF p2' singletonI t_in2] .
  show ?case
    using step1 step2 seq_comp by blast
next
  case (If b c1 c2)
  obtain n10 en10 ex10 E10 where
        c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    and en10_eq: "cfg_entry (to_cfg c1) = en10"
    and ex10_eq: "cfg_exit  (to_cfg c1) = ex10"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and en20_eq: "cfg_entry (to_cfg c2) = en20"
    and ex20_eq: "cfg_exit  (to_cfg c2) = ex20"
    by (rule to_cfg_compile)
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp
  have en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto
  from If.prems(1) en_if ex_if
    have p: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))" by simp

  from cfg_path_If_iff[OF c1_0 c2_0, THEN iffD1, OF p] have split_or:
    "(\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]
                \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
   \<or> (\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20)" .

  show ?case
  proof (rule disjE[OF split_or])
    assume "\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]
                  \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
    then obtain es1 where
          es_eq: "es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
      and pc1: "(to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
      by blast
    have collect_chain:
      "edges_collect es {s} = edges_collect es1 {x \<in> {s}. bval b x}"
    proof -
      have "edges_collect es {s}
            = edges_collect (offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))])
                           (edges_collect [(EA_Assume b, en10 + 1)] {s})"
        unfolding es_eq by (simp add: edges_collect_append)
      also have "\<dots> = edges_collect [(EA_Nop, n20 + (n10 + 1))]
                                    (edges_collect (offset_path 1 es1)
                                                  (edges_collect [(EA_Assume b, en10 + 1)] {s}))"
        by (simp add: edges_collect_append)
      also have "\<dots> = edges_collect (offset_path 1 es1)
                                    (edges_collect [(EA_Assume b, en10 + 1)] {s})"
        by simp
      also have "\<dots> = edges_collect es1 (edges_collect [(EA_Assume b, en10 + 1)] {s})"
        by simp
      also have "\<dots> = edges_collect es1 {x \<in> {s}. bval b x}"
        by simp
      finally show ?thesis .
    qed
    have bv: "bval b s"
    proof (rule ccontr)
      assume nb: "\<not> bval b s"
      have empty_filter: "{x \<in> {s}. bval b x} = {}" using nb by auto
      have "edges_collect es {s} = edges_collect es1 {}"
        using collect_chain empty_filter
        by argo
      hence "edges_collect es {s} = {}" by simp
      with If.prems(3) show False by simp
    qed
    hence filter_eq: "{x \<in> {s}. bval b x} = {s}" by auto
    from If.prems(3) collect_chain filter_eq
      have t_in: "t \<in> edges_collect es1 {s}" by simp
    from pc1 en10_eq ex10_eq
      have p1: "(to_cfg c1) \<turnstile> (cfg_entry (to_cfg c1)) \<longrightarrow>\<^bsub>es1\<^esub> (cfg_exit (to_cfg c1))" by simp
    have step1: "(c1, s) \<rightarrow>* (SKIP, t)"
      using If.IH(1)[OF p1 singletonI t_in] .
    show ?thesis using bv step1 star.step IfTrue
      by metis
  next
    assume "\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                  \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    then obtain es2 where
          es_eq: "es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
      and pc2: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
      by blast
    have collect_chain:
      "edges_collect es {s} = edges_collect es2 {x \<in> {s}. \<not> bval b x}"
    proof -
      have "edges_collect es {s}
            = edges_collect (offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))])
                           (edges_collect [(EA_AssumeNot b, en20 + (n10 + 1))] {s})"
        unfolding es_eq by (simp add: edges_collect_append)
      also have "\<dots> = edges_collect [(EA_Nop, n20 + (n10 + 1))]
                                    (edges_collect (offset_path (n10 + 1) es2)
                                                  (edges_collect [(EA_AssumeNot b, en20 + (n10 + 1))] {s}))"
        by (simp add: edges_collect_append)
      also have "\<dots> = edges_collect (offset_path (n10 + 1) es2)
                                    (edges_collect [(EA_AssumeNot b, en20 + (n10 + 1))] {s})"
        by simp
      also have "\<dots> = edges_collect es2 (edges_collect [(EA_AssumeNot b, en20 + (n10 + 1))] {s})"
        by simp
      also have "\<dots> = edges_collect es2 {x \<in> {s}. \<not> bval b x}"
        by simp
      finally show ?thesis .
    qed
    have nbv: "\<not> bval b s"
    proof (rule ccontr)
      assume "\<not> \<not> bval b s"
      hence bv: "bval b s" by simp
      have empty_filter: "{x \<in> {s}. \<not> bval b x} = {}" using bv by auto
      have "edges_collect es {s} = edges_collect es2 {}"
        using collect_chain empty_filter by presburger
      hence "edges_collect es {s} = {}" by simp
      with If.prems(3) show False by simp
    qed
    hence filter_eq: "{x \<in> {s}. \<not> bval b x} = {s}" by auto
    from If.prems(3) collect_chain filter_eq
      have t_in: "t \<in> edges_collect es2 {s}" by simp
    from pc2 en20_eq ex20_eq
      have p2: "(to_cfg c2) \<turnstile> (cfg_entry (to_cfg c2)) \<longrightarrow>\<^bsub>es2\<^esub> (cfg_exit (to_cfg c2))" by simp
    have step2: "(c2, s) \<rightarrow>* (SKIP, t)"
      using If.IH(2)[OF p2 singletonI t_in] .
    show ?thesis using nbv step2 star.step IfFalse
      by metis  
  qed
next
  case (While b c)
  obtain n10 en10 ex10 E10 where
        c0: "compile c 0 = (n10, en10, ex10, E10)"
    and en0_eq: "cfg_entry (to_cfg c) = en10"
    and ex0_eq: "cfg_exit  (to_cfg c) = ex10"
    by (rule to_cfg_compile)
  have c1_1: "compile c 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c0, of 1] by simp
  obtain nW enW exW EW where
        compW: "compile (WHILE b DO c) 0 = (nW, enW, exW, EW)"
    and enW_eq: "cfg_entry (to_cfg (WHILE b DO c)) = enW"
    and exW_eq: "cfg_exit  (to_cfg (WHILE b DO c)) = exW"
    by (rule to_cfg_compile)
  have Ew: "edges (to_cfg (WHILE b DO c)) =
             {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, n10 + 1)}
             \<union> offset_edges 1 E10 \<union> {(ex10 + 1, EA_Nop, 0)}"
    and en_w: "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    and ex_w: "cfg_exit  (to_cfg (WHILE b DO c)) = n10 + 1"
    using cfg_edges_entry_exit_While[OF c1_1] by auto
  from While.prems(1) en_w ex_w
    have p: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n10 + 1)" by simp
  from cfg_path_While_exit_iff[OF c0 c1_1, THEN iffD1, OF p] obtain es_pre where
        es_decomp: "es = es_pre @ [(EA_AssumeNot b, n10 + 1)]"
    and p_pre: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_pre\<^esub> 0"
    by blast
  have t_full: "t \<in> edges_collect (es_pre @ [(EA_AssumeNot b, n10 + 1)]) {s}"
    using While.prems(3) es_decomp by simp
  have nb_t: "\<not> bval b t"
    using t_full by (auto simp: edges_collect_append)
  have body_univ:
    "\<And>es_body S0 s''. (to_cfg c) \<turnstile> (cfg_entry (to_cfg c)) \<longrightarrow>\<^bsub>es_body\<^esub> (cfg_exit (to_cfg c))
       \<Longrightarrow> s'' \<in> edges_collect es_body {S0} \<Longrightarrow> (c, S0) \<rightarrow>* (SKIP, s'')"
    using While.IH(1)[OF _ singletonI] by blast
  have main:
    "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>ER\<^esub> 0
     \<Longrightarrow> T \<in> edges_collect (ER @ [(EA_AssumeNot b, n10 + 1)]) {S0}
     \<Longrightarrow> \<not> bval b T
     \<Longrightarrow> (WHILE b DO c, S0) \<rightarrow>* (SKIP, T)"
    for ER S0 T
  proof (induction "length ER" arbitrary: ER S0 T rule: less_induct)
    case less
    note IH = less.hyps
    note p_R = less.prems(1) and t_R = less.prems(2) and nb_R = less.prems(3)
    show ?case
    proof (cases ER)
      case Nil
      show ?thesis
        using t_R nb_R Nil
        by (metis (lifting) IfFalse edge_collect.simps(4) edges_collect.simps(1,2) edges_collect_append
            mem_Collect_eq singleton_iff small_step.While star.simps) 
    next
      case (Cons hd tl)
      have ne: "ER \<noteq> []" using Cons by simp
      from cfg_path_While_loop_iff[OF c0 c1_1, THEN iffD1, OF p_R]
        have loop_decomp: "ER = [] \<or> (\<exists>es_body ER'.
              ER = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ ER'
              \<and> (to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10
              \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>ER'\<^esub> 0)"
        by blast
      from loop_decomp ne obtain es_body ER' where
            peel_eq: "ER = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ ER'"
        and pc: "(to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10"
        and p_tail: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>ER'\<^esub> 0"
        by auto
      have len: "length ER' < length ER" unfolding peel_eq by simp
      from pc en0_eq ex0_eq have p_body:
            "(to_cfg c) \<turnstile> (cfg_entry (to_cfg c)) \<longrightarrow>\<^bsub>es_body\<^esub> (cfg_exit (to_cfg c))"
        by simp
      show ?thesis
      proof (cases "bval b S0")
        case False
        have head_empty: "edges_collect [(EA_Assume b, en10 + 1)] {S0} = {}"
          using False by auto
        have er_empty: "edges_collect ER {S0} = {}"
        proof -
          have step1: "edges_collect ER {S0}
                = edges_collect (offset_path 1 es_body @ [(EA_Nop, 0)] @ ER')
                    (edges_collect [(EA_Assume b, en10 + 1)] {S0})"
            unfolding peel_eq by (rule edges_collect_append)
          show ?thesis by (metis step1 head_empty edges_collect_empty_set)
        qed
        have all_empty: "edges_collect (ER @ [(EA_AssumeNot b, n10 + 1)]) {S0} = {}"
          by (simp add: edges_collect_append er_empty edges_collect_empty_set)
        from t_R all_empty show ?thesis
          by blast
      next
        case True
        have eq_head: "edges_collect [(EA_Assume b, en10 + 1)] {S0} = {S0}"
          using True by auto
        have collect_tail: "edges_collect ER {S0} = edges_collect ER' (edges_collect es_body {S0})"
        proof -
          have "edges_collect ER {S0} = edges_collect ER' (edges_collect [(EA_Nop, 0)]
                  (edges_collect (offset_path 1 es_body)
                    (edges_collect [(EA_Assume b, en10 + 1)] {S0})))"
            unfolding peel_eq by (simp add: edges_collect_append)
          also have "\<dots> = edges_collect ER' (edges_collect es_body {S0})"
            using eq_head by simp
          finally show ?thesis .
        qed
        from t_R collect_tail have t_chain:
              "T \<in> edges_collect ER' (edges_collect es_body {S0})"
          by (simp add: edges_collect_append)
        obtain s'' where s''_in: "s'' \<in> edges_collect es_body {S0}"
          and t_in': "T \<in> edges_collect ER' {s''}"
          using mem_edges_collect_from_set[OF t_chain] by blast
        have step_body: "(c, S0) \<rightarrow>* (SKIP, s'')" using body_univ[OF p_body s''_in] .
        have t_in_tail: "T \<in> edges_collect (ER' @ [(EA_AssumeNot b, n10 + 1)]) {s''}"
          using t_in' nb_R by (simp add: edges_collect_append)
        have step_tail: "(WHILE b DO c, s'') \<rightarrow>* (SKIP, T)"
          using IH[OF len p_tail t_in_tail nb_R] .
        show ?thesis using True step_body step_tail
          by (meson IfTrue seq_comp small_step.While star.step)
      qed
    qed
  qed
  from main[OF p_pre t_full nb_t] show ?case
    by blast 
qed

end
