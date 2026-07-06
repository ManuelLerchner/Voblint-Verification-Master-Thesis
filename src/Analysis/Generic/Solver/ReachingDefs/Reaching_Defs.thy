section \<open>Concrete path-level reaching definitions (RD instance, B2.3)\<close>

theory Reaching_Defs
  imports Digest_Global_Read
begin

text \<open>
  A concrete per-path reaching-definition map, the object the semantic reader's
  abstract \<open>rd_of\<close> is instantiated with.  A def-site is the target program point of
  an assignment edge; along a single CFG path (a \<open>(edge_action \<times> pp)\<close> step list) the
  last writer of a global wins, so the reaching def of \<open>x\<close> is a \<open>pp option\<close> seeded by
  the incoming def \<open>d0\<close> and updated at every \<open>EA_Assign x\<close> step.

  The key fact for the interprocedural no-kill condition (\<open>CALLEE\<close> of
  \<open>reach_sem_NOKILL_via_combine\<close>) is \<open>path_rd_no_kill_pres\<close>: a callee sub-path that
  does not write \<open>x\<close> preserves the caller's reaching def of \<open>x\<close>.  \<open>path_def_gen\<close>
  witnesses the last-writer semantics.  Bridging \<open>path_rd\<close> over paths to \<open>rd_of\<close> over
  the store-trace collecting is the remaining connective slice.
\<close>

definition path_def :: "vname \<Rightarrow> pp option \<Rightarrow> (edge_action \<times> pp) list \<Rightarrow> pp option" where
  "path_def x d0 es =
     foldl (\<lambda>acc step. case fst step of EA_Assign y _ \<Rightarrow> (if y = x then Some (snd step) else acc)
                        | _ \<Rightarrow> acc) d0 es"

definition writes_var :: "vname \<Rightarrow> (edge_action \<times> pp) list \<Rightarrow> bool" where
  "writes_var x es = (\<exists>step \<in> set es. \<exists>e. fst step = EA_Assign x e)"

definition path_rd :: "vname \<Rightarrow> pp option \<Rightarrow> (edge_action \<times> pp) list \<Rightarrow> pp set" where
  "path_rd x d0 es = set_option (path_def x d0 es)"

text \<open>A sub-path that never writes \<open>x\<close> leaves the fold accumulator unchanged.\<close>
lemma foldl_no_write:
  "\<not> writes_var x cs \<Longrightarrow>
     foldl (\<lambda>acc step. case fst step of EA_Assign y _ \<Rightarrow> (if y = x then Some (snd step) else acc)
                        | _ \<Rightarrow> acc) acc cs = acc"
proof (induction cs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  have nc: "\<not> writes_var x cs" using Cons.prems unfolding writes_var_def by auto
  have step_id: "(case fst c of EA_Assign y _ \<Rightarrow> (if y = x then Some (snd c) else acc) | _ \<Rightarrow> acc) = acc"
    using Cons.prems unfolding writes_var_def by (cases "fst c") auto
  show ?case using Cons.IH[OF nc] step_id by simp
qed

text \<open>No kill: appending a callee sub-path that does not write \<open>x\<close> preserves the
  reaching def of \<open>x\<close>.\<close>
lemma path_def_no_kill:
  assumes "\<not> writes_var x cs"
  shows "path_def x d0 (es @ cs) = path_def x d0 es"
  unfolding path_def_def foldl_append using foldl_no_write[OF assms] by simp

text \<open>The no-kill fact at the def-site set level --- the shape the semantic reader's
  \<open>CALLEE\<close> preservation consumes: the caller's reaching set survives the callee.\<close>
lemma path_rd_no_kill_pres:
  assumes "\<not> writes_var x cs"
  shows "path_rd x d0 es \<subseteq> path_rd x d0 (es @ cs)"
  unfolding path_rd_def using path_def_no_kill[OF assms] by simp

text \<open>Last-writer semantics: an \<open>EA_Assign x\<close> step gens exactly its own def-site,
  killing any prior reaching def.\<close>
lemma path_def_gen:
  "path_def x d0 (es @ [(EA_Assign x e, p)]) = Some p"
  unfolding path_def_def by simp

text \<open>Keyed last-writer semantics: the executable writer can tag a program point
  with any finite def-site key.\<close>
definition path_def_key :: "vname \<Rightarrow> 'g option \<Rightarrow> (pp \<Rightarrow> 'g) \<Rightarrow> (edge_action \<times> pp) list \<Rightarrow> 'g option" where
  "path_def_key x d0 site es =
     foldl (\<lambda>acc step. case fst step of EA_Assign y _ \<Rightarrow> (if y = x then Some (site (snd step)) else acc)
                        | _ \<Rightarrow> acc) d0 es"

lemma foldl_key_no_write:
  "\<not> writes_var x cs \<Longrightarrow>
     foldl (\<lambda>acc step. case fst step of EA_Assign y _ \<Rightarrow> (if y = x then Some (site (snd step)) else acc)
                        | _ \<Rightarrow> acc) acc cs = acc"
proof (induction cs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  have nc: "\<not> writes_var x cs" using Cons.prems unfolding writes_var_def by auto
  have step_id: "(case fst c of EA_Assign y _ \<Rightarrow> (if y = x then Some (site (snd c)) else acc) | _ \<Rightarrow> acc) = acc"
    using Cons.prems unfolding writes_var_def by (cases "fst c") auto
  show ?case using Cons.IH[OF nc] step_id by simp
qed

lemma path_def_key_no_kill:
  assumes "\<not> writes_var x cs"
  shows "path_def_key x d0 site (es @ cs) = path_def_key x d0 site es"
  unfolding path_def_key_def foldl_append
  using foldl_key_no_write[where site = site and acc =
      "foldl (\<lambda>acc step. case fst step of EA_Assign y _ \<Rightarrow> (if y = x then Some (site (snd step)) else acc)
                    | _ \<Rightarrow> acc) d0 es", OF assms]
  by simp

definition path_rd_key :: "vname \<Rightarrow> 'g option \<Rightarrow> (pp \<Rightarrow> 'g) \<Rightarrow> (edge_action \<times> pp) list \<Rightarrow> 'g set" where
  "path_rd_key x d0 site es = set_option (path_def_key x d0 site es)"

lemma path_rd_key_no_kill_pres:
  assumes "\<not> writes_var x cs"
  shows "path_rd_key x d0 site es \<subseteq> path_rd_key x d0 site (es @ cs)"
  unfolding path_rd_key_def using path_def_key_no_kill[OF assms, of d0 site es] by simp

text \<open>Dual of no-kill: a \<^emph>\<open>writing\<close> path is seed-independent.  The last writer wins, so
  once \<open>es\<close> writes \<open>x\<close> the fold result does not depend on the incoming def \<open>a\<close>/\<open>b\<close>.\<close>
lemma path_def_key_write_seed_indep:
  "writes_var x es \<Longrightarrow> path_def_key x a site es = path_def_key x b site es"
proof (induction es arbitrary: a b)
  case Nil thus ?case by (simp add: writes_var_def)
next
  case (Cons c cs)
  show ?case
  proof (cases "\<exists>e. fst c = EA_Assign x e")
    case True
    then obtain e where fc: "fst c = EA_Assign x e" by blast
    show ?thesis unfolding path_def_key_def by (simp add: fc)
  next
    case False
    hence wcs: "writes_var x cs" using Cons.prems unfolding writes_var_def by auto
    have step: "path_def_key x a site (c # cs) = path_def_key x a site cs
              \<and> path_def_key x b site (c # cs) = path_def_key x b site cs"
      unfolding path_def_key_def using False by (cases "fst c") auto
    thus ?thesis using Cons.IH[OF wcs] by simp
  qed
qed

text \<open>Write-absorb: prepending a caller sub-path to a callee path that \<^emph>\<open>does\<close> write \<open>x\<close>
  leaves the reaching-def key unchanged --- the callee's last write kills the caller's
  contribution.  This is the seed-independence the callee-exit read needs to match the
  composed return path.\<close>
lemma path_rd_key_write_absorb:
  assumes "writes_var x es_r"
  shows "path_rd_key x d0 site (es_c @ es_r) = path_rd_key x d0 site es_r"
  unfolding path_rd_key_def path_def_key_def foldl_append
  using path_def_key_write_seed_indep[OF assms,
      of "foldl (\<lambda>acc step. case fst step of EA_Assign y _ \<Rightarrow> (if y = x then Some (site (snd step)) else acc)
                    | _ \<Rightarrow> acc) d0 es_c" site d0]
  unfolding path_def_key_def by simp


subsection \<open>Bridge to the store-trace reader (B2.4)\<close>

text \<open>
  The semantic reader \<open>reach_sem\<close> (\<^theory>\<open>Voblint_Analysis.Digest_Global_Read\<close>) folds
  an abstract \<open>rd_of :: trace \<Rightarrow> 'g set\<close> over store-trace collecting, while \<open>path_rd\<close>
  is defined over CFG paths --- a bare store trace does not determine its path.  These
  lemmas state the realizability contract linking the two: whenever \<open>rd_of\<close> is
  \<^emph>\<open>path-realized\<close> (its value on a trace equals \<open>path_rd\<close> on a corresponding path),
  the concrete no-kill fact transfers to the trace level.
\<close>

text \<open>Transfer: a path-realized \<open>rd_of\<close> inherits \<open>path_rd\<close>'s no-kill preservation across
  a callee that does not write \<open>x\<close>.\<close>
lemma path_realized_callee_pres:
  fixes rd_of :: "trace \<Rightarrow> pp set"
  assumes tau: "rd_of tau = path_rd x d0 ptau"
  assumes ext: "rd_of (tau @ tl rho @ [<last tau|last rho>]) = path_rd x d0 (ptau @ pcallee)"
  assumes nowrite: "\<not> writes_var x pcallee"
  shows "rd_of tau \<subseteq> rd_of (tau @ tl rho @ [<last tau|last rho>])"
  using tau ext path_rd_no_kill_pres[OF nowrite] by simp

text \<open>
  The trace-level \<open>CALLEE\<close> premise of
  \<^const>\<open>reach_sem\<close>'s \<open>reach_sem_NOKILL_via_combine\<close> follows once every caller trace
  has a \<^emph>\<open>path-realized non-writing callee run\<close>: a callee run reaching \<open>ex\<close> from the
  caller's last store, whose path extends the caller's by a segment that does not write
  \<open>x\<close>.  This isolates the sole remaining obligation --- constructing that path-carrying
  run from the interprocedural summary --- from all the reader/kernel plumbing.
\<close>
lemma reach_sem_CALLEE_via_path:
  fixes rd_of :: "trace \<Rightarrow> pp set"
  assumes RUN: "\<And>tau. tau \<in> reaching_compat dg cmp ctx g S cl
      \<Longrightarrow> \<exists>rho ptau pcallee d0. trace_witness g S ex rho \<and> hd rho = enter_state (last tau)
        \<and> rd_of tau = path_rd x d0 ptau
        \<and> rd_of (tau @ tl rho @ [<last tau|last rho>]) = path_rd x d0 (ptau @ pcallee)
        \<and> \<not> writes_var x pcallee"
  assumes tau: "tau \<in> reaching_compat dg cmp ctx g S cl"
  shows "\<exists>rho. trace_witness g S ex rho \<and> hd rho = enter_state (last tau)
          \<and> rd_of tau \<subseteq> rd_of (tau @ tl rho @ [<last tau|last rho>])"
proof -
  from RUN[OF tau] obtain rho ptau pcallee d0
    where run: "trace_witness g S ex rho" "hd rho = enter_state (last tau)"
      and r1: "rd_of tau = path_rd x d0 ptau"
      and r2: "rd_of (tau @ tl rho @ [<last tau|last rho>]) = path_rd x d0 (ptau @ pcallee)"
      and nw: "\<not> writes_var x pcallee" by blast
  have "rd_of tau \<subseteq> rd_of (tau @ tl rho @ [<last tau|last rho>])"
    by (rule path_realized_callee_pres[OF r1 r2 nw])
  thus ?thesis using run by blast
qed


subsection \<open>Path-carrying trace witness (B2.5)\<close>

text \<open>
  A bare store trace does not determine its CFG path, so \<open>path_rd\<close> cannot be applied
  to it directly.  \<open>tp_witness\<close> pairs a witnessed store trace with a generating path,
  mirroring \<^const>\<open>trace_witness\<close> step for step and threading the \<open>(edge_action \<times> pp)\<close>
  path: edges append their step, and a combine \<^emph>\<open>composes\<close> the caller path with the
  callee path (\<open>es_c @ es_r\<close>) --- exactly the append \<open>path_rd\<close>'s no-kill lemma consumes.
\<close>
inductive tp_witness ::
  "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> trace \<Rightarrow> (edge_action \<times> pp) list \<Rightarrow> bool" for g S where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> tp_witness g S v [s] []"
| proc_entry: "(cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
              \<Longrightarrow> tp_witness g S v [s] []"
| edge: "(u, a, v) \<in> edges g \<Longrightarrow> tp_witness g S u tr es \<Longrightarrow> edge_step a (last tr) = Some s'
         \<Longrightarrow> tp_witness g S v (tr @ [s']) (es @ [(a, v)])"
| combine: "(cl, ex, v) \<in> combines g \<Longrightarrow> tp_witness g S cl tau es_c \<Longrightarrow> tp_witness g S ex rho es_r
            \<Longrightarrow> hd rho = enter_state (last tau)
            \<Longrightarrow> tp_witness g S v (tau @ tl rho @ [<last tau|last rho>]) (es_c @ es_r)"

text \<open>The pairing is sound: it projects to the store-trace witness.\<close>
lemma tp_witness_trace: "tp_witness g S v tr es \<Longrightarrow> trace_witness g S v tr"
  by (induction rule: tp_witness.induct) (auto intro: trace_witness.intros)

text \<open>The pairing is complete: every witnessed trace is realized by some path.  Hence a
  path-backed reader is total over the store-trace collecting.\<close>
lemma tp_witness_exists: "trace_witness g S v tr \<Longrightarrow> \<exists>es. tp_witness g S v tr es"
  by (induction rule: trace_witness.induct) (blast intro: tp_witness.intros)+

text \<open>
  Interprocedural no-kill at the witness level: a combine composes the caller and
  callee paths, and when the callee path does not write \<open>x\<close> the caller's reaching def
  of \<open>x\<close> survives to the return.  This is the concrete content \<open>RUN\<close> supplies to
  \<open>reach_sem_CALLEE_via_path\<close> --- carried entirely by the path witness, free of the
  store-trace ambiguity.  A must-write callee (\<open>writes_var x es_r\<close>) breaks the
  inclusion, routing the combine to the \<open>bot\<close>-on-locals theorem.
\<close>
lemma tp_witness_combine_rd_pres:
  assumes comb: "(cl, ex, v) \<in> combines g"
  assumes cw: "tp_witness g S cl tau es_c"
  assumes rw: "tp_witness g S ex rho es_r"
  assumes ent: "hd rho = enter_state (last tau)"
  assumes nw: "\<not> writes_var x es_r"
  shows "tp_witness g S v (tau @ tl rho @ [<last tau|last rho>]) (es_c @ es_r)
         \<and> path_rd x d0 es_c \<subseteq> path_rd x d0 (es_c @ es_r)"
  using tp_witness.combine[OF comb cw rw ent] path_rd_no_kill_pres[OF nw] by blast


subsection \<open>Endpoint-aware path reader (RUN wiring)\<close>

text \<open>
  The concrete reader is a union over paths that witness a trace at the program point
  being read.  The endpoint is part of the reader because the same store trace can be
  path-ambiguous; only a path witnessing the caller point can be composed with the
  callee path at a return.
\<close>
definition reach_paths_sem ::
  "cfg \<Rightarrow> store set \<Rightarrow> vname \<Rightarrow> 'g option \<Rightarrow> (pp \<Rightarrow> 'g) \<Rightarrow> (trace \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool)
     \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'g set" where
  "reach_paths_sem g S x d0 site dg cmp v ctx =
     \<Union> {path_rd_key x d0 site es |tr es. tr \<in> reaching_compat dg cmp ctx g S v
         \<and> tp_witness g S v tr es}"

lemma reach_paths_semI:
  assumes "tr \<in> reaching_compat dg cmp ctx g S v"
  assumes "tp_witness g S v tr es"
  assumes "d \<in> path_rd_key x d0 site es"
  shows "d \<in> reach_paths_sem g S x d0 site dg cmp v ctx"
  unfolding reach_paths_sem_def using assms by blast

lemma reach_paths_return_incl:
  assumes comb: "(cl, ex, v) \<in> combines g"
  assumes DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
  assumes RUN: "\<And>tau es_c. tau \<in> reaching_compat dg cmp ctx g S cl
      \<Longrightarrow> tp_witness g S cl tau es_c
      \<Longrightarrow> \<exists>rho es_r. tp_witness g S ex rho es_r \<and> hd rho = enter_state (last tau)
            \<and> \<not> writes_var x es_r"
  shows "reach_paths_sem g S x d0 site dg cmp cl ctx
       \<subseteq> reach_paths_sem g S x d0 site dg cmp v ctx"
proof
  fix d assume "d \<in> reach_paths_sem g S x d0 site dg cmp cl ctx"
  then obtain tau es_c where tau: "tau \<in> reaching_compat dg cmp ctx g S cl"
    and cw: "tp_witness g S cl tau es_c"
    and d: "d \<in> path_rd_key x d0 site es_c"
    unfolding reach_paths_sem_def by blast
  from tau have tw_cl: "trace_witness g S cl tau" and compat: "cmp (dg tau) ctx"
    unfolding reaching_compat_def cfg_collect_trace_def by auto
  have tau_ne: "tau \<noteq> []" using tw_cl by (rule trace_witness_nonempty)
  from RUN[OF tau cw] obtain rho es_r where rw: "tp_witness g S ex rho es_r"
    and ent: "hd rho = enter_state (last tau)" and nw: "\<not> writes_var x es_r"
    by blast
  define tr' where "tr' = tau @ tl rho @ [<last tau|last rho>]"
  have combined: "tp_witness g S v tr' (es_c @ es_r)"
    unfolding tr'_def using tp_witness.combine[OF comb cw rw ent] .
  have tw_v: "trace_witness g S v tr'" using combined by (rule tp_witness_trace)
  have dg_eq: "dg tr' = dg tau" unfolding tr'_def using tau_ne by (rule DG_RETURN)
  have tr'_reach: "tr' \<in> reaching_compat dg cmp ctx g S v"
    unfolding reaching_compat_def cfg_collect_trace_def using tw_v compat dg_eq by simp
  have "d \<in> path_rd_key x d0 site (es_c @ es_r)"
    using d path_rd_key_no_kill_pres[OF nw, of d0 site es_c] by blast
  thus "d \<in> reach_paths_sem g S x d0 site dg cmp v ctx"
    by (rule reach_paths_semI[OF tr'_reach combined])
qed

text \<open>
  The \<^emph>\<open>callee-exit\<close> inclusion \<open>CALLEE_INCL\<close>, dual to \<open>reach_paths_return_incl\<close>.  Where
  the return inclusion carries the \<^emph>\<open>caller\<close>'s reaching def across a \<^emph>\<open>non-writing\<close> callee
  (no-kill), this carries the \<^emph>\<open>callee-exit\<close> read to the return across a callee that
  \<^emph>\<open>must-write\<close> \<open>x\<close>.  The must-write is essential and irreducible: \<^const>\<open>reach_paths_sem\<close>
  seeds every read at the fixed \<open>d0\<close>, so a non-writing callee leaves \<open>d0\<close> in the
  callee-exit read while the return read already holds the caller's real def --- the two
  disagree unless the callee's own last write kills \<open>d0\<close> (\<open>path_rd_key_write_absorb\<close>).
  Hence \<open>CALLEE_INCL\<close> is not unconditionally derivable from the path machinery; it reduces
  to a per-combine \<^emph>\<open>must-write callee run with a matching caller\<close> (\<open>RUN\<close>), the exact dual
  of the no-kill \<open>RUN\<close> the return inclusion consumes.\<close>
lemma reach_paths_CALLEE_incl:
  assumes comb: "(cl, ex, v) \<in> combines g"
  assumes DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
  assumes RUN: "\<And>rho es_r. rho \<in> reaching_compat dg cmp ctx2 g S ex \<Longrightarrow> tp_witness g S ex rho es_r
      \<Longrightarrow> \<exists>tau es_c. tau \<in> reaching_compat dg cmp ctx g S cl \<and> tp_witness g S cl tau es_c
            \<and> hd rho = enter_state (last tau) \<and> writes_var x es_r"
  shows "reach_paths_sem g S x d0 site dg cmp ex ctx2
       \<subseteq> reach_paths_sem g S x d0 site dg cmp v ctx"
proof
  fix d assume "d \<in> reach_paths_sem g S x d0 site dg cmp ex ctx2"
  then obtain rho es_r where rho: "rho \<in> reaching_compat dg cmp ctx2 g S ex"
    and rw: "tp_witness g S ex rho es_r"
    and d: "d \<in> path_rd_key x d0 site es_r"
    unfolding reach_paths_sem_def by blast
  from RUN[OF rho rw] obtain tau es_c where tau: "tau \<in> reaching_compat dg cmp ctx g S cl"
    and cw: "tp_witness g S cl tau es_c" and ent: "hd rho = enter_state (last tau)"
    and ww: "writes_var x es_r" by blast
  from tau have tw_cl: "trace_witness g S cl tau" and compat: "cmp (dg tau) ctx"
    unfolding reaching_compat_def cfg_collect_trace_def by auto
  have tau_ne: "tau \<noteq> []" using tw_cl by (rule trace_witness_nonempty)
  define tr' where "tr' = tau @ tl rho @ [<last tau|last rho>]"
  have combined: "tp_witness g S v tr' (es_c @ es_r)"
    unfolding tr'_def using tp_witness.combine[OF comb cw rw ent] .
  have tw_v: "trace_witness g S v tr'" using combined by (rule tp_witness_trace)
  have dg_eq: "dg tr' = dg tau" unfolding tr'_def using tau_ne by (rule DG_RETURN)
  have tr'_reach: "tr' \<in> reaching_compat dg cmp ctx g S v"
    unfolding reaching_compat_def cfg_collect_trace_def using tw_v compat dg_eq by simp
  have "d \<in> path_rd_key x d0 site (es_c @ es_r)"
    using d path_rd_key_write_absorb[OF ww, of d0 site es_c] by simp
  thus "d \<in> reach_paths_sem g S x d0 site dg cmp v ctx"
    by (rule reach_paths_semI[OF tr'_reach combined])
qed

subsection \<open>Generic discharge of the callee-exit \<open>RUN\<close>\<close>

text \<open>
  The \<open>RUN\<close> premise of \<open>reach_paths_CALLEE_incl\<close> factors into two independent layers,
  determining how it is discharged generically:

  \<^enum> \<^bold>\<open>Must-write summary\<close> (\<open>must_write_to\<close>) --- the syntactic conjunct \<open>writes_var x es_r\<close>.
    A pure CFG-path predicate: \<^emph>\<open>every\<close> path witnessing the callee exit writes \<open>x\<close>.  It
    does not mention the digest, the context, or the abstract domain --- it is the
    classic interprocedural must-write bit computed once per \<open>(ex, x)\<close> over the callee
    sub-CFG (finitely many acyclic path shapes), and is the generic, instance-independent
    half.
  \<^enum> \<^bold>\<open>Backward realizability\<close> (\<open>REAL\<close>) --- the caller-existence conjunct: every
    digest-compatible callee run reaching \<open>ex\<close> under the routed context \<open>ctx2\<close> arose from
    a compatible caller trace reaching \<open>cl\<close> under \<open>ctx\<close> (with matching entry store).  This
    is \<^emph>\<open>not\<close> a path property; it is the interprocedural contract on the digest/routing
    triple \<open>(dg, cmp, rt)\<close> --- the converse of the forward \<open>DG_CALLEE\<close>/\<open>ENTER_MONO\<close>
    direction the collecting theorem already carries.  It is discharged per digest
    instance, where the calling-context encoding lives; it cannot be a once-and-for-all
    path lemma.

  The no-kill \<open>RUN\<close> of \<open>reach_paths_return_incl\<close> factors dually: a \<^emph>\<open>may-not-write\<close>
  summary (some path to \<open>ex\<close> avoids \<open>x\<close>) plus \<^emph>\<open>forward\<close> realizability (which
  \<open>DG_CALLEE\<close>/\<open>ENTER_MONO\<close> already largely supply).\<close>
definition must_write_to :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> vname \<Rightarrow> bool" where
  "must_write_to g S ex x = (\<forall>rho es. tp_witness g S ex rho es \<longrightarrow> writes_var x es)"

text \<open>
  \<^bold>\<open>REAL\<close>, the backward-realizability contract, named.  This is the \<^emph>\<open>per-digest\<close> layer
  of the callee-exit \<open>RUN\<close>: every digest-compatible callee run reaching \<open>ex\<close> under the
  routed context \<open>ctx2\<close> arose from a compatible caller trace reaching \<open>cl\<close> under \<open>ctx\<close>,
  with matching entry store.  It is the converse of the forward \<open>DG_CALLEE\<close>/\<open>ENTER_MONO\<close>
  direction the collecting theorem already carries, and it depends on how the digest
  encodes the calling context --- hence it is discharged per instance, not by a path
  lemma.  Isolating it as a named predicate makes it the single remaining per-instance
  obligation once \<^const>\<open>must_write_to\<close> is settled.\<close>
definition combine_backward_realizable ::
  "cfg \<Rightarrow> store set \<Rightarrow> (trace \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool)
     \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> bool"
where
  "combine_backward_realizable g S dg cmp cl ctx ex ctx2 =
     (\<forall>rho es_r. rho \<in> reaching_compat dg cmp ctx2 g S ex \<longrightarrow> tp_witness g S ex rho es_r
        \<longrightarrow> (\<exists>tau es_c. tau \<in> reaching_compat dg cmp ctx g S cl \<and> tp_witness g S cl tau es_c
              \<and> hd rho = enter_state (last tau)))"

text \<open>The contract is consistent: it holds whenever no digest-compatible callee run
  reaches \<open>ex\<close> at the routed context (nothing to realize).  A non-vacuous instance is
  supplied by a concrete digest whose routed context is reachable only through the call.\<close>
lemma combine_backward_realizable_vacuous:
  "reaching_compat dg cmp ctx2 g S ex = {}
     \<Longrightarrow> combine_backward_realizable g S dg cmp cl ctx ex ctx2"
  unfolding combine_backward_realizable_def by blast

text \<open>The callee-exit inclusion from the two-layer decomposition: the generic
  \<^const>\<open>must_write_to\<close> summary supplies the write conjunct, the per-digest
  \<^const>\<open>combine_backward_realizable\<close> (\<open>REAL\<close>) contract supplies caller existence.  This
  is the shape a concrete instance discharges --- \<open>must_write_to\<close> by CFG dataflow,
  \<open>REAL\<close> by the digest's context encoding.\<close>
lemma reach_paths_CALLEE_incl_via_mustwrite:
  assumes comb: "(cl, ex, v) \<in> combines g"
  assumes DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
  assumes MW: "must_write_to g S ex x"
  assumes REAL: "combine_backward_realizable g S dg cmp cl ctx ex ctx2"
  shows "reach_paths_sem g S x d0 site dg cmp ex ctx2
       \<subseteq> reach_paths_sem g S x d0 site dg cmp v ctx"
proof -
  have RUN: "\<And>rho es_r. rho \<in> reaching_compat dg cmp ctx2 g S ex \<Longrightarrow> tp_witness g S ex rho es_r
      \<Longrightarrow> \<exists>tau es_c. tau \<in> reaching_compat dg cmp ctx g S cl \<and> tp_witness g S cl tau es_c
            \<and> hd rho = enter_state (last tau) \<and> writes_var x es_r"
  proof -
    fix rho es_r
    assume r: "rho \<in> reaching_compat dg cmp ctx2 g S ex" and w: "tp_witness g S ex rho es_r"
    from REAL r w obtain tau es_c where
      "tau \<in> reaching_compat dg cmp ctx g S cl" "tp_witness g S cl tau es_c"
      "hd rho = enter_state (last tau)"
      unfolding combine_backward_realizable_def by blast
    moreover have "writes_var x es_r" using MW w unfolding must_write_to_def by blast
    ultimately show "\<exists>tau es_c. tau \<in> reaching_compat dg cmp ctx g S cl \<and> tp_witness g S cl tau es_c
              \<and> hd rho = enter_state (last tau) \<and> writes_var x es_r" by blast
  qed
  show ?thesis by (rule reach_paths_CALLEE_incl[OF comb DG_RETURN RUN])
qed

text \<open>Concrete collecting soundness with the path-backed reader.  The return-reader
  inclusion is discharged from the path-carrying run witness; the def-site-keyed
  generator obligation remains \<open>CMP_SOUND\<close>.\<close>
theorem reaching_def_collect_sound_paths:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "trace \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
    and site :: "pp \<Rightarrow> 'g" and d0 :: "'g option"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (u, ctx)\<rbrakk>
        \<Longrightarrow> s' \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v x. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global x
        \<Longrightarrow> sigma (Inl (cl, ctx)) x \<le> sigma (Inl (v, ctx)) x"
    and RUN: "\<And>ctx cl ex v tau es_c. (cl, ex, v) \<in> combines g
        \<Longrightarrow> tau \<in> reaching_compat dg cmp ctx g S cl
        \<Longrightarrow> tp_witness g S cl tau es_c
        \<Longrightarrow> \<exists>rho es_r. tp_witness g S ex rho es_r \<and> hd rho = enter_state (last tau)
              \<and> \<not> writes_var x es_r"
    and CMP_SOUND: "\<And>ctx cl ex v y. (cl, ex, v) \<in> combines g \<Longrightarrow> is_global y
        \<Longrightarrow> rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (ex, rt cl ctx (sigma (Inl (cl, ctx)))) y
              \<le> rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx) y"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx
      \<le> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
  apply (rule reaching_def_collect_sound
           [where reach = "reach_paths_sem g S x d0 site dg cmp" and rt = rt
              and entdg = entdg and dg = dg and cmp = cmp])
  subgoal using ENTRY by blast
  subgoal using PROC_ENTRY by blast
  subgoal using EDGE by blast
  subgoal using LOCAL_POST by blast
  subgoal premises p for ctx cl ex v
  proof (rule reach_paths_return_incl)
    show "(cl, ex, v) \<in> combines g" using p(1) .
    show "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
      using DG_RETURN by blast
    fix tau es_c
    assume tau: "tau \<in> reaching_compat dg cmp ctx g S cl"
      and cw: "tp_witness g S cl tau es_c"
    show "\<exists>rho es_r. tp_witness g S ex rho es_r \<and> hd rho = enter_state (last tau)
            \<and> \<not> writes_var x es_r"
      using RUN[OF p(1) tau cw] .
  qed
  subgoal using CMP_SOUND by blast
  subgoal using DG_INTRA by blast
  subgoal using DG_RETURN by blast
  subgoal using DG_CALLEE by blast
  subgoal using ENTER_MONO by blast
  done

text \<open>
  The path-backed collecting theorem with \<open>CMP_SOUND\<close> \<^emph>\<open>discharged\<close>.  Routing through
  \<open>reaching_def_collect_sound_bot_incl\<close> replaces the abstract-value read obligation
  \<open>CMP_SOUND\<close> by two structural facts: the \<open>Inl\<close> slot is \<^const>\<open>bot\<close> on globals
  (\<open>INL_GLOB_BOT\<close>, a solution invariant) and the callee-exit reaching set is contained in
  the return reaching set (\<open>CALLEE_INCL\<close>, a pure \<^const>\<open>reach_paths_sem\<close> dataflow fact).
  Read soundness at the set-valued reader then follows generically --- no per-solution
  \<open>CMP_SOUND\<close> proof, and no monotone (kill-free) reader, since the local case rides the
  \<open>bot\<close>-on-locals route.\<close>
theorem reaching_def_collect_sound_paths_incl:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "trace \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
    and site :: "pp \<Rightarrow> 'g" and d0 :: "'g option"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (u, ctx)\<rbrakk>
        \<Longrightarrow> s' \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v y. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global y
        \<Longrightarrow> sigma (Inl (cl, ctx)) y \<le> sigma (Inl (v, ctx)) y"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and INL_GLOB_BOT: "\<And>p y. is_global y \<Longrightarrow> sigma (Inl p) y = bot"
    and CALLEE_INCL: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
        \<Longrightarrow> reach_paths_sem g S x d0 site dg cmp ex (rt cl ctx (sigma (Inl (cl, ctx))))
              \<subseteq> reach_paths_sem g S x d0 site dg cmp v ctx"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx
      \<le> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
  by (rule reaching_def_collect_sound_bot_incl
        [where reach = "reach_paths_sem g S x d0 site dg cmp" and sigma = sigma
           and rt = rt and dg = dg and cmp = cmp and entdg = entdg and S = S and g = g])
     (fact ENTRY PROC_ENTRY EDGE LOCAL_POST GLOB_BOT INL_GLOB_BOT CALLEE_INCL
           DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO)+

text \<open>
  \<^bold>\<open>Read soundness of the path-backed reader, complete modulo the two RUN layers.\<close>
  The final collecting theorem carries no reach obligation at all: \<open>CALLEE_INCL\<close> is
  discharged in-place from the generic \<^const>\<open>must_write_to\<close> summary and the per-digest
  \<^const>\<open>combine_backward_realizable\<close> (\<open>REAL\<close>) contract.  Everything else is the standard
  collecting/digest plumbing (\<open>ENTRY\<close>/\<open>EDGE\<close>/digest laws/\<open>ENTER_MONO\<close>).  So for the
  semantic path reader, read soundness holds \<^emph>\<open>modulo exactly\<close> \<open>must_write_to\<close> (a decidable
  CFG summary) and \<open>REAL\<close> (the per-instance digest contract) --- no \<open>CMP_SOUND\<close>, no
  monotone reader, no reach inclusion assumed.\<close>
theorem reaching_def_collect_sound_paths_mustwrite:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and dg :: "trace \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
    and site :: "pp \<Rightarrow> 'g" and d0 :: "'g option"
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (cfg_entry g, ctx)\<rbrakk>"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx
        \<Longrightarrow> s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (u, ctx)\<rbrakk>
        \<Longrightarrow> s' \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
    and LOCAL_POST: "\<And>ctx cl ex v y. (cl, ex, v) \<in> combines g \<Longrightarrow> \<not> is_global y
        \<Longrightarrow> sigma (Inl (cl, ctx)) y \<le> sigma (Inl (v, ctx)) y"
    and GLOB_BOT: "\<And>gk. local_bot_on_locals (sigma (Inr gk))"
    and INL_GLOB_BOT: "\<And>p y. is_global y \<Longrightarrow> sigma (Inl p) y = bot"
    and MW: "\<And>cl ex v. (cl, ex, v) \<in> combines g \<Longrightarrow> must_write_to g S ex x"
    and REAL: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
        \<Longrightarrow> combine_backward_realizable g S dg cmp cl ctx ex (rt cl ctx (sigma (Inl (cl, ctx))))"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (cl, ctx)\<rbrakk>
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (sigma (Inl (cl, ctx))))"
  shows "cfg_collect_ctx dg cmp g S v ctx
      \<le> \<lbrakk>rd_obs (reach_paths_sem g S x d0 site dg cmp) sigma (v, ctx)\<rbrakk>"
proof -
  have CI: "\<And>ctx cl ex v. (cl, ex, v) \<in> combines g
      \<Longrightarrow> reach_paths_sem g S x d0 site dg cmp ex (rt cl ctx (sigma (Inl (cl, ctx))))
            \<subseteq> reach_paths_sem g S x d0 site dg cmp v ctx"
  proof -
    fix ctx cl ex v assume c: "(cl, ex, v) \<in> combines g"
    show "reach_paths_sem g S x d0 site dg cmp ex (rt cl ctx (sigma (Inl (cl, ctx))))
            \<subseteq> reach_paths_sem g S x d0 site dg cmp v ctx"
      by (rule reach_paths_CALLEE_incl_via_mustwrite[OF c DG_RETURN MW[OF c] REAL[OF c]])
  qed
  show ?thesis
    by (rule reaching_def_collect_sound_paths_incl
          [where rt = rt and entdg = entdg])
       (fact ENTRY PROC_ENTRY EDGE LOCAL_POST GLOB_BOT INL_GLOB_BOT CI
             DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO)+
qed

end
