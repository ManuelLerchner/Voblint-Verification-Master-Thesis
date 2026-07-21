theory Proc_CFG_Prototype
  imports "Voblint_IMP2.IMP2_Proc"
begin

section \<open>Stage 0: two-relation procedure-aware CFG kernel\<close>

text \<open>
  The mechanized architectural kernel for the procedure-aware CFG migration
  (\<open>docs/PROCEDURE_AWARE_CFG_MIGRATION.md\<close>, I.1--I.5).  It fixes the one premise the
  design still argues rather than checks: the split of the single overloaded edge set into
  two relations, \<open>intra\<close> (context-preserving flow, phenomenon \<open>Phi1\<close>) and \<open>calls\<close>
  (context-crossing calls, phenomenon \<open>Phi2\<close>).

  The kernel is self-contained: it re-declares the trace algebra (\<open>Root | Call | Resume\<close>,
  \<open>caller_of\<close>, \<open>extend\<close>) over the widened node type, defines the two-relation \<open>cfg\<close>
  record, and proves the return rule, the multi-return join, and recursive nesting on this
  datatype.  It reuses only the concrete store primitives from \<open>IMP2_Proc\<close>
  (\<open>enter_state\<close>, \<open>combine_states\<close>, \<open>combine_assign\<close>, \<open>ret_var\<close>, \<open>aval\<close>, \<open>bval\<close>).

  Scope: this stage proves the trace-algebra invariants, not the calling convention.  The
  actual-to-formal parameter binding of a real call is deferred to the compiler stage; the
  entry store here is \<open>enter_state\<close> (globals preserved, locals reset), which is enough to
  exercise call/return matching and store flow.
\<close>

subsection \<open>Nodes\<close>

text \<open>Program points stay \<open>nat\<close>; procedure identity is a \<open>pname\<close>.  \<open>FunctionEntry p\<close>
  and \<open>FunctionResult p\<close> are genuine nodes (I.5), not keyed side slots.\<close>

type_synonym pp = nat

datatype cfg_node =
    Statement pp
  | FunctionEntry pname
  | FunctionResult pname

subsection \<open>Edge actions --- two sorts by phenomenon (I.4)\<close>

text \<open>
  \<open>Phi1\<close> flow and \<open>Phi2\<close> calls have incompatible typing, so they get distinct action
  datatypes living in distinct relations.  An \<open>edge_action\<close> is a total store transformer
  within one context; there is no call constructor here, so \<open>edge_step\<close> has no call case
  and the \<open>Intra\<close> rule can never traverse a call --- by typing, not by a \<open>None\<close> result or
  a side condition.  A \<open>EA_Ret\<close> action writes the return value into \<open>ret_var\<close> in the
  callee's own context and its graph target is \<open>FunctionResult p\<close>, which is why the summary
  join is ordinary predecessor folding.
\<close>

datatype edge_action =
    EA_Nop
  | EA_Assign   vname aexp
  | EA_Assume   bexp
  | EA_AssumeNot bexp
  | EA_Ret      "aexp option" pname   \<comment> \<open>return-value write; target = FunctionResult p\<close>

datatype call_action =
    CallEdge "vname option" pname "aexp list"   \<comment> \<open>dst, callee, actuals; target = continuation\<close>

subsection \<open>Transfer\<close>

text \<open>\<open>edge_step\<close> is total on \<open>intra\<close> actions: no inert edge, no call case.\<close>

fun edge_step :: "edge_action \<Rightarrow> store \<Rightarrow> store option" where
  "edge_step EA_Nop s = Some s"
| "edge_step (EA_Assign x a) s = Some (s(x := aval a s))"
| "edge_step (EA_Assume b) s = (if bval b s then Some s else None)"
| "edge_step (EA_AssumeNot b) s = (if bval b s then None else Some s)"
| "edge_step (EA_Ret e p) s =
     Some (s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)))"

text \<open>Return-value rehydration at the caller, unchanged from the production transfer:
  write the callee's \<open>ret_var\<close> into the destination over the combined store.\<close>
definition combine_collect :: "vname option \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_collect dst s t = combine_assign dst (t ret_var) (combine_states s t)"

subsection \<open>CFG record --- two relations, one per phenomenon\<close>

text \<open>No \<open>combines\<close>, no \<open>cfg_exit\<close>.  The continuation is the \<open>calls\<close>-edge target; program
  end is \<open>FunctionResult main\<close>.  The flat CFG is exactly the \<open>calls = {}\<close> fragment (I.6),
  so every theorem quantifying over \<open>intra\<close> is verbatim a flat-CFG theorem.\<close>

record cfg =
  intra     :: "(cfg_node \<times> edge_action \<times> cfg_node) set"
  calls     :: "(cfg_node \<times> call_action \<times> cfg_node) set"
  cfg_entry :: cfg_node

subsection \<open>Activation-local traces\<close>

text \<open>The trace datatype, observers, and extension mirror the production
  \<open>CFG_Local_Trace\<close> exactly, over the widened node type \<open>cfg_node\<close> in place of \<open>pp\<close>.\<close>

datatype ltr =
    Root "(cfg_node \<times> store) list"
  | Call ltr "(cfg_node \<times> store) list"
  | Resume ltr ltr "(cfg_node \<times> store) list"

primrec path :: "ltr \<Rightarrow> (cfg_node \<times> store) list" where
  "path (Root p)       = p"
| "path (Call _ p)     = p"
| "path (Resume _ _ p) = p"

definition sink_node :: "ltr \<Rightarrow> cfg_node" where
  "sink_node t = fst (last (path t))"

definition sink_store :: "ltr \<Rightarrow> store" where
  "sink_store t = snd (last (path t))"

fun caller_of :: "ltr \<Rightarrow> ltr option" where
  "caller_of (Root _)             = None"
| "caller_of (Call caller _)      = Some caller"
| "caller_of (Resume current _ _) = caller_of current"

primrec extend :: "ltr \<Rightarrow> (cfg_node \<times> store) \<Rightarrow> ltr" where
  "extend (Root p) x       = Root (p @ [x])"
| "extend (Call c p) x     = Call c (p @ [x])"
| "extend (Resume c d p) x = Resume c d (p @ [x])"

subsection \<open>The closure relation\<close>

text \<open>
  \<open>valid_ptr\<close> is the least set closed under the four concrete operations, in the
  two-relation form (I.4, Part II \S8.2): \<open>Init\<close> seeds the main activation at
  \<open>cfg_entry\<close>; \<open>Intra\<close> reads \<open>intra\<close>; \<open>Call\<close> and \<open>Ret\<close> read \<open>calls\<close>.  Each rule reads
  exactly the relation for its phenomenon.  \<open>Intra\<close> carries no \<open>is_enter_action\<close> side
  condition --- calls are not \<open>intra\<close> members, so they are untraversable by typing.  \<open>Ret\<close>
  matches the callee's \<open>FunctionResult p\<close> against the \<open>p\<close> in the caller's \<open>CallEdge\<close>;
  continuation \<open>after\<close> and destination \<open>dst\<close> come from that same edge --- no \<open>combines\<close>.
\<close>

inductive_set valid_ptr :: "cfg \<Rightarrow> store set \<Rightarrow> ltr set" for g S where
  Init:
    "s \<in> S
     \<Longrightarrow> Root [(cfg_entry g, s)] \<in> valid_ptr g S"
| Intra:
    "t \<in> valid_ptr g S
     \<Longrightarrow> (sink_node t, a, v) \<in> intra g
     \<Longrightarrow> edge_step a (sink_store t) = Some s'
     \<Longrightarrow> extend t (v, s') \<in> valid_ptr g S"
| Call:
    "caller \<in> valid_ptr g S
     \<Longrightarrow> (sink_node caller, CallEdge dst p args, after) \<in> calls g
     \<Longrightarrow> Call caller [(FunctionEntry p, enter_state (sink_store caller))] \<in> valid_ptr g S"
| Ret:
    "callee \<in> valid_ptr g S
     \<Longrightarrow> caller_of callee = Some caller
     \<Longrightarrow> sink_node callee = FunctionResult p
     \<Longrightarrow> (sink_node caller, CallEdge dst p args, after) \<in> calls g
     \<Longrightarrow> Resume caller callee
           (path caller @ [(after, combine_collect dst (sink_store caller) (sink_store callee))])
         \<in> valid_ptr g S"

subsection \<open>Structural lemmas\<close>

lemma path_extend [simp]: "path (extend t x) = path t @ [x]"
  by (cases t) auto

lemma caller_of_extend [simp]: "caller_of (extend t x) = caller_of t"
  by (cases t) auto

lemma sink_node_extend [simp]: "sink_node (extend t x) = fst x"
  by (simp add: sink_node_def)

lemma sink_store_extend [simp]: "sink_store (extend t x) = snd x"
  by (simp add: sink_store_def)

text \<open>Sinks of literal singleton-path traces reduce automatically, so the witness proofs
  never hand-compute \<open>last\<close>.\<close>

lemma sink_node_Root [simp]: "sink_node (Root [(n, s)]) = n"
  by (simp add: sink_node_def)

lemma sink_store_Root [simp]: "sink_store (Root [(n, s)]) = s"
  by (simp add: sink_store_def)

lemma sink_node_Call [simp]: "sink_node (Call c [(n, s)]) = n"
  by (simp add: sink_node_def)

lemma sink_store_Call [simp]: "sink_store (Call c [(n, s)]) = s"
  by (simp add: sink_store_def)

lemma valid_ptr_path_nonempty:
  "t \<in> valid_ptr g S \<Longrightarrow> path t \<noteq> []"
  by (induction t rule: valid_ptr.induct) auto

subsection \<open>protoA --- a call reads only the \<open>calls\<close> relation\<close>

text \<open>Two-relation form of \<open>protoA\<close>: every \<open>Call\<close> activation exists only because a
  concrete caller took a \<open>calls\<close> edge --- the invariant survives later intra extension of
  the callee.  The \<open>intra\<close> relation plays no role in forming a call.\<close>

lemma protoA:
  assumes "Call caller q \<in> valid_ptr g S"
  shows "\<exists>dst p args after. (sink_node caller, CallEdge dst p args, after) \<in> calls g"
proof -
  have "t \<in> valid_ptr g S \<Longrightarrow>
          \<forall>ca q. t = Call ca q \<longrightarrow>
            (\<exists>dst p args after. (sink_node ca, CallEdge dst p args, after) \<in> calls g)"
    for t
  proof (induction rule: valid_ptr.induct)
    case (Init s) thus ?case by simp
  next
    case (Intra t a v s')
    show ?case
    proof (intro allI impI)
      fix ca q assume "extend t (v, s') = Call ca q"
      then obtain q' where "t = Call ca q'" by (cases t) auto
      with Intra.IH show
        "\<exists>dst p args after. (sink_node ca, CallEdge dst p args, after) \<in> calls g" by blast
    qed
  next
    case (Call caller dst p args after) then show ?case by auto
  next
    case (Ret callee caller p dst args after) then show ?case by simp
  qed
  with assms show ?thesis by blast
qed

subsection \<open>A concrete two-return witness CFG\<close>

text \<open>Procedure \<open>f\<close> has two distinct return sites, both feeding \<open>FunctionResult f\<close>:
  \<open>Gx > 0\<close> returns \<open>1\<close>, otherwise returns \<open>-1\<close>.  \<open>main\<close> calls \<open>f\<close> at its entry, with
  continuation \<open>Statement 100\<close>.\<close>

definition mn :: pname where "mn = ''main''"
definition pf :: pname where "pf = ''f''"

definition bpos :: bexp where "bpos = Less (N 0) (V ''Gx'')"

definition demo :: cfg where
  "demo =
     \<lparr> intra =
         { (FunctionEntry pf, EA_Assume bpos,    Statement 0),
           (Statement 0,      EA_Ret (Some (N 1))    pf, FunctionResult pf),
           (FunctionEntry pf, EA_AssumeNot bpos, Statement 1),
           (Statement 1,      EA_Ret (Some (N (-1))) pf, FunctionResult pf) },
       calls =
         { (FunctionEntry mn, CallEdge None pf [], Statement 100) },
       cfg_entry = FunctionEntry mn \<rparr>"

lemmas demo_defs = demo_def mn_def pf_def bpos_def

subsection \<open>protoB1 / protoB2 --- both return sites reach \<open>FunctionResult f\<close>\<close>

text \<open>Entry seed with \<open>Gx = 1\<close> takes the positive branch; the callee reaches
  \<open>FunctionResult pf\<close> through \<open>Statement 0\<close>.\<close>

lemma protoB1:
  "\<exists>t \<in> valid_ptr demo UNIV. sink_node t = FunctionResult pf"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)(''Gx'' := 1)"
  define r where "r = Root [(cfg_entry demo, s0)]"
  have root: "r \<in> valid_ptr demo UNIV"
    unfolding r_def by (rule valid_ptr.Init) simp
  have ecall: "(sink_node r, CallEdge None pf [], Statement 100) \<in> calls demo"
    unfolding r_def by (simp add: demo_defs)
  define callee where "callee = Call r [(FunctionEntry pf, enter_state (sink_store r))]"
  have C: "callee \<in> valid_ptr demo UNIV"
    unfolding callee_def by (rule valid_ptr.Call[OF root ecall])
  have eA: "(sink_node callee, EA_Assume bpos, Statement 0) \<in> intra demo"
    unfolding callee_def by (simp add: demo_defs)
  have stepA: "edge_step (EA_Assume bpos) (sink_store callee) = Some (sink_store callee)"
    unfolding callee_def r_def by (simp add: demo_defs s0_def enter_state_def is_global_def)
  define c0 where "c0 = extend callee (Statement 0, sink_store callee)"
  have C0: "c0 \<in> valid_ptr demo UNIV"
    unfolding c0_def by (rule valid_ptr.Intra[OF C eA stepA])
  have eR: "(sink_node c0, EA_Ret (Some (N 1)) pf, FunctionResult pf) \<in> intra demo"
    unfolding c0_def by (simp add: demo_defs)
  have stepR: "edge_step (EA_Ret (Some (N 1)) pf) (sink_store c0)
                 = Some ((sink_store c0)(ret_var := aval (N 1) (sink_store c0)))"
    by simp
  have T: "extend c0 (FunctionResult pf, (sink_store c0)(ret_var := aval (N 1) (sink_store c0)))
             \<in> valid_ptr demo UNIV"
    by (rule valid_ptr.Intra[OF C0 eR stepR])
  moreover have "sink_node (extend c0
      (FunctionResult pf, (sink_store c0)(ret_var := aval (N 1) (sink_store c0)))) = FunctionResult pf"
    by simp
  ultimately show ?thesis by blast
qed

text \<open>Entry seed with \<open>Gx = 0\<close> takes the negative branch through \<open>Statement 1\<close>.\<close>

lemma protoB2:
  "\<exists>t \<in> valid_ptr demo UNIV. sink_node t = FunctionResult pf"
proof -
  define s1 :: store where "s1 = (\<lambda>_. 0)"
  define r where "r = Root [(cfg_entry demo, s1)]"
  have root: "r \<in> valid_ptr demo UNIV"
    unfolding r_def by (rule valid_ptr.Init) simp
  have ecall: "(sink_node r, CallEdge None pf [], Statement 100) \<in> calls demo"
    unfolding r_def by (simp add: demo_defs)
  define callee where "callee = Call r [(FunctionEntry pf, enter_state (sink_store r))]"
  have C: "callee \<in> valid_ptr demo UNIV"
    unfolding callee_def by (rule valid_ptr.Call[OF root ecall])
  have eA: "(sink_node callee, EA_AssumeNot bpos, Statement 1) \<in> intra demo"
    unfolding callee_def by (simp add: demo_defs)
  have stepA: "edge_step (EA_AssumeNot bpos) (sink_store callee) = Some (sink_store callee)"
    unfolding callee_def r_def by (simp add: demo_defs s1_def enter_state_def is_global_def)
  define c1 where "c1 = extend callee (Statement 1, sink_store callee)"
  have C1: "c1 \<in> valid_ptr demo UNIV"
    unfolding c1_def by (rule valid_ptr.Intra[OF C eA stepA])
  have eR: "(sink_node c1, EA_Ret (Some (N (-1))) pf, FunctionResult pf) \<in> intra demo"
    unfolding c1_def by (simp add: demo_defs)
  have stepR: "edge_step (EA_Ret (Some (N (-1))) pf) (sink_store c1)
                 = Some ((sink_store c1)(ret_var := aval (N (-1)) (sink_store c1)))"
    by simp
  have T: "extend c1 (FunctionResult pf, (sink_store c1)(ret_var := aval (N (-1)) (sink_store c1)))
             \<in> valid_ptr demo UNIV"
    by (rule valid_ptr.Intra[OF C1 eR stepR])
  moreover have "sink_node (extend c1
      (FunctionResult pf, (sink_store c1)(ret_var := aval (N (-1)) (sink_store c1)))) = FunctionResult pf"
    by simp
  ultimately show ?thesis by blast
qed

subsection \<open>protoRet --- the return rule matches procedure, continuation, and dst from the edge\<close>

text \<open>Given a completed callee at \<open>FunctionResult pf\<close> whose caller sits at \<open>FunctionEntry
  mn\<close> (so the \<open>demo\<close> call edge applies), the \<open>Ret\<close> rule resumes at the continuation
  \<open>Statement 100\<close>, recovering \<open>dst\<close>, \<open>after\<close>, and the callee identity \<open>pf\<close> from the single
  \<open>CallEdge\<close> --- no \<open>combines\<close> lookup.\<close>

lemma protoRet:
  assumes callee: "callee \<in> valid_ptr demo UNIV"
    and caller: "caller_of callee = Some cr"
    and cr_sink: "sink_node cr = FunctionEntry mn"
    and sink: "sink_node callee = FunctionResult pf"
  shows "Resume cr callee
           (path cr @ [(Statement 100, combine_collect None (sink_store cr) (sink_store callee))])
         \<in> valid_ptr demo UNIV"
proof -
  have edge: "(sink_node cr, CallEdge None pf [], Statement 100) \<in> calls demo"
    by (simp add: cr_sink demo_defs)
  show ?thesis by (rule valid_ptr.Ret[OF callee caller sink edge])
qed

subsection \<open>proto_multireturn_join --- both return sites resume at the same continuation\<close>

text \<open>The two distinct callees of \<open>protoB1\<close>/\<open>protoB2\<close> both reach \<open>FunctionResult pf\<close> and
  both resume through the single \<open>demo\<close> call edge at \<open>Statement 100\<close>.  The join is the
  \<open>calls\<close>-edge target, not a \<open>combines\<close> lookup.  They do not share a caller --- a single
  concrete activation takes exactly one branch --- but both land at the same continuation.\<close>

lemma proto_multireturn_join:
  "\<exists>t1 t2. t1 \<in> valid_ptr demo UNIV \<and> t2 \<in> valid_ptr demo UNIV
     \<and> t1 \<noteq> t2
     \<and> sink_node t1 = FunctionResult pf \<and> sink_node t2 = FunctionResult pf
     \<and> (\<exists>c1. caller_of t1 = Some c1
          \<and> Resume c1 t1 (path c1 @ [(Statement 100,
                combine_collect None (sink_store c1) (sink_store t1))]) \<in> valid_ptr demo UNIV)
     \<and> (\<exists>c2. caller_of t2 = Some c2
          \<and> Resume c2 t2 (path c2 @ [(Statement 100,
                combine_collect None (sink_store c2) (sink_store t2))]) \<in> valid_ptr demo UNIV)"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)(''Gx'' := 1)"
  define s1 :: store where "s1 = (\<lambda>_. 0)"
  define r0 where "r0 = Root [(cfg_entry demo, s0)]"
  define r1 where "r1 = Root [(cfg_entry demo, s1)]"

  \<comment> \<open>positive branch\<close>
  have R0: "r0 \<in> valid_ptr demo UNIV" unfolding r0_def by (rule valid_ptr.Init) simp
  have ec0: "(sink_node r0, CallEdge None pf [], Statement 100) \<in> calls demo"
    unfolding r0_def by (simp add: demo_defs)
  define k0 where "k0 = Call r0 [(FunctionEntry pf, enter_state (sink_store r0))]"
  have K0: "k0 \<in> valid_ptr demo UNIV" unfolding k0_def by (rule valid_ptr.Call[OF R0 ec0])
  have eA0: "(sink_node k0, EA_Assume bpos, Statement 0) \<in> intra demo"
    unfolding k0_def by (simp add: demo_defs)
  have stA0: "edge_step (EA_Assume bpos) (sink_store k0) = Some (sink_store k0)"
    unfolding k0_def r0_def by (simp add: demo_defs s0_def enter_state_def is_global_def)
  define c0 where "c0 = extend k0 (Statement 0, sink_store k0)"
  have C0: "c0 \<in> valid_ptr demo UNIV" unfolding c0_def by (rule valid_ptr.Intra[OF K0 eA0 stA0])
  have eR0: "(sink_node c0, EA_Ret (Some (N 1)) pf, FunctionResult pf) \<in> intra demo"
    unfolding c0_def by (simp add: demo_defs)
  have stR0: "edge_step (EA_Ret (Some (N 1)) pf) (sink_store c0)
                = Some ((sink_store c0)(ret_var := aval (N 1) (sink_store c0)))" by simp
  define t1 where "t1 = extend c0 (FunctionResult pf, (sink_store c0)(ret_var := aval (N 1) (sink_store c0)))"
  have T1: "t1 \<in> valid_ptr demo UNIV" unfolding t1_def by (rule valid_ptr.Intra[OF C0 eR0 stR0])

  \<comment> \<open>negative branch\<close>
  have R1: "r1 \<in> valid_ptr demo UNIV" unfolding r1_def by (rule valid_ptr.Init) simp
  have ec1: "(sink_node r1, CallEdge None pf [], Statement 100) \<in> calls demo"
    unfolding r1_def by (simp add: demo_defs)
  define k1 where "k1 = Call r1 [(FunctionEntry pf, enter_state (sink_store r1))]"
  have K1: "k1 \<in> valid_ptr demo UNIV" unfolding k1_def by (rule valid_ptr.Call[OF R1 ec1])
  have eA1: "(sink_node k1, EA_AssumeNot bpos, Statement 1) \<in> intra demo"
    unfolding k1_def by (simp add: demo_defs)
  have stA1: "edge_step (EA_AssumeNot bpos) (sink_store k1) = Some (sink_store k1)"
    unfolding k1_def r1_def by (simp add: demo_defs s1_def enter_state_def is_global_def)
  define c1 where "c1 = extend k1 (Statement 1, sink_store k1)"
  have C1: "c1 \<in> valid_ptr demo UNIV" unfolding c1_def by (rule valid_ptr.Intra[OF K1 eA1 stA1])
  have eR1: "(sink_node c1, EA_Ret (Some (N (-1))) pf, FunctionResult pf) \<in> intra demo"
    unfolding c1_def by (simp add: demo_defs)
  have stR1: "edge_step (EA_Ret (Some (N (-1))) pf) (sink_store c1)
                = Some ((sink_store c1)(ret_var := aval (N (-1)) (sink_store c1)))" by simp
  define t2 where "t2 = extend c1 (FunctionResult pf, (sink_store c1)(ret_var := aval (N (-1)) (sink_store c1)))"
  have T2: "t2 \<in> valid_ptr demo UNIV" unfolding t2_def by (rule valid_ptr.Intra[OF C1 eR1 stR1])

  \<comment> \<open>the two witnesses are distinct: their caller seeds differ at \<open>Gx\<close>\<close>
  have sneq: "s0 ''Gx'' \<noteq> s1 ''Gx''" by (simp add: s0_def s1_def)
  have neq: "t1 \<noteq> t2"
    using sneq by (auto simp: t1_def t2_def c0_def c1_def k0_def k1_def r0_def r1_def)

  have sn1: "sink_node t1 = FunctionResult pf" by (simp add: t1_def)
  have sn2: "sink_node t2 = FunctionResult pf" by (simp add: t2_def)

  \<comment> \<open>each return site resumes at \<open>Statement 100\<close> through the single call edge\<close>
  have ct1: "caller_of t1 = Some r0" by (simp add: t1_def c0_def k0_def)
  have ct2: "caller_of t2 = Some r1" by (simp add: t2_def c1_def k1_def)
  have edge0: "(sink_node r0, CallEdge None pf [], Statement 100) \<in> calls demo"
    unfolding r0_def by (simp add: demo_defs)
  have edge1: "(sink_node r1, CallEdge None pf [], Statement 100) \<in> calls demo"
    unfolding r1_def by (simp add: demo_defs)
  have res1: "Resume r0 t1
      (path r0 @ [(Statement 100, combine_collect None (sink_store r0) (sink_store t1))])
        \<in> valid_ptr demo UNIV"
    by (rule valid_ptr.Ret[OF T1 ct1 sn1 edge0])
  have res2: "Resume r1 t2
      (path r1 @ [(Statement 100, combine_collect None (sink_store r1) (sink_store t2))])
        \<in> valid_ptr demo UNIV"
    by (rule valid_ptr.Ret[OF T2 ct2 sn2 edge1])

  from T1 T2 neq sn1 sn2 ct1 ct2 res1 res2 show ?thesis by blast
qed

subsection \<open>proto_recursion_nesting --- same-procedure activations are distinct and nested\<close>

text \<open>A self-recursive procedure \<open>r\<close>: at its entry it either returns (\<open>Gx <= 0\<close>) or calls
  itself (\<open>Gx > 0\<close>) at the continuation \<open>Statement 200\<close>.  Two activations of \<open>r\<close> are
  distinct and correctly nested via \<open>caller_of\<close>, with no context reconstruction.\<close>

definition pr :: pname where "pr = ''r''"

definition rec_cfg :: cfg where
  "rec_cfg =
     \<lparr> intra =
         { (FunctionEntry pr, EA_AssumeNot bpos, Statement 0),
           (Statement 0,      EA_Ret (Some (N 0)) pr, FunctionResult pr),
           (FunctionEntry pr, EA_Assume bpos,    Statement 1) },
       calls =
         { (Statement 1, CallEdge None pr [], Statement 200) },
       cfg_entry = FunctionEntry pr \<rparr>"

lemmas rec_defs = rec_cfg_def pr_def bpos_def

lemma proto_recursion_nesting:
  "\<exists>outer inner.
      outer \<in> valid_ptr rec_cfg UNIV \<and> inner \<in> valid_ptr rec_cfg UNIV
    \<and> outer \<noteq> inner
    \<and> caller_of inner = Some outer
    \<and> caller_of outer = None
    \<and> sink_node outer = Statement 1
    \<and> sink_node inner = FunctionEntry pr"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)(''Gx'' := 1)"
  define root where "root = Root [(cfg_entry rec_cfg, s0)]"
  have R: "root \<in> valid_ptr rec_cfg UNIV" unfolding root_def by (rule valid_ptr.Init) simp
  have eA: "(sink_node root, EA_Assume bpos, Statement 1) \<in> intra rec_cfg"
    unfolding root_def by (simp add: rec_defs)
  have stepA: "edge_step (EA_Assume bpos) (sink_store root) = Some (sink_store root)"
    unfolding root_def by (simp add: rec_defs s0_def enter_state_def is_global_def)
  define outer where "outer = extend root (Statement 1, sink_store root)"
  have OUTER: "outer \<in> valid_ptr rec_cfg UNIV"
    unfolding outer_def by (rule valid_ptr.Intra[OF R eA stepA])
  have so: "sink_node outer = Statement 1" by (simp add: outer_def)
  have ecall: "(sink_node outer, CallEdge None pr [], Statement 200) \<in> calls rec_cfg"
    by (simp add: so rec_defs)
  define inner where "inner = Call outer [(FunctionEntry pr, enter_state (sink_store outer))]"
  have INNER: "inner \<in> valid_ptr rec_cfg UNIV"
    unfolding inner_def by (rule valid_ptr.Call[OF OUTER ecall])
  have si: "sink_node inner = FunctionEntry pr" by (simp add: inner_def)
  have ci: "caller_of inner = Some outer" by (simp add: inner_def)
  have co: "caller_of outer = None" by (simp add: outer_def root_def)
  have neq: "outer \<noteq> inner" by (simp add: outer_def inner_def)
  from OUTER INNER neq ci co so si show ?thesis by blast
qed

end
