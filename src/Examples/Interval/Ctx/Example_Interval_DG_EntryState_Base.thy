theory Example_Interval_DG_EntryState_Base
  imports
    "Voblint_Analysis.Interval_Ctx_Entry_State_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>A random-argument call: the compiled base for the entry-state witness\<close>

text \<open>
  \<open>rc_program\<close> is the acceptance witness for the entry-state coverage instance: a
  procedure \<open>p\<close> returning its formal unchanged, called once with an argument whose
  concrete value is unconstrained (\<open>__voblint_nondet_int()\<close>).  Unlike a program that calls its
  callee with distinct literal arguments and so routes to distinct exact contexts,
  this program's single call site is entered from infinitely many distinct concrete
  stores, all sharing one caller-local abstract value (\<open>Top\<close>).  The routed context
  this file's siblings compute for that call is therefore \<open>Top\<close> itself: one abstract
  context that concretizes every one of those infinitely many concrete entries, not
  a family of contexts covering them.
\<close>

text \<open>\<open>special_pname_nondet_int\<close> is an ordinary identifier, not a keyword, so it cannot be
  written inside the \<open>program { ... }\<close> quotation the way other calls can: Pure's inner-syntax
  lexer reserves leading-underscore tokens for translation-internal nonterminals, rejecting any
  user identifier that begins with one.  The call is spliced in directly instead.\<close>
definition rc_program :: imp_prog where
  "rc_program = mk_program [(STR ''p'', \<lparr>formals = [STR ''a''], body = imp \<lbrakk> return a \<rbrakk>\<rparr>)]
     (Seq (VIMP_Proc.com.Call (Some (STR ''x'')) special_pname_nondet_int [])
          (imp \<lbrakk> y := p(x) \<rbrakk>))
     []"

definition rc_pi :: proc_table where "rc_pi = prog_table rc_program"
definition rc_procs :: "pname list" where "rc_procs = prog_procs rc_program"
definition rc_main :: "VIMP_Proc.com" where "rc_main = prog_main rc_program"

text \<open>The storage classifier: \<open>rc_program\<close> declares no globals, so \<open>rc_gs\<close>
  classifies every variable this chain touches as local.\<close>
abbreviation rc_gs :: "vname \<Rightarrow> bool" where
  "rc_gs \<equiv> declared_global rc_program"

abbreviation rc_lookup :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "rc_lookup s x \<equiv> lookup_resolved_st_q s (location_of rc_gs x)"

definition rc_cfg :: cfg where
  "rc_cfg = compile_prog rc_pi rc_procs"

text \<open>
  The compiled CFG.  Procedure \<open>p\<close> runs between \<open>FunctionEntry (STR ''p'')\<close> and
  \<open>FunctionResult (STR ''p'')\<close>: the body's  \<open>return a\<close> publishes through \<open>EA_Ret\<close> at
  statement \<open>0\<close>.  \<open>main\<close> occupies statements \<open>2..4\<close>: \<open>2\<close> draws \<open>x\<close> from \<open>__voblint_nondet_int()\<close> and
  continues at \<open>3\<close>, the single call site, continuing at \<open>4\<close>.\<close>

interpretation rc: compiled_cfg rc_pi rc_procs rc_cfg
  by (unfold_locales; unfold rc_cfg_def; simp add: compile_prog_finite)

text \<open>The one call site's shape, computed directly from \<open>rc_cfg\<close>. Exported for the
  routed-context siblings, which key off this single call rather than case-splitting
  on several.\<close>
lemma rc_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls rc_cfg.
     u = Statement 3 \<and> ca = CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]
       \<and> ce = FunctionEntry (STR ''p'') \<and> cont = Statement 4"
  unfolding rc_cfg_def by eval

text \<open>The call site has exactly one outgoing edge.\<close>
lemma rc_calls_unique_site:
  "\<forall>(u1, ca1, ce1, k1) \<in> calls rc_cfg. \<forall>(u2, ca2, ce2, k2) \<in> calls rc_cfg.
      u1 = u2 \<longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> k1 = k2"
  unfolding rc_cfg_def by eval

lemmas rc_finC = rc.finite_calls

subsection \<open>Source-level well-formedness\<close>

lemma rc_wf: "wf_compile_input rc_gs rc_pi rc_procs"
  by (auto simp: wf_compile_input_simps rc_pi_def rc_procs_def rc_main_def rc_program_def
      split: if_splits option.splits)

end
