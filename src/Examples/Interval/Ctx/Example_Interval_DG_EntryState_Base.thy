theory Example_Interval_DG_EntryState_Base
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.Run_Analysis_Sound"
begin

section \<open>A random-argument call: the compiled base for the entry-state witness\<close>

text \<open>
  \<open>rc_program\<close> is the acceptance witness for the entry-state coverage instance: a
  procedure \<open>p\<close> returning its formal unchanged, called once with an argument whose
  concrete value is unconstrained (\<open>random()\<close>).  Unlike a program that calls its
  callee with distinct literal arguments and so routes to distinct exact contexts,
  this program's single call site is entered from infinitely many distinct concrete
  stores, all sharing one caller-local abstract value (\<open>Top\<close>).  The routed context
  this file's siblings compute for that call is therefore \<open>Top\<close> itself: one abstract
  context that concretizes every one of those infinitely many concrete entries, not
  a family of contexts covering them.
\<close>

definition rc_program :: imp_prog where
  "rc_program = program {
     void p(a) { return a }
     void main() { x := random(); y := p(x) }
   }"

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
  "rc_cfg = compile_prog rc_pi rc_procs (STR ''main'') rc_main"

text \<open>
  The compiled CFG.  Procedure \<open>p\<close> runs between \<open>FunctionEntry (STR ''p'')\<close> and
  \<open>FunctionResult (STR ''p'')\<close>: the body's \<open>return a\<close> publishes through \<open>EA_Ret\<close> at
  statement \<open>0\<close>.  \<open>main\<close> occupies statements \<open>2..4\<close>: \<open>2\<close> draws \<open>x\<close> from \<open>random()\<close> and
  continues at \<open>3\<close>, the single call site, continuing at \<open>4\<close>.\<close>

lemma rc_entry: "cfg_entry rc_cfg = FunctionEntry (STR ''main'')" by eval

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

lemma rc_finE: "finite (intra rc_cfg)" unfolding rc_cfg_def using compile_prog_finite by simp
lemma rc_finC: "finite (calls rc_cfg)" unfolding rc_cfg_def using compile_prog_finite by simp

subsection \<open>The analysis specification (interval, as an executable D/G analysis)\<close>

text \<open>Classifier-parametric commutation mirrors, generic in \<open>gs\<close>: the entry point for
  this file, generic in the classifier rather than fixed to a name-based convention.\<close>

lemmas ivl_Hstep_for =
  unit_dg_Hstep_for[OF ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
    ivl_tf_st_for_reduces]

lemmas ivl_Henter_for =
  unit_dg_Henter_for[OF ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]]

lemmas ivl_Hcomb_for = unit_dg_Hcomb_for

text \<open>The abstract D/G soundness interpretation at \<open>rc_gs\<close>, generic in the storage
  classifier: gives access to this instantiation's own \<open>dg_gen\<close>/\<open>dg_gamma\<close> accessors.\<close>
lemma rc_reserved: "reserved_ret_var rc_gs"
  unfolding wf_compile_input_simps
    rc_pi_def rc_procs_def rc_main_def rc_program_def
  by (auto simp: proc_decl_of_def prog_main_name_def valid_formal_def reserved_ret_var_def
      value_providing_def source_aexp_def ret_var_def
      split: if_splits option.splits)

interpretation rc_sds:
  sound_dg_spec_ltr_for "unit_dg_spec_for rc_gs (ivl_tf_for rc_gs)" "gamma_unit rc_gs" rc_gs
  unfolding sound_dg_spec_ltr_for_def
  by (rule sound_dg_spec_unit_for[OF ivl_is_sound_transfer_for rc_reserved])

subsection \<open>Source-level well-formedness\<close>

lemma rc_wf: "wf_compile_input rc_gs rc_pi rc_procs (STR ''main'') rc_main"
  unfolding wf_compile_input_simps
    rc_pi_def rc_procs_def rc_main_def rc_program_def
  by (auto simp: proc_decl_of_def prog_main_name_def valid_formal_def reserved_ret_var_def
      value_providing_def source_aexp_def ret_var_def
      split: if_splits option.splits)

end
