(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
theorem run_voblint_certified_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "declared_global p, prog_table p
                  \<turnstile> (main_body (prog_table p), s0, [])
                    \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and terminates: "config_terminates D rule ctx p"
      and ans: "run_voblint D rule ctx p = Analysed res"
  shows "\<exists>v stk.
             prog_table p, prog_cfg p \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,
                        cinit_stores (declared_global p)\<^esub> v
           \<and> analysis_result_covers D rule ctx p v s
           \<and> checks_sound_at res v s"
