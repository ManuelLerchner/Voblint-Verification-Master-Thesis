(* src/Analyses/Nonrelational/Nonrelational_Transfer.thy *)
lemma nonrel_refine_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "geval_query.channel_holds eval ch t" and
    "truthy (eval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (nonrel_refine b pol \<sigma>)"
