(* src/Analyses/Nonrelational/Nonrelational_Transfer.thy *)
lemma nonrel_refine_sound:
  assumes "t \<in> gamma_tabs \<kappa> \<sigma>" and ch: "eval_query.channel_holds ch t" and
    "truthy (eval b t) = pol"
  shows "t \<in> gamma_tabs \<kappa> (nonrel_refine b pol \<sigma>)"
