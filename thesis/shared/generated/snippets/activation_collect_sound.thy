(* src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy *)
theorem activation_collect_sound:
  assumes "activation_coverage g S cover R c\<^sub>0 \<G>"
  shows "\<A>\<^bsub>\<G>,R,c\<^sub>0,g,S\<^esub> v ctx \<subseteq> cover v ctx"
