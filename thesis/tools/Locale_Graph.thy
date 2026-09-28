theory Locale_Graph
  imports Voblint_Examples.Voblint
begin

text \<open>
  Writes the thesis's locale hierarchy (\<open>thesis/shared/dot/locale_deps.dot\<close>).
  Run through \<open>pixi run thesis-locale-graph\<close>, which loads this theory on the
  \<open>Voblint_Examples\<close> heap. The fragments select the framework's interface
  locales; every locale whose name contains one of them is drawn.
\<close>

ML_file "locale_graph.ML"

ML \<open>
  File.write
    (Path.append (Resources.master_directory \<^theory>)
       (Path.explode "../shared/dot/locale_deps.dot"))
    (Locale_Graph.dot
       ["numeric_domain", "analysis", "dg_", "routed", "ltr_coverage", "transfer"]
       \<^theory> ^ "\n")
\<close>

end
