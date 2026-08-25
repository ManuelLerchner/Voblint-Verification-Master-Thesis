(*  Emit the locale hierarchy as a Graphviz digraph.

    Isabelle's own `locale_deps` command renders the same graph into the
    Prover IDE's graph view, which cannot be included in a document.
    `Locale.pretty_locale_deps` exposes the underlying data, so the thesis
    figure is generated from the theory rather than drawn by hand and cannot
    drift from the sources.

    Load into a theory that imports everything the figure should cover, and
    evaluate:

      ML_file "thesis/tools/locale_graph.ML"
      ML \<open>Locale_Graph.write "thesis/shared/dot/locale_deps.dot"
                                 ["sound_domain", "dg_spec"] @{theory}\<close>

    The string list restricts the graph to locales whose name contains one of
    the given fragments; pass [] for everything, which is unreadably large in
    a session of this size.
*)

signature LOCALE_GRAPH =
sig
  val dot: string list -> theory -> string
  val write: string -> string list -> theory -> unit
end;

structure Locale_Graph: LOCALE_GRAPH =
struct

fun keep [] _ = true
  | keep fragments name = exists (fn f => String.isSubstring f name) fragments;

fun quote_id s = "\"" ^ Long_Name.base_name s ^ "\"";

fun node_line name =
  "  " ^ quote_id name ^
  " [shape=box, style=rounded, fontname=\"DejaVu Sans Mono\", fontsize=10];";

fun edge_line (parent, child) =
  "  " ^ quote_id parent ^ " -> " ^ quote_id child ^ ";";

fun dot fragments thy =
  let
    val deps = Locale.pretty_locale_deps thy;
    val wanted = filter (fn {name, ...} => keep fragments name) deps;
    val names = map #name wanted;
    val edges =
      maps (fn {name, parents, ...} =>
              map (rpair name) (filter (member (op =) names) parents))
           wanted;
  in
    cat_lines
      (["digraph locales {",
        "  rankdir=TB;",
        "  edge [arrowsize=0.7];"] @
       map node_line names @
       map edge_line edges @
       ["}"])
  end;

fun write path fragments thy =
  File.write (Path.explode path) (dot fragments thy);

end;
