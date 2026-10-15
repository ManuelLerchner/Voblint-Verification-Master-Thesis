{
  /*
   * The strata are drawn from window.VOBLINT_STATS.sessions, which the site build reads
   * from the ROOT files and theory imports (scripts/session_graph.py). Without that data
   * the figure keeps the layers its markup shipped with. Either way, hovering a session
   * lights what it rests on directly and, lighter, everything below that in turn.
   */
  const strataLabel = (name) =>
    name === "TD"
      ? "TD"
      : name.replace("Voblint_Analysis_", "").replace("Voblint_", "").replace("_", " ");

  const STRATA_DESC = {
    TD: "The vendored top-down solver with side effects and its verification: strategy trees, update rules and the post-solution theorems. Parented on HOL and its libraries, including the AFP's Root_Balanced_Tree.",
    Voblint_VIMP:
      "The source language: syntax of surface VIMP, the eight machine kinds and their wraparound, variable identities, core VIMP's expressions and commands with the evaluation eval, the elaboration from surface VIMP, and the generic small-step semantics gpstep with calls, frames and returns. Core VIMP's step pstep instantiates it, and the initial stores are fixed here. Also the generated grammar. Parented on HOL-Library, using HOL-IMP and Deriving.",
    Voblint_CFG:
      "The graph model: nodes, intra and call edges, graph execution, activation traces and the collecting semantics, each generic in the evaluator. It never mentions the compiler.",
    Voblint_Domain:
      "What an abstract value is: sound-domain classes with concretization, the lattices of the numeric domains, the dead-code lift, pointwise states and backward filtering.",
    Voblint_Solver:
      "The strategy-tree equation language of the vendored solver, its post-solution vocabulary and the bridge into TD. It never sees a CFG.",
    Voblint_Compile:
      "The compiler to a CFG and its correctness: structural invariants, the forward simulation csim_step, the bridge from source runs to traces, and the invariant that the elaborated graph's traces keep every variable within its kind.",
    Voblint_Framework:
      "The D/G analysis framework: the analysis record and its contract, the local-specification interface every selectable analysis supplies, the equation generator, context routing and collecting soundness for an arbitrary CFG. No compiler, no domain.",
    Voblint_Exec:
      "The executable carrier: association-list states, and the transport of a solved system to the function-valued states the framework is stated over.",
    Voblint_Routing:
      "The equations of a compiled program under a context policy, and the finiteness arguments for its context-key spaces.",
    Voblint_Result:
      "The output end: what a solved routed system publishes, and the domain-free soundness endpoints that carry a source run into the result table.",
    Voblint_Nonrelational:
      "What a per-variable domain reuses: the class kind_int_domain of value operations per kind, and everything built from it once: transfers, guard refinement, procedure entry, the check classifier, their executable versions and the analysis run by the shared D/G pipeline, with their soundness.",
    Voblint_Analysis_Sign:
      "The Sign domain: the sign lattice's arithmetic and backward operations with their soundness, and the Sign analysis on machine kinds, an instance of kind_int_domain.",
    Voblint_Analysis_Interval:
      "The Interval domain: arithmetic, widening and narrowing with their soundness, and the Interval analysis on machine kinds, with wraparound or the kind's top on signed overflow and widening bounded by the kind's range.",
    Voblint_Analysis_Parity:
      "The Parity domain: the parity lattice's arithmetic with its soundness, and the Parity analysis on machine kinds, an instance of kind_int_domain.",
    Voblint_Analysis_Congruence:
      "The Congruence domain: arithmetic, including the remainder, with its soundness, and the Congruence analysis on machine kinds, with classes normalized modulo the kind's width.",
    Voblint_Analysis_Int:
      "The refinement modes and reduction machinery of the Int product, and Int on machine kinds: the reduced product of Interval and Congruence, after Goblint's IntDomTuple.",
    Voblint_Analysis_Order:
      "The relational Order analysis over variable identities. It supplies its local specification directly, without the class, and answers comparisons to the other analyses.",
    Voblint_CLI:
      "The selected analyses run as one combined state under every global update rule and context policy, with its soundness for any distinct, nonempty selection. run_voblint exposes Sign, Interval, Parity, Congruence, Int and relational Order to the CLI and browser, with the arithmetic diagnostics, and proves the source-level soundness results.",
    Voblint_Codegen:
      "The export_code declaration that writes the analyzer out as one OCaml module, on top of Voblint_CLI and last in ROOTS.",
  };

  /* A short role per session; a layer's name lists the roles of what lies in it. */
  const STRATA_ROLE = {
    TD: "solver",
    Voblint_VIMP: "language",
    Voblint_CFG: "graph",
    Voblint_Domain: "values",
    Voblint_Solver: "solver interface",
    Voblint_Compile: "compiler",
    Voblint_Framework: "framework",
    Voblint_Exec: "executable carrier",
    Voblint_Routing: "routing",
    Voblint_Result: "result",
    Voblint_Nonrelational: "per-variable analysis builder",
    Voblint_Analysis_Sign: "analyses",
    Voblint_Analysis_Interval: "analyses",
    Voblint_Analysis_Parity: "analyses",
    Voblint_Analysis_Congruence: "analyses",
    Voblint_Analysis_Int: "Int product",
    Voblint_Analysis_Order: "analyses",
    Voblint_CLI: "entry point",
    Voblint_Codegen: "code export",
  };

  const BEDROCK = "Isabelle/HOL";
  const EXAMPLES = "Voblint_Examples_*";
  const isExample = (name) => name.startsWith("Voblint_Examples");
  const strataCount = (n) => Number(n).toLocaleString("en-US");
  const plural = (n, one, many) => `${strataCount(n)} ${n === 1 ? one : many}`;

  const roleTitle = (names) => {
    const roles = [...new Set(names.map((n) => STRATA_ROLE[n] ?? strataLabel(n)))];
    const text =
      roles.length > 1 ? `${roles.slice(0, -1).join(", ")} and ${roles.at(-1)}` : roles[0];
    return text.charAt(0).toUpperCase() + text.slice(1);
  };

  /* Sizes: a layer is MIN px plus height per line; sessions share its width by lines, never under MINW. */
  const W = 670;
  const X0 = 320;
  const TOP = 14;
  const MIN = 22;
  const PER_LINE = 0.0032;
  const BED = 36;
  const MINW = 104;

  const shareWidths = (lines) => {
    if (lines.length === 1) return [W];
    let widths = lines.map((l) => (W * l) / lines.reduce((a, b) => a + b, 0));
    for (let round = 0; round < lines.length; round++) {
      const small = new Set(widths.flatMap((w, i) => (w < MINW ? [i] : [])));
      if (!small.size) break;
      const rest = lines.reduce((sum, l, i) => (small.has(i) ? sum : sum + l), 0);
      const budget = W - MINW * small.size;
      widths = lines.map((l, i) => (small.has(i) ? MINW : (budget * l) / rest));
    }
    return widths;
  };

  function buildStrata(svg, sessions) {
    const core = sessions.filter((s) => !isExample(s.name));
    const examples = sessions.filter((s) => isExample(s.name));
    const sum = (list, key) => list.reduce((a, s) => a + s[key], 0);
    const depths = [...new Set(core.map((s) => s.depth))].sort((a, b) => b - a);
    const lowestExample = examples.reduce(
      (low, s) => (!low || s.depth < low.depth ? s : low),
      null,
    );

    const rows = [];
    if (examples.length) {
      rows.push({
        key: "examples",
        title: "Examples and regressions",
        parts: [
          {
            name: EXAMPLES,
            label: `${examples.length} example sessions`,
            href: "Voblint/index.html",
            lines: sum(examples, "lines"),
            meta: `${plural(examples.length, "session", "sessions")} · ${plural(sum(examples, "theories"), "theory", "theories")} · ${strataCount(sum(examples, "lines"))} lines · ${plural(sum(examples, "proofs"), "lemma", "lemmas")}`,
            rests: [...new Set(examples.flatMap((s) => s.rests_on))]
              .filter((n) => !isExample(n))
              .sort(),
            info: `Executable runs and regressions, one session per folder, most parented on the analysis session its witnesses exercise, with the Voblint capstone on top. Drawn as one layer at the surface; individually they sit as low as ${lowestExample.name}.`,
          },
        ],
      });
    }
    for (const depth of depths) {
      const names = core.filter((s) => s.depth === depth).sort((a, b) => b.lines - a.lines);
      rows.push({
        key: `d${depth}`,
        title: roleTitle(names.map((s) => s.name)),
        parts: names.map((s) => ({
          name: s.name,
          label:
            s.name === "Voblint_CLI"
              ? "CLI · five numeric analyses + Order"
              : s.name === "Voblint_Analysis_Order"
                ? "Order (relational)"
                : strataLabel(s.name),
          href: s.name === "TD" ? "Unsorted/TD/index.html" : `Voblint/${s.name}/index.html`,
          lines: s.lines,
          meta: `${plural(s.theories, "theory", "theories")} · ${strataCount(s.lines)} lines · ${plural(s.proofs, "lemma", "lemmas")}`,
          rests: s.rests_on,
          info: STRATA_DESC[s.name] ?? `The session in ${s.dir}.`,
        })),
      });
    }
    rows.push({
      key: "bedrock",
      title: "Bedrock",
      bedrock: true,
      parts: [
        {
          name: BEDROCK,
          label: "Isabelle/HOL · HOL-IMP · Deriving",
          href: "https://isabelle.in.tum.de/",
          meta: "the logic and its libraries; not counted",
          rests: [],
          info: "Isabelle/HOL, and the HOL-IMP library and AFP entry Deriving that Voblint_VIMP uses. Every layer above rests on the kernel checking its proofs.",
        },
      ],
    });

    const markup = [];
    let y = TOP;
    for (const row of rows) {
      const lines = row.parts.map((p) => p.lines ?? 0);
      const h = row.bedrock ? BED : Math.round(MIN + lines.reduce((a, b) => a + b, 0) * PER_LINE);
      const widths = shareWidths(lines);
      const depthClass = /^d(\d+)$/.test(row.key)
        ? `stratum-d${Math.min(Number(row.key.slice(1)), 11)}`
        : `stratum-${row.key}`;
      markup.push(
        `<g class="stratum ${depthClass}" data-layer="${row.key}">` +
          `<text class="stratum-name" x="${X0 - 14}" y="${(y + h / 2 + 4).toFixed(0)}" text-anchor="end">${escapeText(row.title)}</text>`,
      );
      let x = X0;
      row.parts.forEach((part, i) => {
        const w = widths[i];
        const external = part.href.startsWith("http") ? ' target="_blank" rel="noreferrer"' : "";
        markup.push(
          `<a class="stratum-part" href="${part.href}"${external} data-name="${escapeText(part.name)}" data-meta="${escapeText(part.meta)}" data-rests="${part.rests.join(" ")}" data-info="${escapeText(part.info)}">` +
            `<rect x="${x.toFixed(1)}" y="${y}" width="${w.toFixed(1)}" height="${h}"/>` +
            `<text x="${(x + w / 2).toFixed(1)}" y="${(y + h / 2 + 4).toFixed(0)}">${escapeText(part.label)}</text></a>`,
        );
        x += w;
      });
      markup.push("</g>");
      y += h;
    }

    svg.innerHTML = markup.join("");
    svg.setAttribute("viewBox", `0 0 1000 ${y + 14}`);
  }

  for (const figure of document.querySelectorAll(".scene-strata")) {
    const svg = figure.querySelector(".strata-svg");
    const stats = window.VOBLINT_STATS;

    if (stats?.sessions?.length) {
      buildStrata(svg, stats.sessions);

      for (const element of figure.querySelectorAll("[data-stat]")) {
        const value = element.dataset.stat.split(".").reduce((obj, key) => obj?.[key], stats);
        if (value !== undefined) {
          element.textContent = strataCount(value);
        }
      }
    }

    const parts = [...figure.querySelectorAll(".stratum-part")];
    const direct = new Map(
      parts.map((p) => [p.dataset.name, p.dataset.rests.split(" ").filter(Boolean)]),
    );
    const examples = parts.find((p) => p.dataset.name.startsWith("Voblint_Examples"));
    const bedrock = parts.find((p) => p.dataset.name === BEDROCK);

    /* Everything a session rests on through any chain; the bedrock carries every session. */
    const below = (name) => {
      const seen = new Set();
      const todo = [...(direct.get(name) ?? [])];
      while (todo.length) {
        const next = todo.pop();
        if (seen.has(next)) continue;
        seen.add(next);
        todo.push(...(direct.get(next) ?? []));
      }
      if (name !== BEDROCK) seen.add(BEDROCK);
      return seen;
    };

    const name = figure.querySelector(".strata-info-name");
    const meta = figure.querySelector(".strata-info-meta");
    const rests = figure.querySelector(".strata-info-rests");
    const text = figure.querySelector(".strata-info-text");

    const show = (part) => {
      const directSet = new Set(direct.get(part.dataset.name));
      if (!directSet.size && part !== bedrock) directSet.add(BEDROCK);
      const all = below(part.dataset.name);
      const transitive = [...all].filter((n) => !directSet.has(n));

      for (const other of parts) {
        const n = other.dataset.name;
        other.classList.toggle("is-current", other === part);
        other.classList.toggle("is-support", directSet.has(n));
        other.classList.toggle("is-support-transitive", !directSet.has(n) && all.has(n));
        other
          .closest(".stratum")
          .classList.toggle("is-current", other.closest(".stratum") === part.closest(".stratum"));
      }

      const codes = (list) =>
        list.map((n) => `<code>${escapeText(strataLabel(n))}</code>`).join(", ");
      svg.classList.add("has-current");
      name.innerHTML = `<code>${escapeText(part.dataset.name)}</code>`;
      meta.textContent = part.dataset.meta;
      rests.innerHTML =
        part === bedrock
          ? "Rests on nothing: the kernel checks every proof above it."
          : `Rests directly on ${codes([...directSet])}` +
            (transitive.length
              ? `, and transitively on ${transitive.length} more: ${codes(transitive)}`
              : "") +
            ".";
      text.textContent = part.dataset.info;
    };

    for (const part of parts) {
      part.addEventListener("pointerenter", () => show(part));
      part.addEventListener("focus", () => show(part));
    }

    show(parts.find((p) => p.dataset.name === "Voblint_CLI") ?? examples ?? parts[0]);
  }
}
