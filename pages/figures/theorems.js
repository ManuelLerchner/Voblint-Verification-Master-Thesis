{
  /*
   * The theorem explorer. A tab picks the theorem; hovering or focusing one of its
   * premises or conclusions lights the graph elements whose data-refs name it.
   */
  for (const figure of document.querySelectorAll(".scene-theorems")) {
    const svg = figure.querySelector(".cfg-svg");

    const highlight = (ref) => {
      for (const element of svg.querySelectorAll(".is-hl")) {
        element.classList.remove("is-hl");
      }

      svg.classList.toggle("has-hl", ref !== null);

      if (ref !== null) {
        for (const element of svg.querySelectorAll(`[data-refs~="${ref}"]`)) {
          element.classList.add("is-hl");
        }
      }
    };

    for (const item of figure.querySelectorAll(".rule-item[data-ref]")) {
      const panel = item.closest(".thm-panel");
      const explain = () => renderRuleExplanation(panel, item.dataset.ref);

      item.addEventListener("pointerenter", () => {
        highlight(item.dataset.ref);
        explain();
      });
      item.addEventListener("focus", () => {
        highlight(item.dataset.ref);
        explain();
      });
      item.addEventListener("pointerleave", () => highlight(null));
      item.addEventListener("blur", () => highlight(null));
    }
  }

  /*
   * What each premise and conclusion says, with the formal clause and the definition it
   * rests on. The panel keeps the last item shown, so its link stays reachable.
   */
  const ISA = "Voblint";
  const isaEntity = (kind) => (session, theory, name) =>
    `${ISA}/${session}/${theory}.html#${theory}.${name}%7C${kind}`;
  const isaConst = isaEntity("const");
  const isaFact = isaEntity("fact");

  const REACHING = isaConst("Voblint_Typed_CLI", "Typed_Run", "reaching");
  const REPORT = ["Voblint_CLI", "Analysis_Report"];
  const OBLIGATIONS = isaConst("Voblint_CLI", "Typed_Report", "tobligation_holds");

  const RULE_EXPLANATIONS = {
    run: {
      clause:
        "s0 ∈ tinit_stores (kenv_of ds)  ∧  star (tpstep (kenv_of ds) (typed_ptable p ds)) (main_body …, s0, []) (residual, s, frs)",
      text: "Start from an initial store (globals are `0`, every other variable holds some value of its kind) with an empty call stack, and let core VIMP's semantics run the elaborated program for any number of steps. It arrives at the rest of the program `residual`, the store `s` and the call frames `frs`. The run may stop anywhere, even inside a call.",
      link: isaConst("Voblint_Typed_CFG", "Typed_CFG", "tpstep"),
      linkText: "tpstep",
    },
    ans: {
      clause: "run_voblint conf ds p = Analysed res",
      text: "The exported analyzer, the function the playground calls, accepted the program and its kind declarations `ds`, its solve finished, and it returned the report `res`. Its checks and diagnostics are exactly what the page draws.",
      link: isaConst("Voblint_CLI", "Run_Voblint", "run_voblint"),
      linkText: "run_voblint",
    },
    v: {
      clause: "∃v stk. typed_ptable p ds, typed_cfg p ds, prog_main_name ⊢ (residual, s, frs) ≈ (v, s, stk)",
      text: "The compiler's simulation relation matches the reached source configuration with a configuration of the compiled graph at some node `v`, holding the same store `s`.",
      link: isaConst("Voblint_Compile", "Simulation_Relation", "csim"),
      linkText: "csim",
    },
    coll: {
      clause: "s ∈ reaching ds p v",
      text: "The graph's collecting semantics reaches node `v` with store `s`: some valid activation trace from an initial store ends there. Every analysis result is judged against this set.",
      link: REACHING,
      linkText: "reaching",
    },
    coll2: {
      clause: "s ∈ reaching ds p v",
      text: "The graph's collecting semantics reaches node `v` with store `s`. Here it is a premise: the theorem speaks about every store the program can really have at `v`.",
      link: REACHING,
      linkText: "reaching",
    },
    cover: {
      clause: "∃d. Lifted d ∈ report_states_at res v ∧ s ∈ tmcp.act_gamma ds … d",
      text: "Some state the report holds at `v`, under one of the contexts solved there, describes `s`, read through the concretization of the activated analyses. Not every context has to: another activation's state need not describe this store.",
      link: isaConst(...REPORT, "report_states_at"),
      linkText: "report_states_at",
    },
    checks: {
      clause: "¬ DEAD res v ∧ (∀c. PROVED res v c ⟶ truthy (teval c s)) ∧ (∀c. REFUTED res v c ⟶ ¬ truthy (teval c s))",
      text: "`v` is not DEAD, and every definite verdict the report gives at `v` is valid in `s`: `PROVED` means the condition is true in `s`, `REFUTED` that it is false. `UNKNOWN` claims nothing.",
      link: isaConst(...REPORT, "HAS_VERDICT"),
      linkText: "HAS_VERDICT",
    },
    safe0: {
      clause: "SAFE res v ⟶ (∀ob ∈ tobligations_at ds p v. s ⊨ ob)",
      text: "If the report names no arithmetic diagnostic at `v`, every obligation of the expressions evaluated there holds in `s`: no zero divisor, no signed overflow, no conversion out of range.",
      link: OBLIGATIONS,
      linkText: "tobligation_holds",
    },
    notdead: {
      clause: "check_verdict c ≠ Dead",
      text: "The check is not DEAD: the store `s` reaches its node, and the report describes every reaching store, which a DEAD node cannot.",
      link: isaConst(...REPORT, "DEAD"),
      linkText: "DEAD",
    },
    next: {
      clause: "next_check residual = Some (l, e)",
      text: "The next command the source program will execute is `__voblint_check(e)`, labelled `l`. The parser writes the check's own line and column into `l`.",
      link: isaConst("Voblint_Compile", "Residual_Edges", "next_check"),
      linkText: "next_check",
    },
    listed: {
      clause:
        "∃c ∈ set (report_checks res). check_label c = l ∧ check_exp c = e ∧ s ∈ reaching ds p (check_point c)",
      text: "The report lists a check `c` under the label `l`, with condition `e`, at a node the store `s` really reaches.",
      link: REACHING,
      linkText: "reaching",
    },
    holds: {
      clause:
        "(check_verdict c = Decided Check_Proved ⟶ truthy (teval e s)) ∧ (… Check_Refuted ⟶ ¬ truthy (teval e s))",
      text: "Evaluating `e` in the store `s` agrees with the verdict: true for `PROVED`, false for `REFUTED`. `teval` is core VIMP's evaluation, with every operation wrapped into its kind.",
      link: isaConst("Voblint_Typed", "Typed_Exp", "teval"),
      linkText: "teval",
    },
    deadv: {
      clause: "DEAD res v",
      text: "The report marks node `v` DEAD: every state it holds there is ⊥.",
      link: isaConst(...REPORT, "DEAD"),
      linkText: "DEAD",
    },
    empty: {
      clause: "reaching ds p v = {}",
      text: "The collecting semantics has no store at `v`: no run, starting with its globals at zero, ever gets there.",
      link: REACHING,
      linkText: "reaching",
    },
    nodiag: {
      clause: "SAFE res v",
      text: "The report lists no arithmetic diagnostic, neither a warning nor an error, at node `v`.",
      link: isaConst(...REPORT, "SAFE"),
      linkText: "SAFE",
    },
    div: {
      clause: "(v, a, w) ∈ intra (typed_cfg p ds) ⟹ e ∈ set (edge_expressions a) ⟹ ob ∈ set (tarith_obligations e) ⟹ s ⊨ ob",
      text: "For every expression on an edge leaving `v`, every obligation it raises holds in `s`: a divisor is non-zero, a signed operation's mathematical result lies in its kind, a narrowing conversion's operand fits its target. The theorem's other two parts state the same for a call's arguments and for a value returned to a caller.",
      link: OBLIGATIONS,
      linkText: "tobligation_holds",
    },
    distinct: {
      clause: "distinct (map check_label (report_checks res))",
      text: "No two rows of the report carry the same label. The renderers check this on the result and fail otherwise.",
      link: isaFact("Voblint_CLI", "Run_Voblint", "run_voblint_labelled_check_sound"),
      linkText: "run_voblint_labelled_check_sound",
    },
    sites: {
      clause:
        "∀c ∈ set (report_checks res). check_label c = l ⟶ check_exp c = e ∧ check_verdict c ≠ Dead ∧ (… Proved ⟶ truthy (teval e s)) ∧ (… Refuted ⟶ ¬ truthy (teval e s))",
      text: "A row exists under the label `l`, and every row under it is the row for the check about to run: same condition, not DEAD, and its verdict holds in `s`. The verdict shown at a check's line is therefore that check's.",
      link: isaFact("Voblint_CLI", "Run_Voblint", "run_voblint_labelled_check_sound"),
      linkText: "run_voblint_labelled_check_sound",
    },
  };

  function renderRuleExplanation(panel, ref) {
    const entry = RULE_EXPLANATIONS[ref];
    const target = panel.querySelector(".rule-explain");

    if (!entry || !target) {
      return;
    }

    const clause = document.createElement("pre");
    clause.className = "rule-clause";
    clause.innerHTML = highlightInner(entry.clause);

    const text = document.createElement("p");
    text.innerHTML = withCode(entry.text);

    const link = document.createElement("a");
    link.className = "isa-link";
    link.href = entry.link;
    link.textContent = `Definition of ${entry.linkText} ↗`;

    target.replaceChildren(clause, text, link);
  }

  /* Theorem tabs. */
  for (const figure of document.querySelectorAll(".scene-theorems")) {
    const tabs = figure.querySelectorAll("[role=tab]");

    for (const tab of tabs) {
      tab.addEventListener("click", () => {
        figure.dataset.theorem = tab.dataset.theorem;

        for (const other of tabs) {
          other.setAttribute("aria-selected", String(other === tab));
        }
      });
    }
  }

  /*
   * Colors the theorem statements the way Isabelle/jEdit distinguishes them: outer
   * keywords, the theorem name, free variables and variables bound by a quantifier
   * or lambda. Names that are constants of the development stay plain.
   */
  const ISABELLE_CONSTANTS = new Set([
    "star",
    "tpstep",
    "typed_ptable",
    "typed_cfg",
    "kenv_of",
    "tinit_stores",
    "main_body",
    "run_voblint",
    "prog_main_name",
    "reaching",
    "report_states_at",
    "tmcp",
    "act_gamma",
    "tactivation",
    "conf_analyses",
    "DEAD",
    "PROVED",
    "REFUTED",
    "SAFE",
    "tobligations_at",
    "next_check",
    "set",
    "report_checks",
    "check_label",
    "check_exp",
    "check_point",
    "check_verdict",
    "truthy",
    "teval",
    "intra",
    "edge_expressions",
    "tarith_obligations",
    "distinct",
    "map",
  ]);

  const span = (kind, text) => `<span class="isa-${kind}">${escapeText(text)}</span>`;

  function highlightInner(term) {
    const bound = new Set();

    for (const match of term.matchAll(/[∀∃λ]\s*([A-Za-z_][\w\s]*?)\s*(?:\.|∈)/g)) {
      for (const name of match[1].split(/\s+/)) {
        bound.add(name);
      }
    }

    return term.replace(
      /([A-Za-z_][\w']*)|([∀∃λ∈∧∨⟶¬≠=.])|([^A-Za-z_∀∃λ∈∧∨⟶¬≠=.]+)/g,
      (_whole, word, symbol, rest) => {
        if (word) {
          if (bound.has(word)) return span("bound", word);
          if (ISABELLE_CONSTANTS.has(word)) return escapeText(word);
          if (/^[A-Z][\w']+$/.test(word)) return span("ctor", word);
          return span("free", word);
        }

        return symbol ? span("op", symbol) : escapeText(rest);
      },
    );
  }

  function highlightIsabelle(source) {
    return source
      .split(/("[^"]*")/)
      .map((part, i) => {
        if (i % 2 === 1) {
          return span("quote", '"') + highlightInner(part.slice(1, -1)) + span("quote", '"');
        }

        return escapeText(part)
          .replace(
            /^(theorem|corollary|lemma)(\s+)([\w']+)/m,
            '<span class="isa-keyword">$1</span>$2<span class="isa-name">$3</span>',
          )
          .replace(/\b(assumes|shows|and|fixes|obtains)\b/g, '<span class="isa-sub">$1</span>');
      })
      .join("");
  }

  for (const pre of document.querySelectorAll(".thm-panel pre")) {
    pre.innerHTML = highlightIsabelle(pre.textContent);
  }
}
