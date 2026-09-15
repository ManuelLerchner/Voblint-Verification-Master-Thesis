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
  const isaConst = (session, theory, name) =>
    `${ISA}/${session}/${theory}.html#${theory}.${name}%7Cconst`;

  const RULE_EXPLANATIONS = {
    run: {
      clause:
        "s0 ∈ cinit_stores (declared_global p)  ∧  star (pstep …) (main_body …, s0, []) (residual, s, frs)",
      text: "Start from an initial store (declared globals are `0`, locals arbitrary) with an empty call stack, and let the source semantics take any number of steps. It arrives at the rest of the program `residual`, the store `s` and the call frames `frs`. The run may stop anywhere, even inside a call.",
      link: isaConst("Voblint_VIMP", "VIMP_Proc", "pstep"),
      linkText: "pstep",
    },
    term: {
      clause: "config_terminates D rule ctx p",
      text: "The verified solver, instantiated for this domain `D`, globals rule and context policy, terminates on this program. HOL functions are total, so without this premise the answer could be an unspecified value that no execution computes. It is checked by running the analysis, never proved in general.",
      link: isaConst("Voblint_CLI", "Analysis_Certified", "config_terminates"),
      linkText: "config_terminates",
    },
    ans: {
      clause: "run_voblint D rule ctx p = Analysed res",
      text: "The exported analyzer, the function the playground calls, accepted the program as well-formed and returned the result `res`. Its checks and diagnostics are exactly what the page draws.",
      link: isaConst("Voblint_CLI", "Analysis_Run", "run_voblint"),
      linkText: "run_voblint",
    },
    v: {
      clause: "∃v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)",
      text: "The compiler's simulation relation matches the source state to a node `v` of the compiled graph, with the same store `s` and a matching stack `stk`. This is the forward simulation proved for the compiler.",
      link: isaConst("Voblint_Compile", "Simulation_Relation", "csim"),
      linkText: "csim",
    },
    coll: {
      clause: "s ∈ ltr_collect (declared_global p) (prog_cfg p) (cinit_stores …) v",
      text: "The graph's collecting semantics reaches node `v` with store `s`: some valid activation-local trace from an initial store ends there. Every analysis result is judged against this set.",
      link: isaConst("Voblint_CFG", "LTR_Collect", "ltr_collect"),
      linkText: "ltr_collect",
    },
    coll2: {
      clause: "s ∈ ltr_collect (declared_global p) (prog_cfg p) (cinit_stores …) v",
      text: "The graph's collecting semantics reaches node `v` with store `s`. Here it is a premise: the theorem speaks about every store the program can really have at `v`.",
      link: isaConst("Voblint_CFG", "LTR_Collect", "ltr_collect"),
      linkText: "ltr_collect",
    },
    cover: {
      clause: "analysis_result_covers D rule ctx p v s",
      text: "In the table this configuration built, some context solved at `v` holds an abstract state whose concretization contains `s`. Not every context has to: another activation's entry need not describe this store.",
      link: isaConst("Voblint_CLI", "Analysis_Certified", "analysis_result_covers"),
      linkText: "analysis_result_covers",
    },
    checks: {
      clause: "checks_sound_at res v s",
      text: "For every check the result lists at `v`: its verdict is not DEAD, `PROVED` implies its condition is true in `s`, and `REFUTED` implies it is false in `s`. `UNKNOWN` claims nothing.",
      link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "checks_sound_at"),
      linkText: "checks_sound_at",
    },
    next: {
      clause: "next_check residual = Some e",
      text: "The next command the source program will execute is `__voblint_check(e)`.",
      link: isaConst("Voblint_Compile", "Residual_Edges", "next_check"),
      linkText: "next_check",
    },
    listed: {
      clause: "∃c ∈ set (res_checks res). check_exp c = e ∧ s ∈ ltr_collect … (check_point c)",
      text: "The result lists a check `c` with condition `e`, at a node the store `s` really reaches. The node is found, not assumed: two identical procedure bodies list their checks separately.",
      link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "check_sites"),
      linkText: "check_sites",
    },
    holds: {
      clause:
        "(check_verdict c = Decided Check_Proved ⟶ truthy (aval e s)) ∧ (… Check_Refuted ⟶ ¬ truthy (aval e s))",
      text: "Evaluating `e` in the store `s` agrees with the verdict: true for `PROVED`, false for `REFUTED`.",
      link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "checks_sound_at"),
      linkText: "checks_sound_at",
    },
    listed2: {
      clause: "chk ∈ set (res_checks res)",
      text: "`chk` is one of the checks the result lists.",
      link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "check_sites"),
      linkText: "check_sites",
    },
    deadv: {
      clause: "check_verdict chk = Dead",
      text: "The result marks that check DEAD: no context solved at its node has a live state.",
      link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "checks_sound_at"),
      linkText: "checks_sound_at",
    },
    empty: {
      clause:
        "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores …) (check_point chk) = {}",
      text: "The collecting semantics has no store at the check's node: no run, from any initial store, ever gets there.",
      link: isaConst("Voblint_CFG", "LTR_Collect", "ltr_collect"),
      linkText: "ltr_collect",
    },
    nodiag: {
      clause: "∀d ∈ set (res_diagnostics res). diagnostic_point d ≠ v",
      text: "The result lists no arithmetic diagnostic, neither a warning nor an error, at node `v`.",
      link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "arithmetic_safe_at"),
      linkText: "arithmetic_safe_at",
    },
    div: {
      clause: "arithmetic_safe_at (prog_cfg p) v s",
      text: "For every arithmetic expression on the graph's edges at `v`, every divisor evaluates to a non-zero value in `s`. The corollary `run_voblint_arithmetic_intra_safe` states it for one edge at a time.",
      link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "arithmetic_safe_at"),
      linkText: "arithmetic_safe_at",
    },
    sites: {
      clause:
        "map (λchk. (check_point chk, check_exp chk)) (res_checks res) = check_sites (prog_cfg p)",
      text: "Read as (node, condition) pairs, the result's checks are exactly the check edges of the compiled graph, in the graph's edge order. Nothing is dropped or invented; pairing them with source lines happens outside the proof.",
      link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "check_sites"),
      linkText: "check_sites",
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
    "pstep",
    "declared_global",
    "prog_table",
    "main_body",
    "config_terminates",
    "run_voblint",
    "csim",
    "prog_cfg",
    "ltr_collect",
    "cinit_stores",
    "analysis_result_covers",
    "checks_sound_at",
    "next_check",
    "set",
    "res_checks",
    "check_exp",
    "check_point",
    "check_verdict",
    "truthy",
    "aval",
    "res_diagnostics",
    "diagnostic_point",
    "arithmetic_safe_at",
    "map",
    "check_sites",
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
          if (/^[A-Z][\w']+$/.test(word)) return span("ctor", word);
          if (ISABELLE_CONSTANTS.has(word)) return escapeText(word);
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
