{
  /*
   * One step per clause of compile / compile_proc as it walks the counting loop. Nodes
   * carry data-pending (the step whose clause first hands out their number as a
   * continuation) and data-built (the step that compiles them); edges carry data-built.
   */
  const SOURCE_MORPH_STEPS = [
    {
      rule: null,
      text: "The program before compilation. The compiler numbers statements in the order it meets them, and every statement is compiled against the number of the statement that follows it.",
    },
    {
      rule: {
        name: "compile_proc",
        clause:
          "compile_proc Π p decl n =\n  (let r = n + csize (body decl); …\n   in … insert (FunctionEntry p, EA_Body p, ben)\n          (if falls_through (body decl)\n           then insert (Statement r, EA_Ret None p, FunctionResult p) E\n           else E) …)",
      },
      text: "`main` gets its two special nodes, `entry_main` and `exit_main`, and a body edge to where its body will begin. The body has `csize` 4, so its epilogue will be `Statement 4`: that number is reserved now, dashed, before any statement is compiled.",
    },
    {
      rule: {
        name: "compile (Assign x a)",
        clause:
          "compile Π p (Assign x a) k n =\n  (Suc n, Statement n, {(Statement n, EA_Assign x a, k)}, {})",
      },
      text: "`i = 0` becomes `Statement 0` with one edge to its continuation `k`. The `Seq` around it chose `k = Statement 1`, the number of the loop that comes next, so the edge can point there already.",
    },
    {
      rule: {
        name: "compile (While b c)",
        clause:
          "compile Π p (While b c) k n =\n  (let (n1, en1, E1, K1) = compile Π p c (Statement n) (Suc n)\n   in (n1, Statement n,\n       {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} ∪ E1, K1))",
      },
      text: "The loop head is `Statement 1`, with two edges out: `EA_Assume` into the body and `EA_AssumeNot` to the loop's continuation `Statement 3`. The body is compiled with the head itself as its continuation.",
    },
    {
      rule: {
        name: "compile (Assign x a)",
        clause:
          "compile Π p (Assign x a) k n =\n  (Suc n, Statement n, {(Statement n, EA_Assign x a, k)}, {})",
      },
      text: "`i = i + 1` is `Statement 2`. Its continuation is the loop head, so its edge is the back edge that makes the cycle.",
    },
    {
      rule: {
        name: "compile (Check l c)",
        clause:
          "compile Π p (Check l c) k n =\n  (Suc n, Statement n, {(Statement n, EA_Check l c, k)}, {})",
      },
      text: "The check becomes `Statement 3` with an `EA_Check` edge to the reserved epilogue `Statement 4`.",
    },
    {
      rule: {
        name: "compile_proc",
        clause:
          "compile_proc Π p decl n =\n  (let r = n + csize (body decl); …\n   in … insert (FunctionEntry p, EA_Body p, ben)\n          (if falls_through (body decl)\n           then insert (Statement r, EA_Ret None p, FunctionResult p) E\n           else E) …)",
      },
      text: "The body falls through its end, so the epilogue `Statement 4` gets the implicit `EA_Ret None main` edge into `exit_main`. Every edge into a result node is now a return edge.",
    },
    {
      rule: null,
      text: "The source has become a graph: one node per statement, and every node's outgoing edges point where the source would go next.",
    },
  ];

  for (const figure of document.querySelectorAll(".scene-source-morph")) {
    const lines = [...figure.querySelectorAll(".sm-line")];
    const parts = [...figure.querySelectorAll("[data-built]")];
    const caption = figure.querySelector(".sm-caption");
    const ruleBox = figure.querySelector(".sm-rule");
    const ruleName = figure.querySelector(".sm-rule-name");
    const ruleClause = figure.querySelector(".sm-rule-clause");
    let previous = null;

    /* A copy of the source line flies to the node it becomes. */
    const fly = (step) => {
      const line = lines.find((l) => Number(l.dataset.line) === step);
      const node = figure.querySelector(`[data-origin="${step}"] rect`);

      if (!line || !node || reducedMotion) {
        return;
      }

      const box = figure.getBoundingClientRect();
      const from = line.getBoundingClientRect();
      const to = node.getBoundingClientRect();
      const ghost = document.createElement("span");
      ghost.className = "sm-ghost";
      ghost.textContent = line.textContent.trim();
      ghost.style.left = `${from.left - box.left}px`;
      ghost.style.top = `${from.top - box.top}px`;
      figure.append(ghost);

      requestAnimationFrame(() => {
        ghost.style.transform = `translate(${to.left + to.width / 2 - from.left - ghost.offsetWidth / 2}px, ${to.top + to.height / 2 - from.top - ghost.offsetHeight / 2}px) scale(0.8)`;
        ghost.style.opacity = "0";
      });

      setTimeout(() => ghost.remove(), 900);
    };

    const render = (i) => {
      const state = SOURCE_MORPH_STEPS[i];

      for (const part of parts) {
        const built = i >= Number(part.dataset.built);
        const pending =
          !built && part.dataset.pending !== undefined && i >= Number(part.dataset.pending);
        part.classList.toggle("is-hidden", !built && !pending);
        part.classList.toggle("is-pending", pending);
        part.classList.toggle("is-new", built && Number(part.dataset.built) === i);
      }

      for (const line of lines) {
        const step = Number(line.dataset.line);
        line.classList.toggle("is-current", step === i);
        line.classList.toggle("is-peeled", step < i && i < SOURCE_MORPH_STEPS.length - 1);
      }

      figure.classList.toggle("is-final", i === SOURCE_MORPH_STEPS.length - 1);
      ruleBox.hidden = !state.rule;

      if (state.rule) {
        ruleName.innerHTML = `<code>${escapeText(state.rule.name)}</code>`;
        ruleClause.textContent = state.rule.clause;
      }

      caption.innerHTML = withCode(state.text);

      if (previous !== null && i === previous + 1) {
        fly(i);
      }

      previous = i;
    };

    const stepper = makeStepper(figure, {
      count: SOURCE_MORPH_STEPS.length,
      render,
      controls: figure.querySelector(".sm-controls"),
      chipsBox: figure.querySelector(".sm-steps"),
      interval: 3400,
    });

    /* Without motion, open on the finished graph rather than on the bare source. */
    if (reducedMotion) {
      stepper.show(SOURCE_MORPH_STEPS.length - 1);
    }
  }
}
