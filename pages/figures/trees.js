{
  /*
   * Each tree here is a chain: every node has one continuation. "n" ties a node to the
   * do-notation lines carrying the same data-n; "walk" is what evaluating it under the
   * current σ reads, contributes or returns.
   */
  const TREES = {
    edge: {
      nodes: [
        { kind: "QueryL", label: "QueryL H", edge: "λh." },
        { kind: "Answer", label: "Answer (assume (i ≥ 5) h)" },
      ],
      walk: [
        "`QueryL H` reads `σ(H) = [0, 5]` and binds it to `h`. That read is the edge's only dependency.",
        "`Answer` applies the edge's action: `assume (i ≥ 5)` on `[0, 5]` gives `[5, 5]`.",
      ],
      post: "The answer `[5, 5]` is below `σ(X) = [5, 5]`, so `X` is covered. A transfer that also touched globals would add a `QueryG` to read them and a `Side` to write them; the shipped domains keep their whole state local, so their edges compile to exactly this shape.",
    },
    loop: {
      nodes: [
        { kind: "QueryL", label: "QueryL E", edge: "λe." },
        { kind: "QueryL", label: "QueryL B", edge: "λb." },
        { kind: "Answer", label: "Answer ([i := 0] e ⊔ [i := i + 1] b)" },
      ],
      walk: [
        "`QueryL E` reads `σ(E) = ⊤` and binds it to `e`.",
        "`QueryL B` reads `σ(B) = [0, 4]` and binds it to `b`.",
        "`Answer` returns `[0, 0] ⊔ [1, 5] = [0, 5]`.",
      ],
      post: "The answer `[0, 5]` is below `σ(H) = [0, 5]`, and the tree has no side effects, so `H` is covered.",
    },
    call: {
      nodes: [
        { kind: "QueryL", label: "QueryL (pp5, c)", edge: "λcaller." },
        { kind: "Side", label: "Side (Seed entry_f c') entry" },
        { kind: "QueryL", label: "QueryL (exit_f, c')", edge: "λcallee." },
        { kind: "Answer", label: "Answer (combine caller callee)" },
      ],
      walk: [
        "`QueryL (pp5, c)` reads the caller's state: `a = ⊤`.",
        "`enter` binds `n := 2`, the context policy picks `c' = [n ↦ [2, 2]]`, and `Side` contributes `n = [2, 2]` to the global unknown `Seed entry_f c'`.",
        "`QueryL (exit_f, c')` reads the callee's exit under that key: `#ret = [2, 2]`.",
        "`Answer` returns the combined state: `a = [2, 2]`.",
      ],
      post: "The answer is below `σ(pp6, c)`, and the side contribution `n = [2, 2]` is below `σ(Seed entry_f c')`. A post-solution bounds both.",
    },
    entry: {
      nodes: [
        { kind: "QueryG", label: "QueryG (Seed entry_f c)", edge: "λseed." },
        { kind: "Answer", label: "Answer seed" },
      ],
      walk: [
        "`QueryG (Seed entry_f c)` reads the global every call site's `Side` writes to. For `c = [n ↦ [2, 2]]` that is `n = [2, 2]`.",
        "`Answer` returns it as the entry state of this copy of `f`.",
      ],
      post: "The answer is below `σ(entry_f, c)`. Several call sites can write one seed; the Globals setting decides how their contributions combine.",
    },
  };

  function drawTree(svg, tree) {
    svg.innerHTML = `<defs><marker id="tree-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0 L10 5 L0 10 z" class="arrow-head"/></marker></defs>`;
    const x = 180;
    const gap = tree.nodes.length > 3 ? 92 : 118;
    const top = 44;

    tree.nodes.forEach((node, i) => {
      const y = top + i * gap;

      if (i > 0) {
        const edge = document.createElementNS(SVG_NS, "g");
        edge.setAttribute("class", "tree-edge");
        edge.innerHTML = `<line x1="${x}" y1="${y - gap + 22}" x2="${x}" y2="${y - 24}" marker-end="url(#tree-arrow)"/>`;
        const from = tree.nodes[i - 1];

        if (from.edge) {
          edge.innerHTML += `<text x="${x + 10}" y="${y - gap / 2 + 4}">${escapeText(from.edge)} …</text>`;
        }

        svg.append(edge);
      }

      const group = document.createElementNS(SVG_NS, "g");
      group.setAttribute("class", `tree-node tree-${node.kind.toLowerCase()}`);
      group.dataset.n = String(i + 1);
      const width = Math.min(340, 26 + node.label.length * 7.4);
      group.innerHTML =
        `<rect x="${x - width / 2}" y="${y - 20}" width="${width}" height="40" rx="${node.kind === "Answer" ? 20 : 8}"/>` +
        `<text x="${x}" y="${y + 5}">${escapeText(node.label)}</text>`;
      svg.append(group);
    });
  }

  for (const figure of document.querySelectorAll(".scene-trees")) {
    const svg = figure.querySelector(".trees-svg");
    const tabs = figure.querySelectorAll("[role=tab]");
    const codes = figure.querySelectorAll(".trees-code");
    const walk = figure.querySelector(".trees-walk");
    const post = figure.querySelector(".trees-post");
    const controls = figure.querySelector(".trees-controls");
    const chipsBox = figure.querySelector(".trees-steps");
    let tree = TREES.edge;
    let stepper = null;

    const mark = (n) => {
      for (const node of svg.querySelectorAll(".tree-node")) {
        node.classList.toggle("is-current", node.dataset.n === String(n));
      }

      for (const line of figure.querySelectorAll(".trees-code:not([hidden]) [data-n]")) {
        line.classList.toggle("is-current", line.dataset.n === String(n));
      }
    };

    const render = (i) => {
      mark(i + 1);
      walk.replaceChildren(
        ...tree.walk.slice(0, i + 1).map((text, j) => {
          const item = document.createElement("li");
          item.innerHTML = withCode(text);
          item.classList.toggle("is-current", j === i);
          return item;
        }),
      );
      post.innerHTML = i === tree.walk.length - 1 ? `<p>${withCode(tree.post)}</p>` : "";
      post.hidden = i !== tree.walk.length - 1;
    };

    const select = (name) => {
      tree = TREES[name];
      figure.dataset.tree = name;
      tabs.forEach((tab) => {
        tab.setAttribute("aria-selected", String(tab.dataset.tree === name));
      });
      codes.forEach((code) => {
        code.hidden = code.dataset.for !== name;
      });
      drawTree(svg, tree);
      stepper?.stop();
      chipsBox.replaceChildren();
      const fresh = controls.querySelector(".loop-play").cloneNode(true);
      controls.querySelector(".loop-play").replaceWith(fresh);
      stepper = makeStepper(figure, {
        count: tree.walk.length,
        render,
        controls,
        chipsBox,
        interval: 2600,
        autoplay: false,
      });
      stepper.show(tree.walk.length - 1);
    };

    for (const line of figure.querySelectorAll(".trees-code [data-n]")) {
      line.addEventListener("pointerenter", () => mark(line.dataset.n));
      line.addEventListener("pointerleave", () => mark(stepper.current() + 1));
    }

    tabs.forEach((tab) => {
      tab.addEventListener("click", () => select(tab.dataset.tree));
    });
    select("edge");
  }
}
