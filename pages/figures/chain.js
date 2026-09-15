{
  /*
   * n at pp0 of the factorial program. Runs reach it with n = 2 and n = 1; the solver's
   * values are the interval analyzer's results under each context mode.
   */
  const CHAIN = {
    none: {
      buckets: [{ label: "c = ()", members: [1, 2] }],
      gamma: [{ label: "c = ()", low: -Infinity, high: 2 }],
      sets: {
        source: "{n = 2, n = 1}",
        collect: "{n = 2, n = 1}",
        activation: "() ↦ {n = 2, n = 1}",
        gamma: "() ↦ n ∈ [−∞, 2]",
      },
      link: "one context, so the single bucket is the whole set",
      note: "With one context for all of `f`, the bucket and the collecting semantics coincide. The solver's value is `[−∞, 2]` because the entry of `f` was widened, so the abstraction admits every `n` below `1` although no run has one.",
    },
    entry: {
      buckets: [
        { label: "c₁", members: [2] },
        { label: "c₂", members: [1] },
      ],
      gamma: [
        { label: "c₁", low: 2, high: 2 },
        { label: "c₂", low: 1, high: 1 },
      ],
      sets: {
        source: "{n = 2, n = 1}",
        collect: "{n = 2, n = 1}",
        activation: "c₁ = [n ↦ [2,2]] ↦ {n = 2}   c₂ = [n ↦ [1,1]] ↦ {n = 1}",
        gamma: "c₁ ↦ n ∈ [2, 2]   c₂ ↦ n ∈ [1, 1]",
      },
      link: "every trace has a context, so the buckets together are exactly the set",
      note: "Each depth of the recursion has its own context, so the set splits into two buckets and each bucket gets an exact interval. No store enters between rungs 3 and 4, and the check in `main` is proved.",
    },
  };

  for (const figure of document.querySelectorAll(".scene-chain")) {
    const tabs = figure.querySelectorAll("[role=tab]");
    const low = -4;
    const high = 3;
    const x0 = 110;
    const dx = 58;
    const xOf = (n) => x0 + (n - low) * dx;

    const drawRung = (svg, rung, data) => {
      const reached = (n) => n === 1 || n === 2;
      svg.replaceChildren();

      const axis = document.createElementNS(SVG_NS, "line");
      axis.setAttribute("class", "axis");
      axis.setAttribute("x1", "40");
      axis.setAttribute("x2", String(xOf(high) + 30));
      axis.setAttribute("y1", "34");
      axis.setAttribute("y2", "34");
      svg.append(axis);

      const groups =
        rung === "activation"
          ? data.buckets.map((b) => ({ label: b.label, has: (n) => b.members.includes(n) }))
          : rung === "gamma"
            ? data.gamma.map((g) => ({
                label: g.label,
                has: (n) => n >= g.low && n <= g.high,
                open: g.low === -Infinity,
              }))
            : [];

      for (const group of groups) {
        const members = [];
        for (let n = low; n <= high; n++) {
          if (group.has(n)) members.push(n);
        }
        const left = group.open ? 26 : xOf(members[0]) - 18;
        const right = xOf(members[members.length - 1]) + 18;
        const band = document.createElementNS(SVG_NS, "rect");
        band.setAttribute("class", "chain-band");
        band.setAttribute("x", String(left));
        band.setAttribute("y", "20");
        band.setAttribute("width", String(right - left));
        band.setAttribute("height", "28");
        band.setAttribute("rx", "14");
        svg.append(band);

        const label = document.createElementNS(SVG_NS, "text");
        label.setAttribute("class", "chain-band-label");
        label.setAttribute("x", String((left + right) / 2));
        label.setAttribute("y", "13");
        label.textContent = group.label;
        svg.append(label);
      }

      const inAny = (n) => groups.some((g) => g.has(n));

      for (let n = low; n <= high; n++) {
        const circle = document.createElementNS(SVG_NS, "circle");
        const kind = reached(n) ? "in" : rung === "gamma" && inAny(n) ? "extra" : "out";
        circle.setAttribute("cx", String(xOf(n)));
        circle.setAttribute("cy", "34");
        circle.setAttribute("r", kind === "out" ? "4" : "8");
        circle.setAttribute("class", `dot-${kind}`);
        svg.append(circle);

        const tick = document.createElementNS(SVG_NS, "text");
        tick.setAttribute("class", "chain-tick");
        tick.setAttribute("x", String(xOf(n)));
        tick.setAttribute("y", "62");
        tick.textContent = String(n);
        svg.append(tick);
      }

      const minus = document.createElementNS(SVG_NS, "text");
      minus.setAttribute("class", "chain-tick");
      minus.setAttribute("x", "40");
      minus.setAttribute("y", "62");
      minus.textContent = "−∞";
      svg.append(minus);
    };

    const render = (mode) => {
      const data = CHAIN[mode];
      figure.dataset.mode = mode;
      tabs.forEach((tab) => {
        tab.setAttribute("aria-selected", String(tab.dataset.mode === mode));
      });

      for (const rung of figure.querySelectorAll(".chain-rung")) {
        drawRung(rung.querySelector("svg"), rung.dataset.rung, data);
        rung.querySelector(".chain-set").textContent = data.sets[rung.dataset.rung];
      }

      for (const link of figure.querySelectorAll("[data-mode-link]")) {
        link.hidden = link.dataset.modeLink !== mode;
      }

      figure.querySelector(".chain-link-note").textContent = data.link;
      figure.querySelector(".chain-note").innerHTML = withCode(data.note);
    };

    tabs.forEach((tab) => {
      tab.addEventListener("click", () => render(tab.dataset.mode));
    });
    render(figure.dataset.mode);
  }
}
