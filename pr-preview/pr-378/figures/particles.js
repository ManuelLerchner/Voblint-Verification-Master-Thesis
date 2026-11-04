{
  /*
   * The value of x at each node, from `cli/voblint --analysis interval --dot` on the
   * "multiples-of-three" example. lo/hi are ±Infinity for an unbounded side. Runs only ever
   * reach multiples of three, which no interval can express, so every band admits integers
   * that no run has.
   */
  const PT_NODES = {
    pp2: { x: 380, y: 60, code: "if (x > 0)", lo: -Infinity, hi: Infinity, value: "⊤" },
    pp3: { x: 190, y: 210, code: "if (x < 3)", lo: 1, hi: Infinity, value: "[1, +∞]" },
    pp6: { x: 570, y: 210, code: "if (x > 5)", lo: -Infinity, hi: 0, value: "[−∞, 0]" },
    pp4: {
      x: 190,
      y: 360,
      code: "check(x == 1)",
      lo: 1,
      hi: 2,
      value: "[1, 2]",
      verdict: "UNKNOWN",
    },
    pp7: { x: 570, y: 360, code: "check(x == 6)", bot: true, value: "⊥", verdict: "DEAD" },
    pp9: { x: 380, y: 510, code: "end of main", lo: -Infinity, hi: Infinity, value: "⊤" },
  };

  const PT_LOW = -12;
  const PT_HIGH = 12;
  const PT_DX = 9;
  const PT_HOP = 620;
  const PT_STAGGER = 170;
  const PT_RUNS = [0, 3, -2, 1, -4, 4, -1, 2, -3];

  /* The route a run with this x takes through the graph. */
  const ptRoute = (x) =>
    x > 0
      ? x < 3
        ? ["pp2", "pp3", "pp4", "pp9"]
        : ["pp2", "pp3", "pp9"]
      : x > 5
        ? ["pp2", "pp6", "pp7", "pp9"]
        : ["pp2", "pp6", "pp9"];
  const ptSlot = (node, v) => ({
    x: node.x - ((PT_HIGH - PT_LOW) * PT_DX) / 2 + (v - PT_LOW) * PT_DX,
    y: node.y + 30,
  });
  const ptReached = (name, v) =>
    mod(v, 3) === 0 && PT_RUNS.some((n) => 3 * n === v && ptRoute(v).includes(name));

  const svgEl = (name, attrs, text) => {
    const el = document.createElementNS(SVG_NS, name);
    for (const [key, value] of Object.entries(attrs)) {
      el.setAttribute(key, String(value));
    }
    if (text !== undefined) {
      el.textContent = text;
    }
    return el;
  };

  for (const figure of document.querySelectorAll(".scene-particles")) {
    const nodesLayer = figure.querySelector(".pt-nodes");
    const routesLayer = figure.querySelector(".pt-routes");
    const flight = figure.querySelector(".pt-flight");
    const tabs = figure.querySelectorAll(".pt-modes [role=tab]");
    const dots = {};

    /* Each drawn edge as path data, so a particle can travel along its actual geometry. */
    const edgePaths = {};
    for (const edge of figure.querySelectorAll(".pt-edges [data-from]")) {
      edgePaths[`${edge.dataset.from}>${edge.dataset.to}`] =
        edge.tagName === "line"
          ? `L${edge.getAttribute("x1")} ${edge.getAttribute("y1")} L${edge.getAttribute("x2")} ${edge.getAttribute("y2")}`
          : edge.getAttribute("d").replace(/^\s*M/, "L");
    }

    /* A hop leaves its slot, joins the edge at its start, follows it, and drops to the next slot. */
    const hopPath = (a, b, key) => {
      const path = svgEl("path", {
        d: `M${a.x} ${a.y} ${key ? edgePaths[key] : ""} L${b.x} ${b.y}`,
      });
      routesLayer.append(path);
      return { path, length: path.getTotalLength() };
    };

    for (const [name, node] of Object.entries(PT_NODES)) {
      const group = svgEl("g", { class: `pt-node${node.bot ? " is-bot" : ""}` });
      const half = ((PT_HIGH - PT_LOW) * PT_DX) / 2 + 10;
      const left = node.x - half;
      const right = node.x + half;
      const y = node.y + 30;

      group.append(
        svgEl("rect", {
          class: "pt-label-box",
          x: node.x - 96,
          y: node.y - 13,
          width: 192,
          height: 26,
          rx: 7,
        }),
      );
      group.append(
        svgEl("text", { class: "pt-label", x: node.x, y: node.y + 5 }, `${name} · ${node.code}`),
      );

      if (node.verdict) {
        group.append(
          svgEl(
            "text",
            {
              class: `pt-verdict ${node.verdict.toLowerCase()}`,
              x: node.x + 104,
              y: node.y + 5,
              "text-anchor": "start",
            },
            node.verdict,
          ),
        );
      }

      group.append(svgEl("line", { class: "pt-axis", x1: left, x2: right, y1: y, y2: y }));

      if (!node.bot) {
        const bandLeft = node.lo === -Infinity ? left - 4 : ptSlot(node, node.lo).x - 7;
        const bandRight = node.hi === Infinity ? right + 4 : ptSlot(node, node.hi).x + 7;
        group.append(
          svgEl("rect", {
            class: "pt-band",
            x: bandLeft,
            y: y - 10,
            width: bandRight - bandLeft,
            height: 20,
            rx: 10,
          }),
        );

        if (node.lo === -Infinity) {
          group.append(
            svgEl("path", {
              class: "pt-band-tail",
              d: `M${left - 4} ${y - 6} L${left - 13} ${y} L${left - 4} ${y + 6}`,
            }),
          );
        }
        if (node.hi === Infinity) {
          group.append(
            svgEl("path", {
              class: "pt-band-tail",
              d: `M${right + 4} ${y - 6} L${right + 13} ${y} L${right + 4} ${y + 6}`,
            }),
          );
        }
      }

      group.append(
        svgEl(
          "text",
          { class: "pt-value", x: node.x, y: y + 40 },
          node.bot ? "x ∈ ⊥: no store" : `x ∈ ${node.value}`,
        ),
      );

      dots[name] = new Map();
      for (let v = PT_LOW; v <= PT_HIGH; v++) {
        const slot = ptSlot(node, v);
        if (v % 6 === 0) {
          group.append(svgEl("text", { class: "pt-tick", x: slot.x, y: y + 24 }, String(v)));
        }

        /* Integers the band admits that no run reaches: the price of the interval's shape. */
        if (!node.bot && v >= node.lo && v <= node.hi && !ptReached(name, v)) {
          group.append(svgEl("circle", { class: "pt-hole", cx: slot.x, cy: y, r: 2.4 }));
        }

        const dot = svgEl("circle", { class: "pt-dot", cx: slot.x, cy: y, r: 4.5 });
        group.append(dot);
        dots[name].set(v, dot);
      }

      nodesLayer.append(group);
    }

    /* Final state first: every dot a run leaves, so the figure is complete without motion. */
    const settle = () => {
      flight.replaceChildren();
      routesLayer.replaceChildren();
      for (const n of PT_RUNS) {
        for (const name of ptRoute(3 * n)) {
          dots[name].get(3 * n).classList.add("is-landed");
        }
      }
    };

    let frame = 0;
    let resume = null;

    /* Offscreen, the animation stops requesting frames; the class change brings it back. */
    new MutationObserver(() => {
      if (resume && !figure.classList.contains("is-offscreen")) {
        const go = resume;
        resume = null;
        go();
      }
    }).observe(figure, { attributes: true, attributeFilter: ["class"] });

    const setMode = (mode) => {
      figure.dataset.mode = mode;
      tabs.forEach((tab) => {
        tab.setAttribute("aria-selected", String(tab.dataset.mode === mode));
      });
    };

    const play = () => {
      cancelAnimationFrame(frame);
      for (const map of Object.values(dots)) {
        for (const dot of map.values()) {
          dot.classList.remove("is-landed");
        }
      }
      flight.replaceChildren();
      routesLayer.replaceChildren();

      if (reducedMotion) {
        settle();
        return;
      }

      const runs = PT_RUNS.map((n, k) => {
        const v = 3 * n;
        const route = ptRoute(v);
        const points = [
          { x: ptSlot(PT_NODES.pp2, v).x, y: -10 },
          ...route.map((name) => ptSlot(PT_NODES[name], v)),
        ];
        const hops = points
          .slice(1)
          .map((b, i) => hopPath(points[i], b, i === 0 ? null : `${route[i - 1]}>${route[i]}`));
        const particle = svgEl("circle", {
          class: "pt-particle",
          r: 4.5,
          cx: points[0].x,
          cy: points[0].y,
        });
        flight.append(particle);
        return { v, route, hops, particle, delay: k * PT_STAGGER, landed: 0 };
      });

      let start = 0;
      let paused = 0;
      let last = 0;

      const tick = (now) => {
        if (!start) {
          start = now;
          last = now;
        }
        if (figure.classList.contains("is-offscreen")) {
          resume = () => {
            last = performance.now();
            frame = requestAnimationFrame(tick);
          };
          return;
        }
        paused += Math.max(0, now - last - 100);
        last = now;
        const t = now - start - paused;
        let active = false;

        for (const run of runs) {
          const hops = run.hops.length;
          const progress = Math.max(0, Math.min(hops, (t - run.delay) / PT_HOP));
          const i = Math.min(hops - 1, Math.floor(progress));
          const f = progress - i;
          const ease = f * f * (3 - 2 * f);
          const at = run.hops[i].path.getPointAtLength(run.hops[i].length * ease);
          run.particle.setAttribute("cx", at.x.toFixed(1));
          run.particle.setAttribute("cy", at.y.toFixed(1));

          while (run.landed < Math.floor(progress)) {
            dots[run.route[run.landed]].get(run.v).classList.add("is-landed");
            run.landed++;
          }

          if (progress < hops) {
            active = true;
          } else {
            run.particle.remove();
          }
        }

        if (active) {
          frame = requestAnimationFrame(tick);
        } else {
          settle();
          setTimeout(() => setMode("both"), 900);
        }
      };

      frame = requestAnimationFrame(tick);
    };

    tabs.forEach((tab) => {
      tab.addEventListener("click", () => setMode(tab.dataset.mode));
    });
    figure.querySelector(".pt-replay").addEventListener("click", () => {
      setMode("concrete");
      play();
    });
    figure.querySelector(".pt-modes").hidden = false;

    /* The runs start the first time the figure scrolls into view. */
    settle();
    if ("IntersectionObserver" in window && !reducedMotion) {
      const observer = new IntersectionObserver(
        (entries) => {
          if (entries.some((entry) => entry.isIntersecting)) {
            observer.disconnect();
            setMode("concrete");
            play();
          }
        },
        { threshold: 0.35 },
      );
      observer.observe(figure);
    }
  }
}
