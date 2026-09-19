{
  /*
   * Turns are call depths of the real runs; the spiral widens as x grows. Results are what
   * cli/voblint --analysis interval reports for each program and setting; "no answer" means
   * the run was killed at the bound given in SPIRAL_BOUND.
   */
  const SPIRAL_BOUND = 60;
  const CX = 300;
  const TOP = 58;
  const HEIGHT = 290;

  const NO = null;
  const SPIRAL_PROGRAMS = {
    grows: {
      fixture: "24-site-figures/03-recursion_grows_entry_state_diverges.vimp",
      turns: 7,
      endless: true,
      code: "fun f(x) {\n  __voblint_check(x >= 0);\n\n  f(x + 1);\n}\n\nfun main() {\n  f(0);\n}",
      grid: {
        join: { none: NO, cs1: NO, cs2: NO, cs3: NO, entry: NO },
        "per-origin": { none: NO, cs1: NO, cs2: NO, cs3: NO, entry: NO },
        warrow: {
          none: "[0,+∞]",
          cs1: "[0,0] | [1,+∞]",
          cs2: "[0,0] | [1,1] | [2,+∞]",
          cs3: "[0,0] | [1,1] | [2,2] | [3,+∞]",
          entry: NO,
        },
        "warrow-per-origin": {
          none: "[0,+∞]",
          cs1: "[0,0] | [1,+∞]",
          cs2: "[0,0] | [1,1] | [2,+∞]",
          cs3: "[0,0] | [1,1] | [2,2] | [3,+∞]",
          entry: NO,
        },
      },
    },
    bounded: {
      fixture: "24-site-figures/precision/26-recursion_bounded_entry_state_join.vimp",
      turns: 11,
      endless: false,
      code: "fun f(x) {\n  __voblint_check(x >= 0);\n\n  if (x < 10) {\n    f(x + 1);\n  }\n}\n\nfun main() {\n  f(0);\n}",
      grid: Object.fromEntries(
        ["join", "per-origin", "warrow", "warrow-per-origin"].map((g) => [
          g,
          {
            none: "[0,10]",
            cs1: "[0,0] | [1,10]",
            cs2: "[0,0] | [1,1] | [2,10]",
            cs3: "[0,0] | [1,1] | [2,2] | [3,10]",
            entry: "[0,0] | [1,1] | … | [10,10]",
          },
        ]),
      ),
    },
  };

  const GLOBALS = [
    ["join", "Join"],
    ["per-origin", "Join per origin"],
    ["warrow", "Warrow"],
    ["warrow-per-origin", "Warrow per origin"],
  ];
  const CONTEXTS = [
    ["none", "none"],
    ["cs1", "call string k=1"],
    ["cs2", "k=2"],
    ["cs3", "k=3"],
    ["entry", "entry state"],
  ];

  const TEXT = {
    grows: {
      join: "One context covers every depth, and Join adds each new entry to it: `[0, 0]`, `[0, 1]`, `[0, 2]`, … The value grows with every turn of the spiral, and the solve does not finish.",
      warrow:
        "One context covers every depth. Its entry value keeps growing, so warrowing jumps to `[0, +∞]` instead of following the spiral outward, and `x >= 0` is proved for every turn.",
      cs: "The call string keeps the last `k` call sites: `s₀` is the call in `main`, `s₁` the recursive one. The first `k` depths get contexts of their own with exact values. Every deeper call has the same `k` recursive sites, so they share one context, and warrowing cuts it off at `+∞`.",
      entry:
        "Entry-state contexts key each call by its entry state, and every depth enters with a new value: `x = 0`, `x = 1`, `x = 2`, … Each turn asks for yet another context, and the solve does not finish, even with warrowing. The growing chips illustrate that mechanism; only the time-out was measured.",
    },
    bounded: {
      join: "The spiral stops after eleven turns, so the one shared context only ever grows to `[0, 10]`. Join needs no widening here and finishes at once.",
      warrow:
        "Warrow reaches the same `[0, 10]` as Join on this program, so the settings that differ so sharply on the endless spiral agree once the recursion is bounded.",
      cs: "The first `k` depths get exact contexts, and the deeper calls share one context holding `[k, 10]`.",
      entry:
        "Every depth enters with a different value, but there are only eleven of them, so entry-state contexts finish with one exact context per turn, `[0, 0]` through `[10, 10]`.",
    },
  };

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

  for (const figure of document.querySelectorAll(".scene-recursion-spiral")) {
    const turnsLayer = figure.querySelector(".spiral-turns");
    const bands = figure.querySelector(".spiral-bands");
    const callsLayer = figure.querySelector(".spiral-calls");
    const chips = figure.querySelector(".spiral-chips");
    const bridge = figure.querySelector(".spiral-bridge");
    const codeBox = figure.querySelector(".spiral-code code");
    const programTabs = figure.querySelectorAll(".spiral-programs [data-program]");
    const tabs = figure.querySelectorAll(".spiral-modes [role=tab]");
    const kBox = figure.querySelector(".spiral-k");
    const kButtons = kBox.querySelectorAll("[data-k]");
    const result = figure.querySelector(".spiral-result");
    const timer = figure.querySelector(".spiral-timer");
    const caption = figure.querySelector(".spiral-caption");
    const tryLink = figure.querySelector(".spiral-try");
    const table = figure.querySelector(".spiral-table");
    let program = "grows";
    let mode = "warrow";
    let k = 2;
    let tick = null;
    let geo = null;

    /* f(0) on the narrow turn at the bottom, each deeper call one turn higher and wider;
       spacing and sizes adapt to the number of turns. */
    const geometry = (turns) => {
      const gap = HEIGHT / turns;
      return {
        gap,
        y: (d) => TOP + (turns - d) * gap,
        rx: (d) => 38 + (d * 226) / (turns - 1),
        ry: Math.min(16, gap * 0.36),
        r: Math.min(17, gap * 0.46),
      };
    };

    const drawSpiral = () => {
      const cfg = SPIRAL_PROGRAMS[program];
      geo = geometry(cfg.turns);
      turnsLayer.replaceChildren();
      callsLayer.replaceChildren();

      for (let d = 0; d < cfg.turns; d++) {
        const y = geo.y(d);
        const rx = geo.rx(d);
        const fade = cfg.endless && d >= cfg.turns - 2 ? " fading" : "";
        const last = d === cfg.turns - 1;

        if (!last || cfg.endless) {
          const nextRx = last ? rx + 226 / (cfg.turns - 1) : geo.rx(d + 1);
          turnsLayer.append(
            svgEl("path", {
              class: `turn-back${fade}`,
              d: `M${CX + rx} ${y} C ${CX + rx} ${y - geo.ry * 1.3}, ${CX - nextRx} ${y - geo.gap - geo.ry * 1.3}, ${CX - nextRx} ${y - geo.gap}`,
            }),
          );
        }

        turnsLayer.append(
          svgEl("path", {
            class: `turn-front${fade}`,
            d: `M${CX - rx} ${y} A ${rx} ${geo.ry} 0 0 0 ${CX + rx} ${y}`,
          }),
        );
        const call = svgEl("g", { class: `call${fade}` });
        call.append(svgEl("circle", { cx: CX, cy: y + geo.ry, r: geo.r }));
        /* Labels shrink with the circle so f(10) still fits on the tighter bounded spiral. */
        const size = Math.min(10.5, (1.9 * geo.r) / String(`f(${d})`).length);
        call.append(
          svgEl(
            "text",
            { x: CX, y: y + geo.ry + size * 0.36, style: `font-size: ${size.toFixed(1)}px` },
            `f(${d})`,
          ),
        );
        callsLayer.append(call);
      }

      const end = geo.y(cfg.turns) - 28;
      callsLayer.append(
        svgEl(
          "text",
          { class: "spiral-more", x: CX, y: end },
          cfg.endless ? "⋮ wider, forever" : "x = 10: no further call",
        ),
      );
    };

    const callY = (d) => geo.y(d) + geo.ry;

    const band = (from, to, label, cls) => {
      const cfg = SPIRAL_PROGRAMS[program];
      const bottom = callY(from) + geo.r + 4;
      const top = to === Infinity ? geo.y(cfg.turns) + 6 : callY(to) - geo.r - 4;
      bands.append(
        svgEl("rect", {
          class: `band ${cls}`,
          x: CX - geo.r - 12,
          y: top,
          width: 2 * geo.r + 24,
          height: bottom - top,
          rx: geo.r + 8,
        }),
      );
      const chip = svgEl("g", { class: `chip ${cls}` });
      const y = (Math.max(top, geo.y(cfg.turns)) + bottom) / 2;
      const h = Math.min(28, geo.gap - 6);
      chip.append(svgEl("line", { x1: CX + geo.r + 12, y1: y, x2: 572, y2: y }));
      chip.append(svgEl("rect", { x: 572, y: y - h / 2, width: 250, height: h, rx: h / 2 }));
      chip.append(svgEl("text", { x: 586, y: y + 4 }, label));
      chips.append(chip);
    };

    const clear = () => {
      bands.replaceChildren();
      chips.replaceChildren();
      clearInterval(tick);
      tick = null;
      timer.hidden = true;
    };

    const setBridge = (from) => {
      bridge.toggleAttribute("hidden", from === null);
      if (from !== null) {
        const y0 = callY(from);
        const y1 = geo.y(SPIRAL_PROGRAMS[program].turns);
        bridge
          .querySelector("path")
          .setAttribute("d", `M832 ${y0} C 890 ${y0 - 60}, 890 ${y1 + 60}, 832 ${y1}`);
        bridge.querySelector("text").setAttribute("y", String((y0 + y1) / 2));
      }
    };

    const csSites = (d) => (d < k ? [...Array(d).fill("s₁"), "s₀"] : Array(k).fill("s₁")).join(" ");

    /* The endless settings: contexts pile up turn by turn until the run is killed. */
    const drawEndless = (animate) => {
      const turns = SPIRAL_PROGRAMS[program].turns;
      let n = 0;
      const step = () => {
        bands.replaceChildren();
        chips.replaceChildren();
        const shown = Math.min(n, turns - 1);
        if (mode === "join") {
          band(0, shown, `one context: x ∈ [0, ${n}]`, "shared");
        } else {
          for (let d = 0; d <= shown; d++) band(d, d, `key x = [${d}, ${d}]`, "own");
        }
        const seconds = Math.min(SPIRAL_BOUND, Math.round((n / (turns - 1)) * SPIRAL_BOUND));
        timer.hidden = false;
        timer.textContent =
          n >= turns - 1
            ? `voblint: killed after ${SPIRAL_BOUND} s without an answer`
            : `solving… ${seconds} s`;
        n = n >= turns - 1 ? 0 : n + 1;
      };
      if (!animate) {
        n = turns - 1;
        step();
        return;
      }
      step();
      tick = setInterval(() => {
        if (!figure.classList.contains("is-offscreen")) {
          step();
        }
      }, 1100);
    };

    const answer = (value) =>
      value === NO
        ? `<span class="verdict unknown">no answer</span> <code>killed after ${SPIRAL_BOUND} s</code>`
        : `<span class="verdict proved">PROVED</span> <code>x = ${escapeText(value)}</code>`;

    const renderTable = () => {
      const grid = SPIRAL_PROGRAMS[program].grid;
      const head = `<thead><tr><th scope="col">Globals \\ context</th>${CONTEXTS.map(([, label]) => `<th scope="col">${label}</th>`).join("")}</tr></thead>`;
      const rows = GLOBALS.map(
        ([g, label]) =>
          `<tr><th scope="row">${label}</th>${CONTEXTS.map(([c]) => {
            const value = grid[g][c];
            return value === NO
              ? `<td class="none">no answer</td>`
              : `<td><code>${escapeText(value)}</code></td>`;
          }).join("")}</tr>`,
      ).join("");
      table.innerHTML = `${head}<tbody>${rows}</tbody>`;
    };

    const render = () => {
      clear();
      const cfg = SPIRAL_PROGRAMS[program];
      figure.dataset.program = program;
      figure.dataset.mode = mode;
      programTabs.forEach((tab) => {
        tab.setAttribute("aria-selected", String(tab.dataset.program === program));
      });
      tabs.forEach((tab) => {
        tab.setAttribute("aria-selected", String(tab.dataset.mode === mode));
      });
      kBox.hidden = mode !== "cs";
      kButtons.forEach((b) => {
        b.setAttribute("aria-pressed", String(Number(b.dataset.k) === k));
      });
      caption.innerHTML = withCode(TEXT[program][mode].replaceAll("`[k, 10]`", `\`[${k}, 10]\``));
      const globals = mode === "join" ? "join" : "warrow";
      const context = mode === "cs" ? `cs${k}` : mode === "entry" ? "entry" : "none";
      const value = cfg.grid[globals][context];
      result.innerHTML = answer(value);

      if (value === NO) {
        setBridge(null);
        drawEndless(!reducedMotion);
      } else if (mode === "cs") {
        for (let d = 0; d < k; d++) band(d, d, `[${csSites(d)}] ↦ x ∈ [${d}, ${d}]`, "own");
        band(
          k,
          cfg.endless ? Infinity : cfg.turns - 1,
          `[${csSites(k)}] ↦ x ∈ [${k}, ${cfg.endless ? "+∞" : 10}]`,
          "shared",
        );
        setBridge(cfg.endless ? k : null);
      } else if (mode === "entry") {
        for (let d = 0; d < cfg.turns; d++) band(d, d, `key x = [${d}, ${d}]`, "own");
        setBridge(null);
      } else {
        band(
          0,
          cfg.endless ? Infinity : cfg.turns - 1,
          `one context: x ∈ [0, ${cfg.endless ? "+∞" : 10}]`,
          "shared",
        );
        setBridge(cfg.endless && mode === "warrow" ? 0 : null);
      }

      const link = {
        join: "globals=join&context=none",
        warrow: "globals=warrow&context=none",
        cs: `globals=warrow&context=call-string&k=${k}`,
        entry: "globals=warrow&context=entry-state",
      }[mode];
      tryLink.href = `playground.html?fixture=${cfg.fixture}&analysis=interval&${link}`;
    };

    const selectProgram = (name) => {
      program = name;
      codeBox.textContent = SPIRAL_PROGRAMS[name].code;
      drawSpiral();
      renderTable();
      render();
    };

    programTabs.forEach((tab) => {
      tab.addEventListener("click", () => selectProgram(tab.dataset.program));
    });
    tabs.forEach((tab) => {
      tab.addEventListener("click", () => {
        mode = tab.dataset.mode;
        render();
      });
    });
    kButtons.forEach((b) => {
      b.addEventListener("click", () => {
        k = Number(b.dataset.k);
        render();
      });
    });
    figure.querySelector(".spiral-programs").hidden = false;
    selectProgram("grows");
  }
}
