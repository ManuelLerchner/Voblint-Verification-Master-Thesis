{
  /*
   * The site build writes window.VOBLINT_STATS. Without it the markup keeps the figures
   * it shipped with and the breakdown stays hidden.
   */
  const SESSION_LABELS = {
    Program_Model: "Program model: VIMP, CFG, compiler",
    Abstract_Interpreter: "Abstract interpreter: domains, solver, framework",
    Analyses: "Analyses: five domains and their results",
    Executable_Surface: "Executable surface: run_voblint, code export",
    Examples: "Examples and regressions",
  };

  const CORPUS_LABELS = {
    precision: "precision",
    soundness: "soundness",
    "known-imprecision": "known imprecision",
    other: "graph, parser and tooling",
  };

  const formatCount = (n) => Number(n).toLocaleString("en-US");

  /* Shoelace area of a path made only of absolute M/L commands. */
  function polygonArea(d) {
    const points = [...d.matchAll(/(-?[\d.]+)[ ,]+(-?[\d.]+)/g)].map((m) => [
      Number(m[1]),
      Number(m[2]),
    ]);
    let twice = 0;

    points.forEach(([x1, y1], i) => {
      const [x2, y2] = points[(i + 1) % points.length];
      twice += x1 * y2 - x2 * y1;
    });

    return Math.abs(twice) / 2;
  }

  function statRow(label, detail, parts, total) {
    const row = document.createElement("div");
    row.className = "stats-row";

    const head = document.createElement("p");
    head.innerHTML = `<span>${escapeText(label)}</span><small>${escapeText(detail)}</small>`;

    const bar = document.createElement("div");
    bar.className = "stats-bar";
    bar.style.setProperty(
      "--share",
      `${((100 * parts.reduce((sum, p) => sum + p.value, 0)) / total).toFixed(2)}%`,
    );

    for (const part of parts) {
      const piece = document.createElement("span");
      piece.className = part.kind;
      piece.style.flexGrow = String(part.value);
      piece.title = `${part.title}: ${formatCount(part.value)}`;
      bar.append(piece);
    }

    row.append(head, bar);
    return row;
  }

  /*
   * The solver berg is the body mirrored and scaled by s about (832, 430). Its left tip is the
   * body's right tip (640, 300) and its lower edge the body's (575, 400), so the arrow and the
   * label's pointer follow the berg whatever size the counts give it.
   */
  function placeSolverLinks(figure, s) {
    const at = ([x, y]) => [832 - (x - 455) * s, 430 + (y - 262.5) * s];
    const [tipX, tipY] = at([640, 300]);
    const [lowX, lowY] = at([575, 400]);
    const startX = tipX - 8;
    const startY = tipY - 6;
    const midX = (startX + 618) / 2;

    figure
      .querySelector(".berg-link path")
      .setAttribute(
        "d",
        `M${startX.toFixed(0)} ${startY.toFixed(0)} Q ${midX.toFixed(0)} ${(Math.min(startY, 350) - 26).toFixed(0)} 618 350`,
      );
    const [by, solverName] = figure.querySelectorAll(".berg-link text");
    for (const [text, dy] of [
      [by, 30],
      [solverName, 46],
    ]) {
      text.setAttribute("x", midX.toFixed(0));
      text.setAttribute("y", ((startY + 350) / 2 + dy).toFixed(0));
    }

    const pointer = figure.querySelector(".berg-label.solver line");
    pointer.setAttribute("x2", (lowX - 8).toFixed(0));
    pointer.setAttribute("y2", (lowY - 2).toFixed(0));
  }

  /*
   * A contribution calendar: weeks as columns from the Monday before the first commit to the
   * build date, days as rows. Levels are quartiles of the busy days, so one record day does not
   * wash out the rest.
   */
  function drawCommitHeatmap(block, commits, built) {
    const SVG_NS = "http://www.w3.org/2000/svg";
    const DAY = 86400000;
    const CELL = 17;
    const GAP = 4;
    const LEFT = 30;
    const TOP = 20;
    const days = commits.days;
    const dates = Object.keys(days);
    const parse = (iso) => new Date(`${iso}T00:00:00Z`);
    const iso = (d) => d.toISOString().slice(0, 10);

    const first = parse(dates[0]);
    const last = new Date(Math.max(parse(dates[dates.length - 1]), parse(built)));
    const start = new Date(first.getTime() - ((first.getUTCDay() + 6) % 7) * DAY);
    const weeks = Math.floor((last - start) / DAY / 7) + 1;

    const busy = Object.values(days).sort((a, b) => a - b);
    const quantile = (q) => busy[Math.min(busy.length - 1, Math.floor(q * busy.length))];
    const cuts = [quantile(0.25), quantile(0.5), quantile(0.75)];
    const level = (n) => (n === 0 ? 0 : 1 + cuts.filter((c) => n > c).length);

    const svg = block.querySelector(".commit-heatmap");
    const width = LEFT + weeks * (CELL + GAP);
    const height = TOP + 7 * (CELL + GAP);
    svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
    svg.style.width = `${width}px`;
    svg.replaceChildren();

    const node = (name, attrs, text) => {
      const el = document.createElementNS(SVG_NS, name);
      for (const [k, v] of Object.entries(attrs)) el.setAttribute(k, String(v));
      if (text !== undefined) el.textContent = text;
      svg.append(el);
      return el;
    };

    ["Mon", "", "Wed", "", "Fri", "", ""].forEach((label, row) => {
      if (label)
        node("text", { class: "commit-day", x: 0, y: TOP + row * (CELL + GAP) + CELL - 2 }, label);
    });

    const monthFormat = new Intl.DateTimeFormat("en-US", { month: "short", timeZone: "UTC" });
    const dayFormat = new Intl.DateTimeFormat("en-US", {
      weekday: "short",
      day: "numeric",
      month: "short",
      year: "numeric",
      timeZone: "UTC",
    });
    let month = -1;
    const months = [];

    for (let w = 0; w < weeks; w++) {
      for (let row = 0; row < 7; row++) {
        const date = new Date(start.getTime() + (w * 7 + row) * DAY);
        if (date > last) break;
        if (row === 0 && date.getUTCMonth() !== month) {
          month = date.getUTCMonth();
          months.push({ w, label: monthFormat.format(date) });
        }
        const n = days[iso(date)] ?? 0;
        const cell = node("rect", {
          class: `commit-cell level-${level(n)}`,
          x: LEFT + w * (CELL + GAP),
          y: TOP + row * (CELL + GAP),
          width: CELL,
          height: CELL,
          rx: 3,
        });
        const title = document.createElementNS(SVG_NS, "title");
        title.textContent = `${n === 0 ? "No" : formatCount(n)} commit${n === 1 ? "" : "s"} on ${dayFormat.format(date)}`;
        cell.append(title);
      }
    }

    /* A month that starts too late in its first column to fit its name gives way to the next. */
    months
      .filter((m, i) => i === months.length - 1 || months[i + 1].w - m.w >= 3)
      .forEach((m) => {
        node("text", { class: "commit-month", x: LEFT + m.w * (CELL + GAP), y: 11 }, m.label);
      });

    const legend = block.querySelector(".commit-legend");
    const bounds = [
      "no commits",
      `1–${cuts[0]}`,
      `${cuts[0] + 1}–${cuts[1]}`,
      `${cuts[1] + 1}–${cuts[2]}`,
      `more than ${cuts[2]}`,
    ];
    legend.replaceChildren(
      Object.assign(document.createElement("li"), { textContent: "Less" }),
      ...bounds.map((label, i) => {
        const item = document.createElement("li");
        item.className = `commit-swatch level-${i}`;
        item.title = `${label} commits a day`;
        return item;
      }),
      Object.assign(document.createElement("li"), { textContent: "More" }),
    );

    /* Facts beside the calendar: totals and the longest run of consecutive days with commits. */
    let streak = 0;
    let best = 0;
    for (let d = new Date(first); d <= last; d = new Date(d.getTime() + DAY)) {
      streak = days[iso(d)] ? streak + 1 : 0;
      best = Math.max(best, streak);
    }
    const [busiest, busiestCount] = Object.entries(days).sort((a, b) => b[1] - a[1])[0];
    const facts = [
      [formatCount(commits.total), "commits"],
      [formatCount(dates.length), "days with commits"],
      [`${best} days`, "longest streak"],
      [
        formatCount(busiestCount),
        `commits on ${dayFormat.format(parse(busiest))}, the busiest day`,
      ],
    ];
    block.querySelector(".commit-facts").replaceChildren(
      ...facts.flatMap(([value, label]) => {
        const wrap = document.createElement("div");
        wrap.append(
          Object.assign(document.createElement("dt"), { textContent: value }),
          Object.assign(document.createElement("dd"), { textContent: label }),
        );
        return [wrap];
      }),
    );
    svg.setAttribute(
      "aria-label",
      `Commits per day from ${dayFormat.format(first)} to ${dayFormat.format(last)}: ${formatCount(commits.total)} commits on ${dates.length} days.`,
    );
  }

  for (const figure of document.querySelectorAll(".scene-iceberg")) {
    const stats = window.VOBLINT_STATS;

    if (!stats) {
      continue;
    }

    for (const element of figure.querySelectorAll("[data-stat]")) {
      const value = element.dataset.stat.split(".").reduce((obj, key) => obj?.[key], stats);

      if (value !== undefined) {
        element.textContent = formatCount(value);
      }
    }

    /* One area per line across all three shapes: the tip keeps its outline and scales in height,
       the solver berg is the body scaled about its centre. */
    const tip = figure.querySelector(".berg-tip");
    const body = figure.querySelector(".berg-body");
    const bodyArea = polygonArea(body.getAttribute("d"));
    const waterline = 110;
    const wanted = (bodyArea * stats.generated_ocaml) / stats.isabelle.lines;
    const scale = Math.min(2, wanted / polygonArea(tip.getAttribute("d")));
    const solver = figure.querySelector(".berg-solver");
    const shrink = Math.sqrt(stats.solver.used.lines / stats.isabelle.lines).toFixed(3);
    solver.setAttribute(
      "transform",
      solver.getAttribute("transform").replace(/scale\([^)]*\)/, `scale(-${shrink} ${shrink})`),
    );
    placeSolverLinks(figure, Number(shrink));
    tip.setAttribute(
      "d",
      tip
        .getAttribute("d")
        .replace(
          /(-?[\d.]+)[ ,]+(-?[\d.]+)/g,
          (_, x, y) => `${x} ${(waterline - (waterline - Number(y)) * scale).toFixed(1)}`,
        ),
    );

    const sessions = figure.querySelector('[data-stats="sessions"]');
    const widest = Math.max(...stats.isabelle.sessions.map((s) => s.lines));
    sessions.replaceChildren(
      ...stats.isabelle.sessions.map((s) =>
        statRow(
          SESSION_LABELS[s.name] ?? s.name,
          `${formatCount(s.lines)} lines · ${s.theories} theories · ${formatCount(s.proofs)} lemmas`,
          [
            { kind: "code", value: s.code, title: "proof and definitions" },
            { kind: "doc", value: s.doc, title: "documentation" },
            { kind: "blank", value: s.lines - s.code - s.doc, title: "blank" },
          ],
          widest,
        ),
      ),
    );

    const corpus = figure.querySelector('[data-stats="corpus"]');
    const kinds = Object.entries(stats.corpus.kinds);
    const most = Math.max(...kinds.map(([, n]) => n));
    corpus.replaceChildren(
      ...kinds.map(([kind, n]) =>
        statRow(
          CORPUS_LABELS[kind] ?? kind,
          `${n} programs`,
          [{ kind: `corpus-${kind}`, value: n, title: kind }],
          most,
        ),
      ),
    );

    /*
     * Groups of declaration and statement kinds; each entry sums the keywords it lists. Every
     * group draws one square per KIND_UNIT items, in its own hue, one shade per kind.
     */
    const KIND_UNIT = 10;
    const KIND_GROUPS = [
      [
        "Proved statements",
        1,
        [
          ["theorems", ["theorem"]],
          ["lemmas", ["lemma"]],
          ["corollaries", ["corollary"]],
        ],
      ],
      [
        "Definitions",
        2,
        [
          ["definitions", ["definition"]],
          ["recursive functions", ["fun", "primrec"]],
          ["abbreviations", ["abbreviation"]],
        ],
      ],
      [
        "Structure",
        5,
        [
          ["locales", ["locale"]],
          ["locale interpretations", ["interpretation", "global_interpretation", "sublocale"]],
          ["type classes", ["class"]],
          ["class instantiations", ["instantiation"]],
          ["named fact bundles", ["lemmas"]],
        ],
      ],
      [
        "Inductive definitions",
        3,
        [
          ["inductive predicates and sets", ["inductive", "inductive_set"]],
          ["inversion rules", ["inductive_cases"]],
        ],
      ],
      [
        "Types",
        4,
        [
          ["datatypes", ["datatype"]],
          ["records", ["record"]],
          ["type synonyms", ["type_synonym"]],
        ],
      ],
    ];

    const counts = { ...stats.isabelle.kinds.declarations, ...stats.isabelle.kinds.statements };
    const el = (tag, className, text) => {
      const node = document.createElement(tag);
      if (className) node.className = className;
      if (text !== undefined) node.textContent = text;
      return node;
    };

    figure.querySelector('[data-stats="kinds"]').replaceChildren(
      ...KIND_GROUPS.map(([title, hue, entries]) => {
        const kinds = entries
          .map(([label, keywords]) => ({
            label,
            keywords,
            total: keywords.reduce((sum, k) => sum + (counts[k] ?? 0), 0),
          }))
          .sort((a, b) => b.total - a.total);
        const groupTotal = kinds.reduce((sum, k) => sum + k.total, 0);

        const card = el("div", "kind-card");
        card.style.setProperty("--kind", `var(--kind-${hue})`);

        const head = el("div", "kind-head");
        head.append(el("p", "kind-title", title), el("p", "kind-total", formatCount(groupTotal)));

        const waffle = el("div", "kind-waffle");
        waffle.setAttribute("role", "img");
        waffle.setAttribute(
          "aria-label",
          `${title}: ${kinds.map((k) => `${formatCount(k.total)} ${k.label}`).join(", ")}`,
        );

        const legend = el("ul", "kind-legend");

        /* One focus per card: a square under the pointer or a hovered legend row picks its kind. */
        const focus = (run) => {
          waffle.classList.toggle("has-focus", run !== null);
          for (const other of waffle.querySelectorAll(".kind-run")) {
            other.classList.toggle("is-focus", other === run);
          }
        };
        waffle.addEventListener("pointermove", (event) => {
          const square = event.target.closest(".kind-run i");
          focus(square ? square.parentElement : null);
        });
        waffle.addEventListener("pointerleave", () => focus(null));

        kinds.forEach((kind, shade) => {
          const run = el("span", "kind-run");
          run.dataset.shade = String(shade);
          run.title = `${kind.label}: ${formatCount(kind.total)} (${kind.keywords.join(", ")})`;
          for (let i = 0; i < Math.ceil(kind.total / KIND_UNIT); i++) {
            run.append(el("i"));
          }
          waffle.append(run);

          const item = el("li");
          item.title = run.title;
          const swatch = el("span", "kind-swatch");
          swatch.dataset.shade = String(shade);
          item.append(swatch, el("b", "", formatCount(kind.total)), el("span", "", kind.label));
          legend.append(item);

          item.addEventListener("pointerenter", () => focus(run));
          item.addEventListener("pointerleave", () => focus(null));
        });

        card.append(head, waffle, legend);
        return card;
      }),
    );

    if (stats.commits) {
      drawCommitHeatmap(figure.querySelector(".stats-commits"), stats.commits, stats.date);
    } else {
      figure.querySelector(".stats-commits").hidden = true;
    }

    /* The commit the site was built from, linked on GitHub wherever the page names it. */
    const commitLink = () => {
      const link = document.createElement("a");
      link.href = `${REPO_URL}/commit/${stats.commit_sha}`;
      link.target = "_blank";
      link.rel = "noreferrer";
      link.append(Object.assign(document.createElement("code"), { textContent: stats.commit }));
      return link;
    };

    const stamp = figure.querySelector(".stats-stamp");
    stamp.replaceChildren(`Counted when the site was built, on ${stats.date}`);
    if (stats.commit_sha) {
      stamp.append(" at commit ", commitLink());
    }
    stamp.append(".");

    figure.querySelector(".stats-breakdown").hidden = false;
  }
}
