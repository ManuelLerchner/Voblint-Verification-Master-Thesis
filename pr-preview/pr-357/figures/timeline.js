/* Further reading: the reading list itself, placed on one time axis */
{
  const AXIS_Y = 96;
  const DOT_R = 7;
  const STACK = 19;

  /* Four papers predate 1990 and the rest cluster after 2010, so the axis skips the gap. */
  const EARLY = { from: 1976, to: 1990, x0: 40, x1: 262 };
  const LATE = { from: 2008, to: 2027, x0: 318, x1: 975 };

  const xOf = (year) => {
    const span = year <= EARLY.to ? EARLY : LATE;
    return span.x0 + ((year - span.from) / (span.to - span.from)) * (span.x1 - span.x0);
  };

  const node = (name, attrs, parent) => {
    const el = document.createElementNS(SVG_NS, name);
    for (const [key, value] of Object.entries(attrs)) {
      el.setAttribute(key, value);
    }
    parent?.append(el);
    return el;
  };

  for (const figure of document.querySelectorAll(".scene-timeline")) {
    const section = figure.closest("section");
    const svg = figure.querySelector(".timeline-svg");
    const info = figure.querySelector(".timeline-info");
    const legend = figure.querySelector(".timeline-legend");
    const idle = info.innerHTML;

    const groups = [...section.querySelectorAll(".reading-group")];
    const entries = groups
      .flatMap((group, g) =>
        [...group.querySelectorAll(".reading-list > li[data-year]")].map((li) => ({
          id: li.id,
          g,
          year: Number(li.dataset.year),
          title: li.querySelector("a").textContent,
          meta: li.querySelector(".reading-meta").textContent,
        })),
      )
      .sort((a, b) => a.year - b.year || a.g - b.g);

    const axis = node("g", { class: "tl-axis" }, svg);
    for (const span of [EARLY, LATE]) {
      node("line", { x1: span.x0, y1: AXIS_Y, x2: span.x1, y2: AXIS_Y }, axis);
    }
    const gap = (EARLY.x1 + LATE.x0) / 2;
    for (const dx of [-6, 6]) {
      node(
        "line",
        { class: "tl-break", x1: gap + dx - 5, y1: AXIS_Y + 8, x2: gap + dx + 5, y2: AXIS_Y - 8 },
        axis,
      );
    }

    const years = new Set(entries.map((entry) => entry.year));
    for (let year = LATE.from; year < LATE.to; year += 2) {
      years.add(year);
    }
    for (const year of years) {
      const x = xOf(year);
      node("line", { x1: x, y1: AXIS_Y, x2: x, y2: AXIS_Y + 6 }, axis);
      node("text", { x, y: AXIS_Y + 24, "text-anchor": "middle" }, axis).textContent = year;
    }

    const perYear = new Map();
    const dots = node("g", { class: "tl-dots" }, svg);

    for (const entry of entries) {
      const level = perYear.get(entry.year) ?? 0;
      perYear.set(entry.year, level + 1);

      const link = node(
        "a",
        {
          href: `#${entry.id}`,
          class: `tl-dot g${entry.g}`,
          "data-group": entry.g,
        },
        dots,
      );
      node("title", {}, link).textContent = `${entry.title} (${entry.year})`;
      node("circle", { cx: xOf(entry.year), cy: AXIS_Y - 20 - level * STACK, r: DOT_R }, link);

      const show = () => {
        info.innerHTML = `<b>${escapeText(entry.title)}</b><span>${escapeText(entry.meta)}</span>`;
        figure.dataset.group = entry.g;
      };
      const hide = () => {
        info.innerHTML = idle;
        delete figure.dataset.group;
      };
      link.addEventListener("mouseenter", show);
      link.addEventListener("focus", show);
      link.addEventListener("mouseleave", hide);
      link.addEventListener("blur", hide);
    }

    groups.forEach((group, g) => {
      const item = document.createElement("li");
      item.className = `g${g}`;
      item.innerHTML = `<span class="swatch"></span>${escapeText(group.querySelector("h3").textContent)}`;
      item.addEventListener("mouseenter", () => {
        figure.dataset.group = g;
      });
      item.addEventListener("mouseleave", () => {
        delete figure.dataset.group;
      });
      legend.append(item);
    });
  }
}
