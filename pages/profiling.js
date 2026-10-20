import * as Plot from "https://cdn.jsdelivr.net/npm/@observablehq/plot@0.6.16/+esm";
import * as d3 from "https://cdn.jsdelivr.net/npm/d3@7.9.0/+esm";

/*
 * The domains and context policies come from the snapshot, so a snapshot that measures more
 * of them shows them all. Known ones keep a fixed place, and with it their colour, whatever a
 * snapshot leaves out; contexts take the palette's first slots and domains the rest, so no
 * chart reuses a colour for both.
 */
const PALETTE = [
  "#2a78d6",
  "#eb6834",
  "#1baf7a",
  "#eda100",
  "#e87ba4",
  "#008300",
  "#6250d6",
  "#e34948",
];
const KNOWN_CONTEXTS = ["none", "entry-state", "call-string-1", "call-string-2"];
const KNOWN_DOMAINS = ["sign", "parity", "congruence", "interval", "int"];
let CONTEXTS = [];
let DOMAINS = [];
const ordered = (known, present) => [
  ...known.filter((x) => present.has(x)),
  ...[...present].filter((x) => !known.includes(x)).sort(),
];
const contextLabel = (c) => c.replace(/^call-string-(\d+)$/, "call-string k=$1");
const contextColor = (c) => PALETTE[Math.max(0, KNOWN_CONTEXTS.indexOf(c)) % 3];
const domainColor = (d) => PALETTE[3 + (Math.max(0, KNOWN_DOMAINS.indexOf(d)) % 5)];
const contextScale = () => ({
  domain: CONTEXTS,
  range: CONTEXTS.map(contextColor),
  legend: true,
  tickFormat: contextLabel,
});
const domainScale = () => ({ domain: DOMAINS, range: DOMAINS.map(domainColor), legend: true });
const axisStyle = {
  fontSize: 12,
  fontFamily: "inherit",
  background: "transparent",
  color: "#172126",
};

const $ = (id) => document.getElementById(id);
const fmtMs = (ms) =>
  ms >= 1000 ? `${(ms / 1000).toFixed(2)} s` : `${ms.toFixed(ms < 10 ? 1 : 0)} ms`;
const width = (el) => Math.max(320, el.clientWidth);

function segmented(container, options, initial, onChange) {
  container.replaceChildren(
    ...options.map(([value, label]) => {
      const b = document.createElement("button");
      b.type = "button";
      b.textContent = label;
      b.setAttribute("aria-pressed", String(value === initial));
      b.addEventListener("click", () => {
        for (const other of container.children) other.setAttribute("aria-pressed", "false");
        b.setAttribute("aria-pressed", "true");
        onChange(value);
      });
      return b;
    }),
  );
}

/* Browser/native ratios where the native solve is long enough for its clock to mean something. */
const RATIO_FLOOR_MS = 1;

function browserPairs(data) {
  const native = new Map(
    data.runs
      .filter((r) => r.status === "ok" && r.ms != null)
      .map((r) => [`${r.fixture}|${r.domain}|${r.context}`, r.ms]),
  );
  return data.browser
    .filter((b) => b.wasm_ms != null)
    .map((b) => ({ ...b, native: native.get(`${b.fixture}|${b.domain}|${b.context}`) }))
    .filter((b) => b.native != null);
}

function kpis(data, ok) {
  const slowest = d3.greatest(ok, (r) => r.ms);
  const ratios = browserPairs(data)
    .filter((b) => b.native >= RATIO_FLOOR_MS)
    .map((b) => b.wasm_ms / b.native);
  const items = [
    [
      `${new Set(data.runs.map((r) => r.fixture)).size}`,
      `fixtures, each under ${DOMAINS.length * CONTEXTS.length} configurations`,
    ],
    [d3.format(",")(data.runs.length), "native runs measured"],
    [fmtMs(d3.median(ok, (r) => r.ms)), "median native solve"],
    [
      fmtMs(slowest.ms),
      `slowest: ${slowest.fixture.split("/").pop()} (${slowest.domain}, ${contextLabel(slowest.context)})`,
    ],
    ratios.length
      ? [
          times(d3.median(ratios)),
          `median WebAssembly / native solve time, ${ratios.length} runs over ${RATIO_FLOOR_MS} ms`,
        ]
      : ["–", "no run long enough to compare the builds"],
  ];
  $("kpis").replaceChildren(
    ...items.map(([v, l]) => {
      const div = document.createElement("div");
      div.className = "kpi";
      div.innerHTML = `<div class="kpi-value"></div><div class="kpi-label"></div>`;
      div.firstChild.textContent = v;
      div.lastChild.textContent = l;
      return div;
    }),
  );
}

function tradeoff(data) {
  const configs = d3
    .rollups(
      data.runs,
      (rows) => {
        const ok = rows.filter((r) => r.status === "ok");
        const proved = d3.sum(ok, (r) => r.verdicts.PROVED);
        return {
          seconds: d3.sum(ok, (r) => r.ms) / 1000,
          proved,
          share: proved / Math.max(1, totalChecks(data)),
          ran: ok.length,
          rejected: rows.filter((r) => r.status === "rejected").length,
          timeouts: rows.filter((r) => r.status === "timeout").length,
        };
      },
      (r) => r.domain,
      (r) => r.context,
    )
    .flatMap(([domain, byCtx]) => byCtx.map(([context, v]) => ({ domain, context, ...v })));

  const title = (d) =>
    `${d.domain} · ${contextLabel(d.context)}\n${d.seconds.toFixed(2)} s analysis\n` +
    `${d.proved} checks proved (${(d.share * 100).toFixed(1)}%)\n` +
    `${d.ran} fixtures ran, ${d.rejected} rejected, ${d.timeouts} timed out`;
  /* Two panels on one shared domain axis: a scatter of 15 labelled points collides. */
  const panel = (el, x, label, extra) => {
    el.replaceChildren(
      Plot.plot({
        width: width(el),
        height: 260,
        marginLeft: 84,
        style: axisStyle,
        color: contextScale(),
        y: { domain: DOMAINS, label: null },
        x: { label, grid: true, nice: true, ...extra },
        marks: [
          Plot.ruleY(DOMAINS, { stroke: "#e3eaeb" }),
          Plot.ruleY(
            d3
              .rollups(
                configs,
                (v) => d3.extent(v, (d) => d[x]),
                (d) => d.domain,
              )
              .map(([domain, [lo, hi]]) => ({ domain, lo, hi })),
            { y: "domain", x1: "lo", x2: "hi", stroke: "#a9bec2", strokeWidth: 2 },
          ),
          Plot.dot(configs, {
            x,
            y: "domain",
            fill: "context",
            r: 7,
            stroke: "white",
            strokeWidth: 2,
            tip: true,
            title,
          }),
        ],
      }),
    );
  };
  panel($("chart-tradeoff-time"), "seconds", "Analysis time over the corpus (s) →", { zero: true });
  panel($("chart-tradeoff-proved"), "share", "Checks proved →", {
    tickFormat: "%",
    domain: [0, 1],
  });
  readTradeoff(configs);
}

const pct = (x) => `${(x * 100).toFixed(0)}%`;
const times = (x) => `${x.toFixed(1)}×`;

/* Configuration values in a reading are chips, so a reader tells settings from prose at a glance. */
const ctxChip = (c) =>
  `<span class="chip chip-ctx" style="--swatch:${contextColor(c)}">${contextLabel(c)}</span>`;
const domChip = (d) => `<span class="chip chip-dom" style="--swatch:${domainColor(d)}">${d}</span>`;
const progChip = (t) => `<span class="chip chip-prog">${t}</span>`;

/* The readings are computed from the snapshot, so a new measurement cannot leave them stale. */
function reading(id, sentences) {
  $(id).innerHTML = sentences.filter(Boolean).join(" ");
}

function readTradeoff(configs) {
  const at = (domain, context) => configs.find((c) => c.domain === domain && c.context === context);
  const baseline = CONTEXTS[0];
  /* Per domain, what each richer context policy costs and buys over the first one. */
  const gains = DOMAINS.flatMap((domain) =>
    CONTEXTS.slice(1).map((context) => {
      const base = at(domain, baseline);
      const c = at(domain, context);
      return base && c && base.seconds > 0
        ? { domain, context, cost: c.seconds / base.seconds, gain: c.proved - base.proved }
        : null;
    }),
  ).filter(Boolean);
  /* Per context policy, what the most precise domain buys over the least precise one. */
  const domainGains = CONTEXTS.map((context) => {
    const row = configs.filter((c) => c.context === context);
    const lo = d3.least(row, (c) => c.proved);
    const hi = d3.greatest(row, (c) => c.proved);
    return lo && hi ? { context, lo, hi, gain: hi.proved - lo.proved } : null;
  }).filter(Boolean);
  const best = d3.greatest(configs, (c) => c.share);
  /* Equal proof counts are a tie, listed cheapest first, never a winner by list order. */
  const tied = configs
    .filter((c) => c.proved === best.proved)
    .sort((x, y) => x.seconds - y.seconds);
  const rejected = configs.filter((c) => c.rejected > 0);
  const timeouts = configs.filter((c) => c.timeouts > 0);
  const byContext = (context) => gains.filter((g) => g.context === context);
  const range = (xs, f) => {
    const [lo, hi] = d3.extent(xs);
    return lo === hi ? f(lo) : `${f(lo)}–${f(hi)}`;
  };
  const maxContextGain = d3.max(gains, (g) => g.gain) ?? 0;
  const maxDomainGain = d3.max(domainGains, (g) => g.gain) ?? 0;
  reading("reading-tradeoff", [
    ...CONTEXTS.slice(1).map((context) => {
      const g = byContext(context);
      if (!g.length) return null;
      const top = d3.greatest(g, (x) => x.gain);
      return `Over ${ctxChip(baseline)}, ${ctxChip(context)} costs <strong>${range(
        g.map((x) => x.cost),
        times,
      )}</strong> the time across the domains and proves ${range(
        g.map((x) => x.gain),
        (x) => `${x >= 0 ? "+" : ""}${x}`,
      )} checks; it helps ${domChip(top.domain)} most (+${top.gain}).`;
    }),
    maxContextGain !== maxDomainGain
      ? maxContextGain > maxDomainGain
        ? `On this corpus contexts matter more than domains: the largest gain from a context policy (+${maxContextGain}) beats the largest gain from choosing a more precise domain under one policy (+${maxDomainGain}).`
        : `On this corpus domains matter more than contexts: choosing a more precise domain under one policy gains up to +${maxDomainGain}, a context policy at most +${maxContextGain}.`
      : null,
    tied.length === 1
      ? `The most precise configuration is ${domChip(best.domain)} with ${ctxChip(best.context)} at <strong>${pct(best.share)}</strong>.`
      : `${tied.length} configurations tie for the most proofs at <strong>${pct(best.share)}</strong>: ${tied.map((c) => `${domChip(c.domain)} with ${ctxChip(c.context)} (${c.seconds.toFixed(1)}&nbsp;s)`).join(", ")}. The costlier ones buy no extra proofs on these fixtures.`,
    rejected.length
      ? `Some dots stand on fewer runs: the CLI rejects ${rejected.map((c) => `${domChip(c.domain)} with ${ctxChip(c.context)} for ${c.rejected} fixtures`).join(", ")}.`
      : null,
    timeouts.length
      ? `Runs past the time limit count as no proof: ${timeouts.map((c) => `${domChip(c.domain)} with ${ctxChip(c.context)} (${c.timeouts})`).join(", ")}.`
      : null,
  ]);
}

/* Every check in the corpus once: the largest verdict count any configuration saw per fixture. */
let checksCache = null;
function totalChecks(data) {
  if (checksCache == null) {
    checksCache = d3.sum(
      d3.rollups(
        data.runs.filter((r) => r.verdicts),
        (v) => d3.max(v, (r) => d3.sum(Object.values(r.verdicts))),
        (r) => r.fixture,
      ),
      ([, n]) => n,
    );
  }
  return checksCache;
}

function quantile(data, domain) {
  const series = CONTEXTS.flatMap((context) =>
    data.runs
      .filter(
        (r) => r.status === "ok" && r.domain === domain && r.context === context && r.ms != null,
      )
      .map((r) => Math.max(0.001, r.ms))
      .sort(d3.ascending)
      .map((ms, i) => ({ context, rank: i + 1, ms })),
  );
  readQuantile(data, domain);
  const el = $("chart-quantile");
  el.replaceChildren(
    Plot.plot({
      width: width(el),
      height: 360,
      marginLeft: 56,
      style: axisStyle,
      color: contextScale(),
      x: { label: "Fixtures solved →", grid: true },
      y: { type: "log", label: "↑ Time per fixture (ms)", grid: true },
      marks: [
        Plot.line(series, { x: "rank", y: "ms", stroke: "context", strokeWidth: 2 }),
        Plot.tip(
          series,
          Plot.pointer({
            x: "rank",
            y: "ms",
            stroke: "context",
            title: (d) => `${contextLabel(d.context)}\nfixture #${d.rank}: ${fmtMs(d.ms)}`,
          }),
        ),
      ],
    }),
  );
}

function readQuantile(data, domain) {
  const runs = (context) =>
    data.runs.filter((r) => r.status === "ok" && r.domain === domain && r.context === context);
  const parts = CONTEXTS.map((context) => {
    const rs = runs(context).sort((a, b) => b.ms - a.ms);
    const top = Math.max(1, Math.round(rs.length * 0.05));
    return {
      context,
      rs,
      top,
      median: d3.median(rs, (r) => r.ms),
      share: d3.sum(rs.slice(0, top), (r) => r.ms) / d3.sum(rs, (r) => r.ms),
    };
  }).filter((p) => p.rs.length);
  const heaviest = d3.greatest(parts, (p) => p.share);
  reading("reading-quantile", [
    `For ${domChip(domain)}, the median fixture solves in ${parts.map((p) => `<strong>${fmtMs(p.median)}</strong> under ${ctxChip(p.context)}`).join(", ")}.`,
    heaviest
      ? `Cost is most concentrated under ${ctxChip(heaviest.context)}: the slowest ${heaviest.top === 1 ? "fixture" : `${heaviest.top} fixtures`} (5%) ${heaviest.top === 1 ? "takes" : "take"} <strong>${pct(heaviest.share)}</strong> of its solve time, led by <code>${heaviest.rs[0].fixture}</code> at ${fmtMs(heaviest.rs[0].ms)}.`
      : null,
    heaviest && heaviest.share > 0.5
      ? "A corpus total under that policy says more about those programs than about a typical one."
      : null,
  ]);
}

/* Least-squares slope on log-log axes: the k of a power law n^k. */
function slope(points, x, y) {
  const pts = points
    .filter((p) => p[x] > 0 && p[y] > 0)
    .map((p) => [Math.log(p[x]), Math.log(p[y])]);
  if (pts.length < 3) return null;
  const mx = d3.mean(pts, (p) => p[0]);
  const my = d3.mean(pts, (p) => p[1]);
  return d3.sum(pts, ([a, b]) => (a - mx) * (b - my)) / d3.sum(pts, ([a]) => (a - mx) ** 2);
}

/* Below this the native solve is too short for a browser/native ratio to mean much. */
const DEPTH_RATIO_FLOOR_MS = 100;
/* A fitted exponent this close to 0 is a flat line, not a power law. */
const FLAT_EXPONENT = 0.2;

/* "a", "a and b", "a, b and c". */
const listing = (xs) =>
  xs.length < 2 ? xs.join("") : `${xs.slice(0, -1).join(", ")} and ${xs.at(-1)}`;

function readDepth(data) {
  const fits = DOMAINS.map((domain) => {
    const rows = data.depth.filter((d) => (d.domain ?? "interval") === domain);
    const big = rows.filter((d) => d.n >= 100);
    const last = d3.greatest(
      rows.filter((d) => d.native_ms != null),
      (d) => d.n,
    );
    const both = d3.greatest(
      rows.filter((d) => d.wasm_ms != null && d.native_ms >= DEPTH_RATIO_FLOOR_MS),
      (d) => d.n,
    );
    return {
      domain,
      kNative: slope(
        big.filter((d) => d.native_ms != null),
        "n",
        "native_ms",
      ),
      kEvals: slope(
        big.filter((d) => d.evals),
        "n",
        "evals",
      ),
      last,
      stopped: rows.find((d) => d.status && d.status !== "ok"),
      ratio: both ? both.wasm_ms / both.native_ms : null,
    };
  }).filter((f) => f.last);
  const withSlopes = fits.filter((f) => f.kNative != null);
  const flat = withSlopes.filter((f) => Math.abs(f.kNative) < FLAT_EXPONENT);
  /* Domains whose exponents round alike are one statement, not one clause each. */
  const growing = d3.groups(
    withSlopes.filter((f) => Math.abs(f.kNative) >= FLAT_EXPONENT),
    (f) => f.kNative.toFixed(1),
  );
  const outgrow = withSlopes.filter(
    (f) => f.kEvals != null && f.kNative > f.kEvals + 0.3 && !flat.includes(f),
  );
  const chips = (fs) => listing(fs.map((f) => domChip(f.domain)));
  const stopped = d3.groups(
    fits.filter((f) => f.stopped),
    (f) => `${f.stopped.n}|${f.stopped.status}`,
  );
  const ratios = fits.filter((f) => f.ratio != null);
  reading("reading-depth", [
    growing.length
      ? `From n&nbsp;=&nbsp;100 up, solve time grows about as ${listing(growing.map(([k, fs]) => `<strong>n<sup>${k}</sup></strong> for ${chips(fs)}`))}.`
      : null,
    flat.length
      ? `It stays flat for ${chips(flat)}: ${flat.length === 1 ? "this domain has" : "these domains have"} only a few abstract values, so the entry states of <code>h</code> collapse to ${listing([...new Set(flat.map((f) => f.last.contexts))].map(String))} contexts at every depth.`
      : null,
    outgrow.length
      ? `For ${chips(outgrow)}, the solver's evaluations grow only as <strong>n<sup>${d3.mean(outgrow, (f) => f.kEvals).toFixed(1)}</sup></strong>, so each evaluation gets slower as contexts accumulate. The CPU profile of <code>h(1000)</code> below shows where that time goes.`
      : null,
    ...stopped.map(([key, fs]) => {
      const [n, status] = key.split("|");
      return `${chips(fs)} ${fs.length === 1 ? "stops" : "stop"} at n&nbsp;=&nbsp;${n} (${status}), after ${listing(fs.map((f) => `${fmtMs(f.last.native_ms)} and ${(f.last.rss / 2 ** 20).toFixed(0)}&nbsp;MB at n&nbsp;=&nbsp;${f.last.n}${fs.length > 1 ? ` for ${domChip(f.domain)}` : ""}`))}.`;
    }),
    ratios.length
      ? `Where a native solve takes at least ${DEPTH_RATIO_FLOOR_MS}&nbsp;ms, WebAssembly needs <strong>${range(
          ratios.map((f) => f.ratio),
          times,
        )}</strong> the native time at the deepest such run (${chips(ratios)}).`
      : null,
  ]);
}

/* "1.5×" for one value, "1.5×–2.8×" for a spread. */
function range(xs, f) {
  const [lo, hi] = d3.extent(xs);
  return f(lo) === f(hi) ? f(lo) : `${f(lo)}–${f(hi)}`;
}

function depth(data) {
  readDepth(data);
  const rows = data.depth
    .flatMap((d) => [
      d.native_ms != null && {
        n: d.n,
        domain: d.domain ?? "interval",
        build: "native",
        ms: d.native_ms,
      },
      d.wasm_ms != null && {
        n: d.n,
        domain: d.domain ?? "interval",
        build: "WebAssembly",
        ms: d.wasm_ms,
      },
    ])
    .filter(Boolean);
  const series = (d) => `${d.domain} · ${d.build}`;
  let el = $("chart-depth-time");
  el.replaceChildren(
    Plot.plot({
      width: width(el),
      height: 320,
      marginLeft: 56,
      style: axisStyle,
      color: domainScale(),
      x: { type: "log", label: "Recursion depth n →", grid: true },
      y: { type: "log", label: "↑ Solve time (ms)", grid: true },
      marks: [
        Plot.line(rows, {
          x: "n",
          y: "ms",
          z: series,
          stroke: "domain",
          strokeWidth: 2,
          strokeDasharray: (d) => (d.build === "native" ? null : "5 4"),
        }),
        Plot.dot(rows, {
          x: "n",
          y: "ms",
          fill: "domain",
          r: 3.5,
          stroke: "white",
          strokeWidth: 1.5,
          tip: true,
          title: (d) => `${d.domain}, ${d.build}, n = ${d.n}\n${fmtMs(d.ms)}`,
        }),
      ],
    }),
  );
  const work = data.depth
    .filter((d) => d.evals)
    .map((d) => ({ ...d, domain: d.domain ?? "interval" }));
  el = $("chart-depth-work");
  el.replaceChildren(
    Plot.plot({
      width: width(el),
      height: 320,
      marginLeft: 64,
      style: axisStyle,
      color: domainScale(),
      x: { type: "log", label: "Recursion depth n →", grid: true },
      y: { type: "log", label: "↑ Evaluations", grid: true },
      marks: [
        Plot.line(work, { x: "n", y: "evals", stroke: "domain", strokeWidth: 2 }),
        Plot.dot(work, {
          x: "n",
          y: "evals",
          fill: "domain",
          r: 3.5,
          stroke: "white",
          strokeWidth: 1.5,
          tip: true,
          title: (d) =>
            `${d.domain}, n = ${d.n}\n${d3.format(",")(d.evals)} evaluations\n${d3.format(",")(d.unknowns)} unknowns, ${d.contexts} contexts\npeak RSS ${(d.rss / 2 ** 20).toFixed(0)} MB`,
        }),
      ],
    }),
  );
}

/* A gap between the time and evaluation exponents this large marks data-structure cost. */
const SCALING_GAP = 0.5;

function scalingFits(data) {
  return d3
    .groups(data.scaling ?? [], (r) => r.family)
    .map(([family, rows]) => {
      const ok = rows.filter((r) => r.native_ms != null);
      const big = ok.filter((r) => r.n >= 100);
      const kTime = slope(big, "n", "native_ms");
      const kEvals = slope(
        big.filter((r) => r.evals),
        "n",
        "evals",
      );
      return {
        family,
        what: rows[0].what,
        context: rows[0].context,
        maxN: d3.max(ok, (r) => r.n),
        stopped: rows.find((r) => r.status && r.status !== "ok"),
        kTime,
        kEvals,
        gap: kTime != null && kEvals != null ? kTime - kEvals : null,
      };
    });
}

function scaling(data) {
  const section = $("scaling-section");
  if (!data.scaling?.length) {
    section.hidden = true;
    return;
  }
  section.hidden = false;
  const fits = scalingFits(data);
  const families = fits.map((f) => f.family);
  const color = {
    domain: families,
    range: families.map((_, i) => PALETTE[i % PALETTE.length]),
    legend: true,
  };
  const rows = data.scaling.filter((r) => r.native_ms != null);
  const el = $("chart-scaling");
  el.replaceChildren(
    Plot.plot({
      width: width(el),
      height: 380,
      marginLeft: 56,
      style: axisStyle,
      color,
      x: { type: "log", label: "Size n →", grid: true },
      y: { type: "log", label: "↑ Solve time (ms)", grid: true },
      marks: [
        Plot.line(rows, { x: "n", y: "native_ms", stroke: "family", strokeWidth: 2 }),
        Plot.dot(rows, {
          x: "n",
          y: "native_ms",
          fill: "family",
          r: 3.5,
          stroke: "white",
          strokeWidth: 1.5,
          tip: true,
          title: (d) =>
            `${d.family}, n = ${d.n}\n${fmtMs(d.native_ms)}${d.evals ? `\n${d3.format(",")(d.evals)} evaluations` : ""}`,
        }),
      ],
    }),
  );
  const fmtK = (k) => (k == null ? "" : k.toFixed(1));
  $("scaling-table").tBodies[0].replaceChildren(
    ...[...fits]
      .sort((a, b) => (b.gap ?? -9) - (a.gap ?? -9))
      .map((f) => {
        const tr = document.createElement("tr");
        const cells = [
          [f.family, "path"],
          [f.what, ""],
          [contextLabel(f.context), ""],
          [`${f.maxN}${f.stopped ? ` (${f.stopped.status} at ${f.stopped.n})` : ""}`, "num"],
          [fmtK(f.kTime), "num"],
          [fmtK(f.kEvals), "num"],
          [fmtK(f.gap), "num"],
        ];
        tr.replaceChildren(
          ...cells.map(([text, cls]) => {
            const td = document.createElement("td");
            td.className = cls;
            td.textContent = text;
            return td;
          }),
        );
        return tr;
      }),
  );
  const broken = fits
    .filter((f) => f.gap != null && f.gap >= SCALING_GAP)
    .sort((a, b) => b.gap - a.gap);
  const fine = fits.filter((f) => f.gap != null && f.gap < SCALING_GAP);
  const stopped = fits.filter((f) => f.stopped);
  reading("reading-scaling", [
    broken.length
      ? `Solve time outgrows the solver's evaluations for ${listing(broken.map((f) => `<strong>${f.what}</strong> (time n<sup>${f.kTime.toFixed(1)}</sup>, evaluations n<sup>${f.kEvals.toFixed(1)}</sup>)`))}: along ${broken.length === 1 ? "this dimension" : "these dimensions"}, each evaluation gets more expensive as the program grows, so a list the solver consults grows with it.`
      : "No family's solve time outgrows its evaluations by a full power, so none of these dimensions alone drives a list the solver scans per evaluation.",
    fine.length
      ? `For ${listing(fine.map((f) => f.what))}, time and work grow at about the same rate, so the generated code's per-evaluation cost stays flat there.`
      : null,
    stopped.length
      ? `${listing(stopped.map((f) => `${f.what} passed the time limit at n&nbsp;=&nbsp;${f.stopped.n}`))}.`
      : null,
    broken.length
      ? `The CPU profile of <code>${broken[0].family}</code> below shows which functions that time goes to.`
      : null,
  ]);
}

/* Who wrote a frame's code, which is also how far the proofs reach into it. */
const FLAME_KINDS = [
  [
    "generated",
    "Generated from the Isabelle theories",
    "#2a78d6",
    (n) => n.startsWith("Voblint_Generated."),
  ],
  [
    "runtime",
    "OCaml runtime and Zarith",
    "#eb6834",
    (n) => /^(caml_|ml_z_|Stdlib|Zarith|_)/.test(n),
  ],
  ["cli", "Hand-written CLI and rendering", "#1baf7a", (n) => /^[A-Z]\w*\./.test(n)],
  ["other", "Unresolved or grouped frames", "#a9bec2", () => true],
];
const flameKind = (name) => FLAME_KINDS.find(([, , , test]) => test(name));

/* Samples whose stack contains a frame matching [test], each sample counted once. */
function inclusive(node, test, inside = false) {
  const here = !inside && test(node.name);
  if (here) return node.value;
  return d3.sum(node.children, (c) => inclusive(c, test, inside || here));
}

function selfTimes(node, acc = new Map()) {
  const self = node.value - d3.sum(node.children, (c) => c.value);
  if (self > 0) acc.set(node.name, (acc.get(node.name) ?? 0) + self);
  for (const c of node.children) selfTimes(c, acc);
  return acc;
}

function readFlame(profile) {
  const root = profile.tree;
  const total = root.value;
  const share = (re) => inclusive(root, (n) => re.test(n)) / total;
  const report = share(/\.report_of$/);
  const cut = share(/^\[(callers not recorded|stack deeper)/);
  const solve = share(/\.tD_side_rule_Interp_solve_rec_c$/);
  const top = [...selfTimes(root)]
    .filter(([n]) => !n.startsWith("[") && n !== "all samples")
    .sort((a, b) => b[1] - a[1])
    .slice(0, 4);
  const lookups = d3.sum(top, ([n, v]) => (/\.(membera|equal_\w+)$/.test(n) ? v : 0)) / total;
  const generated = inclusive(root, (n) => n.startsWith("Voblint_Generated.")) / total;
  reading("reading-flame", [
    `${profile.samples.toLocaleString("en")} samples of ${progChip(profile.title)} under ${domChip(profile.domain)} with ${ctxChip(profile.context)}${profile.profiler ? `, recorded with ${profile.profiler}` : ""}.`,
    `<strong>${pct(generated)}</strong> of them are inside code generated from the theories.`,
    `At least ${pct(solve)} fall inside the solver's recursion (<code>solve_rec_c</code>) and at least ${pct(report)} inside <code>report_of</code>, which turns the solution into the published report after the solve; the ${pct(cut)} of samples whose stack was cut off cannot be assigned to either.`,
    report > solve
      ? "So for this program, reading the result out costs more than computing it."
      : null,
    `The functions that spend the most time themselves are ${top.map(([n, v]) => `<code>${n.replace(/^Voblint_Generated\./, "")}</code> (${pct(v / total)})`).join(", ")}.`,
    lookups > 0.15
      ? "<code>membera</code> is the generated list membership test, which compares elements one by one with the <code>equal_…</code> functions, and <code>caml_apply2</code> is OCaml applying the equality closure it is passed. The report's <code>lookup_table</code>, for one, checks whether a node and context are among the covered keys this way, so a lookup scans a list that grows with the number of contexts. That is a plausible source of the super-linear growth in the scaling plot; confirming it needs a profile across depths."
      : null,
  ]);
}

/* A frame's definition at the commit the snapshot was measured on. */
function sourceUrl(source, meta) {
  if (!source || !meta.commit_sha || !meta.repo_url) return null;
  return `${meta.repo_url}/blob/${meta.commit_sha}/${source.path}#L${source.line}`;
}

function showSource(frame, meta) {
  const el = $("flame-source");
  if (!frame) {
    el.replaceChildren();
    return;
  }
  const url = sourceUrl(frame.source, meta);
  const name = document.createElement("code");
  name.textContent = frame.name;
  if (!url) {
    el.replaceChildren(
      name,
      document.createTextNode(
        frame.name.endsWith(".fun")
          ? " is an anonymous closure; it has no definition of its own to link to."
          : flameKind(frame.name)[0] === "runtime"
            ? " belongs to the OCaml runtime or Zarith, outside this repository."
            : " has no source link: it is a local function, or its name is not defined at a single top-level place.",
      ),
    );
    return;
  }
  const a = document.createElement("a");
  a.href = url;
  a.target = "_blank";
  a.rel = "noreferrer";
  a.textContent = `${frame.source.path}:${frame.source.line}`;
  const note = String(meta.commit).endsWith("-dirty")
    ? " (measured with uncommitted changes, so the committed line may differ)"
    : "";
  el.replaceChildren(
    name,
    document.createTextNode(" is defined at "),
    a,
    document.createTextNode(` at commit ${meta.commit_sha.slice(0, 9)}${note}.`),
  );
}

let flameChart = null;
function flame(data, index) {
  const profile = data.flame?.[index];
  const el = $("chart-flame");
  if (!profile) {
    el.replaceChildren();
    $("reading-flame").textContent = "";
    $("flame-details").textContent =
      data.flame === null
        ? "This snapshot was recorded without CPU profiles: they need macOS's sample tool."
        : "This snapshot has no CPU profiles.";
    return;
  }
  $("flame-legend").replaceChildren(
    ...FLAME_KINDS.map(([, label, color]) => {
      const s = document.createElement("span");
      s.style.setProperty("--swatch", color);
      s.textContent = label;
      return s;
    }),
  );
  const total = profile.tree.value;
  const details = $("flame-details");
  flameChart = flamegraph()
    .width(width(el))
    .cellHeight(18)
    .minFrameSize(2)
    .transitionDuration(300)
    .sort(true)
    .setColorMapper((d) => flameKind(d.data.name)[2])
    .setLabelHandler(
      (d) =>
        `${d.data.name} · ${d3.format(",")(d.data.value)} samples (${((100 * d.data.value) / total).toFixed(1)}%)` +
        (d.data.recursion ? ` · recursion ${d.data.recursion} deep` : ""),
    )
    .setDetailsElement(details)
    .onClick((d) => showSource(d.data, data.meta));
  el.replaceChildren();
  d3.select(el).datum(structuredClone(profile.tree)).call(flameChart);
  details.textContent =
    "Hover a bar for its samples; click to zoom in and see where it is defined.";
  showSource(null, data.meta);
  readFlame(profile);
  const open = $("flame-open");
  open.hidden = true;
  profileLink(profile).then((href) => {
    if (href && data.flame[index] === profile) {
      open.href = href;
      open.hidden = false;
    }
  });
}

function browserOverview(data) {
  const pairs = browserPairs(data).filter((b) => b.native >= RATIO_FLOOR_MS);
  const configs = d3
    .rollups(
      pairs,
      (v) => ({ ratio: d3.median(v, (b) => b.wasm_ms / b.native), n: v.length }),
      (b) => b.domain,
      (b) => b.context,
    )
    .flatMap(([domain, cs]) => cs.map(([context, v]) => ({ domain, context, ...v })));
  const el = $("chart-browser-overview");
  el.replaceChildren(
    Plot.plot({
      width: width(el),
      height: 240,
      marginLeft: 84,
      style: axisStyle,
      color: contextScale(),
      y: { domain: DOMAINS, label: null },
      x: { type: "log", label: "Median WebAssembly / native solve time →", grid: true, nice: true },
      marks: [
        Plot.ruleX([1], { stroke: "#a9bec2", strokeDasharray: "4 4" }),
        Plot.ruleY(DOMAINS, { stroke: "#e3eaeb" }),
        Plot.dot(configs, {
          x: "ratio",
          y: "domain",
          fill: "context",
          r: 7,
          stroke: "white",
          strokeWidth: 2,
          tip: true,
          title: (d) =>
            `${d.domain} · ${contextLabel(d.context)}\n${times(d.ratio)} on the median run\n${d.n} runs over ${RATIO_FLOOR_MS} ms natively`,
        }),
      ],
    }),
  );
  return configs;
}

function browser(data, domain, context) {
  const pts = browserPairs(data)
    .filter((b) => b.domain === domain && b.context === context)
    .map((b) => ({
      fixture: b.fixture,
      native: Math.max(0.01, b.native),
      wasm: Math.max(0.01, b.wasm_ms),
    }));
  const configs = browserOverview(data);
  const measured = pts.filter((p) => p.native >= RATIO_FLOOR_MS);
  const r = measured.map((p) => p.wasm / p.native);
  const [lo, hi] = d3.extent(configs, (c) => c.ratio);
  const slowest = d3.greatest(configs, (c) => c.ratio);
  reading("reading-browser", [
    configs.length
      ? `Across the ${configs.length} configurations, the browser build's median run takes <strong>${times(lo)}–${times(hi)}</strong> the native solve time; the gap is widest for ${domChip(slowest.domain)} with ${ctxChip(slowest.context)}.`
      : null,
    measured.length
      ? `For ${domChip(domain)} with ${ctxChip(context)}, ${measured.length} fixtures solve in at least ${RATIO_FLOOR_MS}&nbsp;ms natively; the median takes ${times(d3.median(r))} as long in the browser, and ${pct(r.filter((x) => x > 2).length / r.length)} of them more than twice as long.`
      : `For ${domChip(domain)} with ${ctxChip(context)}, no fixture solves in ${RATIO_FLOOR_MS}&nbsp;ms natively, too fast for a ratio to mean much.`,
  ]);
  if (!pts.length) {
    $("chart-browser").replaceChildren();
    return;
  }
  const [a, b] = [
    d3.min(pts, (p) => Math.min(p.native, p.wasm)),
    d3.max(pts, (p) => Math.max(p.native, p.wasm)),
  ];
  const diag = (k) => [
    { x: a, y: a * k },
    { x: b / k, y: b },
  ];
  const el = $("chart-browser");
  el.replaceChildren(
    Plot.plot({
      width: width(el),
      height: 400,
      marginLeft: 56,
      style: axisStyle,
      x: { type: "log", label: "Native solve (ms) →", grid: true, domain: [a, b] },
      y: { type: "log", label: "↑ WebAssembly solve (ms)", grid: true, domain: [a, b] },
      marks: [
        ...[1, 2, 10].map((k) =>
          Plot.line(diag(k), { x: "x", y: "y", stroke: "#a9bec2", strokeDasharray: "4 4" }),
        ),
        ...[1, 2, 10].map((k) =>
          Plot.text([diag(k)[1]], {
            x: "x",
            y: "y",
            text: () => `${k}×`,
            dy: -6,
            fill: "#607078",
            fontSize: 11,
          }),
        ),
        Plot.dot(pts, {
          x: "native",
          y: "wasm",
          r: 3.5,
          fill: contextColor(context),
          fillOpacity: 0.75,
          stroke: "white",
          strokeWidth: 1,
        }),
        Plot.tip(
          pts,
          Plot.pointer({
            x: "native",
            y: "wasm",
            title: (d) => `${d.fixture}\nnative ${fmtMs(d.native)}\nWebAssembly ${fmtMs(d.wasm)}`,
          }),
        ),
      ],
    }),
  );
}

/*
 * The playground with the fixture and the configuration this row measured. The profile
 * ignores a fixture's PARAM header, so the link sets every setting the measurement fixed
 * rather than letting the header's settings apply.
 */
/* The playground's Share encoding: raw deflate, base64url without padding. */
async function packSource(source) {
  const deflated = new Blob([source]).stream().pipeThrough(new CompressionStream("deflate-raw"));
  const bytes = new Uint8Array(await new Response(deflated).arrayBuffer());
  return btoa(String.fromCharCode(...bytes))
    .replaceAll("+", "-")
    .replaceAll("/", "_")
    .replace(/=+$/, "");
}

/* A profiled program in the playground: its fixture, or its packed source when it has none. */
async function profileLink(profile) {
  const base = playgroundLink({
    fixture: profile.fixture ?? "",
    domain: profile.domain,
    context: profile.context,
  });
  if (profile.fixture) return base;
  const query = base.replace("fixture=&", "");
  return profile.source ? `${query}#code=${await packSource(profile.source)}` : null;
}

function playgroundLink(r) {
  const callString = r.context.startsWith("call-string");
  const params = new URLSearchParams({
    fixture: r.fixture,
    analysis: r.domain,
    globals: "warrow",
    context: callString ? "call-string" : r.context,
    ...(callString ? { k: r.context.split("-").pop() } : {}),
    ...(r.domain === "int" ? { refinement: "fixpoint" } : {}),
    placement: "flow-sensitive",
  });
  return `playground.html?${params}`;
}

const quantileDomainDefault = () => (DOMAINS.includes("interval") ? "interval" : DOMAINS[0]);

function table(data) {
  const select = $("fixture-config");
  select.replaceChildren(
    ...DOMAINS.flatMap((d) =>
      CONTEXTS.map(
        (c) =>
          new Option(
            `${d} · ${contextLabel(c)}`,
            `${d}|${c}`,
            false,
            d === quantileDomainDefault() && c === CONTEXTS[1],
          ),
      ),
    ),
  );
  let sortKey = "ms";
  let dir = -1;
  const render = () => {
    const [domain, context] = select.value.split("|");
    const q = $("fixture-filter").value.trim().toLowerCase();
    const rows = data.runs
      .filter(
        (r) => r.domain === domain && r.context === context && r.fixture.toLowerCase().includes(q),
      )
      .map((r) => ({
        ...r,
        proved: r.verdicts ? `${r.verdicts.PROVED}/${d3.sum(Object.values(r.verdicts))}` : r.status,
      }))
      .sort((a, b) => dir * d3.ascending(a[sortKey] ?? -1, b[sortKey] ?? -1));
    $("fixture-table").tBodies[0].replaceChildren(
      ...rows.slice(0, 200).map((r) => {
        const tr = document.createElement("tr");
        const cells = [
          [r.fixture, "path"],
          [r.ms != null ? r.ms.toFixed(1) : r.status, "num"],
          [r.evals != null ? d3.format(",")(r.evals) : "", "num"],
          [r.unknowns ?? "", "num"],
          [r.contexts ?? "", "num"],
          [r.rss ? (r.rss / 2 ** 20).toFixed(0) : "", "num"],
          [r.proved, "num"],
        ];
        const href = playgroundLink(r);
        tr.replaceChildren(
          ...cells.map(([text, cls], i) => {
            const td = document.createElement("td");
            td.className = cls;
            if (i === 0) {
              const a = document.createElement("a");
              a.href = href;
              a.textContent = text;
              a.title = "Open in the playground with this configuration";
              td.append(a);
            } else {
              td.textContent = text;
            }
            return td;
          }),
        );
        tr.className = "linked";
        tr.addEventListener("click", (e) => {
          if (e.target.closest("a")) return;
          if (e.metaKey || e.ctrlKey) window.open(href, "_blank");
          else location.href = href;
        });
        return tr;
      }),
    );
    for (const th of document.querySelectorAll("#fixture-table th")) {
      th.setAttribute(
        "aria-sort",
        th.dataset.key === sortKey ? (dir < 0 ? "descending" : "ascending") : "none",
      );
    }
  };
  for (const th of document.querySelectorAll("#fixture-table th")) {
    th.addEventListener("click", () => {
      dir = th.dataset.key === sortKey ? -dir : -1;
      sortKey = th.dataset.key;
      render();
    });
  }
  select.addEventListener("change", render);
  $("fixture-filter").addEventListener("input", render);
  render();
}

/* Snapshots from before the device record carried flat machine/os/node fields. */
function deviceOf(meta) {
  return meta.device ?? { cpu: meta.machine, os: meta.os, node: meta.node };
}

function deviceLine(d) {
  return [
    d.cpu,
    d.model,
    d.logical_cpus &&
      `${d.logical_cpus} logical CPUs${d.performance_cpus ? ` (${d.performance_cpus} performance)` : ""}`,
    d.memory_gib && `${d.memory_gib} GiB`,
    d.os,
    d.ocaml && `OCaml ${d.ocaml}`,
    d.wasm_of_ocaml && `wasm_of_ocaml ${d.wasm_of_ocaml}`,
    d.node && `Node ${d.node}`,
  ]
    .filter(Boolean)
    .join(", ");
}

/* Conditions that make a snapshot's timings less comparable, stated where they are read. */
function caveats(meta) {
  const d = deviceOf(meta);
  return [
    d.on_battery && "measured on battery power, where the CPU may run slower",
    meta.jobs > 1 && `${meta.jobs} runs in parallel, which adds timing noise`,
    d.virtualized && "measured in a virtual machine",
    String(meta.commit).endsWith("-dirty") && "measured with uncommitted changes",
    meta.filter && `only fixtures matching “${meta.filter}”`,
  ].filter(Boolean);
}

function method(meta) {
  const updates = (meta.updates ?? []).map(
    (u) => `${u.phases.join(", ")} re-run ${u.date} at ${u.commit} on ${u.cpu}`,
  );
  const items = [
    `Commit ${meta.commit}, measured ${meta.date}${meta.duration_s ? ` in ${Math.round(meta.duration_s / 60)} min` : ""} on ${deviceLine(deviceOf(meta))}.`,
    updates.length ? `Later partial re-runs: ${updates.join("; ")}.` : null,
    `Native: the CLI built from the generated OCaml, one process per run${meta.jobs ? `, ${meta.jobs} at a time` : ""}. Time is the CLI's own measurement around the solve (--timing), the median of ${meta.reps} runs; process start-up, parsing and printing are not in it. Peak RSS is the whole process's, from the system's time command.`,
    `WebAssembly: the playground's bundle under Node with a ${meta.wasm_stack_kib ?? 512} KiB stack, about a Chrome worker's, timed by the analyzer around the same solve, median of ${meta.reps} runs.`,
    `Solver work (evaluations, unknowns, contexts) is counted from a separate traced run's JSON Lines events.`,
    `Every configuration uses the CLI's other defaults (globals warrow, Int refinement to a fixpoint, flow-sensitive program globals) and ignores a fixture's PARAM header, so all configurations see the same programs.`,
    `Fixtures whose header bounds the run with --timeout are left out; runs over ${meta.timeout_s} s count as timeouts. A configuration the CLI rejects for a fixture (exit 1) counts as no proof.`,
    `These are measurements of one machine and build: evidence about cost on this corpus, not a claim about other programs or a property the theorems establish.`,
  ].filter(Boolean);
  $("method-list").replaceChildren(
    ...items.map((t) => {
      const li = document.createElement("li");
      li.textContent = t;
      return li;
    }),
  );
}

async function load(entry) {
  const data = await fetchJson(entry.file);
  /* Parse-error and ill-formed fixtures test the frontend; they have nothing to profile. */
  data.runs = data.runs.filter((r) => ["ok", "rejected", "timeout"].includes(r.status));
  data.browser ??= [];
  data.depth ??= [];
  DOMAINS = ordered(KNOWN_DOMAINS, new Set(data.runs.map((r) => r.domain)));
  CONTEXTS = ordered(KNOWN_CONTEXTS, new Set(data.runs.map((r) => r.context)));
  checksCache = null;
  const warn = caveats(data.meta);
  $("snapshot-meta").textContent =
    `commit ${data.meta.commit} · ${data.meta.date} · ${deviceOf(data.meta).cpu}` +
    (warn.length ? ` · ⚠ ${warn.join("; ")}` : "");
  const ok = data.runs.filter((r) => r.status === "ok");
  kpis(data, ok);
  tradeoff(data);
  let quantileDomain = DOMAINS.includes("interval") ? "interval" : DOMAINS[0];
  segmented(
    $("quantile-domains"),
    DOMAINS.map((d) => [d, d]),
    quantileDomain,
    (d) => {
      quantileDomain = d;
      quantile(data, d);
    },
  );
  quantile(data, quantileDomain);
  depth(data);
  scaling(data);
  let flameIndex = 0;
  segmented(
    $("flame-targets"),
    (data.flame ?? []).map((p, i) => [i, p.title]),
    0,
    (i) => {
      flameIndex = i;
      flame(data, i);
    },
  );
  flame(data, flameIndex);
  $("flame-search").oninput = (e) => flameChart?.search(e.target.value);
  $("flame-reset").onclick = () => flameChart?.resetZoom();
  let browserDomain = quantileDomain;
  let browserContext = CONTEXTS[0];
  segmented(
    $("browser-domains"),
    DOMAINS.map((d) => [d, d]),
    browserDomain,
    (d) => {
      browserDomain = d;
      browser(data, browserDomain, browserContext);
    },
  );
  segmented(
    $("browser-contexts"),
    CONTEXTS.map((c) => [c, contextLabel(c)]),
    browserContext,
    (c) => {
      browserContext = c;
      browser(data, browserDomain, browserContext);
    },
  );
  browser(data, browserDomain, browserContext);
  table(data);
  method(data.meta);
  for (const el of document.querySelectorAll("[data-meta]"))
    el.textContent = data.meta[el.dataset.meta];
  let resizeTimer;
  window.onresize = () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => {
      tradeoff(data);
      quantile(data, quantileDomain);
      depth(data);
      scaling(data);
      flame(data, flameIndex);
      browser(data, browserDomain, browserContext);
    }, 150);
  };
}

/* A missing or unreadable snapshot says so in place of the numbers, never as a blank page. */
function showUnavailable(message) {
  $("snapshot-bar").hidden = true;
  const note = document.createElement("p");
  note.className = "reading";
  note.textContent = message;
  $("kpis").replaceChildren(note);
  for (const section of document.querySelectorAll("main.profiling > section.section")) {
    section.hidden = true;
  }
}

async function fetchJson(url) {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`${url}: HTTP ${response.status}`);
  return response.json();
}

async function loadSafely(entry) {
  try {
    await load(entry);
  } catch (error) {
    console.error(error);
    showUnavailable(`The snapshot “${entry.label}” could not be read: ${error.message}`);
  }
}

let index = null;
try {
  index = await fetchJson("data/profiling/index.json");
} catch (error) {
  console.error(error);
}
if (!index?.snapshots?.length) {
  showUnavailable(
    "No profiling snapshot has been recorded yet. Run `pixi run profile` to measure one; it lands in pages/data/profiling/.",
  );
} else {
  const select = $("snapshot-select");
  select.replaceChildren(...index.snapshots.map((s, i) => new Option(s.label, String(i))));
  select.addEventListener("change", () => loadSafely(index.snapshots[Number(select.value)]));
  await loadSafely(index.snapshots[0]);
}
