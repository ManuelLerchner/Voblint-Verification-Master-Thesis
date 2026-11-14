/*
 * Fills the explainer's cost section from the latest profiling snapshot, so its numbers
 * follow the measurement instead of going stale in the prose. Each placeholder keeps its
 * written fallback when the data is missing.
 */

const fmtMs = (ms) =>
  ms >= 1000 ? `${(ms / 1000).toFixed(1)} s` : `${ms.toFixed(ms < 10 ? 1 : 0)} ms`;

function median(xs) {
  const s = [...xs].sort((a, b) => a - b);
  const m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
}

function fill(name, text) {
  const el = document.querySelector(`[data-profile="${name}"]`);
  if (el && text) el.textContent = text;
}

async function summarize() {
  const index = await fetch("data/profiling/index.json").then((r) => r.json());
  const entry = index.snapshots?.[0];
  if (!entry) return;
  const data = await fetch(entry.file).then((r) => r.json());
  const solves = data.runs.filter((r) => r.status === "ok" && r.ms != null).map((r) => r.ms);
  if (solves.length) fill("median", fmtMs(median(solves)));
  fill("when", `taken ${data.meta.date} on ${data.meta.device?.cpu ?? "one machine"}`);

  const interval = (data.depth ?? []).filter(
    (d) => (d.domain ?? "interval") === "interval" && d.native_ms != null,
  );
  const deep = interval.reduce((a, d) => (!a || d.n > a.n ? d : a), null);
  const small = interval.find((d) => d.n === 100);
  if (deep && small && deep.n > small.n) {
    fill(
      "depth",
      `Under the interval domain, h(${small.n}) solves in ${fmtMs(small.native_ms)} and h(${deep.n}) in ${fmtMs(deep.native_ms)}: ${deep.n / small.n} times the depth, ${Math.round(deep.native_ms / small.native_ms)} times the time.`,
    );
  }

  const native = new Map(
    data.runs
      .filter((r) => r.status === "ok" && r.ms != null)
      .map((r) => [`${r.fixture}|${r.domain}|${r.context}`, r.ms]),
  );
  const ratios = (data.browser ?? [])
    .map((b) => [b.wasm_ms, native.get(`${b.fixture}|${b.domain}|${b.context}`)])
    .filter(([w, n]) => w != null && n != null && n >= 1)
    .map(([w, n]) => w / n);
  if (ratios.length) {
    fill(
      "browser",
      `On the corpus runs long enough to time, the browser takes ${median(ratios).toFixed(1)} times as long as the native command line on the median run.`,
    );
  }
}

summarize().catch(() => {});
