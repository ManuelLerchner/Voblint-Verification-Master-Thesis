// Running-time figures from one profiling snapshot, reduced by tools/profiling.py to
// /shared/generated/profiling.json. The snapshot is pinned in shared/profiling.toml,
// so every number here belongs to one recorded measurement. An unknown key is a
// compile error, so a renamed figure cannot leave a stale number on the page.

#import "@preview/lilaq:0.6.0" as lq
#import "theme.typ": vb

#let _prof = json("/shared/generated/profiling.json")

/// The raw value at a dotted path such as "depth_fits.interval.time".
#let prof-value(path) = {
  let v = _prof
  for key in path.split(".") {
    assert(
      type(v) == dictionary and key in v,
      message: "unknown profiling figure `" + path + "` (pixi run thesis-profiling-write)",
    )
    v = v.at(key)
  }
  v
}

/// A duration in milliseconds, as the profiling page prints it.
#let prof-ms(path) = {
  let ms = prof-value(path)
  if ms >= 1000 { [#calc.round(ms / 1000, digits: 1)~s] } else if ms >= 10 {
    [#calc.round(ms)~ms]
  } else { [#calc.round(ms, digits: 1)~ms] }
}

#let prof-pct(path) = [#calc.round(prof-value(path) * 100)%]
// One decimal always, so 1.0 prints as 1.0 and not as 1.
#let _one-decimal(x) = {
  let r = calc.round(x, digits: 1)
  if r == calc.round(r) { str(int(r)) + ".0" } else { str(r) }
}
#let prof-times(path) = [#_one-decimal(prof-value(path))$times$]
#let prof-int(path) = str(prof-value(path))
/// "the median of 3 runs", or "a single run" when the snapshot repeated nothing.
#let prof-runs() = {
  let n = prof-value("meta.reps")
  if n == 1 [a single run] else [the median of #n runs]
}
#let prof-exp(path) = $n^#_one-decimal(prof-value(path))$

/// How a fitted power law reads in prose: "nearly constant", "about linearly",
/// "about quadratically", or the exponent itself when it is none of these.
#let prof-growth(path) = {
  let k = prof-value(path)
  if calc.abs(k) < 0.2 [nearly constant] else if calc.abs(k - 1) < 0.2 [about linearly] else if (
    calc.abs(k - 2) < 0.3
  ) [about quadratically] else [as #prof-exp(path)]
}

// Domains keep the colours they carry in every other figure.
#let _domain-color = (
  sign: vb.sign,
  interval: vb.ivl,
  parity: vb.par,
  congruence: vb.cong,
  int: vb.neutral,
)
#let _order = ("sign", "parity", "congruence", "interval", "int")

/// Solve time of h(n) under entry-state contexts, one line per domain, log-log.
#let depth-plot(width: 6.4cm, height: 4.6cm) = {
  let series = prof-value("depth")
  lq.diagram(
    width: width,
    height: height,
    xscale: "log",
    yscale: "log",
    xlabel: [recursion depth $n$],
    ylabel: [solve time (ms)],
    legend: (position: left + top),
    ..(
      _order
        .filter(d => d in series)
        .map(d => {
          let pts = series.at(d)
          lq.plot(
            pts.map(p => p.n),
            pts.map(p => p.native_ms),
            label: d,
            color: _domain-color.at(d, default: vb.neutral),
            mark: "o",
            mark-size: 3pt,
          )
        })
    ),
  )
}

