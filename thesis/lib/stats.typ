// Repository figures, measured by scripts/pages_stats.py and written to
// /shared/generated/stats.json by tools/stats.py (the site reads the same
// collection). An unknown key is a compile error, so a renamed figure cannot
// leave a stale number on the page.

#let _stats = json("/shared/generated/stats.json").stats

/// The raw integer behind a key such as "isabelle.lines".
#let stat-value(key) = {
  assert(
    key in _stats,
    message: "unknown statistic `"
      + key
      + "` -- keys are in thesis/shared/generated/stats.json "
      + "(pixi run thesis-stats-write)",
  )
  _stats.at(key)
}

// Thousands grouped with commas, as the site prints them: 62,098.
#let _grouped(n) = {
  let digits = str(n)
  let groups = ()
  while digits.len() > 3 {
    groups.insert(0, digits.slice(digits.len() - 3))
    digits = digits.slice(0, digits.len() - 3)
  }
  groups.insert(0, digits)
  groups.join(",")
}

/// A repository figure, formatted: `#stat("corpus.cases")`.
#let stat(key) = _grouped(stat-value(key))

/// The sum of several figures, formatted.
#let stat-sum(..keys) = _grouped(keys.pos().map(stat-value).sum())

/// `part` as a whole-number percentage of `whole`: `#stat-percent("isabelle.doc", "isabelle.lines")`.
#let stat-percent(part, whole) = (
  str(int(calc.round(100 * stat-value(part) / stat-value(whole)))) + "%"
)

/// The key suffixes below a prefix, in key order: `stat-keys("corpus.by_group.")`.
#let stat-keys(prefix) = {
  _stats.keys().filter(k => k.starts-with(prefix)).map(k => k.slice(prefix.len()))
}
