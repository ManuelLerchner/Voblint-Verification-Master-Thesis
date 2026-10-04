// Repository figures, measured by scripts/pages_stats.py and written to
// /shared/generated/stats.json by tools/stats.py (the site reads the same
// collection). An unknown key is a compile error, so a renamed figure cannot
// leave a stale number on the page.
//
// A diffle review renders each revision from its committed files alone, and
// this data is not committed (every build measures it). diffle says so through
// `sys.inputs.diffle`; every figure then prints as a placeholder.
#let _review = "diffle" in sys.inputs
#let _stats = if _review { (:) } else { json("/shared/generated/stats.json").stats }
#let _placeholder = text(fill: luma(140))[\#]

/// The raw integer behind a key such as "isabelle.lines"; none under review.
#let stat-value(key) = {
  if _review { return none }
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
#let stat(key) = if _review { _placeholder } else { _grouped(stat-value(key)) }

/// The sum of several figures, formatted.
#let stat-sum(..keys) = if _review { _placeholder } else {
  _grouped(keys.pos().map(stat-value).sum())
}

/// `part` as a whole-number percentage of `whole`: `#stat-percent("isabelle.doc", "isabelle.lines")`.
#let stat-percent(part, whole) = if _review { [#_placeholder%] } else {
  str(int(calc.round(100 * stat-value(part) / stat-value(whole)))) + "%"
}

/// The key suffixes below a prefix, in key order: `stat-keys("corpus.by_group.")`.
#let stat-keys(prefix) = {
  _stats.keys().filter(k => k.starts-with(prefix)).map(k => k.slice(prefix.len()))
}
