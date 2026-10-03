/* The shared report uses analysis headers followed by indented name=value lines.
 * Keep only declared names and preserve the values printed by the analyzer. */
export function sharedGlobalValues(shared) {
  const values = new Map((shared?.globals ?? []).map((name) => [name, []]));
  let analysis = null;

  for (const line of shared?.reachable ? shared.lines : []) {
    if (!line.startsWith(" ") && line.endsWith(":")) {
      analysis = line.slice(0, -1);
      continue;
    }
    const binding = /^ {2}([^=]+)=(.*)$/.exec(line);
    if (analysis && binding && values.has(binding[1])) {
      values.get(binding[1]).push([analysis, binding[2]]);
    }
  }
  return new Map(
    [...values].map(([name, samples]) => [
      name,
      !shared.reachable
        ? "⊥"
        : samples.length === 0
          ? undefined
          : samples.length === 1
            ? samples[0][1]
            : samples.map(([label, value]) => `${label} ${value}`).join(" · "),
    ]),
  );
}

export function sharedWriteHint(contribution, name, values) {
  return {
    text: `⇢ ${contribution} · final ${name}: ${values.get(name) ?? "unavailable"}`,
    title:
      "Write contribution evaluated from the final analysis state; final is the reported shared global value. This is not an individual solver trace event or a flow-sensitive value after the statement.",
  };
}
