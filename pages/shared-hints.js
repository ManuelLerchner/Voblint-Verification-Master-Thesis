/* Each shared global's unknown reports analysis headers followed by indented
 * name=value lines. Keep that global's own binding as the analyzer printed it. */
function unknownValue({ name, reachable, lines }) {
  if (!reachable) {
    return "⊥";
  }

  const samples = [];
  let analysis = null;

  for (const line of lines) {
    if (!line.startsWith(" ") && line.endsWith(":")) {
      analysis = line.slice(0, -1);
      continue;
    }
    const binding = /^ {2}([^=]+)=(.*)$/.exec(line);
    if (analysis && binding && binding[1] === name) {
      samples.push([analysis, binding[2]]);
    }
  }

  return samples.length === 0
    ? undefined
    : samples.length === 1
      ? samples[0][1]
      : samples.map(([label, value]) => `${label} ${value}`).join(" · ");
}

export function sharedGlobalValues(shared) {
  const values = new Map((shared?.globals ?? []).map((name) => [name, undefined]));

  for (const unknown of shared?.unknowns ?? []) {
    values.set(unknown.name, unknownValue(unknown));
  }
  return values;
}

export function sharedWriteHint(contribution, name, values) {
  return {
    text: `⇢ ${contribution} · final ${name}: ${values.get(name) ?? "unavailable"}`,
    title:
      "Write contribution evaluated from the final analysis state; final is the reported shared global value. This is not an individual solver trace event or a flow-sensitive value after the statement.",
  };
}
