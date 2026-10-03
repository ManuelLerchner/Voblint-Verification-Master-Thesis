/*
 * The two graphs the playground draws from one run, as data. Neither runs the analyzer
 * again, and neither combines two states: the control-flow view lists each context's
 * state at its point, and the analysis view's global edges are what the solver trace
 * recorded. The page lays both out; this module only decides what they contain.
 */
import { globalKey, localKey, parseEvents } from "./replay_state.js";

/* A zero divisor beside a point's name: definite before possible. */
export const DIVISION_ICON = { definite: "⛔", possible: "⚠️" };

/* A check's report verdict as the node colour the analysis view uses for it. */
const VERDICT_STATUS = { REFUTED: "refuted", UNKNOWN: "unknown", PROVED: "proved" };

/* One context's row inside a CFG node: its context key and its state, kept short. */
export const CFG_ROW_WIDTH = 44;

/* The context part of an analysis node's "owner / context" label. */
function contextOf(node) {
  return node.context.slice(node.context.indexOf(" / ") + 3);
}

/* A state's sections in one line each, kept short: "x=[1,2] y=⊤", or a whole value. */
function sectionTexts(sections) {
  return sections
    .map((section) =>
      section.bindings
        ? section.bindings.map(([name, value]) => `${name}=${value}`).join(" ")
        : section.whole,
    )
    .filter(Boolean)
    .map((line) =>
      line.length > CFG_ROW_WIDTH ? `${line.slice(0, CFG_ROW_WIDTH - 1)}\u2026` : line,
    );
}

export function cfgRowLine(row) {
  const key = row.context_key || contextOf(row);
  const state =
    row.status === "unreachable"
      ? "unreachable"
      : row.sections
          .map((section) =>
            section.bindings
              ? section.bindings.map(([name, value]) => `${name}=${value}`).join(" ")
              : section.whole,
          )
          .filter(Boolean)
          .join(" | ") || "no bindings";
  const line = `${key}: ${state}`;

  return line.length > CFG_ROW_WIDTH ? `${line.slice(0, CFG_ROW_WIDTH - 1)}…` : line;
}

function byPoint(items) {
  const groups = new Map();

  for (const item of items ?? []) {
    groups.set(item.point, [...(groups.get(item.point) ?? []), item]);
  }

  return groups;
}

/*
 * The compiled CFG of the run, as res_cfg holds it: every program point once, boxed by
 * its procedure. A point's colour is the report's verdict for its checks and divisions,
 * never one context's. With several contexts, each context's state is a row of its own.
 */
export function cfgView(result) {
  const nodesById = new Map((result.nodes ?? []).map((node) => [node.id, node]));
  const checksAt = byPoint(result.checks);
  const diagnosticsAt = byPoint(result.diagnostics);
  const parentOf = new Map();

  for (const procedure of result.cfg.procedures) {
    for (const id of procedure.members) {
      parentOf.set(id, procedure.id);
    }
  }

  const nodes = result.cfg.nodes.map((node) => {
    const rows = node.rows.map((id) => nodesById.get(id)).filter(Boolean);
    const checks = checksAt.get(node.point) ?? [];
    const diagnostics = diagnosticsAt.get(node.point) ?? [];
    const icons = [
      ...(diagnostics.some((d) => d.severity === "error") ? [DIVISION_ICON.definite] : []),
      ...(diagnostics.some((d) => d.severity !== "error") ? [DIVISION_ICON.possible] : []),
    ];
    const verdicts = [
      ...checks.map((check) => check.verdict),
      ...diagnostics.map((d) => (d.severity === "error" ? "REFUTED" : "UNKNOWN")),
    ];
    const verdict = ["REFUTED", "UNKNOWN", "PROVED"].find((v) => verdicts.includes(v));
    const dead = node.joined === null || rows.every((row) => row.status === "unreachable");

    return {
      id: node.id,
      parent: parentOf.get(node.id),
      point: node.point,
      rows: node.rows,
      /* The state run_voblint joins over the point's contexts; each context's own
         state stays in [rows] for the inspector. */
      lines: [
        [node.point, ...icons].join(" "),
        ...(node.joined === null ? ["unreachable"] : sectionTexts(node.joined)),
        ...checks.map((check) => `check ${check.condition}: ${check.verdict}`),
      ],
      status: verdict
        ? VERDICT_STATUS[verdict]
        : dead
          ? "unreachable"
          : node.kind === "point"
            ? "plain"
            : "boundary",
    };
  });

  return {
    procedures: result.cfg.procedures.map(({ id, label }) => ({ id, label })),
    nodes,
    edges: result.cfg.edges,
  };
}

/*
 * The reads and writes of each flow-insensitive global, as the run's own solver trace
 * recorded them: a point whose right-hand side queried the global's unknown, and one
 * that published to it. Each pair is listed once, however often the solver repeated it.
 */
export function globalDependencies(result, globalId) {
  if (typeof result.trace_jsonl !== "string" || !(result.shared?.unknowns ?? []).length) {
    return [];
  }

  const nodeOfKey = new Map(
    (result.nodes ?? []).map((node) => [`L:${node.point}|${contextOf(node)}`, node.id]),
  );
  const seen = new Set();
  const edges = [];

  for (const event of parseEvents(result.trace_jsonl)) {
    const read = event.event === "query_global";

    if ((!read && event.event !== "side") || event.target?.kind !== "program_global") {
      continue;
    }

    const local = nodeOfKey.get(localKey(event.current));
    const global = globalId(globalKey(event.target).slice(3));
    const [source, target] = read ? [global, local] : [local, global];
    const kind = read ? "global_read" : "global_write";
    const id = `${kind}-${source}-${target}`;

    if (local && !seen.has(id)) {
      seen.add(id);
      edges.push({ id, source, target, kind });
    }
  }

  return edges;
}
