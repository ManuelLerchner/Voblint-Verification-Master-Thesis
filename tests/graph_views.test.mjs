// The playground's two graphs, built from real analyzer payloads: the compiled CFG
// (each point once, every context's state listed at it) and the analysis graph (one
// node per point and context, with trace-recorded global dependencies).
// pixi run graph-views-check (builds the CLI first)
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { test } from "node:test";
import { cfgView, globalDependencies } from "../pages/graph-views.js";

const CLI = "cli/voblint";
const globalId = (name) => `global-${name}`;

/* What the playground receives: the browser payload, with the run's trace attached. */
function payload(file, args) {
  const result = JSON.parse(execFileSync(CLI, ["--json", ...args, file], { encoding: "utf8" }));
  const trace = execFileSync(CLI, ["--format", "jsonl", "--output", "/dev/stdout", ...args, file], {
    encoding: "utf8",
  });

  return { ...result, trace_jsonl: trace.split("\n").filter((l) => l.startsWith("{")).join("\n") };
}

const TWO_CALLS = "tests/graph-views/two-calls.vimp";
const TWO_GLOBALS = "tests/graph-views/two-globals.vimp";
const CALL_STRING = ["--analysis", "interval", "--context", "call-string", "--context-depth", "1"];

test("context-insensitive: the CFG and the analysis graph have the same points", () => {
  const result = payload(TWO_CALLS, ["--analysis", "interval", "--context", "none"]);
  const view = cfgView(result);

  assert.equal(view.nodes.length, result.cfg.nodes.length);
  assert.equal(result.nodes.length, view.nodes.length);
  assert.ok(view.nodes.every((node) => node.rows.length === 1));
});

test("call strings: one body of f in the CFG, two in the analysis graph", () => {
  const result = payload(TWO_CALLS, CALL_STRING);
  const view = cfgView(result);
  const fBoxes = result.graph.clusters.filter((c) => c.label.startsWith("f / "));

  // The program's own procedure comes first, so the layout puts callers left of callees.
  assert.deepEqual(
    view.procedures.map((p) => p.label),
    ["main", "f"],
  );
  assert.equal(view.nodes.filter((n) => n.point === "pp0").length, 1);
  assert.equal(fBoxes.length, 2);
  assert.equal(result.nodes.filter((n) => n.point === "pp0").length, 2);
});

test("the CFG node shows run_voblint's joined state and keeps every context's", () => {
  const result = payload(TWO_CALLS, CALL_STRING);
  const point = result.cfg.nodes.find((n) => n.point === "pp1");
  const node = cfgView(result).nodes.find((n) => n.point === "pp1");
  const rows = point.rows.map((id) => result.nodes.find((n) => n.id === id));
  const values = rows.map((row) => row.sections[0].bindings.find(([x]) => x === "y")?.[1]);

  // The join comes from Isabelle's report_point_join, not from the page.
  assert.deepEqual(point.joined[0].bindings.find(([x]) => x === "y"), ["y", "[2,3]"]);
  assert.ok(node.lines.some((line) => line.includes("y=[2,3]")), node.lines.join("\n"));
  // Each context's own value is still there for the inspector.
  assert.deepEqual(values.sort(), ["[2,2]", "[3,3]"]);
});

test("keyed globals: solver unknowns only in the analysis graph, with edges from analysis_graph_of", () => {
  const result = payload(TWO_GLOBALS, [
    "--analysis", "interval", "--context", "none", "--program-globals", "flow-insensitive",
  ]);
  const view = cfgView(result);
  const edges = globalDependencies(result, globalId);
  const pp = (id) => result.nodes.find((n) => n.id === id)?.point;

  assert.ok(view.nodes.every((n) => n.id.startsWith("cfg_")));
  assert.deepEqual(result.shared.unknowns.map((u) => u.name).sort(), ["g", "h"]);
  // Reading g and publishing g happen at the point after g = g + 1; h is only read.
  assert.ok(edges.some((e) => e.kind === "global_read" && e.source === "global-g"));
  assert.ok(edges.some((e) => e.kind === "global_write" && e.target === "global-g"));
  assert.ok(edges.some((e) => e.kind === "global_read" && e.source === "global-h"));
  assert.ok(!edges.some((e) => e.kind === "global_write" && e.target === "global-h" && pp(e.source) !== "entry_main"));
  assert.equal(new Set(edges.map((e) => e.id)).size, edges.length);
});

test("flow-sensitive globals have no global dependencies to draw", () => {
  const result = payload(TWO_GLOBALS, ["--analysis", "interval", "--context", "none"]);

  assert.deepEqual(globalDependencies(result, globalId), []);
});

test("each step's result is joined over contexts by run_voblint, for the editor's hints", () => {
  const result = payload(TWO_CALLS, CALL_STRING);
  const step = result.cfg.nodes.find((n) => n.point === "pp0").next[0];
  const y = step.state[0].bindings.find(([x]) => x === "y")?.[1];

  assert.equal(step.writes, "y");
  assert.equal(y, "[2,3]");
});
