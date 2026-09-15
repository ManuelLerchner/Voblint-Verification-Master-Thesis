import { EditorView, basicSetup } from "https://esm.sh/codemirror@6.0.2";

import { HighlightStyle, StreamLanguage, syntaxHighlighting } from "https://esm.sh/@codemirror/language@6.12.4";

import { tags } from "https://esm.sh/@lezer/highlight@1.2.3";

import { json } from "https://esm.sh/@codemirror/lang-json@6.0.2";

/*
 * Same semver ranges codemirror@6.0.2 itself imports, so esm.sh resolves them to
 * the one module instance basicSetup uses. A second @codemirror/state instance
 * rejects every extension built from it.
 */
import { Decoration, WidgetType, hoverTooltip } from "https://esm.sh/@codemirror/view@^6.0.0";

import { EditorState, StateEffect, StateField } from "https://esm.sh/@codemirror/state@^6.0.0";

function query(selector) {
  const element = document.querySelector(selector);

  if (!element) {
    throw new Error(`Missing required element: ${selector}`);
  }

  return element;
}

let analysisWorker = null;
let nextAnalysisRequestId = 1;
let pendingAnalysis = null;

const editorMount = query("#program-editor");

const analysisSelect = query("#analysis-select");
const globalsSelect = query("#globals-select");
const contextSelect = query("#context-select");

const contextDepthInput = query("#context-depth");
const contextDepthGroup = query("#context-depth-group");

const globalsHelp = query("#globals-help");

const runButton = query("#run-analysis");
const runButtonIcon = query("#run-analysis-icon");
const runButtonLabel = query("#run-analysis-label");

const status = query("#analyzer-status");
const problems = query("#analysis-problems");

const timing = query("#analysis-timing");
const timingValue = query("#analysis-timing-value");

const inspectorLocation = query("#state-inspector-location");
const inspectorBody = query("#state-inspector-body");
const valueHintsToggle = query("#value-hints-toggle");

const graphPanel = query("#analysis-graph-panel");
const graph = query("#analysis-graph");

const graphZoomOut = query("#graph-zoom-out");
const graphZoomReset = query("#graph-zoom-reset");
const graphZoomIn = query("#graph-zoom-in");
const graphZoomFit = query("#graph-zoom-fit");

const solverGlobals = query("#solver-globals");
const solverGlobalsCount = query("#solver-globals-count");
const solverGlobalsList = query("#solver-globals-list");

const rawResult = query("#raw-result");
const rawResultEmpty = query("#raw-result-empty");
const rawResultCall = query("#raw-result-call");
const rawResultPanes = query("#raw-result-panes");
const rawMounts = {
  input: query("#raw-input-body"),
  output: query("#raw-output-body"),
};

/*
 * Every editor feature on one screen, at the page's default configuration
 * (Interval, Warrowing, call string k=1):
 *
 *   i == 5 and hits == 8 PROVED, i < 5 REFUTED, a == 2 UNKNOWN,
 *   10 / (a - 2) a possible division by zero, record(100) DEAD,
 *   loop hints marked as joins, record's and wrap's parameters keyed by call site.
 *
 * scale is reached from wrap(1) and wrap(4) through one call site, so k=1
 * merges them. Warrowing per origin narrows a to [2,8]; k=2 proves a == 2 and
 * turns the possible division by zero into a definite one. Without context
 * sensitivity, hits == 8 is lost as well.
 */
const initialProgram = `// Move the cursor, hover the badges, click the graph.
// Then try: globals "Warrow per origin", call-string depth k=2, context None.
global hits;

fun record(amount) {
  hits = hits + amount;
}

fun scale(v) {
  return v * 2;
}

fun wrap(w) {
  r = scale(w);
  return r;
}

fun main() {
  i = 0;
  while (i < 5) {
    i = i + 1;
  }
  __voblint_check(i == 5);
  __voblint_check(i < 5);

  record(i);
  record(3);
  __voblint_check(hits == 8);

  if (hits > 10) {
    record(100);
  }

  a = wrap(1);
  b = wrap(4);
  __voblint_check(a == 2);
  share = 10 / (a - 2);
}`;

/* -------------------------------------------------------------------------- */
/* VIMP syntax highlighting                                                   */
/* -------------------------------------------------------------------------- */

const vimpLanguage = StreamLanguage.define({
  startState() {
    return {
      blockComment: false,
    };
  },

  copyState(state) {
    return { ...state };
  },

  token(stream, state) {
    if (state.blockComment) {
      if (stream.skipTo("*/")) {
        stream.match("*/");
        state.blockComment = false;
      } else {
        stream.skipToEnd();
      }

      return "comment";
    }

    if (stream.eatSpace()) {
      return null;
    }

    if (stream.match("//")) {
      stream.skipToEnd();
      return "comment";
    }

    if (stream.match("/*")) {
      if (stream.skipTo("*/")) {
        stream.match("*/");
      } else {
        state.blockComment = true;
        stream.skipToEnd();
      }

      return "comment";
    }

    if (stream.match(/^\d+/)) {
      return "number";
    }

    if (stream.match(/^__voblint_[A-Za-z0-9_]*/)) {
      return "builtin";
    }

    if (stream.match(/^(fun|global|if|else|while|return)\b/)) {
      return "keyword";
    }

    if (stream.match(/^(==|!=|<=|>=|&&|\|\||[+\-*/%<>=!])/)) {
      return "operator";
    }

    if (stream.match(/^[A-Za-z_][A-Za-z0-9_]*/)) {
      return "variableName";
    }

    if (stream.match(/^[(){}\[\],;]/)) {
      return "punctuation";
    }

    /*
     * Always consume one character, including on malformed input.
     */
    stream.next();
    return null;
  },
});

/* Shared by the VIMP editor and the raw JSON views; each language uses its own tags. */
const codeHighlight = HighlightStyle.define([
  {
    tag: tags.keyword,
    color: "#f08a65",
    fontWeight: "650",
  },
  {
    tag: tags.number,
    color: "#c4a7e7",
  },
  {
    tag: tags.operator,
    color: "#8bd5ca",
  },
  {
    tag: tags.comment,
    color: "#718b91",
    fontStyle: "italic",
  },
  {
    tag: tags.standard(tags.variableName),
    color: "#f0c674",
    fontWeight: "600",
  },
  {
    tag: tags.variableName,
    color: "#f7faf9",
  },
  {
    tag: tags.punctuation,
    color: "#a7bbc0",
  },
  {
    tag: tags.propertyName,
    color: "#8bd5ca",
  },
  {
    tag: tags.string,
    color: "#f7faf9",
  },
  {
    tag: [tags.bool, tags.null],
    color: "#f0c674",
  },
]);

/* -------------------------------------------------------------------------- */
/* Status/results                                                             */
/* -------------------------------------------------------------------------- */

function showStatus(message, kind = "") {
  status.textContent = message;

  status.className = kind ? `status ${kind}` : "status";
}

/* -------------------------------------------------------------------------- */
/* Raw run_voblint answer                                                     */
/* -------------------------------------------------------------------------- */

let rawRunProgram = null;

/*
 * Two-space JSON that keeps a small value on one line: a constructor term such
 * as {"Plus":[{"V":"x"},{"N":1}]} reads better whole than spread over a column.
 */
function formatJson(value, indent = "") {
  const flat = JSON.stringify(value);

  if (value === null || typeof value !== "object" || flat.length + indent.length <= 96) {
    return flat;
  }

  const inner = `${indent}  `;

  if (Array.isArray(value)) {
    return `[\n${value.map((item) => inner + formatJson(item, inner)).join(",\n")}\n${indent}]`;
  }

  const fields = Object.entries(value).map(
    ([key, item]) => `${inner}${JSON.stringify(key)}: ${formatJson(item, inner)}`,
  );

  return `{\n${fields.join(",\n")}\n${indent}}`;
}

const rawViews = Object.fromEntries(
  Object.entries(rawMounts).map(([part, parent]) => [
    part,
    new EditorView({
      extensions: [basicSetup, json(), syntaxHighlighting(codeHighlight), EditorState.readOnly.of(true)],
      parent,
    }),
  ]),
);

function setRawText(view, text) {
  view.dispatch({ changes: { from: 0, to: view.state.doc.length, insert: text } });
}

function fillRawViews() {
  if (!rawResult.open || !rawRunProgram) {
    return;
  }

  for (const [part, view] of Object.entries(rawViews)) {
    if (view.state.doc.length === 0) {
      setRawText(view, formatJson(rawRunProgram[part] ?? null));
    }
  }
}

function callPart(text, kind) {
  const span = document.createElement("span");

  span.className = `raw-call-${kind}`;
  span.textContent = text;

  return span;
}

/*
 * A datatype value in the raw encoding, written as Isabelle would print it: a bare
 * constructor, or the constructor applied to its arguments. Anything larger than a
 * constructor with scalar arguments is elided; the panel below holds the whole term.
 */
function constructorTerm(value) {
  if (typeof value === "string") {
    return value;
  }

  const [tag, arg] = Object.entries(value ?? {})[0] ?? ["?", null];
  const args = (Array.isArray(arg) ? arg : [arg]).map((a) =>
    typeof a === "number" || typeof a === "string" ? String(a) : "\u2026",
  );

  return `(${[tag, ...args].join(" ")})`;
}

/*
 * The panel's title: the call run_voblint received and the outline of its answer --
 * the constructor, then each result field with a list's length in place of the list.
 */
function renderRawCall(raw) {
  const input = raw?.input;
  const parts = [callPart("run_voblint", "fn")];

  if (!input) {
    parts.push(callPart(" kind rule ctx p", "arg"), callPart(" \u27f9 ", "arrow"), callPart("?", "arg"));
    rawResultCall.replaceChildren(...parts);
    rawResultCall.title = rawResultCall.textContent;
    return;
  }

  parts.push(
    callPart(` ${constructorTerm(input.kind)} ${constructorTerm(input.rule)} ${constructorTerm(input.ctx)} `, "arg"),
    callPart("p", "program"),
    callPart(" \u27f9 ", "arrow"),
  );

  const output = raw.output;

  if (typeof output === "string") {
    parts.push(callPart(output, "ctor"));
  } else {
    const [tag, record] = Object.entries(output ?? {})[0] ?? ["?", {}];
    const fields = Object.entries(record ?? {}).map(([name, value]) =>
      `${name}: ${Array.isArray(value) ? `[\u2026\u00d7${value.length}]` : "\u2026"}`,
    );

    parts.push(callPart(tag, "ctor"), callPart(` {${fields.join(", ")}}`, "fields"));
  }

  rawResultCall.replaceChildren(...parts);
  rawResultCall.title = rawResultCall.textContent;
}

/* The panel sits above the editor, so a reader who opened it keeps it open across runs. */
function showRawRunProgram(raw) {
  rawRunProgram = raw ?? null;

  for (const view of Object.values(rawViews)) {
    setRawText(view, "");
  }

  renderRawCall(rawRunProgram);
  rawResultEmpty.hidden = rawRunProgram !== null;
  rawResultPanes.hidden = rawRunProgram === null;
  fillRawViews();
}

/* Formatting a large answer is not free, so it waits until the panel is opened. */
rawResult.addEventListener("toggle", fillRawViews);

function clearTiming() {
  timing.hidden = true;
  timingValue.textContent = "—";
}


function formatDuration(milliseconds) {
  if (!Number.isFinite(milliseconds) || milliseconds < 0) {
    return null;
  }

  if (milliseconds < 1) {
    return `${milliseconds.toFixed(2)} ms`;
  }

  if (milliseconds < 100) {
    return `${milliseconds.toFixed(1)} ms`;
  }

  if (milliseconds < 1000) {
    return `${Math.round(milliseconds)} ms`;
  }

  return `${(milliseconds / 1000).toFixed(2)} s`;
}


function renderTiming(result) {
  const milliseconds = result?.timing?.analysis_ms;
  const formatted = formatDuration(milliseconds);

  if (formatted === null) {
    clearTiming();
    return;
  }

  timingValue.textContent = formatted;
  timing.hidden = false;
}

function workerError(message) {
  const error = new Error(
    message.message ?? "Browser analysis failed.",
  );

  if (typeof message.name === "string" && message.name !== "") {
    error.name = message.name;
  }

  if (typeof message.stack === "string" && message.stack !== "") {
    error.stack = message.stack;
  }

  return error;
}

/*
 * A run that did not produce a usable result says so above the editor, in a banner
 * that names what went wrong and, when the parser gave a position, jumps there.
 * The same banner summarizes arithmetic diagnostics after a successful run.
 */
function clearProblems() {
  problems.hidden = true;
  problems.className = "analysis-problems";
  problems.replaceChildren();
}

function jumpToSource(line, column = 1) {
  const doc = editor.state.doc;
  const pos = offsetOf(doc, line, column);

  editor.dispatch({ selection: { anchor: pos } });
  editor.focus();
  scrollEditorTo(pos);
  editorMount.scrollIntoView({ block: "center", behavior: "smooth" });
}

function lineButton(line, column) {
  const button = document.createElement("button");

  button.type = "button";
  button.className = "problem-jump";
  button.textContent = Number.isInteger(column) ? `Go to line ${line}, column ${column}` : `Go to line ${line}`;
  button.addEventListener("click", () => jumpToSource(line, Number.isInteger(column) ? column : 1));

  return button;
}

/* The offending source line with a caret under the reported column, compiler style. */
function sourceExcerpt(line, column) {
  const doc = editor.state.doc;

  if (!Number.isInteger(line) || line < 1 || line > doc.lines) {
    return null;
  }

  const text = doc.line(line).text;
  const gutter = `${line} | `;
  const pre = document.createElement("pre");
  pre.className = "problem-excerpt";
  pre.textContent = `${gutter}${text}`;

  if (Number.isInteger(column)) {
    const caret = document.createElement("span");
    caret.className = "problem-caret";
    caret.textContent = `\n${" ".repeat(gutter.length + Math.max(0, column - 1))}^`;
    pre.append(caret);
  }

  return pre;
}

function showProblem({ kind = "error", title, message, note, line, column, items = [] }) {
  const icon = document.createElement("i");
  icon.className = kind === "error" ? "fa-solid fa-circle-exclamation" : "fa-solid fa-triangle-exclamation";
  icon.setAttribute("aria-hidden", "true");

  const body = document.createElement("div");
  body.className = "problem-body";

  const heading = document.createElement("p");
  heading.className = "problem-title";
  heading.textContent = title;
  body.append(heading);

  /* A message that only repeats the title says nothing; the source line says more. */
  if (message && message.trim().toLowerCase() !== title.trim().toLowerCase()) {
    const text = document.createElement("p");
    text.className = "problem-message";
    text.textContent = message;
    body.append(text);
  }

  if (note) {
    const text = document.createElement("p");
    text.className = "problem-note";
    text.textContent = note;
    body.append(text);
  }

  const excerpt = sourceExcerpt(line, column);

  if (excerpt) {
    body.append(excerpt);
  }

  if (Number.isInteger(line)) {
    body.append(lineButton(line, column));
  }

  if (items.length > 0) {
    const list = document.createElement("ul");
    list.className = "problem-items";

    for (const item of items) {
      const entry = document.createElement("li");
      entry.className = item.kind;
      const label = document.createElement("span");
      label.textContent = item.message;
      entry.append(label);

      if (Number.isInteger(item.line)) {
        entry.append(lineButton(item.line));
      }

      list.append(entry);
    }

    body.append(list);
  }

  problems.className = `analysis-problems ${kind}`;
  problems.setAttribute("role", kind === "error" ? "alert" : "status");
  problems.replaceChildren(icon, body);
  problems.hidden = false;
}

function failureTitle(result) {
  const message = result.message ?? "";

  if (/syntax/i.test(message)) {
    return "Syntax error";
  }

  if (/well-formed/i.test(message)) {
    return "The program is not well-formed";
  }

  return Number.isInteger(result.line) ? "The program could not be parsed" : "The program could not be analyzed";
}

function showDiagnosticsSummary(result) {
  const diagnostics = Array.isArray(result.diagnostics) ? result.diagnostics : [];

  if (diagnostics.length === 0) {
    return;
  }

  const errors = diagnostics.filter((d) => d.severity === "error").length;
  const count = (n, word) => `${n} ${word}${n === 1 ? "" : "s"}`;
  const parts = [errors && count(errors, "error"), diagnostics.length - errors && count(diagnostics.length - errors, "warning")]
    .filter(Boolean)
    .join(" and ");

  showProblem({
    kind: errors > 0 ? "error" : "warning",
    title: `${parts[0].toUpperCase()}${parts.slice(1)} in arithmetic`,
    note: "An error means a divisor is zero in every live context; a warning means it may be zero.",
    items: diagnostics.map((d) => ({ kind: d.severity === "error" ? "error" : "warning", message: d.message ?? "", line: d.line })),
  });
}

function resultFailure(result) {
  const message = result.message ?? "The program could not be analyzed.";

  return Number.isInteger(result.line) && Number.isInteger(result.column)
    ? `${result.line}:${result.column}: ${message}`
    : message;
}

/* -------------------------------------------------------------------------- */
/* Source and result navigation                                               */
/* -------------------------------------------------------------------------- */

/*
 * One run's result keyed back to the text it analysed. Offsets are meaningful
 * only for that exact text, so an edit marks the model stale instead of letting
 * it point at lines that now say something else.
 */
let analysisModel = null;

/* What the inspector shows: a statement's nodes, or a single node without one. */
let inspection = null;
let focusedNodeId = null;
let hoveredSpan = null;
let highlightFrame = 0;

/*
 * A line holding several findings takes the most severe one's color; the badge
 * still lists every distinct label, so a context-sensitive UNKNOWN next to a
 * PROVED on the same line stays visible.
 */
const ANNOTATION_SEVERITY = ["dead", "proved", "unknown", "warning", "refuted", "error"];

const ANNOTATION_ICON = {
  dead: "∅",
  proved: "✓",
  unknown: "?",
  warning: "⚠",
  refuted: "✗",
  error: "✗",
};

function offsetOf(doc, line, column) {
  const text = doc.line(clamp(line, 1, doc.lines));

  return text.from + clamp(column - 1, 0, text.length);
}

function isLive(node) {
  return node.status !== "unreachable";
}

function buildAnalysisModel(result, doc) {
  const nodes = new Map();
  const nodesByPoint = new Map();

  for (const node of result.nodes ?? []) {
    nodes.set(node.id, node);

    const group = nodesByPoint.get(node.point) ?? [];

    group.push(node);
    nodesByPoint.set(node.point, group);
  }

  /*
   * A procedure header stands for its entry point, so the cursor on `fun p(n)`
   * inspects the states p is entered with and a graph entry node leads back to it.
   */
  const headers = (result.procedures ?? []).map((procedure) => ({
    ...procedure,
    point: procedure.entry,
  }));

  /*
   * A zero-width statement is the parser's implicit skip -- an empty block or a
   * missing else. Compile may give it no point at all, so it stands for no code
   * and must not read as unreachable.
   */
  const statements = [...headers, ...(result.statements ?? [])]
    .filter((s) => s.line < s.end_line || s.column < s.end_column)
    .filter((s) => s.end_line <= doc.lines)
    .map((s) => ({
      ...s,
      from: offsetOf(doc, s.line, s.column),
      to: offsetOf(doc, s.end_line, s.end_column),
      nodes: nodesByPoint.get(s.point) ?? [],
    }));

  return {
    nodes,
    procedureByEntry: new Map(headers.map((procedure) => [procedure.entry, procedure])),
    seedByEntry: new Map((result.seeds ?? []).filter((seed) => seed.entry).map((seed) => [seed.entry, seed])),
    statements,
    statementByPoint: new Map(statements.map((s) => [s.point, s])),
    stale: false,
  };
}

/* The compiler's return slot: assigned by `return e`, read back by the caller. */
const RETURN_SLOT = "#ret";

function valueOf(node, name) {
  if (name === RETURN_SLOT) {
    return node.ret ?? undefined;
  }

  return (node.bindings.find(([x]) => x === name) ?? node.globals.find(([x]) => x === name))?.[1];
}

/*
 * One hint per variable. Contexts that agree share a value; when they disagree,
 * each value is prefixed by the contexts it holds in, so `L18 [2,2] | L19 [3,3]`
 * cannot be read the wrong way round.
 */
function formatHint(label, samples) {
  const groups = new Map();

  for (const { key, value } of samples) {
    const keys = groups.get(value) ?? [];

    if (key && !keys.includes(key)) {
      keys.push(key);
    }

    groups.set(value, keys);
  }

  if (groups.size === 1) {
    return `${label}${[...groups.keys()][0]}`;
  }

  const parts = [...groups].map(([value, keys]) => (keys.length ? `${keys.join(",")} ${value}` : value));

  return `${label}${parts.join(" | ")}`;
}

/*
 * A header shows each parameter as the procedure is entered, and a call shows
 * the parameters of the callee context it enters, prefixed with an arrow. A
 * `return e` shows the value it returns, and a call whose result is discarded
 * shows what its callee returned, both after a return arrow. A
 * statement shows what it assigns, read from the state after its step -- unless
 * other steps flow into that point too (a loop head, the point after a branch):
 * that state is a join, so its hint is marked as such rather than presented as
 * the assignment's own effect. A callee entry that other calls also enter is
 * marked the same way.
 */
function valueHints(model) {
  const hints = [];

  for (const statement of model.statements) {
    const written = new Map();

    const sample = (label, key, value, merge) => {
      const entry = written.get(label) ?? { samples: [], merge: false };

      entry.samples.push({ key, value });
      entry.merge ||= merge;
      written.set(label, entry);
    };

    const writeLabel = (name) => (name === RETURN_SLOT ? "\u21a9 " : `${name}: `);

    for (const node of statement.nodes.filter(isLive)) {
      if (statement.formals) {
        for (const name of statement.formals) {
          const value = valueOf(node, name);

          if (value !== undefined) {
            sample(`${name}: `, node.context_key, value, false);
          }
        }

        continue;
      }

      const assignsResult = node.next.some((step) => step.writes);

      for (const enter of node.enters) {
        const entry = model.nodes.get(enter.id);
        const callee = entry ? model.procedureByEntry.get(entry.point) : null;

        for (const name of callee && isLive(entry) ? callee.formals : []) {
          const value = valueOf(entry, name);

          if (value !== undefined) {
            sample(`\u2192 ${name}: `, node.context_key, value, enter.join);
          }
        }

        const exit = enter.exit ? model.nodes.get(enter.exit) : null;

        if (!assignsResult && callee?.returns_value && exit && isLive(exit) && exit.ret) {
          sample("\u21a9 ", node.context_key, exit.ret, enter.join);
        }
      }

      for (const step of node.next) {
        const after = step.writes ? model.nodes.get(step.id) : null;
        const value = after && isLive(after) ? valueOf(after, step.writes) : undefined;

        if (value !== undefined) {
          sample(writeLabel(step.writes), node.context_key, value, step.join);
        }
      }
    }

    for (const [name, entry] of written) {
      hints.push({ pos: statement.to, text: formatHint(name, entry.samples), merge: entry.merge });
    }
  }

  return hints;
}

/*
 * Lines inside a statement no context reaches, except a line that also starts
 * a live statement: `if (c) { dead(); }` on one line keeps its live if.
 */
function deadLines(model) {
  const dead = new Set();
  const liveStarts = new Set();

  for (const statement of model.statements) {
    if (statement.nodes.some(isLive)) {
      liveStarts.add(statement.line);
      continue;
    }

    for (let line = statement.line; line <= statement.end_line; line++) {
      dead.add(line);
    }
  }

  return [...dead].filter((line) => !liveStarts.has(line));
}

/*
 * A DEAD badge on each dimmed line where a dead statement starts, the same
 * annotation a dead check already gets, so the two share one badge.
 */
function deadAnnotations(model, dimmed) {
  const lines = new Set(dimmed);

  return model.statements
    .filter((statement) => lines.has(statement.line) && !statement.nodes.some(isLive))
    .map((statement) => ({
      line: statement.line,
      kind: "dead",
      label: "DEAD",
      detail: "No context reaches this statement.",
    }));
}

function resultAnnotations(result) {
  if (result.status !== "ok") {
    return [{
      line: result.line,
      column: result.column,
      kind: "error",
      label: result.message ? result.message.toUpperCase() : "ERROR",
      detail: result.message ?? "",
    }];
  }

  const checks = Array.isArray(result.checks) ? result.checks : [];
  const diagnostics = Array.isArray(result.diagnostics) ? result.diagnostics : [];

  return [
    ...checks.map((check) => {
      const verdict = typeof check.verdict === "string" ? check.verdict : "UNKNOWN";

      return {
        line: check.line,
        kind: verdict.toLowerCase(),
        label: verdict,
        detail: [check.condition, check.state].filter(Boolean).join(" · "),
      };
    }),

    ...diagnostics.map((diagnostic) => ({
      line: diagnostic.line,
      kind: diagnostic.severity === "error" ? "error" : "warning",
      label: diagnostic.severity === "error" ? "ERROR" : "WARNING",
      detail: diagnostic.message ?? "",
    })),
  ];
}

class AnnotationBadge extends WidgetType {
  constructor(labels, detail) {
    super();

    this.labels = labels;
    this.detail = detail;
  }

  eq(other) {
    return other.labels === this.labels && other.detail === this.detail;
  }

  toDOM() {
    const badge = document.createElement("span");

    badge.className = "cm-verdict-badge";
    badge.textContent = this.labels;
    badge.title = this.detail;

    return badge;
  }

  ignoreEvent() {
    return false;
  }
}

class ValueHint extends WidgetType {
  constructor(text, merge) {
    super();

    this.text = text;
    this.merge = merge;
  }

  eq(other) {
    return other.text === this.text && other.merge === this.merge;
  }

  toDOM() {
    const hint = document.createElement("span");

    hint.className = this.merge ? "cm-value-hint merge" : "cm-value-hint";
    hint.textContent = this.merge ? `⊔ ${this.text}` : this.text;
    hint.title = this.merge
      ? "Value where several paths meet: a join that includes more than this step."
      : "Value after this statement.";

    return hint;
  }

  ignoreEvent() {
    return false;
  }
}

function resultDecorations(doc, view, showHints) {
  const ranges = [];
  const byLine = new Map();

  for (const annotation of view.annotations) {
    if (!Number.isInteger(annotation.line) || annotation.line < 1 || annotation.line > doc.lines) {
      continue;
    }

    const group = byLine.get(annotation.line) ?? [];

    group.push(annotation);
    byLine.set(annotation.line, group);
  }

  for (const [lineNumber, group] of byLine) {
    const line = doc.line(lineNumber);

    const kind = group
      .map((annotation) => annotation.kind)
      .reduce((worst, current) =>
        ANNOTATION_SEVERITY.indexOf(current) > ANNOTATION_SEVERITY.indexOf(worst) ? current : worst,
      );

    const labels = [...new Set(group.map((a) => `${ANNOTATION_ICON[a.kind]} ${a.label}`))].join("  ");
    const detail = group.map((a) => a.detail).filter(Boolean).join("\n");

    ranges.push(Decoration.line({ class: `cm-verdict-line cm-verdict-${kind}` }).range(line.from));

    /* A parse error points at a column: underline the character there. */
    for (const annotation of group.filter((a) => Number.isInteger(a.column))) {
      const at = clamp(line.from + annotation.column - 1, line.from, line.to);
      const from = at < line.to ? at : Math.max(line.from, at - 1);
      const to = Math.min(line.to, from + 1);

      if (to > from) {
        ranges.push(Decoration.mark({ class: "cm-error-token" }).range(from, to));
      }
    }
    ranges.push(
      Decoration.widget({ widget: new AnnotationBadge(labels, detail), side: 2 }).range(line.to),
    );
  }

  for (const lineNumber of view.deadLines) {
    if (lineNumber <= doc.lines) {
      ranges.push(Decoration.line({ class: "cm-dead-line" }).range(doc.line(lineNumber).from));
    }
  }

  if (showHints) {
    for (const hint of view.hints) {
      ranges.push(
        Decoration.widget({ widget: new ValueHint(hint.text, hint.merge), side: 1 }).range(hint.pos),
      );
    }
  }

  return Decoration.set(ranges, true);
}

const setResultView = StateEffect.define();
const setValueHintsVisible = StateEffect.define();

const EMPTY_RESULT_VIEW = { annotations: [], deadLines: [], hints: [] };

const resultViewField = StateField.define({
  create() {
    return { view: EMPTY_RESULT_VIEW, showHints: true, decorations: Decoration.none };
  },

  update(value, transaction) {
    let { view, showHints } = value;
    let changed = false;

    for (const effect of transaction.effects) {
      if (effect.is(setResultView)) {
        view = effect.value;
        changed = true;
      } else if (effect.is(setValueHintsVisible)) {
        showHints = effect.value;
        changed = true;
      }
    }

    if (changed) {
      return { view, showHints, decorations: resultDecorations(transaction.state.doc, view, showHints) };
    }

    /* Everything here describes the analysed text; an edit invalidates all of it. */
    if (transaction.docChanged) {
      return { view: EMPTY_RESULT_VIEW, showHints, decorations: Decoration.none };
    }

    return value;
  },

  provide: (field) => EditorView.decorations.from(field, (value) => value.decorations),
});

const setStatementHighlights = StateEffect.define();

function firstLineSpan(doc, span, className) {
  const to = Math.min(span.to, doc.lineAt(span.from).to);

  return to > span.from ? [Decoration.mark({ class: className }).range(span.from, to)] : [];
}

const statementHighlightField = StateField.define({
  create() {
    return Decoration.none;
  },

  update(decorations, transaction) {
    for (const effect of transaction.effects) {
      if (effect.is(setStatementHighlights)) {
        const { selected, hovered } = effect.value;
        const doc = transaction.state.doc;

        return Decoration.set(
          [
            ...(selected ? firstLineSpan(doc, selected, "cm-statement-selected") : []),
            ...(hovered ? firstLineSpan(doc, hovered, "cm-statement-hovered") : []),
          ],
          true,
        );
      }
    }

    return transaction.docChanged ? Decoration.none : decorations.map(transaction.changes);
  },

  provide: (field) => EditorView.decorations.from(field),
});

/*
 * Highlights are dispatched on the next frame: selection changes arrive inside an
 * editor update, where dispatching again is not allowed.
 */
function scheduleHighlights() {
  cancelAnimationFrame(highlightFrame);

  highlightFrame = requestAnimationFrame(() => {
    const usable = analysisModel && !analysisModel.stale;

    editor.dispatch({
      effects: setStatementHighlights.of({
        selected: usable ? inspection?.statement ?? null : null,
        hovered: usable ? hoveredSpan : null,
      }),
    });
  });
}

/*
 * The statement the cursor means: one starting on the cursor's line and
 * containing it, then any starting on that line, then any containing it -- the
 * smallest in the first non-empty group, so a loop body line selects its own
 * statement and not the loop around it.
 */
function statementAt(model, doc, pos) {
  const line = doc.lineAt(pos).number;
  const contains = (s) => s.from <= pos && pos <= s.to;
  const startsHere = (s) => s.line === line;

  const pools = [
    model.statements.filter((s) => startsHere(s) && contains(s)),
    model.statements.filter(startsHere),
    model.statements.filter(contains),
  ];

  const pool = pools.find((candidates) => candidates.length > 0) ?? [];

  return pool.reduce((best, s) => (!best || s.to - s.from < best.to - best.from ? s : best), null);
}

function inspectStatement(statement) {
  inspection = statement ? { statement, nodes: statement.nodes } : null;

  if (!inspection?.nodes.some((node) => node.id === focusedNodeId)) {
    focusedNodeId = null;
  }

  renderInspector();
  applyGraphSelection();
  scheduleHighlights();
}

function inspectCursor(state) {
  if (analysisModel && !analysisModel.stale) {
    inspectStatement(statementAt(analysisModel, state.doc, state.selection.main.head));
  }
}

function showAnalysisView(result, source) {
  const doc = editor.state.doc;

  /* A result for text the editor no longer holds cannot be placed. */
  if (doc.toString() !== source) {
    analysisModel = null;
    inspection = null;
    renderInspector();
    return;
  }

  analysisModel = result.status === "ok" ? buildAnalysisModel(result, doc) : null;

  showSolverGlobals(analysisModel ? result.seeds : null);

  const dimmed = analysisModel ? deadLines(analysisModel) : [];

  editor.dispatch({
    effects: setResultView.of({
      annotations: [
        ...resultAnnotations(result),
        ...(analysisModel ? deadAnnotations(analysisModel, dimmed) : []),
      ],
      deadLines: dimmed,
      hints: analysisModel ? valueHints(analysisModel) : [],
    }),
  });

  inspection = null;
  focusedNodeId = null;
  inspectCursor(editor.state);
  renderInspector();
}

function clearAnalysisView() {
  analysisModel = null;
  inspection = null;
  focusedNodeId = null;
  hoveredSpan = null;

  showSolverGlobals(null);

  editor.dispatch({ effects: setResultView.of(EMPTY_RESULT_VIEW) });

  renderInspector();
  scheduleHighlights();
}

function markAnalysisStale() {
  if (!analysisModel || analysisModel.stale) {
    return;
  }

  analysisModel.stale = true;
  inspection = null;
  focusedNodeId = null;
  hoveredSpan = null;

  renderInspector();
  applyGraphSelection();
}

/* -------------------------------------------------------------------------- */
/* Variable hover                                                             */
/* -------------------------------------------------------------------------- */

const VIMP_KEYWORDS = new Set(["fun", "global", "if", "else", "while", "return", "skip"]);

function variableTooltip(name, statement, rows) {
  const tooltip = document.createElement("div");

  tooltip.className = "cm-variable-tooltip";

  const head = document.createElement("div");

  head.className = "cm-variable-tooltip-head";

  const title = document.createElement("strong");

  title.textContent = name;
  head.append(title);

  if (rows.some(({ node }) => node.globals.some(([x]) => x === name))) {
    const global = document.createElement("span");

    global.className = "cm-variable-tooltip-tag";
    global.textContent = "global";
    head.append(global);
  }

  const where = document.createElement("span");

  where.className = "cm-variable-tooltip-where";
  where.textContent = statement.formals
    ? `on entry \u00b7 line ${statement.line}`
    : `before line ${statement.line} \u00b7 ${statement.point}`;
  head.append(where);

  const table = document.createElement("table");

  for (const { node, value } of rows) {
    const row = table.insertRow();
    const key = row.insertCell();

    key.textContent = node.context_key;
    key.className = "cm-variable-tooltip-key";
    row.insertCell().textContent = node.context;

    const cell = row.insertCell();

    cell.textContent = value ?? "unreachable";
    cell.className = value === null ? "cm-variable-tooltip-dead" : "cm-variable-tooltip-value";
  }

  tooltip.append(head, table);

  return tooltip;
}

/*
 * A variable's value as the statement under the pointer is reached, in every
 * context that statement has. Names the statement's contexts do not bind -- a
 * procedure name, a keyword -- get no tooltip.
 */
const variableHover = hoverTooltip(
  (view, pos) => {
    if (!analysisModel || analysisModel.stale) {
      return null;
    }

    const word = view.state.wordAt(pos);
    const name = word ? view.state.sliceDoc(word.from, word.to) : "";

    if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name) || VIMP_KEYWORDS.has(name) || name.startsWith("__voblint_")) {
      return null;
    }

    const statement = statementAt(analysisModel, view.state.doc, pos);

    const rows = (statement?.nodes ?? [])
      .map((node) => ({ node, value: isLive(node) ? valueOf(node, name) : null }))
      .filter(({ value }) => value !== undefined);

    if (!rows.some(({ value }) => value !== null)) {
      return null;
    }

    return {
      pos: word.from,
      end: word.to,
      above: true,
      create: () => ({ dom: variableTooltip(name, statement, rows) }),
    };
  },
  { hoverTime: 250 },
);

/* -------------------------------------------------------------------------- */
/* State inspector                                                            */
/* -------------------------------------------------------------------------- */

function inspectorMessage(text) {
  const message = document.createElement("p");

  message.className = "inspector-message";
  message.textContent = text;
  inspectorBody.replaceChildren(message);
}

function statementExcerpt(statement) {
  const doc = editor.state.doc;

  return doc.sliceString(statement.from, Math.min(statement.to, doc.lineAt(statement.from).to)).trim();
}

function renderInspector() {
  inspectorLocation.replaceChildren();

  if (!analysisModel) {
    inspectorMessage("Run the analysis, then place the cursor on a statement.");
    return;
  }

  if (analysisModel.stale) {
    inspectorMessage("The program changed since this run. Rerun to inspect states.");
    return;
  }

  if (!inspection) {
    inspectorMessage("Place the cursor on a statement to see its abstract state in every context.");
    return;
  }

  const { statement, nodes } = inspection;

  const point = document.createElement("strong");

  point.textContent = statement ? `${statement.point} · line ${statement.line}` : nodes[0].point;

  inspectorLocation.append(point);

  if (statement) {
    const excerpt = document.createElement("code");

    excerpt.textContent = statementExcerpt(statement);
    inspectorLocation.append(excerpt);
  }

  if (nodes.length === 0) {
    inspectorMessage("No context reaches this statement: the solver never analysed it.");
    return;
  }

  inspectorBody.replaceChildren(...nodes.map(renderInspectorContext));
}

function statusChip(status) {
  const chip = document.createElement("span");

  chip.className = `inspector-status ${status}`;
  chip.textContent = status;

  return chip;
}

/* A seed's bindings, one chip per "x=v" line exactly as OCaml named them. */
function seedLines(seed) {
  const lines = document.createElement("span");

  lines.className = "seed-lines";

  for (const line of seed.reachable ? seed.lines : []) {
    const chip = document.createElement("code");

    chip.textContent = line;
    lines.append(chip);
  }

  if (!seed.reachable) {
    lines.textContent = "unreachable";
  } else if (seed.lines.length === 0) {
    lines.textContent = "no formals or globals";
  }

  return lines;
}

/*
 * The seed a procedure entry reads back: what the calls routed to this context
 * published, merged by the globals rule, as formals and globals. An unreachable seed
 * is a context no call enters, which is how the program's own entry procedure reads.
 */
function renderSeed(seed) {
  const row = document.createElement("div");

  row.className = seed.reachable ? "inspector-seed" : "inspector-seed dead";

  const label = document.createElement("span");

  label.className = "inspector-seed-label";
  label.textContent = "seed";
  label.title = seed.reachable
    ? `${seed.key}: formals and globals the calls routed to this context published`
    : `${seed.key}: no call enters this context`;

  row.append(label, seedLines(seed));

  return row;
}

function renderInspectorContext(node) {
  const block = document.createElement("section");

  block.className = node.id === focusedNodeId ? "inspector-context focused" : "inspector-context";

  const header = document.createElement("button");

  header.type = "button";
  header.className = "inspector-context-header";
  header.title = "Show this context's node in the graph";
  header.addEventListener("click", () => focusNode(node.id, { reveal: true }));

  const label = document.createElement("span");

  label.className = "inspector-context-label";

  if (node.context_key) {
    const key = document.createElement("span");

    key.className = "inspector-context-key";
    key.textContent = node.context_key;
    header.append(key);
  }

  label.textContent = node.context || node.id;
  header.append(label);

  if (node.status) {
    header.append(statusChip(node.status));
  }

  block.append(header);

  if (!isLive(node)) {
    const dead = document.createElement("p");

    dead.className = "inspector-message";
    dead.textContent = "Unreachable in this context.";
    block.append(dead);

    return block;
  }

  block.append(renderStateTable(node));

  const seed = analysisModel.seedByEntry.get(node.id);

  if (seed) {
    block.append(renderSeed(seed));
  }

  const findings = node.findings.filter((finding) => finding !== "unreachable");

  if (findings.length > 0) {
    const list = document.createElement("ul");

    list.className = "inspector-findings";

    for (const finding of findings) {
      const item = document.createElement("li");

      item.textContent = finding;
      list.append(item);
    }

    block.append(list);
  }

  return block;
}

/*
 * The state as the statement is reached: locals first, then globals, each in the
 * order the analysis lists them.
 */
function renderStateTable(node) {
  const bindings = [...node.bindings, ...node.globals];

  if (bindings.length === 0) {
    const empty = document.createElement("p");

    empty.className = "inspector-message";
    empty.textContent = "No variables in scope.";

    return empty;
  }

  const globals = new Set(node.globals.map(([name]) => name));

  const table = document.createElement("table");
  const head = table.createTHead().insertRow();
  const row = table.createTBody().insertRow();

  for (const [name, value] of bindings) {
    const title = document.createElement("th");

    title.textContent = name;

    if (globals.has(name)) {
      title.className = "global";
      title.title = "global variable";
    }

    head.append(title);
    row.insertCell().textContent = value;
  }

  const wrapper = document.createElement("div");

  wrapper.className = "inspector-table";
  wrapper.append(table);

  return wrapper;
}

/* -------------------------------------------------------------------------- */
/* Graph linking                                                              */
/* -------------------------------------------------------------------------- */

function graphNodeElement(id) {
  return graph.querySelector(`g.node#${CSS.escape(id)}`);
}

function applyGraphSelection() {
  for (const element of graph.querySelectorAll("g.node.graph-node-selected, g.node.graph-node-focused")) {
    element.classList.remove("graph-node-selected", "graph-node-focused");
  }

  if (!analysisModel || analysisModel.stale || !inspection) {
    return;
  }

  for (const node of inspection.nodes) {
    const element = graphNodeElement(node.id);

    element?.classList.add("graph-node-selected");

    if (node.id === focusedNodeId) {
      element?.classList.add("graph-node-focused");
    }
  }
}

/* Pans only the graph's own view; the page stays where the reader put it. */
function revealGraphNodes(ids) {
  const rects = ids
    .map(graphNodeElement)
    .filter(Boolean)
    .map((element) => element.getBoundingClientRect());

  if (graphPanel.hidden || rects.length === 0) {
    return;
  }

  const viewport = graph.getBoundingClientRect();

  const left = Math.min(...rects.map((r) => r.left));
  const right = Math.max(...rects.map((r) => r.right));
  const top = Math.min(...rects.map((r) => r.top));
  const bottom = Math.max(...rects.map((r) => r.bottom));

  const visible =
    left >= viewport.left && right <= viewport.right && top >= viewport.top && bottom <= viewport.bottom;

  if (!visible) {
    panGraphBy(
      (viewport.left + viewport.right) / 2 - (left + right) / 2,
      (viewport.top + viewport.bottom) / 2 - (top + bottom) / 2,
      { animate: true },
    );
  }

  for (const id of ids) {
    const element = graphNodeElement(id);

    element?.classList.remove("graph-node-flash");
    void element?.getBoundingClientRect();
    element?.classList.add("graph-node-flash");
  }
}

function focusNode(id, { reveal = false } = {}) {
  focusedNodeId = id;

  renderInspector();
  applyGraphSelection();

  if (reveal) {
    revealGraphNodes([id]);
  }
}

/* Moves the editor's own scroller to a line without scrolling the page. */
function scrollEditorTo(pos) {
  const scroller = editor.scrollDOM;
  const block = editor.lineBlockAt(pos);

  scroller.scrollTo({
    top: Math.max(0, block.top - scroller.clientHeight / 2 + block.height / 2),
    behavior: "smooth",
  });
}

/* -------------------------------------------------------------------------- */
/* Solver globals                                                             */
/* -------------------------------------------------------------------------- */

/*
 * One seed per procedure entry per context: the state the calls routed there
 * published, which that entry reads back. A seed that feeds a graph node jumps to it.
 */
function showSolverGlobals(seeds) {
  solverGlobalsList.replaceChildren();
  solverGlobals.hidden = !seeds || seeds.length === 0;

  if (solverGlobals.hidden) {
    return;
  }

  const entered = seeds.filter((seed) => seed.reachable).length;

  solverGlobalsCount.textContent = `${seeds.length} seeds \u00b7 ${entered} entered`;

  for (const seed of seeds) {
    const item = document.createElement("li");

    item.className = seed.reachable ? "solver-global" : "solver-global dead";

    const key = seed.entry ? document.createElement("button") : document.createElement("span");

    key.className = "solver-global-key";
    key.textContent = seed.key;

    if (seed.entry) {
      key.type = "button";
      key.title = "Inspect the procedure entry this seed feeds";
      key.addEventListener("click", () => {
        inspectGraphNode(seed.entry);
        revealGraphNodes([seed.entry]);
      });
    }

    item.append(key, seedLines(seed));
    solverGlobalsList.append(item);
  }
}

function inspectGraphNode(id) {
  const node = analysisModel?.nodes.get(id);

  if (!node || analysisModel.stale) {
    return;
  }

  const statement = analysisModel.statementByPoint.get(node.point);

  focusedNodeId = id;

  if (!statement) {
    inspection = { statement: null, nodes: [node] };
    renderInspector();
    applyGraphSelection();
    scheduleHighlights();
    return;
  }

  /* Moving the cursor re-inspects through the update listener; keep the focus. */
  editor.dispatch({ selection: { anchor: statement.from } });
  inspectStatement(statement);
  scrollEditorTo(statement.from);
}

function attachGraphNavigation(svg) {
  let hoveredId = null;

  svg.addEventListener("pointermove", (event) => {
    const id = event.target.closest?.("g.node")?.id ?? null;

    if (id === hoveredId) {
      return;
    }

    hoveredId = id;

    const node = id ? analysisModel?.nodes.get(id) : null;

    hoveredSpan = node ? analysisModel.statementByPoint.get(node.point) ?? null : null;
    scheduleHighlights();
  });

  svg.addEventListener("pointerleave", () => {
    hoveredId = null;
    hoveredSpan = null;
    scheduleHighlights();
  });

  svg.addEventListener("click", (event) => {
    const id = event.target.closest?.("g.node")?.id;

    if (id) {
      inspectGraphNode(id);
    }
  });

  applyGraphSelection();
}

/* -------------------------------------------------------------------------- */
/* Analysis graph                                                             */
/* -------------------------------------------------------------------------- */

let vizPromise = null;
let analysisRunGeneration = 0;

/*
 * The graph sits in a fixed-size view and moves by a CSS transform, so panning and
 * zooming never scroll the page or resize the layout. `graphView` is the transform:
 * the drawing's top-left corner lands at (x, y) in view pixels, scaled by `scale`.
 */
const graphView = { scale: 1, x: 0, y: 0, width: 0, height: 0, fitted: true };

const MIN_GRAPH_SCALE = 0.1;
const MAX_GRAPH_SCALE = 4;
const GRAPH_ZOOM_STEP = 1.2;
const GRAPH_PADDING = 24;

function clamp(value, lo, hi) {
  return Math.min(hi, Math.max(lo, value));
}

function currentGraphSvg() {
  return graph.querySelector("svg");
}

function updateZoomResetLabel() {
  graphZoomReset.textContent = `${Math.round(graphView.scale * 100)}%`;
}

function clearGraph() {
  Object.assign(graphView, { scale: 1, x: 0, y: 0, width: 0, height: 0, fitted: true });
  updateZoomResetLabel();

  graph.replaceChildren();
  graphPanel.hidden = true;
  hideGraphTooltip();
}

/*
 * A graph that failed to render is a different outcome from an analysis that
 * failed: the analysis result is valid and already displayed, and the graph
 * panel carries its own message. Tagging the rethrow lets run()'s outer catch
 * keep that message instead of clearing it and reporting an analysis failure.
 */
class GraphRenderError extends Error {
  constructor(message, options) {
    super(message, options);

    this.name = "GraphRenderError";
  }
}

function showGraphMessage(message, kind = "") {
  const row = document.createElement("p");

  row.className = kind ? `analysis-graph-message ${kind}` : "analysis-graph-message";

  row.textContent = message;

  graph.replaceChildren(row);
  graphPanel.hidden = false;
}

function getViz() {
  if (!vizPromise) {
    vizPromise = import("https://esm.sh/@viz-js/viz@3.30.0")
      .then((Viz) => Viz.instance())
      .catch((error) => {
        vizPromise = null;
        throw error;
      });
  }

  return vizPromise;
}

/*
 * Measure the drawing once, untransformed, in rendered CSS pixels: GraphViz sizes
 * its SVG in points, and measuring after layout avoids converting units by hand.
 */
function rememberNaturalGraphSize(svg) {
  svg.style.transform = "none";

  const rect = svg.getBoundingClientRect();

  graphView.width = rect.width;
  graphView.height = rect.height;
  svg.style.width = `${rect.width}px`;
  svg.style.height = `${rect.height}px`;
}

function applyGraphView({ animate = false } = {}) {
  const svg = currentGraphSvg();

  if (!svg || graphView.width <= 0) {
    updateZoomResetLabel();
    return;
  }

  svg.classList.toggle("is-animating", animate);
  svg.style.transform = `translate(${graphView.x}px, ${graphView.y}px) scale(${graphView.scale})`;
  updateZoomResetLabel();
}

/* Zooms about a point given in view coordinates, keeping that point under the pointer. */
function zoomGraphAt(factor, viewX, viewY, options = {}) {
  const scale = clamp(graphView.scale * factor, MIN_GRAPH_SCALE, MAX_GRAPH_SCALE);
  const ratio = scale / graphView.scale;

  graphView.x = viewX - (viewX - graphView.x) * ratio;
  graphView.y = viewY - (viewY - graphView.y) * ratio;
  graphView.scale = scale;
  graphView.fitted = false;
  applyGraphView(options);
}

function viewCenter() {
  return { x: graph.clientWidth / 2, y: graph.clientHeight / 2 };
}

function zoomGraphIn() {
  const { x, y } = viewCenter();
  zoomGraphAt(GRAPH_ZOOM_STEP, x, y, { animate: true });
}

function zoomGraphOut() {
  const { x, y } = viewCenter();
  zoomGraphAt(1 / GRAPH_ZOOM_STEP, x, y, { animate: true });
}

function panGraphBy(dx, dy, options = {}) {
  graphView.x += dx;
  graphView.y += dy;
  graphView.fitted = false;
  applyGraphView(options);
}

/* 100%: natural size, centered on whatever is at the middle of the view now. */
function resetGraphZoom() {
  const { x, y } = viewCenter();
  zoomGraphAt(1 / graphView.scale, x, y, { animate: true });
}

/*
 * Fit the whole drawing and center it. A graph so tall that fitting it would make
 * its labels unreadable fits the width instead and starts at its top.
 */
function fitGraphZoom({ animate = true } = {}) {
  if (graphView.width <= 0) {
    return;
  }

  const width = Math.max(1, graph.clientWidth - 2 * GRAPH_PADDING);
  const height = Math.max(1, graph.clientHeight - 2 * GRAPH_PADDING);
  const byWidth = width / graphView.width;
  const whole = Math.min(1, byWidth, height / graphView.height);
  const scale = whole >= 0.45 ? whole : Math.min(1, byWidth);

  graphView.scale = scale;
  graphView.x = (graph.clientWidth - graphView.width * scale) / 2;
  graphView.y = graphView.height * scale <= height
    ? (graph.clientHeight - graphView.height * scale) / 2
    : GRAPH_PADDING;
  graphView.fitted = true;
  applyGraphView({ animate });
}

/* Whether the drawing overflows the view along an axis, so a scroll there should pan it. */
function graphOverflows(axis) {
  return axis === "x"
    ? graphView.width * graphView.scale > graph.clientWidth
    : graphView.height * graphView.scale > graph.clientHeight;
}

const XLINK = "http://www.w3.org/1999/xlink";

const graphTooltip = document.createElement("div");
graphTooltip.className = "graph-tooltip";
graphTooltip.hidden = true;
document.body.append(graphTooltip);

function hideGraphTooltip() {
  graphTooltip.hidden = true;
  delete graphTooltip.dataset.node;
}

function placeGraphTooltip(event) {
  const margin = 14;
  const { width, height } = graphTooltip.getBoundingClientRect();
  const left = event.clientX + margin + width > window.innerWidth
    ? event.clientX - margin - width
    : event.clientX + margin;
  const top = event.clientY + margin + height > window.innerHeight
    ? event.clientY - margin - height
    : event.clientY + margin;

  graphTooltip.style.left = `${Math.max(4, left)}px`;
  graphTooltip.style.top = `${Math.max(4, top)}px`;
}

/*
 * GraphViz writes a node's DOT tooltip (its point, state and findings) as the
 * xlink:title of the node's link. Move it into a dataset and drop the link, whose
 * javascript: target belongs to the HTML report's frontend, so hovering shows one
 * styled popup instead of the browser's plain title.
 */
function attachGraphTooltips(svg) {
  for (const link of svg.querySelectorAll("g.node a")) {
    const node = link.closest("g.node");
    node.dataset.tooltip = link.getAttributeNS(XLINK, "title") ?? "";
    link.removeAttributeNS(XLINK, "title");
    link.removeAttributeNS(XLINK, "href");
    link.removeAttribute("href");
  }

  for (const title of svg.querySelectorAll("g.node > title")) {
    title.remove();
  }

  svg.addEventListener("pointermove", (event) => {
    const node = event.target.closest?.("g.node");

    if (!node?.dataset.tooltip) {
      hideGraphTooltip();
      return;
    }

    const [heading, ...lines] = node.dataset.tooltip.split("\n");
    const title = document.createElement("strong");
    title.textContent = heading;
    const body = document.createElement("pre");
    body.textContent = lines.length > 0 ? lines.join("\n") : "no bindings";

    if (graphTooltip.dataset.node !== node.id) {
      graphTooltip.replaceChildren(title, body);
      graphTooltip.dataset.node = node.id;
    }

    graphTooltip.hidden = false;
    placeGraphTooltip(event);
  });

  svg.addEventListener("pointerleave", hideGraphTooltip);
}

async function renderGraph(dot, runGeneration) {
  /*
   * The table is rendered synchronously, while Viz.js may still be loading.
   * Never let a graph from an older run overwrite the result of a newer run.
   */
  if (runGeneration !== analysisRunGeneration) {
    return;
  }

  if (typeof dot !== "string" || dot.trim() === "") {
    throw new Error("Internal error: successful analysis returned no control-flow graph.");
  }

  showGraphMessage("Rendering control-flow graph...");

  try {
    const viz = await getViz();

    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    const svg = viz.renderSVGElement(dot, {
      engine: "dot",
    });

    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    attachGraphTooltips(svg);
    attachGraphNavigation(svg);
    graph.replaceChildren(svg);
    graphPanel.hidden = false;

    rememberNaturalGraphSize(svg);
    fitGraphZoom({ animate: false });
  } catch (error) {
    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    const detail = error instanceof Error ? error.message : String(error);

    showGraphMessage(`Graph rendering failed: ${detail}`, "error");

    throw new GraphRenderError(`Graph rendering failed: ${detail}`, { cause: error });
  }
}

/* -------------------------------------------------------------------------- */
/* Configuration                                                              */
/* -------------------------------------------------------------------------- */

function updateContextControls() {
  const usesCallString = contextSelect.value === "call-string";

  contextDepthGroup.hidden = !usesCallString;

  contextDepthInput.disabled = !usesCallString;
}

function updateGlobalsHelp() {
  const descriptions = {
    join: "Join every value side-effected into a global.",

    "per-origin": "Keep side-effected values separate by origin before joining them.",

    warrow: "Widen, then narrow, every value side-effected into a global.",

    "warrow-per-origin": "Widen and narrow side-effected values separately per origin.",
  };

  globalsHelp.textContent = descriptions[globalsSelect.value] ?? "";
}

function readConfiguration() {
  const analysis = analysisSelect.value;

  const globals = globalsSelect.value;

  const context = contextSelect.value;

  const allowedGlobals = new Set(["join", "per-origin", "warrow", "warrow-per-origin"]);

  if (!allowedGlobals.has(globals)) {
    throw new Error(`Unknown globals rule: ${globals}`);
  }

  const allowedContexts = new Set(["none", "entry-state", "call-string"]);

  if (!allowedContexts.has(context)) {
    throw new Error(`Unknown context mode: ${context}`);
  }

  let contextDepth = 0;

  if (context === "call-string") {
    contextDepth = Number.parseInt(contextDepthInput.value, 10);

    if (!Number.isInteger(contextDepth) || contextDepth < 0) {
      throw new Error("Call-string depth must be a non-negative integer.");
    }
  }

  return {
    analysis,
    globals,
    context,
    contextDepth,
  };
}

function selectedLabel(select) {
  return select.options[select.selectedIndex]?.text ?? select.value;
}

function configurationLabel(configuration) {
  const parts = [selectedLabel(analysisSelect), selectedLabel(globalsSelect), selectedLabel(contextSelect)];

  if (configuration.context === "call-string") {
    parts.push(`k=${configuration.contextDepth}`);
  }

  return parts.join(" · ");
}

/* -------------------------------------------------------------------------- */
/* Run analysis                                                               */
/* -------------------------------------------------------------------------- */

function setRunning(running) {
  runButton.disabled = running;

  if (running) {
    runButton.classList.add("running");
    runButtonIcon.className = "fa-solid fa-spinner";
    runButtonLabel.textContent = "Analyzing";
  } else {
    runButton.classList.remove("running");
    runButtonIcon.className = "fa-solid fa-play";
    runButtonLabel.textContent = "Run analysis";
  }
}

/* -------------------------------------------------------------------------- */
/* Analysis worker                                                            */
/* -------------------------------------------------------------------------- */

function discardAnalysisWorker(worker = analysisWorker) {
  if (worker) {
    worker.terminate();
  }

  if (analysisWorker === worker) {
    analysisWorker = null;
  }
}


function failPendingAnalysis(error) {
  if (!pendingAnalysis) {
    return;
  }

  const pending = pendingAnalysis;
  pendingAnalysis = null;

  pending.reject(
    error instanceof Error
      ? error
      : new Error(String(error)),
  );
}


/*
 * A result describes the configuration it ran under, so changing any setting
 * retires it: a finished run is cleared, and a pending one is cancelled rather than
 * allowed to land under settings it was not computed with. Bumping the generation
 * makes the cancelled run's own handlers stand down.
 */
function resetForConfigurationChange() {
  const hadResult = pendingAnalysis || analysisModel || !graphPanel.hidden || rawRunProgram !== null;

  analysisRunGeneration++;

  if (pendingAnalysis) {
    discardAnalysisWorker();
    failPendingAnalysis(new Error("Analysis cancelled: the configuration changed."));
  }

  setRunning(false);
  clearGraph();
  clearTiming();
  clearAnalysisView();
  clearProblems();
  showRawRunProgram(null);

  if (hadResult) {
    showStatus("Configuration changed \u00b7 run again");
  }
}

function createAnalysisWorker() {
  const worker = new Worker("assets/voblint-worker.js");

  worker.addEventListener("message", (event) => {
    const message = event.data;

    if (
      !pendingAnalysis ||
      !message ||
      message.id !== pendingAnalysis.id
    ) {
      return;
    }

    const pending = pendingAnalysis;
    pendingAnalysis = null;

    if (message.type === "result") {
      pending.resolve(message.result);
      return;
    }

    if (message.type === "error") {
      discardAnalysisWorker(worker);
      pending.reject(workerError(message));
      return;
    }

    discardAnalysisWorker(worker);

    pending.reject(
      new Error(
        `Analysis worker returned unknown message type: ${String(message.type)}`,
      ),
    );
  });

  worker.addEventListener("error", (event) => {
    discardAnalysisWorker(worker);

    const error =
      event.error instanceof Error
        ? event.error
        : new Error(
            event.message || "Analysis worker failed.",
          );

    failPendingAnalysis(error);
  });

  worker.addEventListener("messageerror", (event) => {
    discardAnalysisWorker(worker);

    console.error(
      "Could not decode the analysis worker response:",
      event.data,
    );

    failPendingAnalysis(
      new Error(
        "Could not decode the analysis worker response.",
      ),
    );
  });

  return worker;
}


function getAnalysisWorker() {
  if (!analysisWorker) {
    analysisWorker = createAnalysisWorker();
  }

  return analysisWorker;
}


function runAnalysisInWorker(configuration, source) {
  if (pendingAnalysis) {
    throw new Error("An analysis is already running.");
  }

  const id = nextAnalysisRequestId++;

  return new Promise((resolve, reject) => {
    pendingAnalysis = {
      id,
      resolve,
      reject,
    };

    try {
      getAnalysisWorker().postMessage({
        type: "run",
        id,
        analysis: configuration.analysis,
        globals: configuration.globals,
        context: configuration.context,
        contextDepth: configuration.contextDepth,
        source,
      });
    } catch (error) {
      pendingAnalysis = null;
      discardAnalysisWorker();

      reject(
        error instanceof Error
          ? error
          : new Error(String(error)),
      );
    }
  });
}

async function run() {
  /*
   * Treat one click / shortcut invocation as one UI transaction.
   *
   * Starting a new run invalidates every pending graph render from older
   * runs. It also clears both presentation surfaces before configuration
   * validation, so an invalid selection can never leave an old graph next to
   * a new error/table state.
   */
  if (runButton.disabled || pendingAnalysis) {
    return;
  }

  const runGeneration = ++analysisRunGeneration;

  clearGraph();
  clearTiming();
  clearAnalysisView();
  clearProblems();
  showRawRunProgram(null);

  let configuration;

  try {
    configuration = readConfiguration();
  } catch (error) {
    if (runGeneration === analysisRunGeneration) {
      const message = error instanceof Error ? error.message : String(error);
      showStatus(message, "error");
      showProblem({ title: "These settings cannot run", message });
    }

    return;
  }

  const source = editor.state.doc.toString();

  setRunning(true);

  showStatus("Analyzing...");

  try {
    /*
     * IMPORTANT:
     *
     * The browser adapter takes FIVE arguments:
     *
     *   analysis
     *   globals rule
     *   context
     *   context depth
     *   source
     */
    const rawResult = await runAnalysisInWorker(configuration, source);

    if (typeof rawResult !== "string") {
      throw new TypeError("Voblint_run returned " + `${typeof rawResult}; expected a JSON string.`);
    }

    const result = JSON.parse(rawResult);

    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    renderTiming(result);
    showRawRunProgram(result.raw);
    showAnalysisView(result, source);

    if (result.status === "ok") {
      /*
       * Every supported successful analysis is required to expose its control-
       * flow graph. Keep the run open until that graph has rendered; a missing
       * graph is an internal contract violation and fails the run rather than
       * being presented as a supported graph-less configuration.
       */
      await renderGraph(result.graph, runGeneration);

      if (runGeneration === analysisRunGeneration) {
        showStatus(`${configurationLabel(configuration)} · complete`, "ok");
        showDiagnosticsSummary(result);
      }
    } else {
      /*
       * The graph was already cleared at the start of this run. Leave it
       * cleared on analysis/configuration errors rather than preserving a
       * drawing from a previous successful result.
       */
      if (runGeneration === analysisRunGeneration) {
        clearGraph();

        showStatus(`${configurationLabel(configuration)} · ${failureTitle(result).toLowerCase()}`, "error");
        showProblem({ title: failureTitle(result), message: result.message, line: result.line, column: result.column });
      }
    }
  } catch (error) {
    if (runGeneration === analysisRunGeneration) {
      /*
       * A render failure leaves the analysis result and the graph panel's own
       * message standing; only an analysis failure clears the graph and
       * reports its error in the status line.
       */
      if (error instanceof GraphRenderError) {
        showStatus(`${configurationLabel(configuration)} · graph rendering failed`, "error");
        showProblem({
          kind: "warning",
          title: "The result is ready, but the graph could not be drawn",
          message: error.message,
        });

        console.error(error);

        return;
      }

      clearGraph();

      const message = error instanceof Error ? error.message : String(error);
      showStatus("Browser analysis failed", "error");
      showProblem({ title: "The analyzer stopped", message });

      if (error instanceof Error) {
        console.error(
          `${error.name}: ${error.message}\n\n${error.stack ?? ""}`,
        );
      } else {
        console.error("Browser analysis failed:", error);
      }
    }
  } finally {
    /*
     * An older async run must not re-enable the button while a newer run is
     * still active.
     */
    if (runGeneration === analysisRunGeneration) {
      setRunning(false);
    }
  }
}

/* -------------------------------------------------------------------------- */
/* CodeMirror                                                                 */
/* -------------------------------------------------------------------------- */

const editor = new EditorView({
  doc: initialProgram,

  extensions: [
    basicSetup,

    vimpLanguage,

    syntaxHighlighting(codeHighlight),

    resultViewField,

    statementHighlightField,

    variableHover,

    EditorView.updateListener.of((update) => {
      if (update.docChanged) {
        markAnalysisStale();
      } else if (update.selectionSet) {
        inspectCursor(update.state);
      }
    }),

    EditorView.domEventHandlers({
      click() {
        if (inspection) {
          revealGraphNodes(inspection.nodes.map((node) => node.id));
        }

        return false;
      },

      keydown(event) {
        if ((event.metaKey || event.ctrlKey) && event.key === "Enter") {
          event.preventDefault();

          run();

          return true;
        }

        return false;
      },
    }),
  ],

  parent: editorMount,
});

/* -------------------------------------------------------------------------- */
/* Events                                                                     */
/* -------------------------------------------------------------------------- */

runButton.addEventListener("click", run);

valueHintsToggle.addEventListener("change", () => {
  editor.dispatch({ effects: setValueHintsVisible.of(valueHintsToggle.checked) });
});

contextSelect.addEventListener("change", updateContextControls);

for (const control of [analysisSelect, globalsSelect, contextSelect, contextDepthInput]) {
  control.addEventListener("change", resetForConfigurationChange);
}

globalsSelect.addEventListener("change", updateGlobalsHelp);

graphZoomIn.addEventListener("click", zoomGraphIn);

graphZoomOut.addEventListener("click", zoomGraphOut);

graphZoomReset.addEventListener("click", resetGraphZoom);

graphZoomFit.addEventListener("click", fitGraphZoom);

/*
 * Trackpad: a two-finger scroll pans; a pinch arrives as a wheel event with ctrlKey
 * set (Chrome, Firefox, Edge) or as gesture events (Safari) and zooms at the pointer.
 * A scroll along an axis the drawing already fits is left to the page.
 */
graph.addEventListener(
  "wheel",
  (event) => {
    if (!currentGraphSvg()) {
      return;
    }

    const bounds = graph.getBoundingClientRect();

    if (event.ctrlKey || event.metaKey) {
      event.preventDefault();
      /* A pinch sends small deltas; a wheel notch sends ~100, so cap one event's step. */
      const delta = clamp(event.deltaY * (event.deltaMode === 1 ? 16 : 1), -30, 30);
      zoomGraphAt(Math.exp(-delta * 0.01), event.clientX - bounds.left, event.clientY - bounds.top);
      return;
    }

    const panX = graphOverflows("x") ? event.deltaX : 0;
    const panY = graphOverflows("y") ? event.deltaY : 0;

    if (panX === 0 && panY === 0) {
      return;
    }

    event.preventDefault();
    panGraphBy(-panX, -panY);
  },
  { passive: false },
);

let gestureScale = 1;

graph.addEventListener("gesturestart", (event) => {
  event.preventDefault();
  gestureScale = 1;
});

graph.addEventListener("gesturechange", (event) => {
  event.preventDefault();
  const bounds = graph.getBoundingClientRect();
  zoomGraphAt(event.scale / gestureScale, event.clientX - bounds.left, event.clientY - bounds.top);
  gestureScale = event.scale;
});

/*
 * Mouse and touch: one pointer drags, two pointers pinch. A press that barely moves
 * stays a click, so clicking a node still inspects it.
 */
const graphPointers = new Map();
let graphDrag = null;
let suppressGraphClick = false;

graph.addEventListener("pointerdown", (event) => {
  if (!currentGraphSvg() || event.button > 0) {
    return;
  }

  graphPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });

  if (graphPointers.size === 1) {
    graphDrag = { x: event.clientX, y: event.clientY, moved: false };
  }
});

graph.addEventListener("pointermove", (event) => {
  const previous = graphPointers.get(event.pointerId);

  if (!previous) {
    return;
  }

  const bounds = graph.getBoundingClientRect();

  if (graphPointers.size === 2) {
    const [a, b] = [...graphPointers.values()];
    const before = Math.hypot(a.x - b.x, a.y - b.y);
    graphPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
    const [c, d] = [...graphPointers.values()];
    const after = Math.hypot(c.x - d.x, c.y - d.y);

    if (before > 0) {
      zoomGraphAt(after / before, (c.x + d.x) / 2 - bounds.left, (c.y + d.y) / 2 - bounds.top);
    }

    suppressGraphClick = true;
    return;
  }

  graphPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });

  if (graphDrag) {
    if (!graphDrag.moved && Math.hypot(event.clientX - graphDrag.x, event.clientY - graphDrag.y) < 4) {
      return;
    }

    if (!graphDrag.moved) {
      graphDrag.moved = true;
      graph.setPointerCapture(event.pointerId);
      graph.classList.add("is-panning");
      hideGraphTooltip();
    }

    panGraphBy(event.clientX - previous.x, event.clientY - previous.y);
  }
});

function endGraphPointer(event) {
  graphPointers.delete(event.pointerId);

  if (graphPointers.size === 0) {
    suppressGraphClick = suppressGraphClick || Boolean(graphDrag?.moved);
    graphDrag = null;
    graph.classList.remove("is-panning");
  }
}

graph.addEventListener("pointerup", endGraphPointer);
graph.addEventListener("pointercancel", endGraphPointer);

/* A drag or pinch ends with a click on whatever is under the pointer; swallow it. */
graph.addEventListener(
  "click",
  (event) => {
    if (suppressGraphClick) {
      event.stopPropagation();
      event.preventDefault();
      suppressGraphClick = false;
    }
  },
  { capture: true },
);

graph.addEventListener("dblclick", (event) => {
  if (!event.target.closest?.("g.node")) {
    fitGraphZoom();
  }
});

graph.addEventListener("keydown", (event) => {
  const step = 60;
  const actions = {
    "+": zoomGraphIn,
    "=": zoomGraphIn,
    "-": zoomGraphOut,
    "0": () => fitGraphZoom(),
    ArrowLeft: () => panGraphBy(step, 0, { animate: true }),
    ArrowRight: () => panGraphBy(-step, 0, { animate: true }),
    ArrowUp: () => panGraphBy(0, step, { animate: true }),
    ArrowDown: () => panGraphBy(0, -step, { animate: true }),
  };

  if (actions[event.key] && currentGraphSvg()) {
    event.preventDefault();
    actions[event.key]();
  }
});

/* A view that still shows the fitted graph stays fitted when the page resizes. */
new ResizeObserver(() => {
  if (graphView.fitted && currentGraphSvg()) {
    fitGraphZoom({ animate: false });
  }
}).observe(graph);

updateContextControls();
updateGlobalsHelp();
renderRawCall(null);
renderInspector();
updateZoomResetLabel();

/* -------------------------------------------------------------------------- */
/* Links from the explainer                                                   */
/* -------------------------------------------------------------------------- */

/*
 * The explainer's "Try it" links open a program and a configuration here:
 * playground.html?example=two-sites&globals=warrow. Every program below is one the
 * explainer shows, so the run reproduces what the page claims.
 */
const LINKED_EXAMPLES = {
  "two-sites": `fun p(x) {
  __voblint_check(x <= 2);
}

fun main() {
  p(1);
  p(2);
}`,
  "loop-call": `fun g(x) {
  __voblint_check(x < 10);
}

fun main() {
  x = 0;
  while (x < 10) {
    g(x);
    x = x + 1;
  }
}`,
  "recursion-grows": `fun f(x) {
  __voblint_check(x >= 0);
  f(x + 1);
}

fun main() {
  f(0);
}`,
  "recursion-shrinks": `fun f(a) {
  if (a < 4) {
    f(9 / (a + 2));
  }
  __voblint_check(a <= 9);
}

fun main() {
  f(-1);
}`,
  "counting-loop": `fun main() {
  i = 0;
  while (i < 5) {
    i = i + 1;
  }
  __voblint_check(i == 5);
}`,
  "goblint-1587": `// goblint/analyzer #1587: 3Z - 2 was computed as 3Z, killing the branch below.
fun main() {
  n = __voblint_nondet_int();
  x = 3 * n;
  y = x - 2;
  if (y == 4) {
    __voblint_check(y == 4);
  }
}`,
  "theorems": `fun main() {
  n = __voblint_nondet_int();
  if (n > 0) {
    q = 10 / n;
    __voblint_check(n >= 1);
  } else {
    if (n > 5) {
      __voblint_check(n == 0);
    }
  }
}`,
};

function selectIfOffered(select, value) {
  if (value !== null && [...select.options].some((option) => option.value === value)) {
    select.value = value;
  }
}

function applyLinkedConfiguration() {
  const params = new URLSearchParams(location.search);

  if (![...params.keys()].length) {
    return;
  }

  const example = LINKED_EXAMPLES[params.get("example")];

  if (example) {
    editor.dispatch({ changes: { from: 0, to: editor.state.doc.length, insert: example } });
  }

  selectIfOffered(analysisSelect, params.get("analysis"));
  selectIfOffered(globalsSelect, params.get("globals"));
  selectIfOffered(contextSelect, params.get("context"));

  const depth = Number.parseInt(params.get("k") ?? "", 10);

  if (Number.isInteger(depth) && depth >= 0) {
    contextDepthInput.value = String(depth);
  }

  updateContextControls();
  updateGlobalsHelp();
  run();
}

applyLinkedConfiguration();
