import { json } from "https://esm.sh/@codemirror/lang-json@6.0.2";
import {
  HighlightStyle,
  StreamLanguage,
  syntaxHighlighting,
} from "https://esm.sh/@codemirror/language@6.12.4";
import {
  EditorState,
  Prec,
  StateEffect,
  StateField,
} from "https://esm.sh/@codemirror/state@^6.0.0";
/*
 * Same semver ranges codemirror@6.0.2 itself imports, so esm.sh resolves them to
 * the one module instance basicSetup uses. A second @codemirror/state instance
 * rejects every extension built from it.
 */
import {
  Decoration,
  hoverTooltip,
  keymap,
  WidgetType,
} from "https://esm.sh/@codemirror/view@^6.0.0";
import { tags } from "https://esm.sh/@lezer/highlight@1.2.3";
import { basicSetup, EditorView } from "https://esm.sh/codemirror@6.0.2";
import { vimpStreamParser } from "./code-tokens.js";

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
const graphSaveImage = query("#graph-save-image");

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
 * (Interval, Warrow, call string k=1):
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

const vimpLanguage = StreamLanguage.define(vimpStreamParser);

/* Shared by the VIMP editor and the raw JSON views; each language uses its own tags. */
const codeHighlight = HighlightStyle.define([
  {
    tag: tags.keyword,
    color: "var(--tok-keyword)",
    fontWeight: "650",
  },
  {
    tag: tags.number,
    color: "var(--tok-number)",
  },
  {
    tag: tags.operator,
    color: "var(--tok-operator)",
  },
  {
    tag: tags.comment,
    color: "var(--tok-comment)",
    fontStyle: "italic",
  },
  {
    tag: tags.standard(tags.variableName),
    color: "var(--tok-builtin)",
    fontWeight: "600",
  },
  {
    tag: tags.variableName,
    color: "var(--tok-name)",
  },
  {
    tag: tags.punctuation,
    color: "var(--tok-punct)",
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
      extensions: [
        basicSetup,
        json(),
        syntaxHighlighting(codeHighlight),
        EditorState.readOnly.of(true),
        EditorView.contentAttributes.of({ "aria-label": `run_voblint ${part} as JSON` }),
      ],
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
    parts.push(
      callPart(" kind rule ctx p", "arg"),
      callPart(" \u27f9 ", "arrow"),
      callPart("?", "arg"),
    );
    rawResultCall.replaceChildren(...parts);
    rawResultCall.title = rawResultCall.textContent;
    return;
  }

  parts.push(
    callPart(
      ` ${constructorTerm(input.kind)} ${constructorTerm(input.rule)} ${constructorTerm(input.ctx)} `,
      "arg",
    ),
    callPart("p", "program"),
    callPart(" \u27f9 ", "arrow"),
  );

  const output = raw.output;

  if (typeof output === "string") {
    parts.push(callPart(output, "ctor"));
  } else {
    const [tag, record] = Object.entries(output ?? {})[0] ?? ["?", {}];
    const fields = Object.entries(record ?? {}).map(
      ([name, value]) =>
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
  const error = new Error(message.message ?? "Browser analysis failed.");

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
  button.textContent = Number.isInteger(column)
    ? `Go to line ${line}, column ${column}`
    : `Go to line ${line}`;
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
  icon.className =
    kind === "error" ? "fa-solid fa-circle-exclamation" : "fa-solid fa-triangle-exclamation";
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

  return Number.isInteger(result.line)
    ? "The program could not be parsed"
    : "The program could not be analyzed";
}

function showDiagnosticsSummary(result) {
  const diagnostics = Array.isArray(result.diagnostics) ? result.diagnostics : [];

  if (diagnostics.length === 0) {
    return false;
  }

  const errors = diagnostics.filter((d) => d.severity === "error").length;
  const count = (n, word) => `${n} ${word}${n === 1 ? "" : "s"}`;
  const parts = [
    errors && count(errors, "error"),
    diagnostics.length - errors && count(diagnostics.length - errors, "warning"),
  ]
    .filter(Boolean)
    .join(" and ");

  showProblem({
    kind: errors > 0 ? "error" : "warning",
    title: `${parts[0].toUpperCase()}${parts.slice(1)} in arithmetic`,
    note: "An error means a divisor is zero in every live context; a warning means it may be zero.",
    items: diagnostics.map((d) => ({
      kind: d.severity === "error" ? "error" : "warning",
      message: d.message ?? "",
      line: d.line,
    })),
  });

  return true;
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
    seedByEntry: new Map(
      (result.seeds ?? []).filter((seed) => seed.entry).map((seed) => [seed.entry, seed]),
    ),
    statements,
    statementByPoint: new Map(statements.map((s) => [s.point, s])),
    stale: false,
  };
}

/* The compiler's return slot: assigned by `return e`, read back by the caller. */
const RETURN_SLOT = "#ret";

function slotValue(node, name) {
  if (name === RETURN_SLOT) {
    return node.ret ?? undefined;
  }

  return (node.bindings.find(([x]) => x === name) ?? node.globals.find(([x]) => x === name))?.[1];
}

/*
 * The value a node's own steps give a name, one entry per step that writes it: the
 * step's published state, or null where the step has no successor. Undefined when no
 * step with a published state writes the name -- a call's result is not one.
 */
function valueAfterSteps(node, name) {
  const values = node.next
    .filter((step) => step.writes === name && "state" in step)
    .map((step) => (step.state ? (step.state.find(([x]) => x === name)?.[1] ?? null) : null));

  return values.length > 0 ? values : undefined;
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

  const parts = [...groups].map(([value, keys]) =>
    keys.length ? `${keys.join(",")} ${value}` : value,
  );

  return `${label}${parts.join(" | ")}`;
}

/*
 * A header shows each parameter as the procedure is entered, and a call shows
 * the parameters of the callee context it enters, prefixed with an arrow. A
 * `return e` shows the value it returns, and a call whose result is discarded
 * shows what its callee returned, both after a return arrow. An assignment shows
 * the value its own step produces, which run_voblint publishes beside the state it
 * starts from -- not the target point's state, which is a join wherever other
 * steps flow in too. A call's result is its continuation's state, the call's
 * combine; that and a callee entry other calls also enter are marked as joins.
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
          const value = slotValue(node, name);

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
          const value = slotValue(entry, name);

          if (value !== undefined) {
            sample(`\u2192 ${name}: `, node.context_key, value, enter.join);
          }
        }

        const exit = enter.exit ? model.nodes.get(enter.exit) : null;

        if (!assignsResult && callee?.returns_value && exit && isLive(exit) && exit.ret) {
          sample("\u21a9 ", node.context_key, exit.ret, enter.join);
        }
      }

      for (const step of node.next.filter((step) => step.writes)) {
        if ("state" in step) {
          const value = step.state?.find(([x]) => x === step.writes)?.[1];

          if (value !== undefined) {
            sample(writeLabel(step.writes), node.context_key, value, false);
          }

          continue;
        }

        const after = model.nodes.get(step.id);
        const value = after && isLive(after) ? slotValue(after, step.writes) : undefined;

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
    return [
      {
        line: result.line,
        column: result.column,
        kind: "error",
        label: result.message ? result.message.toUpperCase() : "ERROR",
        detail: result.message ?? "",
      },
    ];
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

    const labels = [...new Set(group.map((a) => `${ANNOTATION_ICON[a.kind]} ${a.label}`))].join(
      "  ",
    );
    const detail = group
      .map((a) => a.detail)
      .filter(Boolean)
      .join("\n");

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
        Decoration.widget({ widget: new ValueHint(hint.text, hint.merge), side: 1 }).range(
          hint.pos,
        ),
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
      return {
        view,
        showHints,
        decorations: resultDecorations(transaction.state.doc, view, showHints),
      };
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
        selected: usable ? (inspection?.statement ?? null) : null,
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

function showAnalysisView(result) {
  const doc = editor.state.doc;

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
  const assigned = rows.some(({ after }) => after);

  where.textContent = statement.formals
    ? `on entry \u00b7 line ${statement.line}`
    : assigned
      ? `before \u2192 after line ${statement.line} \u00b7 ${statement.point}`
      : `before line ${statement.line} \u00b7 ${statement.point}`;
  head.append(where);

  const table = document.createElement("table");

  for (const { node, value, after } of rows) {
    const row = table.insertRow();
    const key = row.insertCell();

    key.textContent = node.context_key;
    key.className = "cm-variable-tooltip-key";
    row.insertCell().textContent = node.context;

    const cell = row.insertCell();

    cell.textContent = value ?? "unreachable";
    cell.className = value === null ? "cm-variable-tooltip-dead" : "cm-variable-tooltip-value";

    if (after) {
      const next = row.insertCell();

      next.textContent = `\u2192 ${after.map((v) => v ?? "no successor").join(" | ")}`;
      next.className = "cm-variable-tooltip-value";
    }
  }

  tooltip.append(head, table);

  return tooltip;
}

/*
 * A variable's value as the statement under the pointer is reached, in every
 * context that statement has, and, where the statement assigns it, the value its
 * step produces. Names the statement's contexts do not bind -- a procedure name, a
 * keyword -- get no tooltip.
 */
const variableHover = hoverTooltip(
  (view, pos) => {
    if (!analysisModel || analysisModel.stale) {
      return null;
    }

    const word = view.state.wordAt(pos);
    const name = word ? view.state.sliceDoc(word.from, word.to) : "";

    if (
      !/^[A-Za-z_][A-Za-z0-9_]*$/.test(name) ||
      VIMP_KEYWORDS.has(name) ||
      name.startsWith("__voblint_")
    ) {
      return null;
    }

    const statement = statementAt(analysisModel, view.state.doc, pos);

    const rows = (statement?.nodes ?? [])
      .map((node) => ({
        node,
        value: isLive(node) ? slotValue(node, name) : null,
        after: isLive(node) && !statement.formals ? valueAfterSteps(node, name) : undefined,
      }))
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

/* A message has no states to show, so it reads on the header line beside the title. */
function inspectorMessage(text) {
  const message = document.createElement("span");

  message.className = "inspector-message";
  message.textContent = text;
  inspectorLocation.append(message);
  inspectorBody.replaceChildren();
}

function statementExcerpt(statement) {
  const doc = editor.state.doc;

  return doc
    .sliceString(statement.from, Math.min(statement.to, doc.lineAt(statement.from).to))
    .trim();
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

/* The drawing, while one is shown; a message or an empty panel has none. */
let cy = null;

function graphElementsById(ids) {
  return cy.collection(ids.map((id) => cy.getElementById(id)).filter((ele) => ele.nonempty()));
}

function applyGraphSelection() {
  if (!cy) {
    return;
  }

  cy.batch(() => {
    cy.nodes(".graph-node-selected").removeClass("graph-node-selected graph-node-focused");

    if (!analysisModel || analysisModel.stale || !inspection) {
      return;
    }

    for (const node of inspection.nodes) {
      const element = cy.getElementById(node.id);

      element.addClass("graph-node-selected");

      if (node.id === focusedNodeId) {
        element.addClass("graph-node-focused");
      }
    }
  });
}

/* Pans only the graph's own view; the page stays where the reader put it. */
function revealGraphNodes(ids) {
  if (!cy || graphPanel.hidden) {
    return;
  }

  const elements = graphElementsById(ids);

  if (elements.empty()) {
    return;
  }

  const box = elements.renderedBoundingBox();
  const visible = box.x1 >= 0 && box.y1 >= 0 && box.x2 <= cy.width() && box.y2 <= cy.height();

  if (!visible) {
    graphFitted = false;
    pendingZoom = null;
    cy.stop(true, true);
    cy.animate({ center: { eles: elements } }, GRAPH_ANIMATION);
  }

  elements.flashClass("graph-node-flash", 900);
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

/* -------------------------------------------------------------------------- */
/* Analysis graph                                                             */
/* -------------------------------------------------------------------------- */

let graphLibrariesPromise = null;
let analysisRunGeneration = 0;

/* A view that still shows the whole fitted graph refits when the panel resizes. */
let graphFitted = true;

/* The zoom an animation is heading for, so steps pressed faster than it runs compound. */
let pendingZoom = null;

const MIN_GRAPH_SCALE = 0.1;
const MAX_GRAPH_SCALE = 4;
const GRAPH_ZOOM_STEP = 1.2;
const GRAPH_PADDING = 24;
const GRAPH_ANIMATION = { duration: 260, easing: "ease-out-cubic" };

const NODE_FONT_SIZE = 12;
const NODE_LINE_HEIGHT = 1.35;
const NODE_PADDING_X = 12;
const NODE_PADDING_Y = 7;
const EDGE_FONT_SIZE = 10;
const CLUSTER_PADDING = 16;
/* Room above a context box for its label, which Cytoscape draws outside the box. */
const CLUSTER_LABEL_SPACE = 22;

function clamp(value, lo, hi) {
  return Math.min(hi, Math.max(lo, value));
}

function updateZoomResetLabel() {
  graphZoomReset.textContent = `${Math.round((cy?.zoom() ?? 1) * 100)}%`;
}

function destroyGraph() {
  stopEdgeFlow();
  cy?.destroy();
  cy = null;
}

function clearGraph() {
  destroyGraph();
  graphFitted = true;
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

  destroyGraph();
  graph.replaceChildren(row);
  graphPanel.hidden = false;
}

function getGraphLibraries() {
  if (!graphLibrariesPromise) {
    graphLibrariesPromise = Promise.all([
      import("https://esm.sh/cytoscape@3.34.3"),
      import("https://esm.sh/elkjs@0.12.0/lib/elk.bundled.js"),
    ])
      .then(([cytoscape, ELK]) => ({ cytoscape: cytoscape.default, elk: new ELK.default() }))
      .catch((error) => {
        graphLibrariesPromise = null;
        throw error;
      });
  }

  return graphLibrariesPromise;
}

/* Cytoscape paints on a canvas, which cannot read CSS custom properties itself. */
function cssToken(name) {
  return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
}

const measureContext = document.createElement("canvas").getContext("2d");

function textWidth(text, font) {
  measureContext.font = font;

  return measureContext.measureText(text).width;
}

function edgeLabel(edge) {
  switch (edge.kind) {
    case "enter":
      return `call ${edge.text}`;
    case "combine":
      return edge.text ? `resume / ${edge.text}` : "resume";
    case "call_to_return":
      return "continuation";
    default:
      return edge.text;
  }
}

/*
 * Where a right-angle path turns, as a share of the gap it crosses. Cytoscape turns
 * every such path halfway by default, so two edges across the same gap would run on
 * one line; a different share per edge keeps them apart while nodes move.
 */
function taxiTurn(index) {
  return `${25 + ((index * 37) % 51)}%`;
}

/*
 * A zero divisor is marked by an icon beside the point, definite before possible, and
 * its message left to the tooltip: an expression-length line would widen the node
 * and, through it, the whole column of the layout.
 */
const DIVISION_ICON = { definite: "\u26d4", possible: "\u26a0\ufe0f" };

function nodeLabelLines(node) {
  const divisions = node.divisions ?? [];
  const messages = new Set(divisions.map((division) => division.message));
  const icons = ["definite", "possible"]
    .filter((verdict) => divisions.some((division) => division.verdict === verdict))
    .map((verdict) => DIVISION_ICON[verdict]);

  return [
    [node.point, ...icons].join(" "),
    ...node.findings.filter((finding) => !messages.has(finding)),
  ];
}

/* A node's label names its point and findings; the full state is the hover tooltip. */
function graphElements(result) {
  const mono = cssToken("--mono");
  const nodeFont = `${NODE_FONT_SIZE}px ${mono}`;
  const edgeFont = `${EDGE_FONT_SIZE}px ${mono}`;
  const nodesById = new Map((result.nodes ?? []).map((node) => [node.id, node]));
  const parentOf = new Map();
  const elements = [];

  for (const cluster of result.graph.clusters) {
    elements.push({
      group: "nodes",
      data: { id: cluster.id, label: cluster.label },
      classes: "context",
    });

    for (const id of cluster.members) {
      parentOf.set(id, cluster.id);
    }
  }

  for (const node of nodesById.values()) {
    const lines = nodeLabelLines(node);
    const width = Math.max(...lines.map((line) => textWidth(line, nodeFont))) + 2 * NODE_PADDING_X;
    const height = lines.length * NODE_FONT_SIZE * NODE_LINE_HEIGHT + 2 * NODE_PADDING_Y;
    const status = node.status ?? (node.kind === "point" ? "plain" : "boundary");

    elements.push({
      group: "nodes",
      data: {
        id: node.id,
        parent: parentOf.get(node.id),
        label: lines.join("\n"),
        width: Math.ceil(width),
        height: Math.ceil(height),
      },
      classes: `point ${status}`,
    });
  }

  result.graph.edges.forEach((edge, index) => {
    if (!nodesById.has(edge.source) || !nodesById.has(edge.target)) {
      return;
    }

    const label = edgeLabel(edge);

    elements.push({
      group: "edges",
      data: {
        id: `edge-${index}`,
        source: edge.source,
        target: edge.target,
        label,
        labelWidth: textWidth(label, edgeFont),
        /* How far along the edge a label beside its end node is centered. */
        labelOffset: textWidth(label, edgeFont) / 2 + 10,
        turn: taxiTurn(index),
      },
      classes: edge.kind,
    });
  });

  return elements;
}

/*
 * Two passes, so a context box can sit beside the code that calls it. Each box is laid
 * out top to bottom on its own, from its intra and continuation edges. The boxes are
 * then placed left to right, callers before callees, with each call edge pinned to
 * the height of its call site and callee entry, which pulls a callee level with the
 * call that enters it. Resume edges are routed in the second pass as well, so no two
 * edges between boxes share a line.
 */
const INNER_LAYOUT = {
  "elk.algorithm": "layered",
  "elk.direction": "DOWN",
  "elk.edgeRouting": "ORTHOGONAL",
  "elk.layered.considerModelOrder.strategy": "NODES_AND_EDGES",
  "elk.layered.nodePlacement.strategy": "NETWORK_SIMPLEX",
  "elk.layered.spacing.nodeNodeBetweenLayers": "24",
  "elk.spacing.nodeNode": "28",
  "elk.spacing.edgeNode": "16",
  "elk.spacing.edgeEdge": "10",
  "elk.spacing.edgeLabel": "2",
  "elk.edgeLabels.placement": "CENTER",
  /* One port per node side: edges then leave a node from its center, not spread across it. */
  "elk.layered.mergeEdges": "true",
  "elk.padding": `[top=${CLUSTER_PADDING + CLUSTER_LABEL_SPACE},left=${CLUSTER_PADDING},bottom=${CLUSTER_PADDING},right=${CLUSTER_PADDING}]`,
};

const OUTER_LAYOUT = {
  "elk.algorithm": "layered",
  "elk.direction": "RIGHT",
  "elk.edgeRouting": "ORTHOGONAL",
  "elk.layered.considerModelOrder.strategy": "NODES_AND_EDGES",
  "elk.layered.nodePlacement.strategy": "NETWORK_SIMPLEX",
  "elk.layered.cycleBreaking.strategy": "MODEL_ORDER",
  "elk.layered.spacing.nodeNodeBetweenLayers": "60",
  "elk.spacing.nodeNode": "30",
  "elk.spacing.edgeEdge": "12",
  "elk.spacing.componentComponent": "60",
};

function routePoints(section, dx = 0, dy = 0) {
  return [section.startPoint, ...(section.bendPoints ?? []), section.endPoint].map((point) => ({
    x: point.x + dx,
    y: point.y + dy,
  }));
}

/*
 * The edges that go round a loop, so the layout lets them bend and keeps the rest of
 * the flow on a straight line. A back edge is one a depth-first walk from the entry
 * finds returning to a point still on its path; the loop it closes is its target, the
 * loop head, and every point that reaches its source without passing the head. The
 * edges within that set, back edge included, go round the loop; the edge leaving it
 * does not, which is what keeps a loop's exit level with the code before it.
 */
function loopEdges(nodes, edges) {
  const out = new Map(nodes.map(({ data }) => [data.id, []]));
  const into = new Map(nodes.map(({ data }) => [data.id, []]));

  for (const edge of edges) {
    out.get(edge.source)?.push(edge);
    into.get(edge.target)?.push(edge);
  }

  const state = new Map();
  const back = new Set();
  const roots = [...out.keys()].sort((a, b) => into.get(a).length - into.get(b).length);

  for (const root of roots) {
    if (state.has(root)) {
      continue;
    }

    state.set(root, "open");

    for (const stack = [{ id: root, next: 0 }]; stack.length > 0; ) {
      const frame = stack.at(-1);
      const edge = out.get(frame.id)[frame.next++];

      if (!edge) {
        state.set(frame.id, "done");
        stack.pop();
      } else if (state.get(edge.target) === "open") {
        back.add(edge.id);
      } else if (!state.has(edge.target)) {
        state.set(edge.target, "open");
        stack.push({ id: edge.target, next: 0 });
      }
    }
  }

  const looping = new Set();

  for (const edge of edges.filter(({ id }) => back.has(id))) {
    const body = new Set([edge.target, edge.source]);

    for (const queue = [edge.source]; queue.length > 0; ) {
      for (const { source } of into.get(queue.shift())) {
        if (!body.has(source)) {
          body.add(source);
          queue.push(source);
        }
      }
    }

    for (const inner of edges) {
      if (body.has(inner.source) && body.has(inner.target)) {
        looping.add(inner.id);
      }
    }
  }

  return { back, looping };
}

/*
 * Boxes in breadth-first call order from the first. The outer pass breaks cycles by
 * that order, so a resume edge, which runs from a callee back to its caller, is the
 * one reversed and a call keeps pointing right.
 */
function callOrder(inner, crossing, parentOf) {
  const callees = new Map([...inner.keys()].map((id) => [id, []]));

  for (const edge of crossing) {
    if (edge.kind === "enter") {
      callees.get(parentOf.get(edge.source)).push(parentOf.get(edge.target));
    }
  }

  const seen = new Set();
  const order = [];

  for (const root of inner.keys()) {
    if (seen.has(root)) {
      continue;
    }

    seen.add(root);

    for (const queue = [root]; queue.length > 0; ) {
      const id = queue.shift();

      order.push(inner.get(id));

      for (const callee of callees.get(id)) {
        if (!seen.has(callee)) {
          seen.add(callee);
          queue.push(callee);
        }
      }
    }
  }

  return order;
}

/*
 * Ports on one side at one height -- two calls entering the same callee -- would
 * share a channel all the way in; fanning them out keeps every edge its own line.
 */
const PORT_SPREAD = 8;

function spreadPorts(ports, width) {
  const groups = new Map();

  for (const port of ports) {
    const key = `${port.side}:${port.y}`;

    groups.set(key, [...(groups.get(key) ?? []), port]);
  }

  return [...groups.values()].flatMap((group) =>
    group.map((port, index) => ({
      id: port.id,
      x: port.side === "EAST" ? width : 0,
      y: port.y + (index - (group.length - 1) / 2) * PORT_SPREAD,
      width: 0,
      height: 0,
      layoutOptions: { "elk.port.side": port.side },
    })),
  );
}

/*
 * Absolute node centers, and each laid-out edge's bends as absolute points. A route
 * inside a box starts and ends on its nodes' borders, which Cytoscape finds itself;
 * a route between boxes starts and ends at their sides, level with its nodes, so its
 * end points are bends too.
 */
async function layoutGraph(elk, elements) {
  const clusters = new Map();
  const parentOf = new Map();
  const edges = [];

  for (const { group, classes, data } of elements) {
    if (classes === "context") {
      clusters.set(data.id, { id: data.id, layoutOptions: INNER_LAYOUT, children: [], edges: [] });
    } else if (group === "nodes") {
      parentOf.set(data.id, data.parent);
      clusters
        .get(data.parent)
        ?.children.push({ id: data.id, width: data.width, height: data.height });
    } else {
      edges.push({ kind: classes, ...data });
    }
  }

  const local = edges.filter(
    (edge) =>
      (edge.kind === "intra" || edge.kind === "call_to_return") &&
      parentOf.get(edge.source) === parentOf.get(edge.target),
  );
  const { back, looping } = loopEdges(
    elements.filter(({ group, classes }) => group === "nodes" && classes !== "context"),
    local,
  );

  for (const edge of local) {
    clusters.get(parentOf.get(edge.source))?.edges.push({
      id: edge.id,
      sources: [edge.source],
      targets: [edge.target],
      labels: edge.label
        ? [{ text: edge.label, width: edge.labelWidth + 8, height: EDGE_FONT_SIZE * 1.6 }]
        : [],
      layoutOptions: {
        "elk.layered.priority.straightness": looping.has(edge.id) ? "0" : "10",
        "elk.layered.priority.direction": back.has(edge.id) ? "0" : "10",
      },
    });
  }

  const inner = new Map();

  for (const [id, cluster] of clusters) {
    inner.set(id, await elk.layout(cluster));
  }

  const innerCenter = (id) => {
    const node = inner.get(parentOf.get(id)).children.find((child) => child.id === id);

    return { x: node.x + node.width / 2, y: node.y + node.height / 2 };
  };

  /* A call leaves its caller's right side and enters the callee's left; a resume runs back. */
  const crossing = edges.filter(
    (edge) =>
      (edge.kind === "enter" || edge.kind === "combine") &&
      parentOf.get(edge.source) !== parentOf.get(edge.target),
  );
  const ports = new Map([...inner.keys()].map((id) => [id, []]));

  for (const edge of crossing) {
    const forward = edge.kind === "enter";

    ports.get(parentOf.get(edge.source)).push({
      id: `${edge.id}-out`,
      side: forward ? "EAST" : "WEST",
      y: innerCenter(edge.source).y,
    });
    ports.get(parentOf.get(edge.target)).push({
      id: `${edge.id}-in`,
      side: forward ? "WEST" : "EAST",
      y: innerCenter(edge.target).y,
    });
  }

  const outer = await elk.layout({
    id: "root",
    layoutOptions: OUTER_LAYOUT,
    children: callOrder(inner, crossing, parentOf).map((box) => ({
      id: box.id,
      width: box.width,
      height: box.height,
      ports: spreadPorts(ports.get(box.id), box.width),
      layoutOptions: { "elk.portConstraints": "FIXED_POS" },
    })),
    edges: crossing.map((edge) => ({
      id: edge.id,
      sources: [`${edge.id}-out`],
      targets: [`${edge.id}-in`],
    })),
  });

  const centers = new Map();
  const routes = new Map();
  const labels = new Map();

  for (const box of outer.children) {
    const layout = inner.get(box.id);

    for (const node of layout.children) {
      centers.set(node.id, {
        x: box.x + node.x + node.width / 2,
        y: box.y + node.y + node.height / 2,
      });
    }

    for (const edge of layout.edges) {
      if (edge.sections?.[0]) {
        routes.set(edge.id, routePoints(edge.sections[0], box.x, box.y).slice(1, -1));
      }

      for (const label of edge.labels ?? []) {
        labels.set(edge.id, {
          x: box.x + label.x + label.width / 2,
          y: box.y + label.y + label.height / 2,
        });
      }
    }
  }

  for (const edge of outer.edges) {
    if (edge.sections?.[0]) {
      routes.set(edge.id, routePoints(edge.sections[0]));
    }
  }

  return { centers, routes, labels };
}

/*
 * Cytoscape draws a polyline as segment points relative to the line between its
 * endpoints' centers: a weight along it and a signed distance across it. Stated that
 * way, a route stays attached when both ends move together, as when a context box is
 * dragged with the edges inside it.
 */
function segmentStyle(points, source, target) {
  const dx = target.x - source.x;
  const dy = target.y - source.y;
  const lengthSquared = dx * dx + dy * dy;

  if (points.length === 0 || lengthSquared < 1) {
    return null;
  }

  const length = Math.sqrt(lengthSquared);
  const weights = [];
  const distances = [];

  for (const point of points) {
    const px = point.x - source.x;
    const py = point.y - source.y;

    weights.push((px * dx + py * dy) / lengthSquared);
    distances.push((dx * py - dy * px) / length);
  }

  return { weights, distances };
}

/*
 * Cytoscape centers an edge label on the edge's midpoint, where a loop's forward and
 * back edges put theirs on top of each other. The inner pass reserves room for each
 * label and places it, so the label keeps that place as an offset from the midpoint.
 */
function applyGraphLayout({ centers, routes, labels }) {
  cy.batch(() => {
    cy.nodes(".point").positions((node) => centers.get(node.id()) ?? { x: 0, y: 0 });

    for (const [id, points] of routes) {
      const edge = cy.getElementById(id);
      const style = segmentStyle(
        points,
        centers.get(edge.data("source")),
        centers.get(edge.data("target")),
      );

      if (style) {
        edge.addClass("routed").data(style);
      }
    }
  });

  cy.batch(() => {
    for (const [id, place] of labels) {
      const edge = cy.getElementById(id);
      const midpoint = edge.midpoint();

      edge
        .addClass("placed-label")
        .data({ labelX: place.x - midpoint.x, labelY: place.y - midpoint.y });
    }
  });
}

/*
 * A call or resume edge crosses between boxes through channels it shares with others,
 * so its label sits on its first or last stretch, beside the node it concerns, instead
 * of midway where the channels meet: a call's above its line, a resume's below, since
 * one node can start a call and receive a resume at the same height.
 */
function graphStyle() {
  const mono = cssToken("--mono");
  const text = cssToken("--text");
  const muted = cssToken("--text-muted");

  const status = (color, fill) => ({
    "border-color": cssToken(color),
    "border-width": 2,
    "background-color": cssToken(fill),
  });

  return [
    {
      selector: "node.context",
      style: {
        shape: "round-rectangle",
        "corner-radius": 10,
        padding: CLUSTER_PADDING,
        "background-color": cssToken("--surface"),
        "background-opacity": 0.72,
        "border-color": cssToken("--border-strong"),
        "border-width": 1,
        label: "data(label)",
        color: muted,
        "font-family": mono,
        "font-size": 11,
        "font-weight": 700,
        "text-valign": "top",
        "text-halign": "center",
        "text-margin-y": -6,
      },
    },
    {
      selector: "node.context:active",
      style: { "overlay-opacity": 0, "border-color": cssToken("--primary"), "border-width": 2 },
    },
    {
      selector: "node.point",
      style: {
        shape: "round-rectangle",
        "corner-radius": 6,
        width: "data(width)",
        height: "data(height)",
        "background-color": cssToken("--surface"),
        "border-color": cssToken("--border-strong"),
        "border-width": 1,
        label: "data(label)",
        color: text,
        "font-family": mono,
        "font-size": NODE_FONT_SIZE,
        "line-height": NODE_LINE_HEIGHT,
        "text-wrap": "wrap",
        "text-max-width": 2000,
        "text-valign": "center",
        "text-halign": "center",
        "overlay-opacity": 0,
        "underlay-color": cssToken("--accent"),
        "underlay-padding": 8,
        "underlay-opacity": 0,
        "underlay-shape": "round-rectangle",
        "transition-property": "underlay-opacity",
        "transition-duration": 300,
      },
    },
    {
      selector: "node.boundary",
      style: {
        "border-style": "double",
        "border-width": 4,
        "border-color": cssToken("--primary"),
        "background-color": cssToken("--primary-soft"),
      },
    },
    { selector: "node.proved", style: status("--success", "--success-soft") },
    { selector: "node.refuted", style: status("--danger", "--danger-soft") },
    {
      selector: "node.unknown",
      style: { ...status("--caution", "--surface"), "background-color": "#fbf1dc" },
    },
    {
      selector: "node.unreachable",
      style: {
        "border-style": "dashed",
        "border-color": cssToken("--text-faint"),
        "background-color": cssToken("--surface-muted"),
        color: muted,
      },
    },
    {
      selector: "node.graph-node-selected",
      style: { "outline-color": cssToken("--primary"), "outline-width": 3, "outline-offset": 2 },
    },
    {
      selector: "node.graph-node-focused",
      style: { "outline-color": cssToken("--accent"), "outline-width": 4, "outline-offset": 2 },
    },
    { selector: "node.graph-node-flash", style: { "underlay-opacity": 0.35 } },
    {
      selector: "edge",
      style: {
        width: 1.4,
        "curve-style": "round-taxi",
        "taxi-direction": "vertical",
        "taxi-turn": "data(turn)",
        "taxi-turn-min-distance": 12,
        "taxi-radius": 6,
        "line-color": "#7c9096",
        "target-arrow-color": "#7c9096",
        "target-arrow-shape": "triangle",
        "arrow-scale": 0.9,
        "line-style": "dashed",
        "line-dash-pattern": [7, 5],
        label: "data(label)",
        color: muted,
        "font-family": mono,
        "font-size": EDGE_FONT_SIZE,
        "text-background-color": cssToken("--surface-muted"),
        "text-background-opacity": 0.9,
        "text-background-padding": 2,
        "text-rotation": "none",
      },
    },
    {
      selector: "edge.placed-label",
      style: { "text-margin-x": "data(labelX)", "text-margin-y": "data(labelY)" },
    },
    {
      selector: "edge.routed",
      style: {
        "curve-style": "round-segments",
        "segment-weights": "data(weights)",
        "segment-distances": "data(distances)",
        "segment-radii": 6,
        "edge-distances": "node-position",
      },
    },
    {
      selector: "edge.enter",
      style: {
        "taxi-direction": "horizontal",
        label: "",
        "source-label": "data(label)",
        "source-text-offset": "data(labelOffset)",
        "source-text-margin-y": -12,
        width: 2.2,
        "line-color": cssToken("--primary"),
        "target-arrow-color": cssToken("--primary"),
        color: cssToken("--primary"),
      },
    },
    {
      selector: "edge.combine",
      style: {
        "taxi-direction": "horizontal",
        label: "",
        "target-label": "data(label)",
        "target-text-offset": "data(labelOffset)",
        "target-text-margin-y": 12,
        width: 1.2,
        "line-color": "#3f7fb4",
        "target-arrow-color": "#3f7fb4",
        "arrow-scale": 0.7,
        color: "#3f7fb4",
      },
    },
    {
      selector: "edge.call_to_return",
      style: { "line-color": "#9aa9ae", "target-arrow-color": "#9aa9ae" },
    },
  ];
}

/*
 * Edges flow toward their target. Every frame restyles every edge and repaints the
 * whole drawing, so a large graph or a reader who asked for less motion keeps still
 * dashes, and nothing moves while the graph is off screen.
 */
const EDGE_FLOW_LIMIT = 400;
let edgeFlowFrame = 0;
let graphInView = false;

new IntersectionObserver((entries) => {
  graphInView = entries.some((entry) => entry.isIntersecting);
}).observe(graph);

function startEdgeFlow() {
  stopEdgeFlow();

  if (
    !cy ||
    cy.edges().length > EDGE_FLOW_LIMIT ||
    matchMedia("(prefers-reduced-motion: reduce)").matches
  ) {
    return;
  }

  let last = 0;

  const step = (time) => {
    edgeFlowFrame = requestAnimationFrame(step);

    if (!graphInView || document.hidden || time - last < 50) {
      return;
    }

    last = time;
    cy.edges().style("line-dash-offset", -((time / 100) % 12));
  };

  edgeFlowFrame = requestAnimationFrame(step);
}

function stopEdgeFlow() {
  cancelAnimationFrame(edgeFlowFrame);
  edgeFlowFrame = 0;
}

/* Zooms about a point given in view coordinates, keeping that point under the pointer. */
function zoomGraphAt(factor, viewX, viewY, { animate = false } = {}) {
  if (!cy) {
    return;
  }

  const zoom = {
    level: clamp((pendingZoom ?? cy.zoom()) * factor, MIN_GRAPH_SCALE, MAX_GRAPH_SCALE),
    renderedPosition: { x: viewX, y: viewY },
  };

  graphFitted = false;
  cy.stop(true, true);

  if (animate) {
    pendingZoom = zoom.level;
    cy.animate({ zoom }, { ...GRAPH_ANIMATION, complete: () => (pendingZoom = null) });
  } else {
    pendingZoom = null;
    cy.zoom(zoom);
  }
}

function viewCenter() {
  return { x: cy.width() / 2, y: cy.height() / 2 };
}

function zoomGraphIn() {
  const { x, y } = viewCenter();
  zoomGraphAt(GRAPH_ZOOM_STEP, x, y, { animate: true });
}

function zoomGraphOut() {
  const { x, y } = viewCenter();
  zoomGraphAt(1 / GRAPH_ZOOM_STEP, x, y, { animate: true });
}

function panGraphBy(dx, dy, { animate = false } = {}) {
  if (!cy) {
    return;
  }

  graphFitted = false;
  pendingZoom = null;
  cy.stop(true, true);

  if (animate) {
    cy.animate({ panBy: { x: dx, y: dy } }, GRAPH_ANIMATION);
  } else {
    cy.panBy({ x: dx, y: dy });
  }
}

/* 100%: natural size, centered on whatever is at the middle of the view now. */
function resetGraphZoom() {
  const { x, y } = viewCenter();
  zoomGraphAt(1 / cy.zoom(), x, y, { animate: true });
}

/*
 * Fit the whole drawing and center it. A graph so tall that fitting it would make
 * its labels unreadable fits the width instead and starts at its top.
 */
/*
 * The whole drawing, not the view: Cytoscape renders every element again at twice
 * the model's size, capped so a large graph stays within what a canvas can hold.
 */
function saveGraphImage() {
  if (!cy) {
    return;
  }

  const image = cy.png({
    output: "blob",
    full: true,
    scale: 2,
    maxWidth: 8000,
    maxHeight: 8000,
    bg: cssToken("--surface-muted"),
  });
  const settings = [analysisSelect.value, globalsSelect.value, contextSelect.value];

  if (contextSelect.value === "call-string") {
    settings.push(`k${contextDepthInput.value}`);
  }

  const link = document.createElement("a");

  link.href = URL.createObjectURL(image);
  link.download = `voblint-graph-${settings.join("-")}.png`;
  link.click();
  setTimeout(() => URL.revokeObjectURL(link.href), 0);
}

function fitGraphZoom({ animate = true } = {}) {
  if (!cy || cy.elements().empty()) {
    return;
  }

  const box = cy.elements().boundingBox();
  const width = Math.max(1, cy.width() - 2 * GRAPH_PADDING);
  const height = Math.max(1, cy.height() - 2 * GRAPH_PADDING);
  const byWidth = width / box.w;
  const whole = Math.min(1, byWidth, height / box.h);
  const zoom = whole >= 0.45 ? whole : Math.min(1, byWidth);
  const pan = {
    x: (cy.width() - box.w * zoom) / 2 - box.x1 * zoom,
    y:
      box.h * zoom <= height
        ? (cy.height() - box.h * zoom) / 2 - box.y1 * zoom
        : GRAPH_PADDING - box.y1 * zoom,
  };

  pendingZoom = null;
  cy.stop(true, true);

  if (animate) {
    cy.animate({ zoom, pan }, GRAPH_ANIMATION);
  } else {
    cy.viewport({ zoom, pan });
  }

  graphFitted = true;
}

/* Whether the drawing overflows the view along an axis, so a scroll there should pan it. */
function graphOverflows(axis) {
  const box = cy.elements().renderedBoundingBox();

  return axis === "x" ? box.x1 < 0 || box.x2 > cy.width() : box.y1 < 0 || box.y2 > cy.height();
}

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
  const left =
    event.clientX + margin + width > window.innerWidth
      ? event.clientX - margin - width
      : event.clientX + margin;
  const top =
    event.clientY + margin + height > window.innerHeight
      ? event.clientY - margin - height
      : event.clientY + margin;

  graphTooltip.style.left = `${Math.max(4, left)}px`;
  graphTooltip.style.top = `${Math.max(4, top)}px`;
}

/* A node's tooltip: its point, then its state and findings. */
function showGraphTooltip(node, event) {
  if (graphTooltip.dataset.node !== node.id) {
    const title = document.createElement("strong");
    title.textContent = node.point;

    const lines = [...node.bindings.map(([name, value]) => `${name}=${value}`), ...node.findings];
    const body = document.createElement("pre");
    body.textContent = lines.length > 0 ? lines.join("\n") : "no bindings";

    graphTooltip.replaceChildren(title, body);
    graphTooltip.dataset.node = node.id;
  }

  graphTooltip.hidden = false;
  placeGraphTooltip(event);
}

/*
 * Hovering a node shows its state and marks its statement in the editor; clicking
 * inspects it. Dragging a node or a whole context box moves it. An edge with both
 * ends inside what moved keeps its route; any other drops its laid-out bends for a
 * right-angle path that follows the move.
 */
function attachGraphInteraction() {
  cy.on("mouseover", "node.point", (event) => {
    const node = analysisModel?.nodes.get(event.target.id());

    graph.classList.add("is-over-node");
    hoveredSpan = node ? (analysisModel.statementByPoint.get(node.point) ?? null) : null;
    scheduleHighlights();

    if (node) {
      showGraphTooltip(node, event.originalEvent);
    }
  });

  cy.on("mousemove", "node.point", (event) => {
    if (!graphTooltip.hidden) {
      placeGraphTooltip(event.originalEvent);
    }
  });

  cy.on("mouseout", "node.point", () => {
    graph.classList.remove("is-over-node");
    hoveredSpan = null;
    scheduleHighlights();
    hideGraphTooltip();
  });

  cy.on("mouseover", "node.context", () => graph.classList.add("is-over-context"));
  cy.on("mouseout", "node.context", () => graph.classList.remove("is-over-context"));

  cy.on("tap", "node.point", (event) => inspectGraphNode(event.target.id()));

  cy.on("dbltap", (event) => {
    if (event.target === cy) {
      fitGraphZoom();
    }
  });

  cy.on("grab", "node", () => {
    graphFitted = false;
    hideGraphTooltip();
  });

  cy.on("drag", "node", (event) => {
    const moved = event.target.isParent() ? event.target.descendants() : event.target;

    moved
      .connectedEdges(".routed, .placed-label")
      .filter((edge) => !(moved.contains(edge.source()) && moved.contains(edge.target())))
      .removeClass("routed placed-label");
  });

  cy.on("dragpan pinchzoom scrollzoom", () => {
    graphFitted = false;
    hideGraphTooltip();
  });

  cy.on("zoom", updateZoomResetLabel);
}

async function renderGraph(result, runGeneration) {
  /*
   * The table is rendered synchronously, while the graph libraries may still be
   * loading. Never let a graph from an older run overwrite the result of a newer run.
   */
  if (runGeneration !== analysisRunGeneration) {
    return;
  }

  if (!Array.isArray(result.graph?.clusters) || !Array.isArray(result.graph?.edges)) {
    throw new Error("Internal error: successful analysis returned no control-flow graph.");
  }

  showGraphMessage("Rendering control-flow graph...");

  try {
    const { cytoscape, elk } = await getGraphLibraries();

    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    const elements = graphElements(result);
    const layout = await layoutGraph(elk, elements);

    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    graph.replaceChildren();
    graphPanel.hidden = false;

    cy = cytoscape({
      container: graph,
      elements,
      style: graphStyle(),
      layout: { name: "preset" },
      minZoom: MIN_GRAPH_SCALE,
      maxZoom: MAX_GRAPH_SCALE,
      boxSelectionEnabled: false,
      autounselectify: true,
    });

    applyGraphLayout(layout);
    attachGraphInteraction();
    applyGraphSelection();
    fitGraphZoom({ animate: false });
    updateZoomResetLabel();
    startEdgeFlow();
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

/*
 * Every extra call site kept multiplies the contexts a recursive program can
 * reach; none of the explainer's examples needs more than two.
 */
const MAX_CONTEXT_DEPTH = 16;

function parseContextDepth(text) {
  const trimmed = String(text ?? "").trim();

  if (!/^\d+$/.test(trimmed)) {
    return null;
  }

  const depth = Number(trimmed);

  return depth <= MAX_CONTEXT_DEPTH ? depth : null;
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
    contextDepth = parseContextDepth(contextDepthInput.value);

    if (contextDepth === null) {
      throw new Error(`Call-string depth must be a whole number from 0 to ${MAX_CONTEXT_DEPTH}.`);
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
  const parts = [
    selectedLabel(analysisSelect),
    selectedLabel(globalsSelect),
    selectedLabel(contextSelect),
  ];

  if (configuration.context === "call-string") {
    parts.push(`k=${configuration.contextDepth}`);
  }

  return parts.join(" · ");
}

/* -------------------------------------------------------------------------- */
/* Run analysis                                                               */
/* -------------------------------------------------------------------------- */

/*
 * While a run is active the run button cancels it. Nothing proves every
 * configuration terminates on every program, so a run that never finishes must
 * be stoppable from where it was started.
 */
let running = false;
let slowRunTimer = 0;

const SLOW_RUN_MS = 5000;

function setRunning(active) {
  running = active;
  clearTimeout(slowRunTimer);

  runButton.classList.toggle("running", active);
  runButtonIcon.className = active ? "fa-solid fa-spinner" : "fa-solid fa-play";
  runButtonLabel.textContent = active ? "Cancel" : "Run analysis";
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

  pending.reject(error instanceof Error ? error : new Error(String(error)));
}

function clearResults() {
  clearGraph();
  clearTiming();
  clearAnalysisView();
  clearProblems();
  showRawRunProgram(null);
}

/*
 * Stops the active run, if any. Bumping the generation makes its own handlers
 * stand down, and a worker still solving is terminated: it cannot be interrupted
 * any other way.
 */
function retireActiveRun(reason) {
  analysisRunGeneration++;

  if (pendingAnalysis) {
    discardAnalysisWorker();
    failPendingAnalysis(new Error(reason));
  }

  setRunning(false);
}

/*
 * A result describes the configuration it ran under, so changing any setting
 * retires it: a finished run is cleared, and a pending one is cancelled rather than
 * allowed to land under settings it was not computed with.
 */
function resetForConfigurationChange() {
  const hadResult = running || analysisModel || !graphPanel.hidden || rawRunProgram !== null;

  retireActiveRun("Analysis cancelled: the configuration changed.");
  clearResults();

  if (hadResult) {
    showStatus("Configuration changed \u00b7 run again");
  }
}

function cancelRun() {
  retireActiveRun("Analysis cancelled.");
  clearResults();
  showStatus("Analysis cancelled \u00b7 run again when ready");
}

function createAnalysisWorker() {
  const worker = new Worker("assets/voblint-worker.js");

  worker.addEventListener("message", (event) => {
    const message = event.data;

    if (!pendingAnalysis || !message || message.id !== pendingAnalysis.id) {
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
      new Error(`Analysis worker returned unknown message type: ${String(message.type)}`),
    );
  });

  worker.addEventListener("error", (event) => {
    discardAnalysisWorker(worker);

    const error =
      event.error instanceof Error
        ? event.error
        : new Error(event.message || "Analysis worker failed.");

    failPendingAnalysis(error);
  });

  worker.addEventListener("messageerror", (event) => {
    discardAnalysisWorker(worker);

    console.error("Could not decode the analysis worker response:", event.data);

    failPendingAnalysis(new Error("Could not decode the analysis worker response."));
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

      reject(error instanceof Error ? error : new Error(String(error)));
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
  if (runButton.disabled || running || pendingAnalysis) {
    return;
  }

  const runGeneration = ++analysisRunGeneration;

  clearResults();

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

  slowRunTimer = setTimeout(() => {
    if (runGeneration === analysisRunGeneration && pendingAnalysis) {
      showStatus(
        `Still analyzing after ${SLOW_RUN_MS / 1000} s. Some settings never finish on some ` +
          "programs, such as Join on a growing recursion: press Cancel to stop.",
      );
    }
  }, SLOW_RUN_MS);

  let result = null;

  try {
    const rawResult = await runAnalysisInWorker(configuration, source);

    if (typeof rawResult !== "string") {
      throw new TypeError(`Voblint_run returned ${typeof rawResult}; expected a JSON string.`);
    }

    result = JSON.parse(rawResult);

    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    /* Positions, excerpts and "go to line" all refer to the analysed text. */
    if (editor.state.doc.toString() !== source) {
      showStatus("The program changed during the run \u00b7 run again");
      return;
    }

    renderTiming(result);
    showRawRunProgram(result.raw);
    showAnalysisView(result);

    if (result.status === "ok") {
      /*
       * Every supported successful analysis is required to expose its control-
       * flow graph. Keep the run open until that graph has rendered; a missing
       * graph is an internal contract violation and fails the run rather than
       * being presented as a supported graph-less configuration.
       */
      await renderGraph(result, runGeneration);

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

        showStatus(
          `${configurationLabel(configuration)} · ${failureTitle(result).toLowerCase()}`,
          "error",
        );
        /* The title already says the program is malformed; the banner keeps only the reason. */
        const message = (result.message ?? "").replace(/^program is not well-formed:\s*/i, "");

        showProblem({
          title: failureTitle(result),
          message,
          line: result.line,
          column: result.column,
        });
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
        showStatus(
          `${configurationLabel(configuration)} · complete, but the graph could not be drawn`,
          "error",
        );

        /* The graph panel already names the failure; arithmetic findings take the banner. */
        if (!showDiagnosticsSummary(result)) {
          showProblem({
            kind: "warning",
            title: "The result is ready, but the graph could not be drawn",
            message: error.message,
          });
        }

        console.error(error);

        return;
      }

      clearGraph();

      const message = error instanceof Error ? error.message : String(error);
      showStatus("Browser analysis failed", "error");
      showProblem({ title: "The analyzer stopped", message });

      if (error instanceof Error) {
        console.error(`${error.name}: ${error.message}\n\n${error.stack ?? ""}`);
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

    /* Above basicSetup's own Mod-Enter binding, which inserts a blank line. */
    Prec.highest(
      keymap.of([
        {
          key: "Mod-Enter",
          run: () => {
            run();
            return true;
          },
        },
      ]),
    ),

    EditorView.contentAttributes.of({ "aria-label": "VIMP program editor" }),

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
    }),
  ],

  parent: editorMount,
});

/* -------------------------------------------------------------------------- */
/* Events                                                                     */
/* -------------------------------------------------------------------------- */

runButton.addEventListener("click", () => (running ? cancelRun() : run()));

function syncValueHints() {
  editor.dispatch({ effects: setValueHintsVisible.of(valueHintsToggle.checked) });
}

valueHintsToggle.addEventListener("change", syncValueHints);

contextSelect.addEventListener("change", updateContextControls);

for (const control of [analysisSelect, globalsSelect, contextSelect, contextDepthInput]) {
  control.addEventListener("change", resetForConfigurationChange);
}

globalsSelect.addEventListener("change", updateGlobalsHelp);

graphZoomIn.addEventListener("click", () => cy && zoomGraphIn());

graphZoomOut.addEventListener("click", () => cy && zoomGraphOut());

graphZoomReset.addEventListener("click", () => cy && resetGraphZoom());

graphZoomFit.addEventListener("click", () => fitGraphZoom());

graphSaveImage.addEventListener("click", saveGraphImage);

/*
 * Trackpad: a two-finger scroll pans; a pinch arrives as a wheel event with ctrlKey
 * set (Chrome, Firefox, Edge) or as gesture events (Safari) and zooms at the pointer.
 * A scroll along an axis the drawing already fits is left to the page. These listen
 * in the capture phase, registered before any drawing exists, so they run ahead of
 * Cytoscape's own wheel zoom and replace it.
 */
graph.addEventListener(
  "wheel",
  (event) => {
    if (!cy) {
      return;
    }

    event.stopImmediatePropagation();

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
    hideGraphTooltip();
    panGraphBy(-panX, -panY);
  },
  { capture: true, passive: false },
);

let gestureScale = 1;

graph.addEventListener(
  "gesturestart",
  (event) => {
    if (!cy) {
      return;
    }

    event.preventDefault();
    event.stopImmediatePropagation();
    gestureScale = 1;
  },
  { capture: true },
);

graph.addEventListener(
  "gesturechange",
  (event) => {
    if (!cy) {
      return;
    }

    event.preventDefault();
    event.stopImmediatePropagation();
    const bounds = graph.getBoundingClientRect();
    zoomGraphAt(
      event.scale / gestureScale,
      event.clientX - bounds.left,
      event.clientY - bounds.top,
    );
    gestureScale = event.scale;
  },
  { capture: true },
);

graph.addEventListener("keydown", (event) => {
  const step = 60;
  const actions = {
    "+": zoomGraphIn,
    "=": zoomGraphIn,
    "-": zoomGraphOut,
    0: () => fitGraphZoom(),
    ArrowLeft: () => panGraphBy(step, 0, { animate: true }),
    ArrowRight: () => panGraphBy(-step, 0, { animate: true }),
    ArrowUp: () => panGraphBy(0, step, { animate: true }),
    ArrowDown: () => panGraphBy(0, -step, { animate: true }),
  };

  if (actions[event.key] && cy) {
    event.preventDefault();
    actions[event.key]();
  }
});

new ResizeObserver(() => {
  if (!cy) {
    return;
  }

  cy.resize();

  if (graphFitted) {
    fitGraphZoom({ animate: false });
  }
}).observe(graph);

updateContextControls();
updateGlobalsHelp();
/* A reload can restore the checkbox's last state, which the editor field does not know. */
syncValueHints();
renderRawCall(null);
renderInspector();
updateZoomResetLabel();

runButton.disabled = false;
showStatus("Ready");
window.voblintPlaygroundReady = true;

/* -------------------------------------------------------------------------- */
/* Regression examples                                                        */
/* -------------------------------------------------------------------------- */

const examplesButton = query("#open-examples");
const examplesDialog = query("#examples-dialog");
const examplesSearch = query("#examples-search");
const examplesBody = query("#examples-body");
const examplesClose = query("#examples-close");
const editorFile = query("#editor-file");

/*
 * What voblint assumes for a flag a fixture's header leaves out. A header that
 * omits one must not inherit whatever the previous run selected.
 */
const FIXTURE_DEFAULTS = { context: "none", globals: "warrow" };

let examplesPromise = null;

/* Generated at site build from tests/regression; fetched once, on first open. */
function loadExamples() {
  examplesPromise ??= fetch("assets/regression-examples.json")
    .then((response) => {
      if (!response.ok) {
        throw new Error(`HTTP ${response.status}`);
      }

      return response.json();
    })
    .catch((error) => {
      examplesPromise = null;
      throw error;
    });

  return examplesPromise;
}

function examplesMessage(text) {
  const message = document.createElement("p");

  message.className = "examples-message";
  message.textContent = text;

  return message;
}

function exampleChip(text, kind = "") {
  const chip = document.createElement("span");

  chip.className = kind ? `example-chip ${kind}` : "example-chip";
  chip.textContent = text;

  return chip;
}

/* A showcase card leads with the point it makes; the fixture's own name moves under it. */
function exampleCard(group, fixture, pick = null) {
  const card = document.createElement("button");

  card.type = "button";
  card.className = pick ? "example-card picked" : "example-card";
  card.title = fixture.path;

  const name = document.createElement("strong");

  name.textContent = pick ? pick.title : fixture.name;

  const chips = document.createElement("span");

  chips.className = "example-chips";
  chips.append(exampleChip(fixture.analyses.join(", ")));

  const { context = FIXTURE_DEFAULTS.context, k, globals } = fixture.settings;

  if (context !== "none") {
    chips.append(exampleChip(k === undefined ? context : `${context} k=${k}`));
  }

  if (globals) {
    chips.append(exampleChip(globals));
  }

  if (fixture.category) {
    chips.append(exampleChip(fixture.category, fixture.category));
  }

  card.append(name, chips);

  const description = pick ? pick.note : fixture.summary;

  if (description) {
    const summary = document.createElement("span");

    summary.className = "example-summary";
    summary.textContent = description;
    card.append(summary);
  }

  if (pick) {
    const path = document.createElement("code");

    path.className = "example-path";
    path.textContent = fixture.path;
    card.append(path);
  }

  card.dataset.search = [group.title, fixture.path, fixture.summary, pick?.title, pick?.note]
    .filter(Boolean)
    .join(" ")
    .toLowerCase();
  card.addEventListener("click", () => openProgram(fixtureProgram(fixture)));

  return card;
}

function examplesSection(title, cards, className = "examples-group") {
  const section = document.createElement("section");
  const heading = document.createElement("h3");
  const grid = document.createElement("div");

  section.className = className;
  heading.textContent = title;
  heading.append(exampleChip(String(cards.length)));
  grid.className = "examples-grid";
  grid.append(...cards);
  section.append(heading, grid);

  return section;
}

function renderExamples({ showcase = [], groups }) {
  const fixtures = new Map(
    groups.flatMap((group) => group.fixtures.map((fixture) => [fixture.path, { group, fixture }])),
  );
  const picks = showcase
    .filter((pick) => fixtures.has(pick.path))
    .map((pick) => {
      const { group, fixture } = fixtures.get(pick.path);

      return exampleCard(group, fixture, pick);
    });

  examplesBody.replaceChildren(
    ...(picks.length > 0 ? [examplesSection("Showcase", picks, "examples-group showcase")] : []),
    ...groups.map((group) =>
      examplesSection(
        group.title,
        group.fixtures.map((fixture) => exampleCard(group, fixture)),
      ),
    ),
    Object.assign(examplesMessage("No example matches the filter."), {
      hidden: true,
      id: "examples-empty",
    }),
  );
}

/* Every word of the filter must occur in a card's folder, path or description. */
function filterExamples() {
  const words = examplesSearch.value.toLowerCase().split(/\s+/).filter(Boolean);
  let shown = 0;

  for (const section of examplesBody.querySelectorAll(".examples-group")) {
    let sectionShown = 0;

    for (const card of section.querySelectorAll(".example-card")) {
      card.hidden = !words.every((word) => card.dataset.search.includes(word));
      sectionShown += card.hidden ? 0 : 1;
    }

    section.hidden = sectionShown === 0;
    shown += sectionShown;
  }

  const empty = examplesBody.querySelector("#examples-empty");

  if (empty) {
    empty.hidden = shown > 0;
  }
}

async function openExamples() {
  examplesDialog.showModal();
  examplesSearch.focus();

  if (examplesBody.dataset.loaded) {
    return;
  }

  examplesBody.replaceChildren(examplesMessage("Loading the regression suite..."));

  try {
    renderExamples(await loadExamples());
    examplesBody.dataset.loaded = "true";
    filterExamples();
  } catch (error) {
    const detail = error instanceof Error ? error.message : String(error);

    examplesBody.replaceChildren(examplesMessage(`The examples could not be loaded: ${detail}.`));
  }
}

/* Loads a fixture as its regression runs it: its source, then its header's settings. */
function fixtureProgram(fixture) {
  return {
    source: fixture.source,
    fileName: fixture.path.split("/").at(-1),
    settings: { ...FIXTURE_DEFAULTS, ...fixture.settings },
  };
}

/* Opens a program and runs it under the settings it carries; absent settings stay. */
function openProgram({ source, fileName, settings = {} }) {
  retireActiveRun("Analysis cancelled: another program was opened.");
  examplesDialog.close();

  editor.dispatch({
    changes: { from: 0, to: editor.state.doc.length, insert: source },
    selection: { anchor: 0 },
  });
  editor.scrollDOM.scrollTo({ top: 0 });
  editorFile.textContent = fileName;

  selectIfOffered(analysisSelect, settings.analysis);
  selectIfOffered(globalsSelect, settings.globals);
  selectIfOffered(contextSelect, settings.context);

  const depth = parseContextDepth(settings.k);

  if (depth !== null) {
    contextDepthInput.value = String(depth);
  }

  updateContextControls();
  updateGlobalsHelp();
  run();
}

examplesButton.addEventListener("click", openExamples);
examplesClose.addEventListener("click", () => examplesDialog.close());
examplesSearch.addEventListener("input", filterExamples);

/* A click on the backdrop lands on the dialog itself, outside its panel. */
examplesDialog.addEventListener("click", (event) => {
  if (event.target === examplesDialog) {
    examplesDialog.close();
  }
});

/* -------------------------------------------------------------------------- */
/* Links from the explainer                                                   */
/* -------------------------------------------------------------------------- */

/*
 * The explainer's "Try it" links open a program and a configuration here:
 * playground.html?example=two-sites&globals=warrow. Every program below is one the
 * explainer shows, so the run reproduces what the page claims.
 */
const LINKED_EXAMPLES = {
  "remainder-sign": `fun main() {
  n = __voblint_nondet_int();
  x = 6 * n + 5;
  a = x % 6;
  __voblint_check(a >= 0);
  if (a < 0) {
    __voblint_check(a == -1);
  } else {
    __voblint_check(a == 5);
  }
}`,
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
  "recursion-bounded": `fun f(x) {
  __voblint_check(x >= 0);
  if (x < 10) {
    f(x + 1);
  }
}

fun main() {
  f(0);
}`,
  "multiples-of-three": `fun main() {
  n = __voblint_nondet_int();
  x = 3 * n;
  if (x > 0) {
    if (x < 3) {
      __voblint_check(x == 1);
    }
  } else {
    if (x > 5) {
      __voblint_check(x == 6);
    }
  }
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
  factorial: `fun f(n) {
  if (n < 2) {
    return 1;
  } else {
    r = f(n - 1);
    return n * r;
  }
}

fun main() {
  a = f(2);
  __voblint_check(a == 2);
}`,
  "int-reduction": `fun main() {
  n = __voblint_nondet_int();
  x = 4 * n + 1;
  if (x >= 0) {
    if (x <= 10) {
      __voblint_check(x >= 1);
      __voblint_check(x <= 9);
    }
  }
}`,
  "counting-loop": `fun main() {
  i = 0;
  while (i < 5) {
    i = i + 1;
  }
  __voblint_check(i == 5);
}`,
  "goblint-1161": `// goblint/analyzer #1161: Goblint's regression test for the fix, in VIMP.
// Before the fix Goblint read c % 2 as the constant 1, so it got both checks backwards.
fun main() {
  top = __voblint_nondet_int();
  c = -5;
  if (top) {
    c = -7;
  }
  __voblint_check(c % 2 == 1);
  __voblint_check(c % 2 == -1);
}`,
  theorems: `fun main() {
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

/* -------------------------------------------------------------------------- */
/* Shareable links                                                            */
/* -------------------------------------------------------------------------- */

/*
 * A link opens a program and a configuration. The Share button always carries the
 * editor's source in the fragment (#code=...), raw-deflated and base64url encoded, so
 * a shared link keeps showing what the sender saw: the fragment never reaches a server,
 * and a named program can change under a link that only names it. Links written by
 * hand or by scripts/playground_link.py may instead name a regression program
 * (?fixture=path) or an explainer example (?example=name), which this page still opens;
 * settings in the query override the ones a named program carries.
 */
const LINK_SETTINGS = ["analysis", "globals", "context", "k"];

const shareButton = query("#share-link");
const shareLabel = query("#share-link-label");

async function packSource(source) {
  const deflated = new Blob([source]).stream().pipeThrough(new CompressionStream("deflate-raw"));
  const bytes = new Uint8Array(await new Response(deflated).arrayBuffer());
  let binary = "";

  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }

  return btoa(binary).replaceAll("+", "-").replaceAll("/", "_").replace(/=+$/, "");
}

async function unpackSource(packed) {
  const binary = atob(packed.replaceAll("-", "+").replaceAll("_", "/"));
  const bytes = Uint8Array.from(binary, (char) => char.charCodeAt(0));
  const inflated = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("deflate-raw"));

  return new Response(inflated).text();
}

async function findFixture(path) {
  const { groups } = await loadExamples();

  return groups.flatMap((group) => group.fixtures).find((fixture) => fixture.path === path);
}

/* The program a link names or carries, or null when it names nothing that exists. */
async function linkedProgram(params, code) {
  if (code !== null) {
    return { source: await unpackSource(code), fileName: "shared.vimp" };
  }

  const fixturePath = params.get("fixture");

  if (fixturePath !== null) {
    const fixture = await findFixture(fixturePath);

    return fixture ? fixtureProgram(fixture) : null;
  }

  const name = params.get("example");

  if (name !== null && Object.hasOwn(LINKED_EXAMPLES, name)) {
    return {
      source: LINKED_EXAMPLES[name],
      fileName: "example.vimp",
    };
  }

  return name === null ? { source: editor.state.doc.toString(), fileName: "example.vimp" } : null;
}

async function applyLinkedConfiguration() {
  const params = new URLSearchParams(location.search);
  const code = new URLSearchParams(location.hash.slice(1)).get("code");

  if (![...params.keys()].length && code === null) {
    return;
  }

  let program;

  try {
    program = await linkedProgram(params, code);
  } catch (error) {
    const detail = error instanceof Error ? error.message : String(error);

    showStatus(`The linked program could not be opened: ${detail}`, "error");
    return;
  }

  if (!program) {
    showStatus("The link names a program this playground does not have.", "error");
    return;
  }

  const overrides = Object.fromEntries(
    LINK_SETTINGS.filter((key) => params.has(key)).map((key) => [key, params.get(key)]),
  );

  openProgram({ ...program, settings: { ...program.settings, ...overrides } });
}

function linkParam(key, value) {
  return `${key}=${encodeURIComponent(value)}`;
}

async function shareLink() {
  const source = editor.state.doc.toString();
  const parameters = [
    linkParam("analysis", analysisSelect.value),
    linkParam("globals", globalsSelect.value),
    linkParam("context", contextSelect.value),
    ...(contextSelect.value === "call-string" ? [linkParam("k", contextDepthInput.value)] : []),
  ];
  const url = new URL(location.href);

  url.search = parameters.join("&");
  url.hash = `code=${await packSource(source)}`;
  history.replaceState(null, "", url);

  let copied = true;

  try {
    await navigator.clipboard.writeText(url.href);
  } catch {
    copied = false;
  }

  shareLabel.textContent = copied ? "Link copied" : "Link in address bar";
  setTimeout(() => {
    shareLabel.textContent = "Share";
  }, 2000);
}

shareButton.addEventListener("click", shareLink);

applyLinkedConfiguration();
