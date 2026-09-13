import { EditorView, basicSetup } from "https://esm.sh/codemirror@6.0.2";

import { HighlightStyle, StreamLanguage, syntaxHighlighting } from "https://esm.sh/@codemirror/language@6.12.4";

import { tags } from "https://esm.sh/@lezer/highlight@1.2.3";

function query(selector) {
  const element = document.querySelector(selector);

  if (!element) {
    throw new Error(`Missing required element: ${selector}`);
  }

  return element;
}

const editorMount = query("#program-editor");

const analysisSelect = query("#analysis-select");
const solverSelect = query("#solver-select");
const contextSelect = query("#context-select");

const contextDepthInput = query("#context-depth");
const contextDepthGroup = query("#context-depth-group");

const solverHelp = query("#solver-help");

const runButton = query("#run-analysis");
const status = query("#analyzer-status");
const results = query("#analysis-results");

const graphPanel = query("#analysis-graph-panel");
const graph = query("#analysis-graph");

const graphZoomOut = query("#graph-zoom-out");
const graphZoomReset = query("#graph-zoom-reset");
const graphZoomIn = query("#graph-zoom-in");
const graphZoomFit = query("#graph-zoom-fit");

/*
 * Precision demo:
 *
 * Interval + Warrowing + Call string k=1
 *   -> UNKNOWN
 *
 * Interval + Warrowing per origin + Call string k=1
 *   -> PROVED
 */
const initialProgram = `fun p(n) {
  __voblint_check(n < 10);
}

fun q(m) {
  p(m);
}

fun main() {
  q(1);
  q(2);
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

const vimpHighlight = HighlightStyle.define([
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
]);

/* -------------------------------------------------------------------------- */
/* Status/results                                                             */
/* -------------------------------------------------------------------------- */

function showStatus(message, kind = "") {
  status.textContent = message;

  status.className = kind ? `status ${kind}` : "status";
}

function clearResults() {
  results.replaceChildren();
}

function renderResult(result) {
  clearResults();

  if (result.status !== "ok") {
    const error = document.createElement("p");
    error.className = "result-error";

    if (Number.isInteger(result.line) && Number.isInteger(result.column)) {
      error.textContent = `${result.line}:${result.column}: ${result.message}`;
    } else {
      error.textContent = result.message ?? "The program could not be analyzed.";
    }

    results.append(error);
    return;
  }

  const checks = Array.isArray(result.checks) ? result.checks : [];

  if (checks.length > 0) {
    const list = document.createElement("div");
    list.className = "result-list";

    for (const check of checks) {
      const verdict = typeof check.verdict === "string" ? check.verdict : "UNKNOWN";

      const row = document.createElement("div");
      row.className = `result-row ${verdict.toLowerCase()}`;

      const verdictElement = document.createElement("strong");

      verdictElement.textContent = verdict;

      const body = document.createElement("div");

      body.className = "result-body";

      const condition = document.createElement("code");

      condition.textContent = check.condition ?? "";

      const state = document.createElement("span");

      const point = check.point ? `${check.point} · ` : "";

      state.textContent = `${point}${check.state ?? ""}`;

      body.append(condition, state);

      row.append(verdictElement, body);

      list.append(row);
    }

    results.append(list);
  }

  const diagnostics = Array.isArray(result.diagnostics) ? result.diagnostics : [];

  if (diagnostics.length > 0) {
    const heading = document.createElement("h3");

    heading.textContent = "Diagnostics";
    results.append(heading);

    for (const diagnostic of diagnostics) {
      const row = document.createElement("p");

      const severity = diagnostic.severity ?? "info";

      row.className = `diagnostic ${severity}`;

      row.textContent = `${severity}: ${diagnostic.message ?? ""}`;

      results.append(row);
    }
  }

  if (checks.length === 0 && diagnostics.length === 0) {
    const empty = document.createElement("p");

    empty.className = "result-empty";

    empty.textContent = "Analysis completed without reported checks or diagnostics.";

    results.append(empty);
  }
}

/* -------------------------------------------------------------------------- */
/* Analysis graph                                                             */
/* -------------------------------------------------------------------------- */

let vizPromise = null;
let analysisRunGeneration = 0;

let graphScale = 1;
let graphBaseWidth = 0;
let graphBaseHeight = 0;

const MIN_GRAPH_SCALE = 0.25;
const MAX_GRAPH_SCALE = 3;
const GRAPH_ZOOM_STEP = 1.15;

function clamp(value, lo, hi) {
  return Math.min(hi, Math.max(lo, value));
}

function currentGraphSvg() {
  return graph.querySelector("svg");
}

function updateZoomResetLabel() {
  graphZoomReset.textContent = `${Math.round(graphScale * 100)}%`;
}

function clearGraph() {
  graphScale = 1;
  graphBaseWidth = 0;
  graphBaseHeight = 0;

  updateZoomResetLabel();

  graph.replaceChildren();
  graphPanel.hidden = true;
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

function rememberNaturalGraphSize(svg) {
  /*
   * Measure the SVG after GraphViz has inserted it into the document.
   * Using rendered CSS pixels avoids unit mismatches between GraphViz's
   * point-based width/height attributes and the SVG viewBox.
   */
  svg.style.width = "";
  svg.style.height = "";
  svg.style.maxWidth = "none";

  const rect = svg.getBoundingClientRect();

  graphBaseWidth = rect.width;
  graphBaseHeight = rect.height;
}

function applyGraphScale() {
  const svg = currentGraphSvg();

  if (!svg || graphBaseWidth <= 0 || graphBaseHeight <= 0) {
    updateZoomResetLabel();
    return;
  }

  /*
   * Change the SVG's actual layout size rather than using transform: scale().
   * This keeps the scroll container's dimensions correct, so zoomed graphs
   * can still be panned with normal scrolling.
   */
  svg.style.width = `${graphBaseWidth * graphScale}px`;

  svg.style.height = `${graphBaseHeight * graphScale}px`;

  updateZoomResetLabel();
}

function setGraphScale(scale) {
  graphScale = clamp(scale, MIN_GRAPH_SCALE, MAX_GRAPH_SCALE);

  applyGraphScale();
}

function zoomGraphIn() {
  setGraphScale(graphScale * GRAPH_ZOOM_STEP);
}

function zoomGraphOut() {
  setGraphScale(graphScale / GRAPH_ZOOM_STEP);
}

function resetGraphZoom() {
  setGraphScale(1);

  graph.scrollTo({
    left: 0,
    top: 0,
  });
}

function graphAvailableWidth() {
  const style = window.getComputedStyle(graph);

  const paddingLeft = Number.parseFloat(style.paddingLeft) || 0;

  const paddingRight = Number.parseFloat(style.paddingRight) || 0;

  return Math.max(1, graph.clientWidth - paddingLeft - paddingRight);
}

function fitGraphZoom() {
  if (graphBaseWidth <= 0) {
    return;
  }

  graphScale = Math.min(1, graphAvailableWidth() / graphBaseWidth);

  applyGraphScale();

  graph.scrollTo({
    left: 0,
    top: 0,
  });
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

    graph.replaceChildren(svg);
    graphPanel.hidden = false;

    graphScale = 1;
    rememberNaturalGraphSize(svg);
    fitGraphZoom();
  } catch (error) {
    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    showGraphMessage(error instanceof Error ? `Graph rendering failed: ${error.message}` : `Graph rendering failed: ${String(error)}`, "error");
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

function updateSolverHelp() {
  const descriptions = {
    default: "Use Voblint's production solver for this domain and context.",

    join: "Always join updates. Explicit solver override.",

    "per-origin": "Keep contributions separate by origin before combining them.",

    warrow: "Use widening followed by narrowing.",

    "warrow-per-origin": "Apply widening and narrowing separately to per-origin contributions.",
  };

  solverHelp.textContent = descriptions[solverSelect.value] ?? "";
}

function readConfiguration() {
  const analysis = analysisSelect.value;

  const solver = solverSelect.value;

  const context = contextSelect.value;

  const allowedSolvers = new Set(["default", "join", "per-origin", "warrow", "warrow-per-origin"]);

  if (!allowedSolvers.has(solver)) {
    throw new Error(`Unknown solver: ${solver}`);
  }

  const allowedContexts = new Set(["none", "entry-state", "call-string"]);

  if (!allowedContexts.has(context)) {
    throw new Error(`Unknown context mode: ${context}`);
  }

  let contextDepth = 0;

  if (context === "call-string") {
    contextDepth = Number.parseInt(contextDepthInput.value, 10);

    if (!Number.isInteger(contextDepth) || contextDepth < 1) {
      throw new Error("Call-string depth must be an integer of at least 1.");
    }
  }

  return {
    analysis,
    solver,
    context,
    contextDepth,
  };
}

function selectedLabel(select) {
  return select.options[select.selectedIndex]?.text ?? select.value;
}

function configurationLabel(configuration) {
  const parts = [selectedLabel(analysisSelect), selectedLabel(solverSelect), selectedLabel(contextSelect)];

  if (configuration.context === "call-string") {
    parts.push(`k=${configuration.contextDepth}`);
  }

  return parts.join(" · ");
}

/* -------------------------------------------------------------------------- */
/* Run analysis                                                               */
/* -------------------------------------------------------------------------- */

async function run() {
  /*
   * Treat one click / shortcut invocation as one UI transaction.
   *
   * Starting a new run invalidates every pending graph render from older
   * runs. It also clears both presentation surfaces before configuration
   * validation, so an invalid selection can never leave an old graph next to
   * a new error/table state.
   */
  const runGeneration = ++analysisRunGeneration;

  clearResults();
  clearGraph();

  if (typeof window.Voblint_run !== "function") {
    showStatus("Browser analyzer bundle is unavailable.", "error");

    return;
  }

  let configuration;

  try {
    configuration = readConfiguration();
  } catch (error) {
    if (runGeneration === analysisRunGeneration) {
      showStatus(error instanceof Error ? error.message : String(error), "error");
    }

    return;
  }

  const source = editor.state.doc.toString();

  runButton.disabled = true;

  showStatus("Analyzing...");

  try {
    /*
     * IMPORTANT:
     *
     * The browser adapter takes FIVE arguments:
     *
     *   analysis
     *   solver
     *   context
     *   context depth
     *   source
     */
    const rawResult = window.Voblint_run(configuration.analysis, configuration.solver, configuration.context, configuration.contextDepth, source);

    if (typeof rawResult !== "string") {
      throw new TypeError("Voblint_run returned " + `${typeof rawResult}; expected a JSON string.`);
    }

    const result = JSON.parse(rawResult);

    if (runGeneration !== analysisRunGeneration) {
      return;
    }

    renderResult(result);

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
      }
    } else {
      /*
       * The graph was already cleared at the start of this run. Leave it
       * cleared on analysis/configuration errors rather than preserving a
       * drawing from a previous successful result.
       */
      if (runGeneration === analysisRunGeneration) {
        clearGraph();

        showStatus(`${configurationLabel(configuration)} · failed`, "error");
      }
    }
  } catch (error) {
    if (runGeneration === analysisRunGeneration) {
      clearGraph();

      showStatus("Browser analysis failed.", "error");

      results.textContent = error instanceof Error ? error.message : String(error);
    }
  } finally {
    /*
     * An older async run must not re-enable the button while a newer run is
     * still active.
     */
    if (runGeneration === analysisRunGeneration) {
      runButton.disabled = false;
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

    syntaxHighlighting(vimpHighlight),

    EditorView.domEventHandlers({
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

contextSelect.addEventListener("change", updateContextControls);

solverSelect.addEventListener("change", updateSolverHelp);

graphZoomIn.addEventListener("click", zoomGraphIn);

graphZoomOut.addEventListener("click", zoomGraphOut);

graphZoomReset.addEventListener("click", resetGraphZoom);

graphZoomFit.addEventListener("click", fitGraphZoom);

graph.addEventListener(
  "wheel",
  (event) => {
    if (!event.ctrlKey && !event.metaKey) {
      return;
    }

    event.preventDefault();

    if (event.deltaY < 0) {
      zoomGraphIn();
    } else {
      zoomGraphOut();
    }
  },
  { passive: false },
);

updateContextControls();
updateSolverHelp();
updateZoomResetLabel();
