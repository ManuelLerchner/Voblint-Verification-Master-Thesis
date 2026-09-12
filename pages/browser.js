import {
  EditorView,
  basicSetup,
} from "https://esm.sh/codemirror@6.0.2";

import {
  HighlightStyle,
  StreamLanguage,
  syntaxHighlighting,
} from "https://esm.sh/@codemirror/language@6.12.4";

import {
  tags,
} from "https://esm.sh/@lezer/highlight@1.2.3";


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

    if (
      stream.match(
        /^(fun|global|if|else|while|return)\b/
      )
    ) {
      return "keyword";
    }

    if (
      stream.match(
        /^(==|!=|<=|>=|&&|\|\||[+\-*/%<>=!])/
      )
    ) {
      return "operator";
    }

    if (
      stream.match(
        /^[A-Za-z_][A-Za-z0-9_]*/
      )
    ) {
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

  status.className = kind
    ? `status ${kind}`
    : "status";
}


function clearResults() {
  results.replaceChildren();
}


function renderResult(result) {
  clearResults();

  if (result.status !== "ok") {
    const error = document.createElement("p");
    error.className = "result-error";

    if (
      Number.isInteger(result.line) &&
      Number.isInteger(result.column)
    ) {
      error.textContent =
        `${result.line}:${result.column}: ${result.message}`;
    } else {
      error.textContent =
        result.message ??
        "The program could not be analyzed.";
    }

    results.append(error);
    return;
  }


  const checks =
    Array.isArray(result.checks)
      ? result.checks
      : [];

  if (checks.length > 0) {
    const list = document.createElement("div");
    list.className = "result-list";

    for (const check of checks) {
      const verdict =
        typeof check.verdict === "string"
          ? check.verdict
          : "UNKNOWN";

      const row = document.createElement("div");
      row.className =
        `result-row ${verdict.toLowerCase()}`;

      const verdictElement =
        document.createElement("strong");

      verdictElement.textContent = verdict;


      const body =
        document.createElement("div");

      body.className = "result-body";


      const condition =
        document.createElement("code");

      condition.textContent =
        check.condition ?? "";


      const state =
        document.createElement("span");

      const point =
        check.point
          ? `${check.point} · `
          : "";

      state.textContent =
        `${point}${check.state ?? ""}`;


      body.append(
        condition,
        state,
      );

      row.append(
        verdictElement,
        body,
      );

      list.append(row);
    }

    results.append(list);
  }


  const diagnostics =
    Array.isArray(result.diagnostics)
      ? result.diagnostics
      : [];

  if (diagnostics.length > 0) {
    const heading =
      document.createElement("h3");

    heading.textContent = "Diagnostics";
    results.append(heading);

    for (const diagnostic of diagnostics) {
      const row =
        document.createElement("p");

      const severity =
        diagnostic.severity ?? "info";

      row.className =
        `diagnostic ${severity}`;

      row.textContent =
        `${severity}: ${diagnostic.message ?? ""}`;

      results.append(row);
    }
  }


  if (
    checks.length === 0 &&
    diagnostics.length === 0
  ) {
    const empty =
      document.createElement("p");

    empty.className = "result-empty";

    empty.textContent =
      "Analysis completed without reported checks or diagnostics.";

    results.append(empty);
  }
}


/* -------------------------------------------------------------------------- */
/* Configuration                                                              */
/* -------------------------------------------------------------------------- */

function updateContextControls() {
  const usesCallString =
    contextSelect.value === "call-string";

  contextDepthGroup.hidden =
    !usesCallString;

  contextDepthInput.disabled =
    !usesCallString;
}


function updateSolverHelp() {
  const descriptions = {
    default:
      "Use Voblint's production solver for this domain and context.",

    join:
      "Always join updates. Explicit solver override.",

    "per-origin":
      "Keep contributions separate by origin before combining them.",

    warrow:
      "Use widening followed by narrowing.",

    "warrow-per-origin":
      "Apply widening and narrowing separately to per-origin contributions.",
  };

  solverHelp.textContent =
    descriptions[solverSelect.value] ?? "";
}


function readConfiguration() {
  const analysis =
    analysisSelect.value;

  const solver =
    solverSelect.value;

  const context =
    contextSelect.value;


  const allowedSolvers =
    new Set([
      "default",
      "join",
      "per-origin",
      "warrow",
      "warrow-per-origin",
    ]);

  if (!allowedSolvers.has(solver)) {
    throw new Error(
      `Unknown solver: ${solver}`,
    );
  }


  const allowedContexts =
    new Set([
      "none",
      "entry-state",
      "call-string",
    ]);

  if (!allowedContexts.has(context)) {
    throw new Error(
      `Unknown context mode: ${context}`,
    );
  }


  let contextDepth = 0;

  if (context === "call-string") {
    contextDepth =
      Number.parseInt(
        contextDepthInput.value,
        10,
      );

    if (
      !Number.isInteger(contextDepth) ||
      contextDepth < 1
    ) {
      throw new Error(
        "Call-string depth must be an integer of at least 1.",
      );
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
  return (
    select.options[
      select.selectedIndex
    ]?.text ??
    select.value
  );
}


function configurationLabel(configuration) {
  const parts = [
    selectedLabel(analysisSelect),
    selectedLabel(solverSelect),
    selectedLabel(contextSelect),
  ];

  if (
    configuration.context ===
    "call-string"
  ) {
    parts.push(
      `k=${configuration.contextDepth}`,
    );
  }

  return parts.join(" · ");
}


/* -------------------------------------------------------------------------- */
/* Run analysis                                                               */
/* -------------------------------------------------------------------------- */

function run() {
  if (
    typeof window.Voblint_run !==
    "function"
  ) {
    showStatus(
      "Browser analyzer bundle is unavailable.",
      "error",
    );

    return;
  }


  let configuration;

  try {
    configuration =
      readConfiguration();
  } catch (error) {
    showStatus(
      error instanceof Error
        ? error.message
        : String(error),
      "error",
    );

    return;
  }


  const source =
    editor.state.doc.toString();


  runButton.disabled = true;

  clearResults();
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
    const rawResult =
      window.Voblint_run(
        configuration.analysis,
        configuration.solver,
        configuration.context,
        configuration.contextDepth,
        source,
      );


    if (typeof rawResult !== "string") {
      throw new TypeError(
        "Voblint_run returned " +
        `${typeof rawResult}; expected a JSON string.`,
      );
    }


    const result =
      JSON.parse(rawResult);


    renderResult(result);


    if (result.status === "ok") {
      showStatus(
        `${configurationLabel(configuration)} · complete`,
        "ok",
      );
    } else {
      showStatus(
        `${configurationLabel(configuration)} · failed`,
        "error",
      );
    }
  } catch (error) {
    showStatus(
      "Browser analysis failed.",
      "error",
    );

    results.textContent =
      error instanceof Error
        ? error.message
        : String(error);
  } finally {
    runButton.disabled = false;
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

    syntaxHighlighting(
      vimpHighlight,
    ),

    EditorView.domEventHandlers({
      keydown(event) {
        if (
          (event.metaKey ||
            event.ctrlKey) &&
          event.key === "Enter"
        ) {
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

runButton.addEventListener(
  "click",
  run,
);

contextSelect.addEventListener(
  "change",
  updateContextControls,
);

solverSelect.addEventListener(
  "change",
  updateSolverHelp,
);


updateContextControls();
updateSolverHelp();