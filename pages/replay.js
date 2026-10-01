/*
 * Solve replay: steps through a run's solve on its control-flow graph.
 *
 * The replay reads the JSON Lines trace (schema 2) of the shown run: the events the
 * exported solver reports through its traced code equations. Every state it shows comes
 * from pages/replay_state.js's reducer, folded over those events: values, the stack of
 * open queries, the stable set, widening points, influence edges, destabilization
 * cascades, globals with their contributions, routes and counters. Nothing here
 * reconstructs history on its own.
 *
 * The trace is an unverified observation of the verified computation, and this replay
 * an unverified visualization of the trace. Nothing here feeds back into the result on
 * the page.
 */

import { contextLabel, createCache, globalKey, localKey, parseEvents } from "./replay_state.js";
import { createTraceView } from "./trace-view.js";

/* Replay states kept for jumps: stepping back or dragging the slider replays at most this many events. */
const SNAPSHOT_EVERY = 256;
/* Characters of a value shown inside a node; the node itself sizes for this many. */
const VALUE_CHARS = 30;

const UNREACHED = "not reached";

function query(selector) {
  const element = document.querySelector(selector);

  if (!element) {
    throw new Error(`Missing page element ${selector}`);
  }

  return element;
}

/* A global unknown as the page's seed list names it. */
function globalName(key) {
  if (key === "G:Global") {
    return "Global";
  }

  const [procedure, context] = key.slice(2).split("|");

  return `enter ${procedure} @ ${context}`;
}

/* One analysis's value loses its "interval: " prefix; a product keeps every label. */
function shortValue(value) {
  const bare = value.includes("; ") ? value : value.replace(/^[^:;=]+: /, "");

  return bare.length > VALUE_CHARS ? `${bare.slice(0, VALUE_CHARS - 1)}…` : bare;
}

/* --------------------------------------------------------------------- view */

export function createSolveReplay(deps) {
  const panel = query("#solve-replay");
  const count = query("#solve-replay-count");
  const message = query("#solve-replay-message");
  const retry = query("#solve-replay-load");
  const body = query("#solve-replay-body");
  const graph = query("#solve-replay-graph");
  const globalsList = query("#solve-replay-globals");
  /* Clicking a line goes to the step whose block it belongs to. */
  const trace = createTraceView(query("#solve-replay-trace"), {
    label: "Trace of the solve. Click a line to go to its step.",
    onLine: (line) => {
      if (replay) {
        stop();
        go(stepOfLine(line));
      }
    },
  });
  const detail = query("#solve-replay-detail");
  const stackList = query("#solve-replay-stack");
  const routesList = query("#solve-replay-routes");
  const countersBody = query("#solve-replay-counters");
  const slider = query("#solve-replay-slider");
  const stepLabel = query("#solve-replay-step");
  const speed = query("#solve-replay-speed");
  const buttons = {
    start: query("#solve-replay-start"),
    back: query("#solve-replay-back"),
    play: query("#solve-replay-play"),
    forward: query("#solve-replay-forward"),
    end: query("#solve-replay-end"),
  };

  /* The run offered for replay, and what was loaded from it. */
  let offered = null;
  let loading = null;
  let replay = null;
  let cy = null;
  let playing = 0;
  let selected = null;
  /* What each drawn node shows, so a step touches only nodes that changed. */
  let drawn = new Map();

  function setMessage(text, { canRetry = false, kind = "" } = {}) {
    message.textContent = text;
    message.className = kind ? `solver-globals-note ${kind}` : "solver-globals-note";
    message.hidden = text === "";
    retry.hidden = !canRetry;
  }

  function stop() {
    cancelAnimationFrame(playing);
    playing = 0;
    buttons.play.querySelector("i").className = "fa-solid fa-play";
    buttons.play.setAttribute("aria-label", "Play");
    buttons.play.title = "Play (space)";
  }

  function clear() {
    stop();
    offered = null;
    loading = null;
    replay = null;
    selected = null;
    drawn = new Map();
    cy?.destroy();
    cy = null;
    graph.replaceChildren();
    globalsList.replaceChildren();
    trace.setText("");
    detail.textContent = "";
    body.hidden = true;
    panel.open = false;
    panel.hidden = true;
    count.textContent = "";
    setMessage("");
  }

  /* A finished run can be replayed; the traces are computed only when the panel opens. */
  function offer(run) {
    clear();
    offered = run;
    panel.hidden = false;
    count.textContent = "open to load";
  }

  async function load() {
    const run = offered;

    if (!run || loading || replay) {
      return;
    }

    setMessage("Solving the run again with its traces...");
    count.textContent = "loading";

    loading = (async () => {
      const answer = JSON.parse(
        await deps.solve({ ...run.configuration, trace: "jsonl" }, run.source),
      );

      if (typeof answer.trace !== "string" || answer.status !== "ok") {
        throw new Error(answer.message ?? "the analyzer returned no trace");
      }

      const records = parseEvents(answer.trace);

      /* The verbose text the steps' lines point into: the trace panel's full form. */
      const verbose = JSON.parse(
        await deps.solve({ ...run.configuration, trace: "verbose" }, run.source),
      );

      if (typeof verbose.trace !== "string" || verbose.status !== "ok") {
        throw new Error(verbose.message ?? "the analyzer returned no trace");
      }

      return {
        answer,
        events: records.filter((record) => Number.isInteger(record.step)),
        text: verbose.trace,
      };
    })();

    try {
      const { answer, events, text } = await loading;

      if (offered !== run) {
        return;
      }

      await build(answer, events, text);
      setMessage("");
      count.textContent = `${events.length} steps`;
    } catch (error) {
      if (offered === run) {
        const detailText = error instanceof Error ? error.message : String(error);

        setMessage(`The replay could not be loaded: ${detailText}`, {
          canRetry: true,
          kind: "error",
        });
        count.textContent = "";
      }
    } finally {
      if (offered === run) {
        loading = null;
      }
    }
  }

  async function build(answer, events, text) {
    const nodeOf = new Map();
    const keyOf = new Map();
    const pointOf = new Map();

    for (const node of answer.nodes ?? []) {
      const context = node.context.slice(node.context.indexOf(" / ") + 3);
      const key = `L:${node.point}|${context}`;

      nodeOf.set(key, node.id);
      keyOf.set(node.id, key);
      pointOf.set(node.id, node.point);
    }

    /* A seed is the entry of its procedure in its context; the analysis global has no node. */
    const entryOf = (key) => {
      const [procedure, context] = key.slice(2).split("|");

      return nodeOf.get(`L:entry_${procedure}|${context}`);
    };

    const cache = createCache(events, SNAPSHOT_EVERY);

    const { cytoscape, elk } = await deps.getGraphLibraries();
    const elements = deps.graphElements(answer).map((element) => {
      if (element.group !== "nodes" || !pointOf.has(element.data.id)) {
        return element;
      }

      const point = pointOf.get(element.data.id);
      const box = deps.nodeBox([point, "x".repeat(VALUE_CHARS)]);

      return {
        ...element,
        data: { ...element.data, label: `${point}\n${UNREACHED}`, ...box },
        classes: "point r-unseen",
      };
    });
    const layout = await deps.layoutGraph(elk, elements);

    graph.replaceChildren();
    body.hidden = false;

    cy = cytoscape({
      container: graph,
      elements,
      style: [...deps.graphStyle(), ...replayStyle(deps.cssToken)],
      layout: { name: "preset" },
      minZoom: 0.1,
      maxZoom: 4,
      boxSelectionEnabled: false,
      autounselectify: true,
    });

    /*
     * Cytoscape draws node labels from textures it caches by text and style and
     * reuses without checking their size. Here labels change at every step, the cache
     * buys nothing, and a reused texture drew labels squashed; labels are drawn
     * directly instead. This reaches into the renderer's private state.
     */
    const labelCache = cy.renderer()?.data?.lblTxrCache;

    if (labelCache) {
      labelCache.getElement = () => null;
    }

    deps.applyGraphLayout(cy, layout);
    deps.followRoutesOnDrag(cy);
    cy.fit(undefined, 24);

    /* A graph too large to read when fitted starts at the solve's root unknown instead. */
    const root = events[0]?.unknown && nodeOf.get(localKey(events[0].unknown));

    if (cy.zoom() < 0.5 && root) {
      cy.zoom(0.8);
      cy.center(cy.getElementById(root));
    }

    cy.on("dbltap", (event) => {
      if (event.target === cy) {
        cy.animate({ fit: { padding: 24 } }, { duration: 260 });
      }
    });
    cy.on("tap", "node.point", (event) => {
      selected = event.target.id();
      render();
    });

    const edgesBetween = new Map();

    cy.edges().forEach((edge) => {
      const key = `${edge.source().id()}>${edge.target().id()}`;

      edgesBetween.set(key, [...(edgesBetween.get(key) ?? []), edge]);
    });

    replay = {
      events,
      lines: events.map((event) => event.line),
      cache,
      nodeOf,
      keyOf,
      pointOf,
      entryOf,
      edgesBetween,
      step: 0,
    };

    trace.setText(text);

    slider.max = String(events.length);
    render();
  }

  /* The four states: unseen, evaluated, solving (on the stack), stable; stable marking is a toggle. */
  function status(state, key, finished) {
    if (!finished && state.stack.at(-1) === key) {
      return "r-current";
    }

    if (!finished && state.stack.includes(key)) {
      return "r-solving";
    }

    if (state.stable.has(key)) {
      return "r-stable";
    }

    return state.evaluated.has(key) ? "r-seen" : "r-unseen";
  }

  /* The graph elements an event touches: edges a value flows along, and its target node. */
  function touched(event) {
    const edges = [];
    const nodes = [];
    const along = (from, to) => {
      const source = replay.nodeOf.get(from);
      const target = replay.nodeOf.get(to);

      edges.push(...(replay.edgesBetween.get(`${source}>${target}`) ?? []));
    };

    switch (event?.event) {
      case "query_local":
      case "value_local":
        along(localKey(event.target), localKey(event.current));
        nodes.push(replay.nodeOf.get(localKey(event.target)));
        break;
      case "route": {
        const call = replay.nodeOf.get(localKey(event.call));
        const context = contextLabel(event.context);

        cy.getElementById(call)
          .outgoers("edge.enter")
          .forEach((edge) => {
            if (replay.keyOf.get(edge.target().id())?.endsWith(`|${context}`)) {
              edges.push(edge);
            }
          });
        break;
      }
      case "query_global":
      case "side":
        nodes.push(replay.entryOf(globalKey(event.target)));
        break;
      case "update_global":
        nodes.push(replay.entryOf(globalKey(event.unknown)));
        break;
      default:
        break;
    }

    return { edges, nodes: nodes.filter(Boolean) };
  }

  function eventGlobal(event) {
    const unknown = event?.event === "update_global" ? event.unknown : event?.target;

    return unknown && unknown.kind !== "local" ? globalKey(unknown) : null;
  }

  function renderGraph(state, event, finished) {
    const changed = event?.event === "update_local" ? localKey(event.unknown) : null;
    const cascade = state.cascade;
    const { edges, nodes } = touched(event);

    cy.batch(() => {
      cy.nodes(".point").forEach((node) => {
        const key = replay.keyOf.get(node.id());
        const seen = state.reached.has(key);
        const value = seen ? shortValue(state.values.get(key) ?? "⊥") : UNREACHED;
        const classes = [
          "point",
          status(state, key, finished),
          cascade.has(key) ? "r-destabilized" : "",
          state.wpoints.has(key) ? "r-wpoint" : "",
          state.widened === key ? "r-widened" : "",
          key === changed ? "r-changed" : "",
          nodes.includes(node.id()) ? "r-target" : "",
          node.id() === selected ? "graph-node-selected" : "",
        ]
          .filter(Boolean)
          .join(" ");
        const label = `${replay.pointOf.get(node.id())}\n${value}`;
        const last = drawn.get(node.id());

        if (!last || last.classes !== classes || last.label !== label) {
          node.classes(classes);
          node.data("label", label);
          drawn.set(node.id(), { classes, label });
        }
      });

      cy.edges(".r-active").removeClass("r-active");

      for (const edge of edges) {
        edge.addClass("r-active");
      }

      drawInfluence(state);
    });

    const current = finished ? null : replay.nodeOf.get(state.stack.at(-1));

    /* The view follows the unknown being solved once it leaves the view. */
    if (current) {
      const node = cy.getElementById(current);
      const view = cy.extent();
      const { x, y } = node.position();

      if (x < view.x1 || x > view.x2 || y < view.y1 || y > view.y2) {
        cy.stop(true, true);
        cy.animate({ center: { eles: node } }, { duration: playing ? 0 : 200 });
      }
    }
  }

  /* Influence edges, reader to read unknown, as an overlay of their own; rebuilt per step. */
  function drawInfluence(state) {
    cy.remove("edge.r-infl");

    const edges = [];

    for (const [read, readers] of state.infl) {
      const target = read.startsWith("L:") ? replay.nodeOf.get(read) : replay.entryOf(read);

      for (const reader of readers) {
        const source = replay.nodeOf.get(reader);

        if (source && target) {
          edges.push({
            group: "edges",
            data: { id: `infl:${reader}>${read}`, source, target },
            classes: "r-infl",
          });
        }
      }
    }

    cy.add(edges);
  }

  /* The stack of open queries, innermost first; always shown. */
  function renderStack(state, finished) {
    const rows = (finished ? [] : [...state.stack].reverse()).map((key, index) => {
      const row = document.createElement("li");
      const [point, context] = key.slice(2).split("|");

      row.className = index === 0 ? "replay-stack-entry is-active" : "replay-stack-entry";
      row.textContent = `(${point}, ${context})`;

      return row;
    });

    stackList.replaceChildren(...rows);
  }

  function counterRows(state) {
    const keys = new Set([
      ...state.counters.evaluations.keys(),
      ...state.counters.updates.keys(),
      ...state.counters.destabilizations.keys(),
    ]);
    const { evaluations, updates } = state.counters;
    const naturally = new Intl.Collator(undefined, { numeric: true });

    /* The busiest unknowns first: most evaluations, then most updates, then by name. */
    const busiest = [...keys].sort(
      (a, b) =>
        (evaluations.get(b) ?? 0) - (evaluations.get(a) ?? 0) ||
        (updates.get(b) ?? 0) - (updates.get(a) ?? 0) ||
        naturally.compare(a, b),
    );
    const rows = busiest.map((key) => {
      const row = document.createElement("tr");
      const cells = [
        key.startsWith("L:") ? `(${key.slice(2).replace("|", ", ")})` : globalName(key),
        state.counters.evaluations.get(key) ?? 0,
        state.counters.updates.get(key) ?? 0,
        state.counters.destabilizations.get(key) ?? 0,
      ];

      row.replaceChildren(
        ...cells.map((value, index) => {
          const cell = document.createElement("td");

          cell.textContent = String(value);

          if (index === 0) {
            cell.title = String(value);
          }

          return cell;
        }),
      );

      return row;
    });

    countersBody.replaceChildren(...rows);
  }

  function renderRoutes(state) {
    routesList.replaceChildren(
      ...state.routes.map(({ call, context, entry }) => {
        const row = document.createElement("li");
        const head = document.createElement("span");
        const detailText = document.createElement("span");
        const [point, callContext] = call.slice(2).split("|");

        head.className = "replay-route";
        head.textContent = `${point} (${callContext}) → context ${context}`;
        detailText.className = "replay-global-detail";
        detailText.textContent = `entry ${entry}`;
        row.append(head, detailText);
        return row;
      }),
    );
  }

  function renderGlobals(state, event) {
    const active = eventGlobal(event);
    const rows = [...state.globals].map(([key, g]) => {
      const row = document.createElement("li");
      const name = document.createElement("code");
      const text = document.createElement("span");

      row.className =
        key === active ? "solver-global replay-global is-active" : "solver-global replay-global";
      name.className = "solver-global-key";
      name.textContent = globalName(key);
      text.textContent = g.value;
      row.append(name, text);

      const detailText = document.createElement("span");

      detailText.className = "replay-global-detail";
      detailText.textContent = [
        g.last ? `last change ${g.last.old} → ${g.last.new}` : "unchanged",
        `${g.contributions.length} contribution(s)${
          g.contributions.length > 0
            ? `, last ${g.contributions.at(-1).value} from ${g.contributions.at(-1).from.slice(2).replace("|", " @ ")}`
            : ""
        }`,
      ].join("; ");
      row.append(detailText);

      return row;
    });

    if (rows.length === 0) {
      const empty = document.createElement("li");

      empty.className = "solver-globals-note";
      empty.textContent = "No global unknown reached yet.";
      rows.push(empty);
    }

    globalsList.replaceChildren(...rows);
  }

  /* The verbose text is set once per load; a step only moves the current line. */
  function renderTrace(step) {
    trace.show(step === 0 ? null : replay.lines[step - 1]);
  }

  /* The first step printed on the last event line at or before [line]; 0 above them. */
  function stepOfLine(line) {
    const { lines } = replay;
    let low = 0;
    let high = lines.length;

    while (low < high) {
      const middle = (low + high) >> 1;

      if (lines[middle] <= line) {
        low = middle + 1;
      } else {
        high = middle;
      }
    }

    if (low === 0) {
      return 0;
    }

    const at = lines[low - 1];
    let first = low - 1;

    while (first > 0 && lines[first - 1] === at) {
      first--;
    }

    return first + 1;
  }

  function renderDetail(state) {
    if (!selected) {
      detail.textContent = "Click a node to read its whole value.";
      return;
    }

    const key = replay.keyOf.get(selected);
    const [point, context] = key.slice(2).split("|");
    const value = state.reached.has(key) ? (state.values.get(key) ?? "⊥") : UNREACHED;
    const facts = [
      state.stable.has(key) ? "stable" : "not stable",
      state.wpoints.has(key) ? "widening point" : "",
      `${state.counters.evaluations.get(key) ?? 0} evaluation(s)`,
      `read by ${[...(state.infl.get(key) ?? [])].map((reader) => reader.slice(2).replace("|", " @ ")).join(", ") || "nothing"}`,
    ].filter(Boolean);

    detail.textContent = `(${point}, ${context}) = ${value} · ${facts.join(" · ")}`;
  }

  function render() {
    if (!replay) {
      return;
    }

    const { step, events } = replay;
    const finished = step === events.length;
    const state = replay.cache.stateAt(step);
    const event = step > 0 ? events[step - 1] : null;

    renderGraph(state, event, finished);
    renderStack(state, finished);
    renderGlobals(state, event);
    renderRoutes(state);
    counterRows(state);

    renderTrace(step);
    renderDetail(state);

    slider.value = String(step);
    stepLabel.textContent = `Step ${step} of ${events.length}${finished ? " · solved" : ""}`;
    buttons.start.disabled = buttons.back.disabled = step === 0;
    buttons.end.disabled = buttons.forward.disabled = finished;
  }

  function go(step) {
    if (!replay) {
      return;
    }

    replay.step = Math.max(0, Math.min(replay.events.length, step));
    render();
  }

  function play() {
    if (!replay) {
      return;
    }

    if (playing) {
      stop();
      return;
    }

    if (replay.step === replay.events.length) {
      go(0);
    }

    let last = performance.now();
    let owed = 0;

    buttons.play.querySelector("i").className = "fa-solid fa-pause";
    buttons.play.setAttribute("aria-label", "Pause");
    buttons.play.title = "Pause (space)";

    const tick = (time) => {
      owed += ((time - last) / 1000) * Number(speed.value);
      last = time;

      const steps = Math.floor(owed);

      if (steps > 0) {
        owed -= steps;
        go(replay.step + steps);
      }

      if (replay.step >= replay.events.length) {
        stop();
        return;
      }

      playing = requestAnimationFrame(tick);
    };

    playing = requestAnimationFrame(tick);
  }

  panel.addEventListener("toggle", () => {
    if (panel.open) {
      load();
      cy?.resize();
    } else {
      stop();
    }
  });

  retry.addEventListener("click", load);
  buttons.start.addEventListener("click", () => go(0));
  buttons.back.addEventListener("click", () => go(replay.step - 1));
  buttons.forward.addEventListener("click", () => go(replay.step + 1));
  buttons.end.addEventListener("click", () => go(replay.events.length));
  buttons.play.addEventListener("click", play);
  slider.addEventListener("input", () => go(Number(slider.value)));

  /* Arrow keys step, space plays, Home and End jump, anywhere in the panel but the slider. */
  body.addEventListener("keydown", (event) => {
    if (!replay || event.target === slider || event.target === speed) {
      return;
    }

    const keys = {
      ArrowLeft: () => go(replay.step - 1),
      ArrowRight: () => go(replay.step + 1),
      Home: () => go(0),
      End: () => go(replay.events.length),
      " ": play,
    };

    if (keys[event.key]) {
      event.preventDefault();
      keys[event.key]();
    }
  });

  return { offer, clear };
}

/* The four states, the current unknown and the step's edges, on top of the CFG's own style. */
function replayStyle(cssToken) {
  return [
    /* A step replaces the previous step's marks at once; a fade would blend the two. */
    { selector: "node.point", style: { "transition-duration": 0 } },
    {
      selector: "node.point.r-unseen",
      style: {
        "border-style": "dashed",
        "border-width": 1,
        "border-color": cssToken("--text-faint"),
        "background-color": cssToken("--surface-muted"),
        color: cssToken("--text-faint"),
      },
    },
    {
      selector: "node.point.r-seen",
      style: {
        "border-width": 1,
        "border-color": cssToken("--border-strong"),
        "background-color": cssToken("--surface"),
      },
    },
    {
      selector: "node.point.r-stable",
      style: {
        "border-width": 2,
        "border-color": cssToken("--primary"),
        "background-color": cssToken("--primary-soft"),
      },
    },
    {
      selector: "node.point.r-solving",
      style: {
        "border-width": 2,
        "border-color": cssToken("--accent"),
        "background-color": cssToken("--accent-soft"),
        "underlay-opacity": 0.25,
      },
    },
    {
      selector: "node.point.r-current",
      style: {
        "border-width": 4,
        "border-color": cssToken("--accent"),
        "background-color": cssToken("--accent-soft"),
        "underlay-opacity": 0.25,
      },
    },
    {
      selector: "node.point.r-destabilized",
      style: { "border-style": "dotted", "border-width": 2 },
    },
    {
      selector: "node.point.r-target",
      style: { "outline-color": cssToken("--primary"), "outline-width": 3, "outline-offset": 3 },
    },
    {
      selector: "node.point.r-changed",
      style: { "underlay-color": cssToken("--success"), "underlay-opacity": 0.35 },
    },
    {
      selector: "node.point.r-wpoint",
      style: { "border-style": "double", "border-width": 4 },
    },
    {
      selector: "node.point.r-widened",
      style: { "underlay-color": cssToken("--accent"), "underlay-opacity": 0.35 },
    },
    {
      selector: "edge.r-infl",
      style: {
        width: 1.5,
        "line-style": "dotted",
        "curve-style": "unbundled-bezier",
        "line-color": cssToken("--text-faint"),
        "target-arrow-shape": "triangle",
        "target-arrow-color": cssToken("--text-faint"),
        "z-index": 5,
      },
    },
    {
      selector: "edge.r-active",
      style: {
        width: 4,
        "line-style": "solid",
        "line-color": cssToken("--accent"),
        "target-arrow-color": cssToken("--accent"),
        "z-index": 10,
      },
    },
  ];
}
