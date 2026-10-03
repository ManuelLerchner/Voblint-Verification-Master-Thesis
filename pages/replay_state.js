/*
 * The solve replay's state, folded from the JSON Lines trace (schema 2).
 *
 * One reducer, `reduce(state, event)`, defines what every event does to the replayed
 * solver state. The playground's animation, its per-step text and its snapshot cache all
 * go through it; nothing else reconstructs history. No DOM here, so Node runs it too
 * (tests/replay_state.test.mjs, tests/replay_check.mjs).
 *
 * What each event is (docs/CLI_DESIGN.md lists the same classification):
 *   start                  scope enter: the root unknown opens the solve stack
 *   query_local            scope enter: the queried unknown is pushed
 *   value_local            scope leave: the queried unknown is popped; observation of its value
 *   iterate                observation (called, stable and widening-point flags as read)
 *   solve / resolve        observation (an iteration of an unstable unknown)
 *   eq                     state transition: one right-hand-side evaluation (counted)
 *   stable_add             state transition: the unknown enters the stable set
 *   stable_remove          state transition: the unknown leaves the stable set
 *   still_unstable         observation
 *   widen                  observation: widening is applied at this step
 *   wpoint_add / _remove   state transition: widening-point membership
 *   add_infl               relation add: reader -> unknown
 *   destabilize            relation remove: every reader of the unknown is dropped
 *   update_local           state transition: the local unknown's stored value
 *   query_global           observation: the global's value as read
 *   side                   observation: one contribution to a global
 *   update_global          state transition: the global's stored value
 *   answer                 observation: the value a right-hand side returned
 *   route                  observation: the context a call is routed to
 */

/* The name the result gives a context, as cli/result/result_text.ml's context_label writes it. */
export function contextLabel(context) {
  switch (context?.kind) {
    case "unit":
      return "unit";
    case "entry_state":
      return context.values.length > 0 ? context.values.join(", ") : "root context";
    case "call_string":
      return context.sites.length > 0 ? `call-string=${context.sites.join(" ")}` : "root context";
    default:
      return "?";
  }
}

export function localKey(unknown) {
  return `L:${unknown.node}|${contextLabel(unknown.context)}`;
}

/* A seed is keyed by procedure and context, a program global by name after "@". */
export function globalKey(unknown) {
  switch (unknown.kind) {
    case "activation_seed":
      return `G:${unknown.procedure}|${contextLabel(unknown.context)}`;
    case "program_global":
      return `G:@${unknown.name}`;
    default:
      return "G:#buffer";
  }
}

export function unknownKey(unknown) {
  return unknown.kind === "local" ? localKey(unknown) : globalKey(unknown);
}

export function emptyState() {
  return {
    /* Local unknown -> stored value; an unknown without one holds ⊥. */
    values: new Map(),
    /* Local unknowns whose right-hand side has been evaluated at least once. */
    evaluated: new Set(),
    /* Local unknowns reached by the solve (the root or a query). */
    reached: new Set(),
    /* Open queries above the root, innermost last. */
    stack: [],
    stable: new Set(),
    wpoints: new Set(),
    /* Read unknown -> the local unknowns that read it. */
    infl: new Map(),
    /* Global unknown -> { value, contributions: [{ from, value }], last: { old, new } | null }. */
    globals: new Map(),
    routes: [],
    /* evaluations(u): right-hand-side evaluations of u. updates(u): stored value changed.
       destabilizations(u): transitions of u from stable to not stable. */
    counters: { evaluations: new Map(), updates: new Map(), destabilizations: new Map() },
    /* Unknowns removed from the stable set since the last update: one cascade. */
    cascade: new Set(),
    /* The step's own marks. */
    widened: null,
    /* Directed relations used by this event, from its payload or recorded influence. */
    eventEdges: [],
    event: null,
    /* Consistency problems found while folding; empty for a well-formed trace. */
    problems: [],
  };
}

export function copyState(state) {
  return {
    values: new Map(state.values),
    evaluated: new Set(state.evaluated),
    reached: new Set(state.reached),
    stack: [...state.stack],
    stable: new Set(state.stable),
    wpoints: new Set(state.wpoints),
    infl: new Map([...state.infl].map(([key, readers]) => [key, new Set(readers)])),
    globals: new Map(
      [...state.globals].map(([key, g]) => [
        key,
        { value: g.value, contributions: [...g.contributions], last: g.last },
      ]),
    ),
    routes: [...state.routes],
    counters: {
      evaluations: new Map(state.counters.evaluations),
      updates: new Map(state.counters.updates),
      destabilizations: new Map(state.counters.destabilizations),
    },
    cascade: new Set(state.cascade),
    widened: state.widened,
    eventEdges: state.eventEdges.map((edge) => ({ ...edge })),
    event: state.event,
    problems: [...state.problems],
  };
}

function bump(counter, key) {
  counter.set(key, (counter.get(key) ?? 0) + 1);
}

function global(state, key) {
  let g = state.globals.get(key);

  if (!g) {
    g = { value: "⊥", contributions: [], last: null };
    state.globals.set(key, g);
  }

  return g;
}

/* The reducer's body, on a state the caller owns. */
export function applyInPlace(state, event) {
  state.event = event;
  state.widened = null;
  state.eventEdges = [];

  switch (event.event) {
    case "start": {
      const key = localKey(event.unknown);

      state.reached.add(key);
      state.stack.push(key);
      break;
    }
    case "query_local": {
      const key = localKey(event.target);

      state.reached.add(key);
      state.stack.push(key);
      break;
    }
    case "value_local": {
      const key = localKey(event.target);

      if (state.stack.at(-1) !== key) {
        state.problems.push(`value_local for ${key} with ${state.stack.at(-1)} on top`);
      }

      state.stack.pop();
      break;
    }
    case "eq": {
      const key = localKey(event.unknown);

      state.evaluated.add(key);
      bump(state.counters.evaluations, key);
      break;
    }
    case "stable_add":
      state.stable.add(localKey(event.unknown));
      break;
    case "stable_remove": {
      const key = localKey(event.unknown);

      if (state.stable.delete(key)) {
        bump(state.counters.destabilizations, key);
        state.cascade.add(key);
      }

      break;
    }
    case "widen":
      state.widened = localKey(event.unknown);
      break;
    case "wpoint_add":
      state.wpoints.add(localKey(event.unknown));
      break;
    case "wpoint_remove":
      state.wpoints.delete(localKey(event.unknown));
      break;
    case "add_infl": {
      const key = unknownKey(event.unknown);
      const readers = state.infl.get(key) ?? new Set();

      readers.add(localKey(event.reader));
      state.infl.set(key, readers);
      break;
    }
    case "destabilize": {
      const from = unknownKey(event.unknown);

      // Capture the logged dependencies before this event consumes them. A value
      // change alone supplies neither these readers nor a destabilization event.
      state.eventEdges = [...(state.infl.get(from) ?? [])].map((to) => ({
        from,
        to,
        kind: "destabilize",
      }));
      state.infl.delete(from);
      break;
    }
    case "update_local": {
      const key = localKey(event.unknown);

      state.values.set(key, event.new);
      state.cascade = new Set();

      if (event.old !== event.new) {
        bump(state.counters.updates, key);
      }

      break;
    }
    case "query_global":
      global(state, globalKey(event.target)).value = event.value;
      state.eventEdges.push({
        from: globalKey(event.target),
        to: localKey(event.current),
        kind: "read",
      });
      break;
    case "side":
      global(state, globalKey(event.target)).contributions.push({
        from: localKey(event.current),
        value: event.value,
      });
      state.eventEdges.push({
        from: localKey(event.current),
        to: globalKey(event.target),
        kind: "side",
      });
      break;
    case "update_global": {
      const key = globalKey(event.unknown);
      const g = global(state, key);

      g.value = event.new;
      g.last = { old: event.old, new: event.new };
      state.cascade = new Set();

      if (event.old !== event.new) {
        bump(state.counters.updates, key);
      }

      break;
    }
    case "route":
      state.routes.push({
        call: localKey(event.call),
        context: contextLabel(event.context),
        entry: event.entry,
      });
      break;
    default:
      break;
  }

  return state;
}

/* The canonical reducer: ReplayState x Event -> ReplayState, leaving its argument alone. */
export function reduce(state, event) {
  return applyInPlace(copyState(state), event);
}

/*
 * States after any number of events, from snapshots taken every [every] events. The
 * working copy is private to the cache and only ever advanced through applyInPlace.
 */
export function createCache(events, every = 256) {
  const snapshots = [];
  const work = emptyState();

  events.forEach((event, index) => {
    if (index % every === 0) {
      snapshots.push(copyState(work));
    }

    applyInPlace(work, event);
  });

  let state = copyState(snapshots[0] ?? emptyState());
  let at = 0;

  return {
    final: work,
    stateAt(step) {
      if (step < at || step - at > every) {
        const base = Math.min(Math.floor(step / every), snapshots.length - 1);

        state = copyState(snapshots[Math.max(0, base)] ?? emptyState());
        at = Math.max(0, base) * every;
      }

      while (at < step) {
        applyInPlace(state, events[at]);
        at++;
      }

      return state;
    },
  };
}

/* Names as the CLI's trace writes them (cli/render/solver_trace.ml). */
function traceContext(context) {
  switch (context?.kind) {
    case "unit":
      return "unit";
    case "entry_state":
      return context.values.length > 0 ? `[${context.values.join(", ")}]` : "root";
    case "call_string":
      return context.sites.length > 0 ? `[${context.sites.join(" ")}]` : "root";
    default:
      return "?";
  }
}

function traceLocal(unknown) {
  return `(${unknown.node}, ${traceContext(unknown.context)})`;
}

function traceGlobal(unknown) {
  switch (unknown.kind) {
    case "activation_seed":
      return `Seed(${unknown.procedure}, ${traceContext(unknown.context)})`;
    case "program_global":
      return `Global ${unknown.name}`;
    default:
      return "Buffer";
  }
}

function traceUnknown(unknown) {
  return unknown.kind === "local" ? traceLocal(unknown) : traceGlobal(unknown);
}

/* One step's label, subject and detail lines. */
function stepText(event) {
  const one = (label) => [label, traceLocal(event.unknown), []];

  switch (event.event) {
    case "start":
      return one("START");
    case "solve":
    case "resolve":
      return one(event.event.toUpperCase());
    case "iterate":
      return [
        "ITERATE",
        `${traceLocal(event.unknown)} called: ${event.called}, stable: ${event.stable}, wpoint: ${event.wpoint}`,
        [],
      ];
    case "eq":
      return one("EQ");
    case "stable_add":
      return one("STABLE+");
    case "stable_remove":
      return one("STABLE-");
    case "still_unstable":
      return one("UNSTABLE");
    case "widen":
      return one("WIDEN");
    case "wpoint_add":
      return one("WPOINT+");
    case "wpoint_remove":
      return one("WPOINT-");
    case "add_infl":
      return ["INFL+", `${traceLocal(event.reader)} reads ${traceUnknown(event.unknown)}`, []];
    case "destabilize":
      return ["DESTAB", traceUnknown(event.unknown), []];
    case "query_local":
      return ["QUERY-L", `${traceLocal(event.current)} -> ${traceLocal(event.target)}`, []];
    case "value_local":
      return [
        "VALUE-L",
        `${traceLocal(event.target)} to ${traceLocal(event.current)}`,
        [["value", event.value]],
      ];
    case "query_global":
      return [
        "QUERY-G",
        `${traceLocal(event.current)} -> ${traceGlobal(event.target)}`,
        [["value", event.value]],
      ];
    case "side":
      return [
        "SIDE",
        `${traceLocal(event.current)} -> ${traceGlobal(event.target)}`,
        [["value", event.value]],
      ];
    case "update_global":
      return [
        "UPDATE-G",
        traceGlobal(event.unknown),
        [
          ["old", event.old],
          ["new", event.new],
        ],
      ];
    case "update_local":
      return [
        "UPDATE-L",
        traceLocal(event.unknown),
        [
          ["old", event.old],
          ["new", event.new],
        ],
      ];
    case "answer":
      return ["ANSWER", traceLocal(event.current), [["value", event.value]]];
    case "route":
      return [
        "ROUTE",
        `call at ${traceLocal(event.call)} -> context ${traceContext(event.context)}`,
        [["entry", event.entry]],
      ];
    default:
      return [event.event, "", []];
  }
}

/* One block per step, indented by the depth of the solve stack after it. */
export function stepBlock(event, index, state) {
  const indent = "  ".repeat(Math.max(0, state.stack.length - 1));
  const [label, subject, details] = stepText(event);
  const head = `[${String(index + 1).padStart(3, "0")}] ${indent}${label.padEnd(9)} ${subject}`;

  return [head, ...details.map(([key, value]) => `      ${indent}${key} = ${value}`)].join("\n");
}

export function parseEvents(jsonl) {
  return jsonl
    .split("\n")
    .filter((line) => line.trim() !== "")
    .map((line) => JSON.parse(line));
}

/*
 * The replay's final state against the result run_voblint returned: every result
 * record's value equals the replayed value (⊥ when the trace never stored one), and the
 * replayed stable set is the set of unknowns the result covers. Returns the mismatches.
 */
export function checkAgainstResult(records) {
  const steps = records.filter((record) => Number.isInteger(record.step));
  const results = records.filter((record) => record.event === "result");
  const { final } = createCache(steps);
  const problems = [...final.problems];

  for (const record of results) {
    const key = localKey(record.unknown);
    const replayed = final.values.get(key) ?? "⊥";

    if (replayed !== record.value) {
      problems.push(`${key}: replayed ${replayed}, result ${record.value}`);
    }
  }

  const covered = new Set(results.map((record) => localKey(record.unknown)));

  for (const key of final.stable) {
    if (!covered.has(key)) {
      problems.push(`${key} is stable but not in the result`);
    }
  }

  for (const key of covered) {
    if (!final.stable.has(key)) {
      problems.push(`${key} is in the result but not stable`);
    }
  }

  if (final.stack.length !== 1) {
    problems.push(`the solve stack ends with ${final.stack.length} entries, not the root alone`);
  }

  return problems;
}
