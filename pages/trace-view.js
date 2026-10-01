/*
 * A read-only view of a solver trace, shared by the trace panel and the solve replay.
 *
 * It reads two forms of the same events: the CLI's trace (`voblint --trace`, compact or
 * --verbose) and the replay's step blocks (`[007] QUERY-L ...`). Everything it adds is
 * presentation: the coloring follows each line's event kind, a query of a procedure's
 * exit unknown opens a banner naming the call, side effects get a gutter mark, and a
 * line folds together with the deeper lines after it. The text itself is never
 * changed, so a download is still the analyzer's output byte for byte.
 */

import {
  codeFolding,
  foldedRanges,
  foldGutter,
  foldService,
  HighlightStyle,
  StreamLanguage,
  syntaxHighlighting,
  unfoldEffect,
} from "https://esm.sh/@codemirror/language@^6.0.0";
import {
  EditorState,
  RangeSetBuilder,
  StateEffect,
  StateField,
} from "https://esm.sh/@codemirror/state@^6.0.0";
import {
  Decoration,
  EditorView,
  GutterMarker,
  gutter,
  highlightSpecialChars,
  lineNumbers,
  WidgetType,
} from "https://esm.sh/@codemirror/view@^6.0.0";
import { tags } from "https://esm.sh/@lezer/highlight@^1.0.0";

/* ---------------------------------------------------------------- event kinds */

/*
 * Every event label of the three forms, by what it does to the solve. A query's answer,
 * a solve step's `sol` and the change it stores carry the values the solve computes,
 * so they get kinds of their own.
 */
const KIND_OF = new Map(
  Object.entries({
    query: [
      "solver_query",
      "eq",
      "iter",
      "multivar",
      "QUERY",
      "QUERY-L",
      "QUERY-G",
      "VALUE-L",
      "RETURN",
      "EQ",
      "ITERATE",
      "SOLVE",
      "RESOLVE",
      "START",
    ],
    answer: ["answer", "ANSWER"],
    sol: ["sol"],
    stored: ["update", "UPDATE-L", "UPDATE-G"],
    update: ["rhs"],
    widen: ["wpoint", "WIDEN", "WPOINT+", "WPOINT-"],
    stable: ["destab", "infl", "DESTAB", "STABLE+", "STABLE-", "UNSTABLE", "INFL+", "RESTART"],
    side: ["side", "SIDE", "FLUSH"],
    route: ["route", "ROUTE"],
    check: ["CHECK"],
  }).flatMap(([kind, labels]) => labels.map((label) => [label, kind])),
);

const KINDS = [
  "query",
  "answer",
  "sol",
  "stored",
  "update",
  "widen",
  "stable",
  "side",
  "route",
  "check",
];

/* A line that starts an event, and where its label sits; other lines continue one. */
const HEAD = /^(\[\d+\] )?( *)(?:%%% ([a-z_]+):|([A-Z][A-Z+-]+)(?= ))/;

function headOf(text) {
  const match = HEAD.exec(text);

  if (!match) {
    return null;
  }

  const label = match[3] ?? match[4];

  return {
    depth: match[2].length,
    labelAt: (match[1] ?? "").length + match[2].length,
    kind: KIND_OF.get(label) ?? null,
  };
}

/* A query of a procedure's exit unknown asks for that procedure's result: a call. */
const CALL = /(?:entering query for|asks|->) \(exit_([\w']+), (.*?)\)(?:;| from |$)/;
const ROOT = /(?:solving for|START) +\(exit_([\w']+), (.*?)\)/;

function callOf(text) {
  const call = CALL.exec(text);
  const root = call ? null : ROOT.exec(text);

  if (call) {
    return `call ${call[1]} @ ${call[2]}`;
  }

  return root ? `solve ${root[1]} @ ${root[2]}` : null;
}

/* ---------------------------------------------------------------- highlighting */

/* Existing tags, one per kind of token, which only the trace's own style below colors. */
const traceTags = {
  query: tags.controlKeyword,
  answer: tags.className,
  sol: tags.typeName,
  stored: tags.attributeName,
  update: tags.definitionKeyword,
  widen: tags.operatorKeyword,
  stable: tags.comment,
  side: tags.moduleKeyword,
  route: tags.namespace,
  check: tags.annotation,
};
const unknownTag = tags.labelName;
const valueTag = tags.number;
const keyTag = tags.propertyName;
const stepTag = tags.meta;
const provedTag = tags.inserted;
const failedTag = tags.deleted;

const traceParser = {
  name: "voblint-trace",
  startState: () => ({ atHead: true, event: null }),
  token(stream, state) {
    if (stream.sol()) {
      state.atHead = true;

      if (stream.match(/^\[\d+\]/)) {
        return "step";
      }
    }

    if (stream.eatSpace()) {
      return null;
    }

    if (state.atHead) {
      state.atHead = false;

      const label = stream.match(/^%%% ([a-z_]+):/) ?? stream.match(/^[A-Z][A-Z+-]+(?= )/);

      if (label) {
        state.event = KIND_OF.get(label[1] ?? label[0]) ?? "key";
        return state.event;
      }
    }

    if (stream.match(/^(?:answer|value)(?=:| =)/)) {
      return "answer";
    }

    // A value line takes the chip of the event it belongs to.
    if (stream.match(/^(?:Old value|New value|Eqd)(?=:)|^(?:old|new)(?= =)/)) {
      return state.event === "sol" || state.event === "stored" ? state.event : "key";
    }

    if (stream.match(/^(?:PROVED|DEAD)\b/)) {
      return "proved";
    }

    if (stream.match(/^(?:REFUTED|UNKNOWN|WARNING|ERROR)\b/)) {
      return "failed";
    }

    // A statement point carries its source: `(pp4 "x = x + 1;" L4, ctx)`.
    if (
      stream.match(/^(?:Seed|Global)?\((?:entry_|exit_)?[\w']+(?: "[^"]*")?(?: L\d+)?, [^()]*\)/)
    ) {
      return "unknown";
    }

    if (stream.match(/^(?:[⊤⊥]|[+-]?∞|-?\d+)/)) {
      return "value";
    }

    stream.next();
    return null;
  },
  tokenTable: {
    ...traceTags,
    unknown: unknownTag,
    value: valueTag,
    key: keyTag,
    step: stepTag,
    proved: provedTag,
    failed: failedTag,
  },
};

const traceHighlight = HighlightStyle.define([
  ...KINDS.map((kind) => ({ tag: traceTags[kind], class: `tr-${kind}` })),
  { tag: unknownTag, class: "tr-unknown" },
  { tag: valueTag, class: "tr-value" },
  { tag: keyTag, class: "tr-key" },
  { tag: stepTag, class: "tr-step" },
  { tag: provedTag, class: "tr-proved" },
  { tag: failedTag, class: "tr-failed" },
]);

/* ---------------------------------------------------------------- folding */

/* An event folds together with the deeper events after it and their continuations. */
const foldByDepth = foldService.of((state, from) => {
  const { doc } = state;
  const line = doc.lineAt(from);
  const head = headOf(line.text);

  if (!head) {
    return null;
  }

  let last = line.number;

  for (let at = line.number + 1; at <= doc.lines; at++) {
    const next = headOf(doc.line(at).text);

    if (next && next.depth <= head.depth) {
      break;
    }

    if (!next && doc.line(at).text.trim() === "") {
      break;
    }

    last = at;
  }

  return last > line.number + 1 ? { from: line.to, to: doc.line(last).to } : null;
});

/* ---------------------------------------------------------------- layout and diffs */

/*
 * The CLI prints an event's value lines (`Old value:`, `answer:`) at column 0; they are
 * drawn under their event instead. In an old/new pair, the components (`x=[0,9]`) one
 * side has and the other lacks are marked, like a diff. The value lines of one event
 * are padded into columns so the same component sits at the same place on each.
 */
const OLD_VALUE = /^ *(?:Old value: |old = )/;
const NEW_VALUE = /^ *(?:New value: |new = )/;
const VALUE_LINE = /^ *(?:Old value: |Eqd: |New value: |answer: |value = |old = |new = )/;

function parts(text, offset) {
  const found = [];
  const separator = /, |; /g;
  let start = 0;

  for (let match = separator.exec(text); ; match = separator.exec(text)) {
    const end = match ? match.index : text.length;

    found.push({ text: text.slice(start, end), from: offset + start, to: offset + end });

    if (!match) {
      return found;
    }

    start = match.index + match[0].length;
  }
}

/*
 * Ranges of [mine]'s parts that [other] lacks, marked with [mark]. A side of one part,
 * such as ⊥, has nothing to line up with, so a pair with one marks nothing.
 */
function changes(mine, other, mark) {
  if (mine.length < 2 || other.length < 2) {
    return [];
  }

  const theirs = new Set(other.map((part) => part.text));

  return mine
    .filter((part) => part.to > part.from && !theirs.has(part.text))
    .map((part) => mark.range(part.from, part.to));
}

const removedMark = Decoration.mark({ class: "tr-removed" });
const addedMark = Decoration.mark({ class: "tr-added" });

function valueAt(line, pattern) {
  const match = pattern.exec(line.text);

  return match ? parts(line.text.slice(match[0].length), line.from + match[0].length) : null;
}

class Pad extends WidgetType {
  constructor(width) {
    super();
    this.width = width;
  }

  eq(other) {
    return other.width === this.width;
  }

  toDOM() {
    const pad = document.createElement("span");

    pad.textContent = " ".repeat(this.width);
    return pad;
  }
}

/* Padding goes before what it moves, outside any diff mark that starts there. */
function padAt(at, width) {
  return Decoration.widget({ widget: new Pad(width), side: -1 }).range(at);
}

function keyOf(part) {
  return part.text.split("=")[0];
}

/* A value line's components, and the column its value starts at. */
function valueRow(line) {
  const label = VALUE_LINE.exec(line.text);

  return label
    ? {
        column: label[0].length,
        parts: parts(line.text.slice(label[0].length), line.from + label[0].length),
      }
    : null;
}

/*
 * Pads a block of value rows into columns: the values first, then each component for
 * the rows whose components so far have the same names as the longest row's. A row of
 * one component, such as ⊥, only has its start aligned.
 */
function align(block) {
  const ranges = [];
  const start = Math.max(...block.map((row) => row.column));
  const reference = block.reduce((a, b) => (b.parts.length > a.parts.length ? b : a)).parts;

  for (const row of block) {
    if (row.column < start) {
      ranges.push(padAt(row.parts[0].from, start - row.column));
    }

    row.matched =
      row.parts.length < 2
        ? 0
        : row.parts.findIndex((part, k) => keyOf(part) !== keyOf(reference[k] ?? { text: "" }));

    if (row.matched < 0) {
      row.matched = row.parts.length;
    }
  }

  for (let column = 0; column < reference.length; column++) {
    const rows = block.filter((row) => row.matched > column);
    const width = Math.max(0, ...rows.map((row) => row.parts[column].text.length));

    for (const row of rows) {
      const cell = row.parts[column];
      const next = row.parts[column + 1];

      if (cell.text.length < width && next) {
        ranges.push(padAt(next.from, width - cell.text.length));
      }
    }
  }

  return ranges;
}

function layout(doc) {
  const ranges = [];
  let labelAt = 0;
  let old = null;
  let block = [];

  const endBlock = () => {
    if (block.length > 1) {
      ranges.push(...align(block));
    }

    block = [];
  };

  for (let at = 1; at <= doc.lines; at++) {
    const line = doc.line(at);
    const head = headOf(line.text);
    const own = /^ */.exec(line.text)[0].length;
    const shift = !head && own < labelAt ? labelAt + 4 - own : 0;
    const row = head ? null : valueRow(line);

    if (row) {
      block.push(row);
    } else {
      endBlock();
    }

    if (head) {
      labelAt = head.labelAt;
      old = null;
      continue;
    }

    if (shift > 0) {
      ranges.push(
        Decoration.line({
          attributes: { style: `padding-left: calc(6px + ${shift}ch)` },
        }).range(line.from),
      );
    }

    const was = valueAt(line, OLD_VALUE);
    const is = valueAt(line, NEW_VALUE);

    if (was) {
      old = was;
    } else if (is && old) {
      ranges.push(...changes(old, is, removedMark), ...changes(is, old, addedMark));
      old = null;
    }
  }

  endBlock();
  return Decoration.set(ranges, true);
}

const layoutField = StateField.define({
  create: (state) => layout(state.doc),
  update: (value, transaction) => (transaction.docChanged ? layout(transaction.state.doc) : value),
  provide: (field) => EditorView.decorations.from(field),
});

/* ---------------------------------------------------------------- banners and marks */

class CallBanner extends WidgetType {
  constructor(call) {
    super();
    this.call = call;
  }

  eq(other) {
    return other.call === this.call;
  }

  toDOM() {
    const banner = document.createElement("div");

    banner.className = "tr-banner";
    banner.textContent = this.call;
    return banner;
  }
}

function banners(doc) {
  const builder = new RangeSetBuilder();

  for (let at = 1; at <= doc.lines; at++) {
    const line = doc.line(at);
    const call = headOf(line.text) && callOf(line.text);

    if (call) {
      builder.add(
        line.from,
        line.from,
        Decoration.widget({ widget: new CallBanner(call), block: true, side: -1 }),
      );
    }
  }

  return builder.finish();
}

const bannerField = StateField.define({
  create: (state) => banners(state.doc),
  update: (value, transaction) => (transaction.docChanged ? banners(transaction.state.doc) : value),
  provide: (field) => EditorView.decorations.from(field),
});

const sideMark = new (class extends GutterMarker {
  toDOM() {
    const mark = document.createElement("span");

    mark.className = "tr-side-mark";
    mark.textContent = "◆";
    mark.title = "Side effect on a global unknown";
    return mark;
  }
})();

const sideGutter = gutter({
  class: "tr-side-gutter",
  lineMarker: (view, line) =>
    headOf(view.state.doc.sliceString(line.from, line.to))?.kind === "side" ? sideMark : null,
  initialSpacer: () => sideMark,
});

/* ---------------------------------------------------------------- current lines */

const setCurrent = StateEffect.define();

const currentLine = Decoration.line({ class: "tr-current" });

const currentField = StateField.define({
  create: () => Decoration.none,
  update(value, transaction) {
    for (const effect of transaction.effects) {
      if (effect.is(setCurrent)) {
        const { doc } = transaction.state;
        const builder = new RangeSetBuilder();

        if (effect.value) {
          for (let at = effect.value.first; at <= effect.value.last; at++) {
            builder.add(doc.line(at).from, doc.line(at).from, currentLine);
          }
        }

        return builder.finish();
      }
    }

    return transaction.docChanged ? Decoration.none : value;
  },
  provide: (field) => EditorView.decorations.from(field),
});

/* ---------------------------------------------------------------- view */

/*
 * [onLine] receives the number of a clicked line, unless the click selected text.
 * The returned view shows [setText]'s text, and [show] marks lines [first]..[last] as
 * current (by default [first] and the value lines that continue it) and centers the first one's label in both directions, unfolding it if needed;
 * [show(null)] marks none and returns to the top.
 */
export function createTraceView(parent, { label, onLine = null }) {
  const view = new EditorView({
    parent,
    extensions: [
      highlightSpecialChars(),
      EditorState.readOnly.of(true),
      EditorView.editable.of(false),
      EditorView.contentAttributes.of({ "aria-label": label, tabindex: "0" }),
      StreamLanguage.define(traceParser),
      syntaxHighlighting(traceHighlight),
      lineNumbers(),
      codeFolding(),
      foldGutter(),
      foldByDepth,
      sideGutter,
      bannerField,
      layoutField,
      currentField,
      EditorView.domEventHandlers({
        click(event, clicked) {
          if (!onLine || !clicked.state.selection.main.empty) {
            return false;
          }

          const pos = clicked.posAtCoords({ x: event.clientX, y: event.clientY });

          if (pos !== null) {
            onLine(clicked.state.doc.lineAt(pos).number);
          }

          return false;
        },
      }),
    ],
  });

  /*
   * Centers [at] in the view's own scroller. EditorView.scrollIntoView would also
   * scroll the page to the view, which pulls a reader back on every replay step.
   */
  function centerInPane(at, again = true) {
    view.requestMeasure({
      read() {
        const scroller = view.scrollDOM;
        const block = view.lineBlockAt(at);
        const coords = view.coordsAtPos(at);
        const box = scroller.getBoundingClientRect();

        return {
          top: block.top - (scroller.clientHeight - block.height) / 2,
          left: coords && coords.left - box.left + scroller.scrollLeft - scroller.clientWidth / 2,
        };
      },
      write({ top, left }) {
        view.scrollDOM.scrollTo({
          top: Math.max(0, top),
          left: left === null ? view.scrollDOM.scrollLeft : Math.max(0, left),
        });

        /* A line off screen has no coordinates until the scroll above renders it. */
        if (left === null && again) {
          centerInPane(at, false);
        }
      },
    });
  }

  return {
    view,

    setText(text) {
      view.dispatch({
        changes: { from: 0, to: view.state.doc.length, insert: text },
        effects: setCurrent.of(null),
        selection: { anchor: 0 },
        scrollIntoView: true,
      });
    },

    show(first, last) {
      if (first === null) {
        view.dispatch({ effects: setCurrent.of(null) });
        view.scrollDOM.scrollTo({ top: 0, left: 0 });
        return;
      }

      const { doc } = view.state;
      const line = doc.line(first);

      if (last === undefined) {
        last = first;

        while (last < doc.lines && !headOf(doc.line(last + 1).text) && doc.line(last + 1).text) {
          last++;
        }
      }

      const at = line.from + (headOf(line.text)?.labelAt ?? 0);
      const folds = [];

      foldedRanges(view.state).between(at, at, (from, to) => {
        folds.push(unfoldEffect.of({ from, to }));
      });

      view.dispatch({
        effects: [...folds, setCurrent.of({ first, last: Math.min(last, doc.lines) })],
      });
      centerInPane(at);
    },
  };
}
