/*
 * What a token is in the two languages this site shows, read one way by every
 * consumer.
 *
 * The playground's editor feeds `vimpStreamParser` to CodeMirror's
 * StreamLanguage; the explainer's static snippets go through `tokenize`, which
 * runs the same VIMP rules over a small stand-in for CodeMirror's StringStream.
 * Neither can colour a keyword the other calls a name.
 *
 * Isabelle has no editor here, only snippets, so it is a plain scanner rather
 * than a stream parser. It classifies enough to read: what a command is, what a
 * logical connective is, and what is neither.
 *
 * Token names are CodeMirror's own, so StreamLanguage maps them to tags without
 * a translation table here.
 */

export const vimpStreamParser = {
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

    if (stream.match(/^[(){}[\],;]/)) {
      return "punctuation";
    }

    /*
     * Always consume one character, including on malformed input.
     */
    stream.next();
    return null;
  },
};

/*
 * The part of CodeMirror's StringStream that the parser above uses. One line at
 * a time, because that is the unit StreamLanguage hands a stream parser.
 */
class LineStream {
  constructor(line) {
    this.string = line;
    this.pos = 0;
    this.start = 0;
  }

  eol() {
    return this.pos >= this.string.length;
  }

  next() {
    return this.pos < this.string.length ? this.string.charAt(this.pos++) : undefined;
  }

  eatSpace() {
    const from = this.pos;

    while (/[\s ]/.test(this.string.charAt(this.pos))) {
      this.pos += 1;
    }

    return this.pos > from;
  }

  skipToEnd() {
    this.pos = this.string.length;
  }

  skipTo(target) {
    const found = this.string.indexOf(target, this.pos);

    if (found < 0) {
      return false;
    }

    this.pos = found;
    return true;
  }

  match(pattern, consume = true) {
    if (typeof pattern === "string") {
      if (this.string.slice(this.pos, this.pos + pattern.length) !== pattern) {
        return false;
      }

      if (consume) {
        this.pos += pattern.length;
      }

      return true;
    }

    const found = this.string.slice(this.pos).match(pattern);

    if (found?.index !== 0) {
      return null;
    }

    if (consume) {
      this.pos += found[0].length;
    }

    return found;
  }

  current() {
    return this.string.slice(this.start, this.pos);
  }
}

/*
 * Runs of source paired with the token name that covers them, in order and
 * covering the whole string. A run with a null name is whitespace or a
 * character the parser does not classify.
 */
function tokenizeVimp(source) {
  const state = vimpStreamParser.startState();
  const runs = [];

  const push = (text, type) => {
    if (!text) {
      return;
    }

    const last = runs[runs.length - 1];

    if (last && last.type === type) {
      last.text += text;
    } else {
      runs.push({ text, type });
    }
  };

  const lines = source.split("\n");

  lines.forEach((line, index) => {
    const stream = new LineStream(line);

    /* A parser that consumed nothing would spin here, so bail out on one. */
    while (!stream.eol()) {
      stream.start = stream.pos;
      const type = vimpStreamParser.token(stream, state);

      if (stream.pos === stream.start) {
        stream.pos += 1;
      }

      push(stream.current(), type ?? null);
    }

    if (index < lines.length - 1) {
      push("\n", null);
    }
  });

  return runs;
}

/*
 * Isabelle as the snippets here use it: a command word, a logical symbol, a
 * bracket, a numeral, or a name. Enough structure to read a statement at a
 * glance, and no attempt at the real grammar.
 */
const ISABELLE_KEYWORDS = new Set([
  "and",
  "assumes",
  "by",
  "case",
  "corollary",
  "datatype",
  "definition",
  "do",
  "else",
  "fixes",
  "fun",
  "if",
  "in",
  "lemma",
  "let",
  "locale",
  "obtains",
  "of",
  "primrec",
  "proof",
  "qed",
  "shows",
  "then",
  "theorem",
  "theory",
  "type_synonym",
  "unfolding",
  "using",
  "where",
]);

/* Connectives, relations and the term-level arrows, all one colour. */
const ISABELLE_SYMBOLS = new Set([
  ..."\u27f9\u27f6\u27f7\u21a6\u21d2\u2192\u2200\u2203\u2208\u2209\u2286\u2282\u222a\u2229",
  ..."\u2294\u2293\u2291\u2264\u2265\u2260\u22a4\u22a5\u00ac\u2227\u2228\u03bb\u00d7\u2261",
  ..."=<>+-*/|&:\u2205",
]);

const ISABELLE_BRACKETS = new Set([..."()[]{}\u27e6\u27e7\u27e8\u27e9,;"]);

function tokenizeIsabelle(source) {
  const runs = [];

  const push = (text, type) => {
    if (!text) {
      return;
    }

    const last = runs[runs.length - 1];

    if (last && last.type === type) {
      last.text += text;
    } else {
      runs.push({ text, type });
    }
  };

  let i = 0;

  while (i < source.length) {
    const rest = source.slice(i);

    if (rest.startsWith("(*")) {
      const end = source.indexOf("*)", i + 2);
      const stop = end < 0 ? source.length : end + 2;
      push(source.slice(i, stop), "comment");
      i = stop;
      continue;
    }

    const space = rest.match(/^\s+/);

    if (space) {
      push(space[0], null);
      i += space[0].length;
      continue;
    }

    const string = rest.match(/^"[^"\n]*"/);

    if (string) {
      push(string[0], "variableName");
      i += string[0].length;
      continue;
    }

    /* A type variable reads as its own kind of name, not as a quoted string. */
    const typeVar = rest.match(/^'[A-Za-z][A-Za-z0-9_]*/);

    if (typeVar) {
      push(typeVar[0], "builtin");
      i += typeVar[0].length;
      continue;
    }

    const number = rest.match(/^\d+/);

    if (number) {
      push(number[0], "number");
      i += number[0].length;
      continue;
    }

    const word = rest.match(/^[A-Za-z_][A-Za-z0-9_.']*/);

    if (word) {
      /* Isabelle capitalizes datatype constructors, so Answer and QueryL read
         as the shape of a term while eqs and sigma read as names. */
      const kind = ISABELLE_KEYWORDS.has(word[0])
        ? "keyword"
        : /^[A-Z]/.test(word[0])
          ? "constructor"
          : "variableName";

      push(word[0], kind);
      i += word[0].length;
      continue;
    }

    const ch = source[i];

    if (ISABELLE_BRACKETS.has(ch)) {
      push(ch, "punctuation");
    } else if (ISABELLE_SYMBOLS.has(ch)) {
      push(ch, "operator");
    } else if (/[\u0370-\u03ff]/.test(ch)) {
      /* A Greek letter here names something -- gamma, sigma -- except the
         binder lambda, which ISABELLE_SYMBOLS already took. */
      push(ch, "variableName");
    } else {
      push(ch, null);
    }

    i += 1;
  }

  return runs;
}

/* The one entry point the page uses; an unknown language highlights nothing. */
export function tokenize(language, source) {
  if (language === "vimp") {
    return tokenizeVimp(source);
  }

  if (language === "isabelle") {
    return tokenizeIsabelle(source);
  }

  return [{ text: source, type: null }];
}
