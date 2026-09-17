/*
 * Colours the page's code snippets.
 *
 * A snippet says what it is in `data-lang`, because nothing else can tell:
 * zoom-code carries a VIMP program in one place and an Isabelle lemma in
 * another, and an inline `code` holds a program fragment in one column of the
 * globals table and an abstract value in the next. The tokens come from
 * code-tokens.js, which the playground's editor also reads, so a keyword is the
 * same colour in both.
 *
 * Only text is rewritten. The hand-written spans inside a snippet -- the per
 * line verdict markers, and the margin notes and badges that are prose rather
 * than code -- are left exactly as they are.
 */

import { tokenize } from "./code-tokens.js";

/* Inside these, the text is commentary about the code, not code. */
const NOT_CODE = ".mh, .mb, .zoom-badge, .bad-hint, .dim";

function highlightTextNode(node, language) {
  const runs = tokenize(language, node.nodeValue);

  if (runs.length <= 1 && !runs[0]?.type) {
    return;
  }

  const fragment = document.createDocumentFragment();

  for (const run of runs) {
    if (!run.type) {
      fragment.append(run.text);
      continue;
    }

    const span = document.createElement("span");

    span.className = `tok-${run.type}`;
    span.textContent = run.text;
    fragment.append(span);
  }

  node.replaceWith(fragment);
}

for (const block of document.querySelectorAll("pre[data-lang], code[data-lang]")) {
  const language = block.dataset.lang;
  const walker = document.createTreeWalker(block, NodeFilter.SHOW_TEXT, {
    acceptNode(node) {
      if (!node.nodeValue.trim()) {
        return NodeFilter.FILTER_REJECT;
      }

      return node.parentElement.closest(NOT_CODE)
        ? NodeFilter.FILTER_REJECT
        : NodeFilter.FILTER_ACCEPT;
    },
  });

  /* Collected first: replacing a node while walking would drop the rest. */
  const nodes = [];

  while (walker.nextNode()) {
    nodes.push(walker.currentNode);
  }

  for (const node of nodes) {
    highlightTextNode(node, language);
  }
}
