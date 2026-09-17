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

function highlight(block) {
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

const blocks = [...document.querySelectorAll("[data-lang]")];

for (const block of blocks) {
  highlight(block);
}

/*
 * A figure that swaps its own program in -- the recursion spiral has two --
 * writes plain text over the spans, so the block is coloured again afterwards.
 * The observer is off while that happens, or it would answer its own writes.
 */
if ("MutationObserver" in window) {
  const observer = new MutationObserver((records) => {
    const touched = new Set(
      records
        .map((record) => record.target)
        .map((node) => (node.closest ? node : node.parentElement)),
    );

    observer.disconnect();

    for (const node of touched) {
      const block = node?.closest("[data-lang]");

      if (block) {
        highlight(block);
      }
    }

    for (const block of blocks) {
      observer.observe(block, { childList: true, subtree: true, characterData: true });
    }
  });

  for (const block of blocks) {
    observer.observe(block, { childList: true, subtree: true, characterData: true });
  }
}
