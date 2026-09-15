#!/usr/bin/env node
/*
 * Regenerates the README's playground figures in docs/images.
 *
 * Each figure is a run of the browser playground on a program from
 * docs/readme-figures, opened through the same #code= link the README carries, so
 * the image, the program and the link cannot disagree. The script serves pages/ and
 * the WebAssembly build itself, drives Chrome through Playwright, and tiles the
 * editor, inspector and graph of each run into one tight image.
 *
 * Needs `pixi run browser-build` (the wasm analyzer), python3, a Chrome install,
 * and Playwright's core package, which the repository does not depend on. It is
 * installed under the ignored build/ directory, where this script looks for it:
 *
 *   npm install --no-save --prefix build/capture playwright-core
 *   node scripts/capture_readme_figures.mjs [figure-name]
 *
 * CHROME_PATH selects a browser binary other than the installed Chrome.
 */

import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { stat } from "node:fs/promises";
import { createServer } from "node:http";
import { createRequire } from "node:module";
import { dirname, extname, join, normalize } from "node:path";
import { fileURLToPath } from "node:url";

const REPO = join(dirname(fileURLToPath(import.meta.url)), "..");
const { chromium } = createRequire(join(REPO, "build/capture/package.json"))("playwright-core");
const PROGRAMS = join(REPO, "docs/readme-figures");
const OUT = join(REPO, "docs/images");
const only = process.argv[2];

/* The site layout scripts/mk/pages-site.sh assembles, later layers first. */
const LAYERS = [
  ["/assets/", join(REPO, "build/browser")],
  ["/assets/", join(REPO, "docs/images")],
  ["/", join(REPO, "pages")],
];

const TYPES = {
  ".css": "text/css",
  ".html": "text/html",
  ".js": "text/javascript",
  ".json": "application/json",
  ".mjs": "text/javascript",
  ".png": "image/png",
  ".svg": "image/svg+xml",
  ".wasm": "application/wasm",
};

async function resolve(urlPath) {
  for (const [prefix, root] of LAYERS) {
    if (!urlPath.startsWith(prefix)) {
      continue;
    }

    const file = join(root, normalize(urlPath.slice(prefix.length)));

    if (file.startsWith(root) && (await stat(file).catch(() => null))?.isFile()) {
      return file;
    }
  }

  return null;
}

const server = createServer(async (request, response) => {
  const file = await resolve(decodeURIComponent(new URL(request.url, "http://x").pathname));

  if (!file) {
    response.writeHead(404).end();
    return;
  }

  response.writeHead(200, { "content-type": TYPES[extname(file)] ?? "application/octet-stream" });
  response.end(readFileSync(file));
});

await new Promise((listening) => server.listen(0, "127.0.0.1", listening));

const BASE = `http://127.0.0.1:${server.address().port}/playground.html`;

/* The query and fragment of a README link to one of the figure programs. */
function programLink(name, ...settings) {
  return execFileSync("python3", [
    join(REPO, "scripts/playground_link.py"),
    join(PROGRAMS, `${name}.vimp`),
    ...settings,
    "--base",
    BASE,
  ])
    .toString()
    .trim()
    .split("playground.html?")[1];
}

const browser = await chromium.launch(
  process.env.CHROME_PATH ? { executablePath: process.env.CHROME_PATH } : { channel: "chrome" },
);
const context = await browser.newContext({ deviceScaleFactor: 2, acceptDownloads: true });

/*
 * Capture-only layout: short programs keep a short editor, and every panel shrinks
 * to its content so a figure carries no empty width.
 */
const CAPTURE_CSS = `
  #program-editor .cm-editor, #program-editor .cm-scroller { min-height: 0 !important; max-height: none !important; }
  .site-nav { position: static !important; }
  #open-examples, #share-link { display: none !important; }
  .analyzer-workspace { grid-template-areas: "editor" "controls" !important; grid-template-columns: max-content !important; }
  .analyzer-sidebar { width: 460px; }
  .editor-shell { width: max-content !important; min-width: 360px; }
  .state-inspector { width: max-content !important; }
  .state-inspector-body { grid-template-columns: repeat(auto-fit, minmax(300px, max-content)) !important; }
`;

async function run(query, width, fileName = "example.vimp") {
  const page = await context.newPage();

  page.on("pageerror", (error) => console.error("page error:", error.message));
  await page.setViewportSize({ width, height: 1000 });
  await page.goto(`${BASE}?${query}`);
  await page.addStyleTag({ content: CAPTURE_CSS });
  await page.waitForFunction(
    () =>
      document.querySelector("#analysis-graph canvas") &&
      !document.querySelector("#run-analysis").disabled,
    null,
    { timeout: 60000 },
  );
  await page.evaluate((name) => {
    document.querySelector("#editor-file").textContent = name;
  }, fileName);
  await page.waitForTimeout(600);

  return page;
}

/* Puts the cursor on the first line containing a fragment, so the inspector shows it. */
async function inspect(page, fragment) {
  const index = await page.$$eval(
    ".cm-line",
    (lines, text) => lines.findIndex((line) => line.textContent.includes(text)),
    fragment,
  );

  await page.click(`.cm-line:nth-child(${index + 1})`);
  await page.keyboard.press("End");
  await page.waitForTimeout(300);
  await page.mouse.move(0, 0);
}

async function shot(page, selector) {
  const element = await page.$(selector);

  await element.scrollIntoViewIfNeeded();

  return element.screenshot({ animations: "disabled" });
}

/* The whole graph, as the playground's Save PNG button exports it. */
async function graph(page) {
  const [download] = await Promise.all([
    page.waitForEvent("download"),
    page.click("#graph-save-image"),
  ]);

  return readFileSync(await download.path());
}

/*
 * Tiles captures on a CSS grid: `areas` is a grid-template-areas value and each cell
 * names its area. A cell marked `fit` is scaled to the height of the other cells, so
 * a tall graph beside short panels shrinks instead of leaving a gap.
 */
async function compose(name, cells, areas) {
  const page = await context.newPage();
  const figures = cells
    .map(
      ({ image, caption, area, fit }) =>
        `<figure style="grid-area:${area}"${fit ? " data-fit" : ""}>` +
        (caption ? `<figcaption>${caption}</figcaption>` : "") +
        `<img src="data:image/png;base64,${image.toString("base64")}"></figure>`,
    )
    .join("");

  await page.setContent(`<!doctype html><style>
    body { margin: 0; background: #f4f7f6; color: #174b57;
      font: 600 15px/1.3 ui-monospace, SFMono-Regular, Menlo, monospace; }
    #grid { display: inline-grid; grid-template-areas: ${areas}; gap: 14px; padding: 14px;
      align-items: start; justify-items: start; }
    figure { margin: 0; }
    figcaption { margin: 0 0 6px 2px; }
    img { display: block; }
  </style><div id="grid">${figures}</div>`);

  await page.evaluate(async () => {
    await Promise.all([...document.images].map((image) => image.decode()));

    for (const image of document.images) {
      image.style.width = `${image.naturalWidth / 2}px`;
    }

    const fitted = [...document.querySelectorAll("figure[data-fit]")];

    for (const figure of fitted) {
      figure.style.display = "none";
    }

    const height = document.querySelector("#grid").getBoundingClientRect().height - 28;

    for (const figure of fitted) {
      const caption = figure.querySelector("figcaption");
      const image = figure.querySelector("img");

      figure.style.display = "";
      image.style.width = "auto";
      image.style.height = `${height - (caption ? caption.getBoundingClientRect().height + 6 : 0)}px`;
    }
  });

  await (await page.$("#grid")).screenshot({ path: join(OUT, `${name}.png`) });
  await page.close();
}

const FIGURES = {
  async while_loop_cfg() {
    const page = await run(programLink("while-loop", "--analysis", "interval"), 900, "while-loop.vimp");

    await inspect(page, "__voblint_check");
    await compose(
      "while_loop_cfg",
      [
        { image: await shot(page, ".editor-shell"), area: "editor" },
        { image: await shot(page, ".state-inspector"), area: "inspector" },
        { image: await graph(page), area: "graph", fit: true },
      ],
      `"editor graph" "inspector graph"`,
    );
  },

  async "playground-overview"() {
    const page = await run("analysis=interval&globals=warrow&context=call-string&k=1", 1100);

    await inspect(page, "__voblint_check(i == 5)");
    await compose(
      "playground-overview",
      [
        { image: await shot(page, ".editor-shell"), area: "editor" },
        { image: await shot(page, "#analysis-problems"), area: "problems" },
        { image: await shot(page, ".state-inspector"), area: "inspector" },
        { image: await graph(page), area: "graph", fit: true },
      ],
      `"editor graph" "problems graph" "inspector graph"`,
    );
  },

  async "playground-contexts"() {
    const none = await run(programLink("contexts", "--analysis", "interval"), 900, "contexts.vimp");
    const noneEditor = await shot(none, ".editor-shell");
    const entry = await run(
      programLink("contexts", "--analysis", "interval", "--context", "entry-state"),
      900,
      "contexts.vimp",
    );

    await compose(
      "playground-contexts",
      [
        { image: noneEditor, caption: "--context none", area: "none" },
        { image: await shot(entry, ".editor-shell"), caption: "--context entry-state", area: "entry" },
        { image: await graph(entry), caption: "entry-state graph", area: "graph", fit: true },
      ],
      `"none graph" "entry graph"`,
    );
  },

  async "playground-int-refinement"() {
    const cells = [];

    for (const analysis of ["int", "interval", "sign", "parity"]) {
      const page = await run(programLink("int-refinement", "--analysis", analysis), 900, "int-refinement.vimp");

      cells.push({
        image: await shot(page, ".editor-shell"),
        caption: `--analysis ${analysis}`,
        area: analysis,
      });
      await page.close();
    }

    await compose("playground-int-refinement", cells, `"int interval" "sign parity"`);
  },

  async "playground-division-definite"() {
    const page = await run(programLink("division-definite", "--analysis", "interval"), 1100, "division-definite.vimp");

    await inspect(page, "7 % divisor");
    await compose(
      "playground-division-definite",
      [
        { image: await shot(page, ".editor-shell"), area: "editor" },
        { image: await shot(page, ".state-inspector"), area: "inspector" },
        { image: await shot(page, "#analysis-problems"), area: "problems" },
      ],
      `"editor problems" "inspector problems"`,
    );
  },

  async "playground-division-possible"() {
    const page = await run(programLink("division-possible", "--analysis", "interval"), 1100, "division-possible.vimp");

    await inspect(page, "7 / divisor");
    await compose(
      "playground-division-possible",
      [
        { image: await shot(page, ".editor-shell"), area: "editor" },
        { image: await shot(page, ".state-inspector"), area: "inspector" },
        { image: await shot(page, "#analysis-problems"), area: "problems" },
      ],
      `"editor problems" "inspector problems"`,
    );
  },
};

if (only && !Object.hasOwn(FIGURES, only)) {
  console.error(`unknown figure ${only}; one of: ${Object.keys(FIGURES).join(", ")}`);
  process.exitCode = 2;
} else {
  for (const [name, capture] of Object.entries(FIGURES)) {
    if (!only || only === name) {
      await capture();
      console.log(`captured docs/images/${name}.png`);
    }
  }
}

await browser.close();
server.close();
