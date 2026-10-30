#!/usr/bin/env node
// Run pages-dev first; uses the same Playwright installation as the figure capture.
// Sample each entity kind, interpretation links, generic links, and thesis links.
import assert from "node:assert/strict";
import { readFileSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const { chromium } = createRequire(join(root, "build/capture/package.json"))("playwright-core");
const seed = Number(process.env.LINK_SAMPLE_SEED || 20261030);
const count = Number(process.env.LINK_SAMPLE_SIZE || 10);
assert(Number.isInteger(seed) && seed >= 0, "LINK_SAMPLE_SEED must be a nonnegative integer");
assert(Number.isInteger(count) && count > 0, "LINK_SAMPLE_SIZE must be a positive integer");
let random = seed >>> 0;
function sample(items) {
  const shuffled = [...items];
  for (let i = shuffled.length - 1; i > 0; i--) {
    random = (Math.imul(1664525, random) + 1013904223) >>> 0;
    const j = random % (i + 1);
    [shuffled[i], shuffled[j]] = [shuffled[j], shuffled[i]];
  }
  return shuffled.slice(0, count);
}

const browser = await chromium.launch(
  process.env.CHROME_PATH ? { executablePath: process.env.CHROME_PATH } : { channel: "chrome" },
);
const report = { seed, count, checked: [], failures: [] };
try {
  const page = await browser.newPage({
    viewport: { width: 1600, height: 1100 },
    reducedMotion: "reduce",
  });
  const target = await browser.newPage();
  page.on("pageerror", (error) => report.failures.push(error.message));
  const base = process.env.PROOF_MAP_BASE || "http://localhost:8000";
  await page.goto(`${base}/proof-map.html?view=treemap`);
  await page.locator("#wheel[data-layout=treemap][data-animating=false]").waitFor();
  const data = await (await page.request.get(`${base}/assets/proof-map.json`)).json();
  const buckets = ["thm", "const", "type", "locale"].map((kind) =>
    sample(data.nodes.filter((n) => n[0].startsWith(`${kind}:`))),
  );
  buckets.push(sample(data.nodes.filter((n) => data.locations[n[0]]?.kind === "interpretation")));
  buckets.push(sample(data.nodes.filter((n) => data.locations[n[0]]?.generic !== undefined)));
  buckets.push(sample(data.nodes.filter((n) => !n[4])));
  const selected = new Map(buckets.flat().map((n) => [n[0], n]));
  const regression = "thm:Interval_Analyses.interval_rule.verdict_report_def";
  selected.set(
    regression,
    data.nodes.find((n) => n[0] === regression),
  );

  async function inspect(url, id, expected) {
    const response = await target.goto(url);
    assert(response === null || response.ok(), `${url}: HTTP ${response?.status()}`);
    const landing = await target.evaluate(() => {
      const anchor = decodeURIComponent(location.hash.slice(1));
      if (!anchor) return { anchor: "", command: "", text: "", visible: true };
      const element = document.getElementById(anchor);
      if (!element) return null;
      const commands = [...document.querySelectorAll(".command")];
      const command = commands.findLast(
        (c) =>
          c.contains(element) ||
          c.compareDocumentPosition(element) & Node.DOCUMENT_POSITION_FOLLOWING,
      );
      const range = document.createRange();
      if (command) {
        range.setStartBefore(command);
        const next = commands[commands.indexOf(command) + 1];
        if (next) range.setEndBefore(next);
        else range.setEndAfter(document.body.lastChild);
      }
      const box = element.getBoundingClientRect();
      return {
        anchor,
        command: command?.textContent.trim(),
        text: command ? range.toString() : element.textContent,
        visible: box.bottom >= 0 && box.top < innerHeight && box.height > 0,
      };
    });
    assert(landing, `${id}: missing anchor in ${url}`);
    if (!id.startsWith("thesis:") && expected !== "theory") {
      const kind = id.slice(0, id.indexOf(":"));
      const name = id.slice(id.indexOf(":") + 1);
      assert.equal(
        landing.anchor,
        `${name}|${kind === "thm" ? "fact" : kind}`,
        `${id}: link changed entity identity`,
      );
    }
    assert(landing.visible, `${id}: browser did not scroll to the anchor`);
    const interpreted = [
      "global_interpretation",
      "interpretation",
      "interpret",
      "sublocale",
    ].includes(landing.command);
    assert.equal(interpreted, expected === "interpretation", `${id}: landed on ${landing.command}`);
    if (expected === "generic") {
      const name = id.split(".").at(-1).replace(/_def$/, "");
      assert(landing.text.includes(name), `${id}: generic source does not display ${name}`);
    }
    report.checked.push({
      id,
      url,
      expected,
      command: landing.command,
      excerpt: landing.text.slice(0, 200),
    });
  }

  for (const [id, node] of selected) {
    try {
      assert(node, `Missing regression entity ${id}`);
      const [kind, name] = [id.split(":")[0], id.slice(id.indexOf(":") + 1)];
      await page.locator("#kind").selectOption(kind);
      await page.locator("#search").fill(name);
      const label = name.split(".").slice(1).join(".");
      const button = page.locator("#results button").filter({ hasText: label });
      await button.first().waitFor();
      // A full name may also prefix a generated fact; require the exact label.
      await page.locator("#results button").evaluateAll((buttons, wanted) => {
        const found = buttons.find((b) => b.firstChild.textContent === wanted);
        if (!found) throw new Error(`Missing result ${wanted}`);
        found.click();
      }, label);
      assert.equal(await page.locator("#selection h2").textContent(), name);
      const links = await page
        .locator("#selection > a")
        .evaluateAll((items) => items.map((a) => ({ text: a.textContent, href: a.href })));
      const location = data.locations[id];
      const expected = location?.kind || (node[4] ? "source" : "theory");
      assert(
        links[0].text.includes(
          expected === "interpretation"
            ? "interpretation"
            : expected === "theory"
              ? "containing theory"
              : "source command",
        ),
      );
      await inspect(links[0].href, id, expected);
      if (location?.generic !== undefined) {
        assert.equal(links.length, 2);
        await inspect(links[1].href, data.nodes[location.generic][0], "generic");
      } else assert.equal(links.length, 1);
      if (id === regression)
        await page.screenshot({ path: join(root, "build/proof-map-link-selection.png") });
    } catch (error) {
      report.failures.push(`${id}: ${error.message}`);
    }
  }
  const thesis = JSON.parse(readFileSync(join(root, "thesis/shared/generated/links.json")));
  for (const [id, path] of sample(
    Object.entries(thesis.links).filter(([, path]) => path.includes("#")),
  )) {
    try {
      await inspect(new URL(path, thesis.base).href, `thesis:${id}`, "source");
    } catch (error) {
      report.failures.push(`${id}: ${error.message}`);
    }
  }
} finally {
  await browser.close();
  writeFileSync(
    join(root, "build/proof-map-link-audit.json"),
    `${JSON.stringify(report, null, 2)}\n`,
  );
}
console.log(
  `Seed ${seed}: checked ${report.checked.length} link landings; ${report.failures.length} failures. Report: build/proof-map-link-audit.json`,
);
assert.deepEqual(report.failures, []);
