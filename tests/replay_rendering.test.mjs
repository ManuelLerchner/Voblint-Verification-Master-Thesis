// Use the playground's Cytoscape version without building the analyzer:
// npm install --prefix build/replay-test --no-save cytoscape@3.34.3
// node --test tests/replay_rendering.test.mjs
// CYTOSCAPE_MODULE may point to an already downloaded copy of the same version.
import assert from "node:assert/strict";
import { resolve } from "node:path";
import { test } from "node:test";
import { pathToFileURL } from "node:url";
import { replayStyle } from "../pages/replay-style.js";

const { default: cytoscape } = await import(pathToFileURL(resolve(
  process.env.CYTOSCAPE_MODULE ?? "build/replay-test/node_modules/cytoscape/dist/cytoscape.esm.mjs",
)));
assert.equal(cytoscape.version, "3.34.3");

for (const [classes, width] of [["r-infl", 1.5], ["r-event r-active", 4], ["", 3]]) {
  test(`pressing a replay edge adds no broad overlay: ${classes || "CFG"}`, () => {
    const cy = cytoscape({
      headless: true, styleEnabled: true,
      style: replayStyle(() => "#123456"),
      elements: [{data: {id: "global"}}, {data: {id: "reader"}},
        {data: {id: "edge", source: "global", target: "reader"}, classes}],
    });
    try {
      const edge = cy.getElementById("edge");
      // Geometry is immaterial to stroke thickness; exercise the actual canvas
      // renderer with a recording context, without a DOM or a browser.
      edge._private.rscratch.allpts = [0, 0, 400, 250];
      edge._private.rscratch.edgeType = "straight";
      const renderer = Object.create(cytoscape("renderer", "canvas").prototype);
      renderer.usePaths = () => false;
      const strokes = [];
      const context = {
        beginPath() {}, moveTo() {}, lineTo() {}, setLineDash() {},
        stroke() { strokes.push(this.lineWidth); },
      };
      for (const pressed of [false, true, false]) {
        pressed ? edge.activate() : edge.unactivate();
        renderer.drawEdgeOverlay(context, edge);
        assert.equal(edge.numericStyle("width"), width);
        assert.deepEqual(strokes, [], "pointer activation must not draw the default 20px grey band");
      }
    } finally {
      cy.destroy();
    }
  });
}
