/*
 * Calls the browser analyzer under Node, as the playground's worker does.
 *
 * Preloaded ahead of the wasm_of_ocaml loader, which must run as the main
 * module because it finds its assets next to require.main:
 *
 *   VOBLINT_WEB_CALLS='[["interval","warrow","none",0,"fixpoint","fun main() {}",false]]' \
 *     node --require tests/voblint_web_calls.cjs build/browser/voblint_web.bc.wasm.js
 *
 * Every call runs in this one process, in order, so state one run leaves in
 * the module reaches the next as it would in a page session. Prints the
 * answers as one JSON array of strings.
 */

const calls = JSON.parse(process.env.VOBLINT_WEB_CALLS ?? "[]");
const START_TIMEOUT_MS = 30_000;
const started = Date.now();

const poll = setInterval(() => {
  if (typeof globalThis.Voblint_run === "function") {
    clearInterval(poll);
    process.stdout.write(JSON.stringify(calls.map((args) => globalThis.Voblint_run(...args))));
  } else if (Date.now() - started > START_TIMEOUT_MS) {
    clearInterval(poll);
    process.stderr.write("voblint_web did not initialize\n");
    process.exitCode = 1;
  }
}, 10);
