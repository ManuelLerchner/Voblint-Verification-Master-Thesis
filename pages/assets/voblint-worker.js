/*
 * Voblint analysis worker.
 *
 * The generated wasm_of_ocaml analyzer lives entirely in this worker.
 * Parsing and analysis may block this worker, but never the browser UI.
 */

/*
 * The loader instantiates its wasm modules asynchronously, and a failed download
 * surfaces only as an unhandled rejection here, never as an error the page sees.
 * Keep it so a failed start can name its cause.
 */
let loaderFailure = null;

self.addEventListener("unhandledrejection", (event) => {
  loaderFailure ??= event.reason;
});

importScripts("./voblint_web.bc.wasm.js");

/* Long enough for the wasm download on a slow mobile connection. */
const ANALYZER_START_TIMEOUT_MS = 60_000;

function waitForAnalyzer() {
  return new Promise((resolve, reject) => {
    const started = performance.now();

    function check() {
      if (typeof self.Voblint_run === "function") {
        resolve();
        return;
      }

      if (loaderFailure !== null || performance.now() - started > ANALYZER_START_TIMEOUT_MS) {
        const cause = loaderFailure instanceof Error ? loaderFailure.message : loaderFailure;

        reject(
          new Error(
            cause
              ? `Voblint analyzer did not initialize: ${cause}`
              : "Voblint analyzer did not initialize.",
          ),
        );
        return;
      }

      setTimeout(check, 10);
    }

    check();
  });
}


const analyzerReady = waitForAnalyzer();


self.onmessage = async (event) => {
  const request = event.data;

  if (!request || request.type !== "run") {
    return;
  }

  try {
    await analyzerReady;

    const result = self.Voblint_run(
      request.analysis,
      request.globals,
      request.context,
      request.contextDepth,
      request.source,
    );

    if (typeof result !== "string") {
      throw new TypeError(
        `Voblint_run returned ${typeof result}; expected a JSON string.`,
      );
    }

    self.postMessage({
      type: "result",
      id: request.id,
      result,
    });
  } catch (error) {
    if (error instanceof Error) {
      self.postMessage({
        type: "error",
        id: request.id,
        name: error.name,
        message: error.message,
        stack: error.stack ?? null,
      });
    } else {
      self.postMessage({
        type: "error",
        id: request.id,
        name: "Error",
        message: String(error),
        stack: null,
      });
    }
  }
};
