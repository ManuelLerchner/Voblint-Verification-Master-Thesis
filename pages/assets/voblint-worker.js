/*
 * Voblint analysis worker.
 *
 * The generated wasm_of_ocaml analyzer lives entirely in this worker.
 * Parsing and analysis may block this worker, but never the browser UI.
 */

importScripts("./voblint_web.bc.wasm.js");


function waitForAnalyzer() {
  return new Promise((resolve, reject) => {
    const started = performance.now();

    function check() {
      if (typeof self.Voblint_run === "function") {
        resolve();
        return;
      }

      if (performance.now() - started > 10_000) {
        reject(
          new Error(
            "Voblint analyzer did not initialize.",
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