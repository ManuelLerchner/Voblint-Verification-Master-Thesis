#!/usr/bin/env python3
"""Serve the Pages site from its sources and reload open tabs when they change.

pages-site-build copies every input into build/github-pages; this server reads
the same inputs in place, layered the way that copy layers them, so an edit to
pages/ shows up without a build. The wasm analyzer still comes from
browser-build, and a rebuild there reloads the tabs too.

Left out, since only the deployed site needs them: the repository figures
filled into the HTML (the pages keep their fallback text), the sitemap and the
PDFs.
"""

import argparse
import subprocess
import sys
import tempfile
import threading
import time
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import unquote, urlsplit

REPO = Path(__file__).resolve().parent.parent
RELOAD = "/__reload"
RELOAD_SCRIPT = (
    f'<script>new EventSource("{RELOAD}").onmessage = () => location.reload();</script>'
).encode()


class Layers:
    """The site's inputs, the later copy in pages-site.sh first."""

    def __init__(self, generated: Path):
        self.assets = [generated, REPO / "build/browser", REPO / "docs/images"]
        self.root = [REPO / "pages", REPO / "build/isabelle-html"]
        self.watched = [REPO / "pages", REPO / "docs/images", REPO / "build/browser"]

    def find(self, url_path: str) -> Path | None:
        relative = unquote(urlsplit(url_path).path).lstrip("/") or "index.html"
        candidates = [root / relative for root in self.root]

        if relative.startswith("assets/"):
            inner = relative.removeprefix("assets/")
            candidates = [root / inner for root in self.assets] + candidates

        for candidate in candidates:
            if candidate.is_dir():
                candidate = candidate / "index.html"

            # A request must stay inside its layer, whatever `..` it carries.
            if candidate.is_file() and any(
                candidate.resolve().is_relative_to(root.resolve())
                for root in self.assets + self.root
            ):
                return candidate

        return None

    def stamp(self) -> float:
        return max(
            (
                path.stat().st_mtime
                for root in self.watched
                if root.exists()
                for path in root.rglob("*")
            ),
            default=0.0,
        )


class Changes:
    """Counts changes to the watched inputs; reload streams wait on it."""

    def __init__(self, layers: Layers, interval: float):
        self.version = 0
        self.changed = threading.Condition()
        threading.Thread(
            target=self.watch, args=(layers, interval), daemon=True
        ).start()

    def watch(self, layers: Layers, interval: float):
        seen = layers.stamp()

        while True:
            time.sleep(interval)
            now = layers.stamp()

            if now != seen:
                seen = now

                with self.changed:
                    self.version += 1
                    self.changed.notify_all()

    def wait(self, version: int, timeout: float) -> int:
        with self.changed:
            self.changed.wait_for(lambda: self.version != version, timeout)
            return self.version


class Handler(SimpleHTTPRequestHandler):
    extensions_map = {
        **SimpleHTTPRequestHandler.extensions_map,
        ".wasm": "application/wasm",
    }

    def __init__(self, *args, layers: Layers, changes: Changes, **kwargs):
        self.layers = layers
        self.changes = changes
        super().__init__(*args, **kwargs)

    def end_headers(self):
        # Module scripts are cached hard otherwise, and a reload would show stale code.
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def translate_path(self, path):
        found = self.layers.find(path)
        return str(found) if found else str(REPO / "build/pages-dev/missing")

    def do_GET(self):
        if self.path == RELOAD:
            return self.stream_reloads()

        found = self.layers.find(self.path)

        if found is None or found.suffix != ".html":
            return super().do_GET()

        body = found.read_bytes()
        at = body.rfind(b"</body>")
        body = (
            body[:at] + RELOAD_SCRIPT + body[at:] if at >= 0 else body + RELOAD_SCRIPT
        )

        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def stream_reloads(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.end_headers()
        version = self.changes.version

        try:
            while True:
                now = self.changes.wait(version, timeout=15)
                # A comment line on a timeout keeps idle proxies and browsers connected.
                self.wfile.write(
                    b"data: reload\n\n" if now != version else b": idle\n\n"
                )
                self.wfile.flush()
                version = now
        except (BrokenPipeError, ConnectionResetError):
            pass

    def log_message(self, format, *args):
        if self.path != RELOAD:
            super().log_message(format, *args)


def generate(out: Path):
    for script, name in (
        ("pages_stats.py", "site-stats.js"),
        ("pages_examples.py", "regression-examples.json"),
    ):
        # Without one, the pages fall back to their neutral text or an empty example list.
        if subprocess.run(
            [sys.executable, REPO / "scripts" / script, "--out", out / name]
        ).returncode:
            print(
                f"pages-dev: {script} failed; serving without assets/{name}",
                file=sys.stderr,
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--port", type=int, default=8000)
    parser.add_argument(
        "--interval", type=float, default=0.5, help="seconds between change scans"
    )
    args = parser.parse_args()

    for missing in ("build/browser", "build/isabelle-html"):
        if not (REPO / missing).exists():
            print(
                f"pages-dev: {missing} is missing; the pages that need it will not load",
                file=sys.stderr,
            )

    with tempfile.TemporaryDirectory(prefix="voblint-pages-dev-") as generated:
        generate(Path(generated))
        layers = Layers(Path(generated))
        handler = partial(
            Handler, layers=layers, changes=Changes(layers, args.interval)
        )

        with ThreadingHTTPServer(("127.0.0.1", args.port), handler) as server:
            server.daemon_threads = True
            print(
                f"pages-dev: http://localhost:{args.port}/playground.html, reloading on changes"
            )

            try:
                server.serve_forever()
            except KeyboardInterrupt:
                pass


if __name__ == "__main__":
    main()
