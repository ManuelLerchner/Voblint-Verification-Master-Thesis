"""Build the slides, timed speaker notes, and an offline replay companion."""

import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "build/presentation"


def run(*args):
    result = subprocess.run(args, cwd=ROOT, check=True, capture_output=True, text=True)
    if result.stderr.strip():
        raise RuntimeError(result.stderr)
    return result.stdout


def plain(value):
    if isinstance(value, str):
        return value
    if isinstance(value, list):
        return "".join(map(plain, value))
    if isinstance(value, dict):
        if value.get("func") == "smartquote":
            return '"' if value.get("double", True) else "'"
        if value.get("func") == "space":
            return " "
        if value.get("func") in {"parbreak", "linebreak"}:
            return "\n"
        return plain(value.get("text", value.get("children", value.get("body", ""))))
    return ""


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    options = ["--root", "thesis", "--font-path", "thesis/assets/fonts"]
    source = "thesis/presentation/slides.typ"
    run("typst", "compile", *options, source, str(OUT / "voblint-slides.pdf"))
    slides = json.loads(
        run(
            "typst",
            "eval",
            *options,
            "--in",
            source,
            "query(<talk-slide>).map(it => it.value)",
        )
    )
    if sum(s["seconds"] for s in slides) != 1200:
        raise ValueError("Main talk must total 20 minutes")
    if [s["id"] for s in slides] != list(range(1, 25)):
        raise ValueError("Expected 20 main slides and four backups")
    notes = []
    elapsed = 0
    for s in slides:
        start = f"{elapsed // 60}:{elapsed % 60:02}"
        elapsed += s["seconds"]
        end = f"{elapsed // 60}:{elapsed % 60:02}"
        notes.append(
            f"{s['id']}. {plain(s['title'])} ({start}–{end}; {s['seconds']} seconds)\n"
            f"{plain(s['notes'])}\n"
        )
    (OUT / "speaker-notes.txt").write_text("\n".join(notes))
    shutil.copyfile(ROOT / "docs/images/solve-replay.gif", OUT / "solve-replay.gif")
    media = '<img src="solve-replay.gif" alt="Solver replay">'
    if shutil.which("ffmpeg"):
        run(
            "ffmpeg",
            "-v",
            "error",
            "-y",
            "-i",
            str(OUT / "solve-replay.gif"),
            "-vf",
            "pad=ceil(iw/2)*2:ceil(ih/2)*2",
            "-pix_fmt",
            "yuv420p",
            "-movflags",
            "+faststart",
            str(OUT / "solve-replay.mp4"),
        )
        media = (
            '<video controls src="solve-replay.mp4" aria-label="Solver replay"></video>'
        )
    (OUT / "replay.html").write_text(
        """<!doctype html>
<html lang="en"><meta charset="utf-8"><title>Voblint solver replay</title>
<style>body{font:20px sans-serif;margin:24px;color:#222}img,video{max-width:100%;
max-height:85vh}a{color:#0065bd}</style>
<h1>Voblint solver replay</h1>
<p>Interval · entry-state contexts · bump(5) and bump(4)</p>
<p>Animated demonstration; the PDF contains a static fallback.</p>
MEDIA
</html>""".replace("MEDIA", media)
    )
    print(f"Built {len(slides)} slides; main talk 20:00. Outputs: {OUT}")


if __name__ == "__main__":
    main()
