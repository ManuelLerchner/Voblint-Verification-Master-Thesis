"""Build the slides and their timed speaker notes.

Warnings fail the build, as for the thesis: a missing font or an overflowing
box must not reach the published deck.
"""

import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "build/presentation"
TALK_SECONDS = 20 * 60


def typst(*args):
    # Roboto comes from the pixi environment, so the deck renders the same on
    # every machine; system fonts would differ between a Mac and CI.
    conda = os.environ.get("CONDA_PREFIX")
    if not conda:
        sys.exit("build.py: run through `pixi run slides`, which provides the fonts")
    fonts = ["--font-path", "thesis/assets/fonts", "--font-path", f"{conda}/fonts"]
    command = [
        "typst",
        *args[:1],
        "--root",
        "thesis",
        "--ignore-system-fonts",
        *fonts,
        *args[1:],
    ]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if result.returncode != 0 or "warning:" in result.stderr:
        sys.exit(result.stderr)
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
        for key in ("text", "children", "body", "child"):
            if key in value:
                return plain(value[key])
        return ""
    return ""


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    source = "thesis/presentation/slides.typ"
    typst("compile", source, str(OUT / "voblint-slides.pdf"))
    slides = json.loads(
        typst("eval", "--in", source, "query(<talk-slide>).map(it => it.value)")
    )
    main_talk = [s for s in slides if s["id"] < 100]
    if [s["id"] for s in main_talk] != list(range(1, len(main_talk) + 1)):
        sys.exit("build.py: main slides must be numbered 1, 2, ... in order")
    total = sum(s["seconds"] for s in main_talk)
    if total > TALK_SECONDS:
        sys.exit(f"build.py: main talk runs {total} s, over {TALK_SECONDS} s")
    notes = []
    elapsed = 0
    for s in slides:
        start = f"{elapsed // 60}:{elapsed % 60:02}"
        elapsed += s["seconds"]
        end = f"{elapsed // 60}:{elapsed % 60:02}"
        label = s["id"] if s["id"] < 100 else "Backup"
        notes.append(
            f"{label}. {plain(s['title'])} ({start}–{end}; {s['seconds']} s)\n"
            f"{plain(s['notes']).strip()}\n"
        )
    (OUT / "speaker-notes.txt").write_text("\n".join(notes))
    print(
        f"Built {len(main_talk)} main slides, {len(slides) - len(main_talk)} backup;"
        f" main talk {total // 60}:{total % 60:02}. Outputs: {OUT}"
    )


if __name__ == "__main__":
    main()
