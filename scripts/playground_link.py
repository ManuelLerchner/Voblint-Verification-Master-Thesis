#!/usr/bin/env python3
"""A playground link that opens a VIMP program with chosen settings.

Encodes the program the way the playground's Share button does: raw deflate,
base64url without padding, in the `#code=` fragment, with the settings in the
query. Documentation links built here reproduce exactly the program they show.

Takes voblint's own analysis flags, read by the same reader tests/run.py uses;
a setting the command line leaves out comes from the file's `// PARAM:` header
when it has one. The header and any regression bookkeeping stay out of the link,
as they do in the playground's example browser. `pixi run voblint FILE --playground` runs this with --open.

    python3 scripts/playground_link.py program.vimp --analysis interval --context entry-state
    python3 scripts/playground_link.py --open tests/regression/02-control-flow/precision/02-while_loop.vimp
"""

from __future__ import annotations

import base64
import sys
import webbrowser
import zlib
from pathlib import Path
from urllib.parse import quote

import vimp_fixture

PLAYGROUND = "https://manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html"


def pack_source(source: str) -> str:
    """Raw deflate (no zlib header), as the browser's CompressionStream("deflate-raw")."""
    compressor = zlib.compressobj(9, zlib.DEFLATED, -15)
    deflated = compressor.compress(source.encode()) + compressor.flush()
    return base64.urlsafe_b64encode(deflated).decode().rstrip("=")


def link(
    source: str,
    analysis: str,
    globals_rule: str = "warrow",
    context: str = "none",
    k: int | None = None,
    base: str = PLAYGROUND,
) -> str:
    settings = [("analysis", analysis), ("globals", globals_rule), ("context", context)]
    if k is not None:
        settings.append(("k", str(k)))
    query = "&".join(f"{key}={quote(value)}" for key, value in settings)
    return f"{base}?{query}#code={pack_source(source)}"


def parse_command_line(argv: list[str]) -> tuple[Path, list[str], str, bool]:
    """The program, its voblint flags, the playground base, and whether to open it.

    Flags and the program may come in any order, as voblint accepts them.
    """
    program: Path | None = None
    flags: list[str] = []
    base = PLAYGROUND
    open_browser = False
    tokens = list(argv)

    while tokens:
        token = tokens.pop(0)

        if token == "--open":
            open_browser = True
        elif token == "--base" and tokens:
            base = tokens.pop(0)
        elif token in vimp_fixture.SETTING_FLAGS or token in vimp_fixture.RUNNER_FLAGS:
            flags.append(token)
            if tokens:
                flags.append(tokens.pop(0))
        elif token.startswith("-"):
            flags.append(token)
        elif program is None:
            program = Path(token)
        else:
            raise ValueError(f"more than one program given: {program} and {token}")

    if program is None:
        raise ValueError("no .vimp program given")

    return program, flags, base, open_browser


def program_link(program: Path, flags: list[str], base: str = PLAYGROUND) -> str:
    """The link for a program: command-line settings over its header's."""
    header = vimp_fixture.param_args(program) or []
    settings = vimp_fixture.analysis_settings(header) | vimp_fixture.analysis_settings(
        flags
    )

    if "analyses" not in settings:
        raise ValueError(
            f"{program}: no --analysis given and no // PARAM: header names one"
        )

    return link(
        vimp_fixture.shown_source(program.read_text()),
        settings["analyses"][0],
        settings.get("globals", "warrow"),
        settings.get("context", "none"),
        settings.get("context_depth"),
        base,
    )


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv

    if {"-h", "--help"} & set(argv):
        print(__doc__)
        return 0

    try:
        program, flags, base, open_browser = parse_command_line(argv)
        url = program_link(program, flags, base)
    except (OSError, ValueError) as error:
        print(f"playground_link: {error}", file=sys.stderr)
        return 2

    print(url)

    if open_browser and not webbrowser.open(url):
        print(
            "playground_link: no browser to open; copy the link above", file=sys.stderr
        )

    return 0


if __name__ == "__main__":
    sys.exit(main())
