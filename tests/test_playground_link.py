"""Links scripts/playground_link.py writes for documentation, in the encoding the
playground's Share button reads back."""

import base64
import sys
import zlib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import playground_link  # noqa: E402


def unpack(packed: str) -> str:
    padded = packed + "=" * (-len(packed) % 4)
    return zlib.decompress(base64.urlsafe_b64decode(padded), wbits=-15).decode()


def test_source_survives_the_fragment_encoding():
    source = "fun main() {\n  x = 1 / 0; // ⚠ ∅\n  __voblint_check(x == 0);\n}\n"
    packed = playground_link.pack_source(source)
    assert "=" not in packed and "+" not in packed and "/" not in packed
    assert unpack(packed) == source


def test_settings_go_in_the_query_and_the_program_in_the_fragment():
    url = playground_link.link("fun main() {}", "interval", context="call-string", k=2)
    base, fragment = url.split("#code=")
    assert base.endswith(
        "playground.html?analysis=interval&globals=warrow&context=call-string&k=2"
    )
    assert unpack(fragment) == "fun main() {}"


def test_flags_in_any_order_override_the_header(tmp_path):
    program = tmp_path / "prog.vimp"
    program.write_text(
        "// PARAM: --analysis sign --context entry-state\nfun main() {}\n"
    )
    path, flags, _, open_browser = playground_link.parse_command_line(
        ["--globals", "join", str(program), "--open"]
    )
    url = playground_link.program_link(path, flags)
    assert open_browser
    assert "?analysis=sign&globals=join&context=entry-state#" in url
    assert unpack(url.split("#code=")[1]) == "fun main() {}\n"


def test_a_program_without_header_keeps_its_first_line(tmp_path):
    program = tmp_path / "prog.vimp"
    program.write_text("// my own comment\nfun main() {}\n")
    url = playground_link.program_link(program, ["--analysis", "interval"])
    assert unpack(url.split("#code=")[1]).startswith("// my own comment")
