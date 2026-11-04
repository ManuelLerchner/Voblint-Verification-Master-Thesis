import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from pages_profiling import fill_profiling

SOURCE = """<span data-meta="reps">recorded repetitions</span>
<span data-meta="timeout_s">recorded limit</span>
<li data-snapshot-summary>Metadata unavailable</li>"""


def snapshot(pages, filename="data/profiling/run.json"):
    directory = pages / "data/profiling"
    directory.mkdir(parents=True)
    (directory / "index.json").write_text(
        json.dumps({"snapshots": [{"label": "A < B", "file": filename}]})
    )
    (directory / "run.json").write_text(
        json.dumps(
            {
                "meta": {
                    "reps": 7,
                    "timeout_s": 12,
                    "date": "2026-10-21",
                    "commit": "abc123",
                    "device": {"cpu": "test CPU"},
                }
            }
        )
    )


def test_static_metadata_matches_snapshot_and_escapes_text(tmp_path):
    snapshot(tmp_path)
    result = fill_profiling(SOURCE, tmp_path)
    assert '<span data-meta="reps">7</span>' in result
    assert '<span data-meta="timeout_s">12 s</span>' in result
    assert "A &lt; B" in result
    assert "abc123 on test CPU" in result
    assert 'href="data/profiling/run.json"' in result
    assert fill_profiling(result, tmp_path) == result


def test_missing_index_preserves_readable_fallback(tmp_path):
    assert fill_profiling(SOURCE, tmp_path) == SOURCE


def test_empty_index_preserves_readable_fallback(tmp_path):
    snapshot(tmp_path)
    (tmp_path / "data/profiling/index.json").write_text('{"snapshots": []}')
    assert fill_profiling(SOURCE, tmp_path) == SOURCE


def test_rejects_snapshot_outside_site(tmp_path):
    snapshot(tmp_path, "../private.json")
    with pytest.raises(ValueError, match="inside the site"):
        fill_profiling(SOURCE, tmp_path)


def test_missing_snapshot_fails_instead_of_publishing_stale_metadata(tmp_path):
    snapshot(tmp_path, "data/profiling/missing.json")
    with pytest.raises(FileNotFoundError):
        fill_profiling(SOURCE, tmp_path)
