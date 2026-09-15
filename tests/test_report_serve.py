"""Serving a report must preserve the output of the user's analysis."""

import os
import shutil
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent


@pytest.mark.parametrize("custom", [False, True])
def test_serve_preserves_existing_report(tmp_path, custom):
    script = tmp_path / "scripts/mk/report.sh"
    script.parent.mkdir(parents=True)
    shutil.copyfile(REPO / "scripts/mk/report.sh", script)
    report = tmp_path / ("custom report" if custom else "build/report")
    report.mkdir(parents=True)
    contents = {"index.xml": b"original analysis", "keep.txt": b"user data"}
    for name, data in contents.items():
        (report / name).write_bytes(data)

    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    python = bin_dir / "python3"
    python.write_text('#!/bin/sh\nprintf "%s\\n" "$@"\n')
    python.chmod(0o755)
    env = dict(
        os.environ, PATH=f"{bin_dir}:{os.environ['PATH']}", NO_OPEN="1", PORT="9123"
    )
    env.pop("OUTDIR", None)
    args = [str(report)] if custom else []
    result = subprocess.run(
        ["bash", str(script), *args], env=env, capture_output=True, text=True
    )

    assert result.returncode == 0, result.stderr
    assert result.stdout.splitlines()[-5:] == [
        "-m",
        "http.server",
        "--directory",
        str(report),
        "9123",
    ]
    assert {p.name: p.read_bytes() for p in report.iterdir()} == contents


def test_missing_report_fails_without_creating_output(tmp_path):
    report = tmp_path / "missing"
    result = subprocess.run(
        ["bash", str(REPO / "scripts/mk/report.sh"), str(report)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 1
    assert "Generate one with voblint --html first" in result.stderr
    assert not report.exists()
