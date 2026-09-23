#!/usr/bin/env python3
"""Aggregate figures on AI assistance for the AI-use statement.

Reads the git history of ``main`` and ``writing`` and the local Claude Code
and Codex session logs of this project, and writes only counts to
``thesis/shared/generated/ai-use-stats.json``, which ``content/ai-use.typ``
renders. No prompt, message text, file content or identity leaves the logs.

The session logs exist only on the author's machine, so this script is a
manual snapshot and must not run in CI or in ``thesis-check``: the committed
JSON is the record. Claude Code prunes transcripts after about 30 days, so its
window is much shorter than the git history. ChatGPT (web) and Cursor keep no
local logs of this kind and are not counted.

    python3 thesis/tools/ai_use_stats.py
"""

from __future__ import annotations

import datetime as dt
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
OUT = REPO / "thesis" / "shared" / "generated" / "ai-use-stats.json"
HOME = Path.home()
# Claude Code keys projects by working directory; sessions started in a
# subdirectory or in the companion knowledge base get their own folder.
CLAUDE_PROJECTS = HOME / ".claude" / "projects"
CLAUDE_PREFIX = "-Users-manuellerchner-git-goblint-formalization"
CODEX_SESSIONS = HOME / ".codex" / "sessions"
CODEX_CWD = "/git/goblint-formalization"
BRANCHES = ["main", "writing"]

AI_TRAILER = re.compile(
    r"^\s*co-authored-by:\s*(claude|codex|chatgpt|gpt|openai|cursor|copilot)",
    re.I | re.M,
)
ISABELLE_BUILD = re.compile(r"isabelle\s+build|isabelle-build")
EDIT_TOOLS = {"Edit", "MultiEdit", "Write", "NotebookEdit"}
# Instruction files for the assistants; `.claude/CLAUDE.md` is a symlink to AGENTS.md
# since the two were unified, so its own history ends there.
RULE_FILES = [
    "AGENTS.md",
    ".claude/CLAUDE.md",
    "thesis/CLAUDE.md",
    "docs/ISABELLE_AGENT_NOTES.md",
]


def git_stats() -> dict:
    fmt = "%H%x1f%P%x1f%ad%x1f%B%x1e"
    out = subprocess.run(
        ["git", "log", *BRANCHES, f"--format={fmt}", "--date=format:%Y-%m"],
        cwd=REPO,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    commits = merges = assisted = 0
    months: Counter[str] = Counter()
    for record in filter(str.strip, out.split("\x1e")):
        _sha, parents, month, body = record.strip("\n").split("\x1f", 3)
        commits += 1
        merges += len(parents.split()) > 1
        months[month] += 1
        if AI_TRAILER.search(body):
            assisted += 1
    first, last = min(months), max(months)
    return {
        "commits": commits,
        "merges": merges,
        "ai_trailer": assisted,
        "first_month": first,
        "last_month": last,
    }


def rule_file_stats() -> dict:
    """Revisions of each instruction file, following renames, and their union."""
    per_file: dict[str, int] = {}
    union: set[str] = set()
    for path in RULE_FILES:
        shas = subprocess.run(
            ["git", "log", *BRANCHES, "--follow", "--format=%H", "--", path],
            cwd=REPO,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.split()
        per_file[path] = len(shas)
        union.update(shas)
    return {"per_file": per_file, "commits": len(union)}


def _records(path: Path):
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            try:
                yield json.loads(line)
            except json.JSONDecodeError:
                continue


def _text(content) -> str:
    if isinstance(content, str):
        return content
    return next((b.get("text", "") for b in content if b.get("type") == "text"), "")


def _is_human(record: dict) -> bool:
    """A prompt the author typed, as opposed to tool results, hooks and notices."""
    if (
        record.get("isMeta")
        or record.get("isCompactSummary")
        or "toolUseResult" in record
    ):
        return False
    origin = record.get("origin")
    if origin is not None:
        return origin.get("kind") == "human"
    # Older records carry no origin; slash commands and injected notices start with a tag.
    text = _text(record["message"]["content"]).lstrip()
    return bool(text) and not text.startswith("<")


def log_stats(paths: list[Path]) -> dict:
    sessions = assistant = human = 0
    tools: Counter[str] = Counter()
    isabelle_builds = 0
    stamps: list[str] = []
    for path in paths:
        message_ids: set[str] = set()
        tool_ids: set[str] = set()
        for record in _records(path):
            if stamp := record.get("timestamp"):
                stamps.append(stamp)
            kind = record.get("type")
            if kind == "user" and _is_human(record):
                human += 1
            if kind != "assistant":
                continue
            message = record.get("message", {})
            message_ids.add(message.get("id") or record.get("uuid"))
            for block in message.get("content", []):
                if block.get("type") != "tool_use" or block.get("id") in tool_ids:
                    continue
                tool_ids.add(block.get("id"))
                name = block.get("name", "")
                tools[name] += 1
                if name == "Bash" and ISABELLE_BUILD.search(
                    block.get("input", {}).get("command", "")
                ):
                    isabelle_builds += 1
        sessions += bool(message_ids)
        assistant += len(message_ids)
    mcp = sum(n for name, n in tools.items() if name.startswith("mcp__isabelle"))
    return {
        "sessions": sessions,
        "assistant_messages": assistant,
        "human_messages": human,
        "tool_calls": sum(tools.values()),
        "bash": tools["Bash"],
        "isabelle_builds": isabelle_builds,
        "edits": sum(tools[t] for t in EDIT_TOOLS),
        "reads": tools["Read"],
        "isabelle_mcp": mcp,
        "subagent_launches": tools["Agent"] + tools["Task"],
        "first_day": min(stamps)[:10] if stamps else None,
        "last_day": max(stamps)[:10] if stamps else None,
    }


def _codex_meta(path: Path) -> dict | None:
    first = next(_records(path), None)
    if not first or first.get("type") != "session_meta":
        return None
    return first.get("payload", {})


def codex_stats(paths: list[Path]) -> dict:
    sessions = assistant = human = tool_calls = shell = edits = mcp = builds = 0
    stamps: list[str] = []
    for path in paths:
        sessions += 1
        for record in _records(path):
            if stamp := record.get("timestamp"):
                stamps.append(stamp)
            payload = record.get("payload") or {}
            kind = (record.get("type"), payload.get("type"))
            if kind == ("event_msg", "user_message"):
                human += 1
            elif (
                kind == ("response_item", "message")
                and payload.get("role") == "assistant"
            ):
                assistant += 1
            elif kind in {
                ("response_item", "function_call"),
                ("response_item", "custom_tool_call"),
            }:
                tool_calls += 1
                name = payload.get("name", "")
                shell += name in {"exec_command", "shell", "local_shell"}
                edits += name == "apply_patch"
                args = str(payload.get("arguments") or payload.get("input") or "")
                builds += bool(ISABELLE_BUILD.search(args))
            elif kind == ("event_msg", "mcp_tool_call_end"):
                server = (payload.get("invocation") or {}).get("server", "")
                mcp += server.startswith("isabelle")
    return {
        "sessions": sessions,
        "assistant_messages": assistant,
        "human_messages": human,
        "tool_calls": tool_calls,
        "bash": shell,
        "isabelle_builds": builds,
        "edits": edits,
        "isabelle_mcp": mcp,
        "first_day": min(stamps)[:10] if stamps else None,
        "last_day": max(stamps)[:10] if stamps else None,
    }


def main() -> None:
    dirs = sorted(CLAUDE_PROJECTS.glob(CLAUDE_PREFIX + "*"))
    top = sorted(f for d in dirs for f in d.glob("*.jsonl"))
    sub = sorted(f for d in dirs for f in d.glob("*/subagents/*.jsonl"))
    codex_main: list[Path] = []
    codex_sub: list[Path] = []
    for path in sorted(CODEX_SESSIONS.rglob("*.jsonl")):
        meta = _codex_meta(path)
        if meta is None or CODEX_CWD not in meta.get("cwd", ""):
            continue
        (codex_sub if meta.get("thread_source") == "subagent" else codex_main).append(
            path
        )
    data = {
        "snapshot": dt.date.today().isoformat(),
        "git": git_stats(),
        "rule_files": rule_file_stats(),
        "claude_code": {
            "project_dirs": len(dirs),
            "top_level": log_stats(top),
            "subagents": log_stats(sub),
        },
        "codex": {
            "top_level": codex_stats(codex_main),
            "subagents": codex_stats(codex_sub),
        },
    }
    OUT.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUT.relative_to(REPO)}")


if __name__ == "__main__":
    main()
