"""Extract reviewer comments from an annotated thesis PDF and locate them in
the Typst sources.

    pixi run thesis-feedback <annotated.pdf> [out-prefix]

Writes <out-prefix>.md, a checklist grouped by section, and <out-prefix>.json;
the prefix defaults to build/feedback/<pdf name>, outside version control,
since a reviewer's comments are not for the public repository.

The revision the PDF was built from comes from its `revision <sha>` keyword,
or else from the last commit on origin/main before the PDF's creation date.
Each comment is matched against the sources at that revision (by voting on
word trigrams of the sentence around the mark), then carried forward to the
working tree: found again, or flagged as changed since.
"""

import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path

import pymupdf

repo = Path(__file__).resolve().parents[2]
pdf_path = Path(sys.argv[1]).expanduser().resolve()
prefix = (
    Path(sys.argv[2])
    if len(sys.argv) > 2
    else repo / "build" / "feedback" / pdf_path.stem
)


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(repo), *args], check=True, capture_output=True, text=True
    ).stdout


doc = pymupdf.open(pdf_path)

# ---- revision -------------------------------------------------------------
keywords = doc.metadata.get("keywords") or ""
m = re.search(r"revision ([0-9a-f]{7,40})(-dirty)?", keywords)
if m:
    revision, how = m.group(1), "PDF metadata" + (" (dirty tree)" if m.group(2) else "")
else:
    raw = doc.metadata.get("creationDate", "")  # D:20261022153211+02'00' or ...Z
    d = re.match(r"D:(\d{14})(Z|[+-]\d{2})?'?(\d{2})?", raw)
    when = datetime.strptime(d.group(1), "%Y%m%d%H%M%S").strftime("%Y-%m-%d %H:%M:%S")
    tz = "+0000" if d.group(2) in (None, "Z") else f"{d.group(2)}{d.group(3) or '00'}"
    revision = git(
        "log", "-1", "--format=%H", f"--before={when} {tz}", "origin/main"
    ).strip()
    how = f"last origin/main commit before creation date {when} {tz}"
rev_short = revision[:9]


# ---- sources --------------------------------------------------------------
def tokenize(text: str):
    """Lowercased words with their 1-based line numbers."""
    out = []
    for lineno, line in enumerate(text.split("\n"), 1):
        for w in re.findall(r"[A-Za-z0-9]+", line):
            out.append((w.lower(), lineno))
    return out


HEADING = re.compile(
    r'^\s*(?:=+\s+(.*?)\s*(?:<[^>]*>)?\s*$|#part\("([^"]+)"|#heading\([^)]*\)\[([^\]]+)\])'
)


def norm(text: str) -> str:
    return " ".join(re.findall(r"[a-z0-9]+", text.lower()))


def sources_at(rev: str | None) -> tuple[dict[str, list], dict[str, tuple[str, int]]]:
    files, headings = {}, {}
    names = git("ls-tree", "-r", "--name-only", rev or "HEAD", "thesis").split("\n")
    for name in names:
        if not name.endswith(".typ") or "/shared/generated/" in name:
            continue
        if rev:
            text = git("show", f"{rev}:{name}")
        else:
            p = repo / name
            if not p.exists():
                continue
            text = p.read_text()
        files[name] = tokenize(text)
        for lineno, line in enumerate(text.split("\n"), 1):
            h = HEADING.match(line)
            if h:
                title = re.sub(
                    r"#[a-z-]+\([^)]*\)", "", next(g for g in h.groups() if g)
                )
                if norm(title):
                    headings.setdefault(norm(title), (name, lineno))
    return files, headings


def index(files):
    idx = defaultdict(list)
    for name, toks in files.items():
        for i in range(len(toks) - 2):
            idx[(toks[i][0], toks[i + 1][0], toks[i + 2][0])].append((name, i))
    return idx


def locate(words: list[str], mark_at: int, files, idx):
    """Best (file, line of the mark, score) for a word sequence."""
    words = [w.lower() for w in words]
    votes = Counter()
    first = {}  # per alignment, the earliest matched trigram: (j, i)
    for j in range(len(words) - 2):
        for name, i in idx.get((words[j], words[j + 1], words[j + 2]), ()):
            votes[(name, i - j)] += 1
            first.setdefault((name, i - j), (j, i))
    if not votes:
        return None
    (name, start), n = votes.most_common(1)[0]
    score = n / max(1, len(words) - 2)
    toks = files[name]
    # Markup the PDF does not show (a reference, a label) shifts the alignment
    # within the sentence, so anchor the mark at a trigram that matched.
    j0, i0 = min(
        (first[k] for k in first if k[0] == name and abs(k[1] - start) <= 5),
        key=lambda ji: ji[0],
    )
    pos = i0 + (mark_at - j0) if mark_at >= j0 else start + mark_at
    pos = min(max(pos, 0), len(toks) - 1)
    return name, toks[pos][1], round(score, 2)


old_files, old_heads = sources_at(revision)
old_idx = index(old_files)
new_files, new_heads = sources_at(None)
new_idx = index(new_files)


def heading_in(quote: str, context: str, heads):
    """A heading whose title the mark is, or is part of, on a contents page."""
    q, c = norm(re.sub(r"\.( \.)+", " ", quote)), norm(context)
    best = None
    for title, loc in heads.items():
        if len(title) < 4:
            continue
        if title in q or (q and q in title and title in c):
            if best is None or len(title) > len(best[0]):
                best = (title, loc)
    return best


# ---- sections -------------------------------------------------------------
toc = doc.get_toc()  # [level, title, page]


def section_of(pno: int) -> str:
    title = ""
    for level, t, page in toc:
        if page - 1 <= pno and level <= 2:
            title = t
    return title


def page_label(page) -> str:
    label = page.get_label() or ""
    # PyMuPDF can leak the dictionary key into a roman label.
    return label.removeprefix("ageLabel") or str(page.number + 1)


# ---- annotations ----------------------------------------------------------
def page_words(page):
    ws = page.get_text("words", sort=True)  # x0 y0 x1 y1 word block line wno
    # Rejoin words hyphenated at a line end.
    out = []
    for w in ws:
        if (
            out
            and out[-1][4].endswith("-")
            and (out[-1][5], out[-1][6]) != (w[5], w[6])
        ):
            prev = out.pop()
            w = (prev[0], prev[1], w[2], w[3], prev[4][:-1] + w[4], w[5], w[6], w[7])
        out.append(w)
    return out


def marked(page, annot, words):
    v = annot.vertices or []
    rects = [pymupdf.Quad(v[i : i + 4]).rect for i in range(0, len(v), 4)] or [
        annot.rect
    ]
    hits = []
    for k, w in enumerate(words):
        r = pymupdf.Rect(w[:4])
        c = pymupdf.Point((r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2)
        if any(q.contains(c) for q in rects):
            hits.append(k)
    return hits


ENDS = re.compile(r"[.!?:]$")


def sentence(words, hits):
    """The sentence around the marked words, as indices into words."""
    lo, hi = hits[0], hits[-1]
    while lo > 0 and not ENDS.search(words[lo - 1][4]) and hits[0] - lo < 40:
        lo -= 1
    while hi < len(words) - 1 and not ENDS.search(words[hi][4]) and hi - hits[-1] < 40:
        hi += 1
    return lo, hi


CATEGORIES = [
    ("undefined term", r"\bwhat('s| is| are| does)\b|no idea|what do you mean|which "),
    ("sounds AI", r"\bai\b|written by you"),
    ("title", r"title|reformulate"),
    ("too detailed", r"detail|shorten|cut "),
    ("praise", r"\bnice\b|\bi like\b|much improved"),
]


def categorize(text: str) -> str:
    t = text.lower()
    return next((c for c, rx in CATEGORIES if re.search(rx, t)), "wording")


def is_contents(page) -> bool:
    """A page of the table of contents: mostly dot leaders."""
    return page.get_text().count(". . .") >= 8


items = []
for page in doc:
    words = page_words(page)
    for annot in page.annots():
        kind = annot.type[1]
        if kind in ("Link", "Popup"):
            continue
        comment = (annot.info.get("content") or "").strip()
        hits = marked(page, annot, words)
        quote = " ".join(words[k][4] for k in hits) if hits else ""
        item = {
            "page": page_label(page),
            "pdf_page": page.number + 1,
            "section": "Contents" if is_contents(page) else section_of(page.number),
            "kind": kind,
            "quote": quote,
            "comment": comment,
            "category": categorize(comment) if comment else "unmarked",
        }
        if hits:
            lo, hi = sentence(words, hits)
            ctx = [
                re.sub(r"[^A-Za-z0-9 ]", " ", words[k][4]) for k in range(lo, hi + 1)
            ]
            ctx_words = " ".join(ctx).split()
            item["context"] = " ".join(words[k][4] for k in range(lo, hi + 1))
            mark_at = len(" ".join(ctx[: hits[0] - lo]).split())
            q_words = re.sub(r"[^A-Za-z0-9 ]", " ", quote).split()
            old_h = (
                heading_in(quote, item["context"], old_heads)
                if is_contents(page)
                else None
            )
            if old_h:
                item["category"] = (
                    "title"
                    if item["category"] in ("wording", "undefined term", "sounds AI")
                    and "ai" not in comment.lower()
                    else item["category"]
                )
                old = (*old_h[1], 1.0)
                new_h = new_heads.get(old_h[0])
                new = (*new_h, 1.0) if new_h else None
            elif len(q_words) >= 12:
                old = locate(q_words, 0, old_files, old_idx)
                new = locate(q_words, 0, new_files, new_idx)
            else:
                old = locate(ctx_words, mark_at, old_files, old_idx)
                new = locate(ctx_words, mark_at, new_files, new_idx)
            if old:
                item["at_revision"] = f"{old[0]}:{old[1]}"
                item["match"] = old[2]
            if new and new[2] >= 0.6:
                item["now"] = f"{new[0]}:{new[1]}"
                item["status"] = "open"
            elif old:
                item["status"] = "changed since"
            else:
                item["status"] = "not located"
        else:
            item["status"] = "not located"
        items.append(item)

for n, it in enumerate(items, 1):
    it["id"] = n

prefix.parent.mkdir(parents=True, exist_ok=True)
Path(f"{prefix}.json").write_text(
    json.dumps(
        {"pdf": str(pdf_path), "revision": revision, "how": how, "items": items},
        indent=2,
    )
)

# ---- markdown -------------------------------------------------------------
lines = [
    f"# Feedback: {pdf_path.name}",
    "",
    f"Built from `{rev_short}` ({how}). {len(items)} annotations.",
    "",
]
counts = Counter(it["status"] for it in items)
lines += [", ".join(f"{v} {k}" for k, v in counts.items()), ""]
current = None
for it in items:
    if it["section"] != current:
        current = it["section"]
        lines += [f"## {current or '(front)'}", ""]
    loc = it.get("now") or (
        f"{it['at_revision']} at {rev_short}" if "at_revision" in it else "?"
    )
    lines.append(
        f"- [ ] **#{it['id']}** `{loc}` · p. {it['page']} · {it['category']} · {it['status']}"
    )
    if it["quote"]:
        lines.append(f"  - marked: “{it['quote']}”")
    if it.get("context") and it["context"] != it["quote"]:
        lines.append(f"  - in: {it['context']}")
    if it["comment"]:
        lines.append("  - comment: " + it["comment"].replace("\n", " "))
lines.append("")
Path(f"{prefix}.md").write_text("\n".join(lines))
print(f"{len(items)} annotations, revision {rev_short} ({how}); {dict(counts)}")
print(f"-> {prefix}.md, {prefix}.json")
