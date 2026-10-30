"""Locate entities in Isabelle's rendered source, including generated facts.

An entity anchor can wrap an interpretation keyword rather than a declaration.
Keep the command that owns each anchor; anchor existence alone cannot tell a
reader whether the page displays the entity's definition or statement.
"""

from html.parser import HTMLParser
from urllib.parse import unquote

INTERPRETATIONS = {"global_interpretation", "interpretation", "interpret", "sublocale"}


class Source(HTMLParser):
    def __init__(self, body):
        super().__init__()
        self.anchors = {}
        self.command = None
        self.awaiting_keyword = False
        self.feed(body)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "command" in attrs.get("class", "").split():
            self.command = {"name": "", "locales": set()}
            self.awaiting_keyword = True
        if "id" in attrs:
            self.anchors[attrs["id"]] = self.command
        if tag == "a" and self.command is not None:
            _, sep, anchor = unquote(attrs.get("href", "")).partition("#")
            if sep and anchor.endswith("|locale"):
                self.command["locales"].add(anchor.removesuffix("|locale"))

    def handle_data(self, text):
        if self.awaiting_keyword and text.strip():
            self.command["name"] = text.strip()
            self.awaiting_keyword = False

    def location(self, anchor):
        if anchor not in self.anchors:
            return "theory"
        command = self.anchors[anchor]
        if command is None:
            return "source"
        if command["name"] in INTERPRETATIONS:
            return "interpretation"
        return "source"


def generic_sources(raw, sources):
    """Find generic declarations within the interpreted locale's ancestry.

    The ancestry comes from Isabelle's Locale.pretty_locale_deps export. The HTML
    supplies the interpreted locale and verifies that a candidate is displayed at a
    source command. Ambiguous matches stay unresolved, never chosen by page order.
    """
    parents = {
        key.removeprefix("locale:"): [
            d.removeprefix("locale:") for d in node["deps"] if d.startswith("locale:")
        ]
        for key, node in raw.items()
        if key.startswith("locale:")
    }
    locale_names = {}
    for locale in parents:
        locale_names.setdefault(locale.split(".")[-1], set()).add(locale)
    candidates = {}
    for key, node in raw.items():
        kind, name = key.split(":", 1)
        parts = name.split(".")
        if len(parts) < 3:
            continue
        anchor = name + "|" + ("fact" if kind == "thm" else kind)
        source = sources[node["theory"]]
        command = source.anchors.get(anchor)
        if (
            source.location(anchor) == "source"
            and command is not None
            and command["name"] not in {"locale", "class"}
        ):
            # A locale context may add facts in a theory other than its owner.
            candidates.setdefault((kind, parts[-2], parts[-1]), []).append(key)

    result = {}
    for key, node in raw.items():
        kind, name = key.split(":", 1)
        anchor = name + "|" + ("fact" if kind == "thm" else kind)
        source = sources[node["theory"]]
        if source.location(anchor) != "interpretation":
            continue
        pending = list(source.anchors[anchor]["locales"])
        visited = set()
        matches = set()
        while pending:
            locale = pending.pop()
            if locale in visited:
                continue
            visited.add(locale)
            pending.extend(parents.get(locale, []))
            if locale_names.get(locale.split(".")[-1]) != {locale}:
                continue
            matches.update(
                candidates.get((kind, locale.split(".")[-1], name.split(".")[-1]), [])
            )
        if len(matches) == 1:
            result[key] = matches.pop()
    return result
