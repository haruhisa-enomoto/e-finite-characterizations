#!/usr/bin/env python3
"""Check generated local page targets and the displayed theorem statements."""
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "_site"


class Page(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.links = []
        self.ids = set()
        self.text = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        for key in ("href", "src"):
            if key in attrs:
                self.links.append(attrs[key])

    def handle_data(self, data):
        self.text.append(data)


def main():
    pages = {}
    for path in SITE.rglob("*.html"):
        page = Page()
        page.feed(path.read_text())
        pages[path.resolve()] = page
    errors = []
    for path, page in pages.items():
        for raw in page.links:
            link = urlsplit(raw)
            if link.scheme or link.netloc or raw.startswith("/"):
                continue
            target = (path.parent / unquote(link.path)).resolve() if link.path else path
            if target.is_dir():
                target /= "index.html"
            if not target.is_relative_to(SITE) or not target.exists():
                errors.append(f"{path.relative_to(SITE)}: missing {raw}")
            # The handwritten pages own their anchors. doc-gen4 also uses
            # JavaScript-generated anchors, so check its page targets only.
            elif path.parent == SITE and link.fragment and target in pages:
                if unquote(link.fragment) not in pages[target].ids:
                    errors.append(f"{path.name}: missing anchor {raw}")
    statement = "".join(pages[(SITE / "statement.html").resolve()].text)
    for name in ("equivalences_arbitraryField", "equivalences_infiniteField", "equivalences_algebraicallyClosedField"):
        if "theorem " + name not in statement:
            errors.append(f"statement.html omits {name}")
    if errors:
        raise SystemExit("\n".join(errors[:50]) + f"\n{len(errors)} link/content errors")
    print(f"Checked {len(pages)} pages; local targets and the three Theorem A declarations checked")


if __name__ == "__main__":
    main()
