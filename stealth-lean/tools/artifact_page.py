#!/usr/bin/env python3
"""Write the claude.ai artifact copy of docs/roadmap.html.

The external link to the roadmap map is a claude.ai artifact. A published artifact cannot fetch from
GitHub, so this copy drops the page's live-data loader and draws the snapshot that tools/build_roadmap.py
put into docs/roadmap.html. The artifact host adds its own document skeleton, so the copy has no
doctype, html, head or body tags and no charset or viewport meta.

Usage, from the project root (the folder that holds ROADMAP.md), after tools/build_roadmap.py:

    python3 tools/artifact_page.py <output.html>

Then publish <output.html> to the artifact's existing URL with the Artifact tool (read it first).
Only the Python standard library is used.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAGE = ROOT / "docs" / "roadmap.html"

SKELETON = ("<!doctype", "<html", "</html", "<head", "</head", "<body", "</body",
            '<meta charset', '<meta name="viewport"')

LOADER = """// Draw only once live data has arrived (or failed), so the stale snapshot numbers never flash first.
document.getElementById("stats").textContent = "Loading live data from main…";
setTimeout(() => { if (!M) { render(); renderSrc(); } }, 10000);
live();"""

STATIC = """// Artifact copy (tools/artifact_page.py): no live data, draw the snapshot at once.
render(); renderSrc();"""

SRC_NOTE = ("`Snapshot${src.sha ? \" of commit \" + src.sha : \"\"} (${src.at}); live data could not be fetched here.`")
SRC_NOTE_STATIC = ("`Snapshot${src.sha ? \" of commit \" + src.sha : \"\"} (${src.at}), republished after changes to "
                   "the roadmap. The statements of the items are in ROADMAP.md on GitHub.`")


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: python3 tools/artifact_page.py <output.html>")
    html = PAGE.read_text()
    for old, new in ((LOADER, STATIC), (SRC_NOTE, SRC_NOTE_STATIC)):
        if html.count(old) != 1:
            raise SystemExit(f"expected exactly one copy of this block in {PAGE}:\n{old}")
        html = html.replace(old, new)
    lines = [l for l in html.split("\n") if not l.lstrip().lower().startswith(SKELETON)]
    out = "\n".join(lines).strip() + "\n"
    if not out.startswith("<style>") or "<title>" not in out[:8000]:
        raise SystemExit("unexpected page layout: the copy must start with the reset <style> line and its <title>")
    Path(sys.argv[1]).write_text(out)
    print(f"wrote {sys.argv[1]} ({len(out)} bytes)")


if __name__ == "__main__":
    main()
