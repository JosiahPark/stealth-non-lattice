#!/usr/bin/env python3
"""Refresh the data snapshot inside docs/roadmap.html.

Run from the repository root after axiom_audit.py has written verification/STATUS.json.
docs/roadmap.html is a self-contained page: it draws ROADMAP.md as a map (sections as bands, items as
boxes, paper results as a spine). When opened in a browser it reads ROADMAP.md and STATUS.json live
from main; the snapshot written here is what it shows when that is not possible (a local file, no
network). The page's layout data (short labels, dependencies, paper results) is the `CFG` block in
the page itself.

Outputs: docs/roadmap.html (snapshot line replaced) and docs/.roadmap_key (a hash of the snapshot
without the build time and commit, so CI commits the page only when its content changes).
Only the Python standard library is used.
"""
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAGE = ROOT / "docs" / "roadmap.html"
MARK = "const SNAPSHOT = "


def main():
    roadmap = (ROOT / "ROADMAP.md").read_text()
    try:
        st = json.loads((ROOT / "verification" / "STATUS.json").read_text())
    except (OSError, ValueError):
        st = {}
    results = [[r["file"], r["theorem"], r["status"].startswith("verified")] for r in st.get("results", [])]
    content = dict(roadmap=roadmap, results=results, theorems=st.get("theorems"), verified=st.get("verified"),
                   audit=st.get("all_verified"))
    key = hashlib.sha256(json.dumps(content, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    sha = os.environ.get("GITHUB_SHA", "")
    snap = dict(content, sha=sha[:7], at=st.get("checked_at") or "before the first CI build", live=False,
                ci=dict(status="completed", conclusion="success" if st.get("all_verified") else "failure", sha=sha) if st else None)
    line = MARK + json.dumps(snap, ensure_ascii=False).replace("</", "<\\/") + ";"
    lines = PAGE.read_text().split("\n")
    hits = [i for i, l in enumerate(lines) if l.lstrip().startswith(MARK)]
    if len(hits) != 1:
        raise SystemExit(f"expected exactly one '{MARK}' line in {PAGE}, found {len(hits)}")
    lines[hits[0]] = line
    PAGE.write_text("\n".join(lines))
    (ROOT / "docs" / ".roadmap_key").write_text(key + "\n")
    done = roadmap.count("\n- [x] ")
    todo = roadmap.count("\n- [ ] ")
    print(f"roadmap: {done} of {done + todo} items ticked; {st.get('verified')}/{st.get('theorems')} theorems verified")


if __name__ == "__main__":
    main()
