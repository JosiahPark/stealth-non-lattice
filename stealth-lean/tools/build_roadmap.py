#!/usr/bin/env python3
"""Refresh the roadmap page and the roadmap picture.

Run from the project root (the folder that holds ROADMAP.md) after axiom_audit.py has written
verification/STATUS.json.

Inputs: ROADMAP.md, verification/STATUS.json, and docs/roadmap_config.json, which holds what ROADMAP.md
does not carry: the paper section of each band, short labels, item dependencies, and which items feed
which result of the paper. A result is "proved" when every item in its `need` list is ticked, "from
named hypotheses" when its `cond` item is ticked, "in progress" when some item that feeds it is ticked,
and "open" otherwise.

Outputs:
* docs/roadmap.html: the interactive map. Its `const SNAPSHOT = ...` and `const CFG = ...` lines are
  replaced. Opened in a browser, the page reads ROADMAP.md and the status live from main; the snapshot
  is what it shows when that is not possible (a local file, no network).
* docs/roadmap.svg: the same map as a static picture, for the README files. It needs no script, no web
  font and no GitHub Pages.
* docs/.roadmap_key: a hash of the content without the build time and commit, so CI commits the page
  and the picture only when their content changes.

Only the Python standard library is used.
"""
import hashlib
import json
import os
import re
from html import escape
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAGE = ROOT / "docs" / "roadmap.html"
PICTURE = ROOT / "docs" / "roadmap.svg"
CONFIG = ROOT / "docs" / "roadmap_config.json"
LIB = "StealthAudit"

ITEM = re.compile(r"^-\s+\[( |x|X|-)\]\s+(.*)$")
LIST_SECTION = re.compile(r"^(not attempted|pending generali[sz]ations?|superseded)", re.I)


# ---------------------------------------------------------------------------------------------------
# ROADMAP.md -> bands, items, results (the same rules as the script inside docs/roadmap.html)
# ---------------------------------------------------------------------------------------------------

def parse_roadmap(text):
    bands, band, item, in_list = [], None, None, False
    for raw in text.split("\n"):
        h = re.match(r"^##\s+(.*)$", raw)
        if h:
            item, title = None, h.group(1).strip()
            if LIST_SECTION.match(title):
                band, in_list = None, True
                continue
            in_list = False
            m = re.match(r"^([A-Z])\.\s+(.*)$", title)
            band = dict(key=m.group(1) if m else title[:12], title=m.group(2) if m else title, items=[])
            bands.append(band)
            continue
        if in_list or band is None:
            continue
        it = ITEM.match(raw)
        if it:
            text_, idm = it.group(2), re.match(r"^([A-Z]\d+[a-z]*)\.\s+(.*)$", it.group(2))
            if idm:
                id_, text_ = idm.group(1), idm.group(2)
            else:
                id_ = band["key"] + str(len(band["items"]) + 1)
            item = dict(id=id_, mark=it.group(1).lower(), text=text_, notes=[], band=band["key"])
            band["items"].append(item)
            continue
        sub = re.match(r"^(\s{2,8})-\s+(.*)$", raw)
        if sub and item:
            item["notes"].append(sub.group(2))
            continue
        if not raw.strip():
            continue
        if re.match(r"^\s+\S", raw) and item:
            if item["notes"]:
                item["notes"][-1] += " " + raw.strip()
            else:
                item["text"] += " " + raw.strip()
            continue
        item = None
    return [b for b in bands if b["items"]]


def model(roadmap, results, cfg):
    bands = parse_roadmap(roadmap)
    items = [it for b in bands for it in b["items"]]
    by_id = {it["id"]: it for it in items}
    built = {r[0] for r in results}
    for it in items:
        code = re.findall(r"`([^`]+)`", it["text"] + " " + " ".join(it["notes"]))
        files = {c for c in code if re.match(rf"^{LIB}/[\w/]+\.lean$", c)}
        written = any(re.search(r"written by the (hourly|formalize) task", n, re.I) for n in it["notes"])
        if it["mark"] == "x":
            it["status"] = "done"
        elif it["mark"] == "-":
            it["status"] = "skipped"
        elif it["id"] in cfg.get("decision", []):
            it["status"] = "decision"
        elif written or files & built:
            it["status"] = "written"
        else:
            it["status"] = "open"
        it["short"] = cfg.get("short", {}).get(it["id"]) or re.sub(r"\s*\(.*$", "", it["text"].replace("`", ""))
    # A split item (`- [-] X. ... (split into Xa, Xb)`) whose sub-items are all ticked counts as done.
    changed = True
    while changed:
        changed = False
        for it in items:
            sp = it["status"] == "skipped" and re.search(r"\(split into ([^)]+)\)", it["text"])
            subs = [x.strip() for x in sp.group(1).split(",") if x.strip()] if sp else []
            if subs and all(x in by_id and by_id[x]["status"] == "done" for x in subs):
                it["status"], changed = "done", True
    nxt = next((it for it in items if it["status"] == "open"), None)
    if nxt:
        nxt["next"] = True

    def done(i):
        return i in by_id and by_id[i]["status"] == "done"

    res = []
    for r in cfg.get("results", []):
        need = r.get("need", [])
        if need and all(done(i) for i in need):
            status = "proved"
        elif r.get("cond") and done(r["cond"]):
            status = "conditional"
        elif any(done(i) for i in r.get("items", [])):
            status = "stated"
        else:
            status = "missing"
        res.append(dict(r, status=status))
    return bands, items, res


# ---------------------------------------------------------------------------------------------------
# The static picture
# ---------------------------------------------------------------------------------------------------

SANS = "-apple-system, Segoe UI, Helvetica, Arial, sans-serif"
MONO = "ui-monospace, Menlo, Consolas, monospace"
# The palette of docs/roadmap.html. Every status is also written out and has its own icon shape, so no
# state is carried by colour alone.
STYLE = (
    ".bg{fill:#f6f7f4}.band{fill:#e9ebe5}.box{fill:#fff;stroke:#d0d4cc}"
    ".tt{font-size:17px;font-weight:600;fill:#1d2430}.sm{font-size:12px;fill:#5d6675}"
    ".lbl{font-size:11px;font-weight:600;letter-spacing:.07em;fill:#5d6675}"
    ".ref{font-size:11px;fill:#5d6675}.rn{font-size:13px;font-weight:600;fill:#1d2430}"
    ".rs{font-size:11px;fill:#5d6675}.st{font-size:11px;font-weight:600;fill:#1d2430}"
    f".id{{font-family:{MONO};font-size:11.5px;font-weight:600;fill:#1d2430}}"
    f".nm{{font-family:{MONO};font-size:11px;fill:#1d2430}}"
    ".ct{font-size:10px;font-weight:600;letter-spacing:.06em;fill:#5d6675}.ct.nx{fill:#2b4a7a}"
    ".next{stroke:#2b4a7a;stroke-width:2}.dash{stroke-dasharray:4 3}"
    ".g{fill:#2e8a57}.a{fill:#c48413}.s{fill:#8b93a1}.gs{stroke:#2e8a57}.as{stroke:#c48413}.ss{stroke:#8b93a1}"
    ".rg{fill:#d7eedf;stroke:#2e8a57;stroke-width:1.5}.ra{fill:#f7e6c2;stroke:#c48413;stroke-width:1.5}"
    ".ro{fill:#e3e6ea;stroke:#8b93a1;stroke-width:1.5;stroke-dasharray:4 3}"
    ".ic{fill:none;stroke-width:1.6}.ck{fill:none;stroke:#fff;stroke-width:1.6;stroke-linecap:round;stroke-linejoin:round}"
    "@media (prefers-color-scheme: dark){.bg{fill:#14181f}.band{fill:#1a1f27}.box{fill:#1b2029;stroke:#2e3542}"
    ".tt,.rn,.st,.id,.nm{fill:#e4e7ec}.sm,.lbl,.ref,.rs,.ct{fill:#9aa3b2}.ct.nx{fill:#8fb0e6}.next{stroke:#8fb0e6}"
    ".g{fill:#5cc08a}.a{fill:#e6a93c}.s{fill:#8e97a6}.gs{stroke:#5cc08a}.as{stroke:#e6a93c}.ss{stroke:#8e97a6}"
    ".rg{fill:#1e3a2b;stroke:#5cc08a}.ra{fill:#3d3018;stroke:#e6a93c}.ro{fill:#262c36;stroke:#8e97a6}"
    ".ck{stroke:#14181f}}"
)

ITEM_STATUS = {"done": ("g", "DONE"), "written": ("a", "WRITTEN"), "open": ("s", "OPEN"),
               "skipped": ("s", "SKIPPED"), "decision": ("s", "DECISION")}
RESULT_STATUS = {"proved": ("rg", "g", "proved"), "conditional": ("ra", "a", "from named hypotheses"),
                 "stated": ("ra", "a", "in progress"), "missing": ("ro", "s", "open")}


def fit(text, width, char_w):
    """Cut `text` so that it fits in `width` px at about `char_w` px per character."""
    n = max(1, int(width / char_w))
    return text if len(text) <= n else text[: n - 1].rstrip() + "…"


def wrap(text, width, char_w, lines=2):
    """Greedy word wrap into at most `lines` lines; the last line is cut if needed."""
    n, out, cur = max(1, int(width / char_w)), [], ""
    for word in text.split():
        trial = (cur + " " + word).strip()
        if len(trial) <= n or not cur:
            cur = trial
        else:
            out.append(cur)
            cur = word
    out.append(cur)
    if len(out) > lines:
        out = out[: lines - 1] + [" ".join(out[lines - 1:])]
    return [fit(l, width, char_w) for l in out]


def icon(kind, cx, cy, r=6):
    """A status mark that differs by shape: a checked disc, a half disc, or a ring."""
    if kind == "g":
        return (f'<circle class="g" cx="{cx}" cy="{cy}" r="{r}"/>'
                f'<path class="ck" d="M{cx - 2.8} {cy + 0.2} l2 2 l3.8 -4.4"/>')
    if kind == "a":
        return (f'<circle class="ic as" cx="{cx}" cy="{cy}" r="{r - 0.8}"/>'
                f'<path class="a" d="M{cx} {cy - r + 0.8} a{r - 0.8} {r - 0.8} 0 0 0 0 {2 * r - 1.6} z"/>')
    return f'<circle class="ic ss" cx="{cx}" cy="{cy}" r="{r - 0.8}"/>'


def render_svg(bands, items, results, cfg, st):
    W, PAD, GAP = 960, 20, 8
    inner = W - 2 * PAD
    out, y = [], 0

    def text(x, yy, cls, s, anchor=None):
        a = f' text-anchor="{anchor}"' if anchor else ""
        out.append(f'<text x="{x}" y="{yy}" class="{cls}"{a}>{escape(s)}</text>')

    done = sum(1 for it in items if it["status"] == "done")
    total = sum(1 for it in items if it["status"] != "skipped")
    stamp = st.get("checked_at") or "before the first CI build"
    proved = sum(1 for r in results if r["status"] == "proved")
    text(PAD, 34, "tt", cfg.get("title", "Roadmap"))
    verdict = "all pass the axiom audit" if st.get("all_verified") else "the axiom audit FAILS"
    text(PAD, 54, "sm", f"{done} of {total} roadmap items done · {st.get('verified', '?')} of {st.get('theorems', '?')} "
                        f"Lean theorems verified, {verdict} · build {stamp}")
    # legend
    lx, ly = PAD, 76
    for kind, label in (("g", "done or proved: compiled, standard axioms only"), ("a", "in progress"), ("s", "open")):
        out.append(icon(kind, lx + 6, ly - 4))
        text(lx + 17, ly, "sm", label)
        lx += 17 + int(len(label) * 6.4) + 22
    y = 96

    # results of the paper
    text(PAD, y + 12, "lbl", f"RESULTS OF THE PAPER · {proved} OF {len(results)} PROVED IN LEAN")
    y += 22
    per, rh = 5, 82
    rw = (inner - (per - 1) * GAP) / per
    for i, r in enumerate(results):
        x, yy = PAD + (i % per) * (rw + GAP), y + (i // per) * (rh + GAP)
        box, kind, label = RESULT_STATUS[r["status"]]
        out.append(f'<rect class="{box}" x="{x:.1f}" y="{yy}" width="{rw:.1f}" height="{rh}" rx="6"/>')
        text(f"{x + 10:.1f}", yy + 20, "rn", fit(r["name"], rw - 20, 6.8))
        for k, line in enumerate(wrap(r.get("sub", ""), rw - 20, 5.5)):
            text(f"{x + 10:.1f}", yy + 36 + 13 * k, "rs", line)
        out.append(icon(kind, x + 16, yy + rh - 13))
        text(f"{x + 27:.1f}", yy + rh - 9, "st", label)
    y += -(-len(results) // per) * (rh + GAP) + 10

    # roadmap sections
    per, bh = 5, 46
    bw = (inner - 2 * 10 - (per - 1) * GAP) / per
    for b in bands:
        rows = -(-len(b["items"]) // per)
        h = 30 + rows * (bh + GAP) + 4
        out.append(f'<rect class="band" x="{PAD}" y="{y}" width="{inner}" height="{h}" rx="6"/>')
        n_done = sum(1 for it in b["items"] if it["status"] == "done")
        text(PAD + 10, y + 19, "lbl", f"{b['key']}. {b['title'].upper()} · {n_done} OF {len(b['items'])} DONE")
        text(W - PAD - 10, y + 19, "ref", cfg.get("bandRef", {}).get(b["key"], ""), "end")
        for i, it in enumerate(b["items"]):
            x, yy = PAD + 10 + (i % per) * (bw + GAP), y + 30 + (i // per) * (bh + GAP)
            kind, label = ITEM_STATUS[it["status"]]
            cls = "box" + (" next" if it.get("next") else "") + (" dash" if it["status"] in ("skipped", "decision") else "")
            out.append(f'<rect class="{cls}" x="{x:.1f}" y="{yy}" width="{bw:.1f}" height="{bh}" rx="4"/>')
            id_w = 9 + 7.2 * len(it["id"])
            text(f"{x + 8:.1f}", yy + 18, "id", it["id"])
            text(f"{x + 8 + id_w:.1f}", yy + 18, "nm", fit(it["short"], bw - 16 - id_w, 6.7))
            out.append(icon(kind, x + 14, yy + bh - 13, 5))
            text(f"{x + 24:.1f}", yy + bh - 9.5, "ct", label)
            if it.get("next"):
                text(f"{x + bw - 8:.1f}", yy + bh - 9.5, "ct nx", "NEXT", "end")
        y += h + 8
    text(PAD, y + 14, "sm", "The stealth radius K is defined by formula (2) of the paper. Statements of the items: ROADMAP.md. "
                            "Every theorem with its axioms: verification/STATUS.md.")
    H = y + 30
    summary = "; ".join(f"{r['name']}: {RESULT_STATUS[r['status']][2]}" for r in results)
    head = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" role="img" '
            f'aria-labelledby="rm-t rm-d" font-family="{SANS}">\n'
            f'<title id="rm-t">{escape(cfg.get("title", "Roadmap"))}: {done} of {total} items done</title>\n'
            f'<desc id="rm-d">{escape(summary)}.</desc>\n<style>{STYLE}</style>\n'
            f'<rect class="bg" x="0" y="0" width="{W}" height="{H}"/>')
    return head + "\n" + "\n".join(out) + "\n</svg>\n"


# ---------------------------------------------------------------------------------------------------

def replace_line(lines, mark, new):
    hits = [i for i, l in enumerate(lines) if l.lstrip().startswith(mark)]
    if len(hits) != 1:
        raise SystemExit(f"expected exactly one '{mark}' line in {PAGE}, found {len(hits)}")
    lines[hits[0]] = new


def main():
    roadmap = (ROOT / "ROADMAP.md").read_text()
    cfg = json.loads(CONFIG.read_text())
    try:
        st = json.loads((ROOT / "verification" / "STATUS.json").read_text())
    except (OSError, ValueError):
        st = {}
    results = [[r["file"], r["theorem"], r["status"].startswith("verified")] for r in st.get("results", [])]
    content = dict(roadmap=roadmap, results=results, theorems=st.get("theorems"), verified=st.get("verified"),
                   audit=st.get("all_verified"))
    key = hashlib.sha256(json.dumps(dict(content, cfg=cfg), sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    sha = os.environ.get("GITHUB_SHA", "")
    snap = dict(content, sha=sha[:7], at=st.get("checked_at") or "before the first CI build", live=False,
                ci=dict(status="completed", conclusion="success" if st.get("all_verified") else "failure", sha=sha) if st else None)

    def js(value):
        return json.dumps(value, ensure_ascii=False).replace("</", "<\\/")

    lines = PAGE.read_text().split("\n")
    replace_line(lines, "const SNAPSHOT = ", "const SNAPSHOT = " + js(snap) + ";")
    replace_line(lines, "const CFG = ", "const CFG = " + js(cfg) + ";")
    PAGE.write_text("\n".join(lines))

    bands, items, res = model(roadmap, results, cfg)
    PICTURE.write_text(render_svg(bands, items, res, cfg, st))
    (ROOT / "docs" / ".roadmap_key").write_text(key + "\n")
    done = sum(1 for it in items if it["status"] == "done")
    total = sum(1 for it in items if it["status"] != "skipped")
    proved = sum(1 for r in res if r["status"] == "proved")
    print(f"roadmap: {done} of {total} items done; {proved} of {len(res)} results proved; "
          f"{st.get('verified')}/{st.get('theorems')} theorems verified")


if __name__ == "__main__":
    main()
