#!/usr/bin/env python3
"""Axiom audit for the StealthAudit Lean library.

Run after `lake build`. It lists every `theorem`/`lemma` in StealthAudit.lean and in every file
under StealthAudit/ (recursively), asks Lean (`#print axioms`) which axioms each one uses, and
fails if the build failed, if any theorem depends on `sorryAx` or on an axiom outside Lean's three standard
ones, if a banned escape hatch appears outside comments, or if a theorem's proof is just one of
its own hypotheses. It writes verification/STATUS.md and verification/STATUS.json.
"""
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LIB = "StealthAudit"
OUT = ROOT / "verification"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(private|protected)\s+)?(theorem|lemma)\s+([^\s(:{\[]+)")
ns_re = re.compile(r"^\s*namespace\s+(\S+)")
sec_re = re.compile(r"^\s*(?:noncomputable\s+)?section\b\s*(\S*)")
end_re = re.compile(r"^\s*end\b\s*(\S*)\s*$")

BANNED = [r"\bsorry\b", r"\badmit\b", r"maxHeartbeats", r"^\s*axiom\s", r"native_decide",
          r"implemented_by", r"@\[extern", r"\bunsafe\b", r"\bopaque\b", r"set_option\s+debug\.",
          r"set_option\s+pp\."]


def lean_files():
    files = [ROOT / f"{LIB}.lean"] + sorted((ROOT / LIB).rglob("*.lean"))
    return [f for f in files if f.exists()]


def module_name(f):
    return ".".join(f.relative_to(ROOT).with_suffix("").parts)


def strip_comments(text):
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return re.sub(r"--.*", "", text)


def collect():
    """(file, full name) of every public theorem/lemma, tracking nested namespaces and sections."""
    decls, skipped = [], []
    for f in lean_files():
        stack = []  # entries: ("ns", "A.B") or ("sec", name)
        for line in strip_comments(f.read_text()).splitlines():
            m = ns_re.match(line)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            m = sec_re.match(line)
            if m:
                stack.append(("sec", m.group(1)))
                continue
            m = end_re.match(line)
            if m and stack:
                name = m.group(1)
                if name:
                    while stack:
                        kind, n = stack.pop()
                        if n == name:
                            break
                else:
                    stack.pop()
                continue
            d = decl_re.match(line)
            if d:
                vis, name = d.group(1), d.group(3)
                ns = ".".join(n for k, n in stack if k == "ns")
                full = name[1:] if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
                if vis == "private":
                    skipped.append((str(f.relative_to(ROOT)), full))
                else:
                    decls.append((str(f.relative_to(ROOT)), full))
    return decls, skipped


def escape_hatches():
    hits = []
    for f in lean_files():
        for i, line in enumerate(strip_comments(f.read_text()).splitlines(), 1):
            for pat in BANNED:
                if re.search(pat, line):
                    hits.append(f"{f.relative_to(ROOT)}:{i}: `{line.strip()[:90]}`")
    return hits


def tautologies():
    """Theorems whose proof is just one of their own hypotheses (`:= h`, `by exact h`, `by assumption`)."""
    hits = []
    for f in lean_files():
        lines = strip_comments(f.read_text()).splitlines()
        for i, line in enumerate(lines):
            d = decl_re.match(line)
            if not d:
                continue
            chunk, j = [line], i + 1
            while j < len(lines) and not re.match(r"^\S", lines[j]):
                chunk.append(lines[j])
                j += 1
            text = "\n".join(chunk)
            k = text.find(":=")
            if k < 0:
                continue
            sig, proof = text[:k], text[k + 2:].strip()
            binders = [b for grp in re.findall(r"[({\[]([^(){}\[\]:]+):", sig) for b in grp.split()]
            m = re.match(r"^(?:by\s+(?:exact\s+)?)?([^\s()]+)$", proof)
            if re.match(r"^by\s+assumption$", proof) or (m and m.group(1) in binders):
                hits.append(f"{f.relative_to(ROOT)}: `{d.group(3)} := {proof[:60]}`")
    return hits


def error_blocks(path, max_lines=400):
    if not path.exists():
        return []
    out, keep = [], False
    starts = ("error", "warning", "info:", "✔", "⚠", "✖", "Some required", "Build completed")
    for line in path.read_text(errors="replace").splitlines():
        s = line.strip()
        if s.startswith("error"):
            keep = True
        elif s.startswith(starts):
            keep = False
        if keep:
            out.append(line)
        if len(out) >= max_lines:
            break
    return out


def main():
    OUT.mkdir(exist_ok=True)
    sha = os.environ.get("GITHUB_SHA", "") or "local"
    decls, skipped = collect()
    probe = ROOT / "AxiomAudit.lean"
    imports = [f"import {module_name(f)}" for f in lean_files()]
    probe.write_text("\n".join(imports) + "\n\n" + "\n".join(f"#print axioms {n}" for _, n in decls) + "\n")
    proc = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT, capture_output=True, text=True)
    out = proc.stdout + proc.stderr

    results = {}
    for m in re.finditer(r"^'(.+)' depends on axioms: \[([^\]]*)\]\s*$", out, re.M):
        results[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"^'(.+)' does not depend on any axioms\s*$", out, re.M):
        results[m.group(1)] = []

    rows, bad = [], []
    for fname, name in decls:
        axioms = results.get(name)
        if axioms is None:
            status = "NOT CHECKED (name not found by Lean)"
            bad.append(name)
        elif "sorryAx" in axioms:
            status = "FAIL: uses sorry"
            bad.append(name)
        elif set(axioms) - STANDARD:
            status = "FAIL: extra axioms " + ", ".join(sorted(set(axioms) - STANDARD))
            bad.append(name)
        else:
            status = "verified (standard axioms only)"
        rows.append({"file": fname, "theorem": name, "axioms": axioms, "status": status})

    build_log = ROOT / "build.log"
    # The workflow records `lake build`'s exit code in build.exit; without it, fall back to the log.
    build_ok = True
    exit_file = ROOT / "build.exit"
    if exit_file.exists():
        build_ok = exit_file.read_text().strip() == "0"
    elif build_log.exists():
        build_ok = not re.search(r"^error", build_log.read_text(errors="replace"), re.M)
    hatches, taut = escape_hatches(), tautologies()
    ok = build_ok and proc.returncode == 0 and not bad and not hatches and not taut
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    summary = {
        "checked_at": stamp,
        "commit": sha,
        "all_verified": ok,
        "build_ok": build_ok,
        "lean_exit_code": proc.returncode,
        "theorems": len(decls),
        "verified": len(decls) - len(bad),
        "problems": bad,
        "skipped_private": [n for _, n in skipped],
        "escape_hatches": hatches,
        "tautologies": taut,
        "results": rows,
    }
    (OUT / "STATUS.json").write_text(json.dumps(summary, indent=2) + "\n")

    md = [f"# Lean verification status: {'PASS' if ok else 'FAIL'}", "",
          f"Checked {stamp} at commit `{sha[:12]}`.", "",
          f"- Build: {'ok' if build_ok else 'FAILED'}",
          f"- Theorems verified with standard axioms only: {len(decls) - len(bad)} of {len(decls)}",
          "- A theorem listed here is a result of the paper only where ROADMAP.md says so; ROADMAP.md also",
          "  lists the results of the paper that are not proved.", ""]
    if hatches:
        md += ["## Escape hatches (outside comments)", ""] + [f"- {h}" for h in hatches] + [""]
    if taut:
        md += ["## Tautological proofs", ""] + [f"- {t}" for t in taut] + [""]
    if bad:
        md += ["## Problems", ""] + [f"- `{n}`" for n in bad] + [""]
    errs = error_blocks(build_log)
    if errs or proc.returncode != 0:
        md += ["## Build errors", "", "```"] + errs + [l for l in out.splitlines() if "error" in l][:60] + ["```", ""]
    md += ["## Theorems", "", "| file | theorem | status |", "|---|---|---|"]
    md += [f"| {r['file']} | `{r['theorem']}` | {r['status']} |" for r in rows]
    (OUT / "STATUS.md").write_text("\n".join(md) + "\n")
    probe.unlink(missing_ok=True)
    print("\n".join(md[:8]))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
