#!/usr/bin/env python3
"""Point the blueprint's Lean links at the source on GitHub.

The repository has no doc-gen documentation, and leanblueprint then links every
\\lean{} declaration to the Mathlib documentation, where it does not exist. This
script, run after `leanblueprint web`, rewrites those links in blueprint/web/*.html
to the declaration's lines in the source on GitHub, at the commit being built:

  https://github.com/metamorphoses-collection/stemma-lean/blob/<commit>/<file>#L<a>-L<b>

Locations come from statements.json (kept up to date by CI); a declaration not
listed there is found by searching StemmaLean/ for its namespace and keyword. A
declaration that cannot be located is an error.

Usage: python3 blueprint/link_decls.py [--commit SHA]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REPO = "https://github.com/metamorphoses-collection/stemma-lean"
DOCS = "https://leanprover-community.github.io/mathlib4_docs/find/#doc/"
KEYWORDS = r"(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:def|theorem|lemma|abbrev|structure|inductive|class|instance)"


def locate(name: str, statements: dict) -> tuple[str, int, int]:
    if name in statements:
        e = statements[name]
        return e["file"], e["line_start"], e["line_end"]
    ns, _, short = name.rpartition(".")
    hits = []
    for f in sorted((ROOT / "StemmaLean").rglob("*.lean")):
        lines = f.read_text().split("\n")
        if not any(re.match(rf"\s*namespace {re.escape(ns)}\s*$", l) for l in lines):
            continue
        for i, l in enumerate(lines, 1):
            if re.match(rf"\s*{KEYWORDS}\s+{re.escape(short)}(\s|$)", l):
                hits.append((str(f.relative_to(ROOT)), i, i))
    if len(hits) != 1:
        sys.exit(f"link_decls.py: cannot locate {name} ({len(hits)} candidates)")
    return hits[0]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--commit", help="commit to link to (default: git rev-parse HEAD)")
    a = ap.parse_args()
    commit = a.commit or subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, check=True,
                                        capture_output=True, text=True).stdout.strip()
    statements = json.loads((ROOT / "statements.json").read_text())
    cache: dict[str, str] = {}

    def url(m: re.Match) -> str:
        name = m.group(1)
        if name not in cache:
            f, a_, b = locate(name, statements)
            anchor = f"#L{a_}" if a_ == b else f"#L{a_}-L{b}"
            cache[name] = f"{REPO}/blob/{commit}/{f}{anchor}"
        return cache[name]

    pat = re.compile(re.escape(DOCS) + r"([^\"'<>\s]+)")
    n_files = 0
    for page in sorted((HERE / "web").glob("*.html")):
        s = page.read_text()
        t = pat.sub(url, s)
        if t != s:
            page.write_text(t)
            n_files += 1
    print(f"link_decls.py: {len(cache)} declarations linked to {REPO} at {commit[:7]} "
          f"in {n_files} pages")


if __name__ == "__main__":
    main()
