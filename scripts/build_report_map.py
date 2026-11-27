#!/usr/bin/env python3
"""Build report_map.json: report results -> fully qualified Lean declarations.

Parses the Verbatim blocks of Appendix B ("Formal verification in Lean") of the report,
attributes every declaration header in a block to the enclosing entry (the
\\subsubsection*, or the \\subsection for the blocks before the first entry), and resolves
each short name to its fully qualified name by scanning the StemmaLean sources
(namespace/section/end tracking).  Ambiguous short names are resolved first by the entry's
`\\emph{Lean:} \\texttt{Files}` line, then by similarity of the hand-copied text with the
source text.  Unresolvable names fail loudly.

Usage: scripts/build_report_map.py path/to/main.tex  [--out report_map.json]

The map is the persisted resolution: `ExtractStatements.lean` re-checks every name against
the elaborated library, so a stale map fails there.
"""
import argparse
import difflib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = ROOT / "StemmaLean"

HEADER_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|structure|abbrev|inductive|class|instance)\s+([^\s({\[:]+)")
SECTION_RE = re.compile(r"\\section\{Formal verification in Lean\}")
VERB_BEGIN = re.compile(r"^\\begin\{Verbatim\}")
VERB_END = re.compile(r"^\\end\{Verbatim\}")


def appendix_bounds(lines):
    start = next(i for i, l in enumerate(lines) if SECTION_RE.search(l))
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if re.match(r"^\\(section\{|bibliographystyle|bibliography\{|end\{document\})", lines[i]):
            end = i
            break
    return start, end


def parse_blocks(lines):
    """Yield dicts {entry_title, kind, labels, files, begin, end, chunks} for every Verbatim
    block of Appendix B.  `begin`/`end` are the line indices of the \\begin/\\end lines."""
    start, stop = appendix_bounds(lines)
    title, kind, files = None, None, []
    blocks = []
    i = start
    while i < stop:
        l = lines[i]
        m = re.match(r"^\\subsubsection\*\{(.*)\}\s*$", l) or re.match(r"^\\subsection\{(.*)\}", l)
        if m:
            title = m.group(1)
            kind = "subsubsection" if l.startswith("\\subsubsection") else "subsection"
            files = []
        m = re.match(r"^\\noindent\\emph\{Lean:\}\s*\\texttt\{([^}]*)\}", l)
        if m:
            files = [f.strip() for f in m.group(1).split(",") if f.strip()]
        if VERB_BEGIN.match(l):
            j = i + 1
            while not VERB_END.match(lines[j]):
                j += 1
            body = lines[i + 1:j]
            blocks.append(dict(entry_title=title, heading=kind, files=list(files),
                               labels=re.findall(r"\\ref\{([^}]*)\}", title or ""),
                               begin=i, end=j, chunks=chunk(body)))
            i = j
        i += 1
    return blocks


def chunk(body):
    """Split a block body into chunks.  A chunk starts at a column-0 non-blank line; it is a
    declaration chunk if that line is a declaration header.  Trailing blank lines are dropped."""
    chunks = []
    cur = None
    for l in body:
        if l and not l[0].isspace():
            if cur:
                chunks.append(cur)
            m = HEADER_RE.match(l)
            cur = dict(kind="decl" if m else "other",
                       keyword=m.group(1) if m else None,
                       name=m.group(2) if m else None, lines=[l])
        elif cur is None:
            if l.strip():
                cur = dict(kind="other", keyword=None, name=None, lines=[l])
        else:
            cur["lines"].append(l)
    if cur:
        chunks.append(cur)
    for c in chunks:
        while c["lines"] and not c["lines"][-1].strip():
            c["lines"].pop()
    # an `other` line indented under a decl (e.g. `deriving`) stays in that decl: merge
    out = []
    for c in chunks:
        if c["kind"] == "other" and out and out[-1]["kind"] == "decl" and \
                c["lines"][0].startswith("deriving"):
            out[-1]["lines"] += c["lines"]
        else:
            out.append(c)
    return out


def scan_library():
    """Return {short-or-declared name: [ {fqn, file, keyword, text} ]} for every declaration in
    StemmaLean/.  Keys: the last component and the name as declared."""
    index = {}
    for path in sorted(LIB.rglob("*.lean")):
        rel = path.relative_to(LIB).as_posix()
        if rel == "Statements.lean":
            continue
        src = path.read_text().splitlines()
        stack = []  # entries: ("ns", Name) or ("sec", name)
        for k, l in enumerate(src):
            m = re.match(r"^namespace\s+(\S+)", l)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            m = re.match(r"^(?:noncomputable\s+)?section\b\s*(\S*)", l)
            if m:
                stack.append(("sec", m.group(1)))
                continue
            m = re.match(r"^end\b\s*(\S*)", l)
            if m and stack:
                stack.pop()
                continue
            m = HEADER_RE.match(l)
            if not m:
                continue
            declared = m.group(2)
            private = bool(re.match(r"^(?:@\[[^\]]*\]\s*)?(?:\w+\s+)*private\s", l))
            ns = ".".join(x for t, x in stack if t == "ns")
            if declared.startswith("_root_."):
                fqn = declared[len("_root_."):]
            else:
                fqn = f"{ns}.{declared}" if ns else declared
            # source text of the header up to `:=` / `where` / `|`, for disambiguation
            text = []
            for l2 in src[k:k + 40]:
                text.append(l2)
                if re.search(r":=|\bwhere\b", l2) or (text and l2.strip() == "" and len(text) > 1):
                    break
            rec = dict(fqn=fqn, file=rel, keyword=m.group(1), declared=declared,
                       private=private, text="\n".join(text))
            for key in {declared, declared.split(".")[-1]}:
                index.setdefault(key, []).append(rec)
    return index


def norm(s):
    s = re.sub(r":=.*", "", s, flags=re.S)
    s = re.sub(r"\bwhere\b.*", "", s, flags=re.S)
    return re.sub(r"\s+", " ", s).strip()


def resolve(c, files, index, problems):
    cands = index.get(c["name"], [])
    if not cands:
        problems.append(f"unknown declaration `{c['name']}` (entry files {files})")
        return None
    exact = [r for r in cands if r["declared"] == c["name"]] or cands
    cands = exact
    if len(cands) > 1 and files:
        infile = [r for r in cands if r["file"] in files]
        if infile:
            cands = infile
    if len(cands) > 1:
        hand = norm("\n".join(c["lines"]))
        scored = sorted(((difflib.SequenceMatcher(None, hand, norm(r["text"])).ratio(), r)
                         for r in cands), key=lambda t: -t[0])
        best, second = scored[0], scored[1]
        if best[0] - second[0] < 0.05:
            problems.append(f"ambiguous `{c['name']}`: " +
                            ", ".join(f"{r['fqn']} ({s:.2f})" for s, r in scored))
            return None
        cands = [best[1]]
    r = cands[0]
    if r["private"]:
        problems.append(f"`{r['fqn']}` is private")
    return r


def report_numbers(aux):
    nums = {}
    for m in re.finditer(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}", aux):
        nums[m.group(1)] = m.group(2)
    return nums


def plain_title(title, nums):
    """The entry title as plain text for a docstring: refs resolved, light LaTeX removed."""
    t = title or ""
    t = re.sub(r"\\ref\{([^}]*)\}", lambda m: nums.get(m.group(1), m.group(1)), t)
    t = re.sub(r"\\cite\{[^}]*\}", "[ref]", t)
    t = re.sub(r"\\(?:emph|textit|texttt)\{([^}]*)\}", r"\1", t)
    t = t.replace("~", " ").replace("--", "–").replace("-/", "- /")
    return re.sub(r"\s+", " ", t).strip()


KINDS = {"thm": "Theorem", "prop": "Proposition", "lem": "Lemma", "cor": "Corollary",
         "def": "Definition", "rem": "Remark"}


def label_info(aux):
    """{label: (number, title)} from main.aux (the title is the optional theorem name)."""
    info = {}
    for m in re.finditer(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}\{[^}]*\}\{((?:[^{}]|\{[^{}]*\})*)\}", aux):
        info[m.group(1)] = (m.group(2), m.group(3))
    return info


def update_selection(aux_text, index, problems):
    """Refresh number/kind/title of scripts/statements_selection.json from main.aux; check names."""
    path = ROOT / "scripts" / "statements_selection.json"
    if not path.exists():
        return
    sel = json.loads(path.read_text())
    info = label_info(aux_text)
    fqns = {r["fqn"] for rs in index.values() for r in rs}
    for s in sel:
        if s["label"] not in info:
            problems.append(f"selection: label {s['label']} not in main.aux")
            continue
        num, title = info[s["label"]]
        title = re.sub(r"\\cite\s*\{[^}]*\}", "", title)
        title = re.sub(r"[;,]?\s*see\s*~?\s*$", "", title.replace("~", " ")).strip(" ;,")
        greek = {"gamma": "γ", "alpha": "α", "delta": "δ", "sigma": "σ"}
        title = re.sub(r"\$\\(\w+)\s*\$", lambda m: greek.get(m.group(1), m.group(1)), title)
        title = re.sub(r"\$([^$]*)\$", r"\1", title)
        s.update(number=num, kind=KINDS.get(s["label"].split(":")[0], "Result"),
                 title=re.sub(r"\s+", " ", title))
        for t in s["theorems"]:
            if t not in fqns:
                problems.append(f"selection: {t} is not a library declaration")
    path.write_text(json.dumps(sel, ensure_ascii=False, indent=1) + "\n")


def build(tex_path):
    tex_path = pathlib.Path(tex_path)
    lines = tex_path.read_text().split("\n")
    aux_path = tex_path.with_suffix(".aux")
    nums = report_numbers(aux_path.read_text()) if aux_path.exists() else {}
    index = scan_library()
    problems = []
    entries = []
    for b in parse_blocks(lines):
        if not entries or entries[-1]["entry_title"] != b["entry_title"]:
            labels = b["labels"]
            label = labels[0] if labels else ("app:lean" if b["heading"] == "subsection" else None)
            entries.append(dict(
                label=label, labels=labels,
                report_number=nums.get(label) if label else None,
                report_numbers=[nums.get(x) for x in labels],
                entry_title=b["entry_title"], heading=b["heading"],
                doc=plain_title(b["entry_title"], nums),
                file=b["files"], decls=[], blocks=[]))
        e = entries[-1]
        blk = []
        for c in b["chunks"]:
            if c["kind"] != "decl":
                blk.append(dict(other="\n".join(c["lines"])))
                continue
            r = resolve(c, b["files"], index, problems)
            if r is None:
                continue
            blk.append(dict(name=r["fqn"], as_written=c["name"], keyword=r["keyword"],
                            source=r["file"]))
            if r["fqn"] not in e["decls"]:
                e["decls"].append(r["fqn"])
        e["blocks"].append(blk)
    if aux_path.exists():
        update_selection(aux_path.read_text(), index, problems)
    for e in entries:
        if e["label"] and e["report_number"] is None:
            problems.append(f"label {e['label']} has no number in main.aux")
    return entries, problems


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tex")
    ap.add_argument("--out", default=str(ROOT / "report_map.json"))
    a = ap.parse_args()
    entries, problems = build(a.tex)
    if problems:
        print("\n".join("ERROR: " + p for p in problems), file=sys.stderr)
        sys.exit(1)
    pathlib.Path(a.out).write_text(json.dumps(entries, ensure_ascii=False, indent=1) + "\n")
    nd = sum(len(e["decls"]) for e in entries)
    print(f"{len(entries)} entries, {nd} declarations (unique per entry) -> {a.out}")


if __name__ == "__main__":
    main()
