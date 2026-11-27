#!/usr/bin/env python3
"""Regenerate the Lean code blocks of the report's Appendix B from `statements.json`.

Every declaration shown in Appendix B is printed by Lean (`scripts/ExtractStatements.lean`),
never copied by hand.  This script replaces the body of each code block with the printed text of
the declarations it lists, in the same order (the order and attribution are those of
`report_map.json`).  `variable`/`include` lines of a hand-written block are not kept: Lean's
printed signatures already carry every binder.

  sync_report_statements.py main.tex            # rewrite the blocks
  sync_report_statements.py main.tex --check    # exit 1 if any block differs from Lean's print
  sync_report_statements.py main.tex --env leancode --options '[...]'
                                                # write the blocks as \\begin{leancode}[...]

Blocks are recognised as `\\begin{ENV}` ... `\\end{ENV}` for ENV in --match-env (default: Verbatim
and the target --env).  The options after `\\begin{ENV}` are kept unless --options is given
(pass --options '' for none).  Only the lines inside the blocks of Appendix B (and, when the
environment or options change, the \\begin/\\end lines) are touched; the file is re-read
immediately before writing, so concurrent edits elsewhere in the file are preserved.

The pipeline:
  scripts/build_report_map.py main.tex           # report results -> Lean names (report_map.json)
  lake env lean scripts/ExtractStatements.lean   # Lean prints them (statements.json, Statements.lean)
  scripts/sync_report_statements.py main.tex     # the report shows what Lean printed
"""
import argparse
import difflib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import build_report_map as brm  # noqa: E402


def find_blocks(lines, envs):
    """Code blocks of Appendix B: dicts with entry_title, begin, end (line indices), env,
    options, chunks."""
    start, stop = brm.appendix_bounds(lines)
    env_alt = "|".join(re.escape(e) for e in envs)
    beg = re.compile(r"^\\begin\{(" + env_alt + r")\}(.*)$")
    title = None
    out = []
    i = start
    while i < stop:
        l = lines[i]
        m = re.match(r"^\\subsubsection\*\{(.*)\}\s*$", l) or re.match(r"^\\subsection\{(.*)\}", l)
        if m:
            title = m.group(1)
        m = beg.match(l)
        if m:
            env, opts = m.group(1), m.group(2)
            j = i + 1
            while not lines[j].startswith("\\end{" + env + "}"):
                j += 1
                if j >= stop:
                    sys.exit(f"ERROR: unterminated {env} block at line {i + 1}")
            out.append(dict(entry_title=title, begin=i, end=j, env=env, options=opts,
                            chunks=brm.chunk(lines[i + 1:j])))
            i = j
        i += 1
    return out


def expected_blocks(lines, envs, rmap, stmts):
    """Pair each block with its report_map block and compute the Lean-printed body."""
    blocks = find_blocks(lines, envs)
    # report_map blocks in order, keyed by entry title
    seq = [(e["entry_title"], b) for e in rmap for b in e["blocks"]]
    if len(seq) != len(blocks):
        sys.exit(f"ERROR: {len(blocks)} code blocks in Appendix B, {len(seq)} in report_map.json; "
                 "rebuild the map (scripts/build_report_map.py)")
    problems = []
    for blk, (title, mb) in zip(blocks, seq):
        if blk["entry_title"] != title:
            problems.append(f"line {blk['begin'] + 1}: entry '{blk['entry_title']}' vs map '{title}'")
            continue
        here = [c["name"] for c in blk["chunks"] if c["kind"] == "decl"]
        want = [d["as_written"] for d in mb if "name" in d]
        if here != want:
            problems.append(f"line {blk['begin'] + 1} ({title}): declarations {here} vs map {want}")
            continue
        texts = []
        for d in mb:
            if "name" not in d:
                continue
            s = stmts.get(d["name"])
            if s is None:
                problems.append(f"{d['name']} missing from statements.json; rerun ExtractStatements")
                continue
            texts.append(s["text"])
        blk["expected"] = "\n\n".join(texts).split("\n")
        blk["current"] = lines[blk["begin"] + 1:blk["end"]]
    if problems:
        sys.exit("ERROR: report and report_map.json disagree; rebuild the map:\n  " +
                 "\n  ".join(problems))
    return blocks


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("tex")
    ap.add_argument("--check", action="store_true", help="exit 1 if a block differs")
    ap.add_argument("--env", default="Verbatim", help="environment to write (default Verbatim)")
    ap.add_argument("--options", default=None,
                    help="options line after \\begin{ENV}, e.g. '[fontsize=\\footnotesize]'; "
                         "default: keep each block's own")
    ap.add_argument("--match-env", nargs="*", default=None,
                    help="environments recognised as code blocks (default: Verbatim and --env)")
    ap.add_argument("--map", default=str(ROOT / "report_map.json"))
    ap.add_argument("--statements", default=str(ROOT / "statements.json"))
    a = ap.parse_args()
    envs = a.match_env or sorted({"Verbatim", a.env})
    rmap = json.loads(pathlib.Path(a.map).read_text())
    stmts = json.loads(pathlib.Path(a.statements).read_text())
    tex = pathlib.Path(a.tex)

    lines = tex.read_text().split("\n")
    blocks = expected_blocks(lines, envs, rmap, stmts)
    differ = [b for b in blocks if b["current"] != b["expected"] or b["env"] != a.env or
              (a.options is not None and b["options"] != a.options)]
    if a.check:
        for b in differ:
            print(f"--- line {b['begin'] + 1}: {b['entry_title']}")
            sys.stdout.writelines(l + "\n" for l in difflib.unified_diff(
                b["current"], b["expected"], "report", "lean", lineterm="", n=1))
        print(f"{len(differ)} of {len(blocks)} blocks differ from Lean's print")
        sys.exit(1 if differ else 0)

    # write: re-read now, recompute positions on the fresh text, replace bottom-up; if the file
    # changes between this read and the write, start again
    for _ in range(5):
        text = tex.read_text()
        lines = text.split("\n")
        blocks = expected_blocks(lines, envs, rmap, stmts)
        n = 0
        for b in reversed(blocks):
            opts = b["options"] if a.options is None else a.options
            new = ["\\begin{" + a.env + "}" + opts] + b["expected"] + ["\\end{" + a.env + "}"]
            old = lines[b["begin"]:b["end"] + 1]
            new[-1] += old[-1][len("\\end{" + b["env"] + "}"):]  # keep text after \end{ENV}
            if new != old:
                lines[b["begin"]:b["end"] + 1] = new
                n += 1
        if tex.read_text() == text:
            tex.write_text("\n".join(lines))
            print(f"{n} of {len(blocks)} blocks rewritten from statements.json")
            return
    sys.exit("ERROR: main.tex keeps changing; not written")


if __name__ == "__main__":
    main()
