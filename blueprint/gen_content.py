#!/usr/bin/env python3
"""Generate blueprint/src/content.tex from the technical report.

The mathematics is copied from the LaTeX source of the technical report
"Testing stemmata against the evidence: Technical report" (Sections 3 to 9):
every numbered theorem, proposition, lemma and corollary with its proof, in
report order, together with the definitions the statements need.  The script
adds the blueprint annotations:

  \\lean{...}   from scripts/statements_selection.json (label -> main theorems),
               falling back to the theorems listed for the label in
               report_map.json;
  \\leanok      on every statement and proof (the whole report is formalised);
  \\uses{...}   on a statement: the definitions it needs (DEF_USES below);
               on a proof: the results it uses, i.e. the edges A -> B of the
               report's dependency map (figures/depmap/results.py, list E).

Citations become plain-text references, and references to report material
that is not in the blueprint (remarks, examples, tables, appendices, the
simulation sections) become "<number> of the report", read from main.aux.

Usage (from the repository root or from blueprint/):

  python3 blueprint/gen_content.py --report PATH/TO/report/main.tex \\
      --depmap PATH/TO/report/figures/depmap/results.py

The report itself is not part of this repository; the generated
src/content.tex is committed, so building the blueprint needs only that file.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

# Report definitions are unlabelled: label them by their optional title.
DEF_LABELS = {
    None: "def:split",
    "Collation": "def:collation",
    "Collation, support and the best-supported stemma": "def:collation",
    "Joint completability": "def:joint",
    "Margin": "def:gamma",
    "Attraction model": "def:attraction",
    "Irreversible model": "def:irreversible",
}

# Lean declarations formalising each definition.
DEF_LEAN = {
    "def:split": ["Stemma.Compat", "Stemma.PairwiseCompat", "Stemma.Splits.Nontriv"],
    "def:stemma": ["Phylogenetics.SplitsEquivalence.IsXTree", "Phylogenetics.SplitsEquivalence.splitSides",
                   "Stemma.Splits.IsSide", "Stemma.Splits.IsSystem", "Stemma.Splits.IsBinary"],
    "def:collation": ["Stemma.weight", "Stemma.IsOptimal", "Stemma.Splits.wt",
                      "Stemma.Splits.IsUniqueSolution"],
    "def:rooted": ["Stemma.Splits.Laminar", "Stemma.Rooted.Lam", "Stemma.Rooted.IsCluster",
                   "Stemma.Rooted.IsBinR"],
    "def:partial": ["Stemma.PSplit", "Stemma.overlapCompat"],
    "def:joint": ["Stemma.Extends", "Stemma.JointPair", "Stemma.Cutting.JointlyCompletable"],
    "def:gamma": ["Stemma.Margin.competitors", "Stemma.Margin.ratio", "Stemma.Margin.margin"],
    "def:attraction": ["Stemma.Mechanisms.read", "Stemma.Mechanisms.PropU", "Stemma.Mechanisms.PropR",
                       "Stemma.Attraction.wt", "Stemma.Attraction.omega"],
    "def:irreversible": ["Stemma.Irreversible.ones", "Stemma.Irreversible.pM",
                         "Stemma.Irreversible.Proposes", "Stemma.Irreversible.suppI"],
    "def:isolated": ["Stemma.Alpha.Isolated"],
}

DEF_TITLES = {
    "def:split": "Splits and compatibility",
    "def:stemma": "Stemma",
    "def:collation": "Collation, support and the best-supported stemma",
    "def:rooted": "Clusters and the rooted variant",
    "def:partial": "Partial splits and overlap-compatibility",
    "def:isolated": "Isolated pair",
}

# Definitions each definition and each result statement needs.
DEF_USES = {
    "def:stemma": ["def:split"],
    "def:collation": ["def:split"],
    "def:rooted": ["def:collation"],
    "def:partial": ["def:split"],
    "def:joint": ["def:partial"],
    "def:gamma": ["def:collation", "def:stemma"],
    "def:attraction": ["def:rooted", "def:stemma"],
    "def:irreversible": ["def:stemma", "def:collation"],
    "def:isolated": ["def:attraction"],
    "prop:buneman": ["def:split", "def:stemma"],
    "lem:facts": ["def:split", "def:stemma"],
    "lem:exclusive": ["def:collation"],
    "thm:universal": ["def:split"],
    "cor:nphard": ["def:collation"],
    "prop:triple": ["def:partial", "def:joint"],
    "thm:cutting": ["def:joint", "def:collation"],
    "lem:hall": ["def:stemma"],
    "thm:local": ["def:stemma", "def:collation"],
    "thm:global": ["def:stemma", "def:collation"],
    "prop:threshold": ["def:stemma", "def:collation"],
    "prop:rooted": ["def:rooted"],
    "thm:pairwise": ["def:gamma"],
    "lem:gamma": ["def:gamma"],
    "thm:consistency": ["def:gamma"],
    "cor:samplesize": ["def:gamma"],
    "prop:blocks": ["def:gamma"],
    "thm:gammaconf": ["def:gamma"],
    "prop:gammablocks": ["def:gamma"],
    "thm:fragmentary": ["def:gamma", "def:partial"],
    "prop:textillegible": ["def:gamma", "def:partial"],
    "thm:cuttingconsistency": ["def:gamma", "def:joint"],
    "prop:dimfree": ["def:gamma", "def:joint"],
    "prop:bediereffect": ["def:stemma", "def:collation"],
    "cor:tops": ["def:rooted", "def:collation"],
    "thm:bedier": ["def:stemma", "def:collation"],
    "prop:gap": ["def:stemma", "def:collation"],
    "prop:rival": ["def:collation"],
    "thm:mechanisms": ["def:attraction"],
    "cor:dominance": ["def:attraction"],
    "prop:modelbounds": ["def:irreversible"],
    "cor:modelglobal": ["def:irreversible", "def:gamma"],
    "prop:quartet": ["def:irreversible"],
    "cor:lba": ["def:irreversible"],
    "thm:coding": ["def:attraction", "def:gamma"],
    "prop:drift": ["def:attraction", "def:gamma"],
    "prop:multistate": ["def:attraction"],
    "prop:tworeading": ["def:attraction", "def:gamma"],
    "prop:alpha": ["def:isolated"],
    "prop:polytomynull": ["def:attraction"],
    "prop:size": ["def:split"],
    "prop:crossing": ["def:stemma"],
    "prop:five": ["def:split"],
    "thm:fpt": ["def:collation"],
}

KIND_NAMES = {"theorem": "Theorem", "proposition": "Proposition", "lemma": "Lemma",
              "corollary": "Corollary", "definition": "Definition"}


def die(msg: str) -> None:
    sys.exit(f"gen_content.py: {msg}")


# ---------------------------------------------------------------- inputs

def read_aux(path: Path) -> dict[str, str]:
    nums = {}
    for m in re.finditer(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}", path.read_text()):
        nums[m.group(1)] = m.group(2)
    return nums


def read_bib(path: Path) -> dict[str, str]:
    """key -> 'Author Year' (two authors joined by 'and', more by 'et al.')."""
    out = {}
    if not path.exists():
        return out
    text = path.read_text()
    for m in re.finditer(r"@\w+\{([^,\s]+),(.*?)\n\}", text, re.S):
        key, body = m.group(1), m.group(2)
        au = re.search(r"\bauthor\s*=\s*\{(.*)\},?\s*$", body, re.M)
        yr = re.search(r"\byear\s*=\s*\{?(\d{4})", body)
        names = []
        if au:
            for a in re.split(r"\s+and\s+", au.group(1)):
                a = a.strip()
                if a.startswith("{") and a.endswith("}"):
                    a = a[1:-1]
                last = a.split(",")[0].strip() if "," in a else a.split()[-1]
                names.append(last)
        if not names:
            who = key
        elif len(names) == 1:
            who = names[0]
        elif len(names) == 2:
            who = f"{names[0]} and {names[1]}"
        else:
            who = f"{names[0]} et al."
        out[key] = f"{who} {yr.group(1)}" if yr else who
    return out


def read_depmap(path: Path):
    ns: dict = {}
    exec(compile(path.read_text(), str(path), "exec"), ns)  # trusted local file
    return ns["R"], ns["E"]


# ---------------------------------------------------------------- text

def match_brace(s: str, i: int, open_: str = "{", close: str = "}") -> int:
    """s[i] == open_; return index just past the matching close."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "\\":
            continue
        if s[j] == open_ and (j == 0 or s[j - 1] != "\\"):
            depth += 1
        elif s[j] == close and (j == 0 or s[j - 1] != "\\"):
            depth -= 1
            if depth == 0:
                return j + 1
    die(f"unbalanced {open_}{close} at offset {i}")
    return -1


def paragraph_span(text: str, start_marker: str, from_marker: str | None = None):
    """(start, end) of the paragraph that contains start_marker; start is moved
    to from_marker if given (within the paragraph)."""
    i = text.find(start_marker)
    if i < 0:
        die(f"marker not found: {start_marker[:40]!r}")
    p0 = text.rfind("\n\n", 0, i)
    p0 = 0 if p0 < 0 else p0 + 2
    p1 = text.find("\n\n", i)
    p1 = len(text) if p1 < 0 else p1
    if from_marker:
        k = text.find(from_marker, p0, p1)
        if k < 0:
            die(f"marker not found in paragraph: {from_marker[:40]!r}")
        p0 = k
    return p0, p1


def wrap_definition(text: str, label: str, start_marker: str, from_marker=None,
                    drop: tuple[str, ...] = ()) -> str:
    p0, p1 = paragraph_span(text, start_marker, from_marker)
    body = text[p0:p1]
    for d in drop:
        if d not in body:
            die(f"{label}: text to drop not found: {d[:40]!r}")
        body = body.replace(d, "")
    title = DEF_TITLES[label]
    env = f"\\begin{{definition}}[{title}]\\label{{{label}}}\n{body.strip()}\n\\end{{definition}}"
    return text[:p0] + env + text[p1:]


def prepare(text: str) -> str:
    """Turn the prose definitions of the report into definition environments."""
    text = "\n".join(l for l in text.split("\n") if not l.lstrip().startswith("%"))
    # The stemma: the paragraph after the compatibility remark.
    text = wrap_definition(text, "def:stemma", r"An (unrooted) \emph{stemma}")
    # Support, conflict graph and the estimator, merged into the collation definition.
    i = text.find(r"\begin{definition}[Collation]")
    j = text.find(r"\end{definition}", i)
    k = text.find(r"Each reading $\rho$ of $u$ \emph{proposes}", j)
    if min(i, j, k) < 0 or text[j + len(r"\end{definition}"):k].strip():
        die("collation definition and support paragraph are not adjacent")
    p1 = text.find("\n\n", k)
    support = text[k:p1]
    text = (text[:i] + r"\begin{definition}[" + DEF_TITLES["def:collation"] + "]"
            + text[i + len(r"\begin{definition}[Collation]"):j]
            + "\n" + support.strip() + "\n" + r"\end{definition}" + text[p1:])
    # Clusters (rooted variant).
    text = wrap_definition(text, "def:rooted", r"When a reference reading $\rho_u^\ast$")
    # Partial splits: from the sentence that introduces them.
    text = wrap_definition(text, "def:partial", r"At such places a unit proposes \emph{partial} splits",
                           from_marker=r"At such places a unit proposes")
    # Rates of the random model, merged into the margin definition.
    i = text.find(r"Let the units be independent and identically distributed")
    j = text.find(r"Each $w(\sigma)$ is binomial with parameters $L$ and $m_\sigma$.", i)
    if min(i, j) < 0:
        die("rates paragraph not found")
    j += len(r"Each $w(\sigma)$ is binomial with parameters $L$ and $m_\sigma$.")
    rates = text[i:j]
    rates = re.sub(r"\s*\(Independence alone does not suffice:.*?\)\s*(?=Let )", " ", rates, flags=re.S)
    if "Independence alone" in rates:
        die("could not drop the independence aside from the rates paragraph")
    m = text.find(r"\begin{definition}[Margin]\label{def:gamma}")
    if m < 0:
        die("margin definition not found")
    head = r"\begin{definition}[Margin]\label{def:gamma}"
    text = text[:m] + head + "\n" + rates.strip() + "\n\nFor binary $T$, the \\emph{margin} is" \
        + text[m + len(head):].replace("\nFor binary $T$,\n", "\n", 1)
    # Isolated pairs: from "Call a pair of leaves" to the end of the paragraph.
    text = wrap_definition(text, "def:isolated", r"Call a pair of leaves $i,j$ \emph{isolated}",
                           from_marker=r"Call a pair of leaves")
    return text


ENV_RE = re.compile(r"\\begin\{(theorem|proposition|lemma|corollary|definition)\}")
HEAD_RE = re.compile(r"\\(section|subsection)\*?\{")


def parse(text: str):
    """Yield ('head', level, title, label) and ('env', kind, title, label, body, proof)."""
    items = []
    pos = 0
    while True:
        me = ENV_RE.search(text, pos)
        mh = HEAD_RE.search(text, pos)
        nxt = min([m for m in (me, mh) if m], key=lambda m: m.start(), default=None)
        if nxt is None:
            break
        if nxt is mh:
            e = match_brace(text, mh.end() - 1)
            title = text[mh.end():e - 1]
            label = None
            ml = re.match(r"\s*\\label\{([^}]*)\}", text[e:])
            if ml:
                label = ml.group(1)
                e += ml.end()
            items.append(("head", mh.group(1), title, label))
            pos = e
            continue
        kind = me.group(1)
        p = me.end()
        title = None
        if text[p] == "[":
            q = match_brace(text, p, "[", "]")
            title = text[p + 1:q - 1]
            p = q
        endtok = f"\\end{{{kind}}}"
        e = text.find(endtok, p)
        body = text[p:e]
        label = None
        ml = re.match(r"\s*\\label\{([^}]*)\}", body)
        if ml:
            label = ml.group(1)
            body = body[ml.end():]
        pos = e + len(endtok)
        proof = None
        # The proof follows the statement, possibly after one paragraph of comment
        # (as for Theorem 9.4); never across another environment or heading.
        mp = re.match(r"\s*\\begin\{proof\}", text[pos:])
        if not mp:
            k = text.find(r"\begin{proof}", pos)
            if k >= 0 and "\\begin{" not in text[pos:k] and not HEAD_RE.search(text[pos:k]):
                mp = re.match(r"[\s\S]*?\\begin\{proof\}", text[pos:])
        if mp:
            s = pos + mp.end()
            f = text.find(r"\end{proof}", s)
            proof = text[s:f]
            pos = f + len(r"\end{proof}")
        items.append(("env", kind, title, label, body.strip("\n"), proof.strip("\n") if proof else None))
    return items


class Translator:
    def __init__(self, aux: dict, bib: dict, known: set[str]):
        self.aux, self.bib, self.known = aux, bib, known
        self.dropped_refs: set[str] = set()
        self.cites: set[str] = set()

    def cite(self, m: re.Match) -> str:
        opt, keys = m.group(1), m.group(2)
        parts = []
        for k in keys.split(","):
            k = k.strip()
            self.cites.add(k)
            parts.append(self.bib.get(k, k))
        s = "; ".join(parts)
        if opt:
            s += ", " + opt
        return f"({s})"

    def ref(self, m: re.Match) -> str:
        cmd, lab = m.group(1), m.group(2)
        if lab in self.known:
            return m.group(0)
        if lab not in self.aux:
            die(f"reference to unknown label {lab}")
        self.dropped_refs.add(lab)
        num = self.aux[lab]
        return (f"({num}) of the report" if cmd == "eqref" else f"{num} of the report")

    def __call__(self, s: str) -> str:
        s = re.sub(r"\\cite(?:\[([^\]]*)\])?\{([^}]*)\}", self.cite, s)
        s = re.sub(r"\\(ref|eqref)\{([^}]*)\}", self.ref, s)
        s = s.replace(r"[label=(\roman*)]", "[(i)]").replace(r"[label=(\alph*)]", "[(a)]") \
             .replace(r"[label=\arabic*.]", "[1.]").replace(r"[label=(\arabic*)]", "[(1)]")
        if "label=" in s:
            die("unhandled enumerate label option: " + s[s.find("label="):][:40])
        return s


# ---------------------------------------------------------------- main

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--report", required=True, type=Path, help="report main.tex")
    ap.add_argument("--depmap", required=True, type=Path, help="report figures/depmap/results.py")
    ap.add_argument("--selection", type=Path, default=ROOT / "scripts" / "statements_selection.json")
    ap.add_argument("--map", type=Path, default=ROOT / "report_map.json")
    ap.add_argument("--statements", type=Path, default=ROOT / "statements.json")
    ap.add_argument("--out", type=Path, default=HERE / "src" / "content.tex")
    a = ap.parse_args()

    src = a.report.read_text()
    aux = read_aux(a.report.with_suffix(".aux"))
    bib = read_bib(a.report.parent / "refs.bib")
    R, E = read_depmap(a.depmap)
    selection = {e["label"]: e for e in json.loads(a.selection.read_text())}
    rmap = json.loads(a.map.read_text())
    statements = json.loads(a.statements.read_text())

    i0 = src.find(r"\section{Preliminaries}")
    i1 = src.find(r"\section{Simulations}")
    if i0 < 0 or i1 < 0:
        die("could not find the Preliminaries .. Simulations range")
    text = prepare(src[i0:i1])
    items = parse(text)

    # Labels of the definitions; results must all carry a label.
    envs = []
    for it in items:
        if it[0] != "env":
            continue
        _, kind, title, label, body, proof = it
        if kind == "definition":
            if label is None:
                if title not in DEF_LABELS:
                    die(f"unlabelled definition with title {title!r}")
                label = DEF_LABELS[title]
        elif label is None:
            die(f"unlabelled {kind} {title!r}")
        envs.append((kind, title, label, body, proof))

    key_of = {lab: key for key, lab, *_ in R}
    kind_of = {lab: kind for kind, _, lab, _, _ in envs}
    lab_of = {key: lab for key, lab, *_ in R}
    result_labels = [lab for kind, _, lab, _, _ in envs if kind != "definition"]
    missing = [lab for lab in key_of if lab not in result_labels and lab.split(":")[0] != "sec"]
    if missing:
        die(f"results of the dependency map not found in the report: {missing}")
    extra = [lab for lab in result_labels if lab not in key_of]
    if extra:
        die(f"results of the report missing from the dependency map: {extra}")

    proof_uses: dict[str, list[str]] = {}
    for s, t in E:
        ls, lt = lab_of[s], lab_of[t]
        if ls.startswith("sec:") or lt.startswith("sec:"):
            continue  # the pruning rule is a heuristic section, not a result
        proof_uses.setdefault(lt, []).append(ls)

    def lean_names(label: str) -> list[str]:
        if label.startswith("def:"):
            return DEF_LEAN[label]
        if label in selection:
            return selection[label]["theorems"]
        names = []
        for e in rmap:
            if label in (e.get("labels") or []):
                names += [d for d in e["decls"] if statements.get(d, {}).get("kind") == "theorem"]
        if not names:
            die(f"no Lean declaration for {label}")
        return list(dict.fromkeys(names))

    # Which headings get emitted: only those with environments under them.
    known = {lab for _, _, lab, _, _ in envs} | {"eq:mwis"}
    chap_has, sec_has = set(), set()
    cur_c = cur_s = None
    for it in items:
        if it[0] == "head":
            if it[1] == "section":
                cur_c, cur_s = it, None
            else:
                cur_s = it
        else:
            chap_has.add(id(cur_c))
            if cur_s is not None:
                sec_has.add(id(cur_s))
    for it in items:
        if it[0] == "head" and it[3] and (id(it) in chap_has or id(it) in sec_has):
            known.add(it[3])

    tr = Translator(aux, bib, known)
    out = []
    out.append("% GENERATED by blueprint/gen_content.py from the technical report;"
               " do not edit by hand.\n")
    out.append(
        "This blueprint lays out the mathematics of the technical report "
        "\\emph{Testing stemmata against the evidence: Technical report} "
        "(Metamorphoses of Civilization Collection, 2026, "
        "\\href{https://doi.org/10.5281/zenodo.24405385}{doi:10.5281/zenodo.24405385}), "
        "Sections 3 to 9, and links every result to its proof in the Lean library "
        "\\href{https://github.com/metamorphoses-collection/stemma-lean}{stemma-lean}. "
        "Statements and proofs are those of the report. Chapters carry the report's section "
        "numbers. The blueprint leaves out the report's remarks and examples, which the report "
        "numbers with its results, so within a chapter the numbers differ and each title gives "
        "the report's number. The dependency graph is that of the report's Appendix A: "
        "an arrow from one result to another means that the second result's proof uses the first. "
        "Every result and every definition is formalised and every proof is complete in Lean, "
        "with no \\texttt{sorry} and only the standard axioms.\n")
    out.append("\\setcounter{chapter}{2}\n")
    n_res = n_def = n_uses_stmt = n_uses_proof = 0
    all_names: list[str] = []
    for it in items:
        if it[0] == "head":
            _, level, title, label = it
            if level == "section" and id(it) in chap_has:
                out.append(f"\n\\chapter{{{tr(title)}}}" + (f"\\label{{{label}}}" if label else "") + "\n")
            elif level == "subsection" and id(it) in sec_has:
                out.append(f"\n\\section{{{tr(title)}}}" + (f"\\label{{{label}}}" if label else "") + "\n")
            continue
        _, kind, title, label, body, proof = it
        if kind == "definition" and label is None:
            label = DEF_LABELS[title]
        names = lean_names(label)
        all_names += names
        if kind == "definition":
            n_def += 1
            t = DEF_TITLES.get(label, title)
            num = aux.get(label)
            shown = t if not num or label not in aux else f"{t}; Definition {num} of the report"
        else:
            n_res += 1
            # The report's own title, unless it carries a citation (then the short title
            # of statements_selection.json, e.g. "Buneman").
            t = title if title and "\\cite" not in title else \
                (selection.get(label, {}).get("title") or "")
            num = aux[label]
            shown = f"{t}; {KIND_NAMES[kind]} {num} of the report" if t else \
                f"{KIND_NAMES[kind]} {num} of the report"
        su = DEF_USES.get(label, [])
        if kind != "definition" and not su:
            die(f"no definitions listed for {label}")
        n_uses_stmt += len(su)
        lines = [f"\\begin{{{kind}}}[{tr(shown)}]", f"\\label{{{label}}}",
                 f"\\lean{{{', '.join(names)}}}", "\\leanok"]
        if su:
            lines.append(f"\\uses{{{', '.join(su)}}}")
        lines.append(tr(body.strip()))
        lines.append(f"\\end{{{kind}}}")
        if kind != "definition":
            pu = proof_uses.get(label, [])
            n_uses_proof += len(pu)
            lines.append("\\begin{proof}")
            lines.append("\\leanok")
            if pu:
                lines.append(f"\\uses{{{', '.join(pu)}}}")
            if proof is None:
                cited = re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}", title or "")
                refs = "; ".join(bib.get(k.strip(), k.strip()) for c in cited for k in c.split(","))
                if pu:
                    via = " and ".join(f"{KIND_NAMES[kind_of[u]]}~\\ref{{{u}}}" for u in pu)
                    lines.append(f"The report gives no separate proof: it follows from {via}. "
                                 "The Lean library proves it in full.")
                else:
                    lines.append("Classical" + (f" ({refs})" if refs else "") + ". The report states it "
                                 "without proof; the Lean library proves it in full.")
            else:
                lines.append(tr(proof.strip()))
            lines.append("\\end{proof}")
        out.append("\n" + "\n".join(lines) + "\n")

    a.out.write_text("".join(out))
    absent = sorted({n for n in all_names if n not in statements})
    print(f"wrote {a.out}")
    print(f"results {n_res}, definitions {n_def}, statement \\uses edges {n_uses_stmt}, "
          f"proof \\uses edges {n_uses_proof}, Lean names {len(all_names)} ({len(set(all_names))} distinct)")
    print(f"references turned into report numbers: {', '.join(sorted(tr.dropped_refs))}")
    print(f"citations turned into text: {len(tr.cites)}")
    if absent:
        print("Lean names not in statements.json (check with checkdecls): " + ", ".join(absent))


if __name__ == "__main__":
    main()
