# scripts

| Script | Run | What it does |
|---|---|---|
| `Audit.lean` | `lake env lean scripts/Audit.lean` | Axiom audit: every declaration of `StemmaLean` (vendored files and `Statements.lean` included) uses only `propext`, `Classical.choice`, `Quot.sound`. |
| `build_report_map.py` | `scripts/build_report_map.py path/to/main.tex` | Parses the code blocks of the report's Appendix B and maps each report result (its `\ref` label, number from `main.aux`, entry title) to the fully qualified Lean declarations it shows. Writes `report_map.json`; refreshes number, kind and title in `statements_selection.json`. Fails on an unknown or ambiguous name. |
| `ExtractStatements.lean` | `lake env lean scripts/ExtractStatements.lean` | Lean prints every declaration of `report_map.json` (`ppSignature`, in its source file's namespace and `open`s, width 84, `pp.unicode.fun`), with its file and line range, into `statements.json`; and regenerates `StemmaLean/Statements.lean` from `statements_selection.json`. Unknown names fail. |
| `statements_selection.json` | edited by hand (theorem lists only) | For each numbered result of the report, by label, the main theorem(s) restated in `Statements.lean`. |
| `sync_report_statements.py` | `scripts/sync_report_statements.py path/to/main.tex [--check] [--env E --options '[...]']` | Rewrites the body of every Appendix B code block from `statements.json`, keeping the block's order of declarations and its options line; `--check` exits 1 if any block differs from what Lean prints. `--env`/`--options` write another environment (e.g. a highlighted `leancode`); blocks are found under `Verbatim` and `--env`. Only the lines of the blocks are touched, and the file is re-read just before writing. |

## The single audit surface

`StemmaLean/Statements.lean` is imported by `StemmaLean.lean`, so `lake build` checks it and the
axiom audit covers it. For each numbered result of the report it restates the main theorems in
full, in report order, each proved by the library theorem (`:= @Stemma.… args`), and pins first
the definitions of the report's encoding that those statements use (`… := rfl`). If a library
statement or definition changes, `lake build` fails there. Regenerate it with
`ExtractStatements.lean`; never edit it by hand. CI regenerates it and fails if the committed
file is stale.

## The report's Lean statements are printed, not copied

The report lives in another repository, so its check cannot run in this CI. After any change to
a statement, in this order:

```
scripts/build_report_map.py  <report-source-dir>/main.tex
lake env lean scripts/ExtractStatements.lean
scripts/sync_report_statements.py <report-source-dir>/main.tex --env leancode --options ''
scripts/sync_report_statements.py <report-source-dir>/main.tex --env leancode --options '' --check
```

The printed blocks use `↦`, `⋯` (an omitted proof), `⟂ᵢ` and `ᵢ`; a LaTeX preamble with
`inputenc` needs a `\newunicodechar` for each.

Set `STATEMENTS_DEBUG=1` to see why a restatement fell back to `#check`.
