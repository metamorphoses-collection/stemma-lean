/-
Extract the Lean statements quoted in the technical report.

Reads `report_map.json` (built by `scripts/build_report_map.py` from Appendix B of the report)
and, for every declaration named there,

* pretty-prints it the way the report shows it (`Lean.PrettyPrinter.ppSignature`, in the
  namespace and `open` scope of its source file, `pp.unicode.fun`, width 100): theorems as their
  signature, definitions with their body, structures and inductives with their fields and
  constructors;
* records its source file and line range (`Lean.findDeclarationRanges?`);
* writes everything to `statements.json`, which `scripts/sync_report_statements.py` copies into
  the report;
* regenerates `StemmaLean/Statements.lean`, the single audit surface: every quoted theorem is
  restated in full (`theorem «Report.N».… : <statement> := @…`) and every quoted definition is
  pinned by an equation proved by `rfl`.  Each restatement is elaborated here first; one that
  does not re-elaborate from its printed form falls back to `#check`, and is listed.

Unknown names fail loudly.  Run from the repository root:
  `lake env lean scripts/ExtractStatements.lean`
This script imports every library module except `StemmaLean.Statements`, so that it still runs
when a change to the library has broken `Statements.lean`.
-/
import Lean
import StemmaLean.Alpha
import StemmaLean.Attraction
import StemmaLean.Basic
import StemmaLean.Bernstein
import StemmaLean.BinaryTree
import StemmaLean.Blocks
import StemmaLean.Buneman
import StemmaLean.Chernoff
import StemmaLean.ClopperPearson
import StemmaLean.Coding
import StemmaLean.CodingGen
import StemmaLean.CodingLimit
import StemmaLean.Consistency
import StemmaLean.Crossing
import StemmaLean.Cutting
import StemmaLean.CuttingDimFree
import StemmaLean.CuttingIllegible
import StemmaLean.CuttingPlanes
import StemmaLean.CuttingRemark
import StemmaLean.Dominance
import StemmaLean.Drift
import StemmaLean.DriftGen
import StemmaLean.Dynamic
import StemmaLean.Five
import StemmaLean.Fragmentary
import StemmaLean.FragmentaryUnits
import StemmaLean.GammaBlocks
import StemmaLean.GammaConf
import StemmaLean.GapThreshold
import StemmaLean.Irreversible
import StemmaLean.Margin
import StemmaLean.Mechanisms
import StemmaLean.NPComplete
import StemmaLean.NPHard
import StemmaLean.PartialSplits
import StemmaLean.Polytomy
import StemmaLean.PolytomyMix
import StemmaLean.PolytomyNull
import StemmaLean.Quartet
import StemmaLean.Reduction
import StemmaLean.Resolve
import StemmaLean.Rival
import StemmaLean.Rooted
import StemmaLean.Size
import StemmaLean.Splits
import StemmaLean.TextIllegible
import StemmaLean.Universal
import StemmaLean.Vendor.SplitsEquivalence
import StemmaLean.Vendor.XTree
import StemmaLean.MultiAttraction
import StemmaLean.RootedConsistency
import StemmaLean.TwoReading
import StemmaLean.RootedTop

namespace ExtractStatements

open Lean Meta Elab Command PrettyPrinter Delaborator SubExpr

/-- Line width of the printed statements: the report's footnotesize code blocks hold about 92
characters, less inside indented entries, so 84 avoids continuation marks. -/
def width : Nat := 84

/-- Line width of `Statements.lean` (Mathlib's limit). -/
def auditWidth : Nat := 100

def reportOpts (o : Options) : Options :=
  (((o.set `pp.unicode.fun true).set `format.width width).set `pp.fullNames false)

/-- Options for the restatements of `Statements.lean`: full names, binder types everywhere, so
that the printed form re-elaborates with no `open` in scope. -/
def auditOpts (o : Options) : Options :=
  ((((o.set `pp.unicode.fun true).set `pp.fullNames true).set `pp.funBinderTypes true).set
    `format.width auditWidth).set `pp.mvars false

/-- In the audit form (recognised by `pp.mvars false`, which only it sets), print `Finset.filter` as an application:
Mathlib's `{x ∈ s | p}` notation elaborates back to a `Finset` only when the expected type is
known, which it is not under field notation or on one side of `=`. -/
@[app_delab Finset.filter] def delabFinsetFilterAudit : Delab := do
  unless !(← getOptions).getBool `pp.mvars true do failure
  let #[_, _, _, _] := (← getExpr).getAppArgs | failure
  let p ← withNaryArg 1 delab
  let t ← withNaryArg 3 delab
  let f := mkIdent ``Finset.filter
  `($f $p $t)

def indent (k : Nat) (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map fun l => if l.isEmpty then l else "".pushn ' ' k ++ l)

def lastLineLen (s : String) : Nat := ((s.splitOn "\n").getLast!).length

/-- The module of a constant and its source file. -/
def sourceOf (n : Name) : CoreM (Name × System.FilePath) := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? n | throwError "{n}: not from an imported module"
  let m := env.header.moduleNames[idx.toNat]!
  let path := (m.components.foldl (fun p c => p / c.toString) ("." : System.FilePath)).addExtension "lean"
  return (m, path)

/-- Replay the `namespace`/`section`/`end`/`open` lines of a source file above line `upto`
(1-based), skipping comments, so that names print as they do in the source. -/
def replayScope (src : Array String) (upto : Nat) : CommandElabM Unit := do
  let mut inComment := false
  for i in [0:upto - 1] do
    let t := (src[i]!).trimAsciiEnd.toString
    if inComment then
      if (t.splitOn "-/").length > 1 then inComment := false
      continue
    if t.startsWith "/-" then
      if (t.splitOn "-/").length == 1 then inComment := true
      continue
    let isCmd := t.startsWith "namespace " || t == "section" || t.startsWith "section " ||
      t.startsWith "noncomputable section" || t == "end" || t.startsWith "end " ||
      (t.startsWith "open " && !t.endsWith " in")
    if isCmd then
      match Parser.runParserCategory (← getEnv) `command t with
      | .ok stx => elabCommand stx
      | .error e => throwError "cannot parse scope line {i+1} `{t}`: {e}"

/-- `ppSignature`, with the declaration's name printed as written in its source. -/
def sigWith (n : Name) (asWritten : Name) (col suffix : Nat) (w : Nat := width) : MetaM String := do
  let decl ← getConstInfo n
  let e := Expr.const n (decl.levelParams.map mkLevelParam)
  let (stx, _) ← delabCore e (delab := Delaborator.delabConstWithSignature)
  let stx := stx.raw.setArg 0 (mkIdent asWritten)
  return (← ppTerm ⟨stx⟩).pretty (w - suffix) (column := col)

/-- The leading binders that `ppSignature` shows before the colon (the rule of
`delabForallParamsWithSignature`): anonymous instances, dependent binders, and named arrows
whose name is accessible and not yet used.  For each, the argument that passes it on: its
name, or `_` for an instance or an unnameable binder. -/
def shownBinders (type : Expr) : Array String :=
  go type {} #[]
where go : Expr → NameSet → Array String → Array String
  | .forallE nm _ b bi, used, acc =>
    if bi.isInstImplicit && nm.hasMacroScopes then go b used (acc.push "_")
    else if b.hasLooseBVar 0 || !(nm.hasMacroScopes || used.contains nm) then
      let arg := if nm.hasMacroScopes || used.contains nm || bi.isInstImplicit then "_"
        else nm.toString
      go b (used.insert nm) (acc.push arg)
    else acc
  | _, _, acc => acc

def ppBody (value : Expr) (k : Nat) : MetaM String := do
  lambdaBoundedTelescope value k fun xs body => do
    let body ← if xs.size < k then
        -- an eta-reduced definition: apply it to the remaining binders
        forallBoundedTelescope (← inferType body) (k - xs.size) fun ys _ =>
          return (mkAppN body ys).headBeta
      else pure body
    return (← Meta.ppExpr body).pretty (width - 2)

/-- `sig :=` and the body, on one line if it fits, else the body on the next lines. -/
def withBody (sig body : String) (w : Nat := width) : String :=
  if !body.contains '\n' && lastLineLen sig + 4 + body.length ≤ w then
    sig ++ " := " ++ body
  else sig ++ " :=\n" ++ indent 2 body

/-- The text of a declaration as the report shows it. -/
def reportText (n : Name) (asWritten : Name) (keyword : String) (src : Array String)
    (lineEnd : Nat) : MetaM (String × String) := do
  let env ← getEnv
  let info ← getConstInfo n
  let nc := if isNoncomputable env n then "noncomputable " else ""
  let pre := match info with
    | .thmInfo _ => keyword ++ " "
    | .defnInfo _ => nc ++ (if keyword == "abbrev" then "abbrev " else "def ")
    | _ => if isStructure env n then "structure " else "inductive "
  let suffix := match info with
    | .defnInfo _ => 3   -- " :="
    | .inductInfo _ => if isStructure env n then 6 else 0   -- " where"
    | _ => 0
  let sig ← sigWith n asWritten pre.length suffix
  match info with
  | .thmInfo _ => return ("theorem", s!"{pre}{sig}")
  | .axiomInfo _ => throwError "{n} is an axiom"
  | .defnInfo d =>
    let k := (shownBinders d.type).size
    -- a recursive definition is compiled (`brecOn`, `WellFounded.fix`): print its unfolding
    -- equation's right-hand side, a `match`, instead of the compiled term
    let compiled := d.value.find? (fun e => e.isConstOf ``Nat.brecOn || e.isConstOf ``WellFounded.fix ||
      (e.isConst && e.constName!.isPrefixOf n == false && n.isPrefixOf e.constName! &&
        e.constName! != n)) |>.isSome
    let body ← if compiled then
        match ← Meta.getUnfoldEqnFor? n (nonRec := true) with
        | some eqn =>
          let ty ← inferType (← mkConstWithLevelParams eqn)
          forallTelescope ty fun xs eq => do
            let some (_, _, rhs) := eq.eq? | ppBody d.value k
            let rhs ← mkLambdaFVars xs[k:] rhs
            return (← Meta.ppExpr rhs).pretty (width - 2)
        | none => ppBody d.value k
      else ppBody d.value k
    return ("def", withBody s!"{pre}{sig}" body)
  | .inductInfo iv =>
    -- a `deriving` clause is not recorded in the environment: take it from the source lines at
    -- the end of the declaration, with their indentation
    let derivingLine := Id.run do
      let mut r := ""
      for j in [lineEnd - 1:min (lineEnd + 1) src.size] do
        let raw := (src[j]!).trimAsciiEnd.toString
        if raw.trimAscii.toString.startsWith "deriving " then r := "\n" ++ raw
      return r
    if isStructure env n then
      let ctor ← getConstInfoCtor iv.ctors.head!
      let fields ← forallTelescope ctor.type fun xs _ => do
        let mut out := #[]
        for x in xs[iv.numParams:] do
          let d ← x.fvarId!.getDecl
          let ty := (← Meta.ppExpr d.type).pretty (width - 2 - d.userName.toString.length - 3)
          out := out.push s!"  {d.userName} : {(indent 4 ty).drop 4 |>.toString}"
        return out
      return ("structure", s!"structure {sig} where\n" ++ "\n".intercalate fields.toList ++ derivingLine)
    else
      let mut ctors := #[]
      for c in iv.ctors do
        let ci ← getConstInfoCtor c
        let t ← forallBoundedTelescope ci.type iv.numParams fun _ body => do
          return (← Meta.ppExpr body).pretty (width - 4)
        ctors := ctors.push s!"  | {c.componentsRev.head!} : {t}"
      return ("inductive", s!"inductive {sig}\n" ++ "\n".intercalate ctors.toList ++ derivingLine)
  | _ => throwError "{n}: unsupported kind of declaration"

/-- The restatement in `Statements.lean`, or `none` for a structure/inductive (`#check`).
A theorem is restated with its own signature, under the name `target`, and proved by applying
the library theorem to the binders; a definition `f` is pinned by `target xs : f xs = body := rfl`,
printed as the signature of a temporary axiom of that type. -/
def auditText (n : Name) (target : Name) : MetaM (Option String) := do
  let info ← getConstInfo n
  match info with
  | .thmInfo t =>
    let sig ← sigWith n target "theorem ".length 3 auditWidth
    let args := shownBinders t.type
    let app := " ".intercalate (s!"@{n}" :: args.toList)
    return some (withBody s!"theorem {sig}" app auditWidth)
  | .defnInfo d =>
    let k := (shownBinders d.type).size
    let eqn ← lambdaBoundedTelescope d.value k fun xs body => do
      let lhs := mkAppN (.const n (d.levelParams.map mkLevelParam)) xs
      let body := if xs.size < k then lhs else body
      mkForallFVars xs (← mkEq lhs body)
    withoutModifyingEnv do
      addDecl (Declaration.axiomDecl
        { name := target, levelParams := d.levelParams, type := eqn, isUnsafe := false })
      let sig ← sigWith target target "theorem ".length 3 auditWidth
      return some (withBody s!"theorem {sig}" "rfl" auditWidth)
  | _ => return none

/-- Elaborate `txt` as commands.  On success keep the new declaration (so later restatements are
checked against the same environment as in the generated file) and return `true`; on failure
restore the state. -/
def elaborates (txt : String) : CommandElabM Bool := do
  let s ← get
  modify fun st => { st with messages := {} }
  let ok ← try
      match Parser.runParserCategory (← getEnv) `command txt with
      | .ok stx =>
        -- synchronously: an asynchronous proof would report its errors too late to be seen here
        withScope (fun sc => { sc with opts := sc.opts.set `Elab.async false }) <| elabCommand stx
        let msgs := (← get).messages
        if msgs.hasErrors && (← IO.getEnv "STATEMENTS_DEBUG").isSome then
          for m in msgs.toList do
            if m.severity == .error then
              IO.eprintln s!"[restatement failed] {(← m.toString).take 600}\n<<<{txt}>>>"
        pure !msgs.hasErrors
      | .error _ => pure false
    catch _ => pure false
  if ok then modify fun st => { st with messages := s.messages } else set s
  return ok

def strField (j : Json) (k : String) : CommandElabM String :=
  match j.getObjValAs? String k with
  | .ok s => pure s
  | .error e => throwError "report_map.json: {e}"

def libraryModules : IO (Array Name) := do
  let files ← System.FilePath.walkDir "StemmaLean"
  let mut out := #[]
  for f in files do
    if f.extension == some "lean" then
      let comps := (f.withExtension "").components
      out := out.push (comps.foldl (fun n c => Name.str n c) .anonymous)
  return out

/-- The current scope as one `open … in` prefix: the namespaces the declaration sits in, and
the namespaces its source file opens, all fully qualified. -/
def scopePrefix : CommandElabM String := do
  let sc ← getScope
  let mut nss : Array String := #[]
  let mut ns := sc.currNamespace
  while !ns.isAnonymous do
    nss := #[ns.toString] ++ nss
    ns := ns.getPrefix
  let mut hid : Array String := #[]
  for d in sc.openDecls.reverse do
    match d with
    | .simple n [] => unless nss.contains n.toString do nss := nss.push n.toString
    | .simple n ex =>
      let hidden := " ".intercalate (ex.map toString)
      hid := hid.push s!"open {n} hiding {hidden} in\n"
    | .explicit _ _ => pure ()
  -- `open A B … in`, wrapped at the line width
  let mut lines : Array String := #["open"]
  for x in nss do
    if (lines.back! ++ " " ++ x).length > width - 3 then lines := lines.push ("    " ++ x)
    else lines := lines.modify (lines.size - 1) (· ++ " " ++ x)
  let opened := "\n".intercalate lines.toList
  return (if nss.isEmpty then "" else s!"{opened} in\n") ++
    String.join hid.toList

structure Placed where
  text : String
  form : String   -- "restated" | "pinned" | "check"

/-- Find a form of the restatement of `n` (as `target`) that re-elaborates: first in the
source's scope with short names, then with full names, each with and without `Classical` and
`pp.analyze`.  Falls back to `#check`. -/
def placeAudit (n target : Name) (header : String) (src : Array String) (line : Nat)
    (s0 : Command.State) : CommandElabM Placed := do
  replayScope src line
  let pre ← scopePrefix
  -- printed forms, most readable first: short names in the source's scope, then full names;
  -- `pp.analyze` adds the annotations a form may need to re-elaborate; proofs inside a statement
  -- are printed only as a last resort
  let short := fun (o : Options) => (auditOpts o).set `pp.fullNames false
  let mut inScope : Array (Option String) := #[]
  for pf in [false, true] do
    for an in [false, true] do
      for fb in [false, true] do
        inScope := inScope.push (← liftTermElabM <| withOptions
          (fun o => (((short o).set `pp.analyze an).set `pp.proofs pf).set `pp.funBinderTypes fb) <|
            auditText n target)
  set s0
  let mut global : Array (Option String) := #[]
  for pf in [false, true] do
    for an in [false, true] do
      for fb in [false, true] do
        global := global.push (← liftTermElabM <| withOptions
          (fun o => (((auditOpts o).set `pp.analyze an).set `pp.proofs pf).set `pp.funBinderTypes fb) <|
            auditText n target)
  let cl := "open scoped Classical in\n"
  let isThm := (← getConstInfo n).isThm
  let mut tries : Array String := #[]
  for i in [0:8] do
    for (p, t?) in [(pre, inScope[i]!), (pre ++ cl, inScope[i]!), ("", global[i]!), (cl, global[i]!)] do
      if let some t := t? then
        unless (t.splitOn "⋯").length > 1 do tries := tries.push (p ++ header ++ "\n" ++ t)
  for full in tries do
    if ← elaborates full then
      return ⟨full, if isThm then "restated" else "pinned"⟩
  return ⟨header.replace "/--" "/-" ++ s!"\n#check @{n}", "check"⟩

/-- The library definitions a statement mentions (not theorems, projections, instances or
auxiliary declarations), in order of first occurrence. -/
def defsUsed (n : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let info ← getConstInfo n
  let mut out := #[]
  for c in info.type.getUsedConstants do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`StemmaLean).isPrefixOf m do continue
    if c.isInternal || (← isProjectionFn c) || isInstanceCore env c then continue
    match env.find? c with
    | some (.defnInfo _) | some (.inductInfo _) => out := out.push c
    | _ => pure ()
  return out

def readJsonArr (file : String) : CommandElabM (Array Json) := do
  let raw ← IO.FS.readFile file
  match Json.parse raw with
  | .ok j => match j.getArr? with
    | .ok a => pure a
    | .error e => throwError "{file}: {e}"
  | .error e => throwError "{file}: {e}"

def run : CommandElabM Unit := do
  let env ← getEnv
  -- every library module except `Statements` must be loaded, or names could go missing
  for m in ← libraryModules do
    if m != `StemmaLean.Statements && !env.header.moduleNames.contains m then
      throwError "ExtractStatements.lean does not import {m}: add it"
  let entries ← readJsonArr "report_map.json"
  let selection ← readJsonArr "scripts/statements_selection.json"
  elabCommand (← `(universe u v w u_1 u_2 u_3))
  let mut s0 ← get
  -- 1. every declaration shown in Appendix B, as the report shows it
  let mut stmts : Array (String × Json) := #[]
  let mut seen : Std.HashSet Name := {}
  let mut unknown : Array String := #[]
  for e in entries do
    let some blocks := ((e.getObjVal? "blocks").toOption.bind (·.getArr?.toOption)) | throwError "blocks"
    for b in blocks do
      for d in b.getArr?.toOption.getD #[] do
        let some nameStr := (d.getObjValAs? String "name").toOption | continue
        let n := nameStr.toName
        unless env.contains n do
          unknown := unknown.push nameStr
          continue
        if seen.contains n then continue
        seen := seen.insert n
        let asWritten := (← strField d "as_written").toName
        let keyword ← strField d "keyword"
        let (mod, path) ← liftCoreM <| sourceOf n
        let some rng ← liftCoreM <| findDeclarationRanges? n | throwError "{n}: no declaration range"
        let src := (← IO.FS.readFile path).splitOn "\n" |>.toArray
        replayScope src rng.range.pos.line
        let (kind, text) ← liftTermElabM <| withOptions reportOpts <|
          reportText n asWritten keyword src rng.range.endPos.line
        set s0
        stmts := stmts.push (nameStr, Json.mkObj [
          ("name", nameStr), ("as_written", asWritten.toString), ("kind", kind),
          ("keyword", keyword), ("module", mod.toString),
          ("file", (path.toString.drop 2).toString),
          ("line_start", rng.range.pos.line), ("line_end", rng.range.endPos.line),
          ("text", text)])
  -- 2. the audit surface: the numbered results' main theorems and the definitions they use
  let mut sections : Array String := #[]
  let mut defsOut : Array String := #[]
  let mut defsDone : Std.HashSet Name := {}
  let mut nThm := 0
  let mut nDef := 0
  let mut checks : Array Name := #[]
  let mut needed : Std.HashSet Name := {}
  -- the definitions of the entry for the encoding (the report's `app:lean` subsection)
  let mut reportDefs : Std.HashSet Name := {}
  for e in entries do
    if (e.getObjValAs? String "heading").toOption == some "subsection" then
      for d in (e.getObjVal? "decls").toOption.bind (·.getArr?.toOption) |>.getD #[] do
        if let some x := d.getStr?.toOption then reportDefs := reportDefs.insert x.toName
  for sel in selection do
    let label ← strField sel "label"
    let num ← strField sel "number"
    let kindW ← strField sel "kind"
    let title := (sel.getObjValAs? String "title").toOption.getD ""
    let some thms := (sel.getObjVal? "theorems").toOption.bind (·.getArr?.toOption) | throwError "theorems"
    let ns := Name.mkSimple s!"Report.{num}"
    let mut out : Array String := #[]
    for t in thms do
      let some nameStr := t.getStr?.toOption | throwError "theorem name"
      let n := nameStr.toName
      unless env.contains n do
        unknown := unknown.push nameStr
        continue
      let (tmod, path) ← liftCoreM <| sourceOf n
      needed := needed.insert tmod
      let some rng ← liftCoreM <| findDeclarationRanges? n | throwError "{n}: no declaration range"
      let src := (← IO.FS.readFile path).splitOn "\n" |>.toArray
      -- definitions first
      for c in ← liftCoreM <| defsUsed n do
        -- only the definitions the report itself sets out (its encoding section)
        unless reportDefs.contains c do continue
        if defsDone.contains c then continue
        defsDone := defsDone.insert c
        let (dmod, dpath) ← liftCoreM <| sourceOf c
        needed := needed.insert dmod
        let some drng ← liftCoreM <| findDeclarationRanges? c | throwError "{c}: no range"
        let dsrc := (← IO.FS.readFile dpath).splitOn "\n" |>.toArray
        let target := `«Report.defs» ++ (c.replacePrefix `Stemma .anonymous).appendAfter "_def"
        let p ← placeAudit c target s!"/-- `{c}`, as defined in the library. -/" dsrc
          drng.range.pos.line s0
        s0 ← get
        if p.form == "check" then checks := checks.push c else nDef := nDef + 1
        defsOut := defsOut.push p.text
      let target := ns ++ Name.mkSimple n.componentsRev.head!.toString
      let header := s!"/-- {kindW} {num}{if title.isEmpty then "" else s!" ({title})"}: `{n}`. -/"
      let p ← placeAudit n target header src rng.range.pos.line s0
      s0 ← get
      if p.form == "check" then checks := checks.push n else nThm := nThm + 1
      out := out.push p.text
    sections := sections.push (s!"/-! ## {kindW} {num}" ++
      (if title.isEmpty then "" else s!": {title}") ++ s!" (`{label}`) -/\n\n" ++
      "\n\n".intercalate out.toList)
  unless unknown.isEmpty do
    throwError "unknown declarations: {unknown}"
  IO.FS.writeFile "statements.json" ((Json.mkObj (stmts.toList)).pretty 100 ++ "\n")
  let imports := needed.toArray.qsort (·.toString < ·.toString)
  let head := "\n".intercalate (imports.toList.map (s!"import {·}")) ++ s!"

/-!
# The numbered results of the technical report

The single audit surface, in report order.  GENERATED by
`lake env lean scripts/ExtractStatements.lean` from `scripts/statements_selection.json` (the main
theorems of each numbered result, by label); do not edit.

Each theorem below restates, in full, a main statement of one numbered result of the report and
is proved by the library theorem that proves it, so this file is a checked, self-contained list
of what is proved: if a library statement changes, this file stops building.  The definitions of
the report's encoding (Appendix B) that these statements use are pinned first, each by an
equation proved by `rfl`; a structure appears as `#check`.  The statements are printed by Lean,
never copied by hand.  The axiom audit (`scripts/Audit.lean`) covers this file.

{nThm} theorems restated, {nDef} definitions pinned, {checks.size} `#check`.
-/

set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.unusedVariables false

universe u v w u_1 u_2 u_3

"
  let body := "/-! ## Definitions used in the statements -/\n\n" ++ "\n\n".intercalate defsOut.toList ++
    "\n\n" ++ "\n\n".intercalate sections.toList
  IO.FS.writeFile "StemmaLean/Statements.lean" (head ++ body ++ "\n")
  logInfo m!"{stmts.size} declarations -> statements.json; Statements.lean: {nThm} theorems, {nDef} definitions, {checks.size} #check: {checks}"

end ExtractStatements

#eval ExtractStatements.run
