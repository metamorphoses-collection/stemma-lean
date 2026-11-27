/-
Axiom audit: every declaration of the `StemmaLean` library (vendored files included) depends only
on `propext`, `Classical.choice` and `Quot.sound`.  A `sorry` would appear as `sorryAx`.
Run: `lake env lean scripts/Audit.lean`.
-/
import Lean
import StemmaLean
import StemmaLean.GammaBlocks
import StemmaLean.TextIllegible
import StemmaLean.Statements
import StemmaLean.MultiAttraction
import StemmaLean.RootedConsistency
import StemmaLean.TwoReading
import StemmaLean.RootedTop

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`StemmaLean).isPrefixOf m then
        count := count + 1
        let axs ← liftCoreM (collectAxioms n)
        for a in axs do
          unless std.contains a do bad := bad.push (n, a)
    | none => pure ()
  if bad.isEmpty then
    logInfo m!"Axiom audit passed: {count} declarations, standard axioms only."
  else
    throwError m!"Axiom audit failed: {bad.toList}"
