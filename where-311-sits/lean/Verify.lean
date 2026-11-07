import Cor312LogVolume
import Lean

/-!
# Axiom check for *Where Theorem 3.11 sits*

For every declaration defined in the sixteen modules that carry the results of the paper,
collect the axioms it depends on and fail unless they are among `propext`,
`Classical.choice` and `Quot.sound`. A proof that uses `sorry` depends on `sorryAx` and
fails this check.

Run with `lake env lean Verify.lean` after `lake build`.
-/

open Lean Elab Command

def paperModules : List Name := [
  `Cor312LogVolume.independence.Cor312Approximation,
  `Cor312LogVolume.independence.Cor312CitedBadPlaceEnlarged,
  `Cor312LogVolume.independence.Cor312CitedDilemma,
  `Cor312LogVolume.independence.Cor312CitedPrimeStripLayer,
  `Cor312LogVolume.independence.Cor312CitedTheory,
  `Cor312LogVolume.independence.Cor312CitedTheoryFamily,
  `Cor312LogVolume.independence.Cor312CitedWeakSHEScale,
  `Cor312LogVolume.independence.Cor312LanaTarget,
  `Cor312LogVolume.independence.Cor312RamifiedBadPlace,
  `Cor312LogVolume.independence.Cor312RamifiedLabelAction,
  `Cor312LogVolume.independence.Cor312RamifiedLogShell,
  `Cor312LogVolume.independence.Cor312SourceBoundDegree,
  `Cor312LogVolume.independence.Cor312SourceBoundFamily,
  `Cor312LogVolume.independence.Cor312SourceBoundIsm,
  `Cor312LogVolume.independence.Cor312SourceBoundSplitting,
  `Cor312LogVolume.independence.Cor312SourceBoundTheory]

elab "#check_paper_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut perModule : Std.HashMap Name Nat := {}
  let mut bad : Array (Name × Array Name) := #[]
  let mut total := 0
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if !paperModules.contains mod then continue
      let axs ← liftCoreM (Lean.collectAxioms n)
      total := total + 1
      perModule := perModule.insert mod (perModule.getD mod 0 + 1)
      let extra := axs.filter (fun a => !allowed.contains a)
      if !extra.isEmpty then bad := bad.push (n, extra)
  for m in paperModules do
    if perModule.getD m 0 == 0 then
      throwError m!"no declarations found in {m}"
  logInfo m!"checked {total} declarations in {paperModules.length} modules"
  unless bad.isEmpty do
    throwError m!"declarations with axioms outside propext, Classical.choice, Quot.sound: {bad}"
  logInfo m!"all of them depend on at most propext, Classical.choice, Quot.sound"

#check_paper_axioms
