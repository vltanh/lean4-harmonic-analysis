module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that the proofs are visible (the module
-- system hides them from a plain `import`). Generate the lines with
--   find VectorValuedHarmonicAnalysis -name '*.lean' | sed 's/\.lean$//; s#/#.#g; s/^/import all /' | sort
import all VectorValuedHarmonicAnalysis.Dyadic.Average
import all VectorValuedHarmonicAnalysis.Dyadic.Martingale
import all VectorValuedHarmonicAnalysis.Dyadic.Shift
import all VectorValuedHarmonicAnalysis.Hardy.Approximation
import all VectorValuedHarmonicAnalysis.Hardy.Basic
import all VectorValuedHarmonicAnalysis.Hardy.FunctionalCalculus
import all VectorValuedHarmonicAnalysis.Hardy.GeometricMean
import all VectorValuedHarmonicAnalysis.Hardy.Jensen
import all VectorValuedHarmonicAnalysis.Hardy.Outer
import all VectorValuedHarmonicAnalysis.Hardy.RangeFunction
import all VectorValuedHarmonicAnalysis.Hardy.RieszFactorization
import all VectorValuedHarmonicAnalysis.Hardy.Szego
import all VectorValuedHarmonicAnalysis.HilbertTransform.Fourier
import all VectorValuedHarmonicAnalysis.HilbertTransform.Truncated
import all VectorValuedHarmonicAnalysis.LittlewoodPaley.Circle
import all VectorValuedHarmonicAnalysis.LittlewoodPaley.Line
import all VectorValuedHarmonicAnalysis.NoncommutativeKhintchine
import all VectorValuedHarmonicAnalysis.Paley.Rademacher
import all VectorValuedHarmonicAnalysis.Paley.Schatten
import all VectorValuedHarmonicAnalysis.RademacherNorm
import all VectorValuedHarmonicAnalysis.Transference

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Checks every declaration of the library: the run fails if one depends on an axiom other than
Lean's standard `propext`, `Classical.choice` and `Quot.sound`. A `sorry` shows up as the axiom
`sorryAx`, and fails the run too (`allowSorry := false`); with `allowSorry := true`, for work in
progress, the declarations that depend on `sorryAx` are listed instead.
-/

open Lean Elab Command

namespace Audit

/-- Whether declarations may still depend on `sorryAx`. -/
meta def allowSorry : Bool := false

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`VectorValuedHarmonicAnalysis).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut s : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.push c
  return s

elab "#audit" : command => do
  let env ← getEnv
  let library := libraryConstants env
  let mut bad : Array Name := #[]
  let mut sorries : Array Name := #[]
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    let other := axs.filter (!standardAxioms.contains ·)
    if other.isEmpty then continue
    if other.all (· == ``sorryAx) then
      unless c.isInternal do sorries := sorries.push c
    else
      bad := bad.push c
  let sorted := sorries.qsort (·.toString < ·.toString)
  logInfo (s!"Checked {library.size} declarations of the library.\n" ++
    s!"{sorted.size} public declarations depend on `sorryAx`:\n" ++
    "\n".intercalate (sorted.toList.map toString))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"
  if !allowSorry && !sorries.isEmpty then
    throwError m!"declarations depend on `sorryAx`: {sorted}"

end Audit

#audit
