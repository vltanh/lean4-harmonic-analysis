module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that proofs are visible to the axiom
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find HarmonicAnalysis -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all HarmonicAnalysis.BeurlingAhlfors.Basic
import all HarmonicAnalysis.BeurlingAhlfors.Duality
import all HarmonicAnalysis.BeurlingAhlfors.LowerBound
import all HarmonicAnalysis.BeurlingAhlfors.TestFunctions
import all HarmonicAnalysis.BeurlingAhlfors.TestFunctions.Approx
import all HarmonicAnalysis.BeurlingAhlfors.TestFunctions.Profile
import all HarmonicAnalysis.BeurlingAhlfors.Transference
import all HarmonicAnalysis.Complex.RadialIntegral
import all HarmonicAnalysis.Complex.Wirtinger
import all HarmonicAnalysis.Complex.WirtingerRadial
import all HarmonicAnalysis.FourierMultiplier.Basic
import all HarmonicAnalysis.FourierMultiplier.Duality
import all HarmonicAnalysis.FourierMultiplier.Norming
import all HarmonicAnalysis.Torus.Cube
import all HarmonicAnalysis.Torus.Lattice
import all HarmonicAnalysis.Torus.Poisson
import all HarmonicAnalysis.Torus.TrigPoly
import all HarmonicAnalysis.Transference.Homogeneous
import all HarmonicAnalysis.Transference.RiemannSum

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Prints the axioms on which the main theorems depend, then checks that they and every declaration
of the library, including private and auxiliary ones, depend only on Lean's standard axioms
`propext`, `Classical.choice` and `Quot.sound`. A `sorry` shows up as the axiom `sorryAx`.

`allowSorry` is `false`, so any `sorry` (the axiom `sorryAx`) fails the audit. Setting it to `true`
while proofs are open lists the declarations whose own proof contains a `sorry` and fails only on
other axioms.
-/

open Lean Elab Command

namespace Audit

/-- The main theorems of the library. -/
meta def mainResults : List Name :=
  [``HarmonicAnalysis.fourier_dzbarCLM,
   ``HarmonicAnalysis.fourier_dzCLM,
   ``HarmonicAnalysis.div_le_multiplierNorm_of_tendsto,
   ``HarmonicAnalysis.multiplierNorm_conj_conjExponent,
   ``HarmonicAnalysis.multiplierNorm_conj_comp_neg,
   ``HarmonicAnalysis.eLpNorm_tsum_le_torusMultiplierNorm,
   ``HarmonicAnalysis.hasSum_periodize,
   ``HarmonicAnalysis.limsup_eLpNorm_sampledCoeff_le,
   ``HarmonicAnalysis.tendsto_riemannSum,
   ``HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm,
   ``HarmonicAnalysis.beurlingPow_dzbarCLM_pow,
   ``HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto,
   ``HarmonicAnalysis.beurlingPowNorm_conjExponent,
   ``HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm,
   ``HarmonicAnalysis.BeurlingAhlfors.exists_schwartz_tendsto_testFun,
   ``HarmonicAnalysis.tendsto_eLpNorm_div_testFun,
   ``HarmonicAnalysis.eLpNorm_div_le_beurlingPowNorm_two,
   ``HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two,
   ``HarmonicAnalysis.beurlingKappa_two_pStar_le_beurlingPowNorm_two,
   ``HarmonicAnalysis.pStar_sub_one_lt_beurlingPowNorm_two,
   ``HarmonicAnalysis.twentyOne_div_five_le_beurlingPowNorm_two_four]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `sorryAx` is listed instead of rejected (`true` only while proofs are open). -/
meta def allowSorry : Bool := false

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`HarmonicAnalysis).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      out := out ++ d.constNames
  return out

/-- Whether the proof or body of `c` itself contains `sorryAx`. -/
meta def hasOwnSorry (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci => match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants.contains ``sorryAx
    | none => false
  | none => false

/-- Whether the axioms `axs` are acceptable. -/
meta def acceptable (axs : Array Name) : Bool :=
  axs.all fun a => standardAxioms.contains a || (allowSorry && a == ``sorryAx)

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut rows : Array String := #[]
  for n in mainResults do
    let axs ← liftCoreM <| collectAxioms n
    unless acceptable axs do bad := bad.push n
    rows := rows.push s!"{n}: {axs.toList}"
  let library := libraryConstants env
  let mut sorries : Array Name := #[]
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    unless acceptable axs do bad := bad.push c
    if hasOwnSorry env c then sorries := sorries.push c
  let sorryRows := sorries.qsort (·.toString < ·.toString) |>.toList.map (s!"  {·}")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "no axioms beyond the standard ones" else "see the error") ++
    (if sorries.isEmpty then "; no `sorry`." else
      s!"; {sorries.size} contain a `sorry`:\n" ++ "\n".intercalate sorryRows))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
