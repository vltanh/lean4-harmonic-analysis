module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that proofs are visible to the axiom
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   { find HarmonicAnalysis -name '*.lean'; cd palomar && find . -name Solution.lean; } |
--     sed 's#^\./##; s/\.lean$//; s#/#.#g; s/^/import all /' | sort
-- The Solution of each Palomar entry is imported, and no Challenge: a Challenge holds a copy of the
-- definitions under the library's names.
import all FourierMultipliers.Solution
import all HarmonicAnalysis.BeurlingAhlfors.Basic
import all HarmonicAnalysis.BeurlingAhlfors.Duality
import all HarmonicAnalysis.BeurlingAhlfors.LowerBound
import all HarmonicAnalysis.BeurlingAhlfors.Periodic
import all HarmonicAnalysis.BeurlingAhlfors.TestFunctions
import all HarmonicAnalysis.BeurlingAhlfors.TestFunctions.Approx
import all HarmonicAnalysis.BeurlingAhlfors.TestFunctions.Profile
import all HarmonicAnalysis.BeurlingAhlfors.Transference
import all HarmonicAnalysis.Complex.RadialIntegral
import all HarmonicAnalysis.Complex.Wirtinger
import all HarmonicAnalysis.Complex.WirtingerRadial
import all HarmonicAnalysis.Defs
import all HarmonicAnalysis.FourierMultiplier.Basic
import all HarmonicAnalysis.FourierMultiplier.Density
import all HarmonicAnalysis.FourierMultiplier.Duality
import all HarmonicAnalysis.FourierMultiplier.Extension
import all HarmonicAnalysis.FourierMultiplier.Norming
import all HarmonicAnalysis.Hardy.Approximation
import all HarmonicAnalysis.Hardy.Basic
import all HarmonicAnalysis.Hardy.Defs
import all HarmonicAnalysis.Hardy.FunctionalCalculus
import all HarmonicAnalysis.Hardy.GeometricMean
import all HarmonicAnalysis.Hardy.Jensen
import all HarmonicAnalysis.Hardy.Outer
import all HarmonicAnalysis.Hardy.RangeFunction
import all HarmonicAnalysis.Hardy.RieszFactorization
import all HarmonicAnalysis.Hardy.Szego
import all HarmonicAnalysis.NoncommutativeKhintchine
import all HarmonicAnalysis.Paley.Rademacher
import all HarmonicAnalysis.Paley.Schatten
import all HarmonicAnalysis.Torus.Cube
import all HarmonicAnalysis.Torus.Lattice
import all HarmonicAnalysis.Torus.Lipschitz
import all HarmonicAnalysis.Torus.Poisson
import all HarmonicAnalysis.Torus.Smooth
import all HarmonicAnalysis.Torus.TrigPoly
import all HarmonicAnalysis.Transference.ContinuousSymbol
import all HarmonicAnalysis.Transference.Homogeneous
import all HarmonicAnalysis.Transference.RiemannSum
import all HarmonicAnalysis.VectorValued.CircPoly
import all HarmonicAnalysis.VectorValued.Defs
import all HarmonicAnalysis.VectorValued.Dyadic.Average
import all HarmonicAnalysis.VectorValued.Dyadic.Martingale
import all HarmonicAnalysis.VectorValued.Dyadic.Shift
import all HarmonicAnalysis.VectorValued.HilbertTransform.Fourier
import all HarmonicAnalysis.VectorValued.HilbertTransform.Truncated
import all HarmonicAnalysis.VectorValued.LittlewoodPaley.Circle
import all HarmonicAnalysis.VectorValued.LittlewoodPaley.Line
import all HarmonicAnalysis.VectorValued.RademacherNorm
import all HarmonicAnalysis.VectorValued.Transference

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Prints the axioms on which the main theorems depend, and those of the Palomar entries (the
Solutions in `palomar/`), then checks that they and every declaration of the library and of the
Solutions, including private and auxiliary ones, depend only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`. A `sorry` shows up as the axiom `sorryAx`.

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
   ``HarmonicAnalysis.existsUnique_extension_of_multiplierNorm_ne_top,
   ``HarmonicAnalysis.enorm_eq_multiplierNorm,
   ``HarmonicAnalysis.multiplierNorm_conjExponent,
   ``HarmonicAnalysis.multiplierNorm_conj_conjExponent,
   ``HarmonicAnalysis.multiplierNorm_conj_comp_neg,
   ``HarmonicAnalysis.tendsto_eLpNorm_mollify_sub,
   ``HarmonicAnalysis.exists_tendsto_hasCompactFourierSupportOffZero,
   ``HarmonicAnalysis.integral_torusMultiplier_mul_trigPoly,
   ``HarmonicAnalysis.hasSum_periodize,
   ``HarmonicAnalysis.tendsto_eLpNorm_tsum_fourier_mul_mFourier,
   ``HarmonicAnalysis.tendsto_riemannSum_real,
   ``HarmonicAnalysis.multiplierNorm_le_liminf_torusMultiplierNorm,
   ``HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm,
   ``HarmonicAnalysis.exists_norm_le_of_liminf_torusMultiplierNorm_ne_top,
   ``HarmonicAnalysis.beurlingPow_dzbarCLM_pow,
   ``HarmonicAnalysis.beurlingPow_dzbar_iterate,
   ``HarmonicAnalysis.iterate_beurlingPow_one_dzbar_iterate,
   ``HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto,
   ``HarmonicAnalysis.beurlingPowNorm_conjExponent,
   ``HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm,
   ``HarmonicAnalysis.BeurlingAhlfors.exists_schwartz_tendsto_testFun,
   ``HarmonicAnalysis.tendsto_eLpNorm_div_testFun,
   ``HarmonicAnalysis.eLpNorm_div_le_beurlingPowNorm_two,
   ``HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two,
   ``HarmonicAnalysis.beurlingKappa_two_pStar_le_beurlingPowNorm_two,
   ``HarmonicAnalysis.pStar_sub_one_lt_beurlingPowNorm_two,
   ``HarmonicAnalysis.twentyOne_div_five_le_beurlingPowNorm_two_four,
   ``UnitAddTorus.cubeFourierCoeff_fderiv,
   ``UnitAddTorus.cubeFourierCoeff_fderiv_of_contDiff,
   ``UnitAddTorus.summable_cubeFourierCoeff,
   ``UnitAddTorus.hasSum_cubeFourierCoeff_mul_mFourier,
   ``UnitAddTorus.eq_of_cubeFourierCoeff_eq,
   ``UnitAddTorus.contDiff_periodicMultiplier,
   ``UnitAddTorus.cubeFourierCoeff_periodicMultiplier,
   ``UnitAddTorus.exists_dzbarPi_eq,
   ``HarmonicAnalysis.periodicMultiplier_beurlingSymbol_dzbarPi,
   ``HarmonicAnalysis.periodicMultiplier_trigPoly,
   ``HarmonicAnalysis.eLpNormRad_dyadicShift_le,
   ``HarmonicAnalysis.eLpNorm_sum_dilateConv_le,
   ``HarmonicAnalysis.eLpNorm_truncatedHilbert_le,
   ``HarmonicAnalysis.eLpNorm_fourierInv_neg_I_sign_le,
   ``HarmonicAnalysis.eLpNorm_fourierInv_sign_le,
   ``HarmonicAnalysis.eLpNormRad_lineBlock_le,
   ``HarmonicAnalysis.eLpNormRad_lineBlock_dilate_le,
   ``HarmonicAnalysis.eLpNorm_circPoly_multiplier_le,
   ``HarmonicAnalysis.eLpNormRad_dyadicBlock_le,
   ``HarmonicAnalysis.log_norm_fourierCoeff_zero_le_integral_log_norm,
   ``HarmonicAnalysis.exists_isOuter,
   ``HarmonicAnalysis.IsOuter.range_eq,
   ``HarmonicAnalysis.IsOuter.exists_tendsto_iff,
   ``HarmonicAnalysis.szegoInf_eq,
   ``HarmonicAnalysis.posDef_of_szegoInf_pos,
   ``HarmonicAnalysis.exists_isOuter_of_integrable_log_det,
   ``HarmonicAnalysis.integrable_log_det_of_isHardyTwo,
   ``HarmonicAnalysis.isOuter_iff_integral_log_norm_det,
   ``HarmonicAnalysis.IsAnalyticRange.exists_isometry,
   ``HarmonicAnalysis.exists_mul_conjTranspose_eq_iff,
   ``HarmonicAnalysis.isFactorable_iff,
   ``HarmonicAnalysis.exists_mul_eq_of_isHardyOne,
   ``HarmonicAnalysis.paley_schatten_of_isHardyOne,
   ``HarmonicAnalysis.paley_schatten,
   ``HarmonicAnalysis.rademacher_schatten_le,
   ``HarmonicAnalysis.ncKhintchine,
   ``HarmonicAnalysis.ncKhintchine_of_normal]

/-- The theorems of the Palomar entries. -/
meta def palomarTheorems : List Name :=
  [``FourierMultipliersChallenge.multiplierNorm_spec,
   ``FourierMultipliersChallenge.multiplierNorm_conjExponent,
   ``FourierMultipliersChallenge.transference,
   ``FourierMultipliersChallenge.transference_homogeneous,
   ``FourierMultipliersChallenge.beurlingPow_dzbar_iterate,
   ``FourierMultipliersChallenge.beurlingPowNorm_conjExponent,
   ``FourierMultipliersChallenge.beurlingKappa_two,
   ``FourierMultipliersChallenge.dragicevic_limit,
   ``FourierMultipliersChallenge.dragicevic_lower_bound,
   ``FourierMultipliersChallenge.dragicevic_lower_bound_pStar,
   ``FourierMultipliersChallenge.pStar_sub_one_lt_beurlingPowNorm_two]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `sorryAx` is listed instead of rejected (`true` only while proofs are open). -/
meta def allowSorry : Bool := false

/-- The modules of the Solutions of the Palomar entries. -/
meta def palomarModules : List Name := [`FourierMultipliers.Solution]

/-- Whether `m` is a module of the library or the Solution of a Palomar entry. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`HarmonicAnalysis).isPrefixOf m || palomarModules.contains m

/-- The constants declared in the library and in the Solutions of the Palomar entries. -/
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
  for n in mainResults ++ palomarTheorems do
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
