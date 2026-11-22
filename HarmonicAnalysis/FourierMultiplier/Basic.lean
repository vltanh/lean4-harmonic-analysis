/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Fourier multipliers on a Euclidean space

`V` is a finite-dimensional real inner product space with its Lebesgue measure `volume`, and the
Fourier transform is Mathlib's, `𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv`.

* `HarmonicAnalysis.fourierMultiplier m f = 𝓕⁻¹ (m · 𝓕 f)`, the Fourier multiplier with symbol
  `m : V → ℂ`, applied to `f : V → ℂ`.
* `HarmonicAnalysis.multiplierNorm m p`, the norm of `f ↦ 𝓕⁻¹ (m · 𝓕 f)` on `L^p (V)`, computed on
  the dense subspace of Schwartz functions: `⨆_{f ∈ 𝓢(V)} ‖T_m f‖_p / ‖f‖_p` in `ℝ≥0∞` (with
  `0 / 0 = 0`; it is `∞` when `T_m` is unbounded on `L^p`).

## Main results

* `HarmonicAnalysis.continuous_fourierMultiplier`: `T_m f` is continuous for every Schwartz
  function `f` (when `m · 𝓕 f` is not integrable, Lean's integral makes it `0`).
* `HarmonicAnalysis.eLpNorm_fourierMultiplier_le`: `‖T_m f‖_p ≤ ‖T_m‖_p ‖f‖_p`.
* `HarmonicAnalysis.div_le_multiplierNorm_of_tendsto` (density): the norm over Schwartz functions
  bounds the ratio `‖v‖_p / ‖u‖_p` for every pair `(u, v)` that is an `L^p`-limit of pairs
  `(φ_k, T_m φ_k)` with `φ_k` Schwartz, that is, for `T_m` on the closure of its graph over
  Schwartz functions. This is how `T_m` is applied to functions of Sobolev spaces that are not
  Schwartz functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform ENNReal

namespace HarmonicAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier multiplier with symbol `m`: `T_m f = 𝓕⁻¹ (m · 𝓕 f)`. -/
def fourierMultiplier (m : V → ℂ) (f : V → ℂ) : V → ℂ :=
  𝓕⁻ (fun ξ : V => m ξ • 𝓕 f ξ)

/-- `‖T_m‖_{L^p → L^p}`: the supremum of `‖T_m f‖_p / ‖f‖_p` over the (dense) Schwartz functions
`f`. -/
def multiplierNorm (m : V → ℂ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ f : 𝓢(V, ℂ), eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume /
    eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume

/-- `T_m f` is continuous for every Schwartz function `f`. -/
theorem continuous_fourierMultiplier (m : V → ℂ) (f : 𝓢(V, ℂ)) :
    Continuous (fourierMultiplier m f) := by
  sorry

/-- `‖T_m f‖_p ≤ ‖T_m‖_p ‖f‖_p` for every Schwartz function `f`. -/
theorem eLpNorm_fourierMultiplier_le (m : V → ℂ) (p : ℝ) (f : 𝓢(V, ℂ)) :
    eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume ≤
      multiplierNorm m p * eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume := by
  sorry

/-- Density: if Schwartz functions `φ_k` satisfy `φ_k → u` and `T_m φ_k → v` in `L^p`, `1 ≤ p`,
then `‖v‖_p / ‖u‖_p ≤ ‖T_m‖_p`. -/
theorem div_le_multiplierNorm_of_tendsto (m : V → ℂ) {p : ℝ} (hp : 1 ≤ p) {φ : ℕ → 𝓢(V, ℂ)}
    {u v : V → ℂ} (hu : AEStronglyMeasurable u volume) (hv : AEStronglyMeasurable v volume)
    (hφu : Tendsto (fun k => eLpNorm (fun x => φ k x - u x) (ENNReal.ofReal p) volume) atTop
      (𝓝 0))
    (hφv : Tendsto (fun k => eLpNorm (fun x => fourierMultiplier m (φ k) x - v x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    eLpNorm v (ENNReal.ofReal p) volume / eLpNorm u (ENNReal.ofReal p) volume ≤
      multiplierNorm m p := by
  sorry

end HarmonicAnalysis
