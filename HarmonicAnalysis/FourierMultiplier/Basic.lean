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

For a bounded measurable symbol and a Schwartz function `f`, `m · 𝓕 f` is integrable, so `T_m f`
is a bounded continuous function (`HarmonicAnalysis.continuous_fourierMultiplier`), and
`‖T_m f‖_p ≤ ‖T_m‖_p ‖f‖_p` (`HarmonicAnalysis.eLpNorm_fourierMultiplier_le`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
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

/-- For a bounded measurable symbol, `T_m f` is continuous for every Schwartz function `f`. -/
theorem continuous_fourierMultiplier {m : V → ℂ} (hm : Measurable m) (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C)
    (f : 𝓢(V, ℂ)) : Continuous (fourierMultiplier m f) := by
  sorry

/-- `‖T_m f‖_p ≤ ‖T_m‖_p ‖f‖_p` for every Schwartz function `f`. -/
theorem eLpNorm_fourierMultiplier_le (m : V → ℂ) {p : ℝ} (hp : 1 ≤ p) (f : 𝓢(V, ℂ)) :
    eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume ≤
      multiplierNorm m p * eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume := by
  sorry

end HarmonicAnalysis
