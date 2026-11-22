/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Torus.Cube
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Order.LiminfLimsup

/-!
# Periodisation and Poisson summation on `𝕋²`

For a Schwartz function `f` on `ℂ ≅ ℝ²` and `R > 0`:

* `HarmonicAnalysis.periodize R f (y) = Σ_{j ∈ ℤ²} f (R (y + j))`, a `ℤ²`-periodic function of
  `y ∈ ℂ` (the lattice `ℤ²` is `ℤ + iℤ`, `HarmonicAnalysis.latticePoint`);
* `HarmonicAnalysis.sampledCoeff R f (n) = R⁻² 𝓕 f (n / R)` for `n ≠ 0`, and `0` at `n = 0`.

## Main results

* `HarmonicAnalysis.summable_sampledCoeff`: these coefficients are summable.
* `HarmonicAnalysis.hasSum_periodize` (Poisson summation on `ℤ²`):
  `Σ_{j ∈ ℤ²} f (R (y + j)) = Σ_{n ∈ ℤ²} R⁻² 𝓕 f (n / R) e^{2πi ⟨n, y⟩}`, the Fourier series of
  the periodisation, which converges absolutely.
* `HarmonicAnalysis.limsup_eLpNorm_sampledCoeff_le`: for `1 < p < ∞`,
  `limsup_{R → ∞} R^{2/p} ‖Σ_n sampledCoeff R f (n) e_n‖_{L^p (𝕋²)} ≤ ‖f‖_{L^p (ℂ)}`.
  On the cell `R · (−½, ½]²`, `Σ_j f (y + R j) = f (y) + O (R^{−3})`, and the mean
  `R⁻² 𝓕 f (0)` removed at `n = 0` contributes `O (R^{2/p − 2})`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ENNReal

namespace HarmonicAnalysis

open UnitAddTorus

/-- The periodisation `y ↦ Σ_{j ∈ ℤ²} f (R (y + j))` of `x ↦ f (R x)`, a `ℤ²`-periodic function on
`ℂ`. -/
def periodize (R : ℝ) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  ∑' j : Fin 2 → ℤ, f (R * (y + latticePoint j))

/-- The coefficients `R⁻² 𝓕 f (n / R)` of the periodisation of `x ↦ f (R x)`, with the mean
(`n = 0`) removed. -/
def sampledCoeff (R : ℝ) (f : ℂ → ℂ) (n : Fin 2 → ℤ) : ℂ :=
  if n = 0 then 0 else ((R : ℂ) ^ 2)⁻¹ * 𝓕 f (latticePoint n / R)

/-- The coefficients `R⁻² 𝓕 f (n / R)` are summable. -/
theorem summable_sampledCoeff (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R) :
    Summable (sampledCoeff R f) := by
  sorry

/-- Poisson summation on `ℤ²`: `Σ_{j ∈ ℤ²} f (R (y + j)) = Σ_{n ∈ ℤ²} R⁻² 𝓕 f (n / R) e_n (y)`. -/
theorem hasSum_periodize (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R) (y : ℂ) :
    HasSum (fun n : Fin 2 → ℤ =>
        ((R : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint n / R) * mFourier n (ofComplex y))
      (periodize R f y) := by
  sorry

/-- The `L^p (𝕋²)` norms of the periodisations, rescaled:
`limsup_{R → ∞} R^{2/p} ‖Σ_n sampledCoeff R f (n) e_n‖_{L^p (𝕋²)} ≤ ‖f‖_{L^p (ℂ)}` for
`1 < p < ∞`. -/
theorem limsup_eLpNorm_sampledCoeff_le (f : 𝓢(ℂ, ℂ)) {p : ℝ} (hp : 1 < p) :
    limsup (fun R : ℕ => ENNReal.ofReal ((R : ℝ) ^ (2 / p)) *
        eLpNorm (fun x => ∑' n, sampledCoeff R f n * mFourier n x) (ENNReal.ofReal p) volume)
      atTop ≤ eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume := by
  sorry

end HarmonicAnalysis
