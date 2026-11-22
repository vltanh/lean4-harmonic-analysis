/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.FourierMultiplier.Basic

/-!
# Duality for Fourier multipliers

For `1 < p < ∞` and `q = p / (p − 1)`:

* `HarmonicAnalysis.multiplierNorm_conj_conjExponent` (the adjoint): the `L²`-adjoint of `T_m` is
  `T_{m̄}`, `∫ T_m f · ḡ = ∫ f · conj (T_{m̄} g)`, so `‖T_m‖_p = ‖T_{m̄}‖_q`, for bounded
  measurable `m`.
* `HarmonicAnalysis.fourierMultiplier_conj`, `HarmonicAnalysis.multiplierNorm_conj_comp_neg`
  (conjugation): `conj (T_m (conj f)) = T_{m̃} f` with `m̃ (ξ) = conj (m (−ξ))`, so
  `‖T_{m̃}‖_p = ‖T_m‖_p`.

Together: `‖T_m‖_p = ‖T_{m (−·)}‖_q`; for an even symbol, `‖T_m‖_p = ‖T_m‖_q`.

## References

* A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex Riesz
  transform*, Math. Ann. 386 (2023), [arXiv:2109.08369](https://arxiv.org/abs/2109.08369),
  §1.3.1 (for the powers of the complex Riesz transform).
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), Exercise 1.16.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace HarmonicAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The adjoint of `T_m` is `T_{m̄}`: for a bounded measurable symbol `m` and `1 < p < ∞`,
`‖T_m‖_{L^p} = ‖T_{m̄}‖_{L^q}`, `q = p / (p − 1)`. -/
theorem multiplierNorm_conj_conjExponent {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p = multiplierNorm (fun ξ => conj (m ξ)) (p / (p - 1)) := by
  sorry

/-- Conjugation: `conj (T_m (conj f)) = T_{m̃} f`, `m̃ (ξ) = conj (m (−ξ))`. -/
theorem fourierMultiplier_conj (m : V → ℂ) (f : V → ℂ) (x : V) :
    fourierMultiplier (fun ξ => conj (m (-ξ))) f x =
      conj (fourierMultiplier m (fun v => conj (f v)) x) := by
  sorry

/-- Conjugation: `‖T_{m̃}‖_{L^p} = ‖T_m‖_{L^p}`, `m̃ (ξ) = conj (m (−ξ))`. -/
theorem multiplierNorm_conj_comp_neg (m : V → ℂ) (p : ℝ) :
    multiplierNorm (fun ξ => conj (m (-ξ))) p = multiplierNorm m p := by
  sorry

end HarmonicAnalysis
