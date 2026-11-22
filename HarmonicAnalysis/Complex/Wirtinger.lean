/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The Wirtinger derivatives

For a function `g : ℂ → F` into a complex normed space, with `ℂ ≅ ℝ²` by `x + iy ↦ (x, y)`, the
Wirtinger derivatives at `z` are
`∂g (z) = ½ (∂_x g (z) − i ∂_y g (z))` and `∂̄g (z) = ½ (∂_x g (z) + i ∂_y g (z))`,
where `∂_x g (z) = fderiv ℝ g z 1` and `∂_y g (z) = fderiv ℝ g z I`
(`HarmonicAnalysis.dz`, `HarmonicAnalysis.dzbar`). On the Schwartz space `𝓢(ℂ, F)` they are
continuous linear maps (`HarmonicAnalysis.dzCLM`, `HarmonicAnalysis.dzbarCLM`), built from the
line derivatives of Mathlib.

## Main results

* `HarmonicAnalysis.fourier_dzbarCLM`, `HarmonicAnalysis.fourier_dzCLM`: the Fourier symbols.
  With `𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv` (Mathlib's convention, `⟨v, ξ⟩ = Re (v̄ ξ)`),
  `𝓕 (∂̄f) (ξ) = π i ξ 𝓕 f (ξ)` and `𝓕 (∂f) (ξ) = π i ξ̄ 𝓕 f (ξ)`.
* `HarmonicAnalysis.dzbar_conj`, `HarmonicAnalysis.dz_conj`: the conjugation rules
  `∂̄ (conj ∘ g) = conj ∘ ∂g` and `∂ (conj ∘ g) = conj ∘ ∂̄g`.

## References

* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), §1.1.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform Real ComplexConjugate

namespace HarmonicAnalysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Wirtinger derivative `∂g (z) = ½ (∂_x g (z) − i ∂_y g (z))` of a function `g : ℂ → F`
(`0` where `g` is not real-differentiable). -/
def dz (g : ℂ → F) (z : ℂ) : F :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 - Complex.I • fderiv ℝ g z Complex.I)

/-- The Wirtinger derivative `∂̄g (z) = ½ (∂_x g (z) + i ∂_y g (z))` of a function `g : ℂ → F`
(`0` where `g` is not real-differentiable). -/
def dzbar (g : ℂ → F) (z : ℂ) : F :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I)

/-- `∂ = ½ (∂_x − i ∂_y)` as a continuous linear map of the Schwartz space `𝓢(ℂ, F)`. -/
def dzCLM : 𝓢(ℂ, F) →L[ℂ] 𝓢(ℂ, F) :=
  (2⁻¹ : ℂ) • (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) (1 : ℂ) -
    Complex.I • LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) Complex.I)

/-- `∂̄ = ½ (∂_x + i ∂_y)` as a continuous linear map of the Schwartz space `𝓢(ℂ, F)`. -/
def dzbarCLM : 𝓢(ℂ, F) →L[ℂ] 𝓢(ℂ, F) :=
  (2⁻¹ : ℂ) • (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) (1 : ℂ) +
    Complex.I • LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, F) Complex.I)

theorem dzCLM_apply (f : 𝓢(ℂ, F)) (z : ℂ) : dzCLM f z = dz f z := by
  simp [dzCLM, dz, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem dzbarCLM_apply (f : 𝓢(ℂ, F)) (z : ℂ) : dzbarCLM f z = dzbar f z := by
  simp [dzbarCLM, dzbar, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- The Fourier symbol of `∂̄`: `𝓕 (∂̄f) (ξ) = π i ξ 𝓕 f (ξ)`. -/
theorem fourier_dzbarCLM (f : 𝓢(ℂ, F)) (ξ : ℂ) :
    𝓕 (dzbarCLM f : ℂ → F) ξ = ((π : ℂ) * Complex.I * ξ) • 𝓕 (f : ℂ → F) ξ := by
  sorry

/-- The Fourier symbol of `∂`: `𝓕 (∂f) (ξ) = π i ξ̄ 𝓕 f (ξ)`. -/
theorem fourier_dzCLM (f : 𝓢(ℂ, F)) (ξ : ℂ) :
    𝓕 (dzCLM f : ℂ → F) ξ = ((π : ℂ) * Complex.I * conj ξ) • 𝓕 (f : ℂ → F) ξ := by
  sorry

/-- The conjugation rule `∂̄ (conj ∘ g) = conj ∘ ∂g`. -/
theorem dzbar_conj (g : ℂ → ℂ) (z : ℂ) : dzbar (fun w => conj (g w)) z = conj (dz g z) := by
  sorry

/-- The conjugation rule `∂ (conj ∘ g) = conj ∘ ∂̄g`. -/
theorem dz_conj (g : ℂ → ℂ) (z : ℂ) : dz (fun w => conj (g w)) z = conj (dzbar g z) := by
  sorry

end HarmonicAnalysis
