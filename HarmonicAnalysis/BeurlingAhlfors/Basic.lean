/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Complex.Wirtinger
public import HarmonicAnalysis.FourierMultiplier.Basic

/-!
# The Beurling–Ahlfors transform and its powers

With `ℂ ≅ ℝ²` by `x + iy ↦ (x, y)` and Mathlib's Fourier transform
`𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv`:

* `HarmonicAnalysis.beurlingSymbol ξ = ξ̄ / ξ`, the symbol of the Beurling–Ahlfors transform `𝓑`
  (`0` at `ξ = 0`, by Lean's `0 / 0 = 0`; the value at one point does not matter);
* `HarmonicAnalysis.beurlingPow k f = 𝓕⁻¹ (m^k · 𝓕 f)`, the power `𝓑^k`;
* `HarmonicAnalysis.beurlingPowNorm k p = ‖𝓑^k‖_{L^p (ℝ²) → L^p (ℝ²)}`, computed on Schwartz
  functions (`HarmonicAnalysis.multiplierNorm`).

## Main results

* `HarmonicAnalysis.beurlingPow_dzbarCLM_pow`: `𝓑^k (∂̄^k F) = ∂^k F` for every Schwartz `F`
  (on the Fourier side, `m^k (π i ξ)^k = (π i ξ̄)^k`). For `k = 1` this is the characterisation
  `𝓑 (∂̄h) = ∂h` of the Beurling–Ahlfors transform.
* Elementary properties of the symbol: `|m| ≤ 1`, `m (−ξ) = m (ξ)`, `m (t ξ) = m (ξ)` for real
  `t ≠ 0`, continuity off `0`, measurability.

## References

* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), §1.3 ((1.11)) and Exercise 2.19.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap ENNReal ComplexConjugate

namespace HarmonicAnalysis

/-- The symbol `m (ξ) = ξ̄ / ξ` of the Beurling–Ahlfors transform (`m (0) = 0`). -/
def beurlingSymbol (ξ : ℂ) : ℂ := conj ξ / ξ

/-- `𝓑^k f = 𝓕⁻¹ (m^k · 𝓕 f)`, with `m (ξ) = ξ̄ / ξ`. -/
def beurlingPow (k : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fourierMultiplier (fun ξ => beurlingSymbol ξ ^ k) f

/-- `‖𝓑^k‖_{L^p (ℝ²) → L^p (ℝ²)}`: the supremum of `‖𝓑^k f‖_p / ‖f‖_p` over the (dense) Schwartz
functions `f`. -/
def beurlingPowNorm (k : ℕ) (p : ℝ) : ℝ≥0∞ :=
  multiplierNorm (fun ξ => beurlingSymbol ξ ^ k) p

theorem norm_beurlingSymbol_le (ξ : ℂ) : ‖beurlingSymbol ξ‖ ≤ 1 := by
  rcases eq_or_ne ξ 0 with rfl | h
  · simp [beurlingSymbol]
  · simp [beurlingSymbol, h]

theorem beurlingSymbol_neg (ξ : ℂ) : beurlingSymbol (-ξ) = beurlingSymbol ξ := by
  simp [beurlingSymbol, neg_div_neg_eq]

theorem beurlingSymbol_ofReal_mul {t : ℝ} (ht : t ≠ 0) (ξ : ℂ) :
    beurlingSymbol (t * ξ) = beurlingSymbol ξ := by
  simp only [beurlingSymbol, map_mul, Complex.conj_ofReal]
  rw [mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr ht)]

theorem continuousAt_beurlingSymbol {ξ : ℂ} (hξ : ξ ≠ 0) : ContinuousAt beurlingSymbol ξ :=
  Complex.continuous_conj.continuousAt.div continuousAt_id hξ

theorem measurable_beurlingSymbol : Measurable beurlingSymbol :=
  Complex.continuous_conj.measurable.div measurable_id

/-- `𝓑^k (∂̄^k F) = ∂^k F` for every Schwartz function `F`. -/
theorem beurlingPow_dzbarCLM_pow (k : ℕ) (F : 𝓢(ℂ, ℂ)) :
    beurlingPow k ((dzbarCLM ^ k) F : ℂ → ℂ) = ((dzCLM ^ k) F : ℂ → ℂ) := by
  sorry

end HarmonicAnalysis
