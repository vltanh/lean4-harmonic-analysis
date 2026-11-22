/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Complex.Wirtinger

/-!
# Wirtinger derivatives of `z^a z̄^b K (|z|²)`

The Leibniz and chain rules for the Wirtinger derivatives of the functions
`w ↦ w^a w̄^b K (|w|²)`, with `a, b ∈ ℕ` and `K : ℝ → ℂ` differentiable at `|z|²`:

* `HarmonicAnalysis.dzbar_monomial_mul_radial`:
  `∂̄ (z^a z̄^b K (|z|²)) = b z^a z̄^{b−1} K (|z|²) + z^{a+1} z̄^b K' (|z|²)`;
* `HarmonicAnalysis.dz_monomial_mul_radial`:
  `∂ (z^a z̄^b K (|z|²)) = a z^{a−1} z̄^b K (|z|²) + z^a z̄^{b+1} K' (|z|²)`.

(The terms with the factor `b`, resp. `a`, are absent when `b = 0`, resp. `a = 0`; in Lean the
exponent `b − 1` is truncated, and the factor `0` makes the term vanish.)
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate

namespace HarmonicAnalysis

/-- `∂̄ (z^a z̄^b K (|z|²)) = b z^a z̄^{b−1} K (|z|²) + z^{a+1} z̄^b K' (|z|²)`. -/
theorem dzbar_monomial_mul_radial (a b : ℕ) {K : ℝ → ℂ} {z : ℂ}
    (hK : DifferentiableAt ℝ K (Complex.normSq z)) :
    dzbar (fun w => w ^ a * conj w ^ b * K (Complex.normSq w)) z =
      b * z ^ a * conj z ^ (b - 1) * K (Complex.normSq z) +
        z ^ (a + 1) * conj z ^ b * deriv K (Complex.normSq z) := by
  sorry

/-- `∂ (z^a z̄^b K (|z|²)) = a z^{a−1} z̄^b K (|z|²) + z^a z̄^{b+1} K' (|z|²)`. -/
theorem dz_monomial_mul_radial (a b : ℕ) {K : ℝ → ℂ} {z : ℂ}
    (hK : DifferentiableAt ℝ K (Complex.normSq z)) :
    dz (fun w => w ^ a * conj w ^ b * K (Complex.normSq w)) z =
      a * z ^ (a - 1) * conj z ^ b * K (Complex.normSq z) +
        z ^ a * conj z ^ (b + 1) * deriv K (Complex.normSq z) := by
  sorry

end HarmonicAnalysis
