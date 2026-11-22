/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Complex.WirtingerRadial
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The test functions for the lower bound of `‖𝓑²‖_p`

For `p > 1` and `ε ≠ 0`, with `t = |z|²`:

* `HarmonicAnalysis.BeurlingAhlfors.cutoff t = σ (t)`, a smooth cutoff, `σ = 1` for `t ≤ 1` and
  `σ = 0` for `t ≥ 2` (`σ (t) = Real.smoothTransition (2 − t)`);
* `HarmonicAnalysis.BeurlingAhlfors.profile p ε t = H (t) = (t + ε²)^{−1/p} σ (t)`;
* `HarmonicAnalysis.BeurlingAhlfors.testFun p ε z = F (z) = z² H (|z|²)`, smooth with compact
  support, and the Schwartz function `HarmonicAnalysis.BeurlingAhlfors.testFunction p k` at
  `ε = 1/(k + 1)`.

These are the functions `f_{2,α} (z) = z² |z|^{−2α} g (|z|)` of Dragičević's proof (`n = 2`), taken
at the critical exponent `α = 1/p` and smoothed at `0` (by `ε`) and at `|z| = 1` (by `σ`), so that
they are Schwartz functions; the limit `α → 1/p` of the source becomes the limit `ε → 0`.

## Main results

* `∂̄²F = z⁴ H'' (t)` and `∂²F = 2H + 4t H' + t² H''` everywhere
  (`dzbar_dzbar_testFun`, `dz_dz_testFun`);
* on the open unit disc, with `α = 1/p` and `s = t / (t + ε²)`,
  `∂̄²F = z⁴ α (α + 1) (t + ε²)^{−α−2}` and `∂²F = (t + ε²)^{−α} (2 − 4αs + α (α + 1) s²)`
  (`dzbar_dzbar_testFun_of_normSq_lt_one`, `dz_dz_testFun_of_normSq_lt_one`);
* on `|z| ≥ 1` both are bounded uniformly in `ε ∈ (0, 1]` (`exists_bound_testFun`); they vanish
  for `|z|² ≥ 2`.

## References

* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), §4.1.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap ContDiff

namespace HarmonicAnalysis.BeurlingAhlfors

/-- The cutoff `σ (t) = Real.smoothTransition (2 − t)`: `1` for `t ≤ 1`, `0` for `t ≥ 2`. -/
def cutoff (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

/-- The radial profile `H (t) = (t + ε²)^{−1/p} σ (t)`. -/
def profile (p ε t : ℝ) : ℝ := (t + ε ^ 2) ^ (-p⁻¹) * cutoff t

/-- The test function `F (z) = z² H (|z|²) = z² (|z|² + ε²)^{−1/p} σ (|z|²)`. -/
def testFun (p ε : ℝ) (z : ℂ) : ℂ := z ^ 2 * (profile p ε (Complex.normSq z) : ℂ)

theorem contDiff_testFun (p : ℝ) {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ ∞ (testFun p ε) := by
  sorry

theorem hasCompactSupport_testFun (p ε : ℝ) : HasCompactSupport (testFun p ε) := by
  sorry

/-- The Schwartz function `F` at `ε = 1/(k + 1)`. -/
def testFunction (p : ℝ) (k : ℕ) : 𝓢(ℂ, ℂ) :=
  (hasCompactSupport_testFun p ((k : ℝ) + 1)⁻¹).toSchwartzMap
    (contDiff_testFun p (inv_ne_zero (Nat.cast_add_one_ne_zero k)))

theorem testFunction_apply (p : ℝ) (k : ℕ) (z : ℂ) :
    testFunction p k z = testFun p ((k : ℝ) + 1)⁻¹ z :=
  rfl

/-- `∂̄²F (z) = z⁴ H'' (|z|²)`. -/
theorem dzbar_dzbar_testFun (p : ℝ) {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    dzbar (dzbar (testFun p ε)) z =
      z ^ 4 * ((deriv (deriv (profile p ε)) (Complex.normSq z) : ℝ) : ℂ) := by
  sorry

/-- `∂²F (z) = 2 H (t) + 4 t H' (t) + t² H'' (t)`, `t = |z|²`. -/
theorem dz_dz_testFun (p : ℝ) {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    dz (dz (testFun p ε)) z =
      ((2 * profile p ε (Complex.normSq z) +
        4 * Complex.normSq z * deriv (profile p ε) (Complex.normSq z) +
        Complex.normSq z ^ 2 * deriv (deriv (profile p ε)) (Complex.normSq z) : ℝ) : ℂ) := by
  sorry

/-- On the open unit disc, `∂̄²F (z) = z⁴ α (α + 1) (|z|² + ε²)^{−α−2}`, `α = 1/p`. -/
theorem dzbar_dzbar_testFun_of_normSq_lt_one (p : ℝ) {ε : ℝ} (hε : ε ≠ 0) {z : ℂ}
    (hz : Complex.normSq z < 1) :
    dzbar (dzbar (testFun p ε)) z =
      z ^ 4 * ((p⁻¹ * (p⁻¹ + 1) * (Complex.normSq z + ε ^ 2) ^ (-p⁻¹ - 2) : ℝ) : ℂ) := by
  sorry

/-- On the open unit disc, `∂²F (z) = (t + ε²)^{−α} (2 − 4αs + α (α + 1) s²)`, `t = |z|²`,
`s = t / (t + ε²)`, `α = 1/p`. -/
theorem dz_dz_testFun_of_normSq_lt_one (p : ℝ) {ε : ℝ} (hε : ε ≠ 0) {z : ℂ}
    (hz : Complex.normSq z < 1) :
    dz (dz (testFun p ε)) z =
      (((Complex.normSq z + ε ^ 2) ^ (-p⁻¹) *
        (2 - 4 * p⁻¹ * (Complex.normSq z / (Complex.normSq z + ε ^ 2)) +
          p⁻¹ * (p⁻¹ + 1) * (Complex.normSq z / (Complex.normSq z + ε ^ 2)) ^ 2) : ℝ) : ℂ) := by
  sorry

/-- Off the open unit disc, `∂̄²F` and `∂²F` are bounded uniformly in `ε ∈ (0, 1]`. -/
theorem exists_bound_testFun (p : ℝ) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ z : ℂ, 1 ≤ Complex.normSq z →
      ‖dzbar (dzbar (testFun p ε)) z‖ ≤ C ∧ ‖dz (dz (testFun p ε)) z‖ ≤ C := by
  sorry

end HarmonicAnalysis.BeurlingAhlfors
