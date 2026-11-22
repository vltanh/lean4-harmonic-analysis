/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Complex.WirtingerRadial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Dragičević's test functions

For `n ∈ ℕ` and `α ∈ ℝ`, Dragičević's test functions (lecture notes, §4.1) are
`f_{n,α} (z) = z^n |z|^{−2α} g_n (|z|)` (`HarmonicAnalysis.BeurlingAhlfors.testFun`), where
`g_n (x) = 1` for `x ≤ 1` and `g_n (x) = exp (−(x − 1)^n)` for `x > 1`
(`HarmonicAnalysis.BeurlingAhlfors.testCutoff`; the source's example of a sufficiently smooth,
rapidly decaying `g_n` equal to `1` on `[0, 1]`). Only `n = 2` is used below. The derivatives are
the pointwise Wirtinger derivatives `HarmonicAnalysis.dz`, `HarmonicAnalysis.dzbar`. For `α < 1`
they agree almost everywhere with the weak ones: `f_{2,α}` is `C¹` off `0` (`g₂` is `C¹` at `1`)
and `C²` off `0` and the unit circle, and near `0`, `f = O (|z|^{2−2α})`,
`∇f = O (|z|^{1−2α})`. (For `α = 1`, `f = z / z̄` and the distribution `∂²f` has a Dirac mass at
`0`.) The source takes `p > 2`; the statements below hold for every `p` in the range given.

## Main results, for `n = 2`

* On the punctured unit disc (lecture notes, proof of Proposition 4.2):
  `∂²f = (2 − α)(1 − α) |z|^{−2α}` and `∂̄²f = (−α)(−α − 1) (z / z̄)² |z|^{−2α}`
  (`dz_dz_testFun_of_norm_lt_one`, `dzbar_dzbar_testFun_of_norm_lt_one`), so that, for
  `0 < α < 1/p`, `∫_Δ |∂²f|^p = π / (1 − αp) ((2 − α)(1 − α))^p` and
  `∫_Δ |∂̄²f|^p = π / (1 − αp) (α (α + 1))^p` (`lintegral_dz_dz_testFun_ball`,
  `lintegral_dzbar_dzbar_testFun_ball`).
* Outside the disc, the integrals of `|∂²f|^p` and `|∂̄²f|^p` stay bounded for `α ∈ [0, 1]`
  (`exists_bound_testFun_compl_ball`; the source: `|Dⁿ f (z)| ≤ P (n, α) |z|^M e^{−(|z| − 1)^n}`).
* `f_{2,α} ∈ W^{2,p}` for `1 ≤ p`, `0 < α < 1/p` (lecture notes, Exercise 4.1, for `p > 2`), in
  the form used: Schwartz
  functions `φ_k` with `∂̄²φ_k → ∂̄²f` and `∂²φ_k → ∂²f` in `L^p`
  (`exists_schwartz_tendsto_testFun`).

## References

* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), §4.1 (Exercise 4.1, Proposition 4.2).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap ENNReal Real ComplexConjugate

namespace HarmonicAnalysis.BeurlingAhlfors

/-- Dragičević's cutoff `g_n (x) = 1` for `x ≤ 1`, `exp (−(x − 1)^n)` for `x > 1`. -/
def testCutoff (n : ℕ) (x : ℝ) : ℝ := if x ≤ 1 then 1 else Real.exp (-(x - 1) ^ n)

/-- Dragičević's test function `f_{n,α} (z) = z^n |z|^{−2α} g_n (|z|)`. -/
def testFun (n : ℕ) (α : ℝ) (z : ℂ) : ℂ :=
  z ^ n * ((‖z‖ ^ (-2 * α) * testCutoff n ‖z‖ : ℝ) : ℂ)

/-- On the punctured unit disc, `∂²f_{2,α} (z) = (2 − α)(1 − α) |z|^{−2α}`. -/
theorem dz_dz_testFun_of_norm_lt_one (α : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    dz (dz (testFun 2 α)) z = (((2 - α) * (1 - α) * ‖z‖ ^ (-2 * α) : ℝ) : ℂ) := by
  sorry

/-- On the punctured unit disc, `∂̄²f_{2,α} (z) = (−α)(−α − 1) (z / z̄)² |z|^{−2α}`. -/
theorem dzbar_dzbar_testFun_of_norm_lt_one (α : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    dzbar (dzbar (testFun 2 α)) z =
      (((-α) * (-α - 1) : ℝ) : ℂ) * (z / conj z) ^ 2 * ((‖z‖ ^ (-2 * α) : ℝ) : ℂ) := by
  sorry

/-- `∫_Δ |∂²f_{2,α}|^p = π / (1 − αp) ((2 − α)(1 − α))^p` for `0 < α < 1/p`. -/
theorem lintegral_dz_dz_testFun_ball {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α) (hα : α * p < 1) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖dz (dz (testFun 2 α)) z‖ₑ ^ p =
      ENNReal.ofReal (π / (1 - α * p) * ((2 - α) * (1 - α)) ^ p) := by
  sorry

/-- `∫_Δ |∂̄²f_{2,α}|^p = π / (1 − αp) (α (α + 1))^p` for `0 < α < 1/p`. -/
theorem lintegral_dzbar_dzbar_testFun_ball {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖dzbar (dzbar (testFun 2 α)) z‖ₑ ^ p =
      ENNReal.ofReal (π / (1 - α * p) * (α * (α + 1)) ^ p) := by
  sorry

/-- Outside the unit disc, `∫ |∂²f_{2,α}|^p` and `∫ |∂̄²f_{2,α}|^p` are bounded uniformly in
`α ∈ [0, 1]`. -/
theorem exists_bound_testFun_compl_ball {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dz (dz (testFun 2 α)) z‖ₑ ^ p ≤ ENNReal.ofReal C ∧
        ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dzbar (dzbar (testFun 2 α)) z‖ₑ ^ p ≤
          ENNReal.ofReal C := by
  sorry

/-- `f_{2,α} ∈ W^{2,p}` for `1 ≤ p < ∞`, `0 < α < 1/p` (lecture notes, Exercise 4.1, where
`p > 2`), in the form used: there are Schwartz functions `φ_k` with `∂̄²φ_k → ∂̄²f_{2,α}` and
`∂²φ_k → ∂²f_{2,α}` in `L^p`. -/
theorem exists_schwartz_tendsto_testFun {p α : ℝ} (hp : 1 ≤ p) (hα0 : 0 < α) (hα : α * p < 1) :
    ∃ φ : ℕ → 𝓢(ℂ, ℂ),
      Tendsto (fun k => eLpNorm (fun z => (dzbarCLM ^ 2) (φ k) z - dzbar (dzbar (testFun 2 α)) z)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (fun z => (dzCLM ^ 2) (φ k) z - dz (dz (testFun 2 α)) z)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  sorry

end HarmonicAnalysis.BeurlingAhlfors
