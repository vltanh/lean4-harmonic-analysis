/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Integrals of radial functions on `ℂ`, and logarithmic averages

* `HarmonicAnalysis.lintegral_comp_normSq`: `∫⁻_ℂ g (|z|²) dz = π ∫⁻_0^∞ g (t) dt` (polar
  coordinates and `t = r²`).
* `HarmonicAnalysis.integral_inv_add`: `∫_0^1 dt / (t + a) = log (1 + 1/a)` for `a > 0`.
* `HarmonicAnalysis.tendsto_integral_div_log`: if `g (u) → c` as `u → ∞`, then
  `(log (1 + U))⁻¹ ∫_0^U g (u) / (1 + u) du → c` as `U → ∞`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

namespace HarmonicAnalysis

/-- Integrals of radial functions: `∫⁻_ℂ g (|z|²) dz = π ∫⁻_0^∞ g (t) dt`. -/
theorem lintegral_comp_normSq {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z : ℂ, g (Complex.normSq z) = ENNReal.ofReal π * ∫⁻ t in Ioi (0 : ℝ), g t := by
  sorry

/-- `∫_0^1 dt / (t + a) = log (1 + 1/a)` for `a > 0`. -/
theorem integral_inv_add {a : ℝ} (ha : 0 < a) :
    ∫ t in (0 : ℝ)..1, (t + a)⁻¹ = Real.log (1 + a⁻¹) := by
  sorry

/-- Logarithmic averages: if `g (u) → c` as `u → ∞` and `g` is integrable on bounded intervals,
then `(log (1 + U))⁻¹ ∫_0^U g (u) / (1 + u) du → c` as `U → ∞`. -/
theorem tendsto_integral_div_log {g : ℝ → ℝ} {c : ℝ} (hg : Tendsto g atTop (𝓝 c))
    (hint : ∀ U, IntervalIntegrable g volume 0 U) :
    Tendsto (fun U => (∫ u in (0 : ℝ)..U, g u / (1 + u)) / Real.log (1 + U)) atTop (𝓝 c) := by
  sorry

end HarmonicAnalysis
