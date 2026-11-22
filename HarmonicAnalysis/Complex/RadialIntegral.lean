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
# Integrals of radial functions on `ℂ`

* `HarmonicAnalysis.lintegral_comp_norm`: `∫⁻_ℂ g (|z|) dz = 2π ∫⁻_0^∞ g (r) r dr` (polar
  coordinates).
* `HarmonicAnalysis.lintegral_ball_norm_rpow`: `∫_{|z| < 1} |z|^{−s} dz = 2π / (2 − s)` for
  `s < 2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real

namespace HarmonicAnalysis

/-- Integrals of radial functions: `∫⁻_ℂ g (|z|) dz = 2π ∫⁻_0^∞ g (r) r dr`. -/
theorem lintegral_comp_norm {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z : ℂ, g ‖z‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  sorry

/-- `∫_{|z| < 1} |z|^{−s} dz = 2π / (2 − s)` for `s < 2`. -/
theorem lintegral_ball_norm_rpow {s : ℝ} (hs : s < 2) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖z‖ ^ (-s)) =
      ENNReal.ofReal (2 * π / (2 - s)) := by
  sorry

end HarmonicAnalysis
