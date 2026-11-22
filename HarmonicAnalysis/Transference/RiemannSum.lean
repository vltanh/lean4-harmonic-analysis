/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Torus.Cube

/-!
# Lattice Riemann sums of functions continuous off the origin

`HarmonicAnalysis.tendsto_riemannSum`: if `φ : ℂ → ℂ` is continuous at every `ξ ≠ 0` and
`|φ (ξ)| ≤ C (1 + |ξ|)^{−3}`, then the Riemann sums over the lattice `R⁻¹ ℤ²`,
`Σ_{n ∈ ℤ²} R⁻² φ (n / R)`, tend to `∫_ℂ φ` as `R → ∞`. No continuity at `0` is needed: the
cells `R⁻¹ (n + [0, 1)²)` shrink, and the step functions `ξ ↦ φ (⌊R ξ⌋ / R)` converge to `φ` off
`0` under the integrable bound `C' (1 + |ξ|)^{−3}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace HarmonicAnalysis

/-- Lattice Riemann sums: for `φ` continuous off `0` with `|φ (ξ)| ≤ C (1 + |ξ|)^{−3}`,
`Σ_{n ∈ ℤ²} R⁻² φ (n / R) → ∫_ℂ φ` as `R → ∞`. -/
theorem tendsto_riemannSum {φ : ℂ → ℂ} (hφ : ∀ ξ ≠ 0, ContinuousAt φ ξ) {C : ℝ}
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-3 : ℝ)) :
    Tendsto (fun R : ℕ => ∑' n : Fin 2 → ℤ, ((R : ℂ) ^ 2)⁻¹ * φ (latticePoint n / R)) atTop
      (𝓝 (∫ ξ, φ ξ)) := by
  sorry

end HarmonicAnalysis
