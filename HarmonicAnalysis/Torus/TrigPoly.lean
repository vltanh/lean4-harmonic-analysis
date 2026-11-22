/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Trigonometric polynomials and Fourier multipliers on the torus

On the torus `𝕋^ι = (ℝ / ℤ)^ι`, with Mathlib's measure (of total mass one) and the monomials
`e_n = UnitAddTorus.mFourier n`, `n ∈ ℤ^ι`:

* `HarmonicAnalysis.trigPoly c = Σ_n c_n e_n`, for finitely supported coefficients `c`;
* `HarmonicAnalysis.torusMultiplier m c = Σ_n m (n) c_n e_n`, the Fourier multiplier with symbol
  `m : ℤ^ι → ℂ` applied to `trigPoly c`;
* `HarmonicAnalysis.torusMultiplierNorm m p`, the norm of this multiplier on the mean-zero
  subspace `L^p_0 (𝕋^ι)`, computed on the dense subspace of mean-zero trigonometric polynomials
  (`c₀ = 0`): `⨆ ‖T_m (trigPoly c)‖_p / ‖trigPoly c‖_p` in `ℝ≥0∞`.

## Main results

* `HarmonicAnalysis.eLpNorm_tsum_le_torusMultiplierNorm` (the `ℓ¹` extension): for a bounded
  symbol, `‖Σ_n m (n) c_n e_n‖_p ≤ ‖T_m‖_{L^p_0} ‖Σ_n c_n e_n‖_p` for every summable `c` with
  `c₀ = 0`, the series converging uniformly.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HarmonicAnalysis

open UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-- The trigonometric polynomial `x ↦ Σ_n c_n e^{2πi ⟨n, x⟩}` on the torus `𝕋^ι`. -/
def trigPoly (c : (ι → ℤ) →₀ ℂ) (x : UnitAddTorus ι) : ℂ :=
  c.sum fun n a => a * mFourier n x

/-- The Fourier multiplier with symbol `m : ℤ^ι → ℂ` applied to the trigonometric polynomial with
coefficients `c`: `x ↦ Σ_n m (n) c_n e^{2πi ⟨n, x⟩}`. -/
def torusMultiplier (m : (ι → ℤ) → ℂ) (c : (ι → ℤ) →₀ ℂ) (x : UnitAddTorus ι) : ℂ :=
  c.sum fun n a => m n * a * mFourier n x

/-- `‖T_m‖_{L^p_0 (𝕋^ι) → L^p_0 (𝕋^ι)}`: the supremum over the (dense) mean-zero trigonometric
polynomials (`c₀ = 0`). -/
def torusMultiplierNorm (m : (ι → ℤ) → ℂ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ (c : (ι → ℤ) →₀ ℂ) (_ : c 0 = 0),
    eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume /
      eLpNorm (trigPoly c) (ENNReal.ofReal p) volume

/-- The `ℓ¹` extension: for a bounded symbol `m`, `1 ≤ p` and summable coefficients `c` with
`c₀ = 0`, `‖Σ_n m (n) c_n e_n‖_p ≤ ‖T_m‖_{L^p_0} ‖Σ_n c_n e_n‖_p`. -/
theorem eLpNorm_tsum_le_torusMultiplierNorm {m : (ι → ℤ) → ℂ} (hm : ∃ C, ∀ n, ‖m n‖ ≤ C)
    {p : ℝ} (hp : 1 ≤ p) {c : (ι → ℤ) → ℂ} (hc : Summable c) (hc0 : c 0 = 0) :
    eLpNorm (fun x => ∑' n, m n * c n * mFourier n x) (ENNReal.ofReal p) volume ≤
      torusMultiplierNorm m p *
        eLpNorm (fun x => ∑' n, c n * mFourier n x) (ENNReal.ofReal p) volume := by
  sorry

end HarmonicAnalysis
