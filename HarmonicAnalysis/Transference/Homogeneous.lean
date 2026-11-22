/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.FourierMultiplier.Basic
public import HarmonicAnalysis.Torus.TrigPoly
public import HarmonicAnalysis.Torus.Poisson
public import HarmonicAnalysis.Transference.RiemannSum

/-!
# Transference from the torus to the plane for homogeneous symbols

`HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm` (de Leeuw's theorem, in the direction
from `𝕋²` to `ℝ²`, for symbols homogeneous of degree `0`): let `m : ℂ → ℂ` be bounded and
measurable, continuous at every `ξ ≠ 0`, with `m (t ξ) = m (ξ)` for `t > 0`. Then for
`1 < p < ∞`, `‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}`, where on the torus `T_m` multiplies the
`n`-th Fourier coefficient by `m (n₀ + i n₁)`.

The proof, after de Leeuw: for a Schwartz function `f`, the coefficients `R⁻² 𝓕 f (n / R)`
(`n ≠ 0`) give a mean-zero function on `𝕋²` whose rescaled `L^p` norm tends at most to `‖f‖_p`
(periodisation and Poisson summation, `HarmonicAnalysis.limsup_eLpNorm_sampledCoeff_le`); by
homogeneity, `m (n) = m (n / R)`, the multiplied series, rescaled, are lattice Riemann sums of
`𝓕⁻¹ (m · 𝓕 f)` (`HarmonicAnalysis.tendsto_riemannSum`), and Fatou's lemma concludes, through
the `ℓ¹` extension of the torus bound (`HarmonicAnalysis.eLpNorm_tsum_le_torusMultiplierNorm`).
The mean-zero condition on the torus costs nothing: the coefficient at `n = 0` is removed, and its
contribution vanishes in the limit when `p > 1`.

## References

* K. de Leeuw, *On `L_p` multipliers*, Ann. of Math. 81 (1965), 364–379.
-/

@[expose] public section

noncomputable section

namespace HarmonicAnalysis

/-- de Leeuw's transference, from `𝕋²` to `ℝ²`, for a bounded measurable symbol `m` that is
continuous off `0` and homogeneous of degree `0`: `‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}` for
`1 < p < ∞`. -/
theorem multiplierNorm_le_torusMultiplierNorm {m : ℂ → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ torusMultiplierNorm (fun n => m (latticePoint n)) p := by
  sorry

end HarmonicAnalysis
