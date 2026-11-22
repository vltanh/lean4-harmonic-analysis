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
from `𝕋²` to `ℝ²`, for symbols homogeneous of degree `0`): let `m : ℂ → ℂ` be continuous at
every `ξ ≠ 0`, with `m (t ξ) = m (ξ)` for `t > 0` (such an `m` is bounded, by its values on the
unit circle, and Borel measurable). Then for
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

## Main results

* `HarmonicAnalysis.exists_norm_le_of_homogeneous`: such a symbol is bounded;
  `HarmonicAnalysis.measurable_of_continuousAt_ne_zero`: it is Borel measurable.
* `HarmonicAnalysis.tsum_mul_sampledCoeff_mul_mFourier_eq`: the multiplied series
  `Σ_n m (n) sampledCoeff R f (n) e_n` at `x / R` is the lattice Riemann sum `Σ_n R⁻² φ_x (n / R)`
  of `φ_x (ξ) = e^{2πi ⟨ξ, x⟩} m (ξ) 𝓕 f (ξ)`, minus `R⁻² φ_x (0)`;
  `HarmonicAnalysis.tendsto_tsum_mul_sampledCoeff_mul_mFourier`: it tends to `T_m f (x)` as
  `R → ∞`.
* `HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm`: the transference.

## References

* K. de Leeuw, *On `L_p` multipliers*, Ann. of Math. 81 (1965), 364–379.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform Real

namespace HarmonicAnalysis

open UnitAddTorus

/-! ### Symbols homogeneous of degree `0` -/

/-- A symbol `m` that is continuous off `0` and homogeneous of degree `0` is bounded: off `0`,
`m (ξ) = m (ξ / |ξ|)`, and `m` is bounded on the (compact) unit circle. -/
theorem exists_norm_le_of_homogeneous {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) : ∃ B, 0 ≤ B ∧ ∀ ξ, ‖m ξ‖ ≤ B := by
  have hc : ContinuousOn m (Metric.sphere 0 1) := fun ξ hξ =>
    (hmc ξ (by rintro rfl; simp at hξ)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hc
  refine ⟨max C ‖m 0‖, (norm_nonneg _).trans (le_max_right _ _), fun ξ => ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact le_max_right _ _
  have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have h1 : (‖ξ‖⁻¹ : ℝ) * ξ ∈ Metric.sphere (0 : ℂ) 1 := by
    simp [hξ'.ne']
  rw [← hmh _ (inv_pos.2 hξ') ξ]
  exact (hC _ h1).trans (le_max_left _ _)

/-- A symbol `m` that is continuous off `0` is Borel measurable. -/
theorem measurable_of_continuousAt_ne_zero {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ) :
    Measurable m := by
  classical
  have h := ContinuousOn.measurable_piecewise (s := {0}) (continuousOn_singleton m 0)
    (fun ξ hξ => (hmc ξ hξ).continuousWithinAt) (measurableSet_singleton 0)
  rwa [Set.piecewise_same] at h

/-! ### The multiplied series as lattice Riemann sums -/

/-- `e_n (ofComplex (x / R)) = e^{2πi ⟨n / R, x⟩}`. -/
private lemma mFourier_ofComplex_div (n : Fin 2 → ℤ) (x : ℂ) (R : ℝ) :
    mFourier n (ofComplex (x / R)) =
      Complex.exp (↑(2 * π * inner ℝ (latticePoint n / R) x) * Complex.I) := by
  rw [mFourier_ofComplex]
  have h : inner ℝ (latticePoint n) (x / R) = inner ℝ (latticePoint n / R) x := by
    rw [div_eq_inv_mul, div_eq_inv_mul, ← Complex.ofReal_inv, ← Complex.real_smul,
      ← Complex.real_smul, real_inner_smul_left, real_inner_smul_right]
  rw [h]
  congr 1
  push_cast
  ring

/-- The terms of the multiplied series, for a bounded symbol: `|m (n) c_n e_n (z)| ≤ B |c_n|`. -/
private lemma norm_mul_sampledCoeff_mul_le {m : ℂ → ℂ} {B : ℝ} (hB : ∀ ξ, ‖m ξ‖ ≤ B)
    (R : ℝ) (f : ℂ → ℂ) (n : Fin 2 → ℤ) (z : UnitAddTorus (Fin 2)) :
    ‖m (latticePoint n) * sampledCoeff R f n * mFourier n z‖ ≤ B * ‖sampledCoeff R f n‖ := by
  rw [norm_mul, norm_mul, norm_mFourier_apply, mul_one]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

/-- The multiplied series, at `x / R`, as a lattice Riemann sum: for `m` homogeneous of degree `0`
(and continuous off `0`), `R > 0` and `φ_x (ξ) = e^{2πi ⟨ξ, x⟩} m (ξ) 𝓕 f (ξ)`,
`Σ_n m (n) sampledCoeff R f (n) e_n (x / R) = Σ_n R⁻² φ_x (n / R) − R⁻² φ_x (0)`. For `n ≠ 0`,
`m (n) = m (n / R)` and `e_n (x / R) = e^{2πi ⟨n / R, x⟩}`; the term `n = 0` is removed on the
left. -/
theorem tsum_mul_sampledCoeff_mul_mFourier_eq {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R) (x : ℂ) :
    ∑' n, m (latticePoint n) * sampledCoeff R f n * mFourier n (ofComplex (x / R)) =
      ∑' n, ((R : ℂ) ^ 2)⁻¹ * (Complex.exp (↑(2 * π * inner ℝ (latticePoint n / R) x) *
        Complex.I) * (m (latticePoint n / R) * 𝓕 (f : ℂ → ℂ) (latticePoint n / R))) -
        ((R : ℂ) ^ 2)⁻¹ * (m 0 * 𝓕 (f : ℂ → ℂ) 0) := by
  obtain ⟨B, -, hB⟩ := exists_norm_le_of_homogeneous hmc hmh
  set a : (Fin 2 → ℤ) → ℂ := fun n =>
    m (latticePoint n) * sampledCoeff R f n * mFourier n (ofComplex (x / R))
  set v : ℂ := ((R : ℂ) ^ 2)⁻¹ * (m 0 * 𝓕 (f : ℂ → ℂ) 0)
  have ha : Summable a := Summable.of_norm_bounded
    ((summable_sampledCoeff f hR).norm.mul_left B) fun n => norm_mul_sampledCoeff_mul_le hB _ _ _ _
  have ha0 : a 0 = 0 := by simp [a, sampledCoeff]
  have hr : (fun n => ((R : ℂ) ^ 2)⁻¹ * (Complex.exp (↑(2 * π * inner ℝ (latticePoint n / R) x) *
      Complex.I) * (m (latticePoint n / R) * 𝓕 (f : ℂ → ℂ) (latticePoint n / R)))) =
      Function.update a 0 v := by
    funext n
    by_cases hn : n = 0
    · subst hn
      simp [v]
    rw [Function.update_of_ne hn]
    have h1 : m (latticePoint n / R) = m (latticePoint n) := by
      rw [div_eq_inv_mul, ← Complex.ofReal_inv]
      exact hmh _ (inv_pos.2 hR) _
    simp only [a, sampledCoeff, hn, ↓reduceIte, mFourier_ofComplex_div, h1]
    ring
  rw [hr, (ha.hasSum.update 0 v).tsum_eq, ha0]
  ring

/-- The multiplied series, rescaled, tend to `T_m f`: for `m` continuous off `0` and homogeneous of
degree `0`, `Σ_n m (n) sampledCoeff R f (n) e_n (x / R) → T_m f (x)` as `R → ∞`, for every
`x ∈ ℂ`. By `HarmonicAnalysis.tsum_mul_sampledCoeff_mul_mFourier_eq`, these are lattice Riemann
sums of `φ_x (ξ) = e^{2πi ⟨ξ, x⟩} m (ξ) 𝓕 f (ξ)`, which is continuous off `0` and
`O ((1 + |ξ|)^{−3})`, minus `R⁻² φ_x (0) → 0`; they tend to `∫ φ_x = T_m f (x)`
(`HarmonicAnalysis.tendsto_riemannSum`). -/
theorem tendsto_tsum_mul_sampledCoeff_mul_mFourier {m : ℂ → ℂ}
    (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ) (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ)
    (f : 𝓢(ℂ, ℂ)) (x : ℂ) :
    Tendsto (fun R : ℕ => ∑' n, m (latticePoint n) * sampledCoeff R f n *
      mFourier n (ofComplex (x / (R : ℝ)))) atTop (𝓝 (fourierMultiplier m f x)) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_homogeneous hmc hmh
  obtain ⟨C, -, hC⟩ := exists_norm_add_le (𝓕 f)
  set φ : ℂ → ℂ := fun ξ => Complex.exp (↑(2 * π * inner ℝ ξ x) * Complex.I) *
    (m ξ * 𝓕 (f : ℂ → ℂ) ξ)
  have hF : Continuous (𝓕 (f : ℂ → ℂ)) := (𝓕 f).continuous
  have he : Continuous fun ξ : ℂ => Complex.exp (↑(2 * π * inner ℝ ξ x) * Complex.I) := by
    fun_prop
  have hφc : ∀ ξ ≠ 0, ContinuousAt φ ξ := fun ξ hξ =>
    he.continuousAt.mul ((hmc ξ hξ).mul hF.continuousAt)
  have hφb : ∀ ξ, ‖φ ξ‖ ≤ B * C * (1 + ‖ξ‖) ^ (-3 : ℝ) := fun ξ => by
    have h := hC 0 ξ
    simp only [zero_add, norm_zero, add_zero, one_pow, mul_one] at h
    rw [Real.rpow_neg (by positivity), Real.rpow_ofNat, mul_assoc]
    simp only [φ, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul (hB ξ) h (norm_nonneg _) hB0
  have hlim := tendsto_riemannSum hφc hφb
  have hint : ∫ ξ, φ ξ = fourierMultiplier m f x := by
    simp only [fourierMultiplier, Real.fourierInv_eq', smul_eq_mul, φ]
  rw [hint] at hlim
  have h0 : Tendsto (fun R : ℕ => ((R : ℂ) ^ 2)⁻¹ * (m 0 * 𝓕 (f : ℂ → ℂ) 0)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).pow 2
    simpa [inv_pow] using this.mul_const (m 0 * 𝓕 (f : ℂ → ℂ) 0)
  have := hlim.sub h0
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with R hR
  rw [tsum_mul_sampledCoeff_mul_mFourier_eq hmc hmh f (by exact_mod_cast hR) x]
  simp only [φ, Complex.ofReal_natCast]

/-- de Leeuw's transference, from `𝕋²` to `ℝ²`, for a symbol `m` that is continuous off `0` and
homogeneous of degree `0`: `‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}` for `1 < p < ∞`.

The proof is the standard argument, after de Leeuw, as in the module docstring. For a Schwartz
function `f` and `R ∈ ℕ`, with `c_R = sampledCoeff R f`, the `ℓ¹` extension of the torus bound
gives `‖Σ_n m (n) c_R (n) e_n‖_p ≤ ‖T_m‖_{L^p_0} ‖Σ_n c_R (n) e_n‖_p` on `𝕋²`. Rescaled by
`R^{2/p}`, the right side has `limsup` at most `‖T_m‖_{L^p_0} ‖f‖_p`; the left side is the
`L^p (ℂ)` norm of the multiplied series at `x / R`, restricted to the dilated cell
`R · (−½, ½]²`, which tends to `T_m f (x)` for every `x`. Fatou's lemma concludes. -/
theorem multiplierNorm_le_torusMultiplierNorm {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ torusMultiplierNorm (fun n => m (latticePoint n)) p := by
  set M := torusMultiplierNorm (fun n => m (latticePoint n)) p
  rcases eq_or_ne M ⊤ with hM | hM
  · rw [hM]
    exact le_top
  refine iSup_le fun f => ENNReal.div_le_of_le_mul ?_
  obtain ⟨B, -, hB⟩ := exists_norm_le_of_homogeneous hmc hmh
  have hp0 : 0 < p := by linarith
  set P := ENNReal.ofReal p
  -- The coefficients `sampledCoeff R f` are summable (for `R = 0` they vanish).
  have hsum : ∀ R : ℕ, Summable (sampledCoeff R f) := by
    intro R
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · have : sampledCoeff ((0 : ℕ) : ℝ) f = 0 := funext fun n => by simp [sampledCoeff]
      rw [this]
      exact summable_zero
    · exact summable_sampledCoeff f (by exact_mod_cast hR)
  have hc0 : ∀ R : ℕ, sampledCoeff R f 0 = 0 := fun R => by simp [sampledCoeff]
  -- The multiplied series `F R` on the torus, and its rescaling `H R` on the dilated cell.
  set F : ℕ → UnitAddTorus (Fin 2) → ℂ := fun R z =>
    ∑' n, m (latticePoint n) * sampledCoeff R f n * mFourier n z
  set G : ℕ → UnitAddTorus (Fin 2) → ℂ := fun R z =>
    ∑' n, sampledCoeff R f n * mFourier n z
  set H : ℕ → ℂ → ℂ := fun R => {y : ℂ | y / (R : ℝ) ∈ centredCell}.indicator
    fun y => F R (ofComplex (y / (R : ℝ)))
  have hFc : ∀ R, Continuous (F R) := fun R =>
    continuous_tsum (fun n => continuous_const.mul (mFourier n).continuous)
      ((hsum R).norm.mul_left B) fun n z => norm_mul_sampledCoeff_mul_le hB _ _ _ _
  have hHm : ∀ R, AEStronglyMeasurable (H R) volume := fun R =>
    ((hFc R).comp (continuous_ofComplex.comp (continuous_id.div_const _))).aestronglyMeasurable
      |>.indicator (measurableSet_dilatedCell _)
  -- `H R → T_m f` pointwise.
  have hHlim : ∀ x, Tendsto (fun R => H R x) atTop (𝓝 (fourierMultiplier m f x)) := by
    intro x
    refine (tendsto_tsum_mul_sampledCoeff_mul_mFourier hmc hmh f x).congr' ?_
    filter_upwards [eventually_div_natCast_mem_centredCell x] with R hR
    exact (Set.indicator_of_mem (s := {y : ℂ | y / (R : ℝ) ∈ centredCell}) (a := x) hR
      fun y => F R (ofComplex (y / (R : ℝ)))).symm
  -- Fatou's lemma.
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := P) hHm _
    (continuous_fourierMultiplier m f).aestronglyMeasurable (ae_of_all _ hHlim)
  have heq : ∀ᶠ R : ℕ in atTop, eLpNorm (H R) P volume =
      ENNReal.ofReal ((R : ℝ) ^ (2 / p)) * eLpNorm (F R) P volume := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    exact (ofReal_rpow_mul_eLpNorm_torus_eq_dilatedCell (F R) hp0 (by exact_mod_cast hR)).symm
  -- The `ℓ¹` extension of the torus bound.
  have hle : ∀ R : ℕ, ENNReal.ofReal ((R : ℝ) ^ (2 / p)) * eLpNorm (F R) P volume ≤
      M * (ENNReal.ofReal ((R : ℝ) ^ (2 / p)) * eLpNorm (G R) P volume) := fun R => by
    rw [mul_left_comm]
    gcongr
    exact eLpNorm_tsum_le_torusMultiplierNorm (fun n => m (latticePoint n)) hp.le (hsum R) (hc0 R)
  calc eLpNorm (fourierMultiplier m f) P volume
      ≤ liminf (fun R => eLpNorm (H R) P volume) atTop := hFatou
    _ = liminf (fun R : ℕ => ENNReal.ofReal ((R : ℝ) ^ (2 / p)) * eLpNorm (F R) P volume)
          atTop := liminf_congr heq
    _ ≤ limsup (fun R : ℕ => ENNReal.ofReal ((R : ℝ) ^ (2 / p)) * eLpNorm (F R) P volume)
          atTop := liminf_le_limsup
    _ ≤ limsup (fun R : ℕ => M * (ENNReal.ofReal ((R : ℝ) ^ (2 / p)) * eLpNorm (G R) P volume))
          atTop := limsup_le_limsup (Eventually.of_forall hle)
    _ = M * limsup (fun R : ℕ => ENNReal.ofReal ((R : ℝ) ^ (2 / p)) * eLpNorm (G R) P volume)
          atTop := ENNReal.limsup_const_mul_of_ne_top hM
    _ ≤ M * eLpNorm (f : ℂ → ℂ) P volume := by
        gcongr
        exact limsup_eLpNorm_sampledCoeff_le f hp

end HarmonicAnalysis
