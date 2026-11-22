/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.CircPoly
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import HarmonicAnalysis.FourierMultiplier.Density
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.Floor

/-!
# Transference of Fourier multipliers from the line to the circle

`𝕋 = ℝ / ℤ` with its normalised Haar measure, `e_n (t) = e^{2πi n t}`. The trigonometric polynomial
with coefficients `a_n` in a complex Banach space is `Σ_n a_n e_n` (`circPoly a`).

Let `X`, `Y` be complex Banach spaces, `1 < p < ∞`, and let `m : ℝ → 𝓛 (X, Y)` be bounded and
strongly measurable, with `m (·) x` continuous at the integers for all `x`. If `T_m h = (m ĥ)ˇ` is
bounded from `L^p (ℝ; X)` to `L^p (ℝ; Y)` with norm `C` (on Schwartz functions), then
`‖Σ_k m (k) a_k e_k‖_{L^p (𝕋; Y)} ≤ C ‖Σ_k a_k e_k‖_{L^p (𝕋; X)}` for all trigonometric polynomials
(`eLpNorm_circPoly_multiplier_le`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Section 5.7.a,
pp. 458–460, for the dimension `d = 1`: Proposition 5.7.1, Lemma 5.7.2
(`tendsto_integral_dilate_multiplier`) and Lemma 5.7.3 (`tendsto_eLpNorm_dilate_smul`), with the
book's proofs: the pairing of `T_m (φ (ε ·) f)` with `ψ (ε ·) g` for Schwartz functions `φ`, `ψ`,
(5.58), periodisation and Riemann sums, and then Gaussians `φ`, `ψ`. In the book the integers are
Lebesgue points of `m (·) x`; here they are points of continuity. The duality at the end is
Proposition 1.3.1, pp. 37–38 (simple functions with values in `Y*` norm `L^p (𝕋; Y)`), and the
density of the trigonometric polynomials (`eLpNorm_le_of_forall_circPoly`). The multiplier norm on
the line is invariant under dilations (`eLpNorm_fourierInv_multiplier_dilate_le`), which is used in
(5.61), p. 465.

The other direction, from the torus to the plane, is Proposition 5.7.4 and Corollary 5.7.6 of the
same section, for scalar symbols: `HarmonicAnalysis.Transference.ContinuousSymbol` and
`HarmonicAnalysis.Transference.Homogeneous`.

A shorter transference: if `m` is constant near each frequency `k` of `f = Σ_k a_k e_k`, take a
Schwartz function `θ` whose Fourier transform has compact support. Then, for small `ε`,
`T_m (θ (ε ·) f) = θ (ε ·) Σ_k m (k) a_k e_k` exactly, and Lemma 5.7.3 on both sides gives the
inequality without duality. This is the argument of HNVW I, Proposition 5.2.5 and Lemma 5.2.6, pp.
391–393, for the Hilbert transform.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal FourierTransform Topology SchwartzMap

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Lemma 5.7.3: periodisation and Riemann sums -/

private theorem coe_add_intCast (x : ℝ) (k : ℤ) :
    ((x + k : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  simp

/-- The integral over `ℝ` as an integral over `(0, 1]` of the sum of the translates. -/
private theorem lintegral_eq_lintegral_Ioc_tsum {h : ℝ → ℝ≥0∞} (hh : AEMeasurable h) :
    ∫⁻ x, h x = ∫⁻ x in Set.Ioc (0 : ℝ) 1, ∑' k : ℤ, h (x + k) := by
  have h1 : ∀ k : ℤ, ∫⁻ x in Set.Ioc (k : ℝ) (k + 1), h x =
      ∫⁻ x in Set.Ioc (0 : ℝ) 1, h (x + k) := fun k => by
    rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
      ← lintegral_add_right_eq_self _ (k : ℝ)]
    refine lintegral_congr fun x => ?_
    have h2 : x + k ∈ Set.Ioc (k : ℝ) (k + 1) ↔ x ∈ Set.Ioc (0 : ℝ) 1 := by
      simp only [Set.mem_Ioc, lt_add_iff_pos_left, add_comm (k : ℝ) 1, add_le_add_iff_right]
    simp only [Set.indicator_apply, h2]
  have h2 : ∀ k : ℤ, AEMeasurable (fun x => h (x + k)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    fun k => (hh.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving).restrict
  rw [lintegral_tsum h2, ← setLIntegral_univ, ← iUnion_Ioc_intCast ℝ,
    lintegral_iUnion (fun k => measurableSet_Ioc) (Set.pairwise_disjoint_Ioc_intCast ℝ)]
  exact tsum_congr h1

/-- The integral over `(0, 1]` of a periodic function is the integral over `𝕋`. -/
private theorem lintegral_Ioc_coe (g : UnitAddCircle → ℝ≥0∞) :
    ∫⁻ x in Set.Ioc (0 : ℝ) 1, g x = ∫⁻ t, g t ∂haarAddCircle := by
  have h := UnitAddCircle.lintegral_preimage 0 g
  rw [zero_add] at h
  rw [h, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- The preimages under `ℝ → 𝕋` of null sets are null sets. -/
private theorem quasiMeasurePreserving_coe :
    QuasiMeasurePreserving (fun x : ℝ => (x : UnitAddCircle)) volume haarAddCircle := by
  refine ⟨AddCircle.measurable_mk', Measure.AbsolutelyContinuous.mk fun N hN h0 => ?_⟩
  rw [Measure.map_apply AddCircle.measurable_mk' hN,
    ← lintegral_indicator_one (AddCircle.measurable_mk' hN),
    lintegral_eq_lintegral_Ioc_tsum
      (measurable_one.indicator (AddCircle.measurable_mk' hN)).aemeasurable]
  set g : UnitAddCircle → ℝ≥0∞ := fun t => ∑' _ : ℤ, N.indicator 1 t
  have h1 : ∀ x : ℝ, ∑' k : ℤ, ((fun x : ℝ => (x : UnitAddCircle)) ⁻¹' N).indicator
      (1 : ℝ → ℝ≥0∞) (x + k) = g x := fun x => by
    classical
    refine tsum_congr fun k => ?_
    simp only [Set.indicator_apply, Set.mem_preimage, coe_add_intCast, Pi.one_apply]
  refine (lintegral_congr h1).trans ?_
  rw [lintegral_Ioc_coe, lintegral_tsum fun _ => (measurable_one.indicator hN).aemeasurable]
  simp [lintegral_indicator_one hN, h0]

/-- A Riemann sum, as the integral of a step function. -/
private theorem mul_tsum_eq_lintegral (W : ℝ → ℝ≥0∞) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ENNReal.ofReal ε * ∑' k : ℤ, W (ε * (x + k)) = ∫⁻ y, W (ε * (x + ⌊y / ε⌋)) := by
  have h1 : ∀ k : ℤ, ∫⁻ y in Set.Ico (0 + k • ε) (0 + (k + 1) • ε), W (ε * (x + ⌊y / ε⌋)) =
      ENNReal.ofReal ε * W (ε * (x + k)) := fun k => by
    have h2 : ∀ y ∈ Set.Ico (0 + k • ε) (0 + (k + 1) • ε),
        W (ε * (x + ⌊y / ε⌋)) = W (ε * (x + k)) := by
      intro y hy
      simp only [zero_add, zsmul_eq_mul, Int.cast_add, Int.cast_one, Set.mem_Ico] at hy
      have h3 : ⌊y / ε⌋ = k :=
        Int.floor_eq_iff.2 ⟨(le_div_iff₀ hε).2 hy.1, (div_lt_iff₀ hε).2 hy.2⟩
      rw [h3]
    rw [setLIntegral_congr_fun measurableSet_Ico h2, setLIntegral_const, Real.volume_Ico,
      mul_comm]
    congr 2
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]
    ring
  rw [← ENNReal.tsum_mul_left, ← setLIntegral_univ, ← iUnion_Ico_add_zsmul hε 0,
    lintegral_iUnion (fun k => measurableSet_Ico) (Set.pairwise_disjoint_Ico_add_zsmul 0 ε)]
  exact (tsum_congr h1).symm

private theorem abs_sub_le {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) (y : ℝ) :
    |ε * (x + ⌊y / ε⌋) - y| ≤ ε := by
  have h1 : ε * ⌊y / ε⌋ ≤ y := by
    calc ε * ⌊y / ε⌋ ≤ ε * (y / ε) := by
          gcongr
          exact Int.floor_le _
      _ = y := mul_div_cancel₀ y hε.ne'
  have h2 : y ≤ ε * (⌊y / ε⌋ + 1) := by
    calc y = ε * (y / ε) := (mul_div_cancel₀ y hε.ne').symm
      _ ≤ ε * (⌊y / ε⌋ + 1) := by
          gcongr
          exact (Int.lt_floor_add_one _).le
  have h3 : 0 ≤ ε * x := mul_nonneg hε.le hx.1.le
  have h4 : ε * x ≤ ε := mul_le_of_le_one_right hε.le hx.2
  rw [abs_le]
  constructor <;> linarith

/-- The terms of the Riemann sums of a function with a bound `C (1 + |y|)^{−2}`. -/
private theorem riemann_le {W : ℝ → ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (hW : ∀ y, W y ≤ ENNReal.ofReal (C * (1 + ‖y‖) ^ (-2 : ℝ))) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) (y : ℝ) :
    W (ε * (x + ⌊y / ε⌋)) ≤ ENNReal.ofReal (4 * C * (1 + ‖y‖) ^ (-2 : ℝ)) := by
  refine (hW _).trans (ENNReal.ofReal_le_ofReal ?_)
  set z := ε * (x + ⌊y / ε⌋) with hz
  have h1 : |z - y| ≤ 1 := (abs_sub_le hε hx y).trans hε1
  have h2 : (1 + ‖y‖) / 2 ≤ 1 + ‖z‖ := by
    have h3 : |y| ≤ |z| + |z - y| := by
      have h4 := abs_sub_abs_le_abs_sub y z
      rw [abs_sub_comm y z] at h4
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [abs_nonneg z]
  have h5 : (1 + ‖z‖) ^ (-2 : ℝ) ≤ 4 * (1 + ‖y‖) ^ (-2 : ℝ) := by
    calc (1 + ‖z‖) ^ (-2 : ℝ) ≤ ((1 + ‖y‖) / 2) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by norm_num)
      _ = 4 * (1 + ‖y‖) ^ (-2 : ℝ) := by
          rw [Real.div_rpow (by positivity) zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul,
            mul_comm, Real.rpow_two]
          norm_num
  calc C * (1 + ‖z‖) ^ (-2 : ℝ) ≤ C * (4 * (1 + ‖y‖) ^ (-2 : ℝ)) := by gcongr
    _ = 4 * C * (1 + ‖y‖) ^ (-2 : ℝ) := by ring

private theorem lintegral_bound_ne_top (C : ℝ) :
    ∫⁻ y : ℝ, ENNReal.ofReal (C * (1 + ‖y‖) ^ (-2 : ℝ)) ≠ ∞ :=
  ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul
    C).lintegral_lt_top.ne

/-- The Riemann sums `ε Σ_k W (ε (x + k))` converge to `∫ W` as `ε ↓ 0`: they are the integrals of
the step functions `W (ε (x + ⌊y / ε⌋))`, which converge to `W (y)`. -/
private theorem tendsto_riemann {W : ℝ → ℝ≥0∞} (hWc : Continuous W) {C : ℝ} (hC : 0 ≤ C)
    (hW : ∀ y, W y ≤ ENNReal.ofReal (C * (1 + ‖y‖) ^ (-2 : ℝ))) {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ε * ∑' k : ℤ, W (ε * (x + k))) (𝓝[>] 0)
      (𝓝 (∫⁻ y, W y)) := by
  have h1 : Tendsto (fun ε : ℝ => ∫⁻ y, W (ε * (x + ⌊y / ε⌋))) (𝓝[>] 0) (𝓝 (∫⁻ y, W y)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun y => ENNReal.ofReal (4 * C * (1 + ‖y‖) ^ (-2 : ℝ))) ?_ ?_ (lintegral_bound_ne_top _)
      (ae_of_all _ fun y => ?_)
    · refine Eventually.of_forall fun ε => hWc.measurable.comp ?_
      have hfl : Measurable fun y : ℝ => ((⌊y / ε⌋ : ℤ) : ℝ) :=
        measurable_from_top.comp (Int.measurable_floor.comp (measurable_id.div_const ε))
      exact (hfl.const_add x).const_mul ε
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)]
        with ε hε hε1
      exact ae_of_all _ fun y => riemann_le hC hW hε (le_of_lt hε1) hx y
    · refine (hWc.tendsto y).comp (tendsto_iff_norm_sub_tendsto_zero.2 ?_)
      refine squeeze_zero' (Eventually.of_forall fun ε => norm_nonneg _) ?_
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact abs_sub_le hε hx y
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (mul_tsum_eq_lintegral W hε x).symm

/-- The Riemann sums are bounded, uniformly in `x` and `ε`. -/
private theorem riemann_bound {W : ℝ → ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (hW : ∀ y, W y ≤ ENNReal.ofReal (C * (1 + ‖y‖) ^ (-2 : ℝ))) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ENNReal.ofReal ε * ∑' k : ℤ, W (ε * (x + k)) ≤
      ∫⁻ y : ℝ, ENNReal.ofReal (4 * C * (1 + ‖y‖) ^ (-2 : ℝ)) := by
  rw [mul_tsum_eq_lintegral W hε x]
  exact lintegral_mono fun y => riemann_le hC hW hε hε1 hx y

/-- HNVW I, proof of Lemma 5.7.3: `ε ∫_ℝ W (ε x) g (x) dx → ∫ W ∫_𝕋 g`, by periodisation and the
convergence of the Riemann sums of `W`. -/
private theorem tendsto_lintegral_dilate {W : ℝ → ℝ≥0∞} (hWc : Continuous W) {C : ℝ} (hC : 0 ≤ C)
    (hW : ∀ y, W y ≤ ENNReal.ofReal (C * (1 + ‖y‖) ^ (-2 : ℝ))) {g : UnitAddCircle → ℝ≥0∞}
    (hg : AEMeasurable g haarAddCircle) (hgi : ∫⁻ t, g t ∂haarAddCircle ≠ ∞) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ε * ∫⁻ x : ℝ, W (ε * x) * g (x : UnitAddCircle)) (𝓝[>] 0)
      (𝓝 ((∫⁻ y, W y) * ∫⁻ t, g t ∂haarAddCircle)) := by
  have hg' : AEMeasurable fun x : ℝ => g (x : UnitAddCircle) :=
    hg.comp_quasiMeasurePreserving quasiMeasurePreserving_coe
  have hWm : ∀ ε a : ℝ, Measurable fun x : ℝ => W (ε * (x + a)) := fun ε a =>
    hWc.measurable.comp (by fun_prop)
  -- the periodisation
  have h1 : ∀ ε : ℝ, ENNReal.ofReal ε * ∫⁻ x : ℝ, W (ε * x) * g (x : UnitAddCircle) =
      ∫⁻ x in Set.Ioc (0 : ℝ) 1,
        (ENNReal.ofReal ε * ∑' k : ℤ, W (ε * (x + k))) * g (x : UnitAddCircle) := fun ε => by
    have hm : AEMeasurable fun x : ℝ => W (ε * x) * g (x : UnitAddCircle) :=
      (hWc.measurable.comp (measurable_const_mul ε)).aemeasurable.mul hg'
    rw [lintegral_eq_lintegral_Ioc_tsum hm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    simp only [coe_add_intCast]
    rw [ENNReal.tsum_mul_right, mul_assoc]
  have h2 : (∫⁻ y, W y) * ∫⁻ t, g t ∂haarAddCircle =
      ∫⁻ x in Set.Ioc (0 : ℝ) 1, (∫⁻ y, W y) * g (x : UnitAddCircle) := by
    rw [lintegral_const_mul'' _ hg'.restrict, lintegral_Ioc_coe]
  simp only [h1, h2]
  -- dominated convergence
  refine tendsto_lintegral_filter_of_dominated_convergence' (fun x : ℝ =>
    (∫⁻ y : ℝ, ENNReal.ofReal (4 * C * (1 + ‖y‖) ^ (-2 : ℝ))) * g (x : UnitAddCircle)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ε =>
      ((Measurable.tsum fun k : ℤ => hWm ε k).const_mul _).aemeasurable.mul hg'.restrict
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)]
      with ε hε hε1
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx => ?_)
    gcongr
    exact riemann_bound hC hW hε (le_of_lt hε1) hx
  · rw [lintegral_const_mul'' _ hg'.restrict, lintegral_Ioc_coe]
    exact ENNReal.mul_ne_top (lintegral_bound_ne_top _) hgi
  · have hfin : ∀ᵐ x : ℝ, g (x : UnitAddCircle) < ∞ :=
      quasiMeasurePreserving_coe.ae (ae_lt_top' hg hgi)
    filter_upwards [ae_restrict_of_ae hfin, ae_restrict_mem measurableSet_Ioc] with x hgx hx
    exact ENNReal.Tendsto.mul_const (tendsto_riemann hWc hC hW hx) (Or.inr hgx.ne)

/-- A Schwartz function is `O ((1 + |y|)^{−2/p})`. -/
private theorem schwartz_rpow_le {p : ℝ} (hp : 1 ≤ p) (φ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖φ y‖ₑ ^ p ≤ ENNReal.ofReal (C * (1 + ‖y‖) ^ (-2 : ℝ)) := by
  obtain ⟨C, hC, hφ⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, (1 + ‖y‖) ^ 2 * ‖φ y‖ ≤ C := by
    refine ⟨2 ^ 2 * ((Finset.Iic (2, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ,
      by positivity, fun y => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (2, 0)) le_rfl le_rfl φ y
    simpa only [norm_iteratedFDeriv_zero] using h
  refine ⟨C ^ p, by positivity, fun y => ?_⟩
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have h0 : (0 : ℝ) < 1 + ‖y‖ := by linarith
  have h2 : ‖φ y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg h0.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hφ y
  calc ‖φ y‖ ^ p ≤ (C * (1 + ‖y‖) ^ (-2 : ℝ)) ^ p := by gcongr
    _ = C ^ p * (1 + ‖y‖) ^ (-2 * p) := by
        rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul h0.le]
    _ ≤ C ^ p * (1 + ‖y‖) ^ (-2 : ℝ) := by
        gcongr
        linarith

/-- **HNVW I, Lemma 5.7.3**, for `d = 1`: for `φ ∈ 𝓢 (ℝ)` and `f ∈ L^p (𝕋; X)`, `1 ≤ p < ∞`,
`ε^{1/p} ‖φ (ε ·) f‖_{L^p (ℝ; X)} → ‖φ‖_{L^p (ℝ)} ‖f‖_{L^p (𝕋; X)}` as `ε ↓ 0`. As in the book,
`ε ∫_ℝ ‖φ (ε x) f (x)‖^p dx = ∫_0^1 (ε Σ_k |φ (ε (x + k))|^p) ‖f (x)‖^p dx`, and the Riemann sums
in the parentheses are bounded and converge to `∫ |φ|^p`. -/
theorem tendsto_eLpNorm_dilate_smul {p : ℝ} (hp : 1 ≤ p) (φ : 𝓢(ℝ, ℂ)) {f : UnitAddCircle → X}
    (hf : MemLp f (ENNReal.ofReal p) haarAddCircle) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ε ^ (1 / p) * eLpNorm (fun x : ℝ =>
        φ (ε * x) • f (x : UnitAddCircle)) (ENNReal.ofReal p) volume) (𝓝[>] 0)
      (𝓝 (eLpNorm φ (ENNReal.ofReal p) volume * eLpNorm f (ENNReal.ofReal p) haarAddCircle)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C, hC, hφ⟩ := schwartz_rpow_le hp φ
  have hWc : Continuous fun y => ‖φ y‖ₑ ^ p :=
    ENNReal.continuous_rpow_const.comp φ.continuous.enorm
  have hfm := hf.aestronglyMeasurable
  have hnorm := eLpNorm_ofReal_rpow_eq_lintegral hp0 hfm
  have hfin : ∫⁻ t, ‖f t‖ₑ ^ p ∂haarAddCircle ≠ ∞ := by
    rw [← hnorm]
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le hf.eLpNorm_ne_top
  have h := tendsto_lintegral_dilate hWc hC hφ (hfm.enorm.pow_const p) hfin
  rw [← hnorm, ← eLpNorm_ofReal_rpow_eq_lintegral hp0 φ.continuous.aestronglyMeasurable,
    ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le] at h
  -- the `p`-th roots
  have h1 := (ENNReal.continuous_rpow_const (y := 1 / p)).continuousAt.tendsto.comp h
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h1
  refine h1.congr fun ε => ?_
  have hm : AEStronglyMeasurable (fun x : ℝ => φ (ε * x) • f (x : UnitAddCircle)) volume :=
    (φ.continuous.comp (continuous_const_mul ε)).aestronglyMeasurable.smul
      (hfm.comp_quasiMeasurePreserving quasiMeasurePreserving_coe)
  have h2 : ∫⁻ x : ℝ, ‖φ (ε * x)‖ₑ ^ p * ‖f (x : UnitAddCircle)‖ₑ ^ p =
      eLpNorm (fun x : ℝ => φ (ε * x) • f (x : UnitAddCircle)) (ENNReal.ofReal p) volume ^ p := by
    rw [eLpNorm_ofReal_rpow_eq_lintegral hp0 hm]
    refine lintegral_congr fun x => ?_
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  simp only [Function.comp_apply, h2]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-! ### Lemma 5.7.2: the action of the periodic multiplier -/

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- `∫ ⟨𝓕⁻ u, v⟩ = ∫ ⟨u, 𝓕⁻ v⟩`. -/
private theorem integral_fourierInv_dual [CompleteSpace Y] {u : ℝ → Y} {v : ℝ → Y →L[ℂ] ℂ}
    (hu : Integrable u) (hv : Integrable v) : ∫ x, v x (𝓕⁻ u x) = ∫ ξ, 𝓕⁻ v ξ (u ξ) := by
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.apply ℂ ℂ : Y →L[ℂ] (Y →L[ℂ] ℂ) →L[ℂ] ℂ) (L := -innerₗ ℝ)
    Real.continuous_fourierChar (continuous_inner (𝕜 := ℝ) (E := ℝ)).neg hu hv
  have hflip : (-innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = -innerₗ ℝ := by
    ext
    simp
  rw [hflip] at h
  exact h

private theorem integrable_dilate_smul (φ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (a : ℤ →₀ X) :
    Integrable fun x : ℝ => φ (ε * x) • circPoly a (x : UnitAddCircle) := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_circPoly a)).isBounded.exists_norm_le
  have hc : Continuous fun x : ℝ => circPoly a (x : UnitAddCircle) :=
    (continuous_circPoly a).comp (AddCircle.continuous_mk' 1)
  exact (φ.integrable.comp_mul_left' hε.ne').smul_bdd C hc.aestronglyMeasurable
    (ae_of_all _ fun x => hC _ ⟨_, rfl⟩)

/-- `(φ (ε ·) e_k)^ = ε⁻¹ φ̂ ((· − k) / ε)`. -/
private theorem integral_exp_dilate (φ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (k : ℤ) (ξ : ℝ) :
    ∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) *
      (φ (ε * x) * fourier k (x : UnitAddCircle)) =
      ((ε⁻¹ : ℝ) : ℂ) * 𝓕 φ (ε⁻¹ * (ξ - k)) := by
  have h := Measure.integral_comp_mul_left (fun w : ℝ =>
    Complex.exp (((-2 * Real.pi * w * (ε⁻¹ * (ξ - k)) : ℝ) : ℂ) * Complex.I) * φ w) ε
  rw [abs_of_pos (inv_pos.2 hε), Complex.real_smul] at h
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  refine Eq.trans ?_ h
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [fourier_coe_apply, mul_comm (φ (ε * x)), ← mul_assoc, ← Complex.exp_add]
  congr 2
  have hε' : (ε : ℂ) ≠ 0 := by simpa using hε.ne'
  push_cast
  field_simp
  ring

/-- `(φ (ε ·) f)^ = Σ_k a_k ε⁻¹ φ̂ ((· − k) / ε)`, for `f = Σ_k a_k e_k`. -/
private theorem fourier_dilate_smul [CompleteSpace X] (φ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε)
    (a : ℤ →₀ X) (ξ : ℝ) :
    𝓕 (fun x : ℝ => φ (ε * x) • circPoly a (x : UnitAddCircle)) ξ =
      a.sum fun k y => (((ε⁻¹ : ℝ) : ℂ) * 𝓕 φ (ε⁻¹ * (ξ - k))) • y := by
  have hi : ∀ k : ℤ, Integrable fun x : ℝ =>
      Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) *
        (φ (ε * x) * fourier k (x : UnitAddCircle)) := fun k => by
    have hc : Continuous fun x : ℝ => fourier k (x : UnitAddCircle) :=
      (map_continuous (fourier k)).comp (AddCircle.continuous_mk' 1)
    exact ((φ.integrable.comp_mul_left' hε.ne').mul_bdd (c := 1) hc.aestronglyMeasurable
      (ae_of_all _ fun x => (norm_fourier_apply_eq_one k _).le)).bdd_mul (c := 1)
      (by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
      (ae_of_all _ fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [circPoly, Finsupp.sum, Finset.smul_sum, smul_smul]
  rw [integral_finsetSum _ fun k _ => (hi k).smul_const (a k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_const, integral_exp_dilate φ hε]

/-- `(ψ (ε ·) g)ˇ = Σ_ℓ b_ℓ ε⁻¹ ψ̌ ((· + ℓ) / ε)`, for `g = Σ_ℓ b_ℓ e_ℓ`. -/
private theorem fourierInv_dilate_smul [CompleteSpace X] (ψ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε)
    (b : ℤ →₀ X) (ξ : ℝ) :
    𝓕⁻ (fun x : ℝ => ψ (ε * x) • circPoly b (x : UnitAddCircle)) ξ =
      b.sum fun l y => (((ε⁻¹ : ℝ) : ℂ) * 𝓕⁻ ψ (ε⁻¹ * (ξ + l))) • y := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_dilate_smul ψ hε]
  refine Finsupp.sum_congr fun l _ => ?_
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe,
    ← mul_neg, neg_add']

private theorem integrable_shift (χ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable fun ξ : ℝ => χ (ε⁻¹ * (ξ - c)) :=
  (χ.integrable.comp_mul_left' (inv_ne_zero hε.ne')).comp_sub_right c

private theorem integrable_mul_smul (χ ω : 𝓢(ℝ, ℂ)) {n : ℝ → Y} (hn : AEStronglyMeasurable n volume)
    {M : ℝ} (hM : ∀ ξ, ‖n ξ‖ ≤ M) {ε : ℝ} (hε : 0 < ε) (c d : ℝ) :
    Integrable fun ξ => (χ (ε⁻¹ * (ξ - c)) * ω (ε⁻¹ * (ξ - d))) • n ξ := by
  have hω : Continuous fun ξ : ℝ => ω (ε⁻¹ * (ξ - d)) := ω.continuous.comp (by fun_prop)
  exact ((integrable_shift χ hε c).mul_bdd hω.aestronglyMeasurable
    (ae_of_all _ fun ξ => SchwartzMap.norm_le_seminorm ℂ ω _)).smul_bdd M hn (ae_of_all _ hM)

/-- The substitution `ξ = k + ε η` in the integrand of (5.58). -/
private theorem dilate_mul_smul (χ ω : 𝓢(ℝ, ℂ)) (n : ℝ → Y) {ε : ℝ} (hε : 0 < ε) (k l η : ℝ) :
    (χ (ε⁻¹ * (ε * η + k - k)) * ω (ε⁻¹ * (ε * η + k - l))) • n (ε * η + k) =
      (χ η * ω (η + ε⁻¹ * (k - l))) • n (ε * η + k) := by
  rw [add_sub_cancel_right, inv_mul_cancel_left₀ hε.ne', add_sub_assoc, mul_add,
    inv_mul_cancel_left₀ hε.ne']

/-- The substitution `ξ = k + ε η` in the integral of (5.58). -/
private theorem smul_integral_mul_smul (χ ω : 𝓢(ℝ, ℂ)) (n : ℝ → Y) {ε : ℝ} (hε : 0 < ε)
    (k l : ℝ) : ((ε⁻¹ : ℝ) : ℂ) • ∫ ξ, (χ (ε⁻¹ * (ξ - k)) * ω (ε⁻¹ * (ξ - l))) • n ξ =
      ∫ η, (χ η * ω (η + ε⁻¹ * (k - l))) • n (ε * η + k) := by
  have h := Measure.integral_comp_mul_left (fun y =>
    (χ (ε⁻¹ * (y + k - k)) * ω (ε⁻¹ * (y + k - l))) • n (y + k)) ε
  rw [abs_of_pos (inv_pos.2 hε), integral_add_right_eq_self
    (fun ξ => (χ (ε⁻¹ * (ξ - k)) * ω (ε⁻¹ * (ξ - l))) • n ξ) k] at h
  rw [Complex.coe_smul, ← h]
  exact integral_congr_ae (ae_of_all _ (dilate_mul_smul χ ω n hε k l))

/-- The integrand of (5.58) after the substitution converges: `n` is continuous at `k`, and `ω`
vanishes at infinity. -/
private theorem tendsto_dilate_mul_smul (χ ω : 𝓢(ℝ, ℂ)) {n : ℝ → Y} {M : ℝ}
    (hM : ∀ ξ, ‖n ξ‖ ≤ M) {k : ℤ} (hc : ContinuousAt n k) (l : ℤ) (η : ℝ) :
    Tendsto (fun ε : ℝ => (χ η * ω (η + ε⁻¹ * (k - l))) • n (ε * η + k)) (𝓝[>] 0)
      (𝓝 (if k = l then (χ η * ω η) • n k else 0)) := by
  rcases eq_or_ne k l with rfl | hkl
  · simp only [ite_true, sub_self, mul_zero, add_zero]
    refine (hc.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds ?_)).const_smul _
    exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · rw [ite_eq_right hkl]
    have h1 : Tendsto (fun ε : ℝ => η + ε⁻¹ * ((k : ℝ) - l)) (𝓝[>] 0) (cocompact ℝ) :=
      (Homeomorph.addLeft η).isClosedEmbedding.tendsto_cocompact.comp
        ((tendsto_cocompact_mul_right₀ (sub_ne_zero.2 (by exact_mod_cast hkl))).comp
          (tendsto_inv_nhdsGT_zero.mono_right atTop_le_cocompact))
    refine Tendsto.zero_smul_isBoundedUnder_le ?_ (isBoundedUnder_of ⟨M, fun ε => hM _⟩)
    simpa using (ω.tendsto_cocompact.comp h1).const_mul (χ η)

/-- HNVW I, (5.58): `ε⁻¹ ∫ φ̂ ((ξ − k) / ε) ψ̌ ((ξ − ℓ) / ε) m (ξ) x dξ → δ_{kℓ} m (k) x`, if
`∫ φ̂ ψ̌ = 1`. Here `χ = φ̂`, `ω = ψ̌` and `n (ξ) = m (ξ) x`. -/
private theorem tendsto_integral_mul_smul [CompleteSpace Y] {χ ω : 𝓢(ℝ, ℂ)}
    (h : ∫ ξ, χ ξ * ω ξ = 1) {n : ℝ → Y} (hn : AEStronglyMeasurable n volume) {M : ℝ}
    (hM : ∀ ξ, ‖n ξ‖ ≤ M) (k l : ℤ) (hc : ContinuousAt n k) :
    Tendsto (fun ε : ℝ => ((ε⁻¹ : ℝ) : ℂ) • ∫ ξ, (χ (ε⁻¹ * (ξ - k)) * ω (ε⁻¹ * (ξ - l))) • n ξ)
      (𝓝[>] 0) (𝓝 (if k = l then n k else 0)) := by
  obtain ⟨Cω, hω⟩ : ∃ Cω : ℝ, ∀ η, ‖ω η‖ ≤ Cω :=
    ⟨_, fun η => SchwartzMap.norm_le_seminorm ℂ ω η⟩
  have hlim : (if k = l then n k else 0) = ∫ η, if k = l then (χ η * ω η) • n k else 0 := by
    split_ifs
    · rw [integral_smul_const, h, one_smul]
    · rw [integral_zero]
  rw [hlim]
  -- dominated convergence
  refine (tendsto_integral_filter_of_dominated_convergence (fun η => ‖χ η‖ * (Cω * M)) ?_ ?_
    (χ.integrable.norm.mul_const _)
    (ae_of_all _ (tendsto_dilate_mul_smul χ ω hM hc l))).congr' ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have h1 := ((integrable_mul_smul χ ω hn hM hε k l).comp_add_right (k : ℝ)).comp_mul_left'
      (ne_of_gt hε)
    exact h1.aestronglyMeasurable.congr (ae_of_all _ (dilate_mul_smul χ ω n hε k l))
  · refine Eventually.of_forall fun ε => ae_of_all _ fun η => ?_
    rw [norm_smul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hω _) (hM _) (norm_nonneg _)
      ((norm_nonneg _).trans (hω 0))) (norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (smul_integral_mul_smul χ ω n hε k l).symm

/-- `∫_𝕋 e_k e_ℓ = δ_{k,−ℓ}`. -/
private theorem integral_fourier_mul_fourier (k l : ℤ) :
    ∫ t : UnitAddCircle, fourier k t * fourier l t ∂haarAddCircle = if k = -l then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) k) (-l)
  rw [fourierCoeff, neg_neg, Pi.single_apply] at h
  simp only [smul_eq_mul] at h
  simp only [mul_comm (fourier k _), h, eq_comm]

/-- The coefficients of the multiplier transform `Σ_k m (k) a_k e_k` of `Σ_k a_k e_k`. -/
private theorem integral_circPoly_multiplier (m : ℝ → X →L[ℂ] Y) (a : ℤ →₀ X)
    (b : ℤ →₀ (Y →L[ℂ] ℂ)) :
    ∫ t, circPoly b t (a.sum fun k y => fourier k t • m k y) ∂haarAddCircle =
      ∑ l ∈ b.support, ∑ k ∈ a.support, if k = -l then b l (m k (a k)) else 0 := by
  have hi : ∀ k l : ℤ, Integrable (fun t : UnitAddCircle =>
      (fourier k t * fourier l t) * b l (m k (a k))) haarAddCircle := fun k l =>
    integrable_haar_of_continuous
      (((map_continuous (fourier k)).mul (map_continuous (fourier l))).mul continuous_const)
  have h1 : ∀ t, circPoly b t (a.sum fun k y => fourier k t • m k y) =
      ∑ l ∈ b.support, ∑ k ∈ a.support, (fourier k t * fourier l t) * b l (m k (a k)) := fun t => by
    rw [circPoly, Finsupp.sum, sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_apply, map_smul, smul_eq_mul]
    ring
  simp only [h1]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => hi k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun k _ => hi k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, integral_fourier_mul_fourier]
  split_ifs <;> simp

/-- `m (φ (ε ·) f)^ = Σ_k ε⁻¹ φ̂ ((· − k) / ε) m a_k`. -/
private theorem multiplier_fourier_dilate [CompleteSpace X] (m : ℝ → X →L[ℂ] Y) (φ : 𝓢(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℤ →₀ X) (ξ : ℝ) :
    m ξ (𝓕 (fun y : ℝ => φ (ε * y) • circPoly a (y : UnitAddCircle)) ξ) =
      ∑ k ∈ a.support, (((ε⁻¹ : ℝ) : ℂ) * 𝓕 φ (ε⁻¹ * (ξ - k))) • m ξ (a k) := by
  rw [fourier_dilate_smul φ hε, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

/-- `m (φ (ε ·) f)^` is integrable. -/
private theorem integrable_multiplier [CompleteSpace X] {m : ℝ → X →L[ℂ] Y} {M : ℝ}
    (hM : ∀ ξ, ‖m ξ‖ ≤ M) (hm : ∀ x, AEStronglyMeasurable (fun ξ => m ξ x) volume) (φ : 𝓢(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℤ →₀ X) : Integrable fun ξ =>
      m ξ (𝓕 (fun y : ℝ => φ (ε * y) • circPoly a (y : UnitAddCircle)) ξ) := by
  simp only [multiplier_fourier_dilate m φ hε a]
  exact integrable_finsetSum _ fun k _ => ((integrable_shift (𝓕 φ) hε k).const_mul _).smul_bdd
    (M * ‖a k‖) (hm (a k)) (ae_of_all _ fun ξ => (m ξ).le_of_opNorm_le (hM ξ) _)

/-- **HNVW I, Lemma 5.7.2**, for `d = 1`: if `φ, ψ ∈ 𝓢 (ℝ)` satisfy `∫ φ̂ ψ̌ = 1`, then
`⟨T̃_m f, g⟩ = lim_{ε ↓ 0} ε ⟨T_m (φ (ε ·) f), ψ (ε ·) g⟩` for all trigonometric polynomials
`f = Σ_k a_k e_k : 𝕋 → X` and `g = Σ_ℓ b_ℓ e_ℓ : 𝕋 → Y*`, where `T̃_m f = Σ_k m (k) a_k e_k` and
`T_m h = (m ĥ)ˇ`. In the book the integers are Lebesgue points of `m (·) x`; here `m (·) x` is
continuous at the integers. (The book also assumes that `φ`, `ψ` are radial; this is not needed.) -/
theorem tendsto_integral_dilate_multiplier [CompleteSpace X] [CompleteSpace Y] {φ ψ : 𝓢(ℝ, ℂ)}
    (h : ∫ ξ, 𝓕 φ ξ * 𝓕⁻ ψ ξ = 1) {m : ℝ → X →L[ℂ] Y} {M : ℝ} (hM : ∀ ξ, ‖m ξ‖ ≤ M)
    (hm : ∀ x, AEStronglyMeasurable (fun ξ => m ξ x) volume)
    (hc : ∀ (k : ℤ) (x : X), ContinuousAt (fun ξ => m ξ x) k) (a : ℤ →₀ X)
    (b : ℤ →₀ (Y →L[ℂ] ℂ)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ x : ℝ, (ψ (ε * x) • circPoly b (x : UnitAddCircle))
        (𝓕⁻ (fun ξ => m ξ (𝓕 (fun y : ℝ => φ (ε * y) • circPoly a (y : UnitAddCircle)) ξ)) x))
      (𝓝[>] 0)
      (𝓝 (∫ t, circPoly b t (a.sum fun k y => fourier k t • m k y) ∂haarAddCircle)) := by
  have hbm : ∀ k l, AEStronglyMeasurable (fun ξ => b l (m ξ (a k))) volume := fun k l =>
    (b l).continuous.comp_aestronglyMeasurable (hm (a k))
  have hbM : ∀ k l ξ, ‖b l (m ξ (a k))‖ ≤ ‖b l‖ * (M * ‖a k‖) := fun k l ξ =>
    (b l).le_opNorm_of_le ((m ξ).le_of_opNorm_le (hM ξ) _)
  -- the terms
  have hterm : ∀ k l : ℤ, Tendsto (fun ε : ℝ => ((ε⁻¹ : ℝ) : ℂ) • ∫ ξ,
      (𝓕 φ (ε⁻¹ * (ξ - k)) * 𝓕⁻ ψ (ε⁻¹ * (ξ - (-l : ℤ)))) • b l (m ξ (a k))) (𝓝[>] 0)
      (𝓝 (if k = -l then b l (m k (a k)) else 0)) := fun k l =>
    tendsto_integral_mul_smul h (hbm k l) (hbM k l) k (-l)
      ((b l).continuous.continuousAt.comp (hc k (a k)))
  rw [integral_circPoly_multiplier]
  refine (tendsto_finsetSum _ fun l _ => tendsto_finsetSum _ fun k _ => hterm k l).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  -- the Fourier transforms
  rw [integral_fourierInv_dual (integrable_multiplier hM hm φ hε' a)
    (integrable_dilate_smul ψ hε' b), ← integral_const_mul]
  have hprod : ∀ ξ, (ε : ℂ) * 𝓕⁻ (fun x : ℝ => ψ (ε * x) • circPoly b (x : UnitAddCircle)) ξ
      (m ξ (𝓕 (fun y : ℝ => φ (ε * y) • circPoly a (y : UnitAddCircle)) ξ)) =
      ∑ l ∈ b.support, ∑ k ∈ a.support, ((ε⁻¹ : ℝ) : ℂ) *
        ((𝓕 φ (ε⁻¹ * (ξ - k)) * 𝓕⁻ ψ (ε⁻¹ * (ξ - (-l : ℤ)))) • b l (m ξ (a k))) := fun ξ => by
    have hε0 : (ε : ℂ) ≠ 0 := by simpa using hε'.ne'
    rw [multiplier_fourier_dilate m φ hε', fourierInv_dilate_smul ψ hε', Finsupp.sum, sum_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_apply, map_smul, smul_eq_mul]
    push_cast
    rw [sub_neg_eq_add]
    field_simp
  have hpi : ∀ k l : ℤ, Integrable fun ξ : ℝ =>
      ((ε⁻¹ : ℝ) : ℂ) * ((𝓕 φ (ε⁻¹ * (ξ - k)) * 𝓕⁻ ψ (ε⁻¹ * (ξ - (-l : ℤ)))) • b l (m ξ (a k))) :=
    fun k l => (integrable_mul_smul (𝓕 φ) (𝓕⁻ ψ) (hbm k l) (hbM k l) hε' k (-l : ℤ)).const_mul _
  simp only [hprod]
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => hpi k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun k _ => hpi k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, smul_eq_mul]

/-! ### Trigonometric polynomials are norming -/

/-- Hölder's inequality for the pairing of `L^p (Y)` and `L^q (Y*)`. -/
private theorem lintegral_dual_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ}
    (hpq : p.HolderConjugate q) {u : α → Y} {g : α → Y →L[ℂ] ℂ} (hu : AEStronglyMeasurable u μ)
    (hg : AEStronglyMeasurable g μ) : ∫⁻ x, ‖g x (u x)‖ₑ ∂μ ≤
      eLpNorm u (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ := by
  have h1 : ∀ x, ‖g x (u x)‖ₑ ≤ ‖u x‖ₑ * ‖g x‖ₑ := fun x => by
    rw [mul_comm]
    exact (g x).le_opENorm _
  refine (lintegral_mono h1).trans ?_
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hu.enorm hg.enorm
  simp only [Pi.mul_apply] at h2
  rw [← eLpNorm_ofReal_rpow_eq_lintegral hpq.pos hu,
    ← eLpNorm_ofReal_rpow_eq_lintegral hpq.symm.pos hg, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_one_div_cancel hpq.ne_zero, mul_one_div_cancel hpq.symm.ne_zero, ENNReal.rpow_one,
    ENNReal.rpow_one] at h2
  exact h2

private theorem enorm_integral_dual_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ}
    (hpq : p.HolderConjugate q) {u : α → Y} {g : α → Y →L[ℂ] ℂ} (hu : AEStronglyMeasurable u μ)
    (hg : AEStronglyMeasurable g μ) : ‖∫ x, g x (u x) ∂μ‖ₑ ≤
      eLpNorm u (ENNReal.ofReal p) μ * eLpNorm g (ENNReal.ofReal q) μ :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_dual_le hpq hu hg)

private theorem integrable_dual {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ}
    (hpq : p.HolderConjugate q) {u : α → Y} {g : α → Y →L[ℂ] ℂ}
    (hu : MemLp u (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) μ) :
    Integrable (fun x => g x (u x)) μ :=
  ⟨(ContinuousLinearMap.apply ℂ ℂ : Y →L[ℂ] (Y →L[ℂ] ℂ) →L[ℂ] ℂ).aestronglyMeasurable_comp₂
    hu.aestronglyMeasurable hg.aestronglyMeasurable,
    (lintegral_dual_le hpq hu.aestronglyMeasurable hg.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top hu.eLpNorm_lt_top hg.eLpNorm_lt_top)⟩

/-- Trigonometric polynomials are dense in `L^q (𝕋)`, `1 ≤ q < ∞`. -/
private theorem exists_circPoly_eLpNorm_sub_le_scalar {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hq : q ≠ ∞)
    {f : UnitAddCircle → ℂ} (hf : MemLp f q haarAddCircle) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ c : ℤ →₀ ℂ, eLpNorm (f - circPoly c) q haarAddCircle ≤ δ := by
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have hmem : hf.toLp f ∈ closure
      (Submodule.span ℂ (Set.range (@fourierLp 1 _ q _)) : Set (Lp ℂ q haarAddCircle)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourierLp_closure_eq_top hq]
    trivial
  obtain ⟨h, hh, hdist⟩ := EMetric.mem_closure_iff.1 hmem δ (pos_iff_ne_zero.2 hδ)
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp (R := ℂ)).1 hh
  refine ⟨c, ?_⟩
  have h1 : (c.sum fun n x => x • @fourierLp 1 _ q _ n) =
      ContinuousMap.toLp (E := ℂ) q haarAddCircle ℂ (c.sum fun n x => x • fourier n) := by
    rw [Finsupp.sum, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun n _ => (map_smul _ _ _).symm
  have h2 : ((c.sum fun n x => x • @fourierLp 1 _ q _ n : Lp ℂ q haarAddCircle) :
      UnitAddCircle → ℂ) =ᵐ[haarAddCircle] circPoly c := by
    rw [h1]
    refine (ContinuousMap.coeFn_toLp haarAddCircle _).trans (ae_of_all _ fun t => ?_)
    simp only [circPoly, Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, mul_comm]
  rw [Lp.edist_def] at hdist
  refine le_trans (le_of_eq ?_) hdist.le
  refine eLpNorm_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, h2] with t ht1 ht2
  simp only [Pi.sub_apply, ht1, ht2]

/-- Vector-valued trigonometric polynomials are dense in `L^q (𝕋; V)`, `1 ≤ q < ∞`. -/
private theorem exists_circPoly_eLpNorm_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hq : q ≠ ∞) {g : UnitAddCircle → V} (hg : MemLp g q haarAddCircle)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ c : ℤ →₀ V, eLpNorm (g - circPoly c) q haarAddCircle ≤ δ := by
  suffices H : ∃ h : UnitAddCircle → V, eLpNorm (g - h) q haarAddCircle ≤ δ ∧
      ∃ c : ℤ →₀ V, h = circPoly c by
    obtain ⟨_, hle, c, rfl⟩ := H
    exact ⟨c, hle⟩
  refine hg.induction_dense hq (fun g => ∃ c : ℤ →₀ V, g = circPoly c)
    (fun v s hs _ ε hε => ?_) (fun f g hf hg => ?_) hδ
  · have hη : ε / (‖v‖ₑ + 1) ≠ 0 := ENNReal.div_ne_zero.2 ⟨hε, by simp⟩
    obtain ⟨c, hc⟩ := exists_circPoly_eLpNorm_sub_le_scalar hq1 hq
      (memLp_indicator_const q hs.nullMeasurableSet (1 : ℂ) (Or.inr (measure_ne_top _ _))) hη
    refine ⟨circPoly (c.mapRange (fun a => a • v) (zero_smul ℂ v)), ?_, _, rfl⟩
    have h1 : ∀ t, circPoly (c.mapRange (fun a => a • v) (zero_smul ℂ v)) t = circPoly c t • v :=
      fun t => by
      rw [circPoly, Finsupp.sum_mapRange_index fun n => smul_zero _, circPoly, Finsupp.sum,
        Finsupp.sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun n _ => by rw [smul_smul, smul_eq_mul]
    have h2 : ∀ t, ‖(circPoly (c.mapRange (fun a => a • v) (zero_smul ℂ v)) -
        s.indicator fun _ => v) t‖ₑ ≤
          ‖v‖ₑ * ‖(s.indicator (fun _ => (1 : ℂ)) - circPoly c) t‖ₑ := by
      intro t
      have h3 : (circPoly (c.mapRange (fun a => a • v) (zero_smul ℂ v)) -
          s.indicator fun _ => v) t =
          -((s.indicator (fun _ => (1 : ℂ)) - circPoly c) t • v) := by
        classical
        rw [Pi.sub_apply, Pi.sub_apply, h1, sub_smul, neg_sub]
        congr 1
        simp only [Set.indicator_apply]
        split_ifs <;> simp
      rw [h3, enorm_neg, enorm_smul, mul_comm]
    calc _ ≤ ‖v‖ₑ * eLpNorm (s.indicator (fun _ => (1 : ℂ)) - circPoly c) q haarAddCircle :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' q ((continuous_circPoly _).aestronglyMeasurable.sub
            (aestronglyMeasurable_const.indicator hs)) (ae_of_all _ h2)
      _ ≤ (‖v‖ₑ + 1) * (ε / (‖v‖ₑ + 1)) := by
          gcongr
          exact le_self_add
      _ ≤ ε := ENNReal.mul_div_le
  · obtain ⟨c, rfl⟩ := hf
    obtain ⟨d, rfl⟩ := hg
    refine ⟨c + d, funext fun t => ?_⟩
    simp only [Pi.add_apply, circPoly]
    rw [Finsupp.sum_add_index' (fun n => smul_zero _) fun n x y => smul_add _ _ _]

/-- HNVW I, proof of Proposition 1.3.1: simple functions with values in `Y*` norm the simple
functions with values in `Y`. -/
private theorem eLpNorm_simpleFunc_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {p q : ℝ} (hpq : p.HolderConjugate q) (s : SimpleFunc α Y) {A : ℝ≥0∞}
    (h : ∀ g : SimpleFunc α (Y →L[ℂ] ℂ), ‖∫ t, g t (s t) ∂μ‖ₑ ≤
      A * eLpNorm (⇑g) (ENNReal.ofReal q) μ) : eLpNorm (⇑s) (ENNReal.ofReal p) μ ≤ A := by
  have hp1 : 0 < p - 1 := hpq.sub_one_pos
  have hsm : AEStronglyMeasurable (⇑s) μ := s.aestronglyMeasurable
  set N := eLpNorm (⇑s) (ENNReal.ofReal p) μ with hN
  have hNp : N ^ p = ∫⁻ t, ‖s t‖ₑ ^ p ∂μ := eLpNorm_ofReal_rpow_eq_lintegral hpq.pos hsm
  have hNt : N ≠ ∞ := (s.memLp_of_isFiniteMeasure _ μ).eLpNorm_ne_top
  rcases eq_or_ne N 0 with hN0 | hN0
  · rw [hN0]
    exact zero_le
  -- the norming function
  have hJ : ∀ y : Y, ∃ f : Y →L[ℂ] ℂ, ‖f‖ ≤ 1 ∧ f y = ((‖y‖ : ℝ) : ℂ) := exists_dual_vector'' ℂ
  choose J hJ1 hJ2 using hJ
  set g : SimpleFunc α (Y →L[ℂ] ℂ) := s.map fun y => ((‖y‖ ^ (p - 1) : ℝ) : ℂ) • J y with hg
  have hgs : ∀ t, g t (s t) = ((‖s t‖ ^ p : ℝ) : ℂ) := fun t => by
    simp only [hg, SimpleFunc.map_apply, smul_apply, hJ2, smul_eq_mul]
    rw [← Complex.ofReal_mul, ← Real.rpow_add_one' (norm_nonneg _) (by linarith), sub_add_cancel]
  have h1 : ‖∫ t, g t (s t) ∂μ‖ₑ = N ^ p := by
    have hi : Integrable (fun t => ‖s t‖ ^ p) μ :=
      (s.map fun y => ‖y‖ ^ p).integrable_of_isFiniteMeasure
    have h0 : 0 ≤ ∫ t, ‖s t‖ ^ p ∂μ := integral_nonneg fun t => by positivity
    simp only [hgs]
    rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0,
      ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun t => by positivity), hNp]
    refine lintegral_congr fun t => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.nonneg]
  have h2 : eLpNorm (⇑g) (ENNReal.ofReal q) μ ≤ N ^ (p - 1) := by
    rw [← ENNReal.rpow_le_rpow_iff hpq.symm.pos,
      eLpNorm_ofReal_rpow_eq_lintegral hpq.symm.pos g.aestronglyMeasurable, ← ENNReal.rpow_mul,
      hpq.sub_one_mul_conj, hNp]
    refine lintegral_mono fun t => ?_
    have h3 : ‖g t‖ₑ ≤ ‖s t‖ₑ ^ (p - 1) := by
      rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp1.le]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [hg, SimpleFunc.map_apply]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (hJ1 _)
    calc ‖g t‖ₑ ^ q ≤ (‖s t‖ₑ ^ (p - 1)) ^ q := ENNReal.rpow_le_rpow h3 hpq.symm.nonneg
      _ = ‖s t‖ₑ ^ p := by rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
  have h3 : N * N ^ (p - 1) ≤ A * N ^ (p - 1) := by
    have h4 : N * N ^ (p - 1) = N ^ p := by
      calc N * N ^ (p - 1) = N ^ (1 : ℝ) * N ^ (p - 1) := by rw [ENNReal.rpow_one]
        _ = N ^ p := by rw [← ENNReal.rpow_add _ _ hN0 hNt, add_sub_cancel]
    rw [h4, ← h1]
    exact (h g).trans (by gcongr)
  rwa [ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos (pos_iff_ne_zero.2 hN0) hNt).ne'
    (ENNReal.rpow_ne_top_of_nonneg hp1.le hNt)] at h3

/-- An inequality for the pairings with all trigonometric polynomials with values in `Y*` holds for
the pairings with all `g ∈ L^q (𝕋; Y*)`, by density. -/
private theorem enorm_integral_le_of_forall_circPoly {p q : ℝ} (hpq : p.HolderConjugate q)
    {u : UnitAddCircle → Y} (hu : MemLp u (ENNReal.ofReal p) haarAddCircle) {A : ℝ≥0∞} (hA : A ≠ ∞)
    (h : ∀ b : ℤ →₀ (Y →L[ℂ] ℂ), ‖∫ t, circPoly b t (u t) ∂haarAddCircle‖ₑ ≤
      A * eLpNorm (circPoly b) (ENNReal.ofReal q) haarAddCircle) {g : UnitAddCircle → Y →L[ℂ] ℂ}
    (hg : MemLp g (ENNReal.ofReal q) haarAddCircle) :
    ‖∫ t, g t (u t) ∂haarAddCircle‖ₑ ≤ A * eLpNorm g (ENNReal.ofReal q) haarAddCircle := by
  have hQ : 1 ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hpq.symm.lt.le
  set U := eLpNorm u (ENNReal.ofReal p) haarAddCircle
  set G := eLpNorm g (ENNReal.ofReal q) haarAddCircle
  have hδ : ∀ δ : ℝ≥0∞, δ ≠ 0 → ‖∫ t, g t (u t) ∂haarAddCircle‖ₑ ≤ A * (G + δ) + U * δ := by
    intro δ hδ
    obtain ⟨b, hb⟩ := exists_circPoly_eLpNorm_sub_le hQ ENNReal.ofReal_ne_top hg hδ
    have hgb := hg.sub (memLp_circPoly b (ENNReal.ofReal q))
    have h2 : ∫ t, g t (u t) ∂haarAddCircle = ∫ t, circPoly b t (u t) ∂haarAddCircle +
        ∫ t, (g - circPoly b) t (u t) ∂haarAddCircle := by
      rw [← integral_add (integrable_dual hpq hu (memLp_circPoly b _))
        (integrable_dual hpq hu hgb)]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp
    rw [h2]
    refine (enorm_add_le _ _).trans (add_le_add ((h b).trans ?_) ((enorm_integral_dual_le hpq
      hu.aestronglyMeasurable hgb.aestronglyMeasurable).trans ?_))
    · gcongr
      have h3 : circPoly b = g - (g - circPoly b) := by simp
      rw [h3]
      exact (eLpNorm_sub_le hQ).trans (add_le_add le_rfl hb)
    · gcongr
  have hc : Continuous fun δ : ℝ≥0∞ => A * (G + δ) + U * δ :=
    ((ENNReal.continuous_const_mul hA).comp (continuous_const.add continuous_id)).add
      (ENNReal.continuous_const_mul hu.eLpNorm_ne_top)
  have hlim := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi 0) (hc.tendsto 0)
  rw [add_zero, mul_zero, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ0
  exact hδ δ (ne_of_gt hδ0)

/-- HNVW I, Proposition 1.3.1 (pp. 37–38), on `𝕋`, with trigonometric polynomials: for
`1 < p < ∞`, the trigonometric polynomials with values in `Y*` norm `L^p (𝕋; Y)`. As in the book
(with the roles of the two spaces exchanged), the simple function `Σ 1_{A_n} y_n` is normed by
`Σ 1_{A_n} ‖y_n‖^{p−1} y_n^*`, with `y_n^*` norming for `y_n`, and simple functions are dense in
`L^p (𝕋; Y)`; moreover, the trigonometric polynomials are dense in `L^q (𝕋; Y*)`. -/
theorem eLpNorm_le_of_forall_circPoly {p q : ℝ} (hpq : p.HolderConjugate q) {u : UnitAddCircle → Y}
    (hu : MemLp u (ENNReal.ofReal p) haarAddCircle) {A : ℝ≥0∞}
    (h : ∀ b : ℤ →₀ (Y →L[ℂ] ℂ), ‖∫ t, circPoly b t (u t) ∂haarAddCircle‖ₑ ≤
      A * eLpNorm (circPoly b) (ENNReal.ofReal q) haarAddCircle) :
    eLpNorm u (ENNReal.ofReal p) haarAddCircle ≤ A := by
  rcases eq_or_ne A ∞ with rfl | hA
  · exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- simple functions
  obtain ⟨s, hs, hsm⟩ := hu.exists_simpleFunc_eLpNorm_sub_lt ENNReal.ofReal_ne_top
    (ENNReal.half_pos (ENNReal.coe_pos.2 hε).ne').ne'
  have hus : MemLp (u - ⇑s) (ENNReal.ofReal p) haarAddCircle := hu.sub hsm
  have hN : eLpNorm (⇑s) (ENNReal.ofReal p) haarAddCircle ≤ A + ε / 2 := by
    refine eLpNorm_simpleFunc_le hpq s fun g => ?_
    have hg : MemLp (⇑g) (ENNReal.ofReal q) haarAddCircle := g.memLp_of_isFiniteMeasure _ _
    have h3 : ∫ t, g t (s t) ∂haarAddCircle =
        ∫ t, g t (u t) ∂haarAddCircle - ∫ t, g t ((u - ⇑s) t) ∂haarAddCircle := by
      rw [← integral_sub (integrable_dual hpq hu hg) (integrable_dual hpq hus hg)]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [Pi.sub_apply, map_sub, sub_sub_cancel]
    rw [h3, add_mul]
    refine enorm_sub_le.trans (add_le_add
      (enorm_integral_le_of_forall_circPoly hpq hu hA h hg)
      ((enorm_integral_dual_le hpq hus.aestronglyMeasurable hg.aestronglyMeasurable).trans ?_))
    gcongr
  have h3 : u = ⇑s + (u - ⇑s) := by simp
  calc eLpNorm u (ENNReal.ofReal p) haarAddCircle
      = eLpNorm (⇑s + (u - ⇑s)) (ENNReal.ofReal p) haarAddCircle := by rw [← h3]
    _ ≤ eLpNorm (⇑s) (ENNReal.ofReal p) haarAddCircle +
        eLpNorm (u - ⇑s) (ENNReal.ofReal p) haarAddCircle :=
        eLpNorm_add_le (ENNReal.one_le_ofReal.2 hpq.lt.le)
    _ ≤ A + ε / 2 + ε / 2 := add_le_add hN hs.le
    _ = A + ε := by rw [add_assoc, ENNReal.add_halves]

/-! ### The Schwartz functions of the proof of Proposition 5.7.1 -/

private theorem exists_schwartz_dilate (G : 𝓢(ℝ, X)) {c : ℝ} (hc : c ≠ 0) :
    ∃ G' : 𝓢(ℝ, X), ∀ ξ, G' ξ = G (c * ξ) :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)) G, fun _ => rfl⟩

/-- `Σ_k a_k ε⁻¹ χ ((· − k) / ε)` is a Schwartz function. -/
private theorem exists_schwartz_shift (χ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (a : ℤ →₀ X) :
    ∃ G : 𝓢(ℝ, X), ∀ ξ, G ξ =
      a.sum fun k y => (((ε⁻¹ : ℝ) : ℂ) * χ (ε⁻¹ * (ξ - k))) • y := by
  induction a using Finsupp.induction_linear with
  | zero => exact ⟨0, fun ξ => by simp⟩
  | add a b iha ihb =>
    obtain ⟨G, hG⟩ := iha
    obtain ⟨H, hH⟩ := ihb
    refine ⟨G + H, fun ξ => ?_⟩
    rw [add_apply, hG, hH,
      Finsupp.sum_add_index' (fun k => smul_zero _) fun k x y => smul_add _ _ _]
  | single k y =>
    obtain ⟨χ', hχ'⟩ := exists_schwartz_dilate χ (inv_ne_zero hε.ne')
    refine ⟨((ε⁻¹ : ℝ) : ℂ) • (χ'.compSubConstCLM ℂ (k : ℝ)).postcompCLM
      (ContinuousLinearMap.toSpanSingleton ℂ y), fun ξ => ?_⟩
    rw [Finsupp.sum_single_index (by rw [smul_zero]), smul_apply, SchwartzMap.postcompCLM_apply,
      SchwartzMap.compSubConstCLM_apply, hχ', ContinuousLinearMap.toSpanSingleton_apply, smul_smul]

/-- The derivatives of `e^{−b x²}` are the products of `e^{−b x²}` with polynomials. -/
private theorem iteratedDeriv_gaussian (b : ℝ) (n : ℕ) : ∃ Q : Polynomial ℝ, ∀ x,
    iteratedDeriv n (fun x : ℝ => Real.exp (-(b * x ^ 2))) x =
      Q.eval x * Real.exp (-(b * x ^ 2)) := by
  induction n with
  | zero => exact ⟨1, fun x => by simp⟩
  | succ n ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q.derivative - Polynomial.C (2 * b) * Polynomial.X * Q, fun x => ?_⟩
    rw [iteratedDeriv_succ, funext hQ]
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(b * x ^ 2)))
        (Real.exp (-(b * x ^ 2)) * -(b * (2 * x))) x := by
      have h2 : HasDerivAt (fun x : ℝ => -(b * x ^ 2)) (-(b * (2 * x))) x := by
        simpa using ((hasDerivAt_pow 2 x).const_mul b).fun_neg
      exact h2.exp
    rw [((Q.hasDerivAt x).fun_mul h1).deriv]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

private theorem pow_mul_gaussian_le {b : ℝ} (hb : 0 < b) (j : ℕ) (x : ℝ) :
    |x| ^ j * Real.exp (-(b * x ^ 2)) ≤ 1 + j.factorial / b ^ j := by
  have hE : 0 < Real.exp (-(b * x ^ 2)) := Real.exp_pos _
  have hE1 : Real.exp (-(b * x ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have h1 : |x| ^ j ≤ 1 + (x ^ 2) ^ j := by
    rw [← sq_abs x]
    have h2 : 0 ≤ (|x| ^ j - 1) ^ 2 := sq_nonneg _
    have h3 : (|x| ^ 2) ^ j = (|x| ^ j) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    have h4 : 0 ≤ |x| ^ j := by positivity
    rw [h3]
    nlinarith
  have h2 : (x ^ 2) ^ j * Real.exp (-(b * x ^ 2)) ≤ j.factorial / b ^ j := by
    have h3 := Real.pow_div_factorial_le_exp (x := b * x ^ 2) (by positivity) j
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity),
      ← mul_pow, mul_comm (x ^ 2) b]
    rw [div_le_iff₀ (by positivity)] at h3
    exact h3.trans_eq (mul_comm _ _)
  calc |x| ^ j * Real.exp (-(b * x ^ 2)) ≤ (1 + (x ^ 2) ^ j) * Real.exp (-(b * x ^ 2)) := by gcongr
    _ = Real.exp (-(b * x ^ 2)) + (x ^ 2) ^ j * Real.exp (-(b * x ^ 2)) := by ring
    _ ≤ 1 + j.factorial / b ^ j := add_le_add hE1 h2

/-- The Gaussian `e^{−b x²}`, `b > 0`, is a Schwartz function. -/
private theorem exists_schwartz_gaussian {b : ℝ} (hb : 0 < b) :
    ∃ φ : 𝓢(ℝ, ℂ), ∀ x, φ x = ((Real.exp (-(b * x ^ 2)) : ℝ) : ℂ) := by
  have hdecay : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : ℝ => Real.exp (-(b * x ^ 2))) x‖ ≤ C := by
    intro k n
    obtain ⟨Q, hQ⟩ := iteratedDeriv_gaussian b n
    refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1),
      |Q.coeff i| * (1 + (k + i).factorial / b ^ (k + i)), fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hQ, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, Polynomial.eval_eq_sum_range]
    calc |x| ^ k * (|∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * x ^ i| *
          Real.exp (-(b * x ^ 2)))
        ≤ |x| ^ k * ((∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| * |x| ^ i) *
          Real.exp (-(b * x ^ 2))) := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
          exact Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_pow]
      _ = ∑ i ∈ Finset.range (Q.natDegree + 1),
          |Q.coeff i| * (|x| ^ (k + i) * Real.exp (-(b * x ^ 2))) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pow_add]
          ring
      _ ≤ _ := by
          gcongr with i hi
          exact pow_mul_gaussian_le hb _ x
  set φ : 𝓢(ℝ, ℝ) := ⟨fun x => Real.exp (-(b * x ^ 2)), by fun_prop, hdecay⟩
  exact ⟨φ.postcompCLM Complex.ofRealCLM, fun x => rfl⟩

/-- `‖e^{−π x² / p}‖_p = 1`. -/
private theorem eLpNorm_gaussian {p : ℝ} (hp : 0 < p) {φ : 𝓢(ℝ, ℂ)}
    (hφ : ∀ x, φ x = ((Real.exp (-(Real.pi / p * x ^ 2)) : ℝ) : ℂ)) :
    eLpNorm φ (ENNReal.ofReal p) volume = 1 := by
  have h1 : eLpNorm φ (ENNReal.ofReal p) volume ^ p = 1 := by
    rw [eLpNorm_ofReal_rpow_eq_lintegral hp φ.continuous.aestronglyMeasurable]
    have h2 : ∀ x, ‖φ x‖ₑ ^ p = ENNReal.ofReal (Real.exp (-Real.pi * x ^ 2)) := fun x => by
      rw [← ofReal_norm, hφ, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp.le, ← Real.exp_mul]
      congr 2
      field_simp
    simp only [h2]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq Real.pi_pos)
      (ae_of_all _ fun x => (Real.exp_pos _).le), integral_gaussian, div_self Real.pi_ne_zero,
      Real.sqrt_one, ENNReal.ofReal_one]
  rw [← ENNReal.rpow_one (eLpNorm φ _ _), ← mul_one_div_cancel hp.ne', ENNReal.rpow_mul, h1,
    ENNReal.one_rpow]

/-! ### Proposition 5.7.1 -/

private theorem continuous_fourierInv {u : ℝ → Y} (hu : Integrable u) : Continuous (𝓕⁻ u) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (continuous_inner (𝕜 := ℝ) (E := ℝ)).neg hu

/-- `∫ φ̂ ψ̌ = ∫ φ ψ = 1` for the Gaussians `φ = e^{−π x² / p}` and `ψ = e^{−π x² / q}`. -/
private theorem integral_fourier_mul_fourierInv_gaussian {p q : ℝ} (hpq : p.HolderConjugate q)
    {φ ψ : 𝓢(ℝ, ℂ)} (hφ : ∀ x, φ x = ((Real.exp (-(Real.pi / p * x ^ 2)) : ℝ) : ℂ))
    (hψ : ∀ x, ψ x = ((Real.exp (-(Real.pi / q * x ^ 2)) : ℝ) : ℂ)) :
    ∫ ξ, 𝓕 φ ξ * 𝓕⁻ ψ ξ = 1 := by
  rw [SchwartzMap.integral_fourier_mul_eq, FourierTransform.fourier_fourierInv_eq]
  have h1 : ∀ x, φ x * ψ x = ((Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ) := fun x => by
    rw [hφ, hψ, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    calc -(Real.pi / p * x ^ 2) + -(Real.pi / q * x ^ 2) = -Real.pi * x ^ 2 * (p⁻¹ + q⁻¹) := by
          ring
      _ = -Real.pi * x ^ 2 := by rw [hpq.inv_add_inv_eq_one, mul_one]
  simp only [h1]
  rw [integral_complex_ofReal, integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one,
    Complex.ofReal_one]

/-- The inequality on the line, for the function `φ (ε ·) f`, whose Fourier transform is a Schwartz
function. -/
private theorem eLpNorm_multiplier_dilate_le [CompleteSpace X] {P : ℝ≥0∞} {m : ℝ → X →L[ℂ] Y}
    {C : ℝ≥0∞} (hC : ∀ G : 𝓢(ℝ, X), eLpNorm (𝓕⁻ fun ξ => m ξ (G ξ)) P volume ≤
      C * eLpNorm (𝓕⁻ (G : ℝ → X)) P volume) (φ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (a : ℤ →₀ X) :
    eLpNorm (𝓕⁻ fun ξ => m ξ (𝓕 (fun y : ℝ => φ (ε * y) • circPoly a (y : UnitAddCircle)) ξ)) P
        volume ≤
      C * eLpNorm (fun y : ℝ => φ (ε * y) • circPoly a (y : UnitAddCircle)) P volume := by
  set h : ℝ → X := fun y => φ (ε * y) • circPoly a (y : UnitAddCircle)
  obtain ⟨G, hG⟩ := exists_schwartz_shift (𝓕 φ) hε a
  have hGh : 𝓕 h = G := funext fun ξ => by rw [hG, fourier_dilate_smul φ hε]
  have hcont : Continuous h := (φ.continuous.comp (continuous_const_mul ε)).smul
    ((continuous_circPoly a).comp (AddCircle.continuous_mk' 1))
  have hinv : 𝓕⁻ (G : ℝ → X) = h := by
    rw [← hGh]
    exact hcont.fourierInv_fourier_eq (integrable_dilate_smul φ hε a) (hGh ▸ G.integrable)
  have h1 := hC G
  rwa [hinv, ← hGh] at h1

/-- `⟨T̃_m f, g⟩` is bounded by the multiplier norm of `m` on the line (HNVW I, p. 460). -/
private theorem enorm_integral_circPoly_multiplier_le [CompleteSpace X] [CompleteSpace Y] {p q : ℝ}
    (hpq : p.HolderConjugate q) {m : ℝ → X →L[ℂ] Y} {M : ℝ} (hM : ∀ ξ, ‖m ξ‖ ≤ M)
    (hm : ∀ x, AEStronglyMeasurable (fun ξ => m ξ x) volume)
    (hc : ∀ (k : ℤ) (x : X), ContinuousAt (fun ξ => m ξ x) k) {C : ℝ≥0∞} (hCt : C ≠ ∞)
    (hC : ∀ G : 𝓢(ℝ, X), eLpNorm (𝓕⁻ fun ξ => m ξ (G ξ)) (ENNReal.ofReal p) volume ≤
      C * eLpNorm (𝓕⁻ (G : ℝ → X)) (ENNReal.ofReal p) volume) (a : ℤ →₀ X)
    (b : ℤ →₀ (Y →L[ℂ] ℂ)) :
    ‖∫ t, circPoly b t (a.sum fun k y => fourier k t • m k y) ∂haarAddCircle‖ₑ ≤
      C * eLpNorm (circPoly a) (ENNReal.ofReal p) haarAddCircle *
        eLpNorm (circPoly b) (ENNReal.ofReal q) haarAddCircle := by
  have hp0 := hpq.pos
  have hq0 := hpq.symm.pos
  -- the Gaussians
  obtain ⟨φ, hφ⟩ := exists_schwartz_gaussian (div_pos Real.pi_pos hp0)
  obtain ⟨ψ, hψ⟩ := exists_schwartz_gaussian (div_pos Real.pi_pos hq0)
  have hφψ := integral_fourier_mul_fourierInv_gaussian hpq hφ hψ
  -- the limits
  have hlim1 := (continuous_enorm.tendsto _).comp
    (tendsto_integral_dilate_multiplier hφψ hM hm hc a b)
  have hlim2 := tendsto_eLpNorm_dilate_smul hpq.lt.le φ (memLp_circPoly a (ENNReal.ofReal p))
  have hlim3 := tendsto_eLpNorm_dilate_smul hpq.symm.lt.le ψ (memLp_circPoly b (ENNReal.ofReal q))
  rw [eLpNorm_gaussian hp0 hφ, one_mul] at hlim2
  rw [eLpNorm_gaussian hq0 hψ, one_mul] at hlim3
  have hlim4 := ENNReal.Tendsto.mul (ENNReal.Tendsto.const_mul (a := C) hlim2 (Or.inr hCt))
    (Or.inr (memLp_circPoly b _).eLpNorm_ne_top) hlim3
    (Or.inr (ENNReal.mul_ne_top hCt (memLp_circPoly a _).eLpNorm_ne_top))
  refine le_of_tendsto_of_tendsto hlim1 hlim4 ?_
  -- the inequality on the line
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  set h : ℝ → X := fun y => φ (ε * y) • circPoly a (y : UnitAddCircle)
  set v : ℝ → Y →L[ℂ] ℂ := fun y => ψ (ε * y) • circPoly b (y : UnitAddCircle)
  have hmult : eLpNorm (𝓕⁻ fun ξ => m ξ (𝓕 h ξ)) (ENNReal.ofReal p) volume ≤
      C * eLpNorm h (ENNReal.ofReal p) volume := eLpNorm_multiplier_dilate_le hC φ hε' a
  have hpair := enorm_integral_dual_le hpq
    (continuous_fourierInv (integrable_multiplier hM hm φ hε' a)).aestronglyMeasurable
    (integrable_dilate_smul ψ hε' b).aestronglyMeasurable
  have hεe : ‖(ε : ℂ)‖ₑ = ENNReal.ofReal ε ^ (1 / p) * ENNReal.ofReal ε ^ (1 / q) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), one_div, one_div,
      hpq.inv_add_inv_eq_one, ENNReal.rpow_one, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg hε'.le]
  rw [Function.comp_apply, enorm_mul, hεe]
  calc _ ≤ ENNReal.ofReal ε ^ (1 / p) * ENNReal.ofReal ε ^ (1 / q) *
        (C * eLpNorm h (ENNReal.ofReal p) volume * eLpNorm v (ENNReal.ofReal q) volume) := by
        gcongr
        exact hpair.trans (by gcongr)
    _ = _ := by ring

/-- A trigonometric polynomial with a nonzero coefficient has a nonzero norm. -/
private theorem eLpNorm_circPoly_ne_zero [CompleteSpace X] {p : ℝ} (hp : 0 < p) {c : ℤ →₀ X}
    (hc : c ≠ 0) : eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle ≠ 0 := by
  intro h
  rw [eLpNorm_eq_zero_iff (by simpa using hp),
    (continuous_circPoly c).ae_eq_iff_eq _ continuous_zero] at h
  refine hc (Finsupp.ext fun n => ?_)
  rw [← integral_fourier_smul_circPoly c n, h]
  simp

/-- **HNVW I, Proposition 5.7.1** (transference from `ℝ^d` to `𝕋^d`), for `d = 1`: let
`m : ℝ → 𝓛 (X, Y)` be bounded and strongly measurable, and let `T_m h = (m ĥ)ˇ` satisfy
`‖T_m h‖_{L^p (ℝ; Y)} ≤ C ‖h‖_{L^p (ℝ; X)}` for Schwartz functions `h` (the hypothesis is stated
with `G = ĥ`). If `m (·) x` is continuous at the integers for all `x`, then
`‖Σ_k m (k) a_k e_k‖_{L^p (𝕋; Y)} ≤ C ‖Σ_k a_k e_k‖_{L^p (𝕋; X)}`, with the same constant, for all
trigonometric polynomials. (In the book the integers are Lebesgue points of `m (·) x`.) -/
theorem eLpNorm_circPoly_multiplier_le [CompleteSpace X] [CompleteSpace Y] {p : ℝ} (hp : 1 < p)
    {m : ℝ → X →L[ℂ] Y} {M : ℝ} (hM : ∀ ξ, ‖m ξ‖ ≤ M)
    (hm : ∀ x, AEStronglyMeasurable (fun ξ => m ξ x) volume)
    (hc : ∀ (k : ℤ) (x : X), ContinuousAt (fun ξ => m ξ x) k) {C : ℝ≥0∞}
    (hC : ∀ G : 𝓢(ℝ, X), eLpNorm (𝓕⁻ fun ξ => m ξ (G ξ)) (ENNReal.ofReal p) volume ≤
      C * eLpNorm (𝓕⁻ (G : ℝ → X)) (ENNReal.ofReal p) volume) (a : ℤ →₀ X) :
    eLpNorm (fun t : UnitAddCircle => a.sum fun k y => fourier k t • m k y) (ENNReal.ofReal p)
        haarAddCircle ≤
      C * eLpNorm (circPoly a) (ENNReal.ofReal p) haarAddCircle := by
  rcases eq_or_ne C ∞ with rfl | hCt
  · rcases eq_or_ne a 0 with rfl | ha
    · have h0 : (fun t : UnitAddCircle => (0 : ℤ →₀ X).sum fun k y => fourier k t • m k y) =
          fun _ => 0 := funext fun t => Finsupp.sum_zero_index
      rw [h0, eLpNorm_fun_zero]
      exact zero_le
    · rw [ENNReal.top_mul (eLpNorm_circPoly_ne_zero (by linarith) ha)]
      exact le_top
  have hpq : p.HolderConjugate (p / (p - 1)) := (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  refine eLpNorm_le_of_forall_circPoly hpq ?_ fun b =>
    enorm_integral_circPoly_multiplier_le hpq hM hm hc hCt hC a b
  have hcont : Continuous fun t : UnitAddCircle => a.sum fun k y => fourier k t • m k y :=
    continuous_finsetSum _ fun k _ => (map_continuous (fourier k)).smul continuous_const
  exact hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### Dilations -/

/-- `(F (ρ ·))ˇ (x) = ρ⁻¹ Fˇ (ρ⁻¹ x)`. -/
theorem fourierInv_comp_mul_left (F : ℝ → Y) {ρ : ℝ} (hρ : 0 < ρ) :
    (𝓕⁻ fun ξ => F (ρ * ξ)) = ρ⁻¹ • fun x => 𝓕⁻ F (ρ⁻¹ * x) := by
  funext x
  have h2 := Measure.integral_comp_mul_left (fun v : ℝ =>
    Complex.exp (((2 * Real.pi * (v * (ρ⁻¹ * x)) : ℝ) : ℂ) * Complex.I) • F v) ρ
  rw [abs_of_pos (inv_pos.2 hρ)] at h2
  rw [Pi.smul_apply, Real.fourierInv_eq', Real.fourierInv_eq']
  simp only [RCLike.inner_apply, conj_trivial, mul_comm _ (ρ⁻¹ * x)] at h2 ⊢
  rw [← h2]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  congr 4
  field_simp

/-- `‖(F (ρ ·))ˇ‖_p = ρ^{1/p − 1} ‖F ˇ‖_p`. -/
private theorem eLpNorm_fourierInv_dilate {p : ℝ} (hp : 0 < p) (F : ℝ → Y) {ρ : ℝ} (hρ : 0 < ρ) :
    eLpNorm (𝓕⁻ fun ξ => F (ρ * ξ)) (ENNReal.ofReal p) volume =
      ‖ρ⁻¹‖ₑ * (ENNReal.ofReal ρ ^ (1 / p) * eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume) := by
  have h3 : eLpNorm (fun x => 𝓕⁻ F (ρ⁻¹ * x)) (ENNReal.ofReal p) volume =
      ENNReal.ofReal ρ ^ (1 / p) * eLpNorm (𝓕⁻ F) (ENNReal.ofReal p) volume := by
    have h4 := (measurableEmbedding_mulLeft₀ (inv_ne_zero hρ.ne')).eLpNorm_map_measure
      (μ := volume) (p := ENNReal.ofReal p) (g := 𝓕⁻ F)
    rw [Real.map_volume_mul_left (inv_ne_zero hρ.ne'), inv_inv, abs_of_pos hρ,
      eLpNorm_smul_measure_of_ne_zero (by simpa using hρ)] at h4
    rw [show (fun x => 𝓕⁻ F (ρ⁻¹ * x)) = 𝓕⁻ F ∘ fun x => ρ⁻¹ * x from rfl, ← h4, smul_eq_mul]
    congr 2
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, one_div]
  rw [fourierInv_comp_mul_left F hρ, eLpNorm_const_smul, h3]

/-- The dilates `m (ρ ·)`, `ρ > 0`, of a Fourier multiplier on the line have the same norm as `m`
(HNVW I, (5.61)), by the substitution `η = ρ ξ`. -/
theorem eLpNorm_fourierInv_multiplier_dilate_le {p : ℝ} (hp : 0 < p) {m : ℝ → X →L[ℂ] Y} {C : ℝ≥0∞}
    (hC : ∀ G : 𝓢(ℝ, X), eLpNorm (𝓕⁻ fun ξ => m ξ (G ξ)) (ENNReal.ofReal p) volume ≤
      C * eLpNorm (𝓕⁻ (G : ℝ → X)) (ENNReal.ofReal p) volume) {ρ : ℝ} (hρ : 0 < ρ) (G : 𝓢(ℝ, X)) :
    eLpNorm (𝓕⁻ fun ξ => m (ρ * ξ) (G ξ)) (ENNReal.ofReal p) volume ≤
      C * eLpNorm (𝓕⁻ (G : ℝ → X)) (ENNReal.ofReal p) volume := by
  obtain ⟨G', hG'⟩ := exists_schwartz_dilate G (inv_ne_zero hρ.ne')
  have h1 : (fun ξ => m (ρ * ξ) (G ξ)) = fun ξ => (fun η => m η (G' η)) (ρ * ξ) := by
    funext ξ
    simp only [hG', inv_mul_cancel_left₀ hρ.ne']
  have h2 : (G : ℝ → X) = fun ξ => G' (ρ * ξ) := by
    funext ξ
    rw [hG', inv_mul_cancel_left₀ hρ.ne']
  rw [h1, h2, eLpNorm_fourierInv_dilate hp (fun η => m η (G' η)) hρ,
    eLpNorm_fourierInv_dilate hp (G' : ℝ → X) hρ]
  calc _ ≤ ‖ρ⁻¹‖ₑ * (ENNReal.ofReal ρ ^ (1 / p) *
        (C * eLpNorm (𝓕⁻ (G' : ℝ → X)) (ENNReal.ofReal p) volume)) := by
        gcongr
        exact hC G'
    _ = _ := by ring

end HarmonicAnalysis
