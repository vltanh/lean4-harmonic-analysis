/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Dyadic.Average
public import HarmonicAnalysis.VectorValued.HilbertTransform.Fourier
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The truncated Hilbert transform on UMD spaces

`H_{ε,R} f (x) = π⁻¹ ∫_{ε < |x − y| < R} f (y) / (x − y) dy` (`truncatedHilbert ε R f`, defined in
`VectorValued.HilbertTransform.Fourier`). On a UMD space the truncations `H_{ε, 2^n ε}` are bounded
on `L^p (ℝ; X)`, `1 < p < ∞`, uniformly in `ε > 0` and `n` (`eLpNorm_truncatedHilbert_le`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Section 5.1.b,
pp. 384–387: with `φ = haarCorrelation haarSplit`, `Φ (x) = ∫_0^x φ` and
`ψ (x) = x⁻¹ Φ (x) 1_{[−1, 1]} (x)`,

`∫_ε^R φ_t * f dt/t = ψ_ε * f − ψ_R * f − (π/8) H_{ε,R} f` (`integral_dilateConv_eq`; the
display before (5.23), p. 385),

where the left-hand side is, for `R = 2^n ε`, an average of the shifts of
`VectorValued.Dyadic.Average` over the dilations `t`.

Departure from the source: the book lets `ε → 0` and `R → ∞` in this identity. The averaged shifts
converge in `L^p` and almost everywhere (Lemma 5.1.8), the error terms, which are `ψ_ε * f`,
`ψ_R * f` and the integrals of `φ_t * f dt/t` that remain when `ε` and `R` are not powers of two
(5.23), tend to `0` (Lemma 5.1.12), and the limit is `H f` (Theorem 5.1.13). Here no limit is taken:
only the truncations with `R = 2^n ε` are bounded, uniformly in `ε` and `n`. For them the integral
over `[ε, R]` itself is an average of dyadic shifts, and the remaining integrals of (5.23) do not
occur; the terms `ψ_ε * f`, `ψ_R * f` are bounded by Young's inequality, `‖ψ‖_1 ‖f‖_p ≤ 2 ‖f‖_p`.
The limit is taken on the Fourier side (`VectorValued.HilbertTransform.Fourier`), with Fatou's
lemma, in `VectorValued.HilbertTransform.Dyadic`. In the bound only the constant is affected:
`(8/π) (2 log 2 · β² + 4) ≤ 4 β² + 11` instead of the book's `(8/π) log 2 · β⁺ β⁻` (the factor `2`
of `2 log 2` comes from the finitely many generations, see `VectorValued.Dyadic.Shift`); the
convergence of the truncations in `L^p` and almost everywhere is not proved.
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The function `φ` of HNVW I, Example 5.1.11 and Theorem 5.1.13: the odd one, for the kernel
(5.19). -/
noncomputable def hilbertProfile : ℝ → ℝ := haarCorrelation haarSplit

/-- HNVW I, (5.22): `ψ (x) = x⁻¹ ∫_0^x φ · 1_{[−1, 1]} (x)`. -/
noncomputable def hilbertError (x : ℝ) : ℝ :=
  (Set.Icc (-1 : ℝ) 1).indicator (fun x => x⁻¹ * ∫ s in (0 : ℝ)..x, hilbertProfile s) x

/-! ### The graph of `φ` -/

/-- The primitive `Λ (y) = ∫_0^y h` of the Haar function. -/
private noncomputable def tent (y : ℝ) : ℝ :=
  max y 0 - 2 * max (y - 1 / 2) 0 + max (y - 1) 0

private theorem intervalIntegrable_of_bounded {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (a b : ℝ) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (by simp) hg.aestronglyMeasurable
    (ae_of_all _ fun x => hC x)

private theorem integral_indicator_Ici (c a b : ℝ) :
    ∫ s in a..b, (Set.Ici c).indicator (1 : ℝ → ℝ) s = max (b - c) 0 - max (a - c) 0 := by
  have hcont : Continuous fun s : ℝ => max (s - c) 0 := by fun_prop
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont.continuousOn (fun s _ => ?_) ?_
  · rcases lt_or_ge s c with h | h
    · have h0 : (Set.Ici c).indicator (1 : ℝ → ℝ) s = 0 :=
        Set.indicator_of_notMem (by simpa using h) _
      rw [h0]
      refine HasDerivAt.hasDerivWithinAt ?_
      refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with t ht
      exact max_eq_right (by simp only [Set.mem_Iio] at ht; linarith)
    · have h1 : (Set.Ici c).indicator (1 : ℝ → ℝ) s = 1 := Set.indicator_of_mem h _
      rw [h1]
      refine ((hasDerivAt_id s).sub_const c).hasDerivWithinAt.congr (fun t ht => ?_) ?_
      · exact max_eq_left (by simp only [Set.mem_Ioi] at ht; linarith)
      · exact max_eq_left (by linarith)
  · refine intervalIntegrable_of_bounded (measurable_one.indicator measurableSet_Ici) (C := 1)
      (fun x => ?_) _ _
    by_cases hx : x ∈ Set.Ici c <;> simp [hx]

private theorem haar_eq (x : ℝ) : haar x = (Set.Ici (0 : ℝ)).indicator 1 x -
    2 * (Set.Ici (1 / 2 : ℝ)).indicator 1 x + (Set.Ici (1 : ℝ)).indicator 1 x := by
  simp only [haar, Set.indicator_apply, Set.mem_Ico, Set.mem_Ici, Pi.one_apply]
  split_ifs <;> grind

/-- `∫_a^b h = Λ (b) − Λ (a)`. -/
private theorem integral_haar (a b : ℝ) : ∫ s in a..b, haar s = tent b - tent a := by
  have h : ∀ c : ℝ, IntervalIntegrable ((Set.Ici c).indicator (1 : ℝ → ℝ)) volume a b := fun c =>
    intervalIntegrable_of_bounded (measurable_one.indicator measurableSet_Ici) (C := 1)
      (fun x => by by_cases hx : x ∈ Set.Ici c <;> simp [hx]) _ _
  simp_rw [haar_eq]
  rw [intervalIntegral.integral_add ((h 0).sub ((h (1 / 2)).const_mul 2)) (h 1),
    intervalIntegral.integral_sub (h 0) ((h (1 / 2)).const_mul 2),
    intervalIntegral.integral_const_mul, integral_indicator_Ici, integral_indicator_Ici,
    integral_indicator_Ici]
  simp only [tent, sub_zero]
  ring

private theorem integral_haarSplit (a b : ℝ) : ∫ s in a..b, haarSplit s =
    (tent (2 * b) - tent (2 * a)) / 2 - (tent (2 * b - 1) - tent (2 * a - 1)) / 2 := by
  have h0 : IntervalIntegrable (fun s => haar (2 * s)) volume a b :=
    intervalIntegrable_of_bounded (measurable_haar.comp (measurable_const_mul 2))
      (fun x => abs_haar_le_one _) _ _
  have h1 : IntervalIntegrable (fun s => haar (2 * s - 1)) volume a b :=
    intervalIntegrable_of_bounded (measurable_haar.comp ((measurable_const_mul 2).sub_const 1))
      (fun x => abs_haar_le_one _) _ _
  simp only [haarSplit]
  rw [intervalIntegral.integral_sub h0 h1, intervalIntegral.integral_comp_mul_left _ two_ne_zero,
    intervalIntegral.integral_comp_mul_sub _ two_ne_zero, integral_haar, integral_haar]
  simp only [smul_eq_mul]
  ring

/-- `φ` is piecewise linear. -/
private theorem hilbertProfile_eq (x : ℝ) : hilbertProfile x =
    3 / 2 * (tent (2 * x + 1) - tent (2 * x)) + (tent (2 * x - 1) - tent (2 * x + 2)) / 2 := by
  have hm : Measurable fun u => haarSplit (x + u) := measurable_haarSplit.comp
    (measurable_const_add x)
  have hi : ∀ a b : ℝ, IntegrableOn (fun u => haarSplit (x + u)) (Set.Ico a b) := fun a b =>
    Measure.integrableOn_of_bounded (M := 1) (by simp) hm.aestronglyMeasurable
      (ae_of_all _ fun u => abs_haarSplit_le _)
  have h1 : ∀ u, haarSplit (x + u) * haar u =
      (Set.Ico (0 : ℝ) (1 / 2)).indicator (fun u => haarSplit (x + u)) u -
        (Set.Ico (1 / 2 : ℝ) 1).indicator (fun u => haarSplit (x + u)) u := fun u => by
    simp only [haar, Set.indicator_apply, Pi.one_apply]
    split_ifs <;> ring
  rw [hilbertProfile, haarCorrelation]
  simp_rw [h1]
  rw [integral_sub ((hi _ _).integrable_indicator measurableSet_Ico)
      ((hi _ _).integrable_indicator measurableSet_Ico), integral_indicator measurableSet_Ico,
    integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_comp_add_left (fun u => haarSplit u),
    intervalIntegral.integral_comp_add_left (fun u => haarSplit u), integral_haarSplit,
    integral_haarSplit]
  ring_nf

private theorem continuous_hilbertProfile : Continuous hilbertProfile := by
  rw [show hilbertProfile = _ from funext hilbertProfile_eq]
  unfold tent
  fun_prop

/-- `∫_0^1 φ = −1/8` (HNVW I, p. 385). -/
theorem integral_hilbertProfile : ∫ s in (0 : ℝ)..1, hilbertProfile s = -1 / 8 := by
  -- the graph of `φ` on `[0, 1]`: linear between `0, -3/4, 0, 1/4, 0` at `0, 1/4, 1/2, 3/4, 1`
  have hi : ∀ a b : ℝ, IntervalIntegrable hilbertProfile volume a b := fun a b =>
    continuous_hilbertProfile.intervalIntegrable a b
  have key : ∀ a b m c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, hilbertProfile s = m * s + c) →
      ∫ s in a..b, hilbertProfile s = m * ((b ^ 2 - a ^ 2) / 2) + (b - a) * c := by
    intro a b m c hab h
    rw [intervalIntegral.integral_congr (g := fun s => m * s + c)
      (by rw [Set.uIcc_of_le hab]; exact h), intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _) (by simp),
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      smul_eq_mul]
  have h1 := key 0 (1 / 4) (-3) 0 (by norm_num) fun s hs => by
    rw [Set.mem_Icc] at hs; rw [hilbertProfile_eq]; simp only [tent]; grind
  have h2 := key (1 / 4) (1 / 2) 3 (-3 / 2) (by norm_num) fun s hs => by
    rw [Set.mem_Icc] at hs; rw [hilbertProfile_eq]; simp only [tent]; grind
  have h3 := key (1 / 2) (3 / 4) 1 (-1 / 2) (by norm_num) fun s hs => by
    rw [Set.mem_Icc] at hs; rw [hilbertProfile_eq]; simp only [tent]; grind
  have h4 := key (3 / 4) 1 (-1) 1 (by norm_num) fun s hs => by
    rw [Set.mem_Icc] at hs; rw [hilbertProfile_eq]; simp only [tent]; grind
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (3 / 4)) (hi (3 / 4) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 / 2)) (hi (1 / 2) (3 / 4)),
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 / 4)) (hi (1 / 4) (1 / 2)),
    h1, h2, h3, h4]
  norm_num

/-- HNVW I, Example 5.1.11: `φ` is odd. -/
theorem hilbertProfile_neg (x : ℝ) : hilbertProfile (-x) = -hilbertProfile x := by
  have h : ∀ y, tent (1 - y) = tent y := fun y => by
    simp only [tent]
    rcases le_total y 0 with h0 | h0 <;> rcases le_total y 1 with h1 | h1 <;>
      rcases le_total y (1 / 2) with h2 | h2 <;> grind
  rw [hilbertProfile_eq, hilbertProfile_eq, ← h (2 * x + 1), ← h (2 * x), ← h (2 * x - 1),
    ← h (2 * x + 2)]
  ring_nf

private theorem hilbertProfile_of_one_le {x : ℝ} (hx : 1 ≤ x) : hilbertProfile x = 0 := by
  rw [hilbertProfile_eq]
  simp only [tent]
  grind

/-- `φ` vanishes outside `[-1, 1]`. -/
private theorem hilbertProfile_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : hilbertProfile x = 0 := by
  rcases le_abs.1 hx with h | h
  · exact hilbertProfile_of_one_le h
  · rw [← neg_neg x, hilbertProfile_neg, hilbertProfile_of_one_le h, neg_zero]

private theorem abs_hilbertProfile_le (x : ℝ) : |hilbertProfile x| ≤ 1 := by
  rw [hilbertProfile_eq]
  simp only [tent]
  grind

/-! ### The primitive of `φ` and the kernel `ψ` -/

/-- HNVW I, (5.21): `Φ (x) = ∫_0^x φ`. -/
private noncomputable def hilbertPrimitive (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, hilbertProfile s

private theorem continuous_hilbertPrimitive : Continuous hilbertPrimitive :=
  intervalIntegral.continuous_primitive
    (fun a b => continuous_hilbertProfile.intervalIntegrable a b) 0

private theorem hilbertPrimitive_neg (x : ℝ) : hilbertPrimitive (-x) = hilbertPrimitive x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) hilbertProfile
  simp only [hilbertProfile_neg, intervalIntegral.integral_neg, neg_zero] at h
  rw [hilbertPrimitive, intervalIntegral.integral_symm, ← h, neg_neg, hilbertPrimitive]

private theorem hilbertPrimitive_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    hilbertPrimitive x = -1 / 8 := by
  rw [hilbertPrimitive, ← intervalIntegral.integral_add_adjacent_intervals
    (continuous_hilbertProfile.intervalIntegrable 0 1)
    (continuous_hilbertProfile.intervalIntegrable 1 x), integral_hilbertProfile,
    intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
  · simp
  · intro s hs
    rw [Set.uIcc_of_le hx] at hs
    exact hilbertProfile_of_one_le hs.1

private theorem hilbertPrimitive_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    hilbertPrimitive x = -1 / 8 := by
  rcases le_abs.1 hx with h | h
  · exact hilbertPrimitive_of_one_le h
  · rw [← hilbertPrimitive_neg, hilbertPrimitive_of_one_le h]

private theorem abs_hilbertPrimitive_le (x : ℝ) : |hilbertPrimitive x| ≤ |x| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := 1)
    (f := hilbertProfile) fun s _ => abs_hilbertProfile_le s
  simpa [hilbertPrimitive] using h

private theorem measurable_hilbertError : Measurable hilbertError :=
  (measurable_inv.mul continuous_hilbertPrimitive.measurable).indicator measurableSet_Icc

private theorem abs_hilbertError_le (x : ℝ) : |hilbertError x| ≤ 1 := by
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [hilbertError, Set.indicator_of_mem hx, abs_mul, abs_inv]
    rcases eq_or_ne x 0 with rfl | h0
    · simp
    · calc |x|⁻¹ * |hilbertPrimitive x| ≤ |x|⁻¹ * |x| :=
            mul_le_mul_of_nonneg_left (abs_hilbertPrimitive_le x) (by positivity)
        _ = 1 := inv_mul_cancel₀ (abs_pos.2 h0).ne'
  · rw [hilbertError, Set.indicator_of_notMem hx]
    simp

private theorem hilbertError_of_one_lt_abs {x : ℝ} (hx : 1 < |x|) : hilbertError x = 0 := by
  rw [hilbertError, Set.indicator_of_notMem]
  rw [Set.mem_Icc, ← abs_le]
  exact not_le.2 hx

/-- HNVW I, p. 385: `y⁻¹ Φ (y / ε) = ψ_ε (y) − (8 y)⁻¹ 1_{|y| > ε}`. -/
private theorem inv_mul_hilbertPrimitive {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    y⁻¹ * hilbertPrimitive (ε⁻¹ * y) =
      ε⁻¹ * hilbertError (ε⁻¹ * y) - 1 / 8 * {y | ε < |y|}.indicator (fun y => y⁻¹) y := by
  have habs : |ε⁻¹ * y| = ε⁻¹ * |y| := by rw [abs_mul, abs_of_pos (inv_pos.2 hε)]
  by_cases hy : ε < |y|
  · have h1 : 1 < |ε⁻¹ * y| := by
      rw [habs, ← div_eq_inv_mul, one_lt_div hε]
      exact hy
    rw [hilbertError_of_one_lt_abs h1, hilbertPrimitive_of_one_le_abs h1.le,
      Set.indicator_of_mem (by exact hy)]
    ring
  · have h1 : ε⁻¹ * y ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc, ← abs_le, habs, ← div_eq_inv_mul, div_le_one hε]
      exact not_lt.1 hy
    rw [Set.indicator_of_notMem (by exact hy), hilbertError, Set.indicator_of_mem h1, mul_inv,
      inv_inv]
    change _ = ε⁻¹ * (ε * y⁻¹ * hilbertPrimitive (ε⁻¹ * y)) - _
    field_simp
    ring

/-- HNVW I, p. 384: `∫_ε^R φ_t (y) dt/t = y⁻¹ (Φ (y / ε) − Φ (y / R))`. -/
private theorem integral_dilate_hilbertProfile {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (y : ℝ) :
    ∫ t in ε..R, t⁻¹ * (t⁻¹ * hilbertProfile (t⁻¹ * y)) =
      y⁻¹ * hilbertPrimitive (ε⁻¹ * y) - y⁻¹ * hilbertPrimitive (R⁻¹ * y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · have h0 := hilbertProfile_neg 0
    rw [neg_zero] at h0
    simp [self_eq_neg.1 h0]
  have hpos : ∀ t ∈ Set.uIcc ε R, t ≠ 0 := fun t ht => by
    rw [Set.uIcc_of_le hεR] at ht
    exact (hε.trans_le ht.1).ne'
  have h := intervalIntegral.integral_comp_mul_deriv (a := ε) (b := R) (f := fun t => t⁻¹ * y)
    (f' := fun t => -(t ^ 2)⁻¹ * y) (g := hilbertProfile)
    (fun t ht => (hasDerivAt_inv (hpos t ht)).mul_const y)
    (ContinuousOn.mul (ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop)
      fun t ht => pow_ne_zero 2 (hpos t ht))) continuousOn_const) continuous_hilbertProfile
  have h2 : ∫ u in ε⁻¹ * y..R⁻¹ * y, hilbertProfile u =
      hilbertPrimitive (R⁻¹ * y) - hilbertPrimitive (ε⁻¹ * y) :=
    (intervalIntegral.integral_interval_sub_left
      (continuous_hilbertProfile.intervalIntegrable _ _)
      (continuous_hilbertProfile.intervalIntegrable _ _)).symm
  rw [h2] at h
  have h3 : ∀ t : ℝ, t⁻¹ * (t⁻¹ * hilbertProfile (t⁻¹ * y)) =
      -y⁻¹ * ((hilbertProfile ∘ fun t => t⁻¹ * y) t * (-(t ^ 2)⁻¹ * y)) := fun t => by
    simp only [Function.comp_apply]
    field_simp
  simp_rw [h3]
  rw [intervalIntegral.integral_const_mul, h]
  ring

/-- HNVW I, p. 385: `∫_ε^R φ_t (y) dt/t = ψ_ε (y) − ψ_R (y) − (8 y)⁻¹ 1_{ε < |y| < R}`, for
`|y| ≠ R`. -/
private theorem integral_dilate_hilbertProfile_eq {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {y : ℝ}
    (hy : |y| ≠ R) :
    ∫ t in ε..R, t⁻¹ * (t⁻¹ * hilbertProfile (t⁻¹ * y)) =
      ε⁻¹ * hilbertError (ε⁻¹ * y) - R⁻¹ * hilbertError (R⁻¹ * y) -
        1 / 8 * {y | ε < |y| ∧ |y| < R}.indicator (fun y => y⁻¹) y := by
  have hind : {y | ε < |y| ∧ |y| < R}.indicator (fun y : ℝ => y⁻¹) y =
      {y | ε < |y|}.indicator (fun y => y⁻¹) y - {y | R < |y|}.indicator (fun y => y⁻¹) y := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rcases lt_or_ge ε |y| with h | h <;> rcases lt_or_ge R |y| with h' | h'
    · simp [h, h', h'.le]
    · simp [h, not_lt.2 h', h'.lt_of_ne hy]
    · exact absurd (h'.trans_le h) (not_lt.2 hεR)
    · simp [not_lt.2 h, not_lt.2 h']
  rw [integral_dilate_hilbertProfile hε hεR, inv_mul_hilbertPrimitive hε,
    inv_mul_hilbertPrimitive (hε.trans_le hεR), hind]
  ring

/-! ### The truncations as averages of the dilated convolutions -/

private theorem integrable_kernel_smul {f : ℝ → X} (hf : LocallyIntegrable f) {g : ℝ → ℝ}
    (hg : Measurable g) {C r : ℝ} (hC : ∀ z, |g z| ≤ C) (h0 : ∀ z, r < |z| → g z = 0) (x : ℝ) :
    Integrable fun y => g (x - y) • f y := by
  have hK : IntegrableOn f (Set.Icc (x - r) (x + r)) := hf.integrableOn_isCompact isCompact_Icc
  have h1 := (hK.integrable_indicator measurableSet_Icc).bdd_smul C
    (φ := fun y => g (x - y)) (hg.comp (measurable_const_sub x)).aestronglyMeasurable
    (ae_of_all _ fun y => hC (x - y))
  refine h1.congr (ae_of_all _ fun y => ?_)
  simp only [Pi.smul_apply']
  by_cases hy : y ∈ Set.Icc (x - r) (x + r)
  · rw [Set.indicator_of_mem hy]
  · rw [h0 (x - y), zero_smul, zero_smul]
    by_contra h
    rw [not_lt, abs_le] at h
    exact hy ⟨by linarith, by linarith⟩

/-- The double integral of (5.23) converges absolutely. -/
private theorem integrable_dilate_smul {f : ℝ → X} (hf : LocallyIntegrable f) {ε R : ℝ}
    (hε : 0 < ε) (x : ℝ) :
    Integrable (Function.uncurry fun t y : ℝ =>
        (t⁻¹ * (t⁻¹ * hilbertProfile (t⁻¹ * (x - y)))) • f y)
      ((volume.restrict (Set.Ioc ε R)).prod volume) := by
  have hK : IntegrableOn f (Set.Icc (x - R) (x + R)) := hf.integrableOn_isCompact isCompact_Icc
  have h1 : Integrable (fun _ : ℝ => ε⁻¹ * ε⁻¹) (volume.restrict (Set.Ioc ε R)) :=
    integrable_const _
  refine (h1.mul_prod (hK.integrable_indicator measurableSet_Icc).norm).mono'
    (AEStronglyMeasurable.smul ?_ hf.aestronglyMeasurable.comp_snd) ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact measurable_fst.inv.mul (measurable_fst.inv.mul (continuous_hilbertProfile.measurable.comp
      (measurable_fst.inv.mul (measurable_const.sub measurable_snd))))
  · have hae : ∀ᵐ z ∂(volume.restrict (Set.Ioc ε R)).prod (volume : Measure ℝ),
        z.1 ∈ Set.Ioc ε R :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hae] with ⟨t, y⟩ ht
    have ht0 : 0 < t := hε.trans ht.1
    simp only [Function.uncurry_apply_pair, norm_smul, norm_mul, Real.norm_eq_abs, abs_inv,
      abs_of_pos ht0]
    by_cases hy : y ∈ Set.Icc (x - R) (x + R)
    · rw [Set.indicator_of_mem hy]
      have h2 : t⁻¹ ≤ ε⁻¹ := inv_anti₀ hε ht.1.le
      have h3 := abs_hilbertProfile_le (t⁻¹ * (x - y))
      calc t⁻¹ * (t⁻¹ * |hilbertProfile (t⁻¹ * (x - y))|) * ‖f y‖
          ≤ ε⁻¹ * (ε⁻¹ * 1) * ‖f y‖ := by gcongr
        _ = ε⁻¹ * ε⁻¹ * ‖f y‖ := by rw [mul_one]
    · have h4 : R < |x - y| := by
        by_contra h
        rw [not_lt, abs_le] at h
        exact hy ⟨by linarith, by linarith⟩
      rw [hilbertProfile_of_one_le_abs, Set.indicator_of_notMem hy]
      · simp
      · rw [abs_mul, abs_inv, abs_of_pos ht0, ← div_eq_inv_mul, one_le_div ht0]
        exact ht.2.trans h4.le

/-- HNVW I, p. 384: the change of the order of integration. -/
private theorem integral_dilateConv_swap [CompleteSpace X] {f : ℝ → X} (hf : LocallyIntegrable f)
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (x : ℝ) :
    ∫ t in ε..R, t⁻¹ • dilateConv hilbertProfile t f x =
      ∫ y, (∫ t in ε..R, t⁻¹ * (t⁻¹ * hilbertProfile (t⁻¹ * (x - y)))) • f y := by
  rw [intervalIntegral.integral_of_le hεR]
  simp_rw [dilateConv, ← integral_smul, smul_smul]
  rw [integral_integral_swap (integrable_dilate_smul hf hε x)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [integral_smul_const, intervalIntegral.integral_of_le hεR]

private theorem integrable_hilbertError_smul {f : ℝ → X} (hf : LocallyIntegrable f) {r : ℝ}
    (hr : 0 < r) (x : ℝ) : Integrable fun y => (r⁻¹ * hilbertError (r⁻¹ * (x - y))) • f y := by
  refine integrable_kernel_smul hf (g := fun z => r⁻¹ * hilbertError (r⁻¹ * z)) (C := r⁻¹)
    (r := r) (measurable_const.mul (measurable_hilbertError.comp (measurable_const_mul _)))
    (fun z => ?_) (fun z hz => ?_) x
  · rw [abs_mul, abs_of_pos (inv_pos.2 hr)]
    exact mul_le_of_le_one_right (inv_pos.2 hr).le (abs_hilbertError_le _)
  · rw [hilbertError_of_one_lt_abs, mul_zero]
    rw [abs_mul, abs_of_pos (inv_pos.2 hr), ← div_eq_inv_mul, one_lt_div hr]
    exact hz

private theorem integrable_truncated_smul {f : ℝ → X} (hf : LocallyIntegrable f) {ε : ℝ}
    (hε : 0 < ε) (R x : ℝ) : Integrable fun y =>
      {z | ε < |z| ∧ |z| < R}.indicator (fun z => z⁻¹) (x - y) • f y := by
  refine integrable_kernel_smul hf (C := ε⁻¹) (r := R) (measurable_inv.indicator
    ((measurableSet_lt measurable_const measurable_norm).inter (measurableSet_lt measurable_norm
      measurable_const))) (fun z => ?_) (fun z hz => by simp [hz.le]) x
  by_cases hz : ε < |z| ∧ |z| < R
  · simpa [hz, abs_inv] using inv_anti₀ hε hz.1.le
  · simp [hz, hε.le]

/-- `H_{ε,R} f` as an integral over the line. -/
private theorem truncatedHilbert_eq_integral (ε R : ℝ) (f : ℝ → X) (x : ℝ) :
    truncatedHilbert ε R f x = Real.pi⁻¹ •
      ∫ y, {z | ε < |z| ∧ |z| < R}.indicator (fun z => z⁻¹) (x - y) • f y := by
  have hS : MeasurableSet {y | ε < |x - y| ∧ |x - y| < R} :=
    (measurableSet_lt measurable_const (measurable_const_sub x).norm).inter
      (measurableSet_lt (measurable_const_sub x).norm measurable_const)
  rw [truncatedHilbert, ← integral_indicator hS]
  congr 2
  funext y
  by_cases hy : ε < |x - y| ∧ |x - y| < R <;> simp [hy]

/-- HNVW I, the display before (5.23), p. 385. -/
theorem integral_dilateConv_eq {f : ℝ → X} (hf : LocallyIntegrable f) {ε R : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R) (x : ℝ) :
    ∫ t in ε..R, t⁻¹ • dilateConv hilbertProfile t f x =
      dilateConv hilbertError ε f x - dilateConv hilbertError R f x -
        (Real.pi / 8) • truncatedHilbert ε R f x := by
  by_cases hX : CompleteSpace X
  swap
  · simp [dilateConv, truncatedHilbert, integral, hX]
  have hR : 0 < R := hε.trans_le hεR
  -- the integration in `t`
  have h : ∀ᵐ y : ℝ, (∫ t in ε..R, t⁻¹ * (t⁻¹ * hilbertProfile (t⁻¹ * (x - y)))) • f y =
      (ε⁻¹ * hilbertError (ε⁻¹ * (x - y))) • f y - (R⁻¹ * hilbertError (R⁻¹ * (x - y))) • f y -
        (1 / 8 : ℝ) • {z | ε < |z| ∧ |z| < R}.indicator (fun z => z⁻¹) (x - y) • f y := by
    filter_upwards [Measure.ae_ne volume (x - R), Measure.ae_ne volume (x + R)] with y hy hy'
    have hne : |x - y| ≠ R := fun h => by
      rcases abs_eq hR.le |>.1 h with h | h
      · exact hy (by linarith)
      · exact hy' (by linarith)
    rw [integral_dilate_hilbertProfile_eq hε hεR hne]
    module
  have hi := integrable_hilbertError_smul hf hε x
  have hi' := integrable_hilbertError_smul hf hR x
  rw [integral_dilateConv_swap hf hε hεR, integral_congr_ae h]
  refine (integral_sub (hi.sub hi') ((integrable_truncated_smul hf hε R x).smul (1 / 8 : ℝ))).trans
    ?_
  simp only [Pi.smul_apply]
  rw [integral_sub' hi hi', integral_smul, truncatedHilbert_eq_integral, smul_smul, dilateConv,
    dilateConv]
  congr 2
  field_simp

/-! ### The bound -/

/-- `‖ψ‖_1 ≤ 2`, as `|ψ| ≤ 1_{[−1, 1]}`. -/
private theorem lintegral_hilbertError_le : ∫⁻ z, ‖hilbertError z‖ₑ ≤ 2 := by
  calc ∫⁻ z, ‖hilbertError z‖ₑ ≤ ∫⁻ z, (Set.Icc (-1 : ℝ) 1).indicator (fun _ => 1) z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
        · rw [Set.indicator_of_mem hz, ← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_one.2 (abs_hilbertError_le z)
        · rw [hilbertError, Set.indicator_of_notMem hz]
          simp
    _ = 2 := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, one_mul]
        norm_num

/-- `‖ψ_t * f‖_p ≤ 2 ‖f‖_p` (Young's inequality). -/
private theorem eLpNorm_dilateConv_hilbertError_le {p : ℝ} (hp : 1 ≤ p) {f : ℝ → X}
    (hf : AEStronglyMeasurable f volume) {t : ℝ} (ht : 0 < t) :
    eLpNorm (dilateConv hilbertError t f) (ENNReal.ofReal p) volume ≤
      2 * eLpNorm f (ENNReal.ofReal p) volume :=
  (eLpNorm_dilateConv_le hp measurable_hilbertError ht hf).trans (by
    gcongr
    exact lintegral_hilbertError_le)

private theorem intervalIntegrable_dilateConv {f : ℝ → X} (hf : LocallyIntegrable f) (x : ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => t⁻¹ • dilateConv hilbertProfile t f x) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine ((integrable_dilate_smul hf (R := b) ha x).integral_prod_left).congr
    (ae_of_all _ fun t => ?_)
  simp only [Function.uncurry_apply_pair, dilateConv, ← integral_smul, smul_smul]

/-- The substitution `t = 2^i s`. -/
private theorem integral_dilateConv_two_pow (f : ℝ → X) (ε : ℝ) (i : ℕ) (x : ℝ) :
    ∫ t in 2 ^ i * ε..2 ^ (i + 1) * ε, t⁻¹ • dilateConv hilbertProfile t f x =
      ∫ s in ε..2 * ε, s⁻¹ • dilateConv hilbertProfile (2 ^ i * s) f x := by
  have hpow : (0 : ℝ) < 2 ^ i := by positivity
  rw [show (2 : ℝ) ^ (i + 1) * ε = 2 ^ i * (2 * ε) by ring,
    ← intervalIntegral.smul_integral_comp_mul_left, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [smul_smul, mul_inv]
  rw [mul_inv_cancel_left₀ hpow.ne']

/-- `∫_ε^{2^n ε} φ_t * f dt/t = ∫_ε^{2ε} Σ_{j<n} φ_{2^{n−1} s 2^{−j}} * f ds/s`. -/
private theorem integral_dilateConv_eq_sum {f : ℝ → X} (hf : LocallyIntegrable f) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) (x : ℝ) :
    ∫ t in ε..2 ^ n * ε, t⁻¹ • dilateConv hilbertProfile t f x =
      ∫ s in ε..2 * ε, s⁻¹ • ∑ j ∈ Finset.range n,
        dilateConv hilbertProfile (2 ^ (n - 1) * s * (2 ^ j)⁻¹) f x := by
  have hpow : ∀ i : ℕ, (0 : ℝ) < 2 ^ i := fun i => by positivity
  have hle : ∀ i : ℕ, (2 : ℝ) ^ i * ε ≤ 2 ^ (i + 1) * ε := fun i => by
    rw [pow_succ]; nlinarith [hpow i, mul_pos (hpow i) hε]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t => t⁻¹ • dilateConv hilbertProfile t f x) (a := fun i : ℕ => 2 ^ i * ε) (n := n)
    fun i _ => intervalIntegrable_dilateConv hf x (mul_pos (hpow i) hε) (hle i)
  simp only [pow_zero, one_mul] at hsum
  have hint : ∀ i ∈ Finset.range n, IntervalIntegrable
      (fun s => s⁻¹ • dilateConv hilbertProfile (2 ^ i * s) f x) volume ε (2 * ε) := by
    intro i _
    have h := (intervalIntegrable_dilateConv hf x (a := 2 ^ i * ε) (b := 2 ^ i * (2 * ε))
      (mul_pos (hpow i) hε) (by nlinarith [mul_pos (hpow i) hε])).comp_mul_left (c := 2 ^ i)
    rw [mul_div_cancel_left₀ _ (hpow i).ne', mul_div_cancel_left₀ _ (hpow i).ne'] at h
    refine (h.smul ((2 : ℝ) ^ i)).congr_ae (ae_of_all _ fun s => ?_)
    simp only [Pi.smul_apply, smul_smul, mul_inv]
    rw [mul_inv_cancel_left₀ (hpow i).ne']
  rw [← hsum, Finset.sum_congr rfl fun i _ => integral_dilateConv_two_pow f ε i x,
    ← intervalIntegral.integral_finsetSum hint]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← Finset.smul_sum, ← Finset.sum_range_reflect]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  rw [Finset.mem_range] at hj
  have : (2 : ℝ) ^ (n - 1) = 2 ^ (n - 1 - j) * 2 ^ j := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

/-- `∫_ε^{2ε} ds/s = log 2`. -/
private theorem lintegral_enorm_inv {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ s in Set.Ioc ε (2 * ε), ‖s⁻¹‖ₑ = ENNReal.ofReal (Real.log 2) := by
  have h2ε : ε ≤ 2 * ε := by linarith
  have hi : IntegrableOn (fun s : ℝ => s⁻¹) (Set.Ioc ε (2 * ε)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h2ε]
    refine intervalIntegral.intervalIntegrable_inv (fun s hs => ?_) continuousOn_id
    rw [Set.uIcc_of_le h2ε] at hs
    exact (hε.trans_le hs.1).ne'
  have hlog := integral_inv_of_pos hε (by linarith : 0 < 2 * ε)
  rw [intervalIntegral.integral_of_le h2ε, mul_div_cancel_right₀ _ hε.ne'] at hlog
  rw [← hlog, ofReal_integral_eq_lintegral_ofReal hi]
  · refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    exact Real.enorm_of_nonneg (inv_nonneg.2 (hε.trans hs.1).le)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact inv_nonneg.2 (hε.trans hs.1).le

/-- The main term of (5.23), by the bounds for the averages of the dyadic shifts and Minkowski's
inequality (HNVW I, Proposition 5.1.10, first inequality): the integration over the dilations. -/
private theorem eLpNorm_integral_dilateConv_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) :
    eLpNorm (fun x => ∫ s in ε..2 * ε, s⁻¹ • ∑ j ∈ Finset.range n,
        dilateConv hilbertProfile (2 ^ (n - 1) * s * (2 ^ j)⁻¹) f x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (Real.log 2) * (2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume) := by
  -- replace `f` by a strongly measurable function
  obtain ⟨g, hgm, hfg⟩ := hf.aestronglyMeasurable
  simp only [dilateConv_congr_ae hilbertProfile _ hfg,
    intervalIntegral.integral_of_le (show ε ≤ 2 * ε by linarith)]
  have hF : StronglyMeasurable (Function.uncurry fun x s : ℝ => ∑ j ∈ Finset.range n,
      dilateConv hilbertProfile (2 ^ (n - 1) * s * (2 ^ j)⁻¹) g x) := by
    refine Finset.stronglyMeasurable_fun_sum _ fun j _ => ?_
    exact (stronglyMeasurable_uncurry_dilateConv continuous_hilbertProfile.measurable
      hgm).comp_measurable (measurable_fst.prodMk ((measurable_snd.const_mul _).mul_const _))
  rw [eLpNorm_congr_ae hfg, ← lintegral_enorm_inv hε]
  refine eLpNorm_integral_smul_le hp.le measurable_inv hF ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact eLpNorm_sum_dilateConv_le hp hβ ((memLp_congr_ae hfg).1 hf) n
    (mul_pos (by positivity) (hε.trans hs.1))

/-- (5.23), for `R = 2^n ε`, where the integral over `[ε, R]` is an average of dyadic shifts and the
additional integrals do not occur. -/
private theorem truncatedHilbert_eq_sub {f : ℝ → X} (hf : LocallyIntegrable f) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) : truncatedHilbert ε (2 ^ n * ε) f = (8 / Real.pi) •
      (dilateConv hilbertError ε f - dilateConv hilbertError (2 ^ n * ε) f -
        fun x => ∫ s in ε..2 * ε, s⁻¹ • ∑ j ∈ Finset.range n,
          dilateConv hilbertProfile (2 ^ (n - 1) * s * (2 ^ j)⁻¹) f x) := by
  funext x
  have h := integral_dilateConv_eq hf hε
    (le_mul_of_one_le_left hε.le (one_le_pow₀ (n := n) one_le_two)) x
  rw [integral_dilateConv_eq_sum hf hε] at h
  simp only [Pi.smul_apply, Pi.sub_apply]
  rw [h, sub_sub_cancel, smul_smul, show 8 / Real.pi * (Real.pi / 8) = 1 by field_simp, one_smul]

/-- **The truncated Hilbert transform on UMD spaces** (HNVW I, Theorem 5.1.13, for the truncations
`H_{ε, 2^n ε}`, with a uniform bound instead of the limit). -/
theorem eLpNorm_truncatedHilbert_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) :
    eLpNorm (truncatedHilbert ε (2 ^ n * ε) f) (ENNReal.ofReal p) volume ≤
      (4 * β ^ 2 + 11) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using hp.le
  set N := eLpNorm f (ENNReal.ofReal p) volume
  have hA := eLpNorm_integral_dilateConv_le hp hβ hf hε n
  have hB := eLpNorm_dilateConv_hilbertError_le hp.le hf.aestronglyMeasurable hε
  have hB' := eLpNorm_dilateConv_hilbertError_le hp.le hf.aestronglyMeasurable
    (by positivity : 0 < 2 ^ n * ε)
  -- the constants
  have hpi := Real.pi_gt_three
  have hlog := Real.log_two_lt_d9
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hc1 : ENNReal.ofReal (8 / Real.pi) * 4 ≤ 11 := by
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_ofNat 11, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos]
    linarith
  have hc2 : ENNReal.ofReal (8 / Real.pi) * (ENNReal.ofReal (Real.log 2) * 2) ≤ 4 := by
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hlog0,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos]
    linarith
  calc eLpNorm (truncatedHilbert ε (2 ^ n * ε) f) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (8 / Real.pi) *
          (2 * N + 2 * N + ENNReal.ofReal (Real.log 2) * (2 * β ^ 2 * N)) := by
        rw [truncatedHilbert_eq_sub (hf.locallyIntegrable hp1) hε, eLpNorm_const_smul,
          Real.enorm_of_nonneg (by positivity)]
        gcongr
        exact (eLpNorm_sub_le hp1).trans (add_le_add ((eLpNorm_sub_le hp1).trans
          (add_le_add hB hB')) hA)
    _ = (ENNReal.ofReal (8 / Real.pi) * (ENNReal.ofReal (Real.log 2) * 2) * β ^ 2 +
          ENNReal.ofReal (8 / Real.pi) * 4) * N := by ring
    _ ≤ (4 * β ^ 2 + 11) * N := by gcongr

end HarmonicAnalysis
