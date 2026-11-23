/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.HilbertTransform.Fourier
import HarmonicAnalysis.VectorValued.Transference
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Littlewood–Paley inequality on the line for UMD spaces

Let `X` be a complex UMD space, `1 < p < ∞`, and let `f = 𝓕⁻ G ∈ L^p (ℝ; X)` with `G ∈ L¹`. For an
interval `I`, let `Δ_I f = 𝓕⁻ (1_I G)`. With independent fair signs `ε_k`,

* `‖Σ_{0 ≤ k < K} ε_k Δ_{(2^k, 2^{k+1})} f‖_{L^p (ℝ × Ω; X)} ≤ 72 ħ β ‖f‖_{L^p (ℝ; X)}`
  (`eLpNormRad_fourierInv_indicator_le`);
* `‖Σ_{|k| ≤ K} ε_k Δ_{I_k} f‖_{L^p (ℝ × Ω; X)} ≤ (144 ħ β + ħ) ‖f‖_{L^p (ℝ; X)}`, where
  `I_0 = (−1, 1)`, `I_k = (2^{k−1}, 2^k)` and `I_{−k} = −I_k` for `k > 0` (`lineBlock`,
  `eLpNormRad_lineBlock_le`), and the same for the dilates `ρ⁻¹ I_k`, `ρ > 0`
  (`eLpNormRad_lineBlock_dilate_le`).

Here `β` is a `UMD_p` constant of `X` and `ħ = dyadicHilbertBound β` the bound of the Hilbert
transform (`eLpNorm_fourierInv_sign_le_dyadic`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Section 5.3,
pp. 404–405 and 412–420: the interval multipliers from the Hilbert transform (Lemma 5.3.9 with
(5.35), p. 404, and Proposition 5.3.10, p. 405), Lemma 5.3.21 (a randomised Mihlin theorem, from
(5.36)), Lemma 5.3.22 (which is Proposition 5.1.10), Lemma 5.3.23 (the multipliers `1_I / φ̂_I`),
Theorem 5.3.24, right-hand inequality, for the intervals `(2^k, 2^{k+1})`, `0 ≤ k < K`, and
Corollary 5.3.25, right-hand inequality, for finitely many intervals; the dilated form of the
corollary gives, by dropping terms, the finite sums of Theorem 5.3.24 over all dyadic intervals (the
book deduces the corollary from the theorem). The left-hand inequalities are not treated.

The signs are real here, while the Rademacher variables of the book are complex if `X` is complex.
This costs a factor `2` in each application of the contraction principle (the book's constant for
real signs is `π/2`, HNVW I, Proposition 3.2.10). Of Lemma 5.3.21 only the case of scalar weights
that are the same for all `k` up to dilation is needed, `w = 1 / φ̂` on `[1/2, 1]`; hence no
`R`-bounds occur, and the `L¹` norm of `w'` replaces the Mihlin norm.
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal FourierTransform

namespace HarmonicAnalysis

/-! ### The Fourier transform of `φ = h * h̃` -/

private theorem integrable_haar : Integrable haar := by
  have h : IntegrableOn haar (Set.Ico 0 1) := by
    refine IntegrableOn.of_bound (by simp) measurable_haar.aestronglyMeasurable 1
      (ae_of_all _ fun x => abs_haar_le_one x)
  exact (integrableOn_iff_integrable_of_support_subset fun x hx => by
    by_contra h'
    exact hx (haar_of_notMem h')).1 h

/-- `φ = h * h̃`, with `h̃ (x) = h (−x)`. -/
private theorem haarCorrelation_eq_convolution :
    haarCorrelation haar = MeasureTheory.convolution (fun x => haar (-x)) haar
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  rw [haarCorrelation, convolution_def, ← integral_neg_eq_self]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [ContinuousLinearMap.mul_apply', ← sub_eq_add_neg]
  rw [mul_comm]

private theorem integrable_haarCorrelation : Integrable (haarCorrelation haar) := by
  rw [haarCorrelation_eq_convolution]
  exact integrable_haar.comp_neg.integrable_convolution _ integrable_haar

/-- The Fourier transform of `φ = h * h̃` is `ĥ (ξ) ĥ (−ξ)` (Fubini). -/
private theorem fourier_haarCorrelation_eq_mul (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ξ =
      𝓕 (fun x : ℝ => ((haar x : ℝ) : ℂ)) (-ξ) * 𝓕 (fun x : ℝ => ((haar x : ℝ) : ℂ)) ξ := by
  have h : (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) =
      MeasureTheory.convolution (fun x : ℝ => ((haar (-x) : ℝ) : ℂ))
        (fun x : ℝ => ((haar x : ℝ) : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext x
    rw [haarCorrelation_eq_convolution, convolution_def, convolution_def, ← integral_complex_ofReal]
    simp
  rw [h, ← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_comp_neg]
  exact Real.fourier_mul_convolution_eq (R := ℂ) integrable_haar.comp_neg.ofReal
    integrable_haar.ofReal ξ

/-- `∫_a^b e^{−2πi v ξ} dv`. -/
private theorem setIntegral_exp {a b : ℝ} (hab : a ≤ b) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∫ v in Set.Ico a b, Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) =
      (Complex.exp (-2 * Real.pi * ξ * Complex.I * b) -
        Complex.exp (-2 * Real.pi * ξ * Complex.I * a)) / (-2 * Real.pi * ξ * Complex.I) := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← integral_exp_mul_complex]
  · refine intervalIntegral.integral_congr fun v _ => ?_
    push_cast
    ring_nf
  · have := Real.pi_ne_zero
    simp [hξ]

/-- `ĥ (ξ) = (1 − e^{−πiξ})² / (2πiξ)`. -/
private theorem fourier_haar {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (fun x : ℝ => ((haar x : ℝ) : ℂ)) ξ =
      (1 - Complex.exp (-(Real.pi * ξ * Complex.I))) ^ 2 / (2 * Real.pi * ξ * Complex.I) := by
  have hpi := Real.pi_ne_zero
  have hd : (Real.pi : ℂ) * ξ ≠ 0 := by simp [hpi, hξ]
  have hc : Continuous fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) := by fun_prop
  have hi : ∀ a b : ℝ, IntegrableOn (fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I)) (Set.Ico a b) := fun a b =>
    (hc.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  have h1 : 𝓕 (fun x : ℝ => ((haar x : ℝ) : ℂ)) ξ =
      (∫ v in Set.Ico (0 : ℝ) (1 / 2),
        Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I)) -
      ∫ v in Set.Ico (1 / 2 : ℝ) 1,
        Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Ico,
      ← integral_indicator measurableSet_Ico, ← integral_sub
      ((hi _ _).integrable_indicator measurableSet_Ico)
      ((hi _ _).integrable_indicator measurableSet_Ico)]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [haar, Set.indicator_apply, Pi.one_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [h1, setIntegral_exp (by norm_num) hξ, setIntegral_exp (by norm_num) hξ]
  set z := Complex.exp (-(Real.pi * ξ * Complex.I)) with hz
  have e1 : Complex.exp (-2 * Real.pi * ξ * Complex.I * ((1 / 2 : ℝ) : ℂ)) = z := by
    rw [hz]
    push_cast
    ring_nf
  have e2 : Complex.exp (-2 * Real.pi * ξ * Complex.I * ((1 : ℝ) : ℂ)) = z ^ 2 := by
    rw [hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have e3 : Complex.exp (-2 * Real.pi * ξ * Complex.I * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [e1, e2, e3]
  have hI := Complex.I_ne_zero
  field_simp
  ring

/-- `φ̂ (ξ) = sin⁴ (πξ/2) / (πξ/2)²`, the Fourier transform of `φ = h * h̃` (HNVW I, proof of Lemma
5.3.23). -/
theorem fourier_haarCorrelation_haar {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ξ =
      ((Real.sin (Real.pi * ξ / 2) ^ 4 / (Real.pi * ξ / 2) ^ 2 : ℝ) : ℂ) := by
  have hpi := Real.pi_ne_zero
  have hd : (Real.pi : ℂ) * ξ ≠ 0 := by simp [hpi, hξ]
  rw [fourier_haarCorrelation_eq_mul, fourier_haar hξ, fourier_haar (neg_ne_zero.2 hξ)]
  -- `z = e^{−πiξ/2}`, `(1 − z²) (1 − z⁻²) = − (z − z⁻¹)² = 4 sin²`
  set t : ℂ := Real.pi * ξ / 2 with ht
  have h2 := Complex.two_sin t
  have e1 : Complex.exp (-(Real.pi * ξ * Complex.I)) = Complex.exp (-t * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul, ht]
    push_cast
    ring_nf
  have e2 : Complex.exp (-(Real.pi * ((-ξ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (t * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul, ht]
    push_cast
    ring_nf
  have e3 : Complex.exp (-t * Complex.I) * Complex.exp (t * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [e1, e2]
  push_cast
  rw [← ht]
  set u := Complex.exp (-t * Complex.I)
  set v := Complex.exp (t * Complex.I)
  have h4 : (1 - v ^ 2) ^ 2 * (1 - u ^ 2) ^ 2 = 16 * Complex.sin t ^ 4 := by
    have h5 : (1 - v ^ 2) * (1 - u ^ 2) = 4 * Complex.sin t ^ 2 := by
      have h6 : (2 * Complex.sin t) ^ 2 = ((u - v) * Complex.I) ^ 2 := by rw [h2]
      rw [mul_pow (u - v), Complex.I_sq] at h6
      linear_combination (u * v + 1 - 2) * e3 + (-1 : ℂ) * h6
    rw [← mul_pow, h5]
    ring
  have hD : t ≠ 0 := by
    rw [ht]
    exact div_ne_zero hd two_ne_zero
  have hden : 2 * (Real.pi : ℂ) * -ξ * Complex.I * (2 * Real.pi * ξ * Complex.I) = 16 * t ^ 2 := by
    rw [ht]
    linear_combination (-4 * (Real.pi : ℂ) ^ 2 * ξ ^ 2) * Complex.I_sq
  rw [div_mul_div_comm, h4, hden, mul_div_mul_left _ _ (by norm_num)]

/-! ### The weight `1 / φ̂` on `[1/2, 1]` -/

/-- HNVW I, proof of Lemma 5.3.23: `sin² t ≥ 2t/π ≥ 1/2` on `[π/4, π/2]`, hence `t / sin⁴ t ≤ π`. -/
private theorem div_sin_pow_le {t : ℝ} (h1 : Real.pi / 4 ≤ t) (h2 : t ≤ Real.pi / 2) :
    t / Real.sin t ^ 4 ≤ Real.pi := by
  have hpi := Real.pi_pos
  have ht : 0 < t := by linarith
  have h3 : 2 / Real.pi * t ≤ Real.sin t ^ 2 := by
    have h := Real.one_sub_mul_le_cos (x := Real.pi - 2 * t) (by linarith) (by linarith)
    rw [Real.cos_pi_sub, Real.cos_two_mul] at h
    have h' : 2 / Real.pi * (Real.pi - 2 * t) = 2 - 2 * (2 / Real.pi * t) := by
      field_simp
    have h4 := Real.sin_sq_add_cos_sq t
    nlinarith
  have h4 : 1 / 2 ≤ 2 / Real.pi * t := by
    calc (1 : ℝ) / 2 = 2 / Real.pi * (Real.pi / 4) := by
          field_simp
          norm_num
      _ ≤ 2 / Real.pi * t := by gcongr
  have h5 : 0 < Real.sin t ^ 4 := by
    have h : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith)
    positivity
  rw [div_le_iff₀ h5]
  have h6 : (2 / Real.pi * t) * (1 / 2) ≤ Real.sin t ^ 2 * Real.sin t ^ 2 :=
    mul_le_mul h3 (h4.trans h3) (by norm_num) (by positivity)
  calc t = Real.pi * ((2 / Real.pi * t) * (1 / 2)) := by field_simp
    _ ≤ Real.pi * (Real.sin t ^ 2 * Real.sin t ^ 2) := by gcongr
    _ = Real.pi * Real.sin t ^ 4 := by ring

/-- `w = 1 / φ̂`, `w (s) = t² / sin⁴ t` with `t = πs/2`. -/
private noncomputable def haarWeight (s : ℝ) : ℝ :=
  (Real.pi * s / 2) ^ 2 / Real.sin (Real.pi * s / 2) ^ 4

/-- `w' (s) = π (t / sin⁴ t) (1 − 2 t cos t / sin t)` with `t = πs/2`. -/
private noncomputable def haarWeightDeriv (s : ℝ) : ℝ :=
  Real.pi * (Real.pi * s / 2 / Real.sin (Real.pi * s / 2) ^ 4) *
    (1 - 2 * (Real.pi * s / 2 * Real.cos (Real.pi * s / 2) / Real.sin (Real.pi * s / 2)))

private theorem measurable_haarWeightDeriv : Measurable haarWeightDeriv := by
  unfold haarWeightDeriv
  fun_prop

private theorem sin_half_pos {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1) :
    0 < Real.sin (Real.pi * s / 2) := by
  have hpi := Real.pi_pos
  exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1]) (by nlinarith [hs.2])

private theorem hasDerivAt_haarWeight {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1) :
    HasDerivAt haarWeight (haarWeightDeriv s) s := by
  have hsin := (sin_half_pos hs).ne'
  have h1 : HasDerivAt (fun s : ℝ => Real.pi * s / 2) (Real.pi / 2) s := by
    simpa using ((hasDerivAt_id s).const_mul Real.pi).div_const 2
  have h2 := (h1.pow 2).fun_div (h1.sin.pow 4) (pow_ne_zero 4 hsin)
  refine h2.congr_deriv ?_
  rw [haarWeightDeriv]
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- HNVW I, proof of Lemma 5.3.23: the bound of `w'`, with the constant `π²` (the book has `2π`; as
`0 ≤ t cos t / sin t ≤ 1`, the bound is elementary, and it is enough). -/
private theorem abs_haarWeightDeriv_le {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1) :
    |haarWeightDeriv s| ≤ Real.pi ^ 2 := by
  have hpi := Real.pi_pos
  have hsin := sin_half_pos hs
  have ht1 : Real.pi / 4 ≤ Real.pi * s / 2 := by nlinarith [hs.1]
  have ht2 : Real.pi * s / 2 ≤ Real.pi / 2 := by nlinarith [hs.2]
  rw [haarWeightDeriv]
  set t := Real.pi * s / 2
  have ht : 0 < t := by linarith
  have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht2⟩
  have h1 : t * Real.cos t ≤ Real.sin t := by
    rcases ht2.lt_or_eq with h | h
    · have h' := Real.le_tan ht.le h
      have hcos' : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
      rwa [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos'] at h'
    · rw [h, Real.cos_pi_div_two, mul_zero]
      exact (Real.sin_pi_div_two.trans_ge zero_le_one)
  have h2 : 0 ≤ t * Real.cos t / Real.sin t := by positivity
  have h3 : t * Real.cos t / Real.sin t ≤ 1 := (div_le_one hsin).2 h1
  have h4 : |1 - 2 * (t * Real.cos t / Real.sin t)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_mul, abs_of_pos hpi, abs_of_nonneg (by positivity)]
  calc Real.pi * (t / Real.sin t ^ 4) * |1 - 2 * (t * Real.cos t / Real.sin t)|
      ≤ Real.pi * Real.pi * 1 := by
        gcongr
        exact div_sin_pow_le ht1 ht2
    _ = Real.pi ^ 2 := by ring

private theorem haarWeight_half_le : |haarWeight (1 / 2)| ≤ Real.pi ^ 2 / 4 := by
  have hpi := Real.pi_pos
  have hsin := sin_half_pos (s := 1 / 2) (by norm_num)
  rw [haarWeight, abs_of_nonneg (by positivity)]
  have h := div_sin_pow_le (t := Real.pi * (1 / 2) / 2) (by linarith) (by linarith)
  rw [sq, mul_div_assoc]
  calc Real.pi * (1 / 2) / 2 * (Real.pi * (1 / 2) / 2 / Real.sin (Real.pi * (1 / 2) / 2) ^ 4)
      ≤ Real.pi * (1 / 2) / 2 * Real.pi := by gcongr
    _ = Real.pi ^ 2 / 4 := by ring

private theorem integrableOn_haarWeightDeriv :
    IntegrableOn haarWeightDeriv (Set.Ioc (1 / 2) 1) :=
  IntegrableOn.of_bound (by simp) measurable_haarWeightDeriv.aestronglyMeasurable (Real.pi ^ 2)
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun _ hs =>
      abs_haarWeightDeriv_le (Set.Ioc_subset_Icc_self hs)))

/-- The fundamental theorem of calculus for `w`. -/
private theorem setIntegral_haarWeightDeriv {σ : ℝ} (hσ : σ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∫ s in Set.Ioo (1 / 2) σ, haarWeightDeriv s = haarWeight σ - haarWeight (1 / 2) := by
  have hsub : Set.Ioc (1 / 2) σ ⊆ Set.Ioc (1 / 2 : ℝ) 1 := Set.Ioc_subset_Ioc_right hσ.2.le
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hσ.1.le]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => ?_) ?_
  · rw [Set.uIcc_of_le hσ.1.le] at hs
    exact hasDerivAt_haarWeight ⟨hs.1, hs.2.trans hσ.2.le⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hσ.1.le]
    exact integrableOn_haarWeightDeriv.mono_set hsub

/-! ### Interval multipliers -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The character `e_a (x) = e^{2πi a x}` of the line. -/
noncomputable def expChar (a x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (a * x) : ℝ) : ℂ) * Complex.I)

/-- The characters `e_a` have modulus `1`. -/
theorem norm_expChar (a x : ℝ) : ‖expChar a x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The characters `e_a` are continuous. -/
theorem continuous_expChar (a : ℝ) : Continuous (expChar a) := by
  unfold expChar
  fun_prop

private theorem expChar_add_left (a b x : ℝ) : expChar (a + b) x = expChar a x * expChar b x := by
  rw [expChar, expChar, expChar, ← Complex.exp_add]
  push_cast
  ring_nf

private theorem expChar_comm (a x : ℝ) : expChar a x = expChar x a := by
  rw [expChar, expChar, mul_comm a]

/-- The inverse Fourier transform `𝓕⁻ G (x) = ∫ e_v (x) G (v) dv`. -/
theorem fourierInv_eq_expChar (G : ℝ → X) (x : ℝ) :
    𝓕⁻ G x = ∫ v, expChar v x • G v := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp [expChar, mul_comm]

/-- HNVW I, (5.35), p. 404, for the modulations: `(G (· + a))ˇ = e_{−a} Ǧ`. -/
theorem fourierInv_smul_expChar (a : ℝ) (G : ℝ → X) (x : ℝ) :
    𝓕⁻ (fun ξ => G (ξ + a)) x = expChar (-a) x • 𝓕⁻ G x := by
  rw [fourierInv_eq_expChar, fourierInv_eq_expChar, ← integral_smul,
    ← integral_add_right_eq_self (fun v => expChar (-a) x • expChar v x • G v) a]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [smul_smul, ← expChar_add_left]
  rw [neg_add_eq_sub, add_sub_cancel_right]

/-- The integrand `e_v (x) G (v)` of `𝓕⁻ G (x)` is integrable. -/
theorem integrable_expChar_smul {G : ℝ → X} (hG : Integrable G) (x : ℝ) :
    Integrable fun v => expChar v x • G v :=
  hG.bdd_smul 1 (by simpa only [expChar_comm] using
    (continuous_expChar x).aestronglyMeasurable) (ae_of_all _ fun v => (norm_expChar v x).le)

/-- `𝓕⁻` is linear. -/
theorem fourierInv_const_smul (c : ℂ) (G : ℝ → X) (x : ℝ) :
    𝓕⁻ (fun ξ => c • G ξ) x = c • 𝓕⁻ G x := by
  rw [fourierInv_eq_expChar, fourierInv_eq_expChar, ← integral_smul]
  exact integral_congr_ae (ae_of_all _ fun ξ => smul_comm _ _ _)

/-- `𝓕⁻` is linear: sums with real coefficients. -/
theorem fourierInv_sum_smul {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (c : Fin K → ℝ) (x : ℝ) :
    𝓕⁻ (fun ξ => ∑ k, c k • G k ξ) x = ∑ k, c k • 𝓕⁻ (G k) x := by
  simp only [fourierInv_eq_expChar]
  simp_rw [← integral_smul, Finset.smul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => integral_congr_ae (ae_of_all _ fun v => smul_comm _ _ _)
  · intro k _
    exact integrable_expChar_smul ((hG k).smul (c k)) x

/-- `∫ K (s) e_v (x − s) ds = e_v (x) 𝓕 K (v)`. -/
private theorem integral_mul_expChar_sub (K : ℝ → ℂ) (x v : ℝ) :
    ∫ s, K s * expChar v (x - s) = expChar v x * 𝓕 K v := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [smul_eq_mul, expChar]
  rw [← mul_assoc (Complex.exp _), ← Complex.exp_add, mul_comm]
  push_cast
  ring_nf

/-- The convolution `K * 𝓕⁻ H`, with `K, H ∈ L¹`, as a Fourier multiplier: HNVW I, Lemma 2.4.8
(p. 109), in this setting. -/
theorem integral_smul_fourierInv_sub {K : ℝ → ℂ} (hK : Integrable K) {H : ℝ → X}
    (hH : Integrable H) (x : ℝ) :
    ∫ s, K s • 𝓕⁻ H (x - s) = 𝓕⁻ (fun ξ => 𝓕 K ξ • H ξ) x := by
  by_cases hX : CompleteSpace X
  swap
  · simp [Real.fourierInv_eq', integral, hX]
  have hint : Integrable (Function.uncurry fun s v : ℝ => (K s * expChar v (x - s)) • H v)
      (volume.prod volume) := by
    have h := (hK.smul_prod hH).bdd_smul 1 (φ := fun p : ℝ × ℝ => expChar p.2 (x - p.1))
      (by unfold expChar; fun_prop : Continuous fun p : ℝ × ℝ =>
        expChar p.2 (x - p.1)).aestronglyMeasurable
      (ae_of_all _ fun p => (norm_expChar _ _).le)
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [Pi.smul_apply', Function.uncurry, smul_smul]
    rw [mul_comm]
  have h1 : ∫ s, K s • 𝓕⁻ H (x - s) = ∫ s, ∫ v, (K s * expChar v (x - s)) • H v := by
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only
    rw [fourierInv_eq_expChar, ← integral_smul]
    simp only [smul_smul]
  rw [h1, integral_integral_swap hint, fourierInv_eq_expChar]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [integral_smul_const, integral_mul_expChar_sub, mul_smul]

/-- The Fourier transform of `φ_t`. -/
private theorem fourier_dilate (φ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun z : ℝ => ((t⁻¹ * φ (t⁻¹ * z) : ℝ) : ℂ)) ξ =
      𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) (t * ξ) := by
  have h := Measure.integral_comp_inv_mul_left (fun y : ℝ =>
    Complex.exp (((-2 * Real.pi * y * (t * ξ) : ℝ) : ℂ) * Complex.I) • ((φ y : ℝ) : ℂ)) t
  rw [abs_of_pos ht] at h
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← inv_smul_smul₀ ht.ne' (∫ v, _ • ((φ v : ℝ) : ℂ)), ← h, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul, Complex.real_smul]
  rw [show -2 * Real.pi * (t⁻¹ * z) * (t * ξ) = -2 * Real.pi * z * ξ by field_simp]
  push_cast
  ring

/-- The convolution `φ_t * 𝓕⁻ G`, with `φ, G ∈ L¹`, as a Fourier multiplier. -/
theorem dilateConv_fourierInv {φ : ℝ → ℝ} (hφ : Integrable φ) {t : ℝ} (ht : 0 < t) {G : ℝ → X}
    (hG : Integrable G) :
    dilateConv φ t (𝓕⁻ G) = 𝓕⁻ fun ξ => 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) (t * ξ) • G ξ := by
  funext x
  have hφt : Integrable fun z : ℝ => ((t⁻¹ * φ (t⁻¹ * z) : ℝ) : ℂ) :=
    ((hφ.comp_mul_left' (inv_ne_zero ht.ne')).const_mul t⁻¹).ofReal
  have h := integral_smul_fourierInv_sub hφt hG x
  simp only [fourier_dilate φ ht, Complex.coe_smul] at h
  rw [dilateConv_eq_integral_sub, h]

/-- `sign · G`, the Hilbert transform on the Fourier side, is integrable. -/
theorem integrable_sign_smul {G : ℝ → X} (hG : Integrable G) :
    Integrable fun ξ => (Real.sign ξ : ℂ) • G ξ :=
  hG.bdd_smul 1 (Complex.measurable_ofReal.comp measurable_realSign).aestronglyMeasurable
    (ae_of_all _ fun ξ => by rcases Real.sign_apply_eq ξ with h | h | h <;> simp [h])

private theorem integrable_sign_sub_smul {G : ℝ → X} (hG : Integrable G) (a : ℝ) :
    Integrable fun ξ => (Real.sign (ξ - a) : ℂ) • G ξ := by
  simpa using (integrable_sign_smul (hG.comp_add_right a)).comp_sub_right a

/-- HNVW I, Lemma 5.3.9, p. 404: `Δ_{(a,b)} = ½ (T_{sgn (· − a)} − T_{sgn (· − b)})`. -/
private theorem fourierInv_indicator_Ioo {G : ℝ → X} (hG : Integrable G) {a b : ℝ} (hab : a ≤ b)
    (x : ℝ) : 𝓕⁻ ((Set.Ioo a b).indicator G) x =
      (1 / 2 : ℝ) • 𝓕⁻ (fun ξ => (Real.sign (ξ - a) : ℂ) • G ξ) x +
        (-1 / 2 : ℝ) • 𝓕⁻ (fun ξ => (Real.sign (ξ - b) : ℂ) • G ξ) x := by
  simp only [fourierInv_eq_expChar]
  rw [← integral_smul, ← integral_smul]
  refine Eq.trans (integral_congr_ae ?_) (integral_add
    ((integrable_expChar_smul (integrable_sign_sub_smul hG a) x).smul (1 / 2 : ℝ))
    ((integrable_expChar_smul (integrable_sign_sub_smul hG b) x).smul (-1 / 2 : ℝ)))
  filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume b] with ξ ha hb
  rcases lt_or_gt_of_ne ha with h1 | h1
  · have h2 : ξ < b := h1.trans_le hab
    rw [Set.indicator_of_notMem (fun h => by linarith [h.1]), Real.sign_of_neg (by linarith),
      Real.sign_of_neg (by linarith), ← add_smul]
    norm_num
  · rcases lt_or_gt_of_ne hb with h2 | h2
    · rw [Set.indicator_of_mem (Set.mem_Ioo.2 ⟨h1, h2⟩), Real.sign_of_pos (by linarith),
        Real.sign_of_neg (by linarith)]
      simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_smul, smul_neg, neg_div]
      rw [neg_neg, ← add_smul]
      norm_num
    · rw [Set.indicator_of_notMem (fun h => by linarith [h.2]), Real.sign_of_pos (by linarith),
        Real.sign_of_pos (by linarith), ← add_smul]
      norm_num

/-- The modulations of the functions in `L^p` are in `L^p`. -/
theorem memLp_expChar_smul {p : ℝ≥0∞} {f : ℝ → X} (hf : MemLp f p volume) (a : ℝ) :
    MemLp (fun x => expChar a x • f x) p volume :=
  hf.of_le ((continuous_expChar a).aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by rw [norm_smul, norm_expChar, one_mul])

/-- HNVW I, (5.35), p. 404, with a factor `s`: `T_{s sgn (· − a)} f = s e_a T_{sgn} (e_{−a} f)`,
where `G (· + a)` is the Fourier transform of `e_{−a} f`. -/
theorem fourierInv_sign_sub (s a : ℝ) (G : ℝ → X) :
    (𝓕⁻ fun ξ => ((s * Real.sign (ξ - a) : ℝ) : ℂ) • G ξ) =
      fun x => ((s : ℂ) * expChar a x) • 𝓕⁻ (fun ξ => (Real.sign ξ : ℂ) • G (ξ + a)) x := by
  funext x
  have h := fourierInv_smul_expChar (-a) (fun ξ => (Real.sign ξ : ℂ) • G (ξ + a)) x
  simp only [neg_neg, ← sub_eq_add_neg, sub_add_cancel] at h
  rw [mul_smul, ← h, ← fourierInv_const_smul]
  simp only [Complex.ofReal_mul, mul_smul]

/-- HNVW I, (5.35), p. 404: `T_{sgn (· − a)} f = e_a T_{sgn} (e_{−a} f)`. -/
private theorem fourierInv_sign_sub_one (a : ℝ) (G : ℝ → X) :
    (𝓕⁻ fun ξ => (Real.sign (ξ - a) : ℂ) • G ξ) =
      fun x => expChar a x • 𝓕⁻ (fun ξ => (Real.sign ξ : ℂ) • G (ξ + a)) x := by
  simpa using fourierInv_sign_sub 1 a G

variable [CompleteSpace X]

omit [CompleteSpace X] in
/-- The randomised bound for the Hilbert transform, with the bound `B` for each choice of signs. -/
theorem eLpNormRad_fourierInv_sign_le {p : ℝ} (hp : 1 < p) {B : ℝ≥0∞}
    (hB : ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        B * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume)
    {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) :
    eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G k ξ) p volume ≤
      B * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  have hsG := fun k => integrable_sign_smul (hG k)
  refine eLpNormRad_le_of_forall (by linarith)
    (fun k => (continuous_fourierInv_of_integrable (hsG k)).aestronglyMeasurable)
    (fun k => (continuous_fourierInv_of_integrable (hG k)).aestronglyMeasurable) fun ε => ?_
  have h1 : (fun x => ∑ k, SignCube.coin (ε k) • 𝓕⁻ (fun ξ => (Real.sign ξ : ℂ) • G k ξ) x) =
      𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • ∑ k, SignCube.coin (ε k) • G k ξ := by
    funext x
    rw [← fourierInv_sum_smul hsG]
    simp only [Finset.smul_sum, smul_comm (_ : ℂ) (_ : ℝ)]
  have h2 : (fun x => ∑ k, SignCube.coin (ε k) • 𝓕⁻ (G k) x) =
      𝓕⁻ fun ξ => ∑ k, SignCube.coin (ε k) • G k ξ :=
    funext fun x => (fourierInv_sum_smul hG _ x).symm
  rw [h1, h2]
  refine hB _ (integrable_finsetSum _ fun k _ => (hG k).smul (SignCube.coin (ε k))) ?_
  rw [← h2]
  exact memLp_finsetSum _ fun k _ => (hf k).const_smul _

/-- The randomised bound for the modulated Hilbert transforms (HNVW I, p. 414, with (5.35), p. 404):
the bound for the Hilbert transform, and the contraction principle for the modulations. -/
private theorem eLpNormRad_fourierInv_sign_sub_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) (a : Fin K → ℝ) :
    eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign (ξ - a k) : ℂ) • G k ξ) p volume ≤
      4 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  set G' : Fin K → ℝ → X := fun k ξ => G k (ξ + a k)
  have hG' : ∀ k, Integrable (G' k) := fun k => (hG k).comp_add_right (a k)
  have hinv : ∀ k, 𝓕⁻ (G' k) = fun x => expChar (-a k) x • 𝓕⁻ (G k) x := fun k =>
    funext fun x => fourierInv_smul_expChar (a k) (G k) x
  have hcont := fun k => continuous_fourierInv_of_integrable (integrable_sign_smul (hG' k))
  -- the modulations on the left
  simp only [fourierInv_sign_sub_one]
  refine (eLpNormRad_smul_le hp.le (c := fun k => expChar (a k))
    (f := fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ) (fun k x => (norm_expChar _ _).le)
    (fun k => (continuous_expChar _).aestronglyMeasurable)
    fun k => (hcont k).aestronglyMeasurable).trans ?_
  -- the Hilbert transform
  have h1 : eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ) p volume ≤
      dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G' k)) p volume :=
    eLpNormRad_fourierInv_sign_le hp (fun _ => eLpNorm_fourierInv_sign_le_dyadic hp hβ) hG'
      fun k => by
        rw [hinv]
        exact memLp_expChar_smul (hf k) _
  -- the modulations on the right
  have h2 : eLpNormRad (fun k => 𝓕⁻ (G' k)) p volume ≤
      2 * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
    simp only [hinv]
    exact eLpNormRad_smul_le hp.le (c := fun k => expChar (-a k)) (fun k x => (norm_expChar _ _).le)
      (fun k => (continuous_expChar _).aestronglyMeasurable) fun k => (hf k).aestronglyMeasurable
  calc 2 * eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ) p volume
      ≤ 2 * (dyadicHilbertBound β * (2 * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume)) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = 4 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by ring

/-- `|± 1/2| = 1/2`, in `[0, ∞]`. -/
theorem enorm_half {𝕜 : Type*} [RCLike 𝕜] {c : 𝕜} (hc : c = 1 / 2 ∨ c = -1 / 2) : ‖c‖ₑ = 2⁻¹ := by
  have h : ‖(1 / 2 : 𝕜)‖ₑ = 2⁻¹ := by
    rw [one_div, enorm_inv two_ne_zero, ← ofReal_norm, RCLike.norm_ofNat, ENNReal.ofReal_ofNat]
  rcases hc with rfl | rfl
  · exact h
  · rw [neg_div, enorm_neg, h]

/-- HNVW I, proof of Lemma 5.3.21, p. 414, with Lemma 5.3.9, p. 404: the randomised bound for
intervals, from the Hilbert transform. For any `a_k ≤ b_k`,
`‖Σ ε_k Δ_{(a_k, b_k)} f_k‖ ≤ 4 ħ ‖Σ ε_k f_k‖`, the factor `4` being two applications of the
contraction principle with the factor `2` (real signs; the book has complex ones). -/
theorem eLpNormRad_fourierInv_Ioo_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) {a b : Fin K → ℝ}
    (hab : ∀ k, a k ≤ b k) :
    eLpNormRad (fun k => 𝓕⁻ ((Set.Ioo (a k) (b k)).indicator (G k))) p volume ≤
      4 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  have hcont : ∀ (c : Fin K → ℝ) k,
      Continuous (𝓕⁻ fun ξ => (Real.sign (ξ - c k) : ℂ) • G k ξ) := fun c k =>
    continuous_fourierInv_of_integrable (integrable_sign_sub_smul (hG k) (c k))
  have h1 : (fun k => 𝓕⁻ ((Set.Ioo (a k) (b k)).indicator (G k))) =
      fun k x => (1 / 2 : ℝ) • 𝓕⁻ (fun ξ => (Real.sign (ξ - a k) : ℂ) • G k ξ) x +
        (-1 / 2 : ℝ) • 𝓕⁻ (fun ξ => (Real.sign (ξ - b k) : ℂ) • G k ξ) x :=
    funext fun k => funext fun x => fourierInv_indicator_Ioo (hG k) (hab k) x
  rw [h1]
  refine (eLpNormRad_add_le hp.le
    (f := fun k x => (1 / 2 : ℝ) • 𝓕⁻ (fun ξ => (Real.sign (ξ - a k) : ℂ) • G k ξ) x)
    (g := fun k x => (-1 / 2 : ℝ) • 𝓕⁻ (fun ξ => (Real.sign (ξ - b k) : ℂ) • G k ξ) x)
    (fun k => ((hcont a k).const_smul _).aestronglyMeasurable)
    fun k => ((hcont b k).const_smul _).aestronglyMeasurable).trans ?_
  rw [eLpNormRad_fun_const_smul (1 / 2 : ℝ)
      (fun k => 𝓕⁻ fun ξ => (Real.sign (ξ - a k) : ℂ) • G k ξ),
    eLpNormRad_fun_const_smul (-1 / 2 : ℝ)
      (fun k => 𝓕⁻ fun ξ => (Real.sign (ξ - b k) : ℂ) • G k ξ),
    enorm_half (Or.inl rfl), enorm_half (Or.inr rfl)]
  set R := 4 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume
  calc _ ≤ (2⁻¹ : ℝ≥0∞) * R + 2⁻¹ * R := by
        gcongr
        · exact eLpNormRad_fourierInv_sign_sub_le hp hβ hG hf a
        · exact eLpNormRad_fourierInv_sign_sub_le hp hβ hG hf b
    _ = R := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-! ### The multipliers `1_{I_k} / φ̂ (2^{−k−1} ·)` -/

omit [CompleteSpace X] in
private theorem fourier_inv_eq_haarWeight {σ : ℝ} (hσ : σ ≠ 0) (y : X) :
    (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) σ)⁻¹ • y = haarWeight σ • y := by
  rw [fourier_haarCorrelation_haar hσ, ← Complex.ofReal_inv, inv_div, Complex.coe_smul, haarWeight]

/-- HNVW I, (5.36), after the change of variable: for `I = (T/2, T)`,
`1_I (ξ) w (ξ/T) = w (1/2) 1_I (ξ) + ∫_{1/2}^1 w' (s) 1_{(sT, T)} (ξ) ds`. -/
private theorem indicator_div_eq {T : ℝ} (hT : 0 < T) (G : ℝ → X) (ξ : ℝ) :
    (Set.Ioo (T / 2) T).indicator (fun ξ =>
        (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) (T⁻¹ * ξ))⁻¹ • G ξ) ξ =
      haarWeight (1 / 2) • (Set.Ioo (T / 2) T).indicator G ξ +
        ∫ s in Set.Ioc (1 / 2 : ℝ) 1, haarWeightDeriv s • (Set.Ioo (T * s) T).indicator G ξ := by
  by_cases hξ : ξ ∈ Set.Ioo (T / 2) T
  · set σ := T⁻¹ * ξ with hσdef
    have hσξ : ξ = T * σ := by rw [hσdef, mul_inv_cancel_left₀ hT.ne']
    have hσ : σ ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
      rw [hσξ] at hξ
      exact ⟨by nlinarith [hξ.1], by nlinarith [hξ.2]⟩
    have h1 : ∫ s in Set.Ioc (1 / 2 : ℝ) 1, haarWeightDeriv s • (Set.Ioo (T * s) T).indicator G ξ =
        ∫ s in Set.Ioc (1 / 2 : ℝ) 1, (Set.Iio σ).indicator haarWeightDeriv s • G ξ := by
      refine integral_congr_ae (ae_of_all _ fun s => ?_)
      by_cases hs : s < σ
      · have hmem : ξ ∈ Set.Ioo (T * s) T := ⟨by rw [hσξ]; gcongr, hξ.2⟩
        simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Iio.2 hs)]
      · have hmem : ξ ∉ Set.Ioo (T * s) T := fun h => by
          have h' := h.1
          rw [hσξ] at h'
          exact hs (lt_of_mul_lt_mul_left h' hT.le)
        simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (s := Set.Iio σ) hs,
          smul_zero, zero_smul]
    have h2 : Set.Ioc (1 / 2 : ℝ) 1 ∩ Set.Iio σ = Set.Ioo (1 / 2) σ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (h.2.trans hσ.2).le⟩, h.2⟩⟩
    rw [h1, integral_smul_const, setIntegral_indicator measurableSet_Iio, h2,
      setIntegral_haarWeightDeriv hσ, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ,
      fourier_inv_eq_haarWeight (by linarith [hσ.1]), ← add_smul, add_sub_cancel]
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, smul_zero, zero_add]
    refine (setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_).symm
    rw [Set.indicator_of_notMem, smul_zero]
    exact fun h => hξ ⟨by nlinarith [h.1, hs.1], h.2⟩

omit [CompleteSpace X] in
/-- The integrability for Fubini's theorem. -/
private theorem integrable_haarWeightDeriv_smul {G : ℝ → X} (hG : Integrable G) (T x : ℝ) :
    Integrable (Function.uncurry fun v s : ℝ =>
      expChar v x • haarWeightDeriv s • (Set.Ioo (T * s) T).indicator G v)
      (volume.prod (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) := by
  have h1 : Integrable (fun p : ℝ × ℝ => haarWeightDeriv p.1 • G p.2)
      ((volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)).prod volume) :=
    Integrable.smul_prod integrableOn_haarWeightDeriv hG
  have hS : MeasurableSet {p : ℝ × ℝ | T * p.1 < p.2 ∧ p.2 < T} :=
    (measurableSet_lt (measurable_fst.const_mul T) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)
  have h2 := (h1.indicator hS).bdd_smul 1 (φ := fun p : ℝ × ℝ => expChar p.2 x)
    (by unfold expChar; fun_prop : Continuous fun p : ℝ × ℝ => expChar p.2 x).aestronglyMeasurable
    (ae_of_all _ fun p => (norm_expChar _ _).le)
  refine h2.swap.congr (ae_of_all _ fun p => ?_)
  simp only [Function.comp_apply, Pi.smul_apply', Function.uncurry, Prod.snd_swap]
  by_cases h : T * p.2 < p.1 ∧ p.1 < T
  · rw [Set.indicator_of_mem (by exact h), Set.indicator_of_mem (by exact h)]
    rfl
  · rw [Set.indicator_of_notMem (by exact h), Set.indicator_of_notMem (by exact h), smul_zero,
      smul_zero, smul_zero]

omit [CompleteSpace X] in
private theorem integral_expChar_haarWeightDeriv_smul (G : ℝ → X) (T x s : ℝ) :
    ∫ v, expChar v x • haarWeightDeriv s • (Set.Ioo (T * s) T).indicator G v =
      haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T * s) T).indicator G) x := by
  rw [fourierInv_eq_expChar, ← integral_smul]
  exact integral_congr_ae (ae_of_all _ fun v => smul_comm _ _ _)

/-- The operator form of (5.36) (HNVW I, p. 413), by Fubini's theorem. -/
private theorem fourierInv_div_eq {G : ℝ → X} (hG : Integrable G) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    𝓕⁻ ((Set.Ioo (T / 2) T).indicator fun ξ =>
        (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) (T⁻¹ * ξ))⁻¹ • G ξ) x =
      haarWeight (1 / 2) • 𝓕⁻ ((Set.Ioo (T / 2) T).indicator G) x +
        ∫ s in Set.Ioc (1 / 2 : ℝ) 1,
          haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T * s) T).indicator G) x := by
  have hint := integrable_haarWeightDeriv_smul hG T x
  have h1 : ∫ s in Set.Ioc (1 / 2 : ℝ) 1,
      haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T * s) T).indicator G) x =
      ∫ v, ∫ s in Set.Ioc (1 / 2 : ℝ) 1,
        expChar v x • haarWeightDeriv s • (Set.Ioo (T * s) T).indicator G v := by
    rw [integral_integral_swap hint]
    simp only [integral_expChar_haarWeightDeriv_smul]
  rw [h1, fourierInv_eq_expChar, fourierInv_eq_expChar, ← integral_smul]
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun v => ?_)) (integral_add
    ((integrable_expChar_smul (hG.indicator measurableSet_Ioo) x).smul (haarWeight (1 / 2)))
    hint.integral_prod_left)
  simp only
  rw [indicator_div_eq hT, smul_add, integral_smul]
  congr 1
  exact smul_comm _ _ _

omit [CompleteSpace X] in
private theorem stronglyMeasurable_fourierInv_Ioo {G : ℝ → X} (hG : StronglyMeasurable G) (T : ℝ) :
    StronglyMeasurable (Function.uncurry fun s x : ℝ =>
      haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T * s) T).indicator G) x) := by
  have hS : MeasurableSet {q : (ℝ × ℝ) × ℝ | T * q.1.1 < q.2 ∧ q.2 < T} :=
    (measurableSet_lt (measurable_fst.fst.const_mul T) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)
  have hc : Continuous fun q : (ℝ × ℝ) × ℝ => expChar q.2 q.1.2 := by
    unfold expChar
    fun_prop
  have h1 : StronglyMeasurable fun z : ℝ × ℝ => ∫ v, expChar v z.2 •
      {q : (ℝ × ℝ) × ℝ | T * q.1.1 < q.2 ∧ q.2 < T}.indicator (fun q => G q.2) (z, v) :=
    StronglyMeasurable.integral_prod_right' (f := fun q : (ℝ × ℝ) × ℝ => expChar q.2 q.1.2 •
      {q : (ℝ × ℝ) × ℝ | T * q.1.1 < q.2 ∧ q.2 < T}.indicator (fun q => G q.2) q)
      (hc.stronglyMeasurable.smul ((hG.comp_measurable measurable_snd).indicator hS))
  have h2 : (Function.uncurry fun s x : ℝ =>
      haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T * s) T).indicator G) x) =
      fun z : ℝ × ℝ => haarWeightDeriv z.1 • ∫ v, expChar v z.2 •
        {q : (ℝ × ℝ) × ℝ | T * q.1.1 < q.2 ∧ q.2 < T}.indicator (fun q => G q.2) (z, v) := by
    funext z
    simp only [Function.uncurry, fourierInv_eq_expChar]
    rfl
  rw [h2]
  exact (measurable_haarWeightDeriv.comp measurable_fst).stronglyMeasurable.smul h1

/-- `w (1/2) + ∫_{1/2}^1 |w'| ≤ 3π²/4 ≤ 9`. -/
private theorem haarWeight_total_le :
    ‖haarWeight (1 / 2)‖ₑ + ∫⁻ s in Set.Ioc (1 / 2 : ℝ) 1, ‖haarWeightDeriv s‖ₑ ≤ 9 := by
  have hpi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2]
  have h1 : ‖haarWeight (1 / 2)‖ₑ ≤ ENNReal.ofReal (Real.pi ^ 2 / 4) := by
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal haarWeight_half_le
  have h2 : ∫⁻ s in Set.Ioc (1 / 2 : ℝ) 1, ‖haarWeightDeriv s‖ₑ ≤
      ENNReal.ofReal (Real.pi ^ 2 / 2) := by
    calc ∫⁻ s in Set.Ioc (1 / 2 : ℝ) 1, ‖haarWeightDeriv s‖ₑ
        ≤ ∫⁻ _s in Set.Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (Real.pi ^ 2) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
            (ae_of_all _ fun s hs => ?_))
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (abs_haarWeightDeriv_le (Set.Ioc_subset_Icc_self hs))
      _ = ENNReal.ofReal (Real.pi ^ 2 / 2) := by
          rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  calc _ ≤ ENNReal.ofReal (Real.pi ^ 2 / 4) + ENNReal.ofReal (Real.pi ^ 2 / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal (Real.pi ^ 2 / 4 + Real.pi ^ 2 / 2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ 9 := by
        rw [← ENNReal.ofReal_ofNat]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- HNVW I, (5.37): the randomised bound for strongly measurable `G_k`, by Minkowski's inequality
and the bound for the intervals. -/
private theorem eLpNormRad_fourierInv_div_le_of_stronglyMeasurable {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hGm : ∀ k, StronglyMeasurable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) {T : Fin K → ℝ} (hT : ∀ k, 0 < T k) :
    eLpNormRad (fun k => 𝓕⁻ ((Set.Ioo (T k / 2) (T k)).indicator fun ξ =>
        (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ((T k)⁻¹ * ξ))⁻¹ • G k ξ)) p volume ≤
      36 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  set R := 4 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume with hR
  have hFm := fun k => stronglyMeasurable_fourierInv_Ioo (hGm k) (T k)
  have h1 : (fun k => 𝓕⁻ ((Set.Ioo (T k / 2) (T k)).indicator fun ξ =>
      (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ((T k)⁻¹ * ξ))⁻¹ • G k ξ)) =
      fun k x => haarWeight (1 / 2) • 𝓕⁻ ((Set.Ioo (T k / 2) (T k)).indicator (G k)) x +
        ∫ s in Set.Ioc (1 / 2 : ℝ) 1,
          haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T k * s) (T k)).indicator (G k)) x :=
    funext fun k => funext fun x => fourierInv_div_eq (hG k) (hT k) x
  -- the integrability in `s`, from Fubini's theorem
  have hFi : ∀ k x, Integrable (fun s => haarWeightDeriv s •
      𝓕⁻ ((Set.Ioo (T k * s) (T k)).indicator (G k)) x)
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := fun k x =>
    (integrable_haarWeightDeriv_smul (hG k) (T k) x).integral_prod_right.congr
      (ae_of_all _ (integral_expChar_haarWeightDeriv_smul (G k) (T k) x))
  have h2 : eLpNormRad (fun k x => haarWeight (1 / 2) •
      𝓕⁻ ((Set.Ioo (T k / 2) (T k)).indicator (G k)) x) p volume ≤
      ‖haarWeight (1 / 2)‖ₑ * R := by
    rw [eLpNormRad_fun_const_smul (haarWeight (1 / 2))
      (fun k => 𝓕⁻ ((Set.Ioo (T k / 2) (T k)).indicator (G k)))]
    gcongr
    exact eLpNormRad_fourierInv_Ioo_le hp hβ hG hf fun k => by linarith [hT k]
  have h3 : eLpNormRad (fun k x => ∫ s in Set.Ioc (1 / 2 : ℝ) 1,
      haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T k * s) (T k)).indicator (G k)) x) p volume ≤
      (∫⁻ s in Set.Ioc (1 / 2 : ℝ) 1, ‖haarWeightDeriv s‖ₑ) * R := by
    refine (eLpNormRad_integral_le hp.le (F := fun k s x => haarWeightDeriv s •
      𝓕⁻ ((Set.Ioo (T k * s) (T k)).indicator (G k)) x) hFm
      fun k => ae_of_all _ fun x => hFi k x).trans ?_
    rw [← lintegral_mul_const _ measurable_haarWeightDeriv.enorm]
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_))
    rw [eLpNormRad_fun_const_smul (haarWeightDeriv s)
      (fun k => 𝓕⁻ ((Set.Ioo (T k * s) (T k)).indicator (G k)))]
    gcongr
    exact eLpNormRad_fourierInv_Ioo_le hp hβ hG hf fun k => by nlinarith [hT k, hs.2]
  rw [h1]
  refine (eLpNormRad_add_le hp.le
    (f := fun k x => haarWeight (1 / 2) • 𝓕⁻ ((Set.Ioo (T k / 2) (T k)).indicator (G k)) x)
    (g := fun k x => ∫ s in Set.Ioc (1 / 2 : ℝ) 1,
      haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T k * s) (T k)).indicator (G k)) x)
    (fun k => ((continuous_fourierInv_of_integrable ((hG k).indicator
      measurableSet_Ioo)).const_smul _).aestronglyMeasurable)
    fun k => (hFm k).integral_prod_left.aestronglyMeasurable).trans ?_
  calc _ ≤ ‖haarWeight (1 / 2)‖ₑ * R +
        (∫⁻ s in Set.Ioc (1 / 2 : ℝ) 1, ‖haarWeightDeriv s‖ₑ) * R := add_le_add h2 h3
    _ ≤ 9 * R := by
        rw [← add_mul]
        gcongr
        exact haarWeight_total_le
    _ = 36 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
        rw [hR]
        ring

/-- HNVW I, Lemmas 5.3.21 and 5.3.23: the randomised bound for the multipliers
`1_{I_k} / φ̂ (2^{−k−1} ·)`. With `w = 1 / φ̂` on `[1/2, 1]`, the constant is
`4 ħ (w (1/2) + ∫_{1/2}^1 |w'|) ≤ 36 ħ`. -/
theorem eLpNormRad_fourierInv_div_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) :
    eLpNormRad (fun k => 𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator fun ξ =>
        (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ((2 ^ ((k : ℕ) + 1))⁻¹ * ξ))⁻¹ •
          G k ξ)) p volume ≤
      36 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  -- replace `G_k` by strongly measurable functions
  set g : Fin K → ℝ → X := fun k => (hG k).aestronglyMeasurable.mk (G k)
  have hgm : ∀ k, StronglyMeasurable (g k) := fun k =>
    (hG k).aestronglyMeasurable.stronglyMeasurable_mk
  have hGg : ∀ k, G k =ᵐ[volume] g k := fun k => (hG k).aestronglyMeasurable.ae_eq_mk
  have h1 : ∀ k, 𝓕⁻ (G k) = 𝓕⁻ (g k) := fun k =>
    funext fun x => Real.fourierInv_congr_ae (hGg k) x
  have h2 : ∀ k : Fin K, 𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator fun ξ =>
      (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ((2 ^ ((k : ℕ) + 1))⁻¹ * ξ))⁻¹ •
        G k ξ) =
      𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ ((k : ℕ) + 1) / 2) (2 ^ ((k : ℕ) + 1))).indicator fun ξ =>
        (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ((2 ^ ((k : ℕ) + 1))⁻¹ * ξ))⁻¹ •
          g k ξ) := fun k => by
    rw [pow_succ, mul_div_cancel_right₀ _ two_ne_zero]
    refine funext fun x => Real.fourierInv_congr_ae ?_ x
    filter_upwards [hGg k] with ξ hξ
    simp only [Set.indicator_apply, hξ]
  simp only [h1, h2] at hf ⊢
  exact eLpNormRad_fourierInv_div_le_of_stronglyMeasurable hp hβ
    (fun k => (hG k).congr (hGg k)) hgm hf fun k => by positivity

/-- The constant `72 ħ β` of the Littlewood–Paley inequality on the half-line,
`ħ = dyadicHilbertBound β` (the book has `36 ħ β` for the whole line, with complex signs). -/
noncomputable def littlewoodPaleyBound (β : ℝ≥0∞) : ℝ≥0∞ := 72 * dyadicHilbertBound β * β

omit [CompleteSpace X] in
/-- `1_I = (1_I / φ̂ (2^{−k−1} ·)) φ̂ (2^{−k−1} ·)` for `I = (2^k, 2^{k+1})`. -/
private theorem indicator_eq_indicator_div (k : ℕ) (G : ℝ → X) :
    (Set.Ioo ((2 : ℝ) ^ k) (2 ^ (k + 1))).indicator G =
      (Set.Ioo ((2 : ℝ) ^ k) (2 ^ (k + 1))).indicator fun ξ =>
        (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ((2 ^ (k + 1))⁻¹ * ξ))⁻¹ •
          𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ((2 ^ (k + 1))⁻¹ * ξ) • G ξ := by
  refine Set.indicator_congr fun ξ hξ => ?_
  have h0 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hσ : (2 ^ (k + 1))⁻¹ * ξ ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    rw [Set.mem_Icc, le_inv_mul_iff₀ h0, inv_mul_le_iff₀ h0, mul_one]
    exact ⟨by rw [pow_succ]; linarith [hξ.1], hξ.2.le⟩
  have hσ0 : 0 < (2 ^ (k + 1))⁻¹ * ξ := by linarith [hσ.1]
  have hsin := sin_half_pos hσ
  have hpi := Real.pi_pos
  rw [fourier_haarCorrelation_haar hσ0.ne', inv_smul_smul₀]
  rw [Complex.ofReal_ne_zero]
  positivity

/-- **The Littlewood–Paley inequality on the positive half-line** (HNVW I, Theorem 5.3.24,
right-hand inequality), for the intervals `(2^k, 2^{k+1})`, `0 ≤ k < K`. -/
theorem eLpNormRad_fourierInv_indicator_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) :
    eLpNormRad (fun k : Fin K =>
        𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator G)) p volume ≤
      littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set φ' : ℝ → ℂ := 𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ))
  have hfm : StronglyMeasurable (𝓕⁻ G) :=
    (continuous_fourierInv_of_integrable hG).stronglyMeasurable
  have hφ : Measurable (haarCorrelation haar) := measurable_haarCorrelation measurable_haar
  -- `φ_{2^{−k−1}} * f = 𝓕⁻ G_k`
  set H : Fin K → ℝ → X := fun k ξ => φ' ((2 ^ ((k : ℕ) + 1))⁻¹ * ξ) • G ξ
  have hφc : Continuous φ' := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) integrable_haarCorrelation.ofReal
  have hH : ∀ k, Integrable (H k) := fun k =>
    hG.bdd_smul (∫ x, ‖((haarCorrelation haar x : ℝ) : ℂ)‖)
      (hφc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun ξ => Real.norm_fourier_le_integral_norm _ _)
  have hconv : ∀ k, 𝓕⁻ (H k) =
      dilateConv (haarCorrelation haar) (((2 : ℝ) ^ ((k : ℕ) + 1))⁻¹) (𝓕⁻ G) := fun k =>
    (dilateConv_fourierInv integrable_haarCorrelation (by positivity) hG).symm
  have hHp : ∀ k, MemLp (𝓕⁻ (H k)) (ENNReal.ofReal p) volume := fun k => by
    rw [hconv]
    exact (eLpNorm_dilateConv_le hp.le hφ (by positivity) hfm.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top integrable_haarCorrelation.hasFiniteIntegral hf.eLpNorm_lt_top)
  -- `1_{I_k} = (1_{I_k} / φ̂ (2^{−k−1} ·)) φ̂ (2^{−k−1} ·)`
  simp only [indicator_eq_indicator_div _ G]
  refine (eLpNormRad_fourierInv_div_le hp hβ hH hHp).trans ?_
  -- Lemma 5.3.22 (Proposition 5.1.10)
  have h1 : eLpNormRad (fun k => 𝓕⁻ (H k)) p volume ≤
      2 * β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
    simp only [hconv]
    refine (eLpNormRad_comp_le hp.le (σ := Fin.succ) (Fin.succ_injective K)
      (f := fun j : Fin (K + 1) =>
        dilateConv (haarCorrelation haar) (((2 : ℝ) ^ (j : ℕ))⁻¹) (𝓕⁻ G)) fun j => ?_).trans
      (eLpNormRad_dilateConv_le hp hβ hf hfm (K + 1))
    exact (stronglyMeasurable_dilateConv hφ _ hfm.aestronglyMeasurable).aestronglyMeasurable
  calc 36 * dyadicHilbertBound β * eLpNormRad (fun k => 𝓕⁻ (H k)) p volume
      ≤ 36 * dyadicHilbertBound β * (2 * β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) := by gcongr
    _ = littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
        rw [littlewoodPaleyBound]
        ring

/-! ### The intervals `I_k`, `k ∈ ℤ` -/

/-- `I_0 = (−1, 1)`. -/
theorem lineBlock_zero : lineBlock 0 = Set.Ioo (-1) 1 := by
  simp [lineBlock]

/-- `I_{k+1} = (2^k, 2^{k+1})` for `k ≥ 0`. -/
theorem lineBlock_natCast_add_one (k : ℕ) :
    lineBlock ((k : ℤ) + 1) = Set.Ioo (2 ^ k) (2 ^ (k + 1)) := by
  have h : ((k : ℤ) + 1).natAbs = k + 1 := by omega
  rw [lineBlock, ite_eq_right (by omega), ite_eq_left (by omega), h, Nat.add_sub_cancel]

/-- `I_{−k} = −I_k`. -/
theorem mem_lineBlock_neg (k : ℤ) (ξ : ℝ) : ξ ∈ lineBlock (-k) ↔ -ξ ∈ lineBlock k := by
  rcases lt_trichotomy k 0 with h | rfl | h
  · rw [lineBlock, lineBlock, ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), Int.natAbs_neg, Set.mem_Ioo, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · rw [neg_zero, lineBlock_zero, Set.mem_Ioo, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · rw [lineBlock, lineBlock, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), Int.natAbs_neg, Set.mem_Ioo, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The intervals `I_k` are measurable. -/
theorem measurableSet_lineBlock (k : ℤ) : MeasurableSet (lineBlock k) := by
  unfold lineBlock
  split_ifs <;> exact measurableSet_Ioo

omit [CompleteSpace X] in
private theorem eLpNorm_expChar_smul (p : ℝ≥0∞) {f : ℝ → X} (hf : Continuous f) (a : ℝ) :
    eLpNorm (fun x => expChar a x • f x) p volume = eLpNorm f p volume := by
  refine eLpNorm_congr_norm_ae ((continuous_expChar a).smul hf).aestronglyMeasurable
    hf.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_smul, norm_expChar, one_mul]

/-- The modulated Hilbert transforms `T_{sgn (· − a)}` (HNVW I, (5.35), p. 404). -/
private theorem eLpNorm_fourierInv_sign_sub_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (a : ℝ) :
    eLpNorm (𝓕⁻ fun ξ => (Real.sign (ξ - a) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      dyadicHilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set G' : ℝ → X := fun ξ => G (ξ + a)
  have hG' : Integrable G' := hG.comp_add_right a
  have hinv : 𝓕⁻ G' = fun x => expChar (-a) x • 𝓕⁻ G x :=
    funext fun x => fourierInv_smul_expChar a G x
  have h1 : eLpNorm (𝓕⁻ G') (ENNReal.ofReal p) volume =
      eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
    rw [hinv]
    exact eLpNorm_expChar_smul _ (continuous_fourierInv_of_integrable hG) _
  rw [fourierInv_sign_sub_one, eLpNorm_expChar_smul _
    (continuous_fourierInv_of_integrable (integrable_sign_smul hG')), ← h1]
  refine eLpNorm_fourierInv_sign_le_dyadic hp hβ hG' ?_
  rw [hinv]
  exact memLp_expChar_smul hf _

/-- HNVW I, Proposition 5.3.10, (1) ⇒ (2) (p. 405): `‖Δ_{(a,b)} f‖_p ≤ ħ ‖f‖_p`, by Lemma 5.3.9. -/
theorem eLpNorm_fourierInv_Ioo_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {G : ℝ → X} (hG : Integrable G) (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) {a b : ℝ}
    (hab : a ≤ b) : eLpNorm (𝓕⁻ ((Set.Ioo a b).indicator G)) (ENNReal.ofReal p) volume ≤
      dyadicHilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set T : ℝ → ℝ → X := fun c => 𝓕⁻ fun ξ => (Real.sign (ξ - c) : ℂ) • G ξ
  set R := dyadicHilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume
  have h1 : 𝓕⁻ ((Set.Ioo a b).indicator G) = (1 / 2 : ℝ) • T a + (-1 / 2 : ℝ) • T b :=
    funext fun x => fourierInv_indicator_Ioo hG hab x
  rw [h1]
  refine (eLpNorm_add_le (ENNReal.one_le_ofReal.2 hp.le)).trans ?_
  rw [eLpNorm_const_smul, eLpNorm_const_smul, enorm_half (Or.inl rfl), enorm_half (Or.inr rfl)]
  calc _ ≤ (2⁻¹ : ℝ≥0∞) * R + 2⁻¹ * R := by
        gcongr
        · exact eLpNorm_fourierInv_sign_sub_le hp hβ hG hf a
        · exact eLpNorm_fourierInv_sign_sub_le hp hβ hG hf b
    _ = R := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

omit [CompleteSpace X] in
private theorem continuous_indicator_fourierInv_lineBlock {G : ℝ → X} (hG : Integrable G) {K : ℕ}
    (s : Set (Fin (2 * K + 1))) (i : Fin (2 * K + 1)) :
    Continuous (s.indicator (fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)) i) := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact continuous_fourierInv_of_integrable (hG.indicator (measurableSet_lineBlock _))
  · exact continuous_zero

/-- The positive intervals: an injection of the indices brings them to `(2^k, 2^{k+1})`, `k ≥ 0`.
-/
private theorem eLpNormRad_lineBlock_pos_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) :
    eLpNormRad ({i : Fin (2 * K + 1) | K < (i : ℕ)}.indicator
        fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)) p volume ≤
      littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set g : Fin (2 * K + 1) → ℝ → X := fun j =>
    𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ (j : ℕ)) (2 ^ ((j : ℕ) + 1))).indicator G)
  have hg : ∀ j, AEStronglyMeasurable (g j) volume := fun j =>
    (continuous_fourierInv_of_integrable (hG.indicator measurableSet_Ioo)).aestronglyMeasurable
  set σ : Fin (2 * K + 1) → Fin (2 * K + 1) := fun k =>
    if _h : K < (k : ℕ) then ⟨k - K - 1, by omega⟩ else ⟨(k : ℕ) + K, by omega⟩ with hσdef
  have hσ : Function.Injective σ := by
    intro a b hab
    simp only [hσdef] at hab
    split_ifs at hab <;> rw [Fin.mk.injEq] at hab <;> exact Fin.ext (by omega)
  have h : ({i : Fin (2 * K + 1) | K < (i : ℕ)}.indicator
      fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)) =
      {i : Fin (2 * K + 1) | K < (i : ℕ)}.indicator fun i => g (σ i) := by
    funext i
    by_cases hi : K < (i : ℕ)
    · rw [Set.indicator_of_mem (by exact hi), Set.indicator_of_mem (by exact hi)]
      have h1 : ((i : ℕ) : ℤ) - K = ((i - K - 1 : ℕ) : ℤ) + 1 := by omega
      simp only [g, hσdef, dite_eq_left hi]
      rw [h1, lineBlock_natCast_add_one]
    · rw [Set.indicator_of_notMem (by exact hi), Set.indicator_of_notMem (by exact hi)]
  rw [h]
  exact (eLpNormRad_indicator_le hp.le _ fun k => hg (σ k)).trans
    ((eLpNormRad_comp_le hp.le hσ hg).trans (eLpNormRad_fourierInv_indicator_le hp hβ hG hf _))

omit [CompleteSpace X] in
/-- Reflections of the line. -/
theorem fourierInv_comp_neg (F : ℝ → X) (x : ℝ) : 𝓕⁻ (fun ξ => F (-ξ)) x = 𝓕⁻ F (-x) :=
  Real.fourierInv_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) F x

omit [CompleteSpace X] in
/-- Reflections of the line preserve the norm of `𝓕⁻ G`. -/
theorem eLpNorm_fourierInv_comp_neg {G : ℝ → X} (hG : Integrable G) (P : ℝ≥0∞) :
    eLpNorm (𝓕⁻ fun ξ => G (-ξ)) P volume = eLpNorm (𝓕⁻ G) P volume := by
  rw [funext (fourierInv_comp_neg G)]
  exact eLpNorm_comp_measurePreserving
    (continuous_fourierInv_of_integrable hG).aestronglyMeasurable
    (Measure.measurePreserving_neg volume)

omit [CompleteSpace X] in
/-- `Δ_{I_{−k}} f (x) = Δ_{I_k} (f (−·)) (−x)`. -/
private theorem fourierInv_lineBlock_neg (k : ℤ) (G : ℝ → X) (x : ℝ) :
    𝓕⁻ ((lineBlock (-k)).indicator G) x =
      𝓕⁻ ((lineBlock k).indicator fun ξ => G (-ξ)) (-x) := by
  classical
  rw [← fourierInv_comp_neg]
  refine congrArg (fun F : ℝ → X => 𝓕⁻ F x) (funext fun ξ => ?_)
  simp only [Set.indicator_apply, mem_lineBlock_neg, neg_neg]

/-- The negative intervals, by reflection. -/
private theorem eLpNormRad_lineBlock_neg_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) :
    eLpNormRad ({i : Fin (2 * K + 1) | (i : ℕ) < K}.indicator
        fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)) p volume ≤
      littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set G' : ℝ → X := fun ξ => G (-ξ)
  have hG' : Integrable G' := hG.comp_neg
  have hG'G := eLpNorm_fourierInv_comp_neg hG (ENNReal.ofReal p)
  have hf' : MemLp (𝓕⁻ G') (ENNReal.ofReal p) volume := hG'G.trans_lt hf.eLpNorm_lt_top
  set h : Fin (2 * K + 1) → ℝ → X := {i : Fin (2 * K + 1) | K < (i : ℕ)}.indicator
    fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G') with hdef
  have hh : ∀ k, Continuous (h k) := continuous_indicator_fourierInv_lineBlock hG' _
  have h1 : ({i : Fin (2 * K + 1) | (i : ℕ) < K}.indicator
      fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)) = fun k x => h (Fin.rev k) (-x) := by
    funext k x
    by_cases hk : (k : ℕ) < K
    · have hk' : K < (Fin.rev k : ℕ) := by
        rw [Fin.val_rev]
        omega
      have hi : ((k : ℕ) : ℤ) - K = -(((Fin.rev k : ℕ) : ℤ) - K) := by
        rw [Fin.val_rev]
        omega
      rw [Set.indicator_of_mem (by exact hk), hdef, Set.indicator_of_mem (by exact hk'), hi,
        fourierInv_lineBlock_neg]
    · have hk' : ¬ K < (Fin.rev k : ℕ) := by
        rw [Fin.val_rev]
        omega
      rw [Set.indicator_of_notMem (by exact hk), hdef, Set.indicator_of_notMem (by exact hk')]
      rfl
  rw [h1, ← hG'G]
  refine (eLpNormRad_comp_le hp.le Fin.rev_injective (f := fun k x => h k (-x))
    fun k => ((hh k).comp continuous_neg).aestronglyMeasurable).trans ?_
  rw [eLpNormRad_comp_measurePreserving (by linarith) (fun k => (hh k).aestronglyMeasurable)
    (Measure.measurePreserving_neg (volume : Measure ℝ))]
  exact eLpNormRad_lineBlock_pos_le hp hβ hG' hf' K

/-- The interval `I_0 = (−1, 1)`. -/
private theorem eLpNormRad_lineBlock_zero_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) :
    eLpNormRad ({i : Fin (2 * K + 1) | (i : ℕ) = K}.indicator
        fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)) p volume ≤
      dyadicHilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set k₀ : Fin (2 * K + 1) := ⟨K, by omega⟩
  set F : ℝ → X := 𝓕⁻ ((Set.Ioo (-1 : ℝ) 1).indicator G)
  have hF : Continuous F := continuous_fourierInv_of_integrable (hG.indicator measurableSet_Ioo)
  have h1 : ({i : Fin (2 * K + 1) | (i : ℕ) = K}.indicator
      fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)) = fun i => if i = k₀ then F else 0 := by
    funext i
    by_cases hi : (i : ℕ) = K
    · rw [Set.indicator_of_mem (by exact hi), ite_eq_left (Fin.ext hi), hi, sub_self,
        lineBlock_zero]
    · rw [Set.indicator_of_notMem (by exact hi), ite_eq_right (fun h => hi (by rw [h]))]
  have hm : ∀ i, AEStronglyMeasurable (if i = k₀ then F else 0) volume := fun i => by
    split_ifs
    · exact hF.aestronglyMeasurable
    · exact continuous_zero.aestronglyMeasurable
  -- every choice of signs gives the same norm
  have h2 : ∀ ε : Fin (2 * K + 1) → Bool, eLpNorm (fun x =>
      ∑ i, SignCube.coin (ε i) • (if i = k₀ then F else 0) x) (ENNReal.ofReal p) volume =
      eLpNorm F (ENNReal.ofReal p) volume := fun ε => by
    have h3 : (fun x => ∑ i, SignCube.coin (ε i) • (if i = k₀ then F else 0) x) =
        SignCube.coin (ε k₀) • F := by
      funext x
      rw [Finset.sum_eq_single k₀ (fun i _ hi => by simp [hi]) (by simp)]
      simp
    rw [h3, eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, SignCube.abs_coin,
      ENNReal.ofReal_one, one_mul]
  rw [h1]
  exact (eLpNormRad_le_of_forall_le (by linarith) hm fun ε => (h2 ε).le).trans
    (eLpNorm_fourierInv_Ioo_le hp hβ hG hf (by norm_num))

/-- **The Littlewood–Paley inequality on the line, with the small frequencies grouped together**
(HNVW I, Corollary 5.3.25, right-hand inequality), for the intervals `I_k`, `|k| ≤ K`. The triangle
inequality separates `(−1, 1)`, which is treated by Proposition 5.3.10, from the other intervals,
and the positive from the negative ones; the latter is the sum over `σ ∈ {+, −}` in the proof of
Theorem 5.3.24, made here at the beginning, with a reflection for the negative intervals. -/
theorem eLpNormRad_lineBlock_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {G : ℝ → X} (hG : Integrable G) (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) :
    eLpNormRad (fun i : Fin (2 * K + 1) => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)) p volume ≤
      (2 * littlewoodPaleyBound β + dyadicHilbertBound β) *
        eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set f : Fin (2 * K + 1) → ℝ → X := fun i => 𝓕⁻ ((lineBlock ((i : ℕ) - K)).indicator G)
  have hm : ∀ (s : Set (Fin (2 * K + 1))) i,
      AEStronglyMeasurable (s.indicator f i) volume := fun s i =>
    (continuous_indicator_fourierInv_lineBlock hG s i).aestronglyMeasurable
  set P : Set (Fin (2 * K + 1)) := {i | K < (i : ℕ)}
  set Z : Set (Fin (2 * K + 1)) := {i | (i : ℕ) = K}
  set N : Set (Fin (2 * K + 1)) := {i | (i : ℕ) < K}
  have hsplit : f = fun i x => P.indicator f i x + (Z.indicator f i x + N.indicator f i x) := by
    funext i x
    rcases lt_trichotomy (i : ℕ) K with hi | hi | hi
    · rw [Set.indicator_of_notMem (s := P) (by simp [P, hi.le]), Set.indicator_of_notMem (s := Z)
        (by simp [Z, hi.ne]), Set.indicator_of_mem (s := N) (by exact hi)]
      simp
    · rw [Set.indicator_of_notMem (s := P) (by simp [P, hi]), Set.indicator_of_mem (s := Z)
        (by exact hi), Set.indicator_of_notMem (s := N) (by simp [N, hi])]
      simp
    · rw [Set.indicator_of_mem (s := P) (by exact hi), Set.indicator_of_notMem (s := Z)
        (by simp [Z, hi.ne']), Set.indicator_of_notMem (s := N) (by simp [N, hi.le])]
      simp
  rw [hsplit]
  calc _ ≤ eLpNormRad (P.indicator f) p volume + (eLpNormRad (Z.indicator f) p volume +
          eLpNormRad (N.indicator f) p volume) :=
        (eLpNormRad_add_le hp.le (hm P) fun i => (hm Z i).add (hm N i)).trans
          (add_le_add_right (eLpNormRad_add_le hp.le (hm Z) (hm N)) _)
    _ ≤ littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume +
        (dyadicHilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume +
          littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) := by
        gcongr
        · exact eLpNormRad_lineBlock_pos_le hp hβ hG hf K
        · exact eLpNormRad_lineBlock_zero_le hp hβ hG hf K
        · exact eLpNormRad_lineBlock_neg_le hp hβ hG hf K
    _ = _ := by ring

/-! ### Dilations -/

omit [CompleteSpace X] in
/-- `‖Σ ε_k 𝓕⁻ (F_k (ρ ·))‖_p = ρ^{1/p − 1} ‖Σ ε_k 𝓕⁻ F_k‖_p`. -/
private theorem eLpNormRad_fourierInv_dilate {n : ℕ} {p : ℝ} (hp : 0 < p) (F : Fin n → ℝ → X)
    {ρ : ℝ} (hρ : 0 < ρ) :
    eLpNormRad (fun k => 𝓕⁻ fun ξ => F k (ρ * ξ)) p volume =
      ‖ρ⁻¹‖ₑ * (ENNReal.ofReal ρ ^ (1 / p) * eLpNormRad (fun k => 𝓕⁻ (F k)) p volume) := by
  let φ : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ ρ⁻¹ (inv_ne_zero hρ.ne')).toMeasurableEquiv
  have hφ : (volume : Measure ℝ).map φ = ENNReal.ofReal ρ • volume := by
    have h := Real.map_volume_mul_left (inv_ne_zero hρ.ne')
    rwa [inv_inv, abs_of_pos hρ] at h
  have h1 : eLpNormRad (fun k x => 𝓕⁻ (F k) (φ x)) p volume =
      eLpNormRad (fun k => 𝓕⁻ (F k)) p (ENNReal.ofReal ρ • volume) := by
    have hprod := Measure.map_prod_map (volume : Measure ℝ)
      (ProbabilityTheory.uniformOn (Set.univ : Set (Fin n → Bool))) φ.measurable measurable_id
    rw [Measure.map_id] at hprod
    rw [← hφ, eLpNormRad, eLpNormRad, hprod]
    have hemb := (φ.prodCongr (MeasurableEquiv.refl (Fin n → Bool))).measurableEmbedding
    exact (hemb.eLpNorm_map_measure
      (g := fun z => ∑ k, (if z.2 k then (1 : ℝ) else -1) • 𝓕⁻ (F k) z.1)).symm
  have h2 : eLpNormRad (fun k => 𝓕⁻ (F k)) p (ENNReal.ofReal ρ • volume) =
      ENNReal.ofReal ρ ^ (1 / p) * eLpNormRad (fun k => 𝓕⁻ (F k)) p volume := by
    rw [eLpNormRad, Measure.prod_smul_left, eLpNorm_smul_measure_of_ne_zero (by simpa using hρ),
      smul_eq_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal hp.le]
    rfl
  have h3 : (fun k => 𝓕⁻ fun ξ => F k (ρ * ξ)) = fun k x => ρ⁻¹ • 𝓕⁻ (F k) (φ x) := by
    funext k x
    exact congrFun (fourierInv_comp_mul_left (F k) hρ) x
  rw [h3, eLpNormRad_fun_const_smul, h1, h2]

/-- **The Littlewood–Paley inequality on the line, dilated**: `eLpNormRad_lineBlock_le` for the
intervals `ρ⁻¹ I_k`, `|k| ≤ K`, with the same constant. For `ρ = 2^N` and `K = 2 N` these are the
dyadic intervals `(2^j, 2^{j+1})`, `−(2^j, 2^{j+1})`, `−N ≤ j < N`, of HNVW I, Theorem 5.3.24
(right-hand inequality), and `(−2^{−N}, 2^{−N})`. -/
theorem eLpNormRad_lineBlock_dilate_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {G : ℝ → X} (hG : Integrable G) (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    eLpNormRad (fun i : Fin (2 * K + 1) =>
        𝓕⁻ ({ξ | ρ * ξ ∈ lineBlock ((i : ℕ) - K)}.indicator G)) p volume ≤
      (2 * littlewoodPaleyBound β + dyadicHilbertBound β) *
        eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  set G' : ℝ → X := fun ξ => G (ρ⁻¹ * ξ)
  have hG' : Integrable G' := hG.comp_mul_left' (inv_ne_zero hρ.ne')
  have hGG' : G = fun ξ => G' (ρ * ξ) := by
    funext ξ
    simp only [G', inv_mul_cancel_left₀ hρ.ne']
  -- `‖𝓕⁻ G‖_p = ρ^{1/p − 1} ‖𝓕⁻ G'‖_p`
  have hnorm : eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume =
      ‖ρ⁻¹‖ₑ * (ENNReal.ofReal ρ ^ (1 / p) * eLpNorm (𝓕⁻ G') (ENNReal.ofReal p) volume) := by
    have h := eLpNormRad_fourierInv_dilate (n := 1) hp0 (fun _ => G') hρ
    rwa [← hGG', eLpNormRad_one hp0 (continuous_fourierInv_of_integrable hG).aestronglyMeasurable,
      eLpNormRad_one hp0 (continuous_fourierInv_of_integrable hG').aestronglyMeasurable] at h
  have hf' : MemLp (𝓕⁻ G') (ENNReal.ofReal p) volume := by
    refine lt_top_iff_ne_top.2 fun h => hf.eLpNorm_lt_top.ne ?_
    rw [hnorm, h, ENNReal.mul_top (ENNReal.rpow_pos (by simpa using hρ) (by simp)).ne',
      ENNReal.mul_top (by simpa using hρ.ne')]
  have hset : (fun i : Fin (2 * K + 1) => 𝓕⁻ ({ξ | ρ * ξ ∈ lineBlock ((i : ℕ) - K)}.indicator G)) =
      fun i : Fin (2 * K + 1) =>
        𝓕⁻ fun ξ => (lineBlock ((i : ℕ) - K)).indicator G' (ρ * ξ) := by
    classical
    funext i
    refine congrArg (fun F : ℝ → X => 𝓕⁻ F) (funext fun ξ => ?_)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, G', inv_mul_cancel_left₀ hρ.ne']
  rw [hset, eLpNormRad_fourierInv_dilate hp0
    (fun i : Fin (2 * K + 1) => (lineBlock ((i : ℕ) - K)).indicator G') hρ, hnorm]
  calc _ ≤ ‖ρ⁻¹‖ₑ * (ENNReal.ofReal ρ ^ (1 / p) *
        ((2 * littlewoodPaleyBound β + dyadicHilbertBound β) *
          eLpNorm (𝓕⁻ G') (ENNReal.ofReal p) volume)) := by
        gcongr
        exact eLpNormRad_lineBlock_le hp hβ hG' hf' K
    _ = _ := by ring

end HarmonicAnalysis
