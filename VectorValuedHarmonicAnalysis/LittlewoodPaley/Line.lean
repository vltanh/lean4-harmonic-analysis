module

public import VectorValuedHarmonicAnalysis.HilbertTransform.Fourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Littlewood–Paley inequality on the line for UMD spaces

Let `X` be a complex UMD space, `1 < p < ∞` and `I_k = (2^k, 2^{k+1})`. For `f = 𝓕⁻ G ∈ L^p (ℝ; X)`,
`G ∈ L¹`, and
`Δ_{I_k} f = 𝓕⁻ (1_{I_k} G)`,

`‖Σ_{0 ≤ k < K} ε_k Δ_{I_k} f‖_{L^p (ℝ × Ω; X)} ≤ C β ħ ‖f‖_{L^p (ℝ; X)}`
(`eLpNormRad_fourierInv_indicator_le`),

where `β` is a `UMD_p` constant of `X` and `ħ = hilbertBound β` the bound of the Hilbert transform.

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Section 5.3,
pp. 412–419: the interval multipliers from the Hilbert transform, Lemma 5.3.21 (a randomised Mihlin
theorem, from (5.36)), Lemma 5.3.22 (which is Proposition 5.1.10), Lemma 5.3.23 (the multipliers
`1_I / φ̂_I`) and Theorem 5.3.24, right-hand inequality, for the intervals `(2^k, 2^{k+1})`, `k ≥ 0`
(the intervals of `(0, 1)` are reached by dilation, the negative ones by reflection).
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal FourierTransform

namespace VectorValuedHarmonicAnalysis

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

/-- The character `e_a (x) = e^{2πi a x}`. -/
private noncomputable def expChar (a x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (a * x) : ℝ) : ℂ) * Complex.I)

private theorem norm_expChar (a x : ℝ) : ‖expChar a x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem continuous_expChar (a : ℝ) : Continuous (expChar a) := by
  unfold expChar
  fun_prop

private theorem expChar_add_left (a b x : ℝ) : expChar (a + b) x = expChar a x * expChar b x := by
  rw [expChar, expChar, expChar, ← Complex.exp_add]
  push_cast
  ring_nf

private theorem expChar_comm (a x : ℝ) : expChar a x = expChar x a := by
  rw [expChar, expChar, mul_comm a]

private theorem fourierInv_eq_expChar (G : ℝ → X) (x : ℝ) :
    𝓕⁻ G x = ∫ v, expChar v x • G v := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp [expChar, mul_comm]

private theorem fourierInv_smul_expChar (a : ℝ) (G : ℝ → X) (x : ℝ) :
    𝓕⁻ (fun ξ => G (ξ + a)) x = expChar (-a) x • 𝓕⁻ G x := by
  rw [fourierInv_eq_expChar, fourierInv_eq_expChar, ← integral_smul,
    ← integral_add_right_eq_self (fun v => expChar (-a) x • expChar v x • G v) a]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [smul_smul, ← expChar_add_left]
  rw [neg_add_eq_sub, add_sub_cancel_right]

private theorem integrable_expChar_smul {G : ℝ → X} (hG : Integrable G) (x : ℝ) :
    Integrable fun v => expChar v x • G v :=
  hG.bdd_smul 1 (by simpa only [expChar_comm] using
    (continuous_expChar x).aestronglyMeasurable) (ae_of_all _ fun v => (norm_expChar v x).le)

private theorem continuous_fourierInv {G : ℝ → X} (hG : Integrable G) : Continuous (𝓕⁻ G) := by
  have h : Continuous (𝓕 G) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hG
  rw [show 𝓕⁻ G = fun x => 𝓕 G (-x) from funext fun x => Real.fourierInv_eq_fourier_neg G x]
  exact h.comp continuous_neg

private theorem dilateConv_eq (φ : ℝ → ℝ) (t : ℝ) (f : ℝ → X) (x : ℝ) :
    dilateConv φ t f x = ∫ z, (t⁻¹ * φ (t⁻¹ * z)) • f (x - z) := by
  rw [dilateConv, ← integral_sub_left_eq_self (fun z => (t⁻¹ * φ (t⁻¹ * z)) • f (x - z)) volume x]
  simp only [sub_sub_cancel]

/-- The convolution `φ_t * 𝓕⁻ G` as a Fourier multiplier. -/
theorem dilateConv_fourierInv {φ : ℝ → ℝ} (hφ : Integrable φ) {t : ℝ} (ht : 0 < t) {G : ℝ → X}
    (hG : Integrable G) :
    dilateConv φ t (𝓕⁻ G) = 𝓕⁻ fun ξ => 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) (t * ξ) • G ξ := by
  funext x
  by_cases hX : CompleteSpace X
  swap
  · simp [dilateConv, Real.fourierInv_eq', integral, hX]
  have hφt : Integrable fun z : ℝ => ((t⁻¹ * φ (t⁻¹ * z) : ℝ) : ℂ) :=
    ((hφ.comp_mul_left' (inv_ne_zero ht.ne')).const_mul t⁻¹).ofReal
  have hint : Integrable (Function.uncurry fun z v : ℝ =>
      (((t⁻¹ * φ (t⁻¹ * z) : ℝ) : ℂ) * expChar v (x - z)) • G v) (volume.prod volume) := by
    have h := (hφt.smul_prod hG).bdd_smul 1 (φ := fun p : ℝ × ℝ => expChar p.2 (x - p.1))
      (by unfold expChar; fun_prop : Continuous fun p : ℝ × ℝ =>
        expChar p.2 (x - p.1)).aestronglyMeasurable
      (ae_of_all _ fun p => (norm_expChar _ _).le)
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [Pi.smul_apply', Function.uncurry, smul_smul]
    rw [mul_comm]
  have h1 : dilateConv φ t (𝓕⁻ G) x =
      ∫ z, ∫ v, (((t⁻¹ * φ (t⁻¹ * z) : ℝ) : ℂ) * expChar v (x - z)) • G v := by
    rw [dilateConv_eq]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [fourierInv_eq_expChar, ← Complex.coe_smul, ← integral_smul]
    simp only [smul_smul]
  have h2 : ∀ v : ℝ, ∫ z, ((t⁻¹ * φ (t⁻¹ * z) : ℝ) : ℂ) * expChar v (x - z) =
      expChar v x * 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) (t * v) := fun v => by
    have h3 := Measure.integral_comp_mul_left
      (fun y : ℝ => ((φ y : ℝ) : ℂ) * expChar v (x - t * y)) t⁻¹
    simp only [mul_inv_cancel_left₀ ht.ne', inv_inv, abs_of_pos ht] at h3
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    have h4 : ∫ z, ((t⁻¹ * φ (t⁻¹ * z) : ℝ) : ℂ) * expChar v (x - z) =
        (t⁻¹ : ℂ) * ∫ z, ((φ (t⁻¹ * z) : ℝ) : ℂ) * expChar v (x - z) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      push_cast
      ring
    rw [h4, h3, ← Complex.coe_smul, smul_eq_mul, inv_mul_cancel_left₀ (by simpa using ht.ne')]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [smul_eq_mul, expChar]
    rw [← mul_assoc (Complex.exp _), ← Complex.exp_add, mul_comm]
    push_cast
    ring_nf
  rw [h1, integral_integral_swap hint, fourierInv_eq_expChar]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [integral_smul_const, h2, mul_smul]

private theorem measurable_sign : Measurable Real.sign :=
  Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

private theorem norm_sign_le (ξ : ℝ) : ‖(Real.sign ξ : ℂ)‖ ≤ 1 := by
  rcases Real.sign_apply_eq ξ with h | h | h <;> simp [h]

private theorem measurable_sign_sub (a : ℝ) : Measurable fun ξ => (Real.sign (ξ - a) : ℂ) :=
  Complex.measurable_ofReal.comp (measurable_sign.comp (measurable_id.sub_const a))

private theorem integrable_sign_smul {G : ℝ → X} (hG : Integrable G) (a : ℝ) :
    Integrable fun ξ => (Real.sign (ξ - a) : ℂ) • G ξ :=
  hG.bdd_smul 1 (measurable_sign_sub a).aestronglyMeasurable (ae_of_all _ fun _ => norm_sign_le _)

/-- `𝓕⁻` is linear. -/
private theorem fourierInv_sum_smul {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (c : Fin K → ℝ) (x : ℝ) :
    𝓕⁻ (fun ξ => ∑ k, c k • G k ξ) x = ∑ k, c k • 𝓕⁻ (G k) x := by
  simp only [fourierInv_eq_expChar]
  simp_rw [← integral_smul, Finset.smul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => integral_congr_ae (ae_of_all _ fun v => smul_comm _ _ _)
  · intro k _
    exact integrable_expChar_smul ((hG k).smul (c k)) x

/-- HNVW I, p. 413: `Δ_{(a,b)} = ½ (T_{sgn (· − a)} − T_{sgn (· − b)})`. -/
private theorem fourierInv_indicator_Ioo {G : ℝ → X} (hG : Integrable G) {a b : ℝ} (hab : a ≤ b)
    (x : ℝ) : 𝓕⁻ ((Set.Ioo a b).indicator G) x =
      (1 / 2 : ℝ) • 𝓕⁻ (fun ξ => (Real.sign (ξ - a) : ℂ) • G ξ) x +
        (-1 / 2 : ℝ) • 𝓕⁻ (fun ξ => (Real.sign (ξ - b) : ℂ) • G ξ) x := by
  simp only [fourierInv_eq_expChar]
  rw [← integral_smul, ← integral_smul]
  refine Eq.trans (integral_congr_ae ?_) (integral_add
    ((integrable_expChar_smul (integrable_sign_smul hG a) x).smul (1 / 2 : ℝ))
    ((integrable_expChar_smul (integrable_sign_smul hG b) x).smul (-1 / 2 : ℝ)))
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton a),
    compl_mem_ae_iff.2 (measure_singleton b)] with ξ ha hb
  have ha' : ξ ≠ a := ha
  have hb' : ξ ≠ b := hb
  rcases lt_or_gt_of_ne ha' with h1 | h1
  · have h2 : ξ < b := h1.trans_le hab
    rw [Set.indicator_of_notMem (fun h => by linarith [h.1]), Real.sign_of_neg (by linarith),
      Real.sign_of_neg (by linarith), ← add_smul]
    norm_num
  · rcases lt_or_gt_of_ne hb' with h2 | h2
    · rw [Set.indicator_of_mem (Set.mem_Ioo.2 ⟨h1, h2⟩), Real.sign_of_pos (by linarith),
        Real.sign_of_neg (by linarith)]
      simp only [Complex.ofReal_one, Complex.ofReal_neg, one_smul, neg_smul, smul_neg, neg_div]
      rw [neg_neg, ← add_smul]
      norm_num
    · rw [Set.indicator_of_notMem (fun h => by linarith [h.2]), Real.sign_of_pos (by linarith),
        Real.sign_of_pos (by linarith), ← add_smul]
      norm_num

private theorem eLpNormRad_const_smul {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : ℕ} (c : ℝ) (f : Fin K → α → E) (p : ℝ) :
    eLpNormRad (fun k x => c • f k x) p μ = ‖c‖ₑ * eLpNormRad f p μ := by
  rw [eLpNormRad, eLpNormRad, ← eLpNorm_const_smul]
  congr 1
  funext z
  simp only [Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

private theorem memLp_expChar_smul {p : ℝ≥0∞} {f : ℝ → X} (hf : MemLp f p volume) (a : ℝ) :
    MemLp (fun x => expChar a x • f x) p volume :=
  hf.of_le ((continuous_expChar a).aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by rw [norm_smul, norm_expChar, one_mul])

variable [CompleteSpace X]

/-- The randomised bound for the modulated Hilbert transforms: for each choice of signs the bound of
the Hilbert transform, and the contraction principle for the modulations (HNVW I, p. 414). -/
private theorem eLpNormRad_fourierInv_sign_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) (a : Fin K → ℝ) :
    eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign (ξ - a k) : ℂ) • G k ξ) p volume ≤
      4 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  set G' : Fin K → ℝ → X := fun k ξ => G k (ξ + a k)
  have hG' : ∀ k, Integrable (G' k) := fun k => (hG k).comp_add_right (a k)
  have hsG : ∀ k, Integrable fun ξ => (Real.sign ξ : ℂ) • G' k ξ := fun k => by
    simpa only [sub_zero] using integrable_sign_smul (hG' k) 0
  have hinv : ∀ k, 𝓕⁻ (G' k) = fun x => expChar (-a k) x • 𝓕⁻ (G k) x := fun k =>
    funext fun x => fourierInv_smul_expChar (a k) (G k) x
  have hG'p : ∀ k, MemLp (𝓕⁻ (G' k)) (ENNReal.ofReal p) volume := fun k => by
    rw [hinv]
    exact memLp_expChar_smul (hf k) _
  -- the modulations on the left
  have h1 : ∀ k, (𝓕⁻ fun ξ => (Real.sign (ξ - a k) : ℂ) • G k ξ) =
      fun x => expChar (a k) x • 𝓕⁻ (fun ξ => (Real.sign ξ : ℂ) • G' k ξ) x := fun k => by
    funext x
    rw [← neg_neg (a k), ← fourierInv_smul_expChar]
    simp only [G', neg_neg, ← sub_eq_add_neg, sub_add_cancel]
  simp only [h1]
  refine (eLpNormRad_smul_le hp.le (c := fun k => expChar (a k))
    (f := fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ) (fun k x => (norm_expChar _ _).le)
    (fun k => (continuous_expChar _).aestronglyMeasurable)
    fun k => (continuous_fourierInv (hsG k)).aestronglyMeasurable).trans ?_
  -- the Hilbert transform, for each choice of signs
  have h2 : eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ) p volume ≤
      hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G' k)) p volume := by
    refine eLpNormRad_le_of_forall (by linarith)
      (fun k => (continuous_fourierInv (hsG k)).aestronglyMeasurable)
      (fun k => (continuous_fourierInv (hG' k)).aestronglyMeasurable) fun ε => ?_
    have h3 : (fun x => ∑ k, SignCube.coin (ε k) • 𝓕⁻ (fun ξ => (Real.sign ξ : ℂ) • G' k ξ) x) =
        𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • ∑ k, SignCube.coin (ε k) • G' k ξ := by
      funext x
      rw [← fourierInv_sum_smul hsG]
      simp only [Finset.smul_sum, smul_comm (_ : ℂ) (_ : ℝ)]
    have h4 : (fun x => ∑ k, SignCube.coin (ε k) • 𝓕⁻ (G' k) x) =
        𝓕⁻ fun ξ => ∑ k, SignCube.coin (ε k) • G' k ξ :=
      funext fun x => (fourierInv_sum_smul hG' _ x).symm
    have h5 : MemLp (𝓕⁻ fun ξ => ∑ k, SignCube.coin (ε k) • G' k ξ) (ENNReal.ofReal p) volume := by
      rw [← h4]
      exact memLp_finsetSum _ fun k _ => (hG'p k).const_smul _
    rw [h3, h4]
    exact eLpNorm_fourierInv_sign_le hp hβ
      (integrable_finsetSum _ fun k _ => (hG' k).smul (SignCube.coin (ε k))) h5
  -- the modulations on the right
  have h6 : eLpNormRad (fun k => 𝓕⁻ (G' k)) p volume ≤
      2 * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
    simp only [hinv]
    exact eLpNormRad_smul_le hp.le (c := fun k => expChar (-a k)) (fun k x => (norm_expChar _ _).le)
      (fun k => (continuous_expChar _).aestronglyMeasurable) fun k => (hf k).aestronglyMeasurable
  calc 2 * eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ) p volume
      ≤ 2 * (hilbertBound β * (2 * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume)) := by
        gcongr
        exact h2.trans (by gcongr)
    _ = 4 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by ring

/-- HNVW I, pp. 413–414: the randomised bound for intervals, from the Hilbert transform. For any
`a_k ≤ b_k`, `‖Σ ε_k Δ_{(a_k, b_k)} f_k‖ ≤ 4 ħ ‖Σ ε_k f_k‖`, the factor `4` being two applications
of the contraction principle with the factor `2` (real signs; the book has complex ones). -/
theorem eLpNormRad_fourierInv_Ioo_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) {a b : Fin K → ℝ}
    (hab : ∀ k, a k ≤ b k) :
    eLpNormRad (fun k => 𝓕⁻ ((Set.Ioo (a k) (b k)).indicator (G k))) p volume ≤
      4 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  have hcont : ∀ (c : Fin K → ℝ) k,
      Continuous (𝓕⁻ fun ξ => (Real.sign (ξ - c k) : ℂ) • G k ξ) := fun c k =>
    continuous_fourierInv (integrable_sign_smul (hG k) (c k))
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
  have hhalf : ∀ c : ℝ, c = 1 / 2 ∨ c = -1 / 2 → ‖c‖ₑ = 2⁻¹ := by
    intro c hc
    rw [← ofReal_norm, Real.norm_eq_abs, show |c| = 2⁻¹ by rcases hc with rfl | rfl <;> norm_num,
      ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [eLpNormRad_const_smul (1 / 2 : ℝ) (fun k => 𝓕⁻ fun ξ => (Real.sign (ξ - a k) : ℂ) • G k ξ),
    eLpNormRad_const_smul (-1 / 2 : ℝ) (fun k => 𝓕⁻ fun ξ => (Real.sign (ξ - b k) : ℂ) • G k ξ),
    hhalf _ (Or.inl rfl), hhalf _ (Or.inr rfl)]
  set R := 4 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume
  calc _ ≤ (2⁻¹ : ℝ≥0∞) * R + 2⁻¹ * R := by
        gcongr
        · exact eLpNormRad_fourierInv_sign_le hp hβ hG hf a
        · exact eLpNormRad_fourierInv_sign_le hp hβ hG hf b
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
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [fourierInv_eq_expChar]
    rw [← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun v => smul_comm _ _ _)
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
      36 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  set R := 4 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume with hR
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
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := fun k x => by
    refine (integrable_haarWeightDeriv_smul (hG k) (T k) x).integral_prod_right.congr
      (ae_of_all _ fun s => ?_)
    simp only [Function.uncurry, fourierInv_eq_expChar]
    rw [← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun v => smul_comm _ _ _)
  have h2 : eLpNormRad (fun k x => haarWeight (1 / 2) •
      𝓕⁻ ((Set.Ioo (T k / 2) (T k)).indicator (G k)) x) p volume ≤
      ‖haarWeight (1 / 2)‖ₑ * R := by
    rw [eLpNormRad_const_smul (haarWeight (1 / 2))
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
    rw [eLpNormRad_const_smul (haarWeightDeriv s)
      (fun k => 𝓕⁻ ((Set.Ioo (T k * s) (T k)).indicator (G k)))]
    gcongr
    exact eLpNormRad_fourierInv_Ioo_le hp hβ hG hf fun k => by nlinarith [hT k, hs.2]
  rw [h1]
  refine (eLpNormRad_add_le hp.le
    (f := fun k x => haarWeight (1 / 2) • 𝓕⁻ ((Set.Ioo (T k / 2) (T k)).indicator (G k)) x)
    (g := fun k x => ∫ s in Set.Ioc (1 / 2 : ℝ) 1,
      haarWeightDeriv s • 𝓕⁻ ((Set.Ioo (T k * s) (T k)).indicator (G k)) x)
    (fun k => ((continuous_fourierInv ((hG k).indicator
      measurableSet_Ioo)).const_smul _).aestronglyMeasurable)
    fun k => (hFm k).integral_prod_left.aestronglyMeasurable).trans ?_
  calc _ ≤ ‖haarWeight (1 / 2)‖ₑ * R +
        (∫⁻ s in Set.Ioc (1 / 2 : ℝ) 1, ‖haarWeightDeriv s‖ₑ) * R := add_le_add h2 h3
    _ ≤ 9 * R := by
        rw [← add_mul]
        gcongr
        exact haarWeight_total_le
    _ = 36 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
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
      36 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
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

/-- The Littlewood–Paley constant. -/
noncomputable def littlewoodPaleyBound (β : ℝ≥0∞) : ℝ≥0∞ := 72 * hilbertBound β * β

omit [CompleteSpace X] in
/-- Young's inequality, qualitatively: `φ_t * f ∈ L^p`. -/
private theorem memLp_dilateConv_haarCorrelation {p : ℝ} (hp : 1 ≤ p) {f : ℝ → X}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hfm : StronglyMeasurable f) {t : ℝ} (ht : 0 < t) :
    MemLp (dilateConv (haarCorrelation haar) t f) (ENNReal.ofReal p) volume := by
  have hφ : Measurable (haarCorrelation haar) :=
    (StronglyMeasurable.integral_prod_right (f := fun x u => haar (x + u) * haar u)
      ((measurable_haar.comp (measurable_fst.add measurable_snd)).mul
        (measurable_haar.comp measurable_snd)).stronglyMeasurable).measurable
  have hw : Measurable fun z => t⁻¹ * haarCorrelation haar (t⁻¹ * z) :=
    (hφ.comp (measurable_const_mul t⁻¹)).const_mul _
  have hwi : Integrable fun z => t⁻¹ * haarCorrelation haar (t⁻¹ * z) :=
    (integrable_haarCorrelation.comp_mul_left' (inv_ne_zero ht.ne')).const_mul t⁻¹
  have hF : StronglyMeasurable (Function.uncurry fun x z : ℝ => f (x - z)) :=
    hfm.comp_measurable (measurable_fst.sub measurable_snd)
  have h1 : dilateConv (haarCorrelation haar) t f =
      fun x => ∫ z, (t⁻¹ * haarCorrelation haar (t⁻¹ * z)) • f (x - z) :=
    funext fun x => dilateConv_eq _ t f x
  rw [h1]
  have hm : StronglyMeasurable fun x => ∫ z, (t⁻¹ * haarCorrelation haar (t⁻¹ * z)) • f (x - z) :=
    StronglyMeasurable.integral_prod_right
      (f := fun x z : ℝ => (t⁻¹ * haarCorrelation haar (t⁻¹ * z)) • f (x - z))
      ((hw.comp measurable_snd).stronglyMeasurable.smul hF)
  rw [memLp_iff]
  refine (eLpNorm_integral_smul_le hp hw hF (C := eLpNorm f (ENNReal.ofReal p) volume)
    (ae_of_all _ fun z => ?_)).trans_lt (ENNReal.mul_lt_top ?_ hf.eLpNorm_lt_top)
  · exact (eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable
      (measurePreserving_sub_right volume z)).le
  · exact hwi.hasFiniteIntegral

/-- **The Littlewood–Paley inequality on the line** (HNVW I, Theorem 5.3.24, right-hand inequality),
for the intervals `(2^k, 2^{k+1})`, `0 ≤ k < K`. -/
theorem eLpNormRad_fourierInv_indicator_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) :
    eLpNormRad (fun k : Fin K =>
        𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator G)) p volume ≤
      littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set φ' : ℝ → ℂ := 𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ))
  have hfm : StronglyMeasurable (𝓕⁻ G) := (continuous_fourierInv hG).stronglyMeasurable
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
    exact memLp_dilateConv_haarCorrelation hp.le hf hfm (by positivity)
  -- `1_{I_k} = (1_{I_k} / φ̂ (2^{−k−1} ·)) φ̂ (2^{−k−1} ·)`
  have hdiv : ∀ k : Fin K, (Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator G =
      (Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator fun ξ =>
        (φ' ((2 ^ ((k : ℕ) + 1))⁻¹ * ξ))⁻¹ • H k ξ := fun k => by
    funext ξ
    by_cases hξ : ξ ∈ Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
      have h0 : (0 : ℝ) < 2 ^ ((k : ℕ) + 1) := by positivity
      have hσ0 : 0 < (2 ^ ((k : ℕ) + 1))⁻¹ * ξ :=
        mul_pos (inv_pos.2 h0) ((by positivity : (0 : ℝ) < 2 ^ (k : ℕ)).trans hξ.1)
      have hσ1 : (2 ^ ((k : ℕ) + 1))⁻¹ * ξ < 1 := by
        rw [inv_mul_lt_iff₀ h0, mul_one]
        exact hξ.2
      have hpi := Real.pi_pos
      have hsin : 0 < Real.sin (Real.pi * ((2 ^ ((k : ℕ) + 1))⁻¹ * ξ) / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
      have hne : φ' ((2 ^ ((k : ℕ) + 1))⁻¹ * ξ) ≠ 0 := by
        simp only [φ']
        rw [fourier_haarCorrelation_haar hσ0.ne', Complex.ofReal_ne_zero]
        positivity
      simp only [H]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]
  simp only [hdiv]
  refine (eLpNormRad_fourierInv_div_le hp hβ hH hHp).trans ?_
  -- Lemma 5.3.22 (Proposition 5.1.10)
  have h1 : eLpNormRad (fun k => 𝓕⁻ (H k)) p volume ≤
      2 * β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
    simp only [hconv]
    refine (eLpNormRad_comp_le hp.le (σ := Fin.succ) (Fin.succ_injective K)
      (f := fun j : Fin (K + 1) =>
        dilateConv (haarCorrelation haar) (((2 : ℝ) ^ (j : ℕ))⁻¹) (𝓕⁻ G)) fun j => ?_).trans
      (eLpNormRad_dilateConv_le hp hβ hf hfm (K + 1))
    exact (memLp_dilateConv_haarCorrelation hp.le hf hfm (by positivity)).aestronglyMeasurable
  calc 36 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (H k)) p volume
      ≤ 36 * hilbertBound β * (2 * β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) := by gcongr
    _ = littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
        rw [littlewoodPaleyBound]
        ring

end VectorValuedHarmonicAnalysis
