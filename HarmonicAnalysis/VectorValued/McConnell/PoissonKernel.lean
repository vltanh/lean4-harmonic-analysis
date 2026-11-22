/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.LittlewoodPaley.Line
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.MeasureTheory.Group.Convolution
import HarmonicAnalysis.FourierMultiplier.Density
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The Poisson kernel of the half-plane and the Cauchy law

For `y > 0` the Poisson kernel `h (s, y) = y / (π (s² + y²))` is the density of the symmetric Cauchy
law with parameter `y` (`cauchyDensity`, `cauchyLaw`; `cauchyLaw 0` is the point mass at `0`). Its
Fourier transform is `e^{−2π|ξ|y}`; hence the Cauchy laws form a convolution semigroup
(`cauchyLaw_conv`), and the Poisson integral of `f = 𝓕⁻ G`,
`u (x, y) = 𝓕⁻ (e^{−2π|ξ|y} G (ξ)) (x)` (`poissonInt G y x`), satisfies

`u (x, a + b) = ∫ u (x − t, b) dν_a (t)`, `ν_a` the Cauchy law with parameter `a`

(`integral_poissonInt_sub`).

Source: T. R. McConnell, *On Fourier multiplier transformations of Banach-valued functions*, Trans.
Amer. Math. Soc. 285 (1984), 739–757, Section 2, for `n = 1`. There, for a Brownian motion started
at `(x', y')`, the place `X (y)` of the first hit of the height `y < y'` has the Cauchy law centred
at `x'` with parameter `y' − y`, (2.2), and the identity is (2.7). Only these laws are used here; no
Brownian motion is constructed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### The Cauchy law -/

/-- McConnell (1984), (2.2), `n = 1`: the Cauchy density `h (s, y) = y / (π (s² + y²))` with
parameter `y`, centred at `0` (the Poisson kernel of the half-plane). -/
noncomputable def cauchyDensity (y s : ℝ) : ℝ :=
  y / (Real.pi * (s ^ 2 + y ^ 2))

/-- The symmetric Cauchy law with parameter `y ≥ 0`; the point mass at `0` for `y = 0` (and
`y < 0`).
-/
noncomputable def cauchyLaw (y : ℝ) : Measure ℝ :=
  ProbabilityTheory.cauchyMeasure 0 y.toNNReal

instance isProbabilityMeasure_cauchyLaw (y : ℝ) : IsProbabilityMeasure (cauchyLaw y) :=
  ProbabilityTheory.instIsProbabilityMeasure_cauchyMeasure 0 y.toNNReal

/-- `h (·, y)` is the density of Mathlib's Cauchy law. -/
private theorem cauchyPDFReal_eq {y : ℝ} (hy : 0 < y) :
    ProbabilityTheory.cauchyPDFReal 0 y.toNNReal = cauchyDensity y := by
  funext s
  rw [ProbabilityTheory.cauchyPDFReal_def, cauchyDensity, Real.coe_toNNReal y hy.le, sub_zero,
    div_eq_mul_inv, mul_inv]
  ring

/-- The Cauchy density is positive. -/
theorem cauchyDensity_pos {y : ℝ} (hy : 0 < y) (s : ℝ) : 0 < cauchyDensity y s := by
  rw [cauchyDensity]
  positivity

/-- The Cauchy density is continuous. -/
theorem continuous_cauchyDensity {y : ℝ} (hy : 0 < y) : Continuous (cauchyDensity y) := by
  unfold cauchyDensity
  refine continuous_const.div (by fun_prop) fun s => ?_
  positivity

/-- The Cauchy density is integrable. -/
private theorem integrable_cauchyDensity {y : ℝ} (hy : 0 < y) : Integrable (cauchyDensity y) := by
  rw [← cauchyPDFReal_eq hy]
  exact ProbabilityTheory.integrable_cauchyPDFReal 0

/-- The Cauchy law with parameter `0` is the point mass at `0`. -/
theorem cauchyLaw_zero : cauchyLaw 0 = Measure.dirac 0 := by
  rw [cauchyLaw, Real.toNNReal_zero, ProbabilityTheory.cauchyMeasure_zero_scale]

/-- The Cauchy law with parameter `y ≤ 0` is the point mass at `0`. -/
private theorem cauchyLaw_of_nonpos {y : ℝ} (hy : y ≤ 0) : cauchyLaw y = cauchyLaw 0 := by
  rw [cauchyLaw, cauchyLaw, Real.toNNReal_zero, Real.toNNReal_of_nonpos hy]

/-- The Cauchy law with parameter `y > 0` has the density `h (·, y)`. -/
theorem cauchyLaw_of_pos {y : ℝ} (hy : 0 < y) :
    cauchyLaw y = volume.withDensity fun s => ENNReal.ofReal (cauchyDensity y s) := by
  rw [cauchyLaw, ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (Real.toNNReal_pos.2 hy).ne']
  congr 1
  funext s
  rw [ProbabilityTheory.cauchyPDF_def, cauchyPDFReal_eq hy]

/-- Integrals for the Cauchy law with parameter `y > 0`. -/
theorem integral_cauchyLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : ℝ}
    (hy : 0 < y) (F : ℝ → E) : ∫ s, F s ∂cauchyLaw y = ∫ s, cauchyDensity y s • F s := by
  rw [cauchyLaw_of_pos hy, integral_withDensity_eq_integral_toReal_smul
    (continuous_cauchyDensity hy).measurable.ennreal_ofReal (ae_of_all _ fun _ =>
      ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (cauchyDensity_pos hy s).le]

/-- On `(0, ∞)`, `e^{2πisξ} e^{−2π|ξ|y} = e^{2π(is − y)ξ}`. -/
private theorem expChar_mul_exp_of_nonneg (y s : ℝ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    expChar ξ s * ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) =
      Complex.exp (2 * Real.pi * (s * Complex.I - y) * ξ) := by
  rw [expChar, Complex.ofReal_exp, ← Complex.exp_add, abs_of_nonneg hξ]
  push_cast
  ring_nf

/-- On `(−∞, 0]`, `e^{2πisξ} e^{−2π|ξ|y} = e^{2π(is + y)ξ}`. -/
private theorem expChar_mul_exp_of_nonpos (y s : ℝ) {ξ : ℝ} (hξ : ξ ≤ 0) :
    expChar ξ s * ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) =
      Complex.exp (2 * Real.pi * (s * Complex.I + y) * ξ) := by
  rw [expChar, Complex.ofReal_exp, ← Complex.exp_add, abs_of_nonpos hξ]
  push_cast
  ring_nf

/-- The exponent `2π(is − y)` on `(0, ∞)` has negative real part. -/
private theorem re_two_pi_mul_sub {y : ℝ} (hy : 0 < y) (s : ℝ) :
    (2 * Real.pi * (s * Complex.I - y) : ℂ).re < 0 := by
  have h : (2 * Real.pi * (s * Complex.I - y) : ℂ).re = -(2 * Real.pi * y) := by simp
  rw [h, neg_lt_zero]
  positivity

/-- The exponent `2π(is + y)` on `(−∞, 0]` has positive real part. -/
private theorem re_two_pi_mul_add {y : ℝ} (hy : 0 < y) (s : ℝ) :
    0 < (2 * Real.pi * (s * Complex.I + y) : ℂ).re := by
  have h : (2 * Real.pi * (s * Complex.I + y) : ℂ).re = 2 * Real.pi * y := by simp
  rw [h]
  positivity

/-- `e^{2πisξ} e^{−2π|ξ|y}` is integrable. -/
private theorem integrable_expChar_mul_exp {y : ℝ} (hy : 0 < y) (s : ℝ) :
    Integrable fun ξ : ℝ => expChar ξ s * ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨(integrableOn_exp_mul_complex_Iic (re_two_pi_mul_add hy s) 0).congr_fun
      (fun ξ hξ => (expChar_mul_exp_of_nonpos y s hξ).symm) measurableSet_Iic,
    (integrableOn_exp_mul_complex_Ioi (re_two_pi_mul_sub hy s) 0).congr_fun
      (fun ξ hξ => (expChar_mul_exp_of_nonneg y s (Set.mem_Ioi.1 hξ).le).symm) measurableSet_Ioi⟩

/-- `e^{−2π|ξ|y}` is integrable. -/
private theorem integrable_exp_neg_abs {y : ℝ} (hy : 0 < y) :
    Integrable fun ξ : ℝ => ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) := by
  simpa [expChar] using integrable_expChar_mul_exp hy 0

/-- The inverse Fourier transform of `e^{−2π|ξ|y}` is the Cauchy density. -/
theorem fourierInv_exp_neg_abs {y : ℝ} (hy : 0 < y) (s : ℝ) :
    𝓕⁻ (fun ξ : ℝ => ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ)) s = cauchyDensity y s := by
  have hint := integrable_expChar_mul_exp hy s
  have hy' := re_two_pi_mul_sub hy s
  have hy'' := re_two_pi_mul_add hy s
  rw [fourierInv_eq_expChar]
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn,
    setIntegral_congr_fun measurableSet_Iic fun ξ hξ => expChar_mul_exp_of_nonpos y s hξ,
    setIntegral_congr_fun measurableSet_Ioi fun ξ hξ =>
      expChar_mul_exp_of_nonneg y s (Set.mem_Ioi.1 hξ).le,
    integral_exp_mul_complex_Iic hy'', integral_exp_mul_complex_Ioi hy', cauchyDensity]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  -- `1 / (2π (is + y)) − 1 / (2π (is − y)) = y / (π (s² + y²))`
  have h1 : (2 * Real.pi * (s * Complex.I + y) : ℂ) ≠ 0 := fun h => by simp [h] at hy''
  have h2 : (2 * Real.pi * (s * Complex.I - y) : ℂ) ≠ 0 := fun h => by simp [h] at hy'
  have h3 : (Real.pi * (s ^ 2 + y ^ 2) : ℂ) ≠ 0 := by
    have h : 0 < Real.pi * (s ^ 2 + y ^ 2) := by positivity
    exact_mod_cast h.ne'
  push_cast
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * s ^ 2 * y * (-1)) * Complex.I_sq

/-- The Fourier transform of the Cauchy law is `e^{−2π|ξ|y}`. -/
theorem integral_expChar_cauchyLaw {y : ℝ} (hy : 0 ≤ y) (ξ : ℝ) :
    ∫ s, expChar ξ s ∂cauchyLaw y = ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) := by
  rcases hy.eq_or_lt with rfl | hy
  · rw [cauchyLaw_zero, integral_dirac]
    simp [expChar]
  set f : ℝ → ℂ := fun ξ => ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) with hf
  have hfc : Continuous f := by
    rw [hf]
    fun_prop
  -- the Fourier transform of the even function `f` is `h (·, y)`
  have hFf : 𝓕 f = fun s => ((cauchyDensity y s : ℝ) : ℂ) := by
    funext s
    have h : cauchyDensity y s = cauchyDensity y (-s) := by
      rw [cauchyDensity, cauchyDensity, neg_sq]
    rw [h, ← fourierInv_exp_neg_abs hy, Real.fourierInv_eq_fourier_neg, neg_neg]
  have hinv := congrFun (hfc.fourierInv_fourier_eq (integrable_exp_neg_abs hy)
    (hFf ▸ (integrable_cauchyDensity hy).ofReal)) ξ
  rw [hFf, fourierInv_eq_expChar] at hinv
  rw [integral_cauchyLaw hy]
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun s => ?_)) hinv
  simp only [expChar, Complex.real_smul, smul_eq_mul]
  rw [mul_comm ξ s, mul_comm]

/-- The characteristic function of the Cauchy law, `E e^{itX} = e^{−|t|y}`. -/
private theorem charFun_cauchyLaw {y : ℝ} (hy : 0 ≤ y) (t : ℝ) :
    charFun (cauchyLaw y) t = ((Real.exp (-(|t| * y)) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have h1 := integral_expChar_cauchyLaw hy (t / (2 * Real.pi))
  have h2 : 2 * Real.pi * |t / (2 * Real.pi)| = |t| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  rw [h2] at h1
  rw [charFun_apply_real, ← h1]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  have h3 : 2 * Real.pi * (t / (2 * Real.pi) * s) = t * s := by field_simp
  simp only [expChar, h3, Complex.ofReal_mul]

/-- The Cauchy law is symmetric. -/
theorem map_neg_cauchyLaw (y : ℝ) : (cauchyLaw y).map (fun s => -s) = cauchyLaw y := by
  wlog hy : 0 ≤ y generalizing y
  · rw [cauchyLaw_of_nonpos (not_le.1 hy).le]
    exact this 0 le_rfl
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have h : charFun ((cauchyLaw y).map fun s => -s) t = charFun (cauchyLaw y) (-t) := by
    rw [charFun_apply_real, charFun_apply_real, integral_map measurable_neg.aemeasurable
      (by fun_prop)]
    simp
  rw [h, charFun_cauchyLaw hy, charFun_cauchyLaw hy, abs_neg]

/-- If `X` and `Y` are independent symmetric Cauchy variables with parameters `a` and `b`, then
`X + Y` is a symmetric Cauchy variable with parameter `a + b`. -/
theorem cauchyLaw_conv {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (cauchyLaw a).conv (cauchyLaw b) = cauchyLaw (a + b) := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_conv, charFun_cauchyLaw ha, charFun_cauchyLaw hb,
    charFun_cauchyLaw (add_nonneg ha hb), ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-! ### Poisson integrals -/

/-- The Poisson integral `u (x, y)` of `f = 𝓕⁻ G`: `u (·, y) = 𝓕⁻ (e^{−2π|ξ|y} G)`. -/
noncomputable def poissonInt (G : ℝ → X) (y : ℝ) : ℝ → X :=
  𝓕⁻ fun ξ => ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) • G ξ

/-- `u (·, 0) = f`. -/
theorem poissonInt_zero (G : ℝ → X) : poissonInt G 0 = 𝓕⁻ G := by
  simp [poissonInt]

/-- `e^{−2π|ξ|y} ≤ 1` for `y ≥ 0`. -/
private theorem norm_exp_neg_abs_le {y : ℝ} (hy : 0 ≤ y) (ξ : ℝ) :
    ‖((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ)‖ ≤ 1 := by
  have hpi := Real.pi_pos
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff,
    neg_nonpos]
  positivity

/-- `e^{−2π|ξ|y} G` is integrable. -/
private theorem integrable_exp_neg_abs_smul {G : ℝ → X} (hG : Integrable G) {y : ℝ} (hy : 0 ≤ y) :
    Integrable fun ξ => ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) • G ξ :=
  hG.bdd_smul 1 (by fun_prop : Continuous fun ξ : ℝ =>
    ((Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ)).aestronglyMeasurable
    (ae_of_all _ (norm_exp_neg_abs_le hy))

/-- Poisson integrals are continuous. -/
theorem continuous_poissonInt {G : ℝ → X} (hG : Integrable G) {y : ℝ} (hy : 0 ≤ y) :
    Continuous (poissonInt G y) :=
  continuous_fourierInv_of_integrable (integrable_exp_neg_abs_smul hG hy)

/-- Poisson integrals of `f = 𝓕⁻ G`, `G ∈ L¹`, are bounded by `‖G‖_1`. -/
theorem norm_poissonInt_le {G : ℝ → X} (hG : Integrable G) {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    ‖poissonInt G y x‖ ≤ ∫ ξ, ‖G ξ‖ := by
  rw [poissonInt, fourierInv_eq_expChar]
  refine norm_integral_le_of_norm_le hG.norm (ae_of_all _ fun ξ => ?_)
  rw [norm_smul, norm_expChar, one_mul, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_exp_neg_abs_le hy ξ)

/-- `∫ e_v (x − t) dν_a (t) = e_v (x) e^{−2π|v|a}`. -/
private theorem integral_expChar_sub_cauchyLaw {a : ℝ} (ha : 0 ≤ a) (x v : ℝ) :
    ∫ t, expChar v (x - t) ∂cauchyLaw a =
      expChar v x * ((Real.exp (-(2 * Real.pi * |v| * a)) : ℝ) : ℂ) := by
  rw [← abs_neg v, ← integral_expChar_cauchyLaw ha, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [expChar]
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- The integrand of the Fubini argument in `integral_poissonInt_sub` is integrable. -/
private theorem integrable_expChar_sub_smul {G : ℝ → X} (hG : Integrable G) {a : ℝ} (x : ℝ) :
    Integrable (Function.uncurry fun t v : ℝ => expChar v (x - t) • G v)
      ((cauchyLaw a).prod volume) :=
  (hG.comp_snd (cauchyLaw a)).bdd_smul 1 (φ := fun p : ℝ × ℝ => expChar p.2 (x - p.1))
    (by unfold expChar; fun_prop : Continuous fun p : ℝ × ℝ =>
      expChar p.2 (x - p.1)).aestronglyMeasurable
    (ae_of_all _ fun p => (norm_expChar _ _).le)

/-- McConnell (1984), Lemma 2.2 and (2.7): `u (x, a + b) = E^x u (X (a), b)`, where `X (a)` has the
Cauchy law with parameter `a` centred at `x`.

The last step of the proof of Lemma 2.2, `∫ u (ξ, b) h_x (ξ, a) dξ = u (x, a + b)`, is in the source
the Poisson integral representation of the harmonic function `u`. Here `u` is given by its Fourier
transform, and the identity follows from Fubini's theorem and the Fourier transform of `ν_a`. -/
theorem integral_poissonInt_sub [CompleteSpace X] {G : ℝ → X} (hG : Integrable G) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) :
    ∫ t, poissonInt G b (x - t) ∂cauchyLaw a = poissonInt G (a + b) x := by
  simp only [poissonInt, fourierInv_eq_expChar]
  rw [integral_integral_swap
    (integrable_expChar_sub_smul (integrable_exp_neg_abs_smul hG hb) x)]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [integral_smul_const, integral_expChar_sub_cauchyLaw ha, mul_smul, smul_smul
    ((Real.exp (-(2 * Real.pi * |v| * a)) : ℝ) : ℂ), ← Complex.ofReal_mul, ← Real.exp_add]
  congr 4
  ring

/-- The Poisson integral is a contraction of `L^p`: by (2.7), `u (x, y) = ∫ f (x − t) dν_y (t)`, and
`ν_y` is a probability measure. -/
theorem eLpNorm_poissonInt_le [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p) {G : ℝ → X}
    (hG : Integrable G) {y : ℝ} (hy : 0 ≤ y) :
    eLpNorm (poissonInt G y) (ENNReal.ofReal p) volume ≤
      eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hc : Continuous (𝓕⁻ G) := continuous_fourierInv_of_integrable hG
  -- (2.7) with `y_2 = 0`
  have h1 : ∀ x, ‖poissonInt G y x‖ₑ ≤ ∫⁻ t, 1 * ‖𝓕⁻ G (x - t)‖ₑ ∂cauchyLaw y := fun x => by
    have h := integral_poissonInt_sub hG hy le_rfl x
    rw [add_zero, poissonInt_zero] at h
    rw [← h]
    simpa only [one_mul] using enorm_integral_le_lintegral_enorm _
  rw [← ENNReal.rpow_le_rpow_iff hp0,
    eLpNorm_ofReal_rpow_eq_lintegral hp0 (continuous_poissonInt hG hy).aestronglyMeasurable,
    eLpNorm_ofReal_rpow_eq_lintegral hp0 hc.aestronglyMeasurable]
  -- Jensen's inequality and Tonelli's theorem
  calc ∫⁻ x, ‖poissonInt G y x‖ₑ ^ p
      ≤ ∫⁻ x, (∫⁻ t, 1 * ‖𝓕⁻ G (x - t)‖ₑ ∂cauchyLaw y) ^ p := by
        gcongr with x
        exact h1 x
    _ ≤ (∫⁻ _, 1 ∂cauchyLaw y) ^ (p - 1) *
        ∫⁻ t, 1 * (∫⁻ x, ‖𝓕⁻ G (x - t)‖ₑ ^ p) ∂cauchyLaw y :=
        lintegral_rpow_lintegral_mul_le measurable_const
          (hc.comp (continuous_fst.sub continuous_snd)).enorm.measurable hp
    _ = ∫⁻ x, ‖𝓕⁻ G x‖ₑ ^ p := by
        have h2 : ∀ t : ℝ, ∫⁻ x, ‖𝓕⁻ G (x - t)‖ₑ ^ p = ∫⁻ x, ‖𝓕⁻ G x‖ₑ ^ p := fun t =>
          lintegral_sub_right_eq_self (fun x => ‖𝓕⁻ G x‖ₑ ^ p) t
        simp [h2]

end HarmonicAnalysis
