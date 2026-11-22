/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.FourierMultiplier.Basic
import HarmonicAnalysis.FourierMultiplier.Norming

/-!
# Duality for Fourier multipliers

For `1 < p < ∞` and `q = p / (p − 1)`:

* `HarmonicAnalysis.multiplierNorm_conj_conjExponent` (the adjoint): the `L²`-adjoint of `T_m` is
  `T_{m̄}`, `∫ T_m f · ḡ = ∫ f · conj (T_{m̄} g)`
  (`HarmonicAnalysis.integral_fourierMultiplier_mul_conj`), so `‖T_m‖_p = ‖T_{m̄}‖_q`, for bounded
  measurable `m`.
* `HarmonicAnalysis.fourierMultiplier_conj`, `HarmonicAnalysis.multiplierNorm_conj_comp_neg`
  (conjugation): `conj (T_m (conj f)) = T_{m̃} f` with `m̃ (ξ) = conj (m (−ξ))`, so
  `‖T_{m̃}‖_p = ‖T_m‖_p`.

Together: `‖T_m‖_p = ‖T_{m (−·)}‖_q`; for an even symbol, `‖T_m‖_p = ‖T_m‖_q`.

The adjoint identity holds because both sides equal `∫ m · 𝓕 f · conj (𝓕 g)`
(`HarmonicAnalysis.integral_fourierInv_mul_conj`, Fubini; the bilinear form is
`HarmonicAnalysis.integral_fourierInv_mul`). With Hölder's inequality and the bound
`‖T_{m̄} g‖_q ≤ ‖T_{m̄}‖_q ‖g‖_q`, it gives `|∫ T_m f · ḡ| ≤ ‖f‖_p ‖T_{m̄}‖_q ‖g‖_q` for every
Schwartz function `g`, hence `‖T_m f‖_p ≤ ‖T_{m̄}‖_q ‖f‖_p`, because Schwartz functions norm `L^p`
(`HarmonicAnalysis.eLpNorm_le_of_forall_schwartz`). Conjugation rests on
`𝓕 (conj ∘ f) (ξ) = conj (𝓕 f (−ξ))` (`HarmonicAnalysis.fourier_conj`) and on the involution
`f ↦ conj ∘ f` of the Schwartz space (`HarmonicAnalysis.conjSchwartz`).

## References

* A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex Riesz
  transform*, Math. Ann. 386 (2023), [arXiv:2109.08369](https://arxiv.org/abs/2109.08369),
  §1.3.1 (for the powers of the complex Riesz transform).
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), Exercise 1.16.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace HarmonicAnalysis

/-- Complex conjugation of a Schwartz function, `x ↦ conj (f x)`. -/
def conjSchwartz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : 𝓢(E, ℂ)) :
    𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f

@[simp]
theorem conjSchwartz_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : 𝓢(E, ℂ))
    (x : E) : conjSchwartz f x = conj (f x) := by
  simp [conjSchwartz]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The Fourier transform and conjugation -/

/-- `conj (𝐞 t) = 𝐞 (−t)`. -/
theorem conj_fourierChar (t : ℝ) : conj ((𝐞 t : ℂ)) = 𝐞 (-t) := by
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- `𝓕 (conj ∘ f) (ξ) = conj (𝓕 f (−ξ))`, for every function `f`. -/
theorem fourier_conj (f : V → ℂ) (ξ : V) :
    𝓕 (fun v => conj (f v)) ξ = conj (𝓕 f (-ξ)) := by
  simp only [Real.fourier_eq, ← integral_conj, Circle.smul_def, smul_eq_mul, map_mul,
    conj_fourierChar, inner_neg_right, neg_neg]

/-- `𝓕⁻¹ (conj ∘ f) = conj ∘ 𝓕 f`, for every function `f`. -/
theorem fourierInv_conj (f : V → ℂ) (ξ : V) :
    𝓕⁻ (fun v => conj (f v)) ξ = conj (𝓕 f ξ) := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_conj, neg_neg]

/-! ### The adjoint -/

/-- `∫ 𝓕⁻¹ φ · ḡ = ∫ φ · conj (𝓕 g)` for integrable `φ` and `g`. -/
theorem integral_fourierInv_mul_conj {φ g : V → ℂ} (hφ : Integrable φ) (hg : Integrable g) :
    ∫ x, 𝓕⁻ φ x * conj (g x) = ∫ ξ, φ ξ * conj (𝓕 g ξ) := by
  have hL : Continuous fun p : V × V => (-innerₗ V) p.1 p.2 := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    fun_prop
  have hg' : Integrable (fun x => conj (g x)) := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hg
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar hL
    hφ hg'
  have hflip (ξ : V) : VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V).flip
      (fun x => conj (g x)) ξ = conj (𝓕 g ξ) := by
    rw [← fourierInv_conj, Real.fourierInv_eq]
    simp only [VectorFourier.fourierIntegral, LinearMap.flip_apply, LinearMap.neg_apply,
      innerₗ_apply_apply, neg_neg]
    simp_rw [real_inner_comm ξ]
  simp only [smul_eq_mul, hflip] at h
  exact h

/-- Hölder's inequality for the pairing: `|∫ u v| ≤ ‖u‖_P ‖v‖_Q` for conjugate exponents. -/
theorem enorm_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℂ}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) (P Q : ℝ≥0∞)
    [ENNReal.HolderConjugate P Q] : ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm u P μ * eLpNorm v Q μ := by
  calc ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm (fun x => u x * v x) 1 μ :=
        (enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one
    _ ≤ 1 * eLpNorm u P μ * eLpNorm v Q μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (fun a b : ℂ => a * b) 1
          (fun hf hg => hf.mul hg) hu hv (ae_of_all _ fun x => by simp)
    _ = _ := by rw [one_mul]

/-- `∫ 𝓕⁻¹ φ · g = ∫ φ · 𝓕⁻¹ g` for integrable `φ` and `g`. -/
theorem integral_fourierInv_mul {φ g : V → ℂ} (hφ : Integrable φ) (hg : Integrable g) :
    ∫ x, 𝓕⁻ φ x * g x = ∫ ξ, φ ξ * 𝓕⁻ g ξ := by
  have hg' : Integrable (fun x => conj (g x)) := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hg
  have h := integral_fourierInv_mul_conj hφ hg'
  simpa only [← fourierInv_conj, Complex.conj_conj] using h

private theorem integrable_smul_fourier {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) (f : 𝓢(V, ℂ)) :
    Integrable (fun ξ => m ξ • 𝓕 (f : V → ℂ) ξ) := by
  obtain ⟨C, hC⟩ := hmb
  have : Integrable (𝓕 (f : V → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 f).integrable
  simpa [smul_eq_mul] using this.bdd_mul hm.aestronglyMeasurable (ae_of_all _ hC)

/-- The `L²`-adjoint of `T_m` is `T_{m̄}`: `∫ T_m f · ḡ = ∫ f · conj (T_{m̄} g)` for Schwartz
functions `f`, `g` and a bounded measurable symbol `m`. -/
theorem integral_fourierMultiplier_mul_conj {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) (f g : 𝓢(V, ℂ)) :
    ∫ x, fourierMultiplier m f x * conj (g x) =
      ∫ x, f x * conj (fourierMultiplier (fun ξ => conj (m ξ)) g x) := by
  have hm' : Measurable fun ξ => conj (m ξ) := Complex.continuous_conj.measurable.comp hm
  have hmb' : ∃ C, ∀ ξ, ‖conj (m ξ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hmb
    exact ⟨C, fun ξ => by simpa using hC ξ⟩
  have h1 := integral_fourierInv_mul_conj (integrable_smul_fourier hm hmb f) g.integrable
  have h2 := integral_fourierInv_mul_conj (integrable_smul_fourier hm' hmb' g) f.integrable
  unfold fourierMultiplier
  rw [h1]
  calc ∫ ξ, m ξ • 𝓕 (f : V → ℂ) ξ * conj (𝓕 (g : V → ℂ) ξ)
      = conj (∫ ξ, conj (m ξ) • 𝓕 (g : V → ℂ) ξ * conj (𝓕 (f : V → ℂ) ξ)) := by
        rw [← integral_conj]
        congr 1
        ext ξ
        simp only [smul_eq_mul, map_mul, Complex.conj_conj]
        ring
    _ = conj (∫ x, 𝓕⁻ (fun ξ => conj (m ξ) • 𝓕 (g : V → ℂ) ξ) x * conj (f x)) := by rw [h2]
    _ = _ := by
        rw [← integral_conj]
        congr 1
        ext x
        simp only [map_mul, Complex.conj_conj]
        ring

/-- `‖T_m‖_p ≤ ‖T_{m̄}‖_q`, by duality. -/
private theorem multiplierNorm_le_conj_conjExponent {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ multiplierNorm (fun ξ => conj (m ξ)) (p / (p - 1)) := by
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) :=
    hpq.ennrealOfReal
  refine iSup_le fun f => ENNReal.div_le_of_le_mul ?_
  rw [mul_comm]
  refine eLpNorm_le_of_forall_schwartz (continuous_fourierMultiplier m f) hp fun g => ?_
  rw [integral_fourierMultiplier_mul_conj hm hmb f g]
  set T := fourierMultiplier (fun ξ => conj (m ξ)) g
  have hT : Continuous T := continuous_fourierMultiplier _ g
  calc ‖∫ x, f x * conj (T x)‖ₑ ≤ eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm (fun x => conj (T x)) (ENNReal.ofReal (p / (p - 1))) volume :=
        enorm_integral_mul_le f.continuous.aestronglyMeasurable
          (Complex.continuous_conj.comp hT).aestronglyMeasurable _ _
    _ = eLpNorm f (ENNReal.ofReal p) volume * eLpNorm T (ENNReal.ofReal (p / (p - 1))) volume := by
        congr 1
        exact eLpNorm_conj _ _ _
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume * (multiplierNorm (fun ξ => conj (m ξ)) (p / (p - 1)) *
          eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume) := by
        gcongr
        exact eLpNorm_fourierMultiplier_le _ _ g
    _ = _ := (mul_assoc _ _ _).symm

/-- The adjoint of `T_m` is `T_{m̄}`: for a bounded measurable symbol `m` and `1 < p < ∞`,
`‖T_m‖_{L^p} = ‖T_{m̄}‖_{L^q}`, `q = p / (p − 1)`. -/
theorem multiplierNorm_conj_conjExponent {m : V → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p = multiplierNorm (fun ξ => conj (m ξ)) (p / (p - 1)) := by
  refine le_antisymm (multiplierNorm_le_conj_conjExponent hm hmb hp) ?_
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hm' : Measurable fun ξ => conj (m ξ) := Complex.continuous_conj.measurable.comp hm
  have hmb' : ∃ C, ∀ ξ, ‖conj (m ξ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hmb
    exact ⟨C, fun ξ => by simpa using hC ξ⟩
  have h := multiplierNorm_le_conj_conjExponent hm' hmb' hpq.symm.lt
  rw [← hpq.symm.conjugate_eq] at h
  simpa using h

/-! ### Conjugation -/

/-- Conjugation: `conj (T_m (conj f)) = T_{m̃} f`, `m̃ (ξ) = conj (m (−ξ))`. -/
theorem fourierMultiplier_conj (m : V → ℂ) (f : V → ℂ) (x : V) :
    fourierMultiplier (fun ξ => conj (m (-ξ))) f x =
      conj (fourierMultiplier m (fun v => conj (f v)) x) := by
  simp only [fourierMultiplier, Real.fourierInv_eq, fourier_conj]
  rw [← integral_conj]
  conv_lhs => rw [← integral_neg_eq_self]
  congr 1
  ext ξ
  simp only [Circle.smul_def, smul_eq_mul, map_mul, conj_fourierChar, Complex.conj_conj, neg_neg,
    inner_neg_left]

/-- Conjugation: `‖T_{m̃}‖_{L^p} = ‖T_m‖_{L^p}`, `m̃ (ξ) = conj (m (−ξ))`. -/
theorem multiplierNorm_conj_comp_neg (m : V → ℂ) (p : ℝ) :
    multiplierNorm (fun ξ => conj (m (-ξ))) p = multiplierNorm m p := by
  have hsurj : Function.Surjective (conjSchwartz : 𝓢(V, ℂ) → 𝓢(V, ℂ)) :=
    fun f => ⟨conjSchwartz f, by ext x; simp⟩
  unfold multiplierNorm
  rw [← hsurj.iSup_comp]
  refine iSup_congr fun f => ?_
  have hf : (conjSchwartz f : V → ℂ) = fun x => conj (f x) := by
    ext x
    simp
  have hT : fourierMultiplier (fun ξ => conj (m (-ξ))) (conjSchwartz f) =
      fun x => conj (fourierMultiplier m f x) := by
    ext x
    have : (fun v => conj (conjSchwartz f v)) = (f : V → ℂ) := by
      ext v
      simp
    rw [fourierMultiplier_conj, this]
  rw [hT, hf]
  exact congr_arg₂ (· / ·) (eLpNorm_conj _ _ _) (eLpNorm_conj _ _ _)

end HarmonicAnalysis
