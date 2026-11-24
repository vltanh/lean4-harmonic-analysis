/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.BeurlingAhlfors.Basic
public import HarmonicAnalysis.FourierMultiplier.Density

/-!
# The Cauchy transform on the Fourier side

The Cauchy transform of `g : ℂ → ℂ` is `C g (z) = (1/π) ∫ g (w) / (z − w) dw`, the inverse of `∂̄`:
`∂̄ (C g) = g` and `∂ (C g) = 𝓑 g`. Since `𝓕 (∂̄f) (ξ) = π i ξ 𝓕 f (ξ)`
(`HarmonicAnalysis.fourier_dzbarCLM`), its Fourier symbol is `(π i ξ)⁻¹`, and it is defined here as
the Fourier multiplier with that symbol, `C g = 𝓕⁻¹ ((π i ξ)⁻¹ 𝓕 g)` (`0` at `ξ = 0`), with no
kernel: the formula `(1/π) ∫ g (w) / (z − w) dw` is not proved here.

On the Schwartz functions `g` whose Fourier transform is compactly supported in `ℂ ∖ {0}`
(`HarmonicAnalysis.HasCompactFourierSupportOffZero`, dense in every `L^p`, `1 < p < ∞`, by
`HarmonicAnalysis.exists_tendsto_hasCompactFourierSupportOffZero`), the function
`ξ ↦ (π i ξ)⁻¹ 𝓕 g (ξ)` is smooth with compact support, since `𝓕 g` vanishes near `0`. So `C g` is
a Schwartz function, and the identities follow on the Fourier side, by the injectivity of `𝓕` on
`𝓢(ℂ, ℂ)`, with no estimate of the kernel. On this class the Cauchy transform is the potential
in `HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`
(`HarmonicAnalysis.BeurlingAhlfors.CompactSupport`).

## Main results

* `HarmonicAnalysis.cauchyTransform`: `C g = 𝓕⁻¹ ((π i ξ)⁻¹ 𝓕 g)`.
* `HarmonicAnalysis.exists_schwartzMap_eq_cauchyTransform`: for `g` in that class, `C g` is a
  Schwartz function `f` with `∂̄f = g` and `∂f = 𝓑 g`;
  `HarmonicAnalysis.dzbar_cauchyTransform`, `HarmonicAnalysis.dz_cauchyTransform`: the same with
  the pointwise Wirtinger derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform Real ContDiff

namespace HarmonicAnalysis

/-- The **Cauchy transform** `C g = 𝓕⁻¹ ((π i ξ)⁻¹ 𝓕 g)`, the Fourier multiplier with the symbol
`(π i ξ)⁻¹` of the inverse of `∂̄` (`0` at `ξ = 0`). It is the Cauchy transform
`C g (z) = (1/π) ∫ g (w) / (z − w) dw`, whose kernel `1 / (π z)` has the Fourier transform
`(π i ξ)⁻¹`; that formula is not proved here, and the theory below uses only the Fourier side. -/
def cauchyTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  fourierMultiplier (fun ξ => ((π : ℂ) * Complex.I * ξ)⁻¹) g

variable {g : 𝓢(ℂ, ℂ)}

/-- For `g` with Fourier transform compactly supported in `ℂ ∖ {0}`, `(π i ξ)⁻¹ 𝓕 g (ξ)` is smooth:
off `0` as a product of smooth functions, and near `0` it vanishes. -/
theorem contDiff_inv_smul_fourier (hg : HasCompactFourierSupportOffZero g) :
    ContDiff ℝ ∞ fun ξ : ℂ => ((π : ℂ) * Complex.I * ξ)⁻¹ • 𝓕 (g : ℂ → ℂ) ξ := by
  have hF : ContDiff ℝ ∞ (𝓕 (g : ℂ → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 g).smooth ⊤
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : 𝓕 (g : ℂ → ℂ) =ᶠ[nhds 0] 0 := notMem_tsupport_iff_eventuallyEq.1 hg.2
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [h0] with ξ hξ
    simp [hξ]
  · have hπ : ((π : ℂ) * Complex.I * x) ≠ 0 := by
      simp [Real.pi_ne_zero, hx]
    have hlin : ContDiffAt ℝ ∞ (fun ξ : ℂ => (π : ℂ) * Complex.I * ξ) x := by fun_prop
    exact (hlin.inv hπ).smul hF.contDiffAt

/-- For `g` with Fourier transform compactly supported in `ℂ ∖ {0}`, `(π i ξ)⁻¹ 𝓕 g (ξ)` has
compact support. -/
theorem hasCompactSupport_inv_smul_fourier (hg : HasCompactFourierSupportOffZero g) :
    HasCompactSupport fun ξ : ℂ => ((π : ℂ) * Complex.I * ξ)⁻¹ • 𝓕 (g : ℂ → ℂ) ξ :=
  hg.1.smul_left (f := fun ξ : ℂ => ((π : ℂ) * Complex.I * ξ)⁻¹)

/-- For `g` with Fourier transform compactly supported in `ℂ ∖ {0}`, the Cauchy transform `C g` is a
Schwartz function `f`, with `𝓕 f (ξ) = (π i ξ)⁻¹ 𝓕 g (ξ)`, `∂̄f = g` and `∂f = 𝓑 g`: `f` is the
inverse Fourier transform of the smooth compactly supported function `(π i ξ)⁻¹ 𝓕 g`;
`𝓕 (∂̄f) = π i ξ (π i ξ)⁻¹ 𝓕 g = 𝓕 g` (`𝓕 g` vanishes at `0`) and the injectivity of `𝓕` on
`𝓢(ℂ, ℂ)` give `∂̄f = g`, and `𝓑 (∂̄f) = ∂f` (`HarmonicAnalysis.beurlingPow_dzbarCLM_pow`) gives
`∂f = 𝓑 g`. -/
theorem exists_schwartzMap_eq_cauchyTransform (hg : HasCompactFourierSupportOffZero g) :
    ∃ f : 𝓢(ℂ, ℂ), ⇑f = cauchyTransform g ∧
      (∀ ξ, 𝓕 (f : ℂ → ℂ) ξ = ((π : ℂ) * Complex.I * ξ)⁻¹ * 𝓕 (g : ℂ → ℂ) ξ) ∧
      dzbarCLM f = g ∧ ⇑(dzCLM f) = beurlingPow 1 g := by
  set S : 𝓢(ℂ, ℂ) :=
    (hasCompactSupport_inv_smul_fourier hg).toSchwartzMap (contDiff_inv_smul_fourier hg)
  have hS : ∀ ξ, S ξ = ((π : ℂ) * Complex.I * ξ)⁻¹ * 𝓕 (g : ℂ → ℂ) ξ := fun _ => rfl
  set f : 𝓢(ℂ, ℂ) := 𝓕⁻ S
  have hfS : 𝓕 f = S := FourierTransform.fourier_fourierInv_eq S
  have hf : ∀ ξ, 𝓕 (f : ℂ → ℂ) ξ = ((π : ℂ) * Complex.I * ξ)⁻¹ * 𝓕 (g : ℂ → ℂ) ξ := fun ξ => by
    rw [← SchwartzMap.fourier_coe, hfS, hS]
  -- `𝓕 (∂̄f) = 𝓕 g`
  have hg0 : 𝓕 (g : ℂ → ℂ) 0 = 0 := image_eq_zero_of_notMem_tsupport hg.2
  have hfour : 𝓕 (dzbarCLM f) = 𝓕 g := by
    ext ξ
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, fourier_dzbarCLM, hf, smul_eq_mul,
      ← mul_assoc]
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp [hg0]
    · rw [mul_inv_cancel₀ (by simp [Real.pi_ne_zero, hξ]), one_mul]
  have hinv : ∀ h : 𝓢(ℂ, ℂ), 𝓕⁻ (𝓕 h) = h := FourierTransform.fourierInv_fourier_eq
  have hdzbar : dzbarCLM f = g := by
    rw [← hinv (dzbarCLM f), hfour, hinv]
  refine ⟨f, ?_, hf, hdzbar, ?_⟩
  · rw [SchwartzMap.fourierInv_coe]
    rfl
  · have h := beurlingPow_dzbarCLM_pow 1 f
    simp only [pow_one] at h
    rw [← h, hdzbar]

/-- `∂̄ (C g) = g` for `g` with Fourier transform compactly supported in `ℂ ∖ {0}`. -/
theorem dzbar_cauchyTransform (hg : HasCompactFourierSupportOffZero g) :
    dzbar (cauchyTransform g) = g := by
  obtain ⟨f, hf, -, hdzbar, -⟩ := exists_schwartzMap_eq_cauchyTransform hg
  funext z
  rw [← hf, ← dzbarCLM_apply, hdzbar]

/-- `∂ (C g) = 𝓑 g` for `g` with Fourier transform compactly supported in `ℂ ∖ {0}`. -/
theorem dz_cauchyTransform (hg : HasCompactFourierSupportOffZero g) :
    dz (cauchyTransform g) = beurlingPow 1 g := by
  obtain ⟨f, hf, -, -, hdz⟩ := exists_schwartzMap_eq_cauchyTransform hg
  funext z
  rw [← hf, ← dzCLM_apply, hdz]

end HarmonicAnalysis
