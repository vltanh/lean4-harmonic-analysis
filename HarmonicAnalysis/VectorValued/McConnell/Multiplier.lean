/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.McConnell.Chain
public import HarmonicAnalysis.VectorValued.McConnell.Kernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Mihlin multipliers on UMD spaces

**Theorem** (`exists_eLpNorm_fourierInv_mihlin_le`; T. R. McConnell, *On Fourier multiplier
transformations of Banach-valued functions*, Trans. Amer. Math. Soc. 285 (1984), 739–757, Theorem
1.1, for `n = 1`). Let `X` be a complex UMD space with the `UMD_p` constant `β`, `1 < p < ∞`. If `m`
is of class `C²` on `ℝ ∖ {0}` with `|ξ|^k |m^{(k)} (ξ)| ≤ c`, `k ≤ 2`, then
`‖𝓕⁻ (m G)‖_{L^p (ℝ; X)} ≤ C c β² ‖𝓕⁻ G‖_{L^p (ℝ; X)}` for `G ∈ L¹ (ℝ; X)`, with an absolute
constant `C`.

## The proof

The proof is McConnell's, pp. 746–751. Let first `m` have compact support in `ℝ ∖ {0}`, let `u` and
`v` be the Poisson integrals of `f = 𝓕⁻ G` and of `𝓕⁻ m`. Then (3.3)

`T_m f (x) = −32 ∫_0^∞ ∫ y² v_{yy} (s, y) u_y (x − s, 3y) ds dy`.

The truncation `T_m^A f`, the integral over `0 < y < A` with the factor `−32`, is the limit of
`−16 g_N`, where (3.5)

`g_N (x) = Σ_i ∫ y_i² v_{yy} (s, y_i) [u (x − s, 2y_{i+1} + y_i) − u (x − s, 3y_i)] ds`, and for
these there is the representation (3.9)

`g_N (x) = Ẽ⁰ E^x Σ_i e (X̃ (y_i), y_i) (Δu)_i`,
`(Δu)_i = u (X (y_{i+1}) − X̃ (y_i), y_{i+1} + y_i) − u (X (y_i) − X̃ (y_i), 2y_i)`,

with two independent chains `X`, `X̃` (`Chain.lean`) and the bounded function
`e = y² v_{yy} / h` (`Kernel.lean`). For fixed `X̃` the `(Δu)_i` are martingale differences under
`P_{(x', A)}`; Burkholder's inequality removes the `e (X̃ (y_i), y_i)`, Lemma 3.2 replaces the two
chains by one chain with the heights `2y_0, y_0 + y_1, 2y_1, …`, and a second use of Burkholder's
inequality, with coefficients `0` and `1`, leaves `f (X (0)) − u (X (z), z)`, `z = 2 y_N`.

The source works with functions `f` of compact support and values in a finite-dimensional subspace,
and reduces the theorem to smooth `m`; here `f = 𝓕⁻ G` with `G ∈ L¹`, and `C²` is enough, since the
representation (3.3) and the limit of the Riemann sums are read on the Fourier side.
-/

@[expose] public section

open MeasureTheory Filter BanachProbability
open scoped ENNReal FourierTransform Topology

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Multipliers with compact support in `ℝ ∖ {0}` -/

/-- `t = 2π|ξ|`, so that `e^{−ty}` is the multiplier of the Poisson integral. -/
private noncomputable def freq (ξ : ℝ) : ℝ :=
  2 * Real.pi * |ξ|

private theorem freq_nonneg (ξ : ℝ) : 0 ≤ freq ξ := by
  unfold freq
  positivity

private theorem freq_pos {ξ : ℝ} (hξ : ξ ≠ 0) : 0 < freq ξ := by
  unfold freq
  positivity

private theorem continuous_freq : Continuous freq := by
  unfold freq
  fun_prop

/-- A multiplier with compact support in `ℝ ∖ {0}` is continuous. -/
private theorem continuous_of_isMihlin {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (h0 : (0 : ℝ) ∉ tsupport m) : Continuous m := by
  refine continuous_of_tsupport fun ξ hξ => ?_
  have hξ0 : ξ ∈ ({0}ᶜ : Set ℝ) := fun h => h0 (by rwa [Set.mem_singleton_iff.1 h] at hξ)
  exact hm.1.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hξ0)

/-- (1.10) for `k = 0`. -/
private theorem norm_le_of_isMihlin {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖m ξ‖ ≤ c := by
  simpa using hm.2 0 (by norm_num) ξ hξ

private theorem nonneg_of_isMihlin {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) : 0 ≤ c :=
  (norm_nonneg _).trans (norm_le_of_isMihlin hm one_ne_zero)

private theorem ae_ne_zero : ∀ᵐ ξ : ℝ, ξ ≠ 0 :=
  compl_mem_ae_iff.2 (measure_singleton 0)

/-- The multipliers `m (ξ) a (2π|ξ|)`, `a` continuous and bounded, act on `L¹`. -/
private theorem integrable_symbol_smul {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) {a : ℝ → ℝ} (ha : Continuous a)
    {C : ℝ} (hC : ∀ t, 0 ≤ t → |a t| ≤ C) :
    Integrable fun ξ => (m ξ * (a (freq ξ) : ℂ)) • G ξ := by
  refine hG.bdd_smul (c * C) ((continuous_of_isMihlin hm h0).mul (Complex.continuous_ofReal.comp
    (ha.comp continuous_freq))).aestronglyMeasurable (ae_ne_zero.mono fun ξ hξ => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul (norm_le_of_isMihlin hm hξ) (hC _ (freq_nonneg ξ)) (norm_nonneg _)
    (nonneg_of_isMihlin hm)

/-- A multiplier with compact support, times a power of `t`, is bounded. -/
private theorem exists_norm_mul_freq_pow_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) (k : ℕ) :
    ∃ M, ∀ ξ, ‖m ξ‖ * freq ξ ^ k ≤ M := by
  have hcont : Continuous fun ξ => ‖m ξ‖ * freq ξ ^ k :=
    (continuous_of_isMihlin hm h0).norm.mul (continuous_freq.pow k)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support (hs.norm.mul_right)
  exact ⟨M, fun ξ => (le_abs_self _).trans (hM ξ)⟩

/-! ### Convolution with the kernel -/

/-- The Cauchy density is integrable. -/
private theorem integrable_cauchyDensity {y : ℝ} (hy : 0 < y) : Integrable (cauchyDensity y) := by
  refine (lintegral_ofReal_ne_top_iff_integrable
    (continuous_cauchyDensity hy).aestronglyMeasurable
    (ae_of_all _ fun s => (cauchyDensity_pos hy s).le)).1 ?_
  have h := measure_univ (μ := cauchyLaw y)
  rw [cauchyLaw_of_pos hy, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  rw [h]
  exact ENNReal.one_ne_top

/-- The symbol of the kernel `v_{yy} (·, y)`. -/
private noncomputable def kernelSymbol (m : ℝ → ℂ) (y ξ : ℝ) : ℂ :=
  m ξ * ((freq ξ ^ 2 * Real.exp (-(freq ξ * y)) : ℝ) : ℂ)

private theorem mihlinKernel_eq (m : ℝ → ℂ) (y : ℝ) :
    mihlinKernel m y = 𝓕⁻ (kernelSymbol m y) := rfl

private theorem continuous_kernelSymbol {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (h0 : (0 : ℝ) ∉ tsupport m) (y : ℝ) : Continuous (kernelSymbol m y) := by
  have h1 := continuous_of_isMihlin hm h0
  have h2 := continuous_freq
  unfold kernelSymbol
  fun_prop

private theorem integrable_kernelSymbol {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) (y : ℝ) :
    Integrable (kernelSymbol m y) :=
  (continuous_kernelSymbol hm h0 y).integrable_of_hasCompactSupport hs.mul_right

/-- The kernel is integrable, by Lemma 3.1. -/
private theorem integrable_mihlinKernel {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {y : ℝ} (hy : 0 < y) :
    Integrable (mihlinKernel m y) := by
  refine ((integrable_cauchyDensity hy).const_mul (17 * c / y ^ 2)).mono'
    (continuous_mihlinKernel hm hs h0 y).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  have h := norm_mihlinKernel_le hm hs h0 hy s
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
  exact h

/-- `∫ K (s) e_v (x − s) ds = e_v (x) K̂ (v)`. -/
private theorem integral_mul_expChar_sub (K : ℝ → ℂ) (x v : ℝ) :
    ∫ s, K s * expChar v (x - s) = expChar v x * 𝓕 K v := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [smul_eq_mul, expChar]
  rw [← mul_assoc (Complex.exp _), ← Complex.exp_add, mul_comm]
  push_cast
  ring_nf

/-- The convolution of `𝓕⁻ φ` with `𝓕⁻ H` on the Fourier side, by Fubini's theorem and the Fourier
inversion theorem. This replaces (3.4) of McConnell (1984), the semigroup property of the Poisson
integrals of `f`, `M` and `M * f`, and its derivatives in `y`. -/
private theorem integral_fourierInv_smul_fourierInv [CompleteSpace X] {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hφi : Integrable φ) (hK : Integrable (𝓕⁻ φ)) {H : ℝ → X}
    (hH : Integrable H) (x : ℝ) :
    ∫ s, 𝓕⁻ φ s • 𝓕⁻ H (x - s) = 𝓕⁻ (fun ξ => φ ξ • H ξ) x := by
  have hint : Integrable (Function.uncurry fun s v : ℝ =>
      (𝓕⁻ φ s * expChar v (x - s)) • H v) (volume.prod volume) := by
    have h := (hK.smul_prod hH).bdd_smul 1 (φ := fun p : ℝ × ℝ => expChar p.2 (x - p.1))
      (by unfold expChar; fun_prop : Continuous fun p : ℝ × ℝ =>
        expChar p.2 (x - p.1)).aestronglyMeasurable
      (ae_of_all _ fun p => (norm_expChar _ _).le)
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [Pi.smul_apply', Function.uncurry, smul_smul]
    rw [mul_comm]
  have h1 : ∫ s, 𝓕⁻ φ s • 𝓕⁻ H (x - s) =
      ∫ s, ∫ v, (𝓕⁻ φ s * expChar v (x - s)) • H v := by
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only
    rw [fourierInv_eq_expChar H, ← integral_smul]
    simp only [smul_smul]
  have hinv : 𝓕 (𝓕⁻ φ) = φ := by
    refine hφ.fourier_fourierInv_eq hφi ?_
    have h : 𝓕 φ = fun ξ => 𝓕⁻ φ (-ξ) := funext fun ξ => by
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [h]
    exact hK.comp_neg
  rw [h1, integral_integral_swap hint, fourierInv_eq_expChar]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [integral_smul_const, integral_mul_expChar_sub, hinv, mul_smul]

/-- The convolution of `y² v_{yy} (·, y)` with `𝓕⁻ H` on the Fourier side; both sides are `0` for
`y = 0`. -/
private theorem integral_mihlinKernel_smul [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {y : ℝ}
    (hy : 0 ≤ y) {H : ℝ → X} (hH : Integrable H) (x : ℝ) :
    ∫ s, ((y : ℂ) ^ 2 * mihlinKernel m y s) • 𝓕⁻ H (x - s) =
      𝓕⁻ (fun ξ => ((y : ℂ) ^ 2 * kernelSymbol m y ξ) • H ξ) x := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [Real.fourierInv_eq']
  · have h := integral_fourierInv_smul_fourierInv (continuous_kernelSymbol hm h0 y)
      (integrable_kernelSymbol hm hs h0 y) (integrable_mihlinKernel hm hs h0 hy) hH x
    simp only [mul_smul, fourierInv_eq_expChar (fun ξ => (y : ℂ) ^ 2 • kernelSymbol m y ξ • H ξ)]
    simp only [fourierInv_eq_expChar (fun ξ => kernelSymbol m y ξ • H ξ)] at h
    rw [integral_smul, mihlinKernel_eq, h, ← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun ξ => smul_comm _ _ _)

/-! ### The representation (3.3) and its Riemann sums -/

/-- The inverse Fourier transform of `−2π|ξ| e^{−2π|ξ|y} G`, which is `u_y (·, y)` for `y > 0`: `u`
is the Poisson integral of `f = 𝓕⁻ G`. -/
noncomputable def poissonDeriv (G : ℝ → X) (y : ℝ) : ℝ → X :=
  𝓕⁻ fun ξ => ((-(2 * Real.pi * |ξ|) * Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ) • G ξ

/-- `T_m^A f (x) = −32 ∫_0^A ∫ y² v_{yy} (s, y) u_y (x − s, 3y) ds dy` (McConnell (1984), p. 747,
for `n = 1`). -/
noncomputable def truncatedMultiplier (m : ℝ → ℂ) (G : ℝ → X) (A x : ℝ) : X :=
  (-32 : ℂ) • ∫ y in (0)..A, ∫ s,
    ((y : ℂ) ^ 2 * mihlinKernel m y s) • poissonDeriv G (3 * y) (x - s)

/-- The symbol of `T_m^A` for `m = 1`, `32 ∫_0^A y² t³ e^{−4ty} dy` with `t = 2π|ξ|`. -/
private noncomputable def truncSymbol (A t : ℝ) : ℝ :=
  ∫ y in (0)..A, 32 * (y ^ 2 * t ^ 3 * Real.exp (-(4 * t * y)))

/-- The source integrates `T_m f (x) = −∫_0^∞ w_y (x, y) dy`, `w` the Poisson integral of `T_m f`,
by parts `n + 1` times, and substitutes `y → 4y` (McConnell (1984), pp. 746–747). Here the same
computation is made for the exponentials `e^{−ty}` on the Fourier side. -/
private theorem truncSymbol_eq (A t : ℝ) : truncSymbol A t =
    1 - Real.exp (-(4 * t * A)) * (1 + 4 * t * A + (4 * t * A) ^ 2 / 2) := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun y => -(Real.exp (-(4 * t * y)) * (1 + 4 * t * y + (4 * t * y) ^ 2 / 2)))
      (32 * (y ^ 2 * t ^ 3 * Real.exp (-(4 * t * y)))) y := fun y => by
    have h1 : HasDerivAt (fun y : ℝ => 4 * t * y) (4 * t) y := by
      simpa using (hasDerivAt_id y).const_mul (4 * t)
    have h2 := h1.neg.exp.mul ((h1.const_add 1).add ((h1.pow 2).div_const 2))
    refine h2.neg.congr_deriv ?_
    simp only [Pi.neg_apply, Pi.add_apply, Pi.pow_apply]
    push_cast
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := A)
    (fun y _ => hderiv y) (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [truncSymbol, h]
  simp
  ring

private theorem truncSymbol_nonneg {A t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) : 0 ≤ truncSymbol A t :=
  intervalIntegral.integral_nonneg hA fun y _ => by positivity

private theorem truncSymbol_le_one {A t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) : truncSymbol A t ≤ 1 := by
  rw [truncSymbol_eq]
  have h : 0 ≤ Real.exp (-(4 * t * A)) * (1 + 4 * t * A + (4 * t * A) ^ 2 / 2) := by positivity
  linarith

private theorem continuous_truncSymbol (A : ℝ) : Continuous (truncSymbol A) := by
  rw [funext (truncSymbol_eq A)]
  fun_prop

/-- `32 ∫_0^∞ y² t³ e^{−4ty} dy = 1`. -/
private theorem tendsto_truncSymbol {t : ℝ} (ht : 0 < t) :
    Tendsto (fun A => truncSymbol A t) atTop (𝓝 1) := by
  have h0 : Tendsto (fun W : ℝ => 1 - (W ^ 0 * Real.exp (-W) + W ^ 1 * Real.exp (-W) +
      W ^ 2 * Real.exp (-W) / 2)) atTop (𝓝 (1 - (0 + 0 + 0 / 2))) :=
    (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).add
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)).add
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).div_const 2)).const_sub 1
  have h1 : Tendsto (fun A : ℝ => 4 * t * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have h2 := h0.comp h1
  rw [zero_div, add_zero, add_zero, sub_zero] at h2
  refine h2.congr fun A => ?_
  rw [truncSymbol_eq, Function.comp_apply]
  ring

/-- `t e^{−ty} ≤ 1 / y`. -/
private theorem freq_mul_exp_le {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    freq ξ * Real.exp (-(freq ξ * y)) ≤ y⁻¹ := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), inv_mul_eq_div,
    le_div_iff₀ hy]
  linarith [Real.add_one_le_exp (freq ξ * y)]

/-- The symbol of `u_y (·, y)` is integrable. -/
private theorem integrable_poissonDerivSymbol {G : ℝ → X} (hG : Integrable G) {y : ℝ}
    (hy : 0 < y) :
    Integrable fun ξ => ((-freq ξ * Real.exp (-(freq ξ * y)) : ℝ) : ℂ) • G ξ := by
  have hfreq := continuous_freq
  refine hG.bdd_smul y⁻¹ (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun ξ => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (freq_nonneg ξ),
    Real.abs_exp]
  exact freq_mul_exp_le hy ξ

/-- McConnell (1984), p. 747: the inner integral in (3.3) is `y² w_{yyy} (x, 4y)`. -/
private theorem integral_mihlinKernel_smul_poissonDeriv [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ∫ s, ((y : ℂ) ^ 2 * mihlinKernel m y s) • poissonDeriv G (3 * y) (x - s) =
      ∫ ξ, (expChar ξ x * (m ξ * ((-(y ^ 2 * freq ξ ^ 3 * Real.exp (-(4 * freq ξ * y))) : ℝ) :
        ℂ))) • G ξ := by
  have h := integral_mihlinKernel_smul hm hs h0 hy.le
    (integrable_poissonDerivSymbol hG (y := 3 * y) (by positivity)) x
  refine h.trans ?_
  rw [fourierInv_eq_expChar]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [smul_smul, kernelSymbol]
  congr 1
  rw [show -(4 * freq ξ * y) = -(freq ξ * y) + -(freq ξ * (3 * y)) by ring, Real.exp_add]
  push_cast
  ring

/-- The integrability for Fubini's theorem in (3.3), where `m` has compact support. -/
private theorem integrable_truncated {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G)
    (A x : ℝ) :
    Integrable (Function.uncurry fun y ξ : ℝ =>
      (expChar ξ x * (m ξ * ((-(y ^ 2 * freq ξ ^ 3 * Real.exp (-(4 * freq ξ * y))) : ℝ) :
        ℂ))) • G ξ) ((volume.restrict (Set.Ioc 0 A)).prod volume) := by
  obtain ⟨M, hM⟩ := exists_norm_mul_freq_pow_le hm hs h0 3
  have hmc := continuous_of_isMihlin hm h0
  have hfreq := continuous_freq
  have hsnd : Integrable (fun p : ℝ × ℝ => G p.2)
      ((volume.restrict (Set.Ioc 0 A)).prod volume) := hG.comp_snd _
  refine hsnd.bdd_smul (A ^ 2 * M) (Continuous.aestronglyMeasurable ?_) ?_
  · unfold expChar
    fun_prop
  · have hmem : ∀ᵐ p ∂(volume.restrict (Set.Ioc 0 A)).prod (volume : Measure ℝ),
        p.1 ∈ Set.Ioc 0 A := by
      refine Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    have hp1 : p.1 ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hp.1.le hp.2 2
    have hexp : Real.exp (-(4 * freq p.2 * p.1)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have := mul_nonneg (freq_nonneg p.2) hp.1.le
      linarith)
    have hf := pow_nonneg (freq_nonneg p.2) 3
    rw [norm_mul, norm_expChar, one_mul, norm_mul, Complex.norm_real, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    calc ‖m p.2‖ * (p.1 ^ 2 * freq p.2 ^ 3 * Real.exp (-(4 * freq p.2 * p.1)))
        ≤ ‖m p.2‖ * (A ^ 2 * freq p.2 ^ 3 * 1) := by gcongr
      _ = A ^ 2 * (‖m p.2‖ * freq p.2 ^ 3) := by ring
      _ ≤ A ^ 2 * M := by
        gcongr
        exact hM _

/-- `T_m^A` on the Fourier side: its symbol is `32 m (ξ) ∫_0^A y² t³ e^{−4ty} dy`, `t = 2π|ξ|`. -/
private theorem truncatedMultiplier_eq [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) {A : ℝ}
    (hA : 0 ≤ A) (x : ℝ) : truncatedMultiplier m G A x =
      𝓕⁻ (fun ξ => (m ξ * (truncSymbol A (freq ξ) : ℂ)) • G ξ) x := by
  rw [truncatedMultiplier, intervalIntegral.integral_of_le hA,
    setIntegral_congr_fun measurableSet_Ioc fun y hy =>
      integral_mihlinKernel_smul_poissonDeriv hm hs h0 hG hy.1 x,
    integral_integral_swap (integrable_truncated hm hs h0 hG A x), fourierInv_eq_expChar,
    ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only
  rw [integral_smul_const, integral_const_mul, integral_const_mul, integral_complex_ofReal,
    smul_smul, smul_smul, integral_neg, ← intervalIntegral.integral_of_le hA, truncSymbol,
    intervalIntegral.integral_const_mul]
  congr 1
  push_cast
  ring

/-- Bounded measurable multipliers converging almost everywhere: the inverse Fourier transforms
converge pointwise. -/
private theorem tendsto_fourierInv_of_dominated {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {G : ℝ → X} (hG : Integrable G) {a : ι → ℝ → ℂ} {b : ℝ → ℂ} {C : ℝ}
    (ha : ∀ᶠ i in l, AEStronglyMeasurable (a i)) (hC : ∀ᶠ i in l, ∀ᵐ ξ, ‖a i ξ‖ ≤ C)
    (hlim : ∀ᵐ ξ, Tendsto (fun i => a i ξ) l (𝓝 (b ξ))) (x : ℝ) :
    Tendsto (fun i => 𝓕⁻ (fun ξ => a i ξ • G ξ) x) l (𝓝 (𝓕⁻ (fun ξ => b ξ • G ξ) x)) := by
  simp only [fourierInv_eq_expChar]
  refine tendsto_integral_filter_of_dominated_convergence (fun ξ => C * ‖G ξ‖) ?_ ?_
    (hG.norm.const_mul C) ?_
  · filter_upwards [ha, hC] with i hi hCi
    exact (integrable_expChar_smul (hG.bdd_smul C hi hCi) x).aestronglyMeasurable
  · filter_upwards [hC] with i hCi
    filter_upwards [hCi] with ξ hξ
    rw [norm_smul, norm_expChar, one_mul, norm_smul]
    exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
  · filter_upwards [hlim] with ξ hξ
    exact (hξ.smul_const _).const_smul _

/-- McConnell (1984), (3.3), for `n = 1`: `T_m^A f (x) → T_m f (x)` as `A → ∞`. -/
theorem tendsto_truncatedMultiplier [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) (x : ℝ) :
    Tendsto (fun A => truncatedMultiplier m G A x) atTop (𝓝 (𝓕⁻ (fun ξ => m ξ • G ξ) x)) := by
  have hmc := continuous_of_isMihlin hm h0
  have hlim : Tendsto (fun A => 𝓕⁻ (fun ξ => (m ξ * (truncSymbol A (freq ξ) : ℂ)) • G ξ) x) atTop
      (𝓝 (𝓕⁻ (fun ξ => m ξ • G ξ) x)) := by
    refine tendsto_fourierInv_of_dominated hG (C := c) (Eventually.of_forall fun A => ?_) ?_ ?_ x
    · exact (hmc.mul (Complex.continuous_ofReal.comp
        ((continuous_truncSymbol A).comp continuous_freq))).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 0] with A hA
      filter_upwards [ae_ne_zero] with ξ hξ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (truncSymbol_nonneg hA (freq_nonneg ξ))]
      exact (mul_le_of_le_one_right (norm_nonneg _)
        (truncSymbol_le_one hA (freq_nonneg ξ))).trans (norm_le_of_isMihlin hm hξ)
    · filter_upwards [ae_ne_zero] with ξ hξ
      simpa using ((tendsto_truncSymbol (freq_pos hξ)).ofReal).const_mul (m ξ)
  exact hlim.congr' ((eventually_ge_atTop 0).mono fun A hA =>
    (truncatedMultiplier_eq hm hs h0 hG hA x).symm)

/-- McConnell (1984), (3.5): `g_N (x) = Σ_i ∫ y_i² v_{yy} (s, y_i) [u (x − s, 2y_{i+1} + y_i) −
u (x − s, 3y_i)] ds`, for `n = 1`. -/
noncomputable def mihlinRiemannSum (m : ℝ → ℂ) (G : ℝ → X) (y : ℕ → ℝ) (N : ℕ) (x : ℝ) : X :=
  ∑ i ∈ Finset.range N, ∫ s, ((y i : ℂ) ^ 2 * mihlinKernel m (y i) s) •
    (poissonInt G (2 * y (i + 1) + y i) (x - s) - poissonInt G (3 * y i) (x - s))

/-- The symbol of `g_N` for `m = 1`, `t = 2π|ξ|`. -/
private noncomputable def riemannSymbol (y : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, y i ^ 2 * (t ^ 2 * Real.exp (-(t * y i))) *
    (Real.exp (-(t * (2 * y (i + 1) + y i))) - Real.exp (-(t * (3 * y i))))

private theorem continuous_riemannSymbol (y : ℕ → ℝ) (N : ℕ) : Continuous (riemannSymbol y N) := by
  unfold riemannSymbol
  fun_prop

/-- The symbol of the Poisson integral is integrable. -/
private theorem integrable_poissonSymbol {G : ℝ → X} (hG : Integrable G) {y : ℝ} (hy : 0 ≤ y) :
    Integrable fun ξ => ((Real.exp (-(freq ξ * y)) : ℝ) : ℂ) • G ξ := by
  have hfreq := continuous_freq
  refine hG.bdd_smul 1 (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun ξ => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
  have := mul_nonneg (freq_nonneg ξ) hy
  linarith

/-- The differences of Poisson integrals on the Fourier side. -/
private theorem poissonInt_sub_poissonInt {G : ℝ → X} (hG : Integrable G) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (z : ℝ) : poissonInt G a z - poissonInt G b z =
      𝓕⁻ (fun ξ => ((Real.exp (-(freq ξ * a)) : ℝ) : ℂ) • G ξ -
        ((Real.exp (-(freq ξ * b)) : ℝ) : ℂ) • G ξ) z := by
  rw [poissonInt, poissonInt]
  simp only [fourierInv_eq_expChar, smul_sub]
  exact (integral_sub (integrable_expChar_smul (integrable_poissonSymbol hG ha) z)
    (integrable_expChar_smul (integrable_poissonSymbol hG hb) z)).symm

/-- The terms of (3.5) on the Fourier side. -/
private theorem integral_mihlinKernel_smul_poissonInt_sub [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y a b : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) :
    ∫ s, ((y : ℂ) ^ 2 * mihlinKernel m y s) • (poissonInt G a (x - s) - poissonInt G b (x - s)) =
      ∫ ξ, expChar ξ x • (m ξ * ((y ^ 2 * (freq ξ ^ 2 * Real.exp (-(freq ξ * y))) *
        (Real.exp (-(freq ξ * a)) - Real.exp (-(freq ξ * b))) : ℝ) : ℂ)) • G ξ := by
  have hH := (integrable_poissonSymbol hG ha).sub (integrable_poissonSymbol hG hb)
  simp only [poissonInt_sub_poissonInt hG ha hb]
  refine (integral_mihlinKernel_smul hm hs h0 hy hH x).trans ?_
  rw [fourierInv_eq_expChar]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [Pi.sub_apply, ← sub_smul, smul_smul, kernelSymbol]
  congr 1
  push_cast
  ring

/-- The terms of `riemannSymbol` are bounded. -/
private theorem abs_riemann_term_le {t y a b : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : |y ^ 2 * (t ^ 2 * Real.exp (-(t * y))) *
      (Real.exp (-(t * a)) - Real.exp (-(t * b)))| ≤ 2 := by
  have hexp : ∀ a : ℝ, 0 ≤ a → Real.exp (-(t * a)) ≤ 1 := fun a ha =>
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ht ha))
  have h1 : y ^ 2 * (t ^ 2 * Real.exp (-(t * y))) ≤ 2 := by
    have h1 := Real.quadratic_le_exp_of_nonneg (mul_nonneg ht hy)
    have h2 : 0 ≤ t * y := mul_nonneg ht hy
    rw [← mul_assoc, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith
  have h2 : |Real.exp (-(t * a)) - Real.exp (-(t * b))| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos (-(t * a)), Real.exp_pos (-(t * b)), hexp a ha,
      hexp b hb]
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact (mul_le_mul h1 h2 (abs_nonneg _) zero_le_two).trans_eq (mul_one 2)

/-- A crude bound; it is used only for the continuity of `g_N`. -/
private theorem abs_riemannSymbol_le {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : |riemannSymbol y N t| ≤ N * 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ =>
    abs_riemann_term_le ht (hy i) (by linarith [hy i, hy (i + 1)]) (by linarith [hy i])).trans_eq
    ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- (3.5) on the Fourier side. -/
private theorem mihlinRiemannSum_eq [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G)
    {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (N : ℕ) (x : ℝ) : mihlinRiemannSum m G y N x =
      𝓕⁻ (fun ξ => (m ξ * (riemannSymbol y N (freq ξ) : ℂ)) • G ξ) x := by
  have hterm := fun i => integral_mihlinKernel_smul_poissonInt_sub hm hs h0 hG (hy i)
    (a := 2 * y (i + 1) + y i) (b := 3 * y i)
    (by linarith [hy (i + 1), hy i]) (by linarith [hy i]) x
  rw [mihlinRiemannSum, Finset.sum_congr rfl fun i _ => hterm i, ← integral_finsetSum,
    fourierInv_eq_expChar]
  · refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [riemannSymbol, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_smul, Finset.smul_sum]
  · intro i _
    exact integrable_expChar_smul (integrable_symbol_smul hm h0 hG
      (a := fun t => y i ^ 2 * (t ^ 2 * Real.exp (-(t * y i))) *
        (Real.exp (-(t * (2 * y (i + 1) + y i))) - Real.exp (-(t * (3 * y i))))) (by fun_prop)
      fun t ht => abs_riemann_term_le ht (hy i) (by linarith [hy (i + 1), hy i])
        (by linarith [hy i])) x

/-- `g_N` is continuous. -/
private theorem continuous_mihlinRiemannSum [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (N : ℕ) :
    Continuous (mihlinRiemannSum m G y N) := by
  rw [funext (mihlinRiemannSum_eq hm hs h0 hG hy N)]
  exact continuous_fourierInv_of_integrable (integrable_symbol_smul hm h0 hG
    (continuous_riemannSymbol y N) fun t ht => abs_riemannSymbol_le hy N ht)

/-- The mean value estimate of McConnell (1984), p. 747, for the function `y² e^{−2ty}`. -/
private theorem abs_sq_mul_exp_sub_le {A a y t : ℝ} (ha : 0 ≤ a) (hay : a ≤ y) (hyA : y ≤ A)
    (ht : 0 ≤ t) :
    |y ^ 2 * Real.exp (-(2 * t * y)) - a ^ 2 * Real.exp (-(2 * t * a))| ≤
      (2 * A + 2 * A ^ 2 * t) * (y - a) := by
  have hderiv : ∀ η : ℝ, HasDerivAt (fun η => η ^ 2 * Real.exp (-(2 * t * η)))
      ((2 * η - 2 * t * η ^ 2) * Real.exp (-(2 * t * η))) η := fun η => by
    have h1 : HasDerivAt (fun η : ℝ => 2 * t * η) (2 * t) η := by
      simpa using (hasDerivAt_id η).const_mul (2 * t)
    refine ((hasDerivAt_pow 2 η).mul h1.neg.exp).congr_deriv ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  refine norm_image_sub_le_of_norm_deriv_le_segment' (E := ℝ) (a := a) (b := y)
    (fun η _ => (hderiv η).hasDerivWithinAt) (fun η hη => ?_) y (Set.right_mem_Icc.2 hay)
  have hη0 : 0 ≤ η := ha.trans hη.1
  have hηA : η ≤ A := hη.2.le.trans hyA
  have h1 : Real.exp (-(2 * t * η)) ≤ 1 := Real.exp_le_one_iff.2 (by
    nlinarith [mul_nonneg ht hη0])
  have h2 : η ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hη0 hηA 2
  have h3 : |2 * η - 2 * t * η ^ 2| ≤ 2 * A + 2 * A ^ 2 * t := by
    have h4 : t * η ^ 2 ≤ t * A ^ 2 := mul_le_mul_of_nonneg_left h2 ht
    have h5 : 0 ≤ t * η ^ 2 := mul_nonneg ht (sq_nonneg η)
    rw [abs_le]
    constructor <;> linarith
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  exact (mul_le_of_le_one_right (abs_nonneg _) h1).trans h3

/-- `½ ρ (a) [u (2b + a) − u (3a)] = ∫_a^b ρ (a) u_y (a + 2y) dy` for `ρ (y) = y² t² e^{−ty}` and
`u (y) = e^{−ty}` (McConnell (1984), p. 747). -/
private theorem riemann_term_eq (a b t : ℝ) :
    a ^ 2 * (t ^ 2 * Real.exp (-(t * a))) *
        (Real.exp (-(t * (2 * b + a))) - Real.exp (-(t * (3 * a)))) =
      ∫ y in a..b,
        -2 * (a ^ 2 * t ^ 3 * Real.exp (-(2 * t * a)) * Real.exp (-(2 * t * y))) := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y => a ^ 2 * t ^ 2 * Real.exp (-(2 * t * a)) *
      Real.exp (-(2 * t * y)))
      (-2 * (a ^ 2 * t ^ 3 * Real.exp (-(2 * t * a)) * Real.exp (-(2 * t * y)))) y := fun y => by
    have h1 : HasDerivAt (fun y : ℝ => 2 * t * y) (2 * t) y := by
      simpa using (hasDerivAt_id y).const_mul (2 * t)
    refine (h1.neg.exp.const_mul _).congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_sub, mul_assoc, ← Real.exp_add]
  ring_nf

/-- McConnell (1984), p. 747: the error of the Riemann sum on one interval is at most a multiple of
the square of its length. Departure from the source: there the estimate is made for the integrand at
a fixed `s`, with an integrable majorant `γ (s)`, and goes through `∫ ρ (y) u_y (y_i + 2y) dy =
½ ρ (y^*) [u (y_i + 2y_{i+1}) − u (3y_i)]`, the second mean value theorem for integrals, which is
not available for vector-valued `u`. Here the estimate is made for the exponentials on the Fourier
side, and `ρ (y_i) u_y (y_i + 2y)` is compared with `ρ (y) u_y (3y)` under the integral sign. -/
private theorem abs_riemann_term_sub_le {A a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbA : b ≤ A)
    (ht : 0 ≤ t) :
    |a ^ 2 * (t ^ 2 * Real.exp (-(t * a))) *
        (Real.exp (-(t * (2 * b + a))) - Real.exp (-(t * (3 * a)))) -
      ∫ y in a..b, -2 * (y ^ 2 * t ^ 3 * Real.exp (-(4 * t * y)))| ≤
      (4 * A * t ^ 3 + 4 * A ^ 2 * t ^ 4) * (b - a) ^ 2 := by
  have hA : 0 ≤ A := (ha.trans hab).trans hbA
  rw [riemann_term_eq, ← intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (E := ℝ) (a := a) (b := b)
    (C := (4 * A * t ^ 3 + 4 * A ^ 2 * t ^ 4) * (b - a)) fun y hy => ?_).trans_eq ?_
  · rw [Set.uIoc_of_le hab] at hy
    have h4 := abs_sq_mul_exp_sub_le ha hy.1.le (hy.2.trans hbA) ht
    have h5 : -2 * (a ^ 2 * t ^ 3 * Real.exp (-(2 * t * a)) * Real.exp (-(2 * t * y))) -
        -2 * (y ^ 2 * t ^ 3 * Real.exp (-(4 * t * y))) = 2 * t ^ 3 * Real.exp (-(2 * t * y)) *
        (y ^ 2 * Real.exp (-(2 * t * y)) - a ^ 2 * Real.exp (-(2 * t * a))) := by
      rw [show -(4 * t * y) = -(2 * t * y) + -(2 * t * y) by ring, Real.exp_add]
      ring
    have h6 : Real.exp (-(2 * t * y)) ≤ 1 := Real.exp_le_one_iff.2 (by
      nlinarith [mul_nonneg ht (ha.trans hy.1.le)])
    rw [h5, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    calc 2 * t ^ 3 * Real.exp (-(2 * t * y)) *
          |y ^ 2 * Real.exp (-(2 * t * y)) - a ^ 2 * Real.exp (-(2 * t * a))|
        ≤ 2 * t ^ 3 * 1 * ((2 * A + 2 * A ^ 2 * t) * (b - a)) := by
          gcongr
          exact h4.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) (by positivity))
      _ = (4 * A * t ^ 3 + 4 * A ^ 2 * t ^ 4) * (b - a) := by ring
  · rw [abs_of_nonneg (by linarith : 0 ≤ b - a), mul_assoc, ← sq]

/-- McConnell (1984), (3.6): the sum of the errors, for one exponential. -/
private theorem abs_riemannSymbol_sub_le {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) {N : ℕ}
    (hN : 0 < N) :
    |riemannSymbol (fun i => i * A / N) N t - -16⁻¹ * truncSymbol A t| ≤
      (4 * A * t ^ 3 + 4 * A ^ 2 * t ^ 4) * A ^ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set y : ℕ → ℝ := fun i => i * A / N with hydef
  have hy0 : y 0 = 0 := by simp [hydef]
  have hyN : y N = A := by simp [hydef, hN'.ne']
  have hstep : ∀ i, y (i + 1) - y i = A / N := fun i => by
    simp only [hydef]
    push_cast
    ring
  have hint : ∀ a b, IntervalIntegrable
      (fun y : ℝ => -2 * (y ^ 2 * t ^ 3 * Real.exp (-(4 * t * y)))) volume a b := fun a b =>
    Continuous.intervalIntegrable (by fun_prop) _ _
  have h1 : -16⁻¹ * truncSymbol A t = ∑ i ∈ Finset.range N,
      ∫ η in y i..y (i + 1), -2 * (η ^ 2 * t ^ 3 * Real.exp (-(4 * t * η))) := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k _ => hint _ _, hy0, hyN,
      truncSymbol, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun η _ => ?_
    ring
  rw [h1, riemannSymbol, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i hi => ?_).trans_eq
    (b := ∑ i ∈ Finset.range N, (4 * A * t ^ 3 + 4 * A ^ 2 * t ^ 4) * (A / N) ^ 2) ?_)
  · have hyi : 0 ≤ y i := by simp only [hydef]; positivity
    have hle : y (i + 1) ≤ A := by
      simp only [hydef]
      rw [div_le_iff₀ hN', mul_comm]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.mem_range.1 hi) hA.le
    have hpos : 0 ≤ A / N := by positivity
    rw [← hstep i]
    exact abs_riemann_term_sub_le hyi (by linarith [hstep i]) hle ht
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp

/-- McConnell (1984), (3.6): the symbols of the Riemann sums converge. -/
private theorem tendsto_riemannSymbol {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ => riemannSymbol (fun i => i * A / N) N t) atTop
      (𝓝 (-16⁻¹ * truncSymbol A t)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun N =>
    norm_nonneg _) ?_ (tendsto_const_div_atTop_nhds_zero_nat
      ((4 * A * t ^ 3 + 4 * A ^ 2 * t ^ 4) * A ^ 2)))
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact abs_riemannSymbol_sub_le hA ht hN

/-- The symbols of the `g_N` are bounded, since `m` has compact support. -/
private theorem exists_norm_mul_riemannSymbol_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {A : ℝ} (hA : 0 < A) :
    ∃ C, ∀ N : ℕ, 0 < N → ∀ ξ,
      ‖m ξ * (riemannSymbol (fun i => i * A / N) N (freq ξ) : ℂ)‖ ≤ C := by
  obtain ⟨M₀, hM₀⟩ := exists_norm_mul_freq_pow_le hm hs h0 0
  obtain ⟨M₃, hM₃⟩ := exists_norm_mul_freq_pow_le hm hs h0 3
  obtain ⟨M₄, hM₄⟩ := exists_norm_mul_freq_pow_le hm hs h0 4
  refine ⟨M₀ + (4 * A * M₃ + 4 * A ^ 2 * M₄) * A ^ 2, fun N hN ξ => ?_⟩
  have h1 := abs_riemannSymbol_sub_le hA (freq_nonneg ξ) hN
  have h2 := truncSymbol_nonneg hA.le (freq_nonneg ξ)
  have h3 := truncSymbol_le_one hA.le (freq_nonneg ξ)
  have hf := freq_nonneg ξ
  have h4 : (4 * A * freq ξ ^ 3 + 4 * A ^ 2 * freq ξ ^ 4) * A ^ 2 / N ≤
      (4 * A * freq ξ ^ 3 + 4 * A ^ 2 * freq ξ ^ 4) * A ^ 2 :=
    div_le_self (by positivity) (by exact_mod_cast hN)
  have h5 : |riemannSymbol (fun i => i * A / N) N (freq ξ)| ≤
      1 + (4 * A * freq ξ ^ 3 + 4 * A ^ 2 * freq ξ ^ 4) * A ^ 2 := by
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖m ξ‖ * |riemannSymbol (fun i => i * A / N) N (freq ξ)|
      ≤ ‖m ξ‖ * (1 + (4 * A * freq ξ ^ 3 + 4 * A ^ 2 * freq ξ ^ 4) * A ^ 2) := by gcongr
    _ = ‖m ξ‖ * freq ξ ^ 0 +
        (4 * A * (‖m ξ‖ * freq ξ ^ 3) + 4 * A ^ 2 * (‖m ξ‖ * freq ξ ^ 4)) * A ^ 2 := by ring
    _ ≤ M₀ + (4 * A * M₃ + 4 * A ^ 2 * M₄) * A ^ 2 := by
      gcongr
      exacts [hM₀ ξ, hM₃ ξ, hM₄ ξ]

/-- McConnell (1984), (3.5)–(3.6): the Riemann sums for the partition of `[0, A]` in `N` equal parts
converge to `−(1/16) T_m^A f (x)`. (The factor is `2 (n + 1)! (−4)^{−(n + 2)}`; it is misprinted on
pp. 747 and 748. The source takes partitions that refine each other; this is not used.) -/
theorem tendsto_mihlinRiemannSum [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) {A : ℝ}
    (hA : 0 < A) (x : ℝ) :
    Tendsto (fun N : ℕ => mihlinRiemannSum m G (fun i => i * A / N) N x) atTop
      (𝓝 ((-16⁻¹ : ℂ) • truncatedMultiplier m G A x)) := by
  have hmc := continuous_of_isMihlin hm h0
  obtain ⟨C, hC⟩ := exists_norm_mul_riemannSymbol_le hm hs h0 hA
  have h1 := tendsto_fourierInv_of_dominated hG
    (a := fun (N : ℕ) ξ => m ξ * (riemannSymbol (fun i => i * A / N) N (freq ξ) : ℂ))
    (b := fun ξ => (-16⁻¹ : ℂ) * (m ξ * (truncSymbol A (freq ξ) : ℂ)))
    (Eventually.of_forall fun N => (hmc.mul (Complex.continuous_ofReal.comp
      ((continuous_riemannSymbol _ N).comp continuous_freq))).aestronglyMeasurable)
    ((eventually_gt_atTop 0).mono fun N hN => ae_of_all _ (hC N hN))
    (ae_of_all _ fun ξ => by
      have h := ((tendsto_riemannSymbol hA (freq_nonneg ξ)).ofReal).const_mul (m ξ)
      push_cast at h
      rwa [mul_left_comm] at h) x
  have h2 : 𝓕⁻ (fun ξ => ((-16⁻¹ : ℂ) * (m ξ * (truncSymbol A (freq ξ) : ℂ))) • G ξ) x =
      (-16⁻¹ : ℂ) • truncatedMultiplier m G A x := by
    rw [truncatedMultiplier_eq hm hs h0 hG hA.le, fourierInv_eq_expChar, fourierInv_eq_expChar,
      ← integral_smul]
    simp only [mul_smul, smul_comm (expChar _ x)]
  rw [h2] at h1
  exact h1.congr fun N => (mihlinRiemannSum_eq hm hs h0 hG (fun i => by positivity) N x).symm

/-! ### The martingale differences -/

/-- `X (y_N) − X (y_i)`, the sum of the increments `ξ_j`, `j ≥ i`. -/
private def chainTail {N : ℕ} (ξ : Fin N → ℝ) (i : ℕ) : ℝ :=
  ∑ j : Fin N, if i ≤ (j : ℕ) then ξ j else 0

/-- `X (y_N) = X (y_i) + (X (y_N) − X (y_i))`. -/
private theorem chainSum_add_chainTail {N : ℕ} (ξ : Fin N → ℝ) (i : ℕ) :
    chainSum ξ i + chainTail ξ i = chainSum ξ N := by
  unfold chainSum chainTail
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.2
  by_cases h : (j : ℕ) < i
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

/-- `X (y_N) − X (y_i) = ξ_i + (X (y_N) − X (y_{i+1}))`. -/
private theorem chainTail_eq_add {N : ℕ} (ξ : Fin N → ℝ) (i : Fin N) :
    chainTail ξ i = ξ i + chainTail ξ (i + 1) := by
  have h1 := chainSum_add_chainTail ξ i
  have h2 := chainSum_add_chainTail ξ (i + 1)
  rw [chainSum_succ] at h2
  linarith

/-- `X (y_N) − X (y_i)` depends only on the increments with index `≥ i`. -/
private theorem chainTail_congr {N : ℕ} {ξ ξ' : Fin N → ℝ} {i : ℕ}
    (h : ∀ j : Fin N, i ≤ (j : ℕ) → ξ j = ξ' j) : chainTail ξ i = chainTail ξ' i := by
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  exacts [h j hj, rfl]

/-- `X (y_N) − X (y_{i+1})` does not depend on `ξ_i`. -/
private theorem chainTail_update {N : ℕ} (ξ : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    chainTail (Function.update ξ i t) (i + 1) = chainTail ξ (i + 1) :=
  chainTail_congr fun j hj => Function.update_of_ne (by
    rintro rfl
    omega) _ _

private theorem continuous_chainTail {N : ℕ} (i : ℕ) :
    Continuous fun ξ : Fin N → ℝ => chainTail ξ i := by
  have h : (fun ξ : Fin N → ℝ => chainTail ξ i) = fun ξ => chainSum ξ N - chainSum ξ i :=
    funext fun ξ => by linarith [chainSum_add_chainTail ξ i]
  rw [h]
  exact (continuous_chainSum N).sub (continuous_chainSum i)

/-- The martingale differences of the proof, under `P_{(z, A)}`:
`u (X (y_{i+1}), b) − u (X (y_i), a)` with `b − a = y_{i+1} − y_i`. -/
private noncomputable def tailDiff (G : ℝ → X) {N : ℕ} (i : Fin N) (a b z : ℝ)
    (ξ : Fin N → ℝ) : X :=
  poissonInt G b (z - chainTail ξ (i + 1)) - poissonInt G a (z - chainTail ξ i)

private theorem continuous_tailDiff {G : ℝ → X} (hG : Integrable G) {N : ℕ} (i : Fin N) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ) : Continuous (tailDiff G i a b z) :=
  ((continuous_poissonInt hG hb).comp (continuous_const.sub (continuous_chainTail _))).sub
    ((continuous_poissonInt hG ha).comp (continuous_const.sub (continuous_chainTail _)))

private theorem norm_tailDiff_le {G : ℝ → X} (hG : Integrable G) {N : ℕ} (i : Fin N) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ) (ξ : Fin N → ℝ) :
    ‖tailDiff G i a b z ξ‖ ≤ (∫ v, ‖G v‖) + ∫ v, ‖G v‖ :=
  (norm_sub_le _ _).trans (add_le_add (norm_poissonInt_le hG hb _) (norm_poissonInt_le hG ha _))

/-- The `i`-th difference depends only on the increments with index `≥ i`. -/
private theorem tailDiff_congr (G : ℝ → X) {N : ℕ} (i : Fin N) (a b z : ℝ) {ξ ξ' : Fin N → ℝ}
    (h : ∀ j, i ≤ j → ξ j = ξ' j) : tailDiff G i a b z ξ = tailDiff G i a b z ξ' := by
  rw [tailDiff, tailDiff, chainTail_congr (i := i) fun j hj => h j hj,
    chainTail_congr (i := i + 1) fun j hj => h j (Fin.le_def.2 (by omega))]

/-- The Poisson integral formula: the mean over the `i`-th increment is zero (McConnell (1984), p.
748, and Lemma 2.1). -/
private theorem integral_tailDiff [CompleteSpace X] {G : ℝ → X} (hG : Integrable G) {N : ℕ}
    (i : Fin N) {a b h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hab : b - a = h) (z : ℝ)
    (ξ : Fin N → ℝ) : ∫ t, tailDiff G i a b z (Function.update ξ i t) ∂cauchyLaw h = 0 := by
  have h1 : ∀ t, tailDiff G i a b z (Function.update ξ i t) =
      poissonInt G b (z - chainTail ξ (i + 1)) -
        poissonInt G a (z - chainTail ξ (i + 1) - t) := fun t => by
    rw [tailDiff, chainTail_eq_add _ i, chainTail_update, Function.update_self]
    congr 2
    ring
  have hint : Integrable (fun t => poissonInt G a (z - chainTail ξ (i + 1) - t))
      (cauchyLaw h) :=
    Integrable.of_bound ((continuous_poissonInt hG ha).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable _
      (ae_of_all _ fun t => norm_poissonInt_le hG ha _)
  simp only [h1]
  rw [integral_sub (integrable_const _) hint, integral_poissonInt_sub hG hh ha, integral_const,
    probReal_univ, one_smul, show h + a = b by linarith, sub_self]

/-- Burkholder's inequality (2.1) in the form used for (3.10): complex coefficients with
`‖e_i‖ ≤ B`. -/
private theorem eLpNorm_sum_smul_tailDiff_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ} (hy : Monotone y) {N : ℕ}
    {a b z : Fin N → ℝ} (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, b i - a i = y (i + 1) - y i)
    {e : Fin N → ℂ} {B : ℝ} (he : ∀ i, ‖e i‖ ≤ B) (hB : 0 ≤ B) :
    eLpNorm (fun ξ => ∑ i, e i • tailDiff G i (a i) (b i) (z i) ξ) (ENNReal.ofReal p)
        (chainLaw y N) ≤
      ENNReal.ofReal B * (2 * β) * eLpNorm (fun ξ => ∑ i, tailDiff G i (a i) (b i) (z i) ξ)
        (ENNReal.ofReal p) (chainLaw y N) := by
  have hh : ∀ i : Fin N, 0 ≤ y (i + 1) - y i := fun i => sub_nonneg.2 (hy (Nat.le_succ _))
  have hb : ∀ i, 0 ≤ b i := fun i => by linarith [ha i, hab i, hh i]
  rcases hB.eq_or_lt with rfl | hB
  · have he0 : ∀ i, e i = 0 := fun i => norm_le_zero_iff.1 (he i)
    simp [he0]
  · have h1 := eLpNorm_sum_complex_smul_le (ν := fun i : Fin N => cauchyLaw (y (i + 1) - y i))
      (D := fun i => tailDiff G i (a i) (b i) (z i)) (e := fun i => e i / B) hp hβ
      (fun i => (continuous_tailDiff hG i (ha i) (hb i) (z i)).stronglyMeasurable)
      (fun i ξ => norm_tailDiff_le hG i (ha i) (hb i) (z i) ξ)
      (fun i _ _ h => tailDiff_congr G i (a i) (b i) (z i) h)
      (fun i ξ => integral_tailDiff hG i (ha i) (hh i) (hab i) (z i) ξ)
      (fun i => by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
        exact (div_le_one hB).2 (he i))
    have h2 : (fun ξ => ∑ i, e i • tailDiff G i (a i) (b i) (z i) ξ) =
        (B : ℂ) • fun ξ => ∑ i, (e i / B) • tailDiff G i (a i) (b i) (z i) ξ := by
      funext ξ
      rw [Pi.smul_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hB.ne')]
    rw [h2, eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB,
      mul_assoc]
    exact mul_le_mul_right h1 _

/-- Burkholder's inequality (2.1) in the form used on p. 751: real coefficients with
`|e_i| ≤ 1`. -/
private theorem eLpNorm_sum_real_smul_tailDiff_le [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hy : Monotone y) {N : ℕ} {a b z : Fin N → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, b i - a i = y (i + 1) - y i) {e : Fin N → ℝ} (he : ∀ i, |e i| ≤ 1) :
    eLpNorm (fun ξ => ∑ i, e i • tailDiff G i (a i) (b i) (z i) ξ) (ENNReal.ofReal p)
        (chainLaw y N) ≤
      β * eLpNorm (fun ξ => ∑ i, tailDiff G i (a i) (b i) (z i) ξ)
        (ENNReal.ofReal p) (chainLaw y N) := by
  have hh : ∀ i : Fin N, 0 ≤ y (i + 1) - y i := fun i => sub_nonneg.2 (hy (Nat.le_succ _))
  have hb : ∀ i, 0 ≤ b i := fun i => by linarith [ha i, hab i, hh i]
  exact eLpNorm_sum_smul_le (ν := fun i : Fin N => cauchyLaw (y (i + 1) - y i))
    (D := fun i => tailDiff G i (a i) (b i) (z i)) hp hβ
    (fun i => (continuous_tailDiff hG i (ha i) (hb i) (z i)).stronglyMeasurable)
    (fun i ξ => norm_tailDiff_le hG i (ha i) (hb i) (z i) ξ)
    (fun i _ _ h => tailDiff_congr G i (a i) (b i) (z i) h)
    (fun i ξ => integral_tailDiff hG i (ha i) (hh i) (hab i) (z i) ξ) he

/-! ### `p`-th powers -/

omit [NormedSpace ℂ X] in
/-- The `p`-th power of the `L^p` norm. -/
private theorem eLpNorm_rpow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 0 < p) {f : α → X} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ a, ‖f a‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne',
    ENNReal.rpow_one]

omit [NormedSpace ℂ X] in
/-- An inequality of `L^p` norms, for the `p`-th powers. -/
private theorem lintegral_rpow_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ} (hp : 0 < p) {f g : α → X} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {C : ℝ≥0∞}
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ C * eLpNorm g (ENNReal.ofReal p) μ) :
    ∫⁻ a, ‖f a‖ₑ ^ p ∂μ ≤ C ^ p * ∫⁻ a, ‖g a‖ₑ ^ p ∂μ := by
  rw [← eLpNorm_rpow_eq hp hf, ← eLpNorm_rpow_eq hp hg, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  exact ENNReal.rpow_le_rpow h hp.le

/-- Jensen's inequality, for a probability measure. -/
private theorem enorm_integral_rpow_le {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {p : ℝ} (hp : 1 ≤ p) {F : α → X} (hF : AEStronglyMeasurable F P) :
    ‖∫ a, F a ∂P‖ₑ ^ p ≤ ∫⁻ a, ‖F a‖ₑ ^ p ∂P := by
  have hp0 : 0 < p := by linarith
  rw [← eLpNorm_rpow_eq hp0 hF]
  refine ENNReal.rpow_le_rpow ?_ hp0.le
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm hF]
  exact eLpNorm_le_eLpNorm_of_exponent_le (by simpa using ENNReal.ofReal_le_ofReal hp)

/-- The integration over the starting point, (3.10): an inequality under `P_{(x', A)}` for every
`x'` gives one for `∫ P^x dx`. -/
private theorem lintegral_chainLaw_le (y : ℕ → ℝ) (N : ℕ) {F₁ F₂ : ℝ → (Fin N → ℝ) → ℝ≥0∞}
    (h₁ : Measurable (Function.uncurry F₁)) (h₂ : Measurable (Function.uncurry F₂)) {C : ℝ≥0∞}
    (h : ∀ x', ∫⁻ ξ, F₁ (x' - chainSum ξ N) ξ ∂chainLaw y N ≤
      C * ∫⁻ ξ, F₂ (x' - chainSum ξ N) ξ ∂chainLaw y N) :
    ∫⁻ x, ∫⁻ ξ, F₁ x ξ ∂chainLaw y N ≤ C * ∫⁻ x, ∫⁻ ξ, F₂ x ξ ∂chainLaw y N := by
  rw [lintegral_chainLaw_reverse y N h₁, lintegral_chainLaw_reverse y N h₂, ← lintegral_const_mul]
  · exact lintegral_mono h
  · refine Measurable.lintegral_prod_right' (f := fun q : ℝ × (Fin N → ℝ) =>
      F₂ (q.1 - chainSum q.2 N) q.2) ?_
    exact h₂.comp ((measurable_fst.sub ((continuous_chainSum N).measurable.comp
      measurable_snd)).prodMk measurable_snd)

/-! ### The probabilistic representation (3.9) -/

/-- McConnell (1984), (3.8), for `n = 1`: `e (s, y) = y² v_{yy} (s, y) / h (s, y)`; it is `0` for
`y = 0`. -/
private noncomputable def mihlinCoeff (m : ℝ → ℂ) (y s : ℝ) : ℂ :=
  (y : ℂ) ^ 2 * mihlinKernel m y s / (cauchyDensity y s : ℂ)

private theorem mihlinCoeff_zero (m : ℝ → ℂ) : mihlinCoeff m 0 = 0 := by
  funext s
  simp [mihlinCoeff]

/-- Lemma 3.1 for `e (s, y)`. -/
private theorem norm_mihlinCoeff_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {y : ℝ} (hy : 0 ≤ y) (s : ℝ) :
    ‖mihlinCoeff m y s‖ ≤ 17 * c := by
  rcases hy.eq_or_lt with rfl | hy
  · rw [mihlinCoeff_zero, Pi.zero_apply, norm_zero]
    linarith [nonneg_of_isMihlin hm]
  · have hpos := cauchyDensity_pos hy s
    rw [mihlinCoeff, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy, abs_of_pos hpos, div_le_iff₀ hpos]
    exact norm_mihlinKernel_le hm hs h0 hy s

private theorem continuous_mihlinCoeff {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {y : ℝ} (hy : 0 ≤ y) :
    Continuous (mihlinCoeff m y) := by
  rcases hy.eq_or_lt with rfl | hy
  · rw [mihlinCoeff_zero]
    exact continuous_zero
  · exact (continuous_const.mul (continuous_mihlinKernel hm hs h0 y)).div
      (Complex.continuous_ofReal.comp (continuous_cauchyDensity hy))
      fun s => Complex.ofReal_ne_zero.2 (cauchyDensity_pos hy s).ne'

/-- McConnell (1984), p. 748: the division by `h` expresses the `s`-integration as an expectation
for the Cauchy law. -/
private theorem integral_mihlinCoeff_smul (m : ℝ → ℂ) {y : ℝ} (hy : 0 ≤ y) (F : ℝ → X) :
    ∫ s, ((y : ℂ) ^ 2 * mihlinKernel m y s) • F s =
      ∫ s, mihlinCoeff m y s • F s ∂cauchyLaw y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [mihlinCoeff_zero]
  · rw [integral_cauchyLaw hy]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    have hpos := Complex.ofReal_ne_zero.2 (cauchyDensity_pos hy s).ne'
    simp only
    rw [← Complex.coe_smul, smul_smul, mihlinCoeff, mul_div_cancel₀ _ hpos]

/-- McConnell (1984), p. 748, from Lemma 2.2: `u (z, y_k + b) = E^z u (X (y_k), b)`. -/
private theorem integral_poissonInt_add_chainSum [CompleteSpace X] {G : ℝ → X}
    (hG : Integrable G) {y : ℕ → ℝ} (hy : Monotone y) (hy0 : y 0 = 0) {N k : ℕ} (hk : k ≤ N)
    {b : ℝ} (hb : 0 ≤ b) (z : ℝ) :
    ∫ ξ, poissonInt G b (z + chainSum ξ k) ∂chainLaw y N = poissonInt G (y k + b) z := by
  have hcont : Continuous fun t => poissonInt G b (z + t) :=
    (continuous_poissonInt hG hb).comp (continuous_const.add continuous_id)
  have hyk : 0 ≤ y k := hy0 ▸ hy (Nat.zero_le k)
  have h1 : ∫ ξ, poissonInt G b (z + chainSum ξ k) ∂chainLaw y N =
      ∫ t, poissonInt G b (z + t) ∂cauchyLaw (y k) := by
    have h := map_chainSum hy hk
    rw [hy0, sub_zero] at h
    rw [← h, integral_map (continuous_chainSum k).aemeasurable hcont.aestronglyMeasurable]
  have h2 : ∫ t, poissonInt G b (z + t) ∂cauchyLaw (y k) =
      ∫ t, poissonInt G b (z - t) ∂cauchyLaw (y k) := by
    conv_lhs => rw [← map_neg_cauchyLaw (y k)]
    rw [integral_map continuous_neg.aemeasurable hcont.aestronglyMeasurable]
    simp only [← sub_eq_add_neg]
  rw [h1, h2, integral_poissonInt_sub hG hyk hb]

/-- McConnell (1984), p. 748: `(Δu)_i = u (X (y_{i+1}) − X̃ (y_i), y_{i+1} + y_i) −
u (X (y_i) − X̃ (y_i), 2y_i)`, with `X (y_i) = x + chainSum ξ i` and `X̃ (y_i) = chainSum ξ' i`,
where `w = (ξ, ξ')`. -/
private noncomputable def chainDiff (G : ℝ → X) (y : ℕ → ℝ) {N : ℕ} (i : ℕ) (x : ℝ)
    (w : (Fin N → ℝ) × (Fin N → ℝ)) : X :=
  poissonInt G (y (i + 1) + y i) (x + chainSum w.1 (i + 1) - chainSum w.2 i) -
    poissonInt G (2 * y i) (x + chainSum w.1 i - chainSum w.2 i)

private theorem continuous_chainDiff {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hy : ∀ i, 0 ≤ y i) {N : ℕ} (i : ℕ) :
    Continuous fun q : ℝ × (Fin N → ℝ) × (Fin N → ℝ) => chainDiff G y i q.1 q.2 := by
  have h1 : ∀ k, Continuous fun q : ℝ × (Fin N → ℝ) × (Fin N → ℝ) => chainSum q.2.1 k := fun k =>
    (continuous_chainSum k).comp (by fun_prop)
  have h2 : Continuous fun q : ℝ × (Fin N → ℝ) × (Fin N → ℝ) => chainSum q.2.2 i :=
    (continuous_chainSum i).comp (by fun_prop)
  exact ((continuous_poissonInt hG (add_nonneg (hy _) (hy _))).comp
    ((continuous_fst.add (h1 (i + 1))).sub h2)).sub
    ((continuous_poissonInt hG (mul_nonneg zero_le_two (hy _))).comp
      ((continuous_fst.add (h1 i)).sub h2))

private theorem norm_chainDiff_le {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hy : ∀ i, 0 ≤ y i) {N : ℕ} (i : ℕ) (x : ℝ) (w : (Fin N → ℝ) × (Fin N → ℝ)) :
    ‖chainDiff G y i x w‖ ≤ (∫ v, ‖G v‖) + ∫ v, ‖G v‖ :=
  (norm_sub_le _ _).trans (add_le_add (norm_poissonInt_le hG (add_nonneg (hy _) (hy _)) _)
    (norm_poissonInt_le hG (mul_nonneg zero_le_two (hy _)) _))

/-- McConnell (1984), p. 748, the two identities before (3.8). -/
private theorem integral_chainDiff [CompleteSpace X] {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hy : Monotone y) (hy0 : y 0 = 0) {N i : ℕ} (hi : i < N) (x : ℝ) (ξ' : Fin N → ℝ) :
    ∫ ξ, chainDiff G y i x (ξ, ξ') ∂chainLaw y N =
      poissonInt G (2 * y (i + 1) + y i) (x - chainSum ξ' i) -
        poissonInt G (3 * y i) (x - chainSum ξ' i) := by
  have hyn : ∀ k, 0 ≤ y k := fun k => hy0 ▸ hy (Nat.zero_le k)
  have hb1 : 0 ≤ y (i + 1) + y i := add_nonneg (hyn _) (hyn _)
  have hb2 : 0 ≤ 2 * y i := mul_nonneg zero_le_two (hyn _)
  have hint : ∀ {b : ℝ}, 0 ≤ b → ∀ k, Integrable
      (fun ξ : Fin N → ℝ => poissonInt G b (x - chainSum ξ' i + chainSum ξ k)) (chainLaw y N) :=
    fun hb k => Integrable.of_bound ((continuous_poissonInt hG hb).comp
      (continuous_const.add (continuous_chainSum k))).aestronglyMeasurable _
      (ae_of_all _ fun ξ => norm_poissonInt_le hG hb _)
  simp only [chainDiff, add_sub_right_comm x]
  rw [integral_sub (hint hb1 (i + 1)) (hint hb2 i),
    integral_poissonInt_add_chainSum hG hy hy0 hi hb1,
    integral_poissonInt_add_chainSum hG hy hy0 hi.le hb2]
  congr 2 <;> ring

private theorem continuous_mihlinCoeff_smul_chainDiff {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G)
    {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) {N : ℕ} (i : ℕ) :
    Continuous fun q : ℝ × (Fin N → ℝ) × (Fin N → ℝ) =>
      mihlinCoeff m (y i) (chainSum q.2.2 i) • chainDiff G y i q.1 q.2 :=
  ((continuous_mihlinCoeff hm hs h0 (hy i)).comp
    ((continuous_chainSum i).comp (continuous_snd.comp continuous_snd))).smul
    (continuous_chainDiff hG hy i)

/-- The integrability for (3.9). -/
private theorem integrable_mihlinCoeff_smul_chainDiff {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G)
    {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (N i : ℕ) (x : ℝ) :
    Integrable (fun w : (Fin N → ℝ) × (Fin N → ℝ) =>
      mihlinCoeff m (y i) (chainSum w.2 i) • chainDiff G y i x w)
      ((chainLaw y N).prod (chainLaw y N)) := by
  have hcont := (continuous_mihlinCoeff_smul_chainDiff hm hs h0 hG hy (N := N) i).comp
    (Continuous.prodMk_right x)
  refine Integrable.of_bound hcont.aestronglyMeasurable
    (17 * c * ((∫ v, ‖G v‖) + ∫ v, ‖G v‖)) (ae_of_all _ fun w => ?_)
  rw [norm_smul]
  exact mul_le_mul (norm_mihlinCoeff_le hm hs h0 (hy i) _) (norm_chainDiff_le hG hy i x w)
    (norm_nonneg _) (by linarith [nonneg_of_isMihlin hm])

/-- One term of (3.9): the `s`-integral is the expectation with respect to `X̃ (y_i)`, and the two
Poisson integrals are expectations with respect to `X (y_{i+1})` and `X (y_i)`. -/
private theorem integral_mihlinCoeff_smul_chainDiff [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y : ℕ → ℝ} (hy : Monotone y) (hy0 : y 0 = 0) {N i : ℕ} (hi : i < N)
    (x : ℝ) :
    ∫ s, ((y i : ℂ) ^ 2 * mihlinKernel m (y i) s) •
        (poissonInt G (2 * y (i + 1) + y i) (x - s) - poissonInt G (3 * y i) (x - s)) =
      ∫ w, mihlinCoeff m (y i) (chainSum w.2 i) • chainDiff G y i x w
        ∂(chainLaw y N).prod (chainLaw y N) := by
  have hyn : ∀ k, 0 ≤ y k := fun k => hy0 ▸ hy (Nat.zero_le k)
  have hmap := map_chainSum hy hi.le
  rw [hy0, sub_zero] at hmap
  have hcont : ∀ {b : ℝ}, 0 ≤ b → Continuous fun s => poissonInt G b (x - s) := fun hb =>
    (continuous_poissonInt hG hb).comp (continuous_const.sub continuous_id)
  have hcontF : Continuous fun s => mihlinCoeff m (y i) s •
      (poissonInt G (2 * y (i + 1) + y i) (x - s) - poissonInt G (3 * y i) (x - s)) :=
    (continuous_mihlinCoeff hm hs h0 (hyn i)).smul
      ((hcont (by linarith [hyn i, hyn (i + 1)])).sub (hcont (by linarith [hyn i])))
  rw [integral_mihlinCoeff_smul m (hyn i),
    integral_prod_symm _ (integrable_mihlinCoeff_smul_chainDiff hm hs h0 hG hyn N i x), ← hmap,
    integral_map (continuous_chainSum _).aemeasurable hcontF.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun ξ' => ?_)
  simp only
  rw [integral_smul, integral_chainDiff hG hy hy0 hi]

/-- McConnell (1984), (3.9). -/
private theorem mihlinRiemannSum_eq_integral [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y : ℕ → ℝ} (hy : Monotone y) (hy0 : y 0 = 0) (N : ℕ) (x : ℝ) :
    mihlinRiemannSum m G y N x = ∫ w, ∑ i : Fin N,
      mihlinCoeff m (y i) (chainSum w.2 i) • chainDiff G y i x w
        ∂(chainLaw y N).prod (chainLaw y N) := by
  have hint := fun i => integrable_mihlinCoeff_smul_chainDiff hm hs h0 hG
    (fun k => hy0 ▸ hy (Nat.zero_le k)) N i x
  rw [integral_finsetSum _ fun (i : Fin N) _ => hint i, mihlinRiemannSum, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mihlinCoeff_smul_chainDiff hm hs h0 hG hy hy0 i.2 x

/-! ### The first use of Burkholder's inequality -/

/-- `∫ dx Ẽ⁰ E^x = Ẽ⁰ ∫ dx E^x`, by Tonelli's theorem. -/
private theorem lintegral_prod_chainLaw (y : ℕ → ℝ) (N : ℕ)
    {F : ℝ → (Fin N → ℝ) × (Fin N → ℝ) → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    ∫⁻ x, ∫⁻ w, F x w ∂(chainLaw y N).prod (chainLaw y N) =
      ∫⁻ ξ', ∫⁻ x, ∫⁻ ξ, F x (ξ, ξ') ∂chainLaw y N ∂(volume : Measure ℝ) ∂chainLaw y N := by
  have h1 : ∀ x, ∫⁻ w, F x w ∂(chainLaw y N).prod (chainLaw y N) =
      ∫⁻ ξ', ∫⁻ ξ, F x (ξ, ξ') ∂chainLaw y N ∂chainLaw y N := fun x =>
    lintegral_prod_symm' _ (hF.comp measurable_prodMk_left)
  have h2 : Measurable fun r : (ℝ × (Fin N → ℝ)) × (Fin N → ℝ) => F r.1.1 (r.2, r.1.2) :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  simp only [h1]
  exact lintegral_lintegral_swap (f := fun x ξ' => ∫⁻ ξ, F x (ξ, ξ') ∂chainLaw y N)
    h2.lintegral_prod_right'.aemeasurable

/-- The same as `lintegral_chainLaw_le` for two independent chains, the second one being fixed. -/
private theorem lintegral_prod_chainLaw_le (y : ℕ → ℝ) (N : ℕ)
    {F₁ F₂ : ℝ → (Fin N → ℝ) × (Fin N → ℝ) → ℝ≥0∞} (h₁ : Measurable (Function.uncurry F₁))
    (h₂ : Measurable (Function.uncurry F₂)) {C : ℝ≥0∞}
    (h : ∀ ξ' x', ∫⁻ ξ, F₁ (x' - chainSum ξ N) (ξ, ξ') ∂chainLaw y N ≤
      C * ∫⁻ ξ, F₂ (x' - chainSum ξ N) (ξ, ξ') ∂chainLaw y N) :
    ∫⁻ x, ∫⁻ w, F₁ x w ∂(chainLaw y N).prod (chainLaw y N) ≤
      C * ∫⁻ x, ∫⁻ w, F₂ x w ∂(chainLaw y N).prod (chainLaw y N) := by
  have hmap : ∀ ξ' : Fin N → ℝ, Measurable fun q : ℝ × (Fin N → ℝ) => (q.1, (q.2, ξ')) :=
    fun ξ' => by fun_prop
  rw [lintegral_prod_chainLaw y N h₁, lintegral_prod_chainLaw y N h₂, ← lintegral_const_mul]
  · exact lintegral_mono fun ξ' => lintegral_chainLaw_le y N
      (F₁ := fun x ξ => F₁ x (ξ, ξ')) (F₂ := fun x ξ => F₂ x (ξ, ξ')) (h₁.comp (hmap ξ'))
      (h₂.comp (hmap ξ')) (h ξ')
  · refine Measurable.lintegral_prod_right' (f := fun q : (Fin N → ℝ) × ℝ =>
      ∫⁻ ξ, F₂ q.2 (ξ, q.1) ∂chainLaw y N) ?_
    refine Measurable.lintegral_prod_right' (f := fun r : ((Fin N → ℝ) × ℝ) × (Fin N → ℝ) =>
      F₂ r.1.2 (r.2, r.1.1)) ?_
    exact h₂.comp (by fun_prop : Measurable fun r : ((Fin N → ℝ) × ℝ) × (Fin N → ℝ) =>
      (r.1.2, (r.2, r.1.1)))

/-- The `(Δu)_i` under `P_{(x', A)}`. -/
private theorem chainDiff_eq_tailDiff (G : ℝ → X) (y : ℕ → ℝ) {N : ℕ} (i : Fin N) (x' : ℝ)
    (ξ ξ' : Fin N → ℝ) : chainDiff G y i (x' - chainSum ξ N) (ξ, ξ') =
      tailDiff G i (2 * y i) (y (i + 1) + y i) (x' - chainSum ξ' i) ξ := by
  have h1 := chainSum_add_chainTail ξ i
  have h2 := chainSum_add_chainTail ξ (i + 1)
  rw [chainDiff, tailDiff]
  congr 2 <;> linarith

/-- McConnell (1984), (3.10) and the first display after the proof of Lemma 3.1 (p. 750): for fixed
`X̃` and under `P_{(x', A)}`, Burkholder's inequality removes the coefficients `e (X̃ (y_i), y_i)`.
(They are complex here, whence the factor `2`.) -/
private theorem lintegral_sum_mihlinCoeff_smul_le [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G)
    {y : ℕ → ℝ} (hy : Monotone y) (hyn : ∀ i, 0 ≤ y i) (N : ℕ) :
    ∫⁻ x, ∫⁻ w, ‖∑ i : Fin N, mihlinCoeff m (y i) (chainSum w.2 i) • chainDiff G y i x w‖ₑ ^ p
        ∂(chainLaw y N).prod (chainLaw y N) ≤
      (ENNReal.ofReal (17 * c) * (2 * β)) ^ p *
        ∫⁻ x, ∫⁻ w, ‖∑ i : Fin N, chainDiff G y i x w‖ₑ ^ p
          ∂(chainLaw y N).prod (chainLaw y N) := by
  have hp0 : 0 < p := by linarith
  have hcont₁ : Continuous fun q : ℝ × (Fin N → ℝ) × (Fin N → ℝ) =>
      ∑ i : Fin N, mihlinCoeff m (y i) (chainSum q.2.2 i) • chainDiff G y i q.1 q.2 :=
    continuous_finsetSum _ fun i _ => continuous_mihlinCoeff_smul_chainDiff hm hs h0 hG hyn i
  have hcont₂ : Continuous fun q : ℝ × (Fin N → ℝ) × (Fin N → ℝ) =>
      ∑ i : Fin N, chainDiff G y i q.1 q.2 :=
    continuous_finsetSum _ fun i _ => continuous_chainDiff hG hyn i
  refine lintegral_prod_chainLaw_le y N ?_ ?_ fun ξ' x' => ?_
  · exact hcont₁.enorm.measurable.pow_const p
  · exact hcont₂.enorm.measurable.pow_const p
  simp only [chainDiff_eq_tailDiff]
  have hD : ∀ i : Fin N, Continuous (tailDiff G i (2 * y i) (y (i + 1) + y i)
      (x' - chainSum ξ' i)) := fun i =>
    continuous_tailDiff hG i (by linarith [hyn i]) (add_nonneg (hyn _) (hyn _)) _
  refine lintegral_rpow_le_of_eLpNorm_le hp0
    (continuous_finsetSum _ fun i _ => (hD i).const_smul _).aestronglyMeasurable
    (continuous_finsetSum _ fun i _ => hD i).aestronglyMeasurable ?_
  exact eLpNorm_sum_smul_tailDiff_le hp hβ hG hy (a := fun i => 2 * y i)
    (b := fun i => y (i + 1) + y i) (z := fun i => x' - chainSum ξ' i)
    (fun i => by linarith [hyn i]) (fun i => by ring)
    (fun i => norm_mihlinCoeff_le hm hs h0 (hyn i) _) (by linarith [nonneg_of_isMihlin hm])

/-! ### Lemma 3.2 and the second use of Burkholder's inequality -/

/-- `z_{2i} = 2 y_i`. -/
private theorem zigzag_two_mul (y : ℕ → ℝ) (i : ℕ) : zigzag y (2 * i) = 2 * y i := by
  rw [zigzag, show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega, two_mul]

/-- `z_{2i+1} = y_{i+1} + y_i`. -/
private theorem zigzag_two_mul_add_one (y : ℕ → ℝ) (i : ℕ) :
    zigzag y (2 * i + 1) = y (i + 1) + y i := by
  rw [zigzag, show (2 * i + 1) / 2 = i by omega, show (2 * i + 1 + 1) / 2 = i + 1 by omega,
    add_comm]

private theorem monotone_zigzag {y : ℕ → ℝ} (hy : Monotone y) : Monotone (zigzag y) :=
  fun _ _ h => add_le_add (hy (Nat.div_le_div_right h))
    (hy (Nat.div_le_div_right (Nat.add_le_add_right h 1)))

/-- The differences `u (X (z_j), z_j) − u (X (z_{j+1}), z_{j+1})` of McConnell (1984), p. 751. -/
private noncomputable def zigzagDiff (G : ℝ → X) (y : ℕ → ℝ) {N : ℕ} (j : ℕ) (x : ℝ)
    (ζ : Fin N → ℝ) : X :=
  poissonInt G (zigzag y j) (x + chainSum ζ j) -
    poissonInt G (zigzag y (j + 1)) (x + chainSum ζ (j + 1))

private theorem continuous_zigzagDiff {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hy : ∀ i, 0 ≤ y i) {N : ℕ} (j : ℕ) :
    Continuous fun q : ℝ × (Fin N → ℝ) => zigzagDiff G y j q.1 q.2 := by
  have h : ∀ k, Continuous fun q : ℝ × (Fin N → ℝ) =>
      poissonInt G (zigzag y k) (q.1 + chainSum q.2 k) := fun k =>
    (continuous_poissonInt hG (add_nonneg (hy _) (hy _))).comp
      (continuous_fst.add ((continuous_chainSum k).comp continuous_snd))
  exact (h j).sub (h (j + 1))

/-- The sum over the even indices. -/
private theorem sum_range_two_mul_ite {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), (if Even j then f j else 0) =
      ∑ i ∈ Finset.range N, f (2 * i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      ite_eq_left (even_two_mul N), ite_eq_right (by simp), add_zero]

/-- McConnell (1984), (3.11), by Lemma 3.2. -/
private theorem lintegral_sum_chainDiff_eq {p : ℝ} {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hyn : ∀ i, 0 ≤ y i) (N : ℕ) (x : ℝ) :
    ∫⁻ w, ‖∑ i : Fin N, chainDiff G y i x w‖ₑ ^ p ∂(chainLaw y N).prod (chainLaw y N) =
      ∫⁻ ζ, ‖∑ i ∈ Finset.range N, zigzagDiff G y (2 * i) x ζ‖ₑ ^ p
        ∂chainLaw (zigzag y) (2 * N) := by
  -- the function of the two sequences of Lemma 3.2
  set Φ : (Fin (2 * N + 1) → ℝ) → ℝ≥0∞ := fun r => ‖∑ i : Fin N,
    (poissonInt G (y (i + 1) + y i) (x + r ⟨2 * i + 1, by omega⟩) -
      poissonInt G (2 * y i) (x + r ⟨2 * i, by omega⟩))‖ₑ ^ p with hΦdef
  have hΦ : Measurable Φ := by
    refine Measurable.pow_const (Continuous.measurable (Continuous.enorm ?_)) p
    refine continuous_finsetSum _ fun i _ => Continuous.sub ?_ ?_
    · exact (continuous_poissonInt hG (add_nonneg (hyn _) (hyn _))).comp (by fun_prop)
    · exact (continuous_poissonInt hG (by linarith [hyn i])).comp (by fun_prop)
  have hm1 : Measurable fun (w : (Fin N → ℝ) × (Fin N → ℝ)) (j : Fin (2 * N + 1)) =>
      chainSum w.1 ((j + 1) / 2) - chainSum w.2 (j / 2) := by
    refine Measurable.of_eval fun j => ?_
    exact ((continuous_chainSum _).measurable.comp measurable_fst).sub
      ((continuous_chainSum _).measurable.comp measurable_snd)
  have hm2 : Measurable fun (ζ : Fin (2 * N) → ℝ) (j : Fin (2 * N + 1)) => chainSum ζ j :=
    Measurable.of_eval fun j => (continuous_chainSum _).measurable
  have h1 : ∀ w : (Fin N → ℝ) × (Fin N → ℝ), ‖∑ i : Fin N, chainDiff G y i x w‖ₑ ^ p =
      Φ fun j => chainSum w.1 ((j + 1) / 2) - chainSum w.2 (j / 2) := fun w => by
    simp only [hΦdef, chainDiff]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (2 * (i : ℕ) + 1 + 1) / 2 = i + 1 by omega, show (2 * (i : ℕ) + 1) / 2 = i by omega,
      show 2 * (i : ℕ) / 2 = i by omega, add_sub_assoc, add_sub_assoc]
  have h2 : ∀ ζ : Fin (2 * N) → ℝ, ‖∑ i ∈ Finset.range N, zigzagDiff G y (2 * i) x ζ‖ₑ ^ p =
      Φ fun j => chainSum ζ j := fun ζ => by
    simp only [hΦdef, zigzagDiff, zigzag_two_mul, zigzag_two_mul_add_one]
    rw [← enorm_neg, ← Finset.sum_neg_distrib, Finset.sum_range]
    simp only [neg_sub]
  simp only [h1, h2]
  rw [← lintegral_map hΦ hm1, ← lintegral_map hΦ hm2, map_two_chains]

/-- The differences `u (X (z_j), z_j) − u (X (z_{j+1}), z_{j+1})` under `P_{(x', A)}`. -/
private theorem zigzagDiff_eq_tailDiff (G : ℝ → X) (y : ℕ → ℝ) {N : ℕ} (j : Fin N) (x' : ℝ)
    (ζ : Fin N → ℝ) : zigzagDiff G y j (x' - chainSum ζ N) ζ =
      -tailDiff G j (zigzag y j) (zigzag y (j + 1)) x' ζ := by
  have h1 := chainSum_add_chainTail ζ j
  have h2 := chainSum_add_chainTail ζ (j + 1)
  rw [zigzagDiff, tailDiff, neg_sub]
  congr 2 <;> linarith

/-- The sum of all the differences: `f (X (0)) − u (X (z), z)`, `z = z_{2N} = 2 y_N`. -/
private theorem sum_zigzagDiff (G : ℝ → X) {y : ℕ → ℝ} (hy0 : y 0 = 0) (N : ℕ) (x : ℝ)
    (ζ : Fin (2 * N) → ℝ) : ∑ j : Fin (2 * N), zigzagDiff G y j x ζ =
      𝓕⁻ G x - poissonInt G (2 * y N) (x + chainSum ζ (2 * N)) := by
  have h := Finset.sum_range_sub' (fun j => poissonInt G (zigzag y j) (x + chainSum ζ j)) (2 * N)
  rw [zigzag_two_mul, chainSum_zero, add_zero, show zigzag y 0 = 0 by simp [zigzag, hy0],
    poissonInt_zero, Finset.sum_range] at h
  exact h

/-- McConnell (1984), p. 751: the second use of Burkholder's inequality (2.1), with the coefficients
`ε_{2i} = 1` and `ε_{2i+1} = 0`; `−1` and `0` for the `tailDiff`, which have the opposite sign.
Departure from the source: the sum there ends with the term `j = 2N − 2`, here with `j = 2N − 1`, so
that the sum of all the differences is `f (X (0)) − u (X (z_{2N}), z_{2N})` instead of
`f (X (0)) − u (X (z_{2N−1}), z_{2N−1})`. -/
private theorem lintegral_sum_zigzagDiff_le [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hy : Monotone y) (hy0 : y 0 = 0) (N : ℕ) :
    ∫⁻ x, ∫⁻ ζ, ‖∑ i ∈ Finset.range N, zigzagDiff G y (2 * i) x ζ‖ₑ ^ p
        ∂chainLaw (zigzag y) (2 * N) ≤
      β ^ p * ∫⁻ x, ∫⁻ ζ, ‖𝓕⁻ G x - poissonInt G (2 * y N) (x + chainSum ζ (2 * N))‖ₑ ^ p
        ∂chainLaw (zigzag y) (2 * N) := by
  have hp0 : 0 < p := by linarith
  have hyn : ∀ k, 0 ≤ y k := fun k => hy0 ▸ hy (Nat.zero_le k)
  have hzn : ∀ k, 0 ≤ zigzag y k := fun k => add_nonneg (hyn _) (hyn _)
  have hcont₁ : Continuous fun q : ℝ × (Fin (2 * N) → ℝ) =>
      ∑ i ∈ Finset.range N, zigzagDiff G y (2 * i) q.1 q.2 :=
    continuous_finsetSum _ fun i _ => continuous_zigzagDiff hG hyn (2 * i)
  have hcont₂ : Continuous fun q : ℝ × (Fin (2 * N) → ℝ) =>
      ∑ j : Fin (2 * N), zigzagDiff G y j q.1 q.2 :=
    continuous_finsetSum _ fun j _ => continuous_zigzagDiff hG hyn j
  simp only [← sum_zigzagDiff G hy0]
  refine lintegral_chainLaw_le (zigzag y) (2 * N) ?_ ?_ fun x' => ?_
  · exact hcont₁.enorm.measurable.pow_const p
  · exact hcont₂.enorm.measurable.pow_const p
  have hD : ∀ j : Fin (2 * N), Continuous (tailDiff G j (zigzag y j) (zigzag y (j + 1)) x') :=
    fun j => continuous_tailDiff hG j (hzn _) (hzn _) _
  -- the coefficients
  have h1 : ∀ ζ : Fin (2 * N) → ℝ,
      ∑ i ∈ Finset.range N, zigzagDiff G y (2 * i) (x' - chainSum ζ (2 * N)) ζ =
      ∑ j : Fin (2 * N), (if Even (j : ℕ) then (-1 : ℝ) else 0) •
        tailDiff G j (zigzag y j) (zigzag y (j + 1)) x' ζ := fun ζ => by
    rw [← sum_range_two_mul_ite (fun j => zigzagDiff G y j (x' - chainSum ζ (2 * N)) ζ),
      Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zigzagDiff_eq_tailDiff]
    split_ifs <;> simp
  have h2 : ∀ ζ : Fin (2 * N) → ℝ,
      ‖∑ j : Fin (2 * N), zigzagDiff G y j (x' - chainSum ζ (2 * N)) ζ‖ₑ =
      ‖∑ j : Fin (2 * N), tailDiff G j (zigzag y j) (zigzag y (j + 1)) x' ζ‖ₑ := fun ζ => by
    simp only [zigzagDiff_eq_tailDiff, Finset.sum_neg_distrib, enorm_neg]
  simp only [h1, h2]
  refine lintegral_rpow_le_of_eLpNorm_le hp0
    (continuous_finsetSum _ fun i _ => (hD i).const_smul _).aestronglyMeasurable
    (continuous_finsetSum _ fun i _ => hD i).aestronglyMeasurable ?_
  exact eLpNorm_sum_real_smul_tailDiff_le hp hβ hG (monotone_zigzag hy)
    (a := fun j => zigzag y j) (b := fun j => zigzag y (j + 1)) (z := fun _ => x')
    (fun j => hzn j) (fun _ => rfl) (fun j => by split_ifs <;> simp)

/-- McConnell (1984), p. 751, the last step: `‖f (X (0)) − u (X (z), z)‖_p ≤ 2 ‖f‖_p`. Departure
from the source: there `E_{(x', A)} |u (X (z), z)|^p ≤ E_{(x', A)} |f (X (0))|^p` since `|u|^p` is
subharmonic, and then `x'` is integrated out with the density of `X (0)`; here the `x`-integral is
taken first, with the translation invariance of Lebesgue measure and the contractivity of the
Poisson integral on `L^p`. -/
private theorem lintegral_fourierInv_sub_poissonInt_le [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b) (N k : ℕ) :
    ∫⁻ x, ∫⁻ ζ, ‖𝓕⁻ G x - poissonInt G b (x + chainSum ζ k)‖ₑ ^ p ∂chainLaw y N ≤
      (2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) ^ p := by
  have hp0 : 0 < p := by linarith
  have hf := continuous_fourierInv_of_integrable hG
  have hu := continuous_poissonInt hG hb
  have hcont : Continuous fun q : ℝ × (Fin N → ℝ) =>
      𝓕⁻ G q.1 - poissonInt G b (q.1 + chainSum q.2 k) :=
    (hf.comp continuous_fst).sub
      (hu.comp (continuous_fst.add ((continuous_chainSum k).comp continuous_snd)))
  have hshift : ∀ a : ℝ, Continuous fun x => poissonInt G b (x + a) := fun a =>
    hu.comp (continuous_id.add continuous_const)
  have h1 : ∀ a : ℝ, ∫⁻ x, ‖𝓕⁻ G x - poissonInt G b (x + a)‖ₑ ^ p ≤
      (2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) ^ p := fun a => by
    have h0 : Continuous fun x => 𝓕⁻ G x - poissonInt G b (x + a) := hf.sub (hshift a)
    rw [← eLpNorm_rpow_eq hp0 h0.aestronglyMeasurable]
    refine ENNReal.rpow_le_rpow ?_ hp0.le
    refine (eLpNorm_sub_le (f := 𝓕⁻ G) (g := fun x => poissonInt G b (x + a))
      (by simpa using ENNReal.ofReal_le_ofReal hp.le)).trans ?_
    have h2 : eLpNorm (fun x => poissonInt G b (x + a)) (ENNReal.ofReal p) volume =
        eLpNorm (poissonInt G b) (ENNReal.ofReal p) volume :=
      eLpNorm_comp_measurePreserving (g := poissonInt G b) (f := fun x => x + a)
        hu.aestronglyMeasurable (measurePreserving_add_right volume a)
    rw [h2, two_mul]
    gcongr
    exact eLpNorm_poissonInt_le hp.le hG hb
  rw [lintegral_lintegral_swap (f := fun x ζ =>
    ‖𝓕⁻ G x - poissonInt G b (x + chainSum ζ k)‖ₑ ^ p)
    (hcont.enorm.measurable.pow_const p).aemeasurable]
  refine (lintegral_mono fun ζ => h1 (chainSum ζ k)).trans_eq ?_
  rw [lintegral_const, measure_univ, mul_one]

/-! ### The estimate of the Riemann sums -/

/-- McConnell (1984), (3.7): `‖g_N‖_p ≤ c_p ‖f‖_p`, for heights `0 = y_0 < y_1 < ⋯`. -/
theorem eLpNorm_mihlinRiemannSum_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) (hs : HasCompactSupport m)
    (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ} (hy : StrictMono y)
    (hy0 : y 0 = 0) (N : ℕ) :
    eLpNorm (mihlinRiemannSum m G y N) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * (68 * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hym := hy.monotone
  have hyn : ∀ k, 0 ≤ y k := fun k => hy0 ▸ hym (Nat.zero_le k)
  have hmeas : AEStronglyMeasurable (mihlinRiemannSum m G y N) volume :=
    (continuous_mihlinRiemannSum hm hs h0 hG hyn N).aestronglyMeasurable
  have h1 : eLpNorm (mihlinRiemannSum m G y N) (ENNReal.ofReal p) volume ^ p ≤
      (ENNReal.ofReal (17 * c) * (2 * β)) ^ p * (β ^ p *
        (2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) ^ p) := by
    rw [eLpNorm_rpow_eq hp0 hmeas]
    refine (lintegral_mono fun x => ?_).trans
      ((lintegral_sum_mihlinCoeff_smul_le hp hβ hm hs h0 hG hym hyn N).trans ?_)
    · rw [mihlinRiemannSum_eq_integral hm hs h0 hG hym hy0]
      exact enorm_integral_rpow_le hp.le ((integrable_finsetSum _ fun (i : Fin N) _ =>
        integrable_mihlinCoeff_smul_chainDiff hm hs h0 hG hyn N i x).aestronglyMeasurable)
    · gcongr
      simp only [lintegral_sum_chainDiff_eq hG hyn]
      refine (lintegral_sum_zigzagDiff_le hp hβ hG hym hy0 N).trans ?_
      gcongr
      exact lintegral_fourierInv_sub_poissonInt_le hp hG (by linarith [hyn N]) _ _
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    ENNReal.rpow_le_rpow_iff hp0] at h1
  refine h1.trans_eq ?_
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  ring

/-! ### McConnell's theorem -/

omit [NormedSpace ℂ X] in
/-- Fatou's lemma: a bound of the `L^p` norms passes to a pointwise limit. -/
private theorem eLpNorm_le_of_tendsto {p : ℝ≥0∞} {f : ℕ → ℝ → X} {g : ℝ → X}
    (hf : ∀ n, AEStronglyMeasurable (f n)) (hg : AEStronglyMeasurable g)
    (h : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {C : ℝ≥0∞}
    (hC : ∀ n, eLpNorm (f n) p volume ≤ C) : eLpNorm g p volume ≤ C :=
  (Lp.eLpNorm_lim_le_liminf_eLpNorm hf g hg (ae_of_all _ h)).trans
    ((liminf_le_liminf (Eventually.of_forall hC)).trans (liminf_const _).le)

/-- `T_m^A f` is continuous. -/
private theorem continuous_truncatedMultiplier [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {A : ℝ} (hA : 0 ≤ A) : Continuous (truncatedMultiplier m G A) := by
  rw [funext (truncatedMultiplier_eq hm hs h0 hG hA)]
  refine continuous_fourierInv_of_integrable (integrable_symbol_smul hm h0 hG
    (continuous_truncSymbol A) (C := 1) fun t ht => ?_)
  rw [abs_of_nonneg (truncSymbol_nonneg hA ht)]
  exact truncSymbol_le_one hA ht

/-- McConnell (1984), p. 747: (3.2) for `T_m^A`, with a constant that does not depend on `A`, from
(3.7), the convergence of the Riemann sums and Fatou's lemma. -/
private theorem eLpNorm_truncatedMultiplier_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) (hs : HasCompactSupport m)
    (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) {A : ℝ} (hA : 0 < A) :
    eLpNorm (truncatedMultiplier m G A) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * (1088 * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set y : ℕ → ℕ → ℝ := fun N i => i * A / (N + 1 : ℕ) with hydef
  have hy : ∀ N, StrictMono (y N) := fun N i j hij => by
    simp only [hydef]
    gcongr
  have hy0 : ∀ N, y N 0 = 0 := fun N => by simp [hydef]
  have hyn : ∀ N i, 0 ≤ y N i := fun N i => by positivity
  refine eLpNorm_le_of_tendsto
    (f := fun N => (-16 : ℂ) • mihlinRiemannSum m G (y N) (N + 1)) (fun N =>
      ((continuous_mihlinRiemannSum hm hs h0 hG (hyn N) _).const_smul _).aestronglyMeasurable)
    (continuous_truncatedMultiplier hm hs h0 hG hA.le).aestronglyMeasurable (fun x => ?_)
    fun N => ?_
  · have h := ((tendsto_mihlinRiemannSum hm hs h0 hG hA x).comp
      (tendsto_add_atTop_nat 1)).const_smul (-16 : ℂ)
    rw [smul_smul, show (-16 : ℂ) * -16⁻¹ = 1 by norm_num, one_smul] at h
    exact h
  · rw [eLpNorm_const_smul, show ‖(-16 : ℂ)‖ₑ = 16 by
      rw [enorm_neg, ← ofReal_norm, Complex.norm_ofNat, ENNReal.ofReal_ofNat]]
    calc 16 * eLpNorm (mihlinRiemannSum m G (y N) (N + 1)) (ENNReal.ofReal p) volume
        ≤ 16 * (ENNReal.ofReal c * (68 * β ^ 2) *
            eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) := by
          gcongr
          exact eLpNorm_mihlinRiemannSum_le hp hβ hm hs h0 hG (hy N) (hy0 N) _
      _ = _ := by ring

/-- McConnell (1984), (3.2): Theorem 1.1 for `n = 1` and multipliers with compact support in
`ℝ ∖ {0}`. -/
theorem eLpNorm_fourierInv_mihlin_le_of_hasCompactSupport [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) :
    eLpNorm (𝓕⁻ fun ξ => m ξ • G ξ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * (1088 * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hmG : Integrable fun ξ => m ξ • G ξ := by
    simpa using integrable_symbol_smul hm h0 hG (a := fun _ => 1) continuous_const (C := 1)
      (by simp)
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  refine eLpNorm_le_of_tendsto (f := fun n : ℕ => truncatedMultiplier m G (n + 1))
    (fun n => (continuous_truncatedMultiplier hm hs h0 hG (hpos n).le).aestronglyMeasurable)
    (continuous_fourierInv_of_integrable hmG).aestronglyMeasurable (fun x => ?_)
    fun n => eLpNorm_truncatedMultiplier_le hp hβ hm hs h0 hG (hpos n)
  exact (tendsto_truncatedMultiplier hm hs h0 hG x).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-! ### The general case -/

/-- Leibniz's formula: products of multipliers with (1.10) (McConnell (1984), p. 746). -/
private theorem isMihlin_mul {a b : ℝ → ℂ} {C₁ C₂ : ℝ} (ha : IsMihlin a C₁) (hb : IsMihlin b C₂) :
    IsMihlin (fun ξ => a ξ * b ξ) (4 * C₁ * C₂) := by
  refine ⟨ha.1.mul hb.1, fun k hk ξ hξ => ?_⟩
  have hC₁ := nonneg_of_isMihlin ha
  have hC₂ := nonneg_of_isMihlin hb
  have hnhds : ({0}ᶜ : Set ℝ) ∈ 𝓝 ξ := isOpen_compl_singleton.mem_nhds hξ
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  rw [iteratedDeriv_fun_mul ((ha.1.contDiffAt hnhds).of_le hk')
    ((hb.1.contDiffAt hnhds).of_le hk')]
  have hterm : ∀ i ∈ Finset.range (k + 1), |ξ| ^ k *
      ‖(k.choose i : ℂ) * iteratedDeriv i a ξ * iteratedDeriv (k - i) b ξ‖ ≤
        k.choose i * (C₁ * C₂) := fun i hi => by
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := ha.2 i (hik.trans hk) ξ hξ
    have h2 := hb.2 (k - i) ((Nat.sub_le _ _).trans hk) ξ hξ
    calc |ξ| ^ k * ‖(k.choose i : ℂ) * iteratedDeriv i a ξ * iteratedDeriv (k - i) b ξ‖
        = k.choose i * ((|ξ| ^ i * ‖iteratedDeriv i a ξ‖) *
            (|ξ| ^ (k - i) * ‖iteratedDeriv (k - i) b ξ‖)) := by
          rw [norm_mul, norm_mul, Complex.norm_natCast, ← Nat.add_sub_of_le hik, pow_add]
          simp only [Nat.add_sub_cancel_left]
          ring
      _ ≤ k.choose i * (C₁ * C₂) := by gcongr
  calc |ξ| ^ k * ‖∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℂ) * iteratedDeriv i a ξ * iteratedDeriv (k - i) b ξ‖
      ≤ ∑ i ∈ Finset.range (k + 1), |ξ| ^ k *
          ‖(k.choose i : ℂ) * iteratedDeriv i a ξ * iteratedDeriv (k - i) b ξ‖ := by
        rw [← Finset.mul_sum]
        gcongr
        exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (C₁ * C₂) := Finset.sum_le_sum hterm
    _ = 2 ^ k * (C₁ * C₂) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k
    _ ≤ 2 ^ 2 * (C₁ * C₂) := by gcongr; norm_num
    _ = 4 * C₁ * C₂ := by ring

/-- Differences of multipliers with (1.10). -/
private theorem isMihlin_sub {a b : ℝ → ℂ} {C₁ C₂ : ℝ} (ha : IsMihlin a C₁) (hb : IsMihlin b C₂) :
    IsMihlin (fun ξ => a ξ - b ξ) (C₁ + C₂) := by
  refine ⟨ha.1.sub hb.1, fun k hk ξ hξ => ?_⟩
  have hnhds : ({0}ᶜ : Set ℝ) ∈ 𝓝 ξ := isOpen_compl_singleton.mem_nhds hξ
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  rw [iteratedDeriv_fun_sub ((ha.1.contDiffAt hnhds).of_le hk')
    ((hb.1.contDiffAt hnhds).of_le hk')]
  calc |ξ| ^ k * ‖iteratedDeriv k a ξ - iteratedDeriv k b ξ‖
      ≤ |ξ| ^ k * (‖iteratedDeriv k a ξ‖ + ‖iteratedDeriv k b ξ‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |ξ| ^ k * ‖iteratedDeriv k a ξ‖ + |ξ| ^ k * ‖iteratedDeriv k b ξ‖ := mul_add _ _ _
    _ ≤ C₁ + C₂ := add_le_add (ha.2 k hk ξ hξ) (hb.2 k hk ξ hξ)

/-- Constants satisfy (1.10). -/
private theorem isMihlin_one : IsMihlin (fun _ => 1) 1 := by
  refine ⟨contDiffOn_const, fun k _ ξ _ => ?_⟩
  rw [iteratedDeriv_const]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [hk]

/-- (1.10) is invariant under dilations. -/
private theorem isMihlin_comp_mul {a : ℝ → ℂ} {C : ℝ} (ha : IsMihlin a C) (hcd : ContDiff ℝ 2 a)
    {r : ℝ} (hr : r ≠ 0) : IsMihlin (fun ξ => a (r * ξ)) C := by
  refine ⟨(hcd.comp (contDiff_const.mul contDiff_id)).contDiffOn, fun k hk ξ hξ => ?_⟩
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  rw [iteratedDeriv_comp_const_smul (hcd.of_le hk') r]
  have h := ha.2 k hk (r * ξ) (mul_ne_zero hr hξ)
  rw [abs_mul, mul_pow] at h
  rw [norm_smul, norm_pow, Real.norm_eq_abs]
  linarith

/-- The derivatives of a function with compact support have compact support. -/
private theorem hasCompactSupport_iteratedDeriv {a : ℝ → ℂ} (hs : HasCompactSupport a) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k a) := by
  induction k with
  | zero => rwa [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- Functions in `C²_c` satisfy (1.10). -/
private theorem exists_isMihlin {a : ℝ → ℂ} (hcd : ContDiff ℝ 2 a) (hs : HasCompactSupport a) :
    ∃ C, IsMihlin a C := by
  have h : ∀ k ≤ 2, ∃ M, ∀ ξ, |ξ| ^ k * ‖iteratedDeriv k a ξ‖ ≤ M := fun k hk => by
    have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
    have hcont : Continuous fun ξ => |ξ| ^ k * ‖iteratedDeriv k a ξ‖ :=
      (continuous_abs.pow k).mul (hcd.continuous_iteratedDeriv k hk').norm
    obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support
      ((hasCompactSupport_iteratedDeriv hs k).norm.mul_left)
    exact ⟨M, fun ξ => (le_abs_self _).trans (hM ξ)⟩
  obtain ⟨M₀, h₀⟩ := h 0 (by norm_num)
  obtain ⟨M₁, h₁⟩ := h 1 (by norm_num)
  obtain ⟨M₂, h₂⟩ := h 2 le_rfl
  refine ⟨max M₀ (max M₁ M₂), hcd.contDiffOn, fun k hk ξ _ => ?_⟩
  interval_cases k
  exacts [(h₀ ξ).trans (le_max_left _ _),
    (h₁ ξ).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (h₂ ξ).trans ((le_max_right _ _).trans (le_max_right _ _))]

/-- A smooth function `ψ` with `ψ (ξ) = 1` for `|ξ| ≤ 1/2` and `ψ (ξ) = 0` for `|ξ| ≥ 1`. The source
takes also `φ` with `φ (ξ) = 0` for `|ξ| ≤ 1/2` and `φ (ξ) = 1` for `|ξ| ≥ 1`; here `φ = 1 − ψ`. -/
private noncomputable def cutoff : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

private theorem cutoff_of_le {ξ : ℝ} (hξ : |ξ| ≤ 1 / 2) : cutoff ξ = 1 :=
  cutoff.one_of_mem_closedBall (by simpa [cutoff] using hξ)

private theorem cutoff_of_ge {ξ : ℝ} (hξ : 1 ≤ |ξ|) : cutoff ξ = 0 :=
  cutoff.zero_of_le_dist (by simpa [cutoff] using hξ)

/-- McConnell (1984), p. 746: `μ_k (ξ) = ψ (ξ / k) φ (k ξ) m (ξ)`, for a real `k = r > 0`. -/
private noncomputable def cutoffMultiplier (m : ℝ → ℂ) (r ξ : ℝ) : ℂ :=
  (cutoff (r⁻¹ * ξ) : ℂ) * (1 - (cutoff (r * ξ) : ℂ)) * m ξ

private theorem contDiff_cutoff : ContDiff ℝ 2 fun ξ => (cutoff ξ : ℂ) :=
  Complex.ofRealCLM.contDiff.comp cutoff.contDiff

/-- McConnell (1984), p. 746: the multipliers `μ_k` satisfy (1.10) with a constant independent of
`k`, by Leibniz's formula. Departure from the source: a first reduction, from `C^{n+1}` multipliers
with compact support in `ℝ^n ∖ {0}` to smooth ones by convolution with an approximate identity, is
not needed, since the proof above applies to `C²` multipliers. -/
private theorem exists_isMihlin_cutoffMultiplier : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℝ → ℂ) (c : ℝ),
    IsMihlin m c → ∀ r : ℝ, 0 < r → IsMihlin (cutoffMultiplier m r) (C * c) := by
  obtain ⟨C, hC⟩ := exists_isMihlin contDiff_cutoff
    (cutoff.hasCompactSupport.comp_left Complex.ofReal_zero)
  have hC0 := nonneg_of_isMihlin hC
  refine ⟨4 * (4 * C * (1 + C)), by positivity, fun m c hm r hr => ?_⟩
  have h1 := isMihlin_comp_mul hC contDiff_cutoff (inv_ne_zero hr.ne')
  have h2 := isMihlin_comp_mul hC contDiff_cutoff hr.ne'
  exact isMihlin_mul (isMihlin_mul h1 (isMihlin_sub isMihlin_one h2)) hm

/-- The support of `μ_k` is in `[−k, k]`. -/
private theorem hasCompactSupport_cutoffMultiplier (m : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (cutoffMultiplier m r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) r) fun ξ hξ => ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hξ
  have h : 1 ≤ |r⁻¹ * ξ| := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hr), inv_mul_eq_div, one_le_div hr]
    exact hξ.le
  rw [cutoffMultiplier, cutoff_of_ge h, Complex.ofReal_zero, zero_mul, zero_mul]

/-- `μ_k` vanishes in a neighbourhood of the origin. -/
private theorem zero_notMem_tsupport_cutoffMultiplier (m : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    (0 : ℝ) ∉ tsupport (cutoffMultiplier m r) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < 1 / (2 * r))] with ξ hξ
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, lt_div_iff₀ (by positivity)] at hξ
  have h : |r * ξ| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hr]
    linarith
  rw [cutoffMultiplier, cutoff_of_le h, Complex.ofReal_one, sub_self, mul_zero, zero_mul,
    Pi.zero_apply]

/-- The `μ_k` converge to `m` on `ℝ ∖ {0}`. -/
private theorem eventually_cutoffMultiplier_eq (m : ℝ → ℂ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∀ᶠ n : ℕ in atTop, cutoffMultiplier m (n + 1) ξ = m ξ := by
  have hpos := abs_pos.2 hξ
  filter_upwards [eventually_ge_atTop ⌈2 * |ξ|⌉₊, eventually_ge_atTop ⌈|ξ|⁻¹⌉₊] with n h1 h2
  have h1' : 2 * |ξ| ≤ n := Nat.ceil_le.1 h1
  have h2' : |ξ|⁻¹ ≤ n := Nat.ceil_le.1 h2
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h3 : |(n + 1 : ℝ)⁻¹ * ξ| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hn), inv_mul_eq_div, div_le_iff₀ hn]
    linarith
  have h4 : 1 ≤ |(n + 1 : ℝ) * ξ| := by
    rw [abs_mul, abs_of_pos hn, ← div_le_iff₀ hpos, one_div]
    linarith
  rw [cutoffMultiplier, cutoff_of_le h3, cutoff_of_ge h4, Complex.ofReal_one, Complex.ofReal_zero,
    sub_zero, one_mul, one_mul]

/-- The `μ_k` are bounded by `m`. -/
private theorem norm_cutoffMultiplier_le (m : ℝ → ℂ) (r ξ : ℝ) :
    ‖cutoffMultiplier m r ξ‖ ≤ ‖m ξ‖ := by
  have h1 : ‖(cutoff (r⁻¹ * ξ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg cutoff.nonneg]
    exact cutoff.le_one
  have h2 : ‖1 - (cutoff (r * ξ) : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 cutoff.le_one)]
    linarith [cutoff.nonneg (x := r * ξ)]
  rw [cutoffMultiplier, norm_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) h1).trans h2)

/-- **Mihlin's theorem on UMD spaces**, McConnell (1984), Theorem 1.1, for `n = 1`: for a complex
Banach space with the `UMD_p` constant `β` and a multiplier `m` of class `C²` on `ℝ ∖ {0}` with
`|ξ|^k |m^{(k)} (ξ)| ≤ c`, `k ≤ 2`, the inequality `‖𝓕⁻ (m G)‖_p ≤ C c β² ‖𝓕⁻ G‖_p`, with an
absolute constant `C`, for the functions `f = 𝓕⁻ G` with `G ∈ L¹`. (The source: `m` real-valued and
`C²` on `ℝ`; on p. 755 the theorem is applied to functions that are not continuous at `0`.) The
extension to `L^p (ℝ; X)` by density is not part of the statement. -/
theorem exists_eLpNorm_fourierInv_mihlin_le : ∃ C : NNReal, ∀ (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p → ∀ β : ℝ≥0∞, IsUMDBound X p β →
    ∀ (m : ℝ → ℂ) (c : ℝ), IsMihlin m c → ∀ G : ℝ → X, Integrable G →
      eLpNorm (𝓕⁻ fun ξ => m ξ • G ξ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal c * (C * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hcut⟩ := exists_isMihlin_cutoffMultiplier
  refine ⟨1088 * C.toNNReal, fun X _ _ _ p hp β hβ m c hm G hG => ?_⟩
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  have hμ : ∀ n : ℕ, IsMihlin (cutoffMultiplier m (n + 1)) (C * c) := fun n =>
    hcut m c hm _ (hpos n)
  have hμc : ∀ n : ℕ, Continuous (cutoffMultiplier m (n + 1)) := fun n =>
    continuous_of_isMihlin (hμ n) (zero_notMem_tsupport_cutoffMultiplier m (hpos n))
  have hlim : ∀ᵐ ξ, Tendsto (fun n : ℕ => cutoffMultiplier m (n + 1) ξ) atTop (𝓝 (m ξ)) :=
    ae_ne_zero.mono fun ξ hξ => tendsto_const_nhds.congr'
      ((eventually_cutoffMultiplier_eq m hξ).mono fun n hn => hn.symm)
  have hbound : ∀ n : ℕ, ∀ᵐ ξ, ‖cutoffMultiplier m (n + 1) ξ‖ ≤ c := fun n =>
    ae_ne_zero.mono fun ξ hξ => (norm_cutoffMultiplier_le m _ ξ).trans (norm_le_of_isMihlin hm hξ)
  have hmm : AEStronglyMeasurable m volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hμc n).aestronglyMeasurable) hlim
  have hmG : Integrable fun ξ => m ξ • G ξ :=
    hG.bdd_smul c hmm (ae_ne_zero.mono fun ξ hξ => norm_le_of_isMihlin hm hξ)
  refine eLpNorm_le_of_tendsto (f := fun n : ℕ => 𝓕⁻ fun ξ => cutoffMultiplier m (n + 1) ξ • G ξ)
    (fun n => (continuous_fourierInv_of_integrable (hG.bdd_smul c
      (hμc n).aestronglyMeasurable (hbound n))).aestronglyMeasurable)
    (continuous_fourierInv_of_integrable hmG).aestronglyMeasurable
    (tendsto_fourierInv_of_dominated hG (Eventually.of_forall fun n =>
      (hμc n).aestronglyMeasurable) (Eventually.of_forall hbound) hlim) fun n => ?_
  refine (eLpNorm_fourierInv_mihlin_le_of_hasCompactSupport hp hβ (hμ n)
    (hasCompactSupport_cutoffMultiplier m (hpos n))
    (zero_notMem_tsupport_cutoffMultiplier m (hpos n)) hG).trans_eq ?_
  rw [ENNReal.ofReal_mul hC, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.ofReal]
  ring

end HarmonicAnalysis
