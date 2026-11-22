/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.McConnell.Chain
public import HarmonicAnalysis.VectorValued.McConnell.Kernel
import HarmonicAnalysis.FourierMultiplier.Density
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Mihlin multipliers on UMD spaces

**Theorem** (`exists_eLpNorm_fourierInv_mihlin_le`; T. R. McConnell, *On Fourier multiplier
transformations of Banach-valued functions*, Trans. Amer. Math. Soc. 285 (1984), 739–757, Theorem
1.1, for `n = 1`). Let `X` be a complex UMD space with a `UMD_p` constant `β`, `1 < p < ∞`. If `m`
is of class `C²` on `ℝ ∖ {0}` with `|ξ|^k |m^{(k)} (ξ)| ≤ c`, `k ≤ 2`, then
`‖𝓕⁻ (m G)‖_{L^p (ℝ; X)} ≤ C c β² ‖𝓕⁻ G‖_{L^p (ℝ; X)}` for `G ∈ L¹ (ℝ; X)`, with an absolute
constant `C`. (The source's `λ` is `2πξ`; its condition (1.10) is invariant under dilations.)

## The proof

The proof is McConnell's, pp. 746–751. Let first `m` have compact support in `ℝ ∖ {0}`, and let `u`,
`v` and `w` be the Poisson integrals of `f = 𝓕⁻ G`, of `𝓕⁻ m` and of `T_m f = 𝓕⁻ (m G)`. Two
integrations by parts in `T_m f (x) = −∫_0^∞ w_y (x, y) dy` and the semigroup property (3.4),
`w (x, y_1 + y_2) = ∫ v (s, y_1) u (x − s, y_2) ds`, give (3.3)

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
chains by one chain with the heights `z_{2i} = 2y_i`, `z_{2i+1} = y_i + y_{i+1}`, and a second use
of Burkholder's inequality, with coefficients `0` and `1`, leaves
`f (X (0)) − u (X (z_{2N−1}), z_{2N−1})`.

The source works with smooth functions `f` of compact support and values in a finite-dimensional
subspace, and reduces the theorem to smooth `m`; here `f = 𝓕⁻ G` with `G ∈ L¹`, and `C²` is enough,
since `w` is smooth in `y ≥ 0` if `m` has compact support.

Corrections to the source:
* (3.1) has `|λ|^α` for `|λ|^{|α|}`;
* in the limit of `g_N` the factor of `T_m^A f` is `2 (n + 1)! (−4)^{−(n + 2)}`; it is misprinted
  on p. 747 and, differently, on p. 748;
* on p. 747, `u_y (s − x, y_i + 2y)` stands for `u_y (x − s, y_i + 2y)`, and a bracket `[` is
  missing;
* the second mean value theorem for integrals (p. 747) fails for vector-valued `u`, and for scalar
  `u` unless `u_y` has a constant sign;
* the coefficients `e (X̃ (y_i), y_i)` are complex unless `m` is even, while (2.1) is stated for
  real coefficients;
* in (3.11) and on p. 751 the differences have the sign opposite to the `(Δu)_i`; this is
  immaterial;
* the measures `P_{(x', A)}` of p. 751 must start at a height not below
  `z_{2N−1} = y_{N−1} + y_N`, which exceeds `A = y_N` if `N > 1`; here they start at `z_{2N−1}`.
-/

@[expose] public section

open MeasureTheory Filter BanachProbability
open scoped ENNReal FourierTransform Topology

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Multipliers with compact support in `ℝ ∖ {0}` -/

/-- The multipliers `m (ξ) a (2π|ξ|)`, `a` continuous, are bounded, since `m` has compact support;
they act on `L¹`. -/
private theorem integrable_symbol_smul {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G)
    {a : ℝ → ℝ} (ha : Continuous a) : Integrable fun ξ => (m ξ * (a (freq ξ) : ℂ)) • G ξ := by
  have hcont : Continuous fun ξ => m ξ * (a (freq ξ) : ℂ) :=
    (continuous_of_isMihlin hm h0).mul (Complex.continuous_ofReal.comp (ha.comp continuous_freq))
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hs.mul_right
  exact hG.bdd_smul M hcont.aestronglyMeasurable (ae_of_all _ hM)

/-- A multiplier with compact support, times a power of `t`, is bounded. -/
private theorem exists_norm_mul_freq_pow_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) (k : ℕ) :
    ∃ M, ∀ ξ, ‖m ξ‖ * freq ξ ^ k ≤ M := by
  have hcont : Continuous fun ξ => ‖m ξ‖ * freq ξ ^ k :=
    (continuous_of_isMihlin hm h0).norm.mul (continuous_freq.pow k)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support (hs.norm.mul_right)
  exact ⟨M, fun ξ => (le_abs_self _).trans (hM ξ)⟩

/-- Multipliers with compact support are integrable. -/
private theorem integrable_of_isMihlin {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) : Integrable m :=
  (continuous_of_isMihlin hm h0).integrable_of_hasCompactSupport hs

/-- The symbol `m G` of `T_m f` is integrable. -/
private theorem integrable_mul_symbol {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) :
    Integrable fun ξ => m ξ • G ξ := by
  simpa using integrable_symbol_smul hm hs h0 hG (a := fun _ => 1) continuous_const

/-- `h (s, y) / y² = 1 / (π y (s² + y²))` decreases in `y`. -/
private theorem cauchyDensity_div_sq_le {a y : ℝ} (ha : 0 < a) (hay : a ≤ y) (s : ℝ) :
    cauchyDensity y s / y ^ 2 ≤ cauchyDensity a s / a ^ 2 := by
  have h : ∀ b : ℝ, 0 < b → cauchyDensity b s / b ^ 2 = (Real.pi * b * (s ^ 2 + b ^ 2))⁻¹ :=
    fun b hb => by
      rw [cauchyDensity]
      field_simp
  have hy := ha.trans_le hay
  rw [h a ha, h y hy]
  gcongr

/-- `v`, `v_y` and `v_{yy}` are for `y ≥ a > 0` dominated by an integrable function of `s`, by Lemma
3.1 for the multipliers `m (ξ) (−2π|ξ|)^{k − 2}`, `k = 0, 1, 2`. -/
private theorem exists_norm_iteratedPoissonDeriv_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {k : ℕ} (hk : k ≤ 2) :
    ∃ C, ∀ a y, 0 < a → a ≤ y → ∀ s,
      ‖iteratedPoissonDeriv k m y s‖ ≤ C * (cauchyDensity a s / a ^ 2) := by
  set g : ℝ → ℂ := fun ξ => ((((-freq ξ) ^ (2 - k))⁻¹ : ℝ) : ℂ) with hg
  have hcd : ContDiff ℝ 2 fun ξ => m ξ * g ξ := contDiff_mul_of_notMem_tsupport hm.1 h0
    fun ξ hξ => Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
      (((contDiffAt_freq hξ).neg.pow _).inv (pow_ne_zero _ (neg_ne_zero.2 (freq_pos hξ).ne')))
  obtain ⟨C, hC⟩ := exists_isMihlin hcd hs.mul_right
  have h0' : (0 : ℝ) ∉ tsupport fun ξ => m ξ * g ξ := fun h => h0 (tsupport_mul_subset_left h)
  have hker : ∀ y, iteratedPoissonDeriv k m y = mihlinKernel (fun ξ => m ξ * g ξ) y := fun y => by
    rw [mihlinKernel_eq]
    refine congrArg _ (funext fun ξ => ?_)
    rcases eq_or_ne ξ 0 with rfl | hξ
    · rw [kernelSymbol, image_eq_zero_of_notMem_tsupport h0, smul_zero, zero_mul, zero_mul]
    · have h1 : (-freq ξ) ^ k = ((-freq ξ) ^ (2 - k))⁻¹ * freq ξ ^ 2 := by
        rw [← neg_sq (freq ξ), ← pow_sub_mul_pow _ hk, inv_mul_cancel_left₀
          (pow_ne_zero _ (neg_ne_zero.2 (freq_pos hξ).ne'))]
      rw [kernelSymbol, smul_eq_mul, h1, hg]
      push_cast
      ring
  refine ⟨17 * C, fun a y ha hay s => ?_⟩
  have hy := ha.trans_le hay
  have h := norm_mihlinKernel_le hC hs.mul_right h0' hy s
  rw [hker]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (cauchyDensity_div_sq_le ha hay s)
    (by linarith [nonneg_of_isMihlin hC]))
  rw [mul_div_assoc', le_div_iff₀ (by positivity), mul_comm]
  exact h

/-- `v`, `v_y` and `v_{yy}` are integrable functions of `s`. -/
private theorem integrable_iteratedPoissonDeriv {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {k : ℕ} (hk : k ≤ 2) {y : ℝ}
    (hy : 0 < y) : Integrable (iteratedPoissonDeriv k m y) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedPoissonDeriv_le hm hs h0 hk
  exact (((integrable_cauchyDensity hy).div_const _).const_mul C).mono'
    (continuous_iteratedPoissonDeriv k (integrable_of_isMihlin hm hs h0) hy).aestronglyMeasurable
    (ae_of_all _ (hC y y hy le_rfl))

/-! ### Convolutions on the Fourier side -/

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
inversion theorem. -/
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

/-! ### The representation (3.3) -/

/-- McConnell (1984), (3.4): `w (x, y_1 + y_2) = ∫ v (s, y_1) u (x − s, y_2) ds`, where `u`, `v` and
`w` are the Poisson integrals of `f = 𝓕⁻ G`, `M = 𝓕⁻ m` and `T_m f = M * f = 𝓕⁻ (m G)`, here for
`y_1 > 0`. The "semigroup property of the Poisson integral", to which the source refers, is read on
the Fourier side. -/
private theorem integral_poissonInt_smul_poissonInt [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 ≤ y₂) (x : ℝ) :
    ∫ s, poissonInt m y₁ s • poissonInt G y₂ (x - s) =
      poissonInt (fun ξ => m ξ • G ξ) (y₁ + y₂) x := by
  have hv := integrable_iteratedPoissonDeriv hm hs h0 (k := 0) (by norm_num) hy₁
  rw [iteratedPoissonDeriv_zero] at hv
  have hmc := continuous_of_isMihlin hm h0
  refine (integral_fourierInv_smul_fourierInv (by unfold freq; fun_prop)
    (integrable_poissonSymbol (integrable_of_isMihlin hm hs h0) hy₁.le) hv
    (integrable_poissonSymbol hG hy₂) x).trans ?_
  refine congrArg (fun F : ℝ → X => 𝓕⁻ F x) (funext fun ξ => ?_)
  rw [smul_eq_mul, smul_smul, smul_smul, mul_add, neg_add, Real.exp_add, freq]
  push_cast
  ring_nf

/-- Differentiation of `∫ v^{(k)} (s, y) g (s) ds`, `k ≤ 1`, `g` bounded, in `y > 0` under the
integral sign. -/
private theorem hasDerivAt_integral_iteratedPoissonDeriv_smul {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {k : ℕ}
    (hk : k + 1 ≤ 2) {g : ℝ → X} (hg : Continuous g) {B : ℝ} (hB : ∀ s, ‖g s‖ ≤ B) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (fun y => ∫ s, iteratedPoissonDeriv k m y s • g s)
      (∫ s, iteratedPoissonDeriv (k + 1) m y s • g s) y := by
  have hmi := integrable_of_isMihlin hm hs h0
  obtain ⟨C, hC⟩ := exists_norm_iteratedPoissonDeriv_le hm hs h0 hk
  have hy2 : 0 < y / 2 := half_pos hy
  have hint : ∀ k ≤ 2, ∀ η, 0 < η → Integrable fun s => iteratedPoissonDeriv k m η s • g s :=
    fun k hk η hη => (integrable_iteratedPoissonDeriv hm hs h0 hk hη).smul_bdd B
      hg.aestronglyMeasurable (ae_of_all _ hB)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := Set.Ioi (y / 2))
    (F := fun η s => iteratedPoissonDeriv k m η s • g s)
    (F' := fun η s => iteratedPoissonDeriv (k + 1) m η s • g s)
    (bound := fun s => C * (cauchyDensity (y / 2) s / (y / 2) ^ 2) * B)
    (Ioi_mem_nhds (half_lt_self hy))
    ((eventually_gt_nhds hy).mono fun η hη =>
      (hint k (by omega) η hη).aestronglyMeasurable)
    (hint k (by omega) y hy) (hint (k + 1) hk y hy).aestronglyMeasurable
    (ae_of_all _ fun s η hη => ?_)
    ((((integrable_cauchyDensity hy2).div_const _).const_mul C).mul_const B)
    (ae_of_all _ fun s η hη => ?_)).2
  · rw [norm_smul]
    exact mul_le_mul (hC _ η hy2 (Set.mem_Ioi.1 hη).le s) (hB s) (norm_nonneg _)
      ((norm_nonneg _).trans (hC _ η hy2 (Set.mem_Ioi.1 hη).le s))
  · exact (hasDerivAt_iteratedPoissonDeriv k hmi (hy2.trans hη) s).smul_const (g s)

/-- Differentiation of `∫ K (s) u (x − s, y) ds`, `K ∈ L¹`, in `y > 0` under the integral sign. -/
private theorem hasDerivAt_integral_smul_poissonInt {K : ℝ → ℂ} (hK : Integrable K) {G : ℝ → X}
    (hG : Integrable G) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun y => ∫ s, K s • poissonInt G y (x - s)) (∫ s, K s • poissonDeriv G y (x - s))
      y := by
  have hy2 : 0 < y / 2 := half_pos hy
  have hint : ∀ k η, 0 < η → Integrable fun s => K s • iteratedPoissonDeriv k G η (x - s) :=
    fun k η hη => hK.smul_bdd (k.factorial / η ^ k * ∫ ξ, ‖G ξ‖)
      ((continuous_iteratedPoissonDeriv k hG hη).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun s => norm_iteratedPoissonDeriv_le k hG hη (x - s))
  simp only [← iteratedPoissonDeriv_zero, ← iteratedPoissonDeriv_one]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := Set.Ioi (y / 2))
    (F := fun η s => K s • iteratedPoissonDeriv 0 G η (x - s))
    (F' := fun η s => K s • iteratedPoissonDeriv 1 G η (x - s))
    (bound := fun s => ‖K s‖ * ((1 : ℕ).factorial / (y / 2) ^ 1 * ∫ ξ, ‖G ξ‖))
    (Ioi_mem_nhds (half_lt_self hy))
    ((eventually_gt_nhds hy).mono fun η hη => (hint 0 η hη).aestronglyMeasurable)
    (hint 0 y hy) (hint 1 y hy).aestronglyMeasurable (ae_of_all _ fun s η hη => ?_)
    (hK.norm.mul_const _) (ae_of_all _ fun s η hη => ?_)).2
  · rw [norm_smul]
    gcongr
    refine (norm_iteratedPoissonDeriv_le 1 hG (hy2.trans hη) (x - s)).trans ?_
    gcongr
    exact (Set.mem_Ioi.1 hη).le
  · exact (hasDerivAt_iteratedPoissonDeriv 0 hG (hy2.trans hη) (x - s)).const_smul (K s)

/-- (3.4) differentiated `k ≤ 2` times with respect to `y_1`. -/
private theorem integral_iteratedPoissonDeriv_smul_poissonInt [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {k : ℕ} (hk : k ≤ 2) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 ≤ y₂) (x : ℝ) :
    ∫ s, iteratedPoissonDeriv k m y₁ s • poissonInt G y₂ (x - s) =
      iteratedPoissonDeriv k (fun ξ => m ξ • G ξ) (y₁ + y₂) x := by
  induction k generalizing y₁ with
  | zero =>
    simp only [iteratedPoissonDeriv_zero]
    exact integral_poissonInt_smul_poissonInt hm hs h0 hG hy₁ hy₂ x
  | succ k ih =>
    have h1 := hasDerivAt_integral_iteratedPoissonDeriv_smul hm hs h0 hk
      ((continuous_poissonInt hG hy₂).comp (continuous_const.sub continuous_id))
      (fun s => norm_poissonInt_le hG hy₂ (x - s)) hy₁
    have h2 := (hasDerivAt_iteratedPoissonDeriv k (integrable_mul_symbol hm hs h0 hG)
      (add_pos_of_pos_of_nonneg hy₁ hy₂) x).comp_add_const y₁ y₂
    refine h1.unique (h2.congr_of_eventuallyEq ?_)
    filter_upwards [eventually_gt_nhds hy₁] with η hη using ih (by omega) hη

/-- McConnell (1984), p. 747: (3.4) differentiated twice with respect to `y_1` and once with respect
to `y_2`, `w_{yyy} (x, y_1 + y_2) = ∫ v_{yy} (s, y_1) u_y (x − s, y_2) ds`. -/
private theorem integral_mihlinKernel_smul_poissonDeriv [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (x : ℝ) :
    ∫ s, mihlinKernel m y₁ s • poissonDeriv G y₂ (x - s) =
      iteratedPoissonDeriv 3 (fun ξ => m ξ • G ξ) (y₁ + y₂) x := by
  have hK := integrable_iteratedPoissonDeriv hm hs h0 le_rfl hy₁
  have h1 := hasDerivAt_integral_smul_poissonInt hK hG hy₂ x
  rw [iteratedPoissonDeriv_two] at h1
  have h2 := (hasDerivAt_iteratedPoissonDeriv 2 (integrable_mul_symbol hm hs h0 hG)
    (add_pos hy₁ hy₂) x).comp_const_add y₁ y₂
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  filter_upwards [eventually_gt_nhds hy₂] with η hη
  have h := integral_iteratedPoissonDeriv_smul_poissonInt hm hs h0 hG le_rfl hy₁ hη.le x
  rwa [iteratedPoissonDeriv_two] at h

/-- `w` and its derivatives in `y` are differentiable on `[0, ∞)`, since `m` has compact support:
`w (·, y)` is the Poisson integral at the height `y + 1` of `𝓕⁻ (e^{2π|ξ|} m G)`. -/
private theorem hasDerivAt_iteratedPoissonDeriv_of_nonneg {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) (k : ℕ)
    {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    HasDerivAt (fun y => iteratedPoissonDeriv k (fun ξ => m ξ • G ξ) y x)
      (iteratedPoissonDeriv (k + 1) (fun ξ => m ξ • G ξ) y x) y := by
  have hW := integrable_symbol_smul hm hs h0 hG Real.continuous_exp
  have e : ∀ k y, iteratedPoissonDeriv k (fun ξ => m ξ • G ξ) y =
      iteratedPoissonDeriv k (fun ξ => (m ξ * ((Real.exp (freq ξ) : ℝ) : ℂ)) • G ξ) (y + 1) :=
    fun k y => by
      refine congrArg _ (funext fun ξ => ?_)
      rw [smul_smul, smul_smul, show -(freq ξ * (y + 1)) = -(freq ξ * y) + -freq ξ by ring,
        Real.exp_add, mul_left_comm _ (m ξ), ← Complex.ofReal_mul, mul_assoc (_ ^ k), mul_assoc,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, mul_comm (m ξ)]
  simp only [e]
  exact (hasDerivAt_iteratedPoissonDeriv k hW (by linarith) x).comp_add_const y 1

/-- `w` and its derivatives decrease exponentially in `y`, since `m` vanishes near the origin. -/
private theorem exists_norm_iteratedPoissonDeriv_le_exp {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) (k : ℕ)
    (x : ℝ) : ∃ δ C : ℝ, 0 < δ ∧ ∀ y, 0 ≤ y →
      ‖iteratedPoissonDeriv k (fun ξ => m ξ • G ξ) y x‖ ≤ C * Real.exp (-(δ * y)) := by
  obtain ⟨ε, hε, hmε⟩ := Metric.eventually_nhds_iff.1 (notMem_tsupport_iff_eventuallyEq.1 h0)
  obtain ⟨M, hM⟩ := exists_norm_mul_freq_pow_le hm hs h0 k
  have hpi := Real.pi_pos
  refine ⟨2 * Real.pi * ε, M * ∫ ξ, ‖G ξ‖, by positivity, fun y hy => ?_⟩
  rw [iteratedPoissonDeriv, fourierInv_eq_expChar, mul_right_comm, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hG.norm.const_mul _) (ae_of_all _ fun ξ => ?_)
  rw [norm_smul, norm_expChar, one_mul, smul_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, Real.abs_exp,
    abs_of_nonneg (freq_nonneg ξ), mul_right_comm, mul_comm (freq ξ ^ k)]
  by_cases hξ : |ξ| < ε
  · have h : m ξ = 0 := hmε (by rwa [dist_zero_right, Real.norm_eq_abs])
    rw [h, norm_zero, zero_mul, zero_mul]
    have h1 := (mul_nonneg (norm_nonneg (m 0)) (pow_nonneg (freq_nonneg 0) k)).trans (hM 0)
    positivity
  · have h1 : 2 * Real.pi * ε ≤ freq ξ := by
      unfold freq
      exact mul_le_mul_of_nonneg_left (not_lt.1 hξ) (by positivity)
    have h2 := (mul_nonneg (norm_nonneg (m ξ)) (pow_nonneg (freq_nonneg ξ) k)).trans (hM ξ)
    gcongr
    exact hM ξ

/-- The functions `y^j w^{(k)} (x, y)` are integrable on `(0, ∞)`. -/
private theorem integrableOn_pow_smul_iteratedPoissonDeriv {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G)
    (j k : ℕ) (x : ℝ) : IntegrableOn
      (fun y : ℝ => y ^ j • iteratedPoissonDeriv k (fun ξ => m ξ • G ξ) y x) (Set.Ioi 0) := by
  obtain ⟨δ, C, hδ, hC⟩ := exists_norm_iteratedPoissonDeriv_le_exp hm hs h0 hG k x
  refine (((integrable_abs_pow_mul_exp j hδ).const_mul (C / δ ^ j)).integrableOn).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun y hy => ContinuousAt.continuousWithinAt ?_)
      measurableSet_Ioi
    exact (continuousAt_id.pow j).smul (hasDerivAt_iteratedPoissonDeriv_of_nonneg hm hs h0 hG k
      (Set.mem_Ioi.1 hy).le x).continuousAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hy0]
    refine (mul_le_mul_of_nonneg_left (hC y hy0.le) (by positivity)).trans_eq ?_
    rw [mul_pow]
    field_simp

omit [NormedSpace ℂ X] in
/-- Integration by parts: `∫_0^∞ y^{j+1} φ' (y) dy = −(j + 1) ∫_0^∞ y^j φ (y) dy`. -/
private theorem integral_Ioi_pow_succ_smul [NormedSpace ℝ X] [CompleteSpace X] {φ φ' : ℝ → X}
    (hd : ∀ y, 0 ≤ y → HasDerivAt φ (φ' y) y) (j : ℕ)
    (h1 : IntegrableOn (fun y => y ^ (j + 1) • φ' y) (Set.Ioi 0))
    (h2 : IntegrableOn (fun y => y ^ j • φ y) (Set.Ioi 0))
    (h3 : IntegrableOn (fun y => y ^ (j + 1) • φ y) (Set.Ioi 0)) :
    ∫ y in Set.Ioi 0, y ^ (j + 1) • φ' y = -(j + 1 : ℝ) • ∫ y in Set.Ioi 0, y ^ j • φ y := by
  have hd' : ∀ y ∈ Set.Ici (0 : ℝ), HasDerivAt (fun y => y ^ (j + 1) • φ y)
      (y ^ (j + 1) • φ' y + (j + 1 : ℝ) • y ^ j • φ y) y := fun y hy => by
    refine ((hasDerivAt_pow (j + 1) y).fun_smul (hd y hy)).congr_deriv ?_
    rw [smul_smul, Nat.cast_add_one, Nat.add_sub_cancel]
  have h2' : IntegrableOn (fun y => (j + 1 : ℝ) • y ^ j • φ y) (Set.Ioi 0) := h2.smul _
  have hint : IntegrableOn (fun y => y ^ (j + 1) • φ' y + (j + 1 : ℝ) • y ^ j • φ y) (Set.Ioi 0) :=
    h1.add h2'
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd' hint
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun y hy => hd' y (Set.mem_Ioi.1 hy).le) hint
      h3)
  rw [integral_add h1 h2', integral_smul, zero_pow j.succ_ne_zero, zero_smul,
    sub_zero] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h

/-- McConnell (1984), pp. 746–747: "`n + 1` integrations by parts" in the formula
`T_m f (x) = −∫_0^∞ w_y (x, y) dy`, for `n = 1`: `T_m f (x) = −½ ∫_0^∞ y² w_{yyy} (x, y) dy`. -/
private theorem fourierInv_eq_integral_iteratedPoissonDeriv [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) (x : ℝ) :
    𝓕⁻ (fun ξ => m ξ • G ξ) x = (-2⁻¹ : ℝ) • ∫ y in Set.Ioi (0 : ℝ),
      y ^ 2 • iteratedPoissonDeriv 3 (fun ξ => m ξ • G ξ) y x := by
  have hd := fun k y (hy : 0 ≤ y) => hasDerivAt_iteratedPoissonDeriv_of_nonneg hm hs h0 hG k hy x
  have hint := fun j k => integrableOn_pow_smul_iteratedPoissonDeriv hm hs h0 hG j k x
  have hint0 := fun k => by simpa only [pow_zero, one_smul] using hint 0 k
  -- `T_m f (x) = −∫_0^∞ w_y (x, y) dy`, since `w → 0` as `y → ∞`
  have h1 : ∫ y in Set.Ioi (0 : ℝ), iteratedPoissonDeriv 1 (fun ξ => m ξ • G ξ) y x =
      -𝓕⁻ (fun ξ => m ξ • G ξ) x := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun y hy => hd 0 y hy) (hint0 1)
      (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun y hy => hd 0 y (Set.mem_Ioi.1 hy).le)
        (hint0 1) (hint0 0)), iteratedPoissonDeriv_zero, poissonInt_zero, zero_sub]
  -- the integrations by parts
  have h2 := integral_Ioi_pow_succ_smul (hd 1) 0 (hint 1 2) (hint 0 1) (hint 1 1)
  have h3 := integral_Ioi_pow_succ_smul (hd 2) 1 (hint 2 3) (hint 1 2) (hint 2 2)
  simp only [pow_zero, one_smul, h1] at h2
  rw [h3, h2, smul_smul, smul_neg, ← neg_smul, smul_smul]
  norm_num

/-- McConnell (1984), (3.3), for `n = 1`: the integrand `∫ y² v_{yy} (s, y) u_y (x − s, 3y) ds` is
`y² w_{yyy} (x, 4y)`. -/
private theorem integral_mihlinKernel_smul_poissonDeriv_eq [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ∫ s, ((y : ℂ) ^ 2 * mihlinKernel m y s) • poissonDeriv G (3 * y) (x - s) =
      y ^ 2 • iteratedPoissonDeriv 3 (fun ξ => m ξ • G ξ) (4 * y) x := by
  simp only [mul_smul]
  rw [integral_smul, integral_mihlinKernel_smul_poissonDeriv hm hs h0 hG hy (by positivity),
    ← Complex.ofReal_pow, Complex.coe_smul, show y + 3 * y = 4 * y by ring]

/-- The integrand of (3.3) is integrable in `y`. -/
private theorem integrableOn_sq_smul_iteratedPoissonDeriv_four_mul {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) (x : ℝ) : IntegrableOn (fun y : ℝ =>
      y ^ 2 • iteratedPoissonDeriv 3 (fun ξ => m ξ • G ξ) (4 * y) x) (Set.Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff _ 0 (by norm_num : (0 : ℝ) < 4)).2
    (by simpa using integrableOn_pow_smul_iteratedPoissonDeriv hm hs h0 hG 2 3 x)
  refine IntegrableOn.congr_fun (h.smul (16⁻¹ : ℝ)) (fun y _ => ?_) measurableSet_Ioi
  simp only [Pi.smul_apply, smul_smul]
  congr 1
  ring

/-- McConnell (1984), (3.3), for `n = 1`: `T_m f (x) = −32 ∫_0^∞ ∫ y² v_{yy} (s, y) u_y (x − s, 3y)
ds dy`, where `(−4)^{n+2} / (n + 1)! = −32`. -/
theorem fourierInv_mihlin_eq_integral [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) (x : ℝ) :
    𝓕⁻ (fun ξ => m ξ • G ξ) x = (-32 : ℂ) • ∫ y in Set.Ioi (0 : ℝ), ∫ s,
      ((y : ℂ) ^ 2 * mihlinKernel m y s) • poissonDeriv G (3 * y) (x - s) := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun y hy =>
    integral_mihlinKernel_smul_poissonDeriv_eq hm hs h0 hG hy x,
    fourierInv_eq_integral_iteratedPoissonDeriv hm hs h0 hG]
  -- the substitution `y → 4y`
  have h := integral_comp_mul_left_Ioi (fun y : ℝ =>
    y ^ 2 • iteratedPoissonDeriv 3 (fun ξ => m ξ • G ξ) y x) 0 (by norm_num : (0 : ℝ) < 4)
  simp only [mul_pow, mul_smul, integral_smul, mul_zero] at h
  rw [← inv_smul_eq_iff₀ (by norm_num)] at h
  rw [← h, smul_smul, smul_smul, show (-32 : ℂ) = ((-32 : ℝ) : ℂ) by norm_num, Complex.coe_smul]
  congr 1
  norm_num

/-- `T_m^A f (x) = −32 ∫_0^A ∫ y² v_{yy} (s, y) u_y (x − s, 3y) ds dy` (McConnell (1984), p. 747,
for `n = 1`). -/
noncomputable def truncatedMultiplier (m : ℝ → ℂ) (G : ℝ → X) (A x : ℝ) : X :=
  (-32 : ℂ) • ∫ y in (0)..A, ∫ s,
    ((y : ℂ) ^ 2 * mihlinKernel m y s) • poissonDeriv G (3 * y) (x - s)

/-- McConnell (1984), (3.3), for `n = 1`: `T_m^A f (x) → T_m f (x)` as `A → ∞`. -/
theorem tendsto_truncatedMultiplier [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) (x : ℝ) :
    Tendsto (fun A => truncatedMultiplier m G A x) atTop (𝓝 (𝓕⁻ (fun ξ => m ξ • G ξ) x)) := by
  rw [fourierInv_mihlin_eq_integral hm hs h0 hG]
  refine (intervalIntegral_tendsto_integral_Ioi 0 ?_ tendsto_id).const_smul (-32 : ℂ)
  exact (integrableOn_sq_smul_iteratedPoissonDeriv_four_mul hm hs h0 hG x).congr_fun (fun y hy =>
    (integral_mihlinKernel_smul_poissonDeriv_eq hm hs h0 hG hy x).symm) measurableSet_Ioi

/-! ### The Riemann sums -/

/-- McConnell (1984), (3.5): `g_N (x) = Σ_i ∫ y_i² v_{yy} (s, y_i) [u (x − s, 2y_{i+1} + y_i) −
u (x − s, 3y_i)] ds`, for `n = 1`. -/
noncomputable def mihlinRiemannSum (m : ℝ → ℂ) (G : ℝ → X) (y : ℕ → ℝ) (N : ℕ) (x : ℝ) : X :=
  ∑ i ∈ Finset.range N, ∫ s, ((y i : ℂ) ^ 2 * mihlinKernel m (y i) s) •
    (poissonInt G (2 * y (i + 1) + y i) (x - s) - poissonInt G (3 * y i) (x - s))

/-- The terms of (3.5), by (3.4) differentiated twice with respect to `y_1`; both sides are `0` for
`y = 0`. -/
private theorem integral_mihlinKernel_smul_poissonInt_sub [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y a b : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) :
    ∫ s, ((y : ℂ) ^ 2 * mihlinKernel m y s) • (poissonInt G a (x - s) - poissonInt G b (x - s)) =
      y ^ 2 • (iteratedPoissonDeriv 2 (fun ξ => m ξ • G ξ) (y + a) x -
        iteratedPoissonDeriv 2 (fun ξ => m ξ • G ξ) (y + b) x) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  have hint : ∀ a, 0 ≤ a → Integrable fun s =>
      iteratedPoissonDeriv 2 m y s • poissonInt G a (x - s) := fun a ha =>
    (integrable_iteratedPoissonDeriv hm hs h0 le_rfl hy).smul_bdd _
      ((continuous_poissonInt hG ha).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun s => norm_poissonInt_le hG ha (x - s))
  simp only [mul_smul, ← iteratedPoissonDeriv_two]
  rw [integral_smul, ← Complex.ofReal_pow, Complex.coe_smul]
  simp only [smul_sub]
  rw [integral_sub (hint a ha) (hint b hb), smul_sub,
    integral_iteratedPoissonDeriv_smul_poissonInt hm hs h0 hG le_rfl hy ha,
    integral_iteratedPoissonDeriv_smul_poissonInt hm hs h0 hG le_rfl hy hb]

/-- `g_N (x) = Σ_i y_i² [w_{yy} (x, 2y_{i+1} + 2y_i) − w_{yy} (x, 4y_i)]`. -/
private theorem mihlinRiemannSum_eq [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G)
    {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (N : ℕ) (x : ℝ) : mihlinRiemannSum m G y N x =
      ∑ i ∈ Finset.range N, y i ^ 2 •
        (iteratedPoissonDeriv 2 (fun ξ => m ξ • G ξ) (2 * y (i + 1) + 2 * y i) x -
          iteratedPoissonDeriv 2 (fun ξ => m ξ • G ξ) (4 * y i) x) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mihlinKernel_smul_poissonInt_sub hm hs h0 hG (hy i)
    (by linarith [hy i, hy (i + 1)]) (by linarith [hy i])]
  congr 3 <;> ring_nf

/-- `g_N` is continuous. -/
private theorem continuous_mihlinRiemannSum [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {y : ℕ → ℝ} (hy : ∀ i, 0 ≤ y i) (N : ℕ) :
    Continuous (mihlinRiemannSum m G y N) := by
  have hW := integrable_mul_symbol hm hs h0 hG
  rw [funext (mihlinRiemannSum_eq hm hs h0 hG hy N)]
  refine continuous_finsetSum _ fun i _ => ?_
  rcases (hy i).eq_or_lt with hi | hi
  · simpa only [← hi, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul] using
      continuous_const
  · exact ((continuous_iteratedPoissonDeriv 2 hW (by linarith [hy (i + 1)])).sub
      (continuous_iteratedPoissonDeriv 2 hW (by linarith))).const_smul _

omit [NormedSpace ℂ X] in
/-- The mean value estimate of McConnell (1984), p. 747, for the function
`η² w_{yyy} (x, 2η + 2y) = ∫ ρ (s, η) u_y (x − s, η + 2y) ds`, `ρ (s, y) = y² v_{yy} (s, y)`, on
`a ≤ η ≤ y`; here `φ = w_{yyy}`. -/
private theorem norm_sq_smul_sub_le [NormedSpace ℝ X] {φ φ' : ℝ → X}
    (hd : ∀ y, 0 ≤ y → HasDerivAt φ (φ' y) y) {M M' : ℝ} (hM : ∀ y, 0 ≤ y → ‖φ y‖ ≤ M)
    (hM' : ∀ y, 0 ≤ y → ‖φ' y‖ ≤ M') {A a y : ℝ} (ha : 0 ≤ a) (hay : a ≤ y) (hyA : y ≤ A) :
    ‖y ^ 2 • φ (4 * y) - a ^ 2 • φ (2 * a + 2 * y)‖ ≤
      (2 * A * M + 2 * A ^ 2 * M') * (y - a) := by
  have hy : 0 ≤ y := ha.trans hay
  have hψ : ∀ η, 0 ≤ η → HasDerivAt (fun η => η ^ 2 • φ (2 * η + 2 * y))
      (η ^ 2 • (2 : ℝ) • φ' (2 * η + 2 * y) + (2 * η) • φ (2 * η + 2 * y)) η := fun η hη => by
    have h1 : HasDerivAt (fun η : ℝ => 2 * η + 2 * y) 2 η := by
      simpa using ((hasDerivAt_id η).const_mul 2).add_const (2 * y)
    have h2 : HasDerivAt (fun η : ℝ => η ^ 2) (2 * η) η := by simpa using hasDerivAt_pow 2 η
    exact h2.fun_smul ((hd _ (by positivity)).scomp η h1)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := a) (b := y)
    (C := 2 * A * M + 2 * A ^ 2 * M') (fun η hη => (hψ η (ha.trans hη.1)).hasDerivWithinAt)
    (fun η hη => ?_) y (Set.right_mem_Icc.2 hay)
  · rwa [show 2 * y + 2 * y = 4 * y by ring] at h
  have hη0 : 0 ≤ η := ha.trans hη.1
  have hηA : η ≤ A := hη.2.le.trans hyA
  have hA : 0 ≤ A := hy.trans hyA
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg (sq_nonneg η),
    Real.norm_of_nonneg zero_le_two, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * η)]
  have h1 := hM (2 * η + 2 * y) (by positivity)
  have h2 := hM' (2 * η + 2 * y) (by positivity)
  calc η ^ 2 * (2 * ‖φ' (2 * η + 2 * y)‖) + 2 * η * ‖φ (2 * η + 2 * y)‖
      ≤ A ^ 2 * (2 * M') + 2 * A * M := by gcongr
    _ = 2 * A * M + 2 * A ^ 2 * M' := by ring

omit [NormedSpace ℂ X] in
/-- The integrands below are continuous. -/
private theorem intervalIntegrable_smul_comp [NormedSpace ℝ X] {φ φ' : ℝ → X}
    (hd : ∀ y, 0 ≤ y → HasDerivAt φ (φ' y) y) {f c : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ y, 0 ≤ y → 0 ≤ f y) (hc : Continuous c) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => (2 : ℝ) • c y • φ (f y)) volume a b := by
  refine ContinuousOn.intervalIntegrable fun y hy => ?_
  rw [Set.uIcc_of_le hab] at hy
  have h : ContinuousAt (fun y => φ (f y)) y :=
    ContinuousAt.comp (hd _ (hf0 y (ha.trans hy.1))).continuousAt hf.continuousAt
  exact ((hc.continuousAt.smul h).const_smul _).continuousWithinAt

omit [NormedSpace ℂ X] in
/-- `ρ (y_i) [u (2y_{i+1} + y_i) − u (3y_i)] = ∫ 2 ρ (y_i) u_y (y_i + 2y) dy`, cf. McConnell (1984),
p. 747, after the integration in `s`; here `φ = w_{yy}`. -/
private theorem riemann_term_eq [NormedSpace ℝ X] [CompleteSpace X] {φ φ' φ'' : ℝ → X}
    (hd : ∀ y, 0 ≤ y → HasDerivAt φ (φ' y) y) (hd' : ∀ y, 0 ≤ y → HasDerivAt φ' (φ'' y) y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 • (φ (2 * b + 2 * a) - φ (4 * a)) =
      ∫ y in a..b, (2 : ℝ) • a ^ 2 • φ' (2 * a + 2 * y) := by
  have h : ∀ y ∈ Set.uIcc a b, HasDerivAt (fun y => a ^ 2 • φ (2 * a + 2 * y))
      ((2 : ℝ) • a ^ 2 • φ' (2 * a + 2 * y)) y := fun y hy => by
    rw [Set.uIcc_of_le hab] at hy
    have h1 : HasDerivAt (fun y : ℝ => 2 * a + 2 * y) 2 y := by
      simpa using ((hasDerivAt_id y).const_mul 2).const_add (2 * a)
    have h2 := ((hd _ (by linarith [hy.1] : 0 ≤ 2 * a + 2 * y)).scomp y h1).const_smul (a ^ 2)
    rwa [smul_comm] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (intervalIntegrable_smul_comp hd'
    (f := fun y => 2 * a + 2 * y) (c := fun _ => a ^ 2) (by fun_prop) (fun y hy => by positivity)
    continuous_const ha hab), smul_sub]
  congr 3 <;> ring_nf

omit [NormedSpace ℂ X] in
/-- McConnell (1984), p. 747: the error of the Riemann sum on one interval is at most a multiple of
the square of its length; here `φ = w_{yy}`.

Departure from the source: the estimate is made there for the integrand at a fixed `s`, with an
integrable majorant `γ (s)`, here after the integration in `s`. It goes there through
`∫ ρ (y) u_y (y_i + 2y) dy = ½ ρ (y^*) [u (y_i + 2y_{i+1}) − u (3y_i)]`, the second mean value
theorem for integrals, which is not available for vector-valued `u` (nor for scalar `u`, unless
`u_y` has a constant sign). Here `ρ (y_i) u_y (y_i + 2y)` is compared with `ρ (y) u_y (3y)` under
the integral sign. -/
private theorem norm_riemann_term_sub_le [NormedSpace ℝ X] [CompleteSpace X] {φ φ' φ'' : ℝ → X}
    (hd : ∀ y, 0 ≤ y → HasDerivAt φ (φ' y) y) (hd' : ∀ y, 0 ≤ y → HasDerivAt φ' (φ'' y) y)
    {M M' : ℝ} (hM : ∀ y, 0 ≤ y → ‖φ' y‖ ≤ M) (hM' : ∀ y, 0 ≤ y → ‖φ'' y‖ ≤ M') {A a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbA : b ≤ A) :
    ‖a ^ 2 • (φ (2 * b + 2 * a) - φ (4 * a)) - ∫ y in a..b, (2 : ℝ) • y ^ 2 • φ' (4 * y)‖ ≤
      2 * (2 * A * M + 2 * A ^ 2 * M') * (b - a) ^ 2 := by
  rw [riemann_term_eq hd hd' ha hab, ← intervalIntegral.integral_sub
    (intervalIntegrable_smul_comp hd' (f := fun y => 2 * a + 2 * y) (c := fun _ => a ^ 2)
      (by fun_prop) (fun y hy => by positivity) continuous_const ha hab)
    (intervalIntegrable_smul_comp hd' (f := fun y => 4 * y) (c := fun y => y ^ 2)
      (by fun_prop) (fun y hy => by positivity) (by fun_prop) ha hab)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := 2 * ((2 * A * M + 2 * A ^ 2 * M') * (b - a))) fun y hy => ?_).trans_eq ?_
  · rw [Set.uIoc_of_le hab] at hy
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg zero_le_two, norm_sub_rev]
    have hM0 := (norm_nonneg _).trans (hM 0 le_rfl)
    have hM0' := (norm_nonneg _).trans (hM' 0 le_rfl)
    have hA : 0 ≤ A := (ha.trans hab).trans hbA
    refine mul_le_mul_of_nonneg_left ((norm_sq_smul_sub_le hd' hM hM' ha hy.1.le
      (hy.2.trans hbA)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))) zero_le_two
    linarith [hy.2]
  · rw [abs_of_nonneg (by linarith : 0 ≤ b - a)]
    ring

omit [NormedSpace ℂ X] in
/-- McConnell (1984), (3.6): the sum of the errors, for the partition of `[0, A]` in `N` equal
parts; here `φ = w_{yy}`. The bound is a multiple of `N μ_N²`, `μ_N = A / N` the mesh size. -/
private theorem norm_riemannSum_sub_le [NormedSpace ℝ X] [CompleteSpace X] {φ φ' φ'' : ℝ → X}
    (hd : ∀ y, 0 ≤ y → HasDerivAt φ (φ' y) y) (hd' : ∀ y, 0 ≤ y → HasDerivAt φ' (φ'' y) y)
    {M M' : ℝ} (hM : ∀ y, 0 ≤ y → ‖φ' y‖ ≤ M) (hM' : ∀ y, 0 ≤ y → ‖φ'' y‖ ≤ M') {A : ℝ}
    (hA : 0 < A) {N : ℕ} (hN : 0 < N) {y : ℕ → ℝ} (hy : y = fun i : ℕ => i * A / N) :
    ‖∑ i ∈ Finset.range N, y i ^ 2 • (φ (2 * y (i + 1) + 2 * y i) - φ (4 * y i)) -
      ∫ y in (0)..A, (2 : ℝ) • y ^ 2 • φ' (4 * y)‖ ≤
      2 * (2 * A * M + 2 * A ^ 2 * M') * A ^ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hy0 : y 0 = 0 := by simp [hy]
  have hyN : y N = A := by simp [hy, hN'.ne']
  have hyn : ∀ i, 0 ≤ y i := fun i => by simp only [hy]; positivity
  have hstep : ∀ i, y (i + 1) - y i = A / N := fun i => by
    simp only [hy]
    push_cast
    ring
  have hmono : ∀ i, y i ≤ y (i + 1) := fun i => by
    linarith [hstep i, (by positivity : 0 ≤ A / N)]
  have hsum : ∫ y in (0)..A, (2 : ℝ) • y ^ 2 • φ' (4 * y) =
      ∑ i ∈ Finset.range N, ∫ y in y i..y (i + 1), (2 : ℝ) • y ^ 2 • φ' (4 * y) := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k _ =>
      intervalIntegrable_smul_comp hd' (f := fun y => 4 * y) (c := fun y => y ^ 2)
        (by fun_prop) (fun y hy => by positivity) (by fun_prop) (hyn k) (hmono k), hy0, hyN]
  rw [hsum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => ?_).trans_eq
    (b := ∑ i ∈ Finset.range N, 2 * (2 * A * M + 2 * A ^ 2 * M') * (A / N) ^ 2) ?_)
  · have hle : y (i + 1) ≤ A := by
      simp only [hy]
      rw [div_le_iff₀ hN', mul_comm]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.mem_range.1 hi) hA.le
    rw [← hstep i]
    exact norm_riemann_term_sub_le hd hd' hM hM' (hyn i) (hmono i) hle
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp

/-- `−(1/16) T_m^A f (x) = ∫_0^A 2 y² w_{yyy} (x, 4y) dy`. -/
private theorem smul_truncatedMultiplier_eq [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {A : ℝ} (hA : 0 ≤ A) (x : ℝ) :
    (-16⁻¹ : ℂ) • truncatedMultiplier m G A x = ∫ y in (0)..A,
      (2 : ℝ) • y ^ 2 • iteratedPoissonDeriv 3 (fun ξ => m ξ • G ξ) (4 * y) x := by
  rw [truncatedMultiplier, intervalIntegral.integral_smul, intervalIntegral.integral_of_le hA,
    intervalIntegral.integral_of_le hA, setIntegral_congr_fun measurableSet_Ioc fun y hy =>
      integral_mihlinKernel_smul_poissonDeriv_eq hm hs h0 hG hy.1 x, smul_smul,
    show (-16⁻¹ : ℂ) * -32 = ((2 : ℝ) : ℂ) by norm_num, Complex.coe_smul]

/-- McConnell (1984), (3.5)–(3.6): the Riemann sums for the partition of `[0, A]` in `N` equal parts
converge to `−(1/16) T_m^A f (x)`. (The factor is `2 (n + 1)! (−4)^{−(n + 2)}`; it is misprinted on
pp. 747 and 748. The source takes partitions that refine each other; this is not used.) -/
theorem tendsto_mihlinRiemannSum [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) {A : ℝ}
    (hA : 0 < A) (x : ℝ) :
    Tendsto (fun N : ℕ => mihlinRiemannSum m G (fun i => i * A / N) N x) atTop
      (𝓝 ((-16⁻¹ : ℂ) • truncatedMultiplier m G A x)) := by
  have hd := fun k y (hy : 0 ≤ y) => hasDerivAt_iteratedPoissonDeriv_of_nonneg hm hs h0 hG k hy x
  have hbd : ∀ k, ∃ M, ∀ y, 0 ≤ y → ‖iteratedPoissonDeriv k (fun ξ => m ξ • G ξ) y x‖ ≤ M :=
    fun k => by
      obtain ⟨δ, C, hδ, hC⟩ := exists_norm_iteratedPoissonDeriv_le_exp hm hs h0 hG k x
      have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0 le_rfl)
      exact ⟨C, fun y hy => (hC y hy).trans (mul_le_of_le_one_right hC0
        (Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))))⟩
  obtain ⟨M, hM⟩ := hbd 3
  obtain ⟨M', hM'⟩ := hbd 4
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun N =>
    norm_nonneg _) ((eventually_gt_atTop 0).mono fun N hN => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (2 * (2 * A * M + 2 * A ^ 2 * M') * A ^ 2)))
  rw [mihlinRiemannSum_eq hm hs h0 hG (fun i => by positivity),
    smul_truncatedMultiplier_eq hm hs h0 hG hA.le]
  exact norm_riemannSum_sub_le (hd 2) (hd 3) hM hM' hA hN rfl

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
/-- An inequality of `L^p` norms, for the `p`-th powers. -/
private theorem lintegral_rpow_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ} (hp : 0 < p) {f g : α → X} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {C : ℝ≥0∞}
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ C * eLpNorm g (ENNReal.ofReal p) μ) :
    ∫⁻ a, ‖f a‖ₑ ^ p ∂μ ≤ C ^ p * ∫⁻ a, ‖g a‖ₑ ^ p ∂μ := by
  rw [← eLpNorm_ofReal_rpow_eq_lintegral hp hf, ← eLpNorm_ofReal_rpow_eq_lintegral hp hg,
    ← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  exact ENNReal.rpow_le_rpow h hp.le

/-- Jensen's inequality, for a probability measure. -/
private theorem enorm_integral_rpow_le {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {p : ℝ} (hp : 1 ≤ p) {F : α → X} (hF : AEStronglyMeasurable F P) :
    ‖∫ a, F a ∂P‖ₑ ^ p ≤ ∫⁻ a, ‖F a‖ₑ ^ p ∂P := by
  have hp0 : 0 < p := by linarith
  rw [← eLpNorm_ofReal_rpow_eq_lintegral hp0 hF]
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
(They are complex, also in the source unless `m` is even, whence the factor `2`.) -/
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
private theorem sum_range_two_mul_add_one_ite {E : Type*} [AddCommMonoid E] (f : ℕ → E) (M : ℕ) :
    ∑ j ∈ Finset.range (2 * M + 1), (if Even j then f j else 0) =
      ∑ i ∈ Finset.range (M + 1), f (2 * i) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      ite_eq_right (by simp [parity_simps]), ite_eq_left (by simp [parity_simps]), add_zero,
      Finset.sum_range_succ _ (M + 1), Nat.mul_succ]

/-- McConnell (1984), (3.11), by Lemma 3.2. (The differences on the right have the sign opposite to
the `(Δu)_i`, as in the source.) -/
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

/-- The differences `u (X (z_j), z_j) − u (X (z_{j+1}), z_{j+1})` under `P_{(x', z_N)}`. -/
private theorem zigzagDiff_eq_tailDiff (G : ℝ → X) (y : ℕ → ℝ) {N : ℕ} (j : Fin N) (x' : ℝ)
    (ζ : Fin N → ℝ) : zigzagDiff G y j (x' - chainSum ζ N) ζ =
      -tailDiff G j (zigzag y j) (zigzag y (j + 1)) x' ζ := by
  have h1 := chainSum_add_chainTail ζ j
  have h2 := chainSum_add_chainTail ζ (j + 1)
  rw [zigzagDiff, tailDiff, neg_sub]
  congr 2 <;> linarith

/-- The sum of all the differences: `f (X (0)) − u (X (z_N), z_N)`. -/
private theorem sum_zigzagDiff (G : ℝ → X) {y : ℕ → ℝ} (hy0 : y 0 = 0) (N : ℕ) (x : ℝ)
    (ζ : Fin N → ℝ) : ∑ j : Fin N, zigzagDiff G y j x ζ =
      𝓕⁻ G x - poissonInt G (zigzag y N) (x + chainSum ζ N) := by
  have h := Finset.sum_range_sub' (fun j => poissonInt G (zigzag y j) (x + chainSum ζ j)) N
  rw [chainSum_zero, add_zero, show zigzag y 0 = 0 by simp [zigzag, hy0], poissonInt_zero,
    Finset.sum_range] at h
  exact h

/-- The sum in (3.11), `N = M + 1`, involves the chain only up to the height `z_{2N−1}`. -/
private theorem lintegral_sum_zigzagDiff_eq {p : ℝ} {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hyn : ∀ i, 0 ≤ y i) (M : ℕ) (x : ℝ) :
    ∫⁻ ζ, ‖∑ i ∈ Finset.range (M + 1), zigzagDiff G y (2 * i) x ζ‖ₑ ^ p
        ∂chainLaw (zigzag y) (2 * M + 1 + 1) =
      ∫⁻ ζ, ‖∑ i ∈ Finset.range (M + 1), zigzagDiff G y (2 * i) x ζ‖ₑ ^ p
        ∂chainLaw (zigzag y) (2 * M + 1) := by
  have hcont : Continuous fun q : ℝ × (Fin (2 * M + 1) → ℝ) =>
      ∑ i ∈ Finset.range (M + 1), zigzagDiff G y (2 * i) q.1 q.2 :=
    continuous_finsetSum _ fun i _ => continuous_zigzagDiff hG hyn (2 * i)
  have hm : Measurable fun ζ : Fin (2 * M + 1) → ℝ =>
      ‖∑ i ∈ Finset.range (M + 1), zigzagDiff G y (2 * i) x ζ‖ₑ ^ p :=
    (hcont.comp (Continuous.prodMk_right x)).enorm.measurable.pow_const p
  rw [← map_init_chainLaw (zigzag y) (2 * M + 1), lintegral_map hm (by unfold Fin.init; fun_prop)]
  refine lintegral_congr fun ζ => ?_
  congr 2
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [zigzagDiff, zigzagDiff, chainSum_init ζ (by omega), chainSum_init ζ (by omega)]

/-- McConnell (1984), p. 751: the second use of Burkholder's inequality (2.1), with the coefficients
`ε_{2i} = 1` and `ε_{2i+1} = 0`; `−1` and `0` for the `tailDiff`, which have the opposite sign. With
`N = M + 1`, the sums end with the term `j = 2N − 2`, and (2.1) is applied under `P_{(x', A)}`,
`A := z_{2N−1}`. -/
private theorem lintegral_sum_zigzagDiff_le [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hy : Monotone y) (hy0 : y 0 = 0) (M : ℕ) :
    ∫⁻ x, ∫⁻ ζ, ‖∑ i ∈ Finset.range (M + 1), zigzagDiff G y (2 * i) x ζ‖ₑ ^ p
        ∂chainLaw (zigzag y) (2 * M + 1) ≤
      β ^ p * ∫⁻ x, ∫⁻ ζ, ‖𝓕⁻ G x - poissonInt G (zigzag y (2 * M + 1))
        (x + chainSum ζ (2 * M + 1))‖ₑ ^ p ∂chainLaw (zigzag y) (2 * M + 1) := by
  have hp0 : 0 < p := by linarith
  have hyn : ∀ k, 0 ≤ y k := fun k => hy0 ▸ hy (Nat.zero_le k)
  have hzn : ∀ k, 0 ≤ zigzag y k := fun k => add_nonneg (hyn _) (hyn _)
  have hcont₁ : Continuous fun q : ℝ × (Fin (2 * M + 1) → ℝ) =>
      ∑ i ∈ Finset.range (M + 1), zigzagDiff G y (2 * i) q.1 q.2 :=
    continuous_finsetSum _ fun i _ => continuous_zigzagDiff hG hyn (2 * i)
  have hcont₂ : Continuous fun q : ℝ × (Fin (2 * M + 1) → ℝ) =>
      ∑ j : Fin (2 * M + 1), zigzagDiff G y j q.1 q.2 :=
    continuous_finsetSum _ fun j _ => continuous_zigzagDiff hG hyn j
  simp only [← sum_zigzagDiff G hy0]
  refine lintegral_chainLaw_le (zigzag y) (2 * M + 1) ?_ ?_ fun x' => ?_
  · exact hcont₁.enorm.measurable.pow_const p
  · exact hcont₂.enorm.measurable.pow_const p
  have hD : ∀ j : Fin (2 * M + 1), Continuous (tailDiff G j (zigzag y j) (zigzag y (j + 1)) x') :=
    fun j => continuous_tailDiff hG j (hzn _) (hzn _) _
  -- the coefficients
  have h1 : ∀ ζ : Fin (2 * M + 1) → ℝ,
      ∑ i ∈ Finset.range (M + 1), zigzagDiff G y (2 * i) (x' - chainSum ζ (2 * M + 1)) ζ =
      ∑ j : Fin (2 * M + 1), (if Even (j : ℕ) then (-1 : ℝ) else 0) •
        tailDiff G j (zigzag y j) (zigzag y (j + 1)) x' ζ := fun ζ => by
    rw [← sum_range_two_mul_add_one_ite (fun j => zigzagDiff G y j (x' - chainSum ζ (2 * M + 1)) ζ),
      Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zigzagDiff_eq_tailDiff]
    split_ifs <;> simp
  have h2 : ∀ ζ : Fin (2 * M + 1) → ℝ,
      ‖∑ j : Fin (2 * M + 1), zigzagDiff G y j (x' - chainSum ζ (2 * M + 1)) ζ‖ₑ =
      ‖∑ j : Fin (2 * M + 1), tailDiff G j (zigzag y j) (zigzag y (j + 1)) x' ζ‖ₑ := fun ζ => by
    simp only [zigzagDiff_eq_tailDiff, Finset.sum_neg_distrib, enorm_neg]
  simp only [h1, h2]
  refine lintegral_rpow_le_of_eLpNorm_le hp0
    (continuous_finsetSum _ fun i _ => (hD i).const_smul _).aestronglyMeasurable
    (continuous_finsetSum _ fun i _ => hD i).aestronglyMeasurable ?_
  exact eLpNorm_sum_real_smul_tailDiff_le hp hβ hG (monotone_zigzag hy)
    (a := fun j => zigzag y j) (b := fun j => zigzag y (j + 1)) (z := fun _ => x')
    (fun j => hzn j) (fun _ => rfl) (fun j => by split_ifs <;> simp)

/-- McConnell (1984), p. 751: `‖u (x', A)‖^p ≤ E_{(x', A)} ‖f (X (0))‖^p`, `A = y_N`, "from the fact
that `|u (s, y)|_B^p` is subharmonic": by Jensen's inequality, since `u (x', A) =
E_{(x', A)} f (X (0))`, (2.7). -/
private theorem enorm_poissonInt_rpow_le [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p) {G : ℝ → X}
    (hG : Integrable G) {y : ℕ → ℝ} (hy : Monotone y) (hy0 : y 0 = 0) (N : ℕ) (x' : ℝ) :
    ‖poissonInt G (y N) x'‖ₑ ^ p ≤ ∫⁻ ζ, ‖𝓕⁻ G (x' - chainSum ζ N)‖ₑ ^ p ∂chainLaw y N := by
  have hc : Continuous fun t => 𝓕⁻ G (x' - t) :=
    (continuous_fourierInv_of_integrable hG).comp (continuous_const.sub continuous_id)
  have h := integral_poissonInt_sub hG (hy0 ▸ hy (Nat.zero_le N) : 0 ≤ y N) le_rfl x'
  have hmap := map_chainSum hy (le_refl N)
  rw [hy0, sub_zero] at hmap
  rw [add_zero, poissonInt_zero, ← hmap,
    integral_map (continuous_chainSum N).aemeasurable hc.aestronglyMeasurable] at h
  rw [← h]
  exact enorm_integral_rpow_le hp (hc.comp (continuous_chainSum N)).aestronglyMeasurable

/-- McConnell (1984), p. 751, the last step, for the chain with the heights `0 = y_0 ≤ ⋯ ≤ y_N = A`:
`E_{(x', A)} ‖f (X (0)) − u (X (A), A)‖^p ≤ 2^p E_{(x', A)} ‖f (X (0))‖^p`, and the integral over
`x'` of the right side is `2^p ‖f‖_p^p`, by the law of `X (0)` (`lintegral_chainLaw_reverse`). -/
private theorem lintegral_fourierInv_sub_poissonInt_le [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p)
    {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ} (hy : Monotone y) (hy0 : y 0 = 0) (N : ℕ) :
    ∫⁻ x, ∫⁻ ζ, ‖𝓕⁻ G x - poissonInt G (y N) (x + chainSum ζ N)‖ₑ ^ p ∂chainLaw y N ≤
      (2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) ^ p := by
  have hp0 : 0 < p := by linarith
  have hf := continuous_fourierInv_of_integrable hG
  have hu := continuous_poissonInt hG (hy0 ▸ hy (Nat.zero_le N) : 0 ≤ y N)
  have hcont : Continuous fun q : ℝ × (Fin N → ℝ) =>
      𝓕⁻ G q.1 - poissonInt G (y N) (q.1 + chainSum q.2 N) :=
    (hf.comp continuous_fst).sub
      (hu.comp (continuous_fst.add ((continuous_chainSum N).comp continuous_snd)))
  -- under `P_{(x', A)}`, where `X (A) = x'`
  have h1 : ∀ x', ∫⁻ ζ, ‖𝓕⁻ G (x' - chainSum ζ N) -
      poissonInt G (y N) (x' - chainSum ζ N + chainSum ζ N)‖ₑ ^ p ∂chainLaw y N ≤
        2 ^ p * ∫⁻ ζ, ‖𝓕⁻ G (x' - chainSum ζ N)‖ₑ ^ p ∂chainLaw y N := fun x' => by
    have hfx : Continuous fun ζ : Fin N → ℝ => 𝓕⁻ G (x' - chainSum ζ N) :=
      hf.comp (continuous_const.sub (continuous_chainSum N))
    simp only [sub_add_cancel]
    refine lintegral_rpow_le_of_eLpNorm_le hp0 (hfx.sub continuous_const).aestronglyMeasurable
      hfx.aestronglyMeasurable ?_
    refine (eLpNorm_sub_le (by simpa using ENNReal.ofReal_le_ofReal hp)).trans ?_
    rw [two_mul]
    gcongr
    rw [← ENNReal.rpow_le_rpow_iff hp0, eLpNorm_ofReal_rpow_eq_lintegral hp0
      hfx.aestronglyMeasurable, eLpNorm_ofReal_rpow_eq_lintegral hp0 aestronglyMeasurable_const,
      lintegral_const, measure_univ, mul_one]
    exact enorm_poissonInt_rpow_le hp hG hy hy0 N x'
  -- the integration over `x'`
  refine (lintegral_chainLaw_le y N
    (F₁ := fun x ζ => ‖𝓕⁻ G x - poissonInt G (y N) (x + chainSum ζ N)‖ₑ ^ p)
    (F₂ := fun x _ => ‖𝓕⁻ G x‖ₑ ^ p) (hcont.enorm.measurable.pow_const p)
    ((hf.comp continuous_fst).enorm.measurable.pow_const p) h1).trans_eq ?_
  simp only [lintegral_const, measure_univ, mul_one]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    eLpNorm_ofReal_rpow_eq_lintegral hp0 hf.aestronglyMeasurable]

/-- McConnell (1984), pp. 750–751: the estimate of the right side of (3.11). -/
private theorem lintegral_sum_zigzagDiff_le_eLpNorm [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ}
    (hy : Monotone y) (hy0 : y 0 = 0) (N : ℕ) :
    ∫⁻ x, ∫⁻ ζ, ‖∑ i ∈ Finset.range N, zigzagDiff G y (2 * i) x ζ‖ₑ ^ p
        ∂chainLaw (zigzag y) (2 * N) ≤
      β ^ p * (2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) ^ p := by
  cases N with
  | zero => simp [show 0 < p by linarith]
  | succ M =>
    refine (lintegral_congr fun x => lintegral_sum_zigzagDiff_eq hG
      (fun k => hy0 ▸ hy (Nat.zero_le k)) M x).trans_le
      ((lintegral_sum_zigzagDiff_le hp hβ hG hy hy0 M).trans ?_)
    gcongr
    exact lintegral_fourierInv_sub_poissonInt_le hp.le hG (monotone_zigzag hy)
      (by simp [zigzag, hy0]) _

/-! ### The estimate of the Riemann sums -/

/-- McConnell (1984), (3.7): `‖g_N‖_p ≤ c_p ‖f‖_p`, for heights `0 = y_0 ≤ y_1 ≤ ⋯`. (In the source
`y_i < y_{i+1}`.) -/
theorem eLpNorm_mihlinRiemannSum_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) (hs : HasCompactSupport m)
    (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) {y : ℕ → ℝ} (hy : Monotone y)
    (hy0 : y 0 = 0) (N : ℕ) :
    eLpNorm (mihlinRiemannSum m G y N) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * (68 * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hyn : ∀ k, 0 ≤ y k := fun k => hy0 ▸ hy (Nat.zero_le k)
  have hmeas : AEStronglyMeasurable (mihlinRiemannSum m G y N) volume :=
    (continuous_mihlinRiemannSum hm hs h0 hG hyn N).aestronglyMeasurable
  have h1 : eLpNorm (mihlinRiemannSum m G y N) (ENNReal.ofReal p) volume ^ p ≤
      (ENNReal.ofReal (17 * c) * (2 * β)) ^ p * (β ^ p *
        (2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) ^ p) := by
    rw [eLpNorm_ofReal_rpow_eq_lintegral hp0 hmeas]
    refine (lintegral_mono fun x => ?_).trans
      ((lintegral_sum_mihlinCoeff_smul_le hp hβ hm hs h0 hG hy hyn N).trans ?_)
    · rw [mihlinRiemannSum_eq_integral hm hs h0 hG hy hy0]
      exact enorm_integral_rpow_le hp.le ((integrable_finsetSum _ fun (i : Fin N) _ =>
        integrable_mihlinCoeff_smul_chainDiff hm hs h0 hG hyn N i x).aestronglyMeasurable)
    · gcongr
      simp only [lintegral_sum_chainDiff_eq hG hyn]
      exact lintegral_sum_zigzagDiff_le_eLpNorm hp hβ hG hy hy0 N
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    ENNReal.rpow_le_rpow_iff hp0] at h1
  refine h1.trans_eq ?_
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  ring

/-! ### McConnell's theorem -/

/-- `T_m^A f = lim (−16 g_N)`, for the partitions of `[0, A]` in `N + 1` equal parts. -/
private theorem tendsto_smul_mihlinRiemannSum [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {A : ℝ} (hA : 0 < A) (x : ℝ) :
    Tendsto (fun N : ℕ => ((-16 : ℂ) • mihlinRiemannSum m G (fun i => i * A / (N + 1 : ℕ)) (N + 1))
      x) atTop (𝓝 (truncatedMultiplier m G A x)) := by
  have h := ((tendsto_mihlinRiemannSum hm hs h0 hG hA x).comp
    (tendsto_add_atTop_nat 1)).const_smul (-16 : ℂ)
  rwa [smul_smul, show (-16 : ℂ) * -16⁻¹ = 1 by norm_num, one_smul] at h

/-- The functions `−16 g_N` are measurable. -/
private theorem aestronglyMeasurable_smul_mihlinRiemannSum [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {A : ℝ} (hA : 0 < A) (N : ℕ) : AEStronglyMeasurable
      ((-16 : ℂ) • mihlinRiemannSum m G (fun i => i * A / (N + 1 : ℕ)) (N + 1)) volume :=
  ((continuous_mihlinRiemannSum hm hs h0 hG (fun i => by positivity) _).const_smul
    _).aestronglyMeasurable

/-- `T_m^A f` is measurable. -/
private theorem aestronglyMeasurable_truncatedMultiplier [CompleteSpace X] {m : ℝ → ℂ} {c : ℝ}
    (hm : IsMihlin m c) (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X}
    (hG : Integrable G) {A : ℝ} (hA : 0 < A) :
    AEStronglyMeasurable (truncatedMultiplier m G A) volume :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (aestronglyMeasurable_smul_mihlinRiemannSum hm hs h0 hG hA)
    (ae_of_all _ (tendsto_smul_mihlinRiemannSum hm hs h0 hG hA))

/-- McConnell (1984), p. 747: (3.2) for `T_m^A`, with a constant that does not depend on `A`, from
(3.7), the convergence of the Riemann sums and Fatou's lemma. -/
private theorem eLpNorm_truncatedMultiplier_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) (hs : HasCompactSupport m)
    (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) {A : ℝ} (hA : 0 < A) :
    eLpNorm (truncatedMultiplier m G A) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * (1088 * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall fun N => ?_)
    (aestronglyMeasurable_smul_mihlinRiemannSum hm hs h0 hG hA)
    (aestronglyMeasurable_truncatedMultiplier hm hs h0 hG hA)
    (ae_of_all _ (tendsto_smul_mihlinRiemannSum hm hs h0 hG hA))
  have hy : Monotone fun i : ℕ => i * A / (N + 1 : ℕ) := fun i j hij => by
    simp only
    gcongr
  rw [eLpNorm_const_smul, show ‖(-16 : ℂ)‖ₑ = 16 by
    rw [enorm_neg, ← ofReal_norm, Complex.norm_ofNat, ENNReal.ofReal_ofNat]]
  calc 16 * eLpNorm (mihlinRiemannSum m G (fun i => i * A / (N + 1 : ℕ)) (N + 1))
        (ENNReal.ofReal p) volume
      ≤ 16 * (ENNReal.ofReal c * (68 * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) := by
        gcongr
        exact eLpNorm_mihlinRiemannSum_le hp hβ hm hs h0 hG hy (by simp) _
    _ = _ := by ring

/-- McConnell (1984), (3.2): Theorem 1.1 for `n = 1` and multipliers with compact support in
`ℝ ∖ {0}`. -/
theorem eLpNorm_fourierInv_mihlin_le_of_hasCompactSupport [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {G : ℝ → X} (hG : Integrable G) :
    eLpNorm (𝓕⁻ fun ξ => m ξ • G ξ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * (1088 * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun n : ℕ => truncatedMultiplier m G (n + 1)) (Eventually.of_forall fun n =>
      eLpNorm_truncatedMultiplier_le hp hβ hm hs h0 hG (hpos n))
    (fun n => aestronglyMeasurable_truncatedMultiplier hm hs h0 hG (hpos n))
    (continuous_fourierInv_of_integrable
      (integrable_mul_symbol hm hs h0 hG)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  exact (tendsto_truncatedMultiplier hm hs h0 hG x).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-! ### The general case -/

/-- If bounded measurable multipliers `a_i` converge almost everywhere to `b`, then `𝓕⁻ (a_i G)`
converges pointwise to `𝓕⁻ (b G)`, `G ∈ L¹`, by dominated convergence. -/
theorem tendsto_fourierInv_of_dominated {ι : Type*} {l : Filter ι}
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
Banach space with a `UMD_p` constant `β` and a multiplier `m` of class `C²` on `ℝ ∖ {0}` with
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
  have hne := Measure.ae_ne volume (0 : ℝ)
  have hlim : ∀ᵐ ξ, Tendsto (fun n : ℕ => cutoffMultiplier m (n + 1) ξ) atTop (𝓝 (m ξ)) :=
    hne.mono fun ξ hξ => tendsto_const_nhds.congr'
      ((eventually_cutoffMultiplier_eq m hξ).mono fun n hn => hn.symm)
  have hbound : ∀ n : ℕ, ∀ᵐ ξ, ‖cutoffMultiplier m (n + 1) ξ‖ ≤ c := fun n =>
    hne.mono fun ξ hξ => (norm_cutoffMultiplier_le m _ ξ).trans (norm_le_of_isMihlin hm hξ)
  have hmm : AEStronglyMeasurable m volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hμc n).aestronglyMeasurable) hlim
  have hmG : Integrable fun ξ => m ξ • G ξ :=
    hG.bdd_smul c hmm (hne.mono fun ξ hξ => norm_le_of_isMihlin hm hξ)
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun n : ℕ => 𝓕⁻ fun ξ => cutoffMultiplier m (n + 1) ξ • G ξ)
    (Eventually.of_forall fun n => ?_)
    (fun n => (continuous_fourierInv_of_integrable (hG.bdd_smul c
      (hμc n).aestronglyMeasurable (hbound n))).aestronglyMeasurable)
    (continuous_fourierInv_of_integrable hmG).aestronglyMeasurable
    (ae_of_all _ (tendsto_fourierInv_of_dominated hG (Eventually.of_forall fun n =>
      (hμc n).aestronglyMeasurable) (Eventually.of_forall hbound) hlim))
  refine (eLpNorm_fourierInv_mihlin_le_of_hasCompactSupport hp hβ (hμ n)
    (hasCompactSupport_cutoffMultiplier m (hpos n))
    (zero_notMem_tsupport_cutoffMultiplier m (hpos n)) hG).trans_eq ?_
  rw [ENNReal.ofReal_mul hC, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.ofReal]
  ring

end HarmonicAnalysis
