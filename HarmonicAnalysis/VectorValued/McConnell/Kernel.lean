/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.McConnell.PoissonKernel
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The kernel of a Mihlin multiplier

`IsMihlin m c`: the function `m : ℝ → ℂ` is of class `C²` on `ℝ ∖ {0}` and
`|ξ|^k |m^{(k)} (ξ)| ≤ c` for `k = 0, 1, 2`. This is (1.10) of T. R. McConnell, *On Fourier
multiplier transformations of Banach-valued functions*, Trans. Amer. Math. Soc. 285 (1984), 739–757,
for `n = 1`; there `m` is real-valued and of class `C²` on `ℝ`, here it is complex-valued, and `C²`
only on `ℝ ∖ {0}`, as needed on p. 755. The source's `λ` is `2πξ`; (1.10) is invariant.

If moreover `m` has compact support in `ℝ ∖ {0}`, let `v (s, y)` be the Poisson integral of the
inverse Fourier transform of `m`. Then `v_{yy} (s, y) = 𝓕⁻ (m (ξ) (2π|ξ|)² e^{−2π|ξ|y}) (s)`
(`mihlinKernel m y s`, `iteratedDeriv_two_poissonInt`), and `y² |v_{yy} (s, y)| ≤ 17 c h (s, y)`,
`h` the Poisson kernel: McConnell's Lemma 3.1, with an explicit constant (`norm_mihlinKernel_le`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

namespace HarmonicAnalysis

/-- McConnell (1984), (1.10), for `n = 1`: `m` is of class `C²` on `ℝ ∖ {0}` and
`|ξ|^k |m^{(k)} (ξ)| ≤ c` for `k ≤ 2` and `ξ ≠ 0`. (The source: `m` real-valued and `C²` on `ℝ`.) -/
def IsMihlin (m : ℝ → ℂ) (c : ℝ) : Prop :=
  ContDiffOn ℝ 2 m {0}ᶜ ∧ ∀ k ≤ 2, ∀ ξ ≠ 0, |ξ| ^ k * ‖iteratedDeriv k m ξ‖ ≤ c

/-- The inverse Fourier transform of `m (ξ) (2π|ξ|)² e^{−2π|ξ|y}`. For `y > 0` it is
`v_{yy} (·, y)`, where `v (s, y) = poissonInt m y s` is the Poisson integral of the inverse Fourier
transform of `m` (`hasDerivAt_poissonDeriv`, `iteratedDeriv_two_poissonInt`). -/
noncomputable def mihlinKernel (m : ℝ → ℂ) (y s : ℝ) : ℂ :=
  𝓕⁻ (fun ξ : ℝ =>
    m ξ * (((2 * Real.pi * |ξ|) ^ 2 * Real.exp (-(2 * Real.pi * |ξ| * y)) : ℝ) : ℂ)) s

/-! ### Multipliers with (1.10) -/

/-- (1.10) for `k = 0`. -/
theorem norm_le_of_isMihlin {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖m ξ‖ ≤ c := by
  simpa using hm.2 0 (by norm_num) ξ hξ

/-- The constant of (1.10) is nonnegative. -/
theorem nonneg_of_isMihlin {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) : 0 ≤ c :=
  (norm_nonneg _).trans (norm_le_of_isMihlin hm one_ne_zero)

/-- The product of a multiplier with support in `ℝ ∖ {0}` and a function of class `C²` on `ℝ ∖ {0}`
is of class `C²`. -/
theorem contDiff_mul_of_notMem_tsupport {m g : ℝ → ℂ} (hm : ContDiffOn ℝ 2 m {0}ᶜ)
    (h0 : (0 : ℝ) ∉ tsupport m) (hg : ∀ ξ ≠ 0, ContDiffAt ℝ 2 g ξ) :
    ContDiff ℝ 2 fun ξ => m ξ * g ξ := by
  refine contDiff_iff_contDiffAt.2 fun ξ => ?_
  by_cases hξ : ξ = 0
  · subst hξ
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h0] with η hη
    rw [hη, Pi.zero_apply, zero_mul]
  · exact (hm.contDiffAt (isOpen_compl_singleton.mem_nhds hξ)).mul (hg ξ hξ)

/-- A multiplier with support in `ℝ ∖ {0}` is continuous. -/
theorem continuous_of_isMihlin {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (h0 : (0 : ℝ) ∉ tsupport m) : Continuous m := by
  simpa using (contDiff_mul_of_notMem_tsupport hm.1 h0 (g := fun _ => 1)
    fun _ _ => contDiffAt_const).continuous

/-- The derivatives of a function with compact support have compact support. -/
private theorem hasCompactSupport_iteratedDeriv {a : ℝ → ℂ} (hs : HasCompactSupport a) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k a) := by
  induction k with
  | zero => rwa [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- Functions of class `C²` with compact support, in particular those with compact support in
`ℝ ∖ {0}`, satisfy (1.10). -/
theorem exists_isMihlin {a : ℝ → ℂ} (hcd : ContDiff ℝ 2 a) (hs : HasCompactSupport a) :
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

/-! ### The symbol of the kernel -/

/-- The symbol `m (ξ) (2π|ξ|)² e^{−2π|ξ|y}` of the kernel `v_{yy} (·, y)`. -/
noncomputable def kernelSymbol (m : ℝ → ℂ) (y ξ : ℝ) : ℂ :=
  m ξ * ((freq ξ ^ 2 * Real.exp (-(freq ξ * y)) : ℝ) : ℂ)

/-- The kernel is the inverse Fourier transform of the symbol. -/
theorem mihlinKernel_eq (m : ℝ → ℂ) (y : ℝ) : mihlinKernel m y = 𝓕⁻ (kernelSymbol m y) :=
  rfl

/-- The function `(2πξ)² e^{−aξ}`; for `a = ± 2πy` it is `(2π|ξ|)² e^{−2π|ξ|y}` on a half-line. -/
private noncomputable def expSymbol (a ξ : ℝ) : ℂ :=
  (((2 * Real.pi * ξ) ^ 2 * Real.exp (-(a * ξ)) : ℝ) : ℂ)

/-- `(2πξ)² e^{−aξ}` is smooth. -/
private theorem contDiff_expSymbol (a : ℝ) : ContDiff ℝ 2 (expSymbol a) :=
  Complex.ofRealCLM.contDiff.comp (f := fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2 * Real.exp (-(a * ξ)))
    (by fun_prop)

/-- The first derivative of `(2πξ)² e^{−aξ}`. -/
private theorem iteratedDeriv_one_expSymbol (a ξ : ℝ) :
    iteratedDeriv 1 (expSymbol a) ξ =
      (((2 * Real.pi) ^ 2 * (2 * ξ - a * ξ ^ 2) * Real.exp (-(a * ξ)) : ℝ) : ℂ) := by
  rw [iteratedDeriv_one]
  refine HasDerivAt.deriv (HasDerivAt.ofReal_comp ?_)
  have h1 : HasDerivAt (fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2) (2 * (2 * Real.pi * ξ) * (2 * Real.pi))
      ξ := by
    simpa using ((hasDerivAt_id ξ).const_mul (2 * Real.pi)).fun_pow 2
  have h2 : HasDerivAt (fun ξ : ℝ => Real.exp (-(a * ξ))) (Real.exp (-(a * ξ)) * -a) ξ := by
    simpa using ((hasDerivAt_id ξ).const_mul a).fun_neg.exp
  refine (h1.fun_mul h2).congr_deriv ?_
  ring

/-- The second derivative of `(2πξ)² e^{−aξ}`. -/
private theorem iteratedDeriv_two_expSymbol (a ξ : ℝ) :
    iteratedDeriv 2 (expSymbol a) ξ =
      (((2 * Real.pi) ^ 2 * (2 - 4 * (a * ξ) + (a * ξ) ^ 2) * Real.exp (-(a * ξ)) : ℝ) : ℂ) := by
  have h0 : iteratedDeriv 1 (expSymbol a) = fun ξ : ℝ =>
      (((2 * Real.pi) ^ 2 * (2 * ξ - a * ξ ^ 2) * Real.exp (-(a * ξ)) : ℝ) : ℂ) :=
    funext (iteratedDeriv_one_expSymbol a)
  rw [iteratedDeriv_succ, h0]
  refine HasDerivAt.deriv (HasDerivAt.ofReal_comp ?_)
  have h1 : HasDerivAt (fun ξ : ℝ => (2 * Real.pi) ^ 2 * (2 * ξ - a * ξ ^ 2))
      ((2 * Real.pi) ^ 2 * (2 - a * (2 * ξ))) ξ := by
    simpa using (((hasDerivAt_id ξ).const_mul 2).fun_sub
      (((hasDerivAt_id ξ).fun_pow 2).const_mul a)).const_mul ((2 * Real.pi) ^ 2)
  have h2 : HasDerivAt (fun ξ : ℝ => Real.exp (-(a * ξ))) (Real.exp (-(a * ξ)) * -a) ξ := by
    simpa using ((hasDerivAt_id ξ).const_mul a).fun_neg.exp
  refine (h1.fun_mul h2).congr_deriv ?_
  ring

/-- Near `ξ ≠ 0` the symbol is `m (η) (2πη)² e^{−aη}` with `a = ± 2πy`. -/
private theorem exists_kernelSymbol_eventuallyEq (m : ℝ → ℂ) (y : ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ a : ℝ, a * ξ = 2 * Real.pi * y * |ξ| ∧ kernelSymbol m y =ᶠ[𝓝 ξ] m * expSymbol a := by
  rcases hξ.lt_or_gt with h | h
  · refine ⟨-(2 * Real.pi * y), by rw [abs_of_neg h]; ring, ?_⟩
    filter_upwards [eventually_lt_nhds h] with η hη
    rw [Pi.mul_apply, kernelSymbol, expSymbol, freq, abs_of_neg hη, mul_neg, neg_sq]
    congr 4
    ring
  · refine ⟨2 * Real.pi * y, by rw [abs_of_pos h], ?_⟩
    filter_upwards [eventually_gt_nhds h] with η hη
    rw [Pi.mul_apply, kernelSymbol, expSymbol, freq, abs_of_pos hη]
    congr 4
    ring

/-- `2π|ξ|` is of class `C²` on `ℝ ∖ {0}`. -/
theorem contDiffAt_freq {ξ : ℝ} (hξ : ξ ≠ 0) : ContDiffAt ℝ 2 freq ξ :=
  contDiffAt_const.mul (contDiffAt_abs hξ)

/-- The symbol is of class `C²`: "`m` vanishes in a neighborhood of the origin so that there is no
difficulty differentiating `|λ|`" (McConnell (1984), p. 750). -/
private theorem contDiff_kernelSymbol {m : ℝ → ℂ} (hm : ContDiffOn ℝ 2 m {0}ᶜ)
    (h0 : (0 : ℝ) ∉ tsupport m) (y : ℝ) : ContDiff ℝ 2 (kernelSymbol m y) :=
  contDiff_mul_of_notMem_tsupport hm h0 fun ξ hξ => Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
    (((contDiffAt_freq hξ).pow 2).mul ((contDiffAt_freq hξ).mul contDiffAt_const).neg.exp)

/-- The symbol has compact support. -/
private theorem hasCompactSupport_kernelSymbol {m : ℝ → ℂ} (hs : HasCompactSupport m) (y : ℝ) :
    HasCompactSupport (kernelSymbol m y) :=
  hs.mul_right

/-- The symbol is integrable. -/
private theorem integrable_kernelSymbol {m : ℝ → ℂ} (hm : ContDiffOn ℝ 2 m {0}ᶜ)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) (y : ℝ) :
    Integrable (kernelSymbol m y) :=
  (contDiff_kernelSymbol hm h0 y).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_kernelSymbol hs y)

/-! ### The kernel -/

/-- The kernel is the derivative of order `2` of the Poisson integral `v`. -/
theorem iteratedPoissonDeriv_two (m : ℝ → ℂ) (y : ℝ) :
    iteratedPoissonDeriv 2 m y = mihlinKernel m y := by
  rw [mihlinKernel_eq]
  refine congrArg _ (funext fun ξ => ?_)
  rw [smul_eq_mul, mul_comm, neg_sq, kernelSymbol]

/-- `mihlinKernel m y s` is the derivative of `v_y (s, y)` in `y`, `y > 0`. -/
theorem hasDerivAt_poissonDeriv {m : ℝ → ℂ} (hm : Integrable m) {y : ℝ} (hy : 0 < y) (s : ℝ) :
    HasDerivAt (fun y => poissonDeriv m y s) (mihlinKernel m y s) y := by
  simpa only [iteratedPoissonDeriv_one, Nat.reduceAdd, iteratedPoissonDeriv_two] using
    hasDerivAt_iteratedPoissonDeriv 1 hm hy s

/-- `mihlinKernel m y s` is the second derivative `v_{yy} (s, y)` in `y` of the Poisson integral
`v (s, y) = poissonInt m y s` of `𝓕⁻ m`, `y > 0`. -/
theorem iteratedDeriv_two_poissonInt {m : ℝ → ℂ} (hm : Integrable m) {y : ℝ} (hy : 0 < y)
    (s : ℝ) : iteratedDeriv 2 (fun y => poissonInt m y s) y = mihlinKernel m y s := by
  rw [iteratedDeriv_poissonInt 2 hm hy, iteratedPoissonDeriv_two]

/-- The kernel is a continuous function of `s`. -/
theorem continuous_mihlinKernel {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) (hs : HasCompactSupport m)
    (h0 : (0 : ℝ) ∉ tsupport m) (y : ℝ) : Continuous (mihlinKernel m y) :=
  continuous_fourierInv_of_integrable (integrable_kernelSymbol hm.1 hs h0 y)

/-- `∫ r^k e^{−r} dξ = 2 k! / b` for `r = b|ξ|`, `b > 0`. -/
private theorem integral_abs_pow_mul_exp (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ ξ : ℝ, (b * |ξ|) ^ k * Real.exp (-(b * |ξ|)) = 2 * (k.factorial / b) := by
  rw [integral_comp_abs (f := fun x => (b * x) ^ k * Real.exp (-(b * x))),
    integral_comp_mul_left_Ioi (fun x => x ^ k * Real.exp (-x)) 0 hb, mul_zero,
    ← Real.Gamma_nat_eq_factorial, Real.Gamma_eq_integral (by positivity), smul_eq_mul,
    div_eq_inv_mul]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [add_sub_cancel_right, Real.rpow_natCast, mul_comm]

/-- `r^k e^{−r}`, `r = b|ξ|`, is integrable. -/
theorem integrable_abs_pow_mul_exp (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun ξ : ℝ => (b * |ξ|) ^ k * Real.exp (-(b * |ξ|)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_abs_pow_mul_exp k hb]
  positivity

/-- `|m (ξ) (2π|ξ|)² e^{−2π|ξ|y}| ≤ (c / y²) r² e^{−r}`, `r = 2πy|ξ|`. -/
private theorem norm_kernelSymbol_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) {y : ℝ} (hy : 0 < y)
    (ξ : ℝ) : ‖kernelSymbol m y ξ‖ ≤
      c / y ^ 2 * ((2 * Real.pi * y * |ξ|) ^ 2 * Real.exp (-(2 * Real.pi * y * |ξ|))) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [kernelSymbol, freq]
  have h := norm_le_of_isMihlin hm hξ
  have h1 : 2 * Real.pi * |ξ| * y = 2 * Real.pi * y * |ξ| := by ring
  rw [kernelSymbol, freq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), h1]
  calc ‖m ξ‖ * ((2 * Real.pi * |ξ|) ^ 2 * Real.exp (-(2 * Real.pi * y * |ξ|)))
      ≤ c * ((2 * Real.pi * |ξ|) ^ 2 * Real.exp (-(2 * Real.pi * y * |ξ|))) := by gcongr
    _ = _ := by
      field_simp

/-- The bound of the case `|s| < y` of the proof of Lemma 3.1 (McConnell (1984), p. 749), valid for
all `s`: `|v_{yy}| ≤ 2c / (π y³)`. -/
private theorem norm_mihlinKernel_le_div {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) {y : ℝ}
    (hy : 0 < y) (s : ℝ) : ‖mihlinKernel m y s‖ ≤ 2 * c / (Real.pi * y ^ 3) := by
  have hb : 0 < 2 * Real.pi * y := by positivity
  rw [mihlinKernel_eq, fourierInv_eq_expChar]
  refine (norm_integral_le_of_norm_le ((integrable_abs_pow_mul_exp 2 hb).const_mul (c / y ^ 2))
    (ae_of_all _ fun ξ => ?_)).trans_eq ?_
  · rw [norm_smul, norm_expChar, one_mul]
    exact norm_kernelSymbol_le hm hy ξ
  · rw [integral_const_mul, integral_abs_pow_mul_exp 2 hb, Nat.factorial_two]
    push_cast
    field_simp

/-- `|(2πξ)² e^{−aξ}| = (2π)² |ξ|² e^{−r}`, `r = aξ`. -/
private theorem norm_expSymbol {a ξ r : ℝ} (ha : a * ξ = r) :
    ‖expSymbol a ξ‖ = (2 * Real.pi) ^ 2 * |ξ| ^ 2 * Real.exp (-r) := by
  rw [expSymbol, Complex.norm_real, Real.norm_of_nonneg (by positivity), ha, mul_pow, sq_abs]

/-- `|((2πξ)² e^{−aξ})'| ≤ (2π)² |ξ| (2 + r) e^{−r}`, `r = aξ ≥ 0`. -/
private theorem norm_iteratedDeriv_one_expSymbol_le {a ξ r : ℝ} (ha : a * ξ = r) (hr : 0 ≤ r) :
    ‖iteratedDeriv 1 (expSymbol a) ξ‖ ≤
      (2 * Real.pi) ^ 2 * |ξ| * (2 + r) * Real.exp (-r) := by
  have h : 2 * ξ - a * ξ ^ 2 = ξ * (2 - r) := by
    rw [← ha]
    ring
  have h' : |2 - r| ≤ 2 + r := abs_le.2 ⟨by linarith, by linarith⟩
  rw [iteratedDeriv_one_expSymbol, Complex.norm_real, ha, h, norm_mul, norm_mul, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (sq_nonneg (2 * Real.pi)),
    Real.norm_eq_abs, Real.norm_eq_abs, ← mul_assoc]
  gcongr

/-- `|((2πξ)² e^{−aξ})''| ≤ (2π)² (2 + 4 r + r²) e^{−r}`, `r = aξ ≥ 0`. -/
private theorem norm_iteratedDeriv_two_expSymbol_le {a ξ r : ℝ} (ha : a * ξ = r) (hr : 0 ≤ r) :
    ‖iteratedDeriv 2 (expSymbol a) ξ‖ ≤
      (2 * Real.pi) ^ 2 * (2 + 4 * r + r ^ 2) * Real.exp (-r) := by
  have h' : |2 - 4 * r + r ^ 2| ≤ 2 + 4 * r + r ^ 2 := abs_le.2 ⟨by nlinarith, by linarith⟩
  rw [iteratedDeriv_two_expSymbol, Complex.norm_real, ha, norm_mul, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (sq_nonneg (2 * Real.pi)),
    Real.norm_eq_abs]
  gcongr

/-- Leibniz's formula (McConnell (1984), pp. 749–750), with `r = 2πy|ξ|`: the second derivative of
`m (ξ) (2π|ξ|)² e^{−2π|ξ|y}` is at most `(2π)² c (7 + 6 r + r²) e^{−r}`. -/
private theorem norm_iteratedDeriv_two_kernelSymbol_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    {y : ℝ} (hy : 0 < y) {ξ : ℝ} (hξ : ξ ≠ 0) {r : ℝ} (hr : r = 2 * Real.pi * y * |ξ|) :
    ‖iteratedDeriv 2 (kernelSymbol m y) ξ‖ ≤
      (2 * Real.pi) ^ 2 * c * ((7 + 6 * r + r ^ 2) * Real.exp (-r)) := by
  obtain ⟨a, ha, hF⟩ := exists_kernelSymbol_eventuallyEq m y hξ
  rw [← hr] at ha
  have hr0 : 0 ≤ r := by
    rw [hr]
    positivity
  have hmc : ContDiffAt ℝ 2 m ξ := hm.1.contDiffAt (isOpen_compl_singleton.mem_nhds hξ)
  have h0 := norm_le_of_isMihlin hm hξ
  have h1 := hm.2 1 (by norm_num) ξ hξ
  have h2 := hm.2 2 le_rfl ξ hξ
  rw [pow_one] at h1
  have hL : iteratedDeriv 2 (kernelSymbol m y) ξ = m ξ * iteratedDeriv 2 (expSymbol a) ξ +
      2 * iteratedDeriv 1 m ξ * iteratedDeriv 1 (expSymbol a) ξ +
      iteratedDeriv 2 m ξ * expSymbol a ξ := by
    rw [hF.iteratedDeriv_eq 2, iteratedDeriv_mul hmc (contDiff_expSymbol a).contDiffAt]
    simp [Finset.sum_range_succ]
  -- the three terms
  have t0 : ‖m ξ * iteratedDeriv 2 (expSymbol a) ξ‖ ≤
      c * ((2 * Real.pi) ^ 2 * (2 + 4 * r + r ^ 2) * Real.exp (-r)) := by
    rw [norm_mul]
    exact mul_le_mul h0 (norm_iteratedDeriv_two_expSymbol_le ha hr0) (norm_nonneg _)
      ((norm_nonneg _).trans h0)
  have t1 : ‖2 * iteratedDeriv 1 m ξ * iteratedDeriv 1 (expSymbol a) ξ‖ ≤
      2 * (c * ((2 * Real.pi) ^ 2 * (2 + r) * Real.exp (-r))) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, mul_assoc]
    calc 2 * (‖iteratedDeriv 1 m ξ‖ * ‖iteratedDeriv 1 (expSymbol a) ξ‖)
        ≤ 2 * (‖iteratedDeriv 1 m ξ‖ *
            ((2 * Real.pi) ^ 2 * |ξ| * (2 + r) * Real.exp (-r))) := by
          gcongr
          exact norm_iteratedDeriv_one_expSymbol_le ha hr0
      _ = 2 * ((|ξ| * ‖iteratedDeriv 1 m ξ‖) *
            ((2 * Real.pi) ^ 2 * (2 + r) * Real.exp (-r))) := by ring
      _ ≤ _ := by gcongr
  have t2 : ‖iteratedDeriv 2 m ξ * expSymbol a ξ‖ ≤
      c * ((2 * Real.pi) ^ 2 * Real.exp (-r)) := by
    rw [norm_mul, norm_expSymbol ha]
    calc ‖iteratedDeriv 2 m ξ‖ * ((2 * Real.pi) ^ 2 * |ξ| ^ 2 * Real.exp (-r))
        = (|ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖) * ((2 * Real.pi) ^ 2 * Real.exp (-r)) := by ring
      _ ≤ _ := by gcongr
  rw [hL]
  refine (norm_add₃_le.trans (add_le_add (add_le_add t0 t1) t2)).trans_eq ?_
  ring

/-- Two integrations by parts (McConnell (1984), p. 749): `−(2πs)² v_{yy}` is the inverse Fourier
transform of the second derivative of the symbol. -/
private theorem fourierInv_iteratedDeriv_two_kernelSymbol {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) (y s : ℝ) :
    𝓕⁻ (iteratedDeriv 2 (kernelSymbol m y)) s =
      -(((2 * Real.pi * s) ^ 2 : ℝ) : ℂ) * mihlinKernel m y s := by
  have hF := contDiff_kernelSymbol hm.1 h0 y
  have hc := hasCompactSupport_kernelSymbol hs y
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (iteratedDeriv n (kernelSymbol m y)) :=
    fun n hn => Continuous.integrable_of_hasCompactSupport
      (hF.continuous_iteratedDeriv n (by exact_mod_cast hn)) (hasCompactSupport_iteratedDeriv hc n)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_iteratedDeriv (N := 2) hF hint le_rfl,
    mihlinKernel_eq, Real.fourierInv_eq_fourier_neg]
  simp only [smul_eq_mul]
  congr 1
  push_cast
  linear_combination ((2 * Real.pi * s) ^ 2 : ℂ) * Complex.I_sq

/-- The bound of the case `|s| ≥ y` of the proof of Lemma 3.1 (McConnell (1984), pp. 749–750), valid
for all `s`: `s² |v_{yy}| ≤ 15c / (π y)`. -/
private theorem sq_mul_norm_mihlinKernel_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c)
    (hs : HasCompactSupport m) (h0 : (0 : ℝ) ∉ tsupport m) {y : ℝ} (hy : 0 < y) (s : ℝ) :
    s ^ 2 * ‖mihlinKernel m y s‖ ≤ 15 * c / (Real.pi * y) := by
  have hb : 0 < 2 * Real.pi * y := by positivity
  have i0 := (integrable_abs_pow_mul_exp 0 hb).const_mul 7
  have i1 := (integrable_abs_pow_mul_exp 1 hb).const_mul 6
  have i2 := integrable_abs_pow_mul_exp 2 hb
  have h1 : ‖𝓕⁻ (iteratedDeriv 2 (kernelSymbol m y)) s‖ ≤
      (2 * Real.pi) ^ 2 * (15 * c / (Real.pi * y)) := by
    rw [fourierInv_eq_expChar]
    refine (norm_integral_le_of_norm_le (((i0.add i1).add i2).const_mul ((2 * Real.pi) ^ 2 * c))
      ?_).trans_eq ?_
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ξ hξ
      rw [norm_smul, norm_expChar, one_mul]
      refine (norm_iteratedDeriv_two_kernelSymbol_le hm hy hξ rfl).trans_eq ?_
      simp only [Pi.add_apply]
      ring
    · rw [integral_const_mul, integral_add' (i0.add i1) i2, integral_add' i0 i1,
        integral_const_mul, integral_const_mul, integral_abs_pow_mul_exp 0 hb,
        integral_abs_pow_mul_exp 1 hb, integral_abs_pow_mul_exp 2 hb, Nat.factorial_two,
        Nat.factorial_one, Nat.factorial_zero]
      push_cast
      field_simp
      ring
  rw [fourierInv_iteratedDeriv_two_kernelSymbol hm hs h0, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _), mul_pow, mul_assoc] at h1
  exact le_of_mul_le_mul_left h1 (by positivity)

/-- McConnell (1984), Lemma 3.1, for `n = 1`: `e (s, y) = y² v_{yy} (s, y) / h (s, y)` is bounded by
a multiple of the constant of (1.10).

Departure from the source: the source treats `|s| < y` and `|s| ≥ y` separately. Both its bounds,
`π y³ |v_{yy}| ≤ 2c` and `π y s² |v_{yy}| ≤ 15c`, hold for all `s` and are added here, since
`y² |v_{yy}| / h = π y (y² + s²) |v_{yy}|`; this gives the constant `17`. -/
theorem norm_mihlinKernel_le {m : ℝ → ℂ} {c : ℝ} (hm : IsMihlin m c) (hs : HasCompactSupport m)
    (h0 : (0 : ℝ) ∉ tsupport m) {y : ℝ} (hy : 0 < y) (s : ℝ) :
    y ^ 2 * ‖mihlinKernel m y s‖ ≤ 17 * c * cauchyDensity y s := by
  have h1 := norm_mihlinKernel_le_div hm hy s
  have h2 := sq_mul_norm_mihlinKernel_le hm hs h0 hy s
  rw [le_div_iff₀ (by positivity)] at h1 h2
  rw [cauchyDensity, mul_div_assoc', le_div_iff₀ (by positivity)]
  calc y ^ 2 * ‖mihlinKernel m y s‖ * (Real.pi * (s ^ 2 + y ^ 2))
      = y * (‖mihlinKernel m y s‖ * (Real.pi * y ^ 3) +
          s ^ 2 * ‖mihlinKernel m y s‖ * (Real.pi * y)) := by ring
    _ ≤ y * (2 * c + 15 * c) := by gcongr
    _ = 17 * c * y := by ring

end HarmonicAnalysis
