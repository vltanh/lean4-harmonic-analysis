/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Harmonic polynomials with coefficients in a Banach space, and their conjugates

D. L. Burkholder, *A geometric condition that implies the existence of certain singular integrals of
Banach-space-valued functions* (1983), p. 278, (18) and (19): for vectors `a_1, …, a_N` and
`b_1, …, b_N` of a real Banach space,

`u (r e^{iθ}) = Σ_{k=1}^N (a_k cos kθ + b_k sin kθ) r^k`,
`v (r e^{iθ}) = Σ_{k=1}^N (a_k sin kθ − b_k cos kθ) r^k`.

As functions of `z = r e^{iθ}`, `z^k = r^k (cos kθ + i sin kθ)`: `u (z) = Σ_k (Re z^k a_k + Im z^k
b_k)` (`harmPoly`) and `v (z) = Σ_k (Im z^k a_k − Re z^k b_k)` (`conjHarmPoly`). Since `z^k` is
holomorphic with derivative `k z^{k−1}`, the partial derivatives are `u_x (z) = Σ_k (Re (k z^{k−1})
a_k + Im (k z^{k−1}) b_k)`, `u_y` the same with `i k z^{k−1}`, and `u_{xy}` the same with
`i k (k − 1) z^{k−2}`.

* `harmDx_conj`, `harmDy_conj`: `v_x = −u_y`, `v_y = u_x`.
* `norm_harmPoly_sub_le`: the Taylor estimate of p. 279, in which Laplace's equation
  `u_{xx} + u_{yy} = 0` is used. The source bounds the third derivatives of `Re z^k` and `Im z^k` in
  the disc `|z| < 2` by `k³ 2^{k−3}` and refers to Taylor's theorem; here the remainder of the
  Taylor polynomial of `z^k` is bounded with the same factor `k³ 2^{k−3}`, by induction on `k`. The
  estimate is printed with `<`, which fails for `u = 0`; it is used with `≤`.
* `harmPoly_rotate`: `u (e^{iα} z)` is of the form (18), with the conjugate `v (e^{iα} z)`.
-/

@[expose] public section

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Burkholder (1983), (18): `u (z) = Σ_{k=1}^N (Re z^k a_k + Im z^k b_k)`, that is,
`u (r e^{iθ}) = Σ_{k=1}^N (a_k cos kθ + b_k sin kθ) r^k`. -/
noncomputable def harmPoly (N : ℕ) (a b : ℕ → X) (z : ℂ) : X :=
  ∑ k ∈ Finset.Icc 1 N, ((z ^ k).re • a k + (z ^ k).im • b k)

/-- Burkholder (1983), (19): `v (z) = Σ_{k=1}^N (Im z^k a_k − Re z^k b_k)`, that is,
`v (r e^{iθ}) = Σ_{k=1}^N (a_k sin kθ − b_k cos kθ) r^k`. -/
noncomputable def conjHarmPoly (N : ℕ) (a b : ℕ → X) (z : ℂ) : X :=
  ∑ k ∈ Finset.Icc 1 N, ((z ^ k).im • a k - (z ^ k).re • b k)

/-- The partial derivative `u_x`. -/
noncomputable def harmDx (N : ℕ) (a b : ℕ → X) (z : ℂ) : X :=
  ∑ k ∈ Finset.Icc 1 N, ((k * z ^ (k - 1)).re • a k + (k * z ^ (k - 1)).im • b k)

/-- The partial derivative `u_y`. -/
noncomputable def harmDy (N : ℕ) (a b : ℕ → X) (z : ℂ) : X :=
  ∑ k ∈ Finset.Icc 1 N,
    ((Complex.I * k * z ^ (k - 1)).re • a k + (Complex.I * k * z ^ (k - 1)).im • b k)

/-- The second partial derivative `u_{xy}`. -/
noncomputable def harmDxy (N : ℕ) (a b : ℕ → X) (z : ℂ) : X :=
  ∑ k ∈ Finset.Icc 1 N, ((Complex.I * (k * (k - 1)) * z ^ (k - 2)).re • a k +
    (Complex.I * (k * (k - 1)) * z ^ (k - 2)).im • b k)

/-- The constant `γ = N³ 2^N Σ_{k=1}^N (|a_k| + |b_k|)` of p. 279. -/
noncomputable def harmConst (N : ℕ) (a b : ℕ → X) : ℝ :=
  N ^ 3 * 2 ^ N * ∑ k ∈ Finset.Icc 1 N, (‖a k‖ + ‖b k‖)

/-! ### The real-linear map `(g_k) ↦ Σ_k (Re g_k a_k + Im g_k b_k)` -/

/-- `Σ_{k=1}^N (Re g_k a_k + Im g_k b_k)`, for complex numbers `g_k`: the function `u` and its
partial derivatives are of this form. -/
private noncomputable def reSum (N : ℕ) (a b : ℕ → X) (g : ℕ → ℂ) : X :=
  ∑ k ∈ Finset.Icc 1 N, ((g k).re • a k + (g k).im • b k)

/-- The sum is additive in the numbers `g_k`. -/
private theorem reSum_sub (N : ℕ) (a b : ℕ → X) (g g' : ℕ → ℂ) :
    reSum N a b g - reSum N a b g' = reSum N a b fun k => g k - g' k := by
  simp only [reSum, ← Finset.sum_sub_distrib, Complex.sub_re, Complex.sub_im, sub_smul]
  exact Finset.sum_congr rfl fun k _ => by abel

/-- The sum is homogeneous for real factors. -/
private theorem smul_reSum (N : ℕ) (a b : ℕ → X) (c : ℝ) (g : ℕ → ℂ) :
    c • reSum N a b g = reSum N a b fun k => c * g k := by
  simp only [reSum, Finset.smul_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul, smul_add,
    smul_smul]

/-- The coefficients `−b_k`, `a_k` in place of `a_k`, `b_k` correspond to the factor `−i`. -/
private theorem reSum_conj (N : ℕ) (a b : ℕ → X) (g : ℕ → ℂ) :
    reSum N (-b) a g = reSum N a b fun k => -Complex.I * g k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [add_comm]

/-- `|Σ_k (Re g_k a_k + Im g_k b_k)| ≤ c Σ_k (|a_k| + |b_k|)` if `|g_k| ≤ c`. -/
private theorem norm_reSum_le (N : ℕ) (a b : ℕ → X) {g : ℕ → ℂ} {c : ℝ}
    (hg : ∀ k ∈ Finset.Icc 1 N, ‖g k‖ ≤ c) :
    ‖reSum N a b g‖ ≤ c * ∑ k ∈ Finset.Icc 1 N, (‖a k‖ + ‖b k‖) := by
  rw [Finset.mul_sum]
  refine norm_sum_le_of_le _ fun k hk => (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, mul_add]
  gcongr
  · exact (Complex.abs_re_le_norm _).trans (hg k hk)
  · exact (Complex.abs_im_le_norm _).trans (hg k hk)

/-- The sum is differentiated term by term. -/
private theorem hasDerivAt_reSum (N : ℕ) (a b : ℕ → X) {g : ℝ → ℕ → ℂ} {g' : ℕ → ℂ} {t : ℝ}
    (h : ∀ k, HasDerivAt (fun s => g s k) (g' k) t) :
    HasDerivAt (fun s => reSum N a b (g s)) (reSum N a b g') t := by
  refine HasDerivAt.fun_sum fun k _ => HasDerivAt.add ?_ ?_
  · exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (h k)).smul_const (a k)
  · exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (h k)).smul_const (b k)

/-! ### The conjugate and the partial derivatives -/

/-- The conjugate of `u` is the function (18) with the coefficients `−b_k` and `a_k`. -/
theorem conjHarmPoly_eq (N : ℕ) (a b : ℕ → X) (z : ℂ) :
    conjHarmPoly N a b z = harmPoly N (-b) a z := by
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.neg_apply, smul_neg]
  abel

/-- `u_x` is the derivative of `u` in the direction of the real axis. -/
theorem hasDerivAt_harmPoly_re (N : ℕ) (a b : ℕ → X) (z : ℂ) :
    HasDerivAt (fun t : ℝ => harmPoly N a b (z + t)) (harmDx N a b z) 0 := by
  refine hasDerivAt_reSum N a b (g := fun t k => (z + (t : ℂ)) ^ k) fun k => ?_
  have h := ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_add z).fun_pow k
  simpa using h.comp_ofReal

/-- The derivative of `w ↦ (z + i w)^k` at `0` is `k z^{k−1} i`. -/
private theorem hasDerivAt_pow_add_mul_I (z : ℂ) (k : ℕ) :
    HasDerivAt (fun w : ℂ => (z + w * Complex.I) ^ k) (k * z ^ (k - 1) * Complex.I)
      ((0 : ℝ) : ℂ) := by
  simpa using (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const Complex.I).const_add z).fun_pow k

/-- `u_y` is the derivative of `u` in the direction of the imaginary axis. -/
theorem hasDerivAt_harmPoly_im (N : ℕ) (a b : ℕ → X) (z : ℂ) :
    HasDerivAt (fun t : ℝ => harmPoly N a b (z + t * Complex.I)) (harmDy N a b z) 0 := by
  refine hasDerivAt_reSum N a b (g := fun t k => (z + t * Complex.I) ^ k) fun k => ?_
  convert (hasDerivAt_pow_add_mul_I z k).comp_ofReal using 1
  ring

/-- `u_{xy}` is the derivative of `u_x` in the direction of the imaginary axis. -/
theorem hasDerivAt_harmDx_im (N : ℕ) (a b : ℕ → X) (z : ℂ) :
    HasDerivAt (fun t : ℝ => harmDx N a b (z + t * Complex.I)) (harmDxy N a b z) 0 := by
  refine hasDerivAt_reSum N a b (g := fun t k => k * (z + t * Complex.I) ^ (k - 1)) fun k => ?_
  convert ((hasDerivAt_pow_add_mul_I z (k - 1)).const_mul (k : ℂ)).comp_ofReal using 1
  rcases k with _ | k
  · simp
  · rw [show k + 1 - 2 = k + 1 - 1 - 1 by omega]
    push_cast [Nat.add_sub_cancel]
    ring

/-- `v_x = −u_y`. -/
theorem harmDx_conj (N : ℕ) (a b : ℕ → X) (z : ℂ) :
    harmDx N (-b) a z = -harmDy N a b z := by
  refine (reSum_conj N a b _).trans ?_
  rw [harmDy, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  beta_reduce
  rw [neg_mul, ← mul_assoc, Complex.neg_re, Complex.neg_im, neg_smul, neg_smul, neg_add]

/-- `v_y = u_x`. -/
theorem harmDy_conj (N : ℕ) (a b : ℕ → X) (z : ℂ) :
    harmDy N (-b) a z = harmDx N a b z := by
  refine (reSum_conj N a b _).trans (Finset.sum_congr rfl fun k _ => ?_)
  beta_reduce
  rw [show -Complex.I * (Complex.I * k * z ^ (k - 1)) = k * z ^ (k - 1) by
    linear_combination (-(k : ℂ) * z ^ (k - 1)) * Complex.I_mul_I]

omit [NormedSpace ℝ X] in
/-- The conjugate has the same constant `γ`. -/
theorem harmConst_conj (N : ℕ) (a b : ℕ → X) : harmConst N (-b) a = harmConst N a b := by
  simp only [harmConst, Pi.neg_apply, norm_neg, add_comm]

/-! ### The Taylor estimate -/

/-- The remainder of the Taylor polynomial of degree 2 of `z ↦ z^m`:
`|(z + ζ)^m − z^m − m z^{m−1} ζ − (m (m − 1) / 2) z^{m−2} ζ²| ≤ m³ 2^{m−3} |ζ|³` for `|z| ≤ 1`,
`|z + ζ| ≤ 2`, by induction on `m`. (The source bounds the third derivatives by `m³ 2^{m−3}` in
`|z| < 2` and refers to Taylor's theorem.) -/
private theorem norm_pow_taylor_le {z ζ : ℂ} (hz : ‖z‖ ≤ 1) (hzζ : ‖z + ζ‖ ≤ 2) (m : ℕ) :
    ‖(z + ζ) ^ m - z ^ m - m * z ^ (m - 1) * ζ - m * (m - 1) / 2 * z ^ (m - 2) * ζ ^ 2‖ ≤
      m ^ 3 * 2 ^ m / 8 * ‖ζ‖ ^ 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- `R_{m+1} = (z + ζ) R_m + (m (m − 1) / 2) z^{m−2} ζ³`
    have hrec : (z + ζ) ^ (m + 1) - z ^ (m + 1) - (m + 1 : ℕ) * z ^ (m + 1 - 1) * ζ -
        (m + 1 : ℕ) * ((m + 1 : ℕ) - 1) / 2 * z ^ (m + 1 - 2) * ζ ^ 2 =
        (z + ζ) * ((z + ζ) ^ m - z ^ m - m * z ^ (m - 1) * ζ -
          m * (m - 1) / 2 * z ^ (m - 2) * ζ ^ 2) + m * (m - 1) / 2 * z ^ (m - 2) * ζ ^ 3 := by
      rcases m with _ | _ | m
      · simp
      · simp
        ring
      · simp only [Nat.add_sub_cancel, show m + 1 + 1 + 1 - 2 = m + 1 by omega,
          show m + 1 + 1 - 2 = m by omega]
        push_cast
        ring
    have hm1 : ‖(m : ℂ) * (m - 1)‖ ≤ m ^ 2 := by
      rcases m with _ | m
      · simp
      · rw [norm_mul, Nat.cast_succ, add_sub_cancel_right, ← Nat.cast_succ, Complex.norm_natCast,
          Complex.norm_natCast, sq]
        gcongr
        exact m.le_succ
    have hlast : ‖(m : ℂ) * (m - 1) / 2 * z ^ (m - 2) * ζ ^ 3‖ ≤ m ^ 2 / 2 * ‖ζ‖ ^ 3 := by
      rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_ofNat]
      gcongr
      exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg z) hz)).trans
        (by gcongr)
    have hfac : 2 * ((m : ℝ) ^ 3 * 2 ^ m / 8) + m ^ 2 / 2 ≤
        ((m + 1 : ℕ) : ℝ) ^ 3 * 2 ^ (m + 1) / 8 := by
      have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ one_le_two
      have hmul := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ 3 * (m : ℝ) ^ 2 + 3 * m + 1)
      push_cast
      rw [pow_succ (2 : ℝ) m]
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [hrec]
    calc _ ≤ 2 * (m ^ 3 * 2 ^ m / 8 * ‖ζ‖ ^ 3) + m ^ 2 / 2 * ‖ζ‖ ^ 3 := by
          refine (norm_add_le _ _).trans (add_le_add ?_ hlast)
          rw [norm_mul]
          gcongr
      _ = (2 * (m ^ 3 * 2 ^ m / 8) + m ^ 2 / 2) * ‖ζ‖ ^ 3 := by ring
      _ ≤ _ := by gcongr

/-- Laplace's equation: `ζ² = 2 i h k` for `ζ = h + i k` with `|h| = |k|`, so that in the Taylor
polynomial of `z ↦ z^m` the terms with `h²` and `k²` cancel. With `|ζ|³ ≤ 8 δ³` the remainder is at
most `m³ 2^m δ³`. -/
private theorem norm_pow_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    {h k : ℝ} (hh : |h| = δ) (hk : |k| = δ) (m : ℕ) :
    ‖(z + (h + k * Complex.I)) ^ m - z ^ m - h * (m * z ^ (m - 1)) -
        k * (Complex.I * m * z ^ (m - 1)) -
        (h * k : ℝ) * (Complex.I * (m * (m - 1)) * z ^ (m - 2))‖ ≤ m ^ 3 * 2 ^ m * δ ^ 3 := by
  have hδ0 : 0 ≤ δ := hh ▸ abs_nonneg h
  have hζ : ‖(h : ℂ) + k * Complex.I‖ ≤ 2 * δ := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, hh, hk, two_mul]
  have hzζ : ‖z + (h + k * Complex.I)‖ ≤ 2 := by
    linarith [norm_add_le z (h + k * Complex.I)]
  have hhk : (h : ℂ) ^ 2 = (k : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← sq_abs h, ← sq_abs k, hh, hk]
  have hsq : ((h : ℂ) + k * Complex.I) ^ 2 = 2 * Complex.I * h * k := by
    linear_combination hhk + (k : ℂ) ^ 2 * Complex.I_sq
  calc _ = ‖(z + (h + k * Complex.I)) ^ m - z ^ m - m * z ^ (m - 1) * (h + k * Complex.I) -
        m * (m - 1) / 2 * z ^ (m - 2) * (h + k * Complex.I) ^ 2‖ := by
        rw [hsq]
        congr 1
        push_cast
        ring
    _ ≤ m ^ 3 * 2 ^ m / 8 * (2 * δ) ^ 3 := (norm_pow_taylor_le hz hzζ m).trans (by gcongr)
    _ = _ := by ring

/-- The Taylor estimate of p. 279:
`|u (z + h + ik) − u (z) − u_x (z) h − u_y (z) k − u_{xy} (z) h k| ≤ γ δ³` for `|z| ≤ 1`,
`|h| = |k| = δ ≤ 1/2` (in the source `|z| < 1` and `0 < δ < 1/2`). The terms
`½ u_{xx} h² + ½ u_{yy} k²` vanish, by Laplace's equation. -/
theorem norm_harmPoly_sub_le (N : ℕ) (a b : ℕ → X) {z : ℂ} (hz : ‖z‖ ≤ 1) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    {h k : ℝ} (hh : |h| = δ) (hk : |k| = δ) :
    ‖harmPoly N a b (z + (h + k * Complex.I)) - harmPoly N a b z - h • harmDx N a b z -
        k • harmDy N a b z - (h * k) • harmDxy N a b z‖ ≤ harmConst N a b * δ ^ 3 := by
  have hδ0 : 0 ≤ δ := hh ▸ abs_nonneg h
  have hsum : harmPoly N a b (z + (h + k * Complex.I)) - harmPoly N a b z - h • harmDx N a b z -
      k • harmDy N a b z - (h * k) • harmDxy N a b z = reSum N a b fun m =>
        (z + (h + k * Complex.I)) ^ m - z ^ m - h * (m * z ^ (m - 1)) -
          k * (Complex.I * m * z ^ (m - 1)) -
          (h * k : ℝ) * (Complex.I * (m * (m - 1)) * z ^ (m - 2)) := by
    rw [← reSum_sub, ← reSum_sub, ← reSum_sub, ← reSum_sub, ← smul_reSum, ← smul_reSum,
      ← smul_reSum]
    rfl
  rw [hsum]
  refine (norm_reSum_le N a b (c := N ^ 3 * 2 ^ N * δ ^ 3) fun m hm => ?_).trans_eq ?_
  · refine (norm_pow_sub_le hz hδ hh hk m).trans ?_
    have hmN : (m : ℝ) ≤ N := Nat.cast_le.2 (Finset.mem_Icc.1 hm).2
    gcongr
    · exact one_le_two
    · exact (Finset.mem_Icc.1 hm).2
  · rw [harmConst]
    ring

/-- The functions (18) are continuous. -/
theorem continuous_harmPoly (N : ℕ) (a b : ℕ → X) : Continuous (harmPoly N a b) := by
  unfold harmPoly
  fun_prop

/-- A bound of `u` on the disc `|z| ≤ 2`. -/
theorem norm_harmPoly_le (N : ℕ) (a b : ℕ → X) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖harmPoly N a b z‖ ≤ 2 ^ N * ∑ k ∈ Finset.Icc 1 N, (‖a k‖ + ‖b k‖) := by
  refine norm_reSum_le N a b (g := fun k => z ^ k) fun k hk => ?_
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg z) hz k).trans
    (pow_le_pow_right₀ one_le_two (Finset.mem_Icc.1 hk).2)

/-- The rotation `u^α (z) = u (e^{iα} z)` is of the form (18), with the coefficients
`a_k cos kα + b_k sin kα` and `b_k cos kα − a_k sin kα` (`ζ = e^{iα}`). -/
theorem harmPoly_rotate (N : ℕ) (a b : ℕ → X) (ζ z : ℂ) :
    harmPoly N a b (ζ * z) = harmPoly N (fun k => (ζ ^ k).re • a k + (ζ ^ k).im • b k)
      (fun k => (ζ ^ k).re • b k - (ζ ^ k).im • a k) z := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, Complex.mul_re, Complex.mul_im]
  module

/-- The conjugate of the rotated function is the rotated conjugate. -/
theorem conjHarmPoly_rotate (N : ℕ) (a b : ℕ → X) (ζ z : ℂ) :
    conjHarmPoly N a b (ζ * z) = conjHarmPoly N (fun k => (ζ ^ k).re • a k + (ζ ^ k).im • b k)
      (fun k => (ζ ^ k).re • b k - (ζ ^ k).im • a k) z := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, Complex.mul_re, Complex.mul_im]
  module

/-- The constant `γ` of the rotated function. -/
theorem harmConst_rotate_le (N : ℕ) (a b : ℕ → X) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    harmConst N (fun k => (ζ ^ k).re • a k + (ζ ^ k).im • b k)
      (fun k => (ζ ^ k).re • b k - (ζ ^ k).im • a k) ≤ 2 * harmConst N a b := by
  rw [harmConst, harmConst, mul_left_comm, Finset.mul_sum _ _ (2 : ℝ)]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
  have h1 : |(ζ ^ k).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (by simp [hζ])
  have h2 : |(ζ ^ k).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (by simp [hζ])
  have hs : ∀ {c : ℝ} (x : X), |c| ≤ 1 → ‖c • x‖ ≤ ‖x‖ := fun {c} x hc => by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg x) hc
  calc _ ≤ ‖a k‖ + ‖b k‖ + (‖b k‖ + ‖a k‖) := add_le_add
        ((norm_add_le _ _).trans (add_le_add (hs (a k) h1) (hs (b k) h2)))
        ((norm_sub_le _ _).trans (add_le_add (hs (b k) h1) (hs (a k) h2)))
    _ = _ := by ring

end HarmonicAnalysis
