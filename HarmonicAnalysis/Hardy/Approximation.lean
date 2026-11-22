/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Hardy.Basic
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Trigonometric polynomials, convergence in `L²`, Fejér means, products of analytic functions

Tools for the matrix-valued Hardy classes `H¹` and `H²` of the circle.

* `circPoly_add`, `circPoly_mapRange`, `exists_circPoly_mul`: sums and images under linear maps of
  trigonometric polynomials, products of analytic polynomials.
* `IsHardyOne`: the Hardy class `H¹`, the matrix-valued functions with integrable entries whose
  Fourier coefficients of negative order vanish.
* `ae_eq_zero_of_matFourierCoeff_eq_zero`: a function with integrable entries is zero almost
  everywhere if its Fourier coefficients are zero.
* `TendstoLTwo F f`: the entries of `F N` converge to those of `f` in `L²`; Fourier coefficients of
  the limit and of products, subsequences that converge almost everywhere. The analytic polynomials
  are dense in `H²` (`IsHardyTwo.exists_tendsto_circPoly`).
* `fejerCoeff f K`: the coefficients of the `K`-th Fejér mean of `f`, a trigonometric polynomial.
  For `K ≥ 1` it is an average of `f` for the Fejér kernel, a probability density, so that it
  satisfies the bounds that `f` satisfies; the Fejér means of `f` converge to `f` in `L¹`.
* `IsHardyOne.bounded_mul`, `IsHardyOne.mul_bounded`: the product of a bounded analytic function and
  a function of `H¹` is in `H¹`, and its constant coefficient is the product of those of the
  factors; `IsHardyTwo.bounded_mul`, `IsHardyTwo.mul_bounded`: the product of a bounded analytic
  function and a function of `H²` is in `H²`.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix Topology

namespace HarmonicAnalysis

variable {l m n : Type*}

/-! ### Trigonometric polynomials -/

section Polynomials

variable {V V' : Type*} [AddCommMonoid V] [Module ℂ V] [AddCommMonoid V'] [Module ℂ V']

/-- The trigonometric polynomial whose coefficients are zero. -/
theorem circPoly_zero (t : UnitAddCircle) : circPoly (0 : ℤ →₀ V) t = 0 :=
  Finsupp.sum_zero_index

/-- The trigonometric polynomial `e_k x`. -/
theorem circPoly_single (k : ℤ) (x : V) (t : UnitAddCircle) :
    circPoly (Finsupp.single k x) t = fourier k t • x :=
  Finsupp.sum_single_index (smul_zero _)

/-- The sum of two trigonometric polynomials. -/
theorem circPoly_add (c d : ℤ →₀ V) (t : UnitAddCircle) :
    circPoly (c + d) t = circPoly c t + circPoly d t :=
  Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _

/-- The image of a trigonometric polynomial under a linear map. -/
theorem circPoly_mapRange (T : V →ₗ[ℂ] V') (c : ℤ →₀ V) (t : UnitAddCircle) :
    circPoly (c.mapRange T (map_zero T)) t = T (circPoly c t) := by
  rw [circPoly, Finsupp.sum_mapRange_index fun _ => smul_zero _, circPoly, map_finsuppSum]
  simp only [map_smul]

/-- The product of a scalar and a trigonometric polynomial. -/
theorem circPoly_smul (z : ℂ) (c : ℤ →₀ V) (t : UnitAddCircle) :
    circPoly (z • c) t = z • circPoly c t :=
  circPoly_mapRange (LinearMap.lsmul ℂ V z) c t

/-- A finite sum of trigonometric polynomials. -/
theorem circPoly_sum {ι : Type*} (s : Finset ι) (c : ι → ℤ →₀ V) (t : UnitAddCircle) :
    circPoly (∑ i ∈ s, c i) t = ∑ i ∈ s, circPoly (c i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact circPoly_zero t
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, circPoly_add, ih]

end Polynomials

/-- The product of two analytic polynomials is an analytic polynomial. -/
theorem exists_circPoly_mul [Fintype m] {c : ℤ →₀ Matrix l m ℂ} {d : ℤ →₀ Matrix m n ℂ}
    (hc : ∀ k ∈ c.support, 0 ≤ k) (hd : ∀ k ∈ d.support, 0 ≤ k) :
    ∃ e : ℤ →₀ Matrix l n ℂ, (∀ k ∈ e.support, 0 ≤ k) ∧
      ∀ t, circPoly e t = circPoly c t * circPoly d t := by
  refine ⟨∑ p ∈ c.support, ∑ q ∈ d.support, Finsupp.single (p + q) (c p * d q), fun k hk => ?_,
    fun t => ?_⟩
  · by_contra hlt
    refine Finsupp.mem_support_iff.1 hk ?_
    simp only [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
    have h1 := hc p hp
    have h2 := hd q hq
    exact Finsupp.single_eq_of_ne (by omega)
  · simp only [circPoly_sum, circPoly_single]
    rw [circPoly, circPoly, Finsupp.sum, Finsupp.sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [fourier_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- If `P` is an analytic polynomial, `e_1 P` is an analytic polynomial without constant term. -/
theorem exists_circPoly_fourier_smul {c : ℤ →₀ Matrix m n ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k) :
    ∃ d : ℤ →₀ Matrix m n ℂ, (∀ k ∈ d.support, 0 < k) ∧
      ∀ t, circPoly d t = fourier 1 t • circPoly c t := by
  refine ⟨c.embDomain (addRightEmbedding 1), fun k hk => ?_, fun t => ?_⟩
  · rw [Finsupp.support_embDomain] at hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hk
    rw [addRightEmbedding_apply]
    have := hc q hq
    omega
  · rw [circPoly, Finsupp.sum_embDomain, circPoly, Finsupp.smul_sum]
    refine Finsupp.sum_congr fun q _ => ?_
    rw [addRightEmbedding_apply, smul_smul, ← fourier_add, add_comm]

/-- If `P` is an analytic polynomial without constant term, `(1 + P) D` is an analytic polynomial
with the constant coefficient `D`. -/
theorem exists_circPoly_eq_one_add_mul [Fintype n] [DecidableEq n] {c : ℤ →₀ Matrix n n ℂ}
    (hc : ∀ k ∈ c.support, 0 < k) (D : Matrix n l ℂ) :
    ∃ d : ℤ →₀ Matrix n l ℂ, (∀ k ∈ d.support, 0 ≤ k) ∧ d 0 = D ∧
      ∀ t, circPoly d t = (1 + circPoly c t) * D := by
  classical
  let T : Matrix n n ℂ →ₗ[ℂ] Matrix n l ℂ := mulRightLinearMap n ℂ D
  refine ⟨Finsupp.single 0 D + c.mapRange T (map_zero T), fun k hk => ?_, ?_, fun t => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hk) with h | h
    · rw [(Finsupp.mem_support_single k 0 _).1 h |>.1]
    · exact (hc k (Finsupp.support_mapRange h)).le
  · have h0 : c 0 = 0 := Finsupp.notMem_support_iff.1 fun h => lt_irrefl _ (hc 0 h)
    rw [Finsupp.add_apply, Finsupp.mapRange_apply, h0, map_zero T, add_zero,
      Finsupp.single_eq_same]
  · rw [circPoly_add, circPoly_single, fourier_zero, one_smul, circPoly_mapRange, Matrix.add_mul,
      Matrix.one_mul]
    rfl

/-! ### Measurable and integrable functions -/

/-- Continuous functions on the circle are integrable. -/
theorem integrable_haar_of_continuous {E : Type*} [NormedAddCommGroup E] {u : UnitAddCircle → E}
    (hu : Continuous u) : Integrable u haarAddCircle :=
  hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The entries of a continuous function are bounded. -/
theorem exists_bound_of_continuous [Finite m] [Finite n] {f : UnitAddCircle → Matrix m n ℂ}
    (hf : Continuous f) : ∃ C : ℝ, ∀ t i j, ‖f t i j‖ ≤ C := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  obtain ⟨C, hC⟩ :=
    isCompact_univ.exists_bound_of_continuousOn (E := m → n → ℂ) hf.continuousOn
  exact ⟨C, fun t i j => ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans
    (hC t (Set.mem_univ t))⟩

/-- The entries of a product of functions with measurable entries are measurable. -/
theorem aestronglyMeasurable_mul [Fintype m] {f : UnitAddCircle → Matrix l m ℂ}
    {g : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, AEStronglyMeasurable (fun t => f t i j) haarAddCircle)
    (hg : ∀ i j, AEStronglyMeasurable (fun t => g t i j) haarAddCircle) (i : l) (j : n) :
    AEStronglyMeasurable (fun t => (f t * g t) i j) haarAddCircle := by
  simp only [Matrix.mul_apply]
  exact Finset.aestronglyMeasurable_fun_sum _ fun o _ => (hf i o).mul (hg o j)

/-- The entries of the product of a continuous function and a function with integrable entries are
integrable. -/
theorem integrable_continuous_mul [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    (hg : Continuous g) {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) (i : l) (j : n) :
    Integrable (fun t => (g t * f t) i j) haarAddCircle := by
  simp only [Matrix.mul_apply]
  refine integrable_finsetSum _ fun o _ => ?_
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hg.matrix_elem i o).continuousOn
  exact (hf o j).bdd_mul (c := C) (hg.matrix_elem i o).aestronglyMeasurable
    (ae_of_all _ fun t => hC t (Set.mem_univ t))

/-- The entries of the product of a function with integrable entries and a continuous function are
integrable. -/
theorem integrable_mul_continuous [Fintype m] {f : UnitAddCircle → Matrix l m ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) {g : UnitAddCircle → Matrix m n ℂ}
    (hg : Continuous g) (i : l) (j : n) :
    Integrable (fun t => (f t * g t) i j) haarAddCircle := by
  simpa only [← Matrix.transpose_mul, Matrix.transpose_apply] using
    integrable_continuous_mul hg.matrix_transpose (f := fun t => (f t)ᵀ) (fun i j => hf j i) j i

/-- The entries of the product of two functions with entries in `L²` are integrable. -/
theorem integrable_mul_of_memLp [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {f : UnitAddCircle → Matrix m n ℂ} (hg : ∀ i j, MemLp (fun t => g t i j) 2 haarAddCircle)
    (hf : ∀ i j, MemLp (fun t => f t i j) 2 haarAddCircle) (i : l) (j : n) :
    Integrable (fun t => (g t * f t) i j) haarAddCircle := by
  simp only [Matrix.mul_apply]
  exact integrable_finsetSum _ fun o _ => (hg i o).integrable_mul (hf o j)

/-- The entries of `fᴴ f` are integrable if those of `f` are in `L²`. -/
theorem integrable_conjTranspose_mul_self [Fintype m] {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, MemLp (fun t => f t i j) 2 haarAddCircle) (i j : n) :
    Integrable (fun t => ((f t)ᴴ * f t) i j) haarAddCircle :=
  integrable_mul_of_memLp (g := fun t => (f t)ᴴ) (fun i j => (hf j i).star) hf i j

/-- The product of a bounded function and a function with entries in `L²` has entries in `L²`. -/
theorem memLp_bounded_mul [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {f : UnitAddCircle → Matrix m n ℂ} {C : ℝ}
    (hg : ∀ i j, AEStronglyMeasurable (fun t => g t i j) haarAddCircle)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖g t i j‖ ≤ C)
    (hf : ∀ i j, MemLp (fun t => f t i j) 2 haarAddCircle) (i : l) (j : n) :
    MemLp (fun t => (g t * f t) i j) 2 haarAddCircle := by
  simp only [Matrix.mul_apply]
  refine memLp_finsetSum _ fun o _ => ?_
  refine (hf o j).of_le_mul (c := C) ((hg i o).mul (hf o j).aestronglyMeasurable) ?_
  filter_upwards [hC] with t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ht i o) (norm_nonneg _)

/-- The product of a function with entries in `L²` and a continuous function has entries in
`L²`. -/
theorem memLp_mul_continuous [Fintype m] {f : UnitAddCircle → Matrix l m ℂ}
    (hf : ∀ i j, MemLp (fun t => f t i j) 2 haarAddCircle) {g : UnitAddCircle → Matrix m n ℂ}
    (hg : Continuous g) (i : l) (j : n) : MemLp (fun t => (f t * g t) i j) 2 haarAddCircle := by
  simp only [Matrix.mul_apply]
  refine memLp_finsetSum _ fun o _ => ?_
  have h : MemLp (fun t => g t o j) ∞ haarAddCircle :=
    (hg.matrix_elem o j).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) _
  exact (hf i o).fun_mul h

/-! ### Fourier coefficients and Hardy classes -/

/-- The matrix-valued Hardy class `H¹`: integrable entries, vanishing Fourier coefficients of
negative order. -/
def IsHardyOne (f : UnitAddCircle → Matrix m n ℂ) : Prop :=
  (∀ i j, Integrable (fun t => f t i j) haarAddCircle) ∧ ∀ k : ℤ, k < 0 → matFourierCoeff f k = 0

/-- `H² ⊆ H¹`. -/
theorem IsHardyTwo.isHardyOne {f : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyTwo f) :
    IsHardyOne f :=
  ⟨fun i j => (hf.1 i j).integrable one_le_two, hf.2⟩

/-- Membership in `H²` depends on the values almost everywhere. -/
theorem IsHardyTwo.congr_ae {f g : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyTwo f)
    (h : ∀ᵐ t ∂haarAddCircle, f t = g t) : IsHardyTwo g := by
  refine ⟨fun i j => (hf.1 i j).ae_eq ?_, fun k hk => ?_⟩
  · filter_upwards [h] with t ht
    rw [ht]
  · rw [← matFourierCoeff_congr_ae h, hf.2 k hk]

/-- Membership in `H¹` depends on the values almost everywhere. -/
theorem IsHardyOne.congr_ae {f g : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyOne f)
    (h : ∀ᵐ t ∂haarAddCircle, f t = g t) : IsHardyOne g := by
  refine ⟨fun i j => (hf.1 i j).congr ?_, fun k hk => ?_⟩
  · filter_upwards [h] with t ht
    rw [ht]
  · rw [← matFourierCoeff_congr_ae h, hf.2 k hk]

/-- A matrix-valued function with integrable entries is zero almost everywhere if its Fourier
coefficients are zero. -/
theorem ae_eq_zero_of_matFourierCoeff_eq_zero [Countable m] [Countable n]
    {f : UnitAddCircle → Matrix m n ℂ} (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle)
    (h : ∀ k, matFourierCoeff f k = 0) : ∀ᵐ t ∂haarAddCircle, f t = 0 := by
  have h1 : ∀ᵐ t ∂haarAddCircle, ∀ i j, f t i j = 0 :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => ae_eq_zero_of_fourierCoeff_eq_zero (hf i j)
      fun k => congrFun (congrFun (h k) i) j
  filter_upwards [h1] with t ht
  exact Matrix.ext ht

/-- The Fourier coefficients of a constant function. -/
theorem matFourierCoeff_const (M : Matrix m n ℂ) (k : ℤ) :
    matFourierCoeff (fun _ => M) k = if k = 0 then M else 0 := by
  ext i j
  rw [matFourierCoeff, Matrix.of_apply, fourierCoeff_const]
  split_ifs <;> rfl

/-- The constant functions are in `H²`. -/
theorem isHardyTwo_const (M : Matrix m n ℂ) : IsHardyTwo fun _ => M :=
  ⟨fun _ _ => memLp_const _, fun k hk => by rw [matFourierCoeff_const, ite_eq_right hk.ne]⟩

/-- The Fourier coefficients of a difference. -/
theorem matFourierCoeff_sub {f g : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle)
    (hg : ∀ i j, Integrable (fun t => g t i j) haarAddCircle) (k : ℤ) :
    matFourierCoeff (fun t => f t - g t) k = matFourierCoeff f k - matFourierCoeff g k := by
  ext i j
  have h := integral_sub ((hf i j).fourier_smul (-k)) ((hg i j).fourier_smul (-k))
  simp only [← smul_sub] at h
  exact h

/-- The difference of two functions of `H²` is in `H²`. -/
theorem IsHardyTwo.sub {f g : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyTwo f)
    (hg : IsHardyTwo g) : IsHardyTwo fun t => f t - g t :=
  ⟨fun i j => (hf.1 i j).sub (hg.1 i j), fun k hk => by
    rw [matFourierCoeff_sub hf.isHardyOne.1 hg.isHardyOne.1, hf.2 k hk, hg.2 k hk, sub_zero]⟩

/-- The Fourier coefficients of the product of a function and a character. -/
private theorem fourierCoeff_fourier_smul (q : ℤ) (v : UnitAddCircle → ℂ) (k : ℤ) :
    fourierCoeff (fun t => fourier q t • v t) k = fourierCoeff v (k - q) := by
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  dsimp only
  rw [smul_smul, ← fourier_add, neg_sub, sub_eq_add_neg, add_comm]

/-- If `f ∈ H²` has no constant term, then `e_{-1} f ∈ H²`. -/
theorem IsHardyTwo.fourier_neg_one_smul {f : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyTwo f)
    (h0 : matFourierCoeff f 0 = 0) : IsHardyTwo fun t => fourier (-1) t • f t := by
  refine ⟨fun i j => (hf.1 i j).of_le ((fourier (-1)).continuous.aestronglyMeasurable.smul
    (hf.1 i j).aestronglyMeasurable) (ae_of_all _ fun t => ?_), fun k hk => ?_⟩
  · dsimp only
    rw [Matrix.smul_apply, norm_smul, norm_fourier_apply_eq_one, one_mul]
  · have h1 : matFourierCoeff f (k - -1) = 0 := by
      rcases (show k - -1 ≤ 0 by omega).eq_or_lt with h | h
      · rw [h, h0]
      · exact hf.2 _ h
    ext i j
    exact (fourierCoeff_fourier_smul (-1) (fun t => f t i j) k).trans
      (congrFun (congrFun h1 i) j)

/-- The Fourier coefficients of the transposed function. -/
theorem matFourierCoeff_transpose (f : UnitAddCircle → Matrix m n ℂ) (k : ℤ) :
    matFourierCoeff (fun t => (f t)ᵀ) k = (matFourierCoeff f k)ᵀ :=
  rfl

/-- `fᵀ ∈ H²` if `f ∈ H²`. -/
theorem IsHardyTwo.transpose {f : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyTwo f) :
    IsHardyTwo fun t => (f t)ᵀ :=
  ⟨fun i j => hf.1 j i, fun k hk => by rw [matFourierCoeff_transpose, hf.2 k hk,
    Matrix.transpose_zero]⟩

/-- `fᵀ ∈ H¹` if `f ∈ H¹`. -/
theorem IsHardyOne.transpose {f : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyOne f) :
    IsHardyOne fun t => (f t)ᵀ :=
  ⟨fun i j => hf.1 j i, fun k hk => by rw [matFourierCoeff_transpose, hf.2 k hk,
    Matrix.transpose_zero]⟩

/-- A function formed from rows and columns of a function of `H²` is in `H²`. -/
theorem IsHardyTwo.submatrix {f : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyTwo f) {o : Type*}
    (r : l → m) (s : o → n) : IsHardyTwo fun t => (f t).submatrix r s :=
  ⟨fun i j => hf.1 (r i) (s j), fun k hk =>
    Matrix.ext fun i j => congrFun (congrFun (hf.2 k hk) (r i)) (s j)⟩

/-- A function formed from rows and columns of a function of `H¹` is in `H¹`. -/
theorem IsHardyOne.submatrix {f : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyOne f) {o : Type*}
    (r : l → m) (s : o → n) : IsHardyOne fun t => (f t).submatrix r s :=
  ⟨fun i j => hf.1 (r i) (s j), fun k hk =>
    Matrix.ext fun i j => congrFun (congrFun (hf.2 k hk) (r i)) (s j)⟩

/-- The Fourier coefficients of a multiple by a constant matrix, on the left. -/
theorem matFourierCoeff_const_mul [Fintype m] (R : Matrix l m ℂ) {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) (k : ℤ) :
    matFourierCoeff (fun t => R * f t) k = R * matFourierCoeff f k := by
  ext i j
  have e : (fun t => (R * f t) i j) = ∑ o, fun t => R i o * f t o j := by
    ext t
    simp [Matrix.mul_apply]
  rw [matFourierCoeff, Matrix.of_apply, e,
    fourierCoeff.sum _ _ fun o _ => (hf o j).const_mul (R i o), Finset.sum_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun o _ => fourierCoeff.const_mul (fun t => f t o j) (R i o) k

/-- The Fourier coefficients of a multiple by a constant matrix, on the right. -/
theorem matFourierCoeff_mul_const [Fintype m] {f : UnitAddCircle → Matrix l m ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) (R : Matrix m n ℂ) (k : ℤ) :
    matFourierCoeff (fun t => f t * R) k = matFourierCoeff f k * R := by
  have h := matFourierCoeff_const_mul Rᵀ (f := fun t => (f t)ᵀ) (fun i j => hf j i) k
  simp only [← Matrix.transpose_mul, matFourierCoeff_transpose] at h
  exact Matrix.transpose_injective h

/-- The product of a constant matrix and a function of `H²` is in `H²`. -/
theorem IsHardyTwo.const_mul [Fintype m] {f : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyTwo f)
    (R : Matrix l m ℂ) : IsHardyTwo fun t => R * f t := by
  refine ⟨fun i j => ?_, fun k hk => ?_⟩
  · simp only [Matrix.mul_apply]
    exact memLp_finsetSum _ fun o _ => (hf.1 o j).const_mul (R i o)
  · rw [matFourierCoeff_const_mul R hf.isHardyOne.1, hf.2 k hk, Matrix.mul_zero]

/-- The product of a function of `H²` and a constant matrix is in `H²`. -/
theorem IsHardyTwo.mul_const [Fintype m] {f : UnitAddCircle → Matrix l m ℂ} (hf : IsHardyTwo f)
    (R : Matrix m n ℂ) : IsHardyTwo fun t => f t * R := by
  simpa only [← Matrix.transpose_mul, Matrix.transpose_transpose] using
    (hf.transpose.const_mul Rᵀ).transpose

/-- The constant coefficient of a product of functions of `H²` is the product of their constant
coefficients. -/
theorem IsHardyTwo.matFourierCoeff_mul_zero [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {h : UnitAddCircle → Matrix m n ℂ} (hg : IsHardyTwo g) (hh : IsHardyTwo h) :
    matFourierCoeff (fun t => g t * h t) 0 = matFourierCoeff g 0 * matFourierCoeff h 0 := by
  simpa using matFourierCoeff_mul hg hh 0

/-! ### Convergence in `L²` -/

/-- Convergence in `L²` of matrix-valued functions, entry by entry. -/
def TendstoLTwo (F : ℕ → UnitAddCircle → Matrix m n ℂ) (f : UnitAddCircle → Matrix m n ℂ) : Prop :=
  ∀ i j, Tendsto (fun N => eLpNorm (fun t => F N t i j - f t i j) 2 haarAddCircle) atTop (𝓝 0)

/-- Convergence in `L²` of a sequence of functions implies that of the Fourier coefficients of the
products with a fixed function of `L²`. -/
private theorem tendsto_fourierCoeff_mul {u : ℕ → UnitAddCircle → ℂ} {v w : UnitAddCircle → ℂ}
    (hv : MemLp v 2 haarAddCircle) (hu : ∀ N, MemLp (u N) 2 haarAddCircle)
    (hw : MemLp w 2 haarAddCircle)
    (h : Tendsto (fun N => eLpNorm (fun t => u N t - w t) 2 haarAddCircle) atTop (𝓝 0)) (k : ℤ) :
    Tendsto (fun N => fourierCoeff (fun t => v t * u N t) k) atTop
      (𝓝 (fourierCoeff (fun t => v t * w t) k)) := by
  have hint {x : UnitAddCircle → ℂ} (hx : MemLp x 2 haarAddCircle) :
      Integrable (fun t => fourier (-k) t • (v t * x t)) haarAddCircle :=
    Integrable.fourier_smul (f := fun t => v t * x t) (hv.integrable_mul hx) _
  refine tendsto_integral_of_L1' _ (Eventually.of_forall fun N => hint (hu N)) ?_
  have h0 : Tendsto (fun N => eLpNorm v 2 haarAddCircle *
      eLpNorm (fun t => u N t - w t) 2 haarAddCircle) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hv.eLpNorm_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
    fun N => ?_
  have e : eLpNorm ((fun t => fourier (-k) t • (v t * u N t)) -
      fun t => fourier (-k) t • (v t * w t)) 1 haarAddCircle =
      eLpNorm (v • fun t => u N t - w t) 1 haarAddCircle := by
    refine eLpNorm_congr_norm_ae ((hint (hu N)).sub (hint hw)).aestronglyMeasurable
      (hv.aestronglyMeasurable.smul ((hu N).sub hw).aestronglyMeasurable) (ae_of_all _ fun t => ?_)
    rw [Pi.sub_apply, ← smul_sub, ← mul_sub, norm_smul, norm_fourier_apply_eq_one, one_mul]
    rfl
  exact e.trans_le (eLpNorm_smul_le_mul_eLpNorm hv.aestronglyMeasurable
    ((hu N).sub hw).aestronglyMeasurable)

/-- A sequence of matrix-valued functions whose entries converge in `L^p` has a subsequence that
converges almost everywhere. -/
private theorem exists_seq_tendsto_ae_of_eLpNorm [Finite m] [Finite n] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {F : ℕ → UnitAddCircle → Matrix m n ℂ} {f : UnitAddCircle → Matrix m n ℂ}
    (hF : ∀ N i j, AEStronglyMeasurable (fun t => F N t i j) haarAddCircle)
    (hf : ∀ i j, AEStronglyMeasurable (fun t => f t i j) haarAddCircle)
    (h : ∀ i j, Tendsto (fun N => eLpNorm (fun t => F N t i j - f t i j) p haarAddCircle) atTop
      (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ t ∂haarAddCircle, Tendsto (fun N => F (ns N) t) atTop (𝓝 (f t)) := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  let d (N : ℕ) (q : m × n) (t : UnitAddCircle) : ℝ := ‖F N t q.1 q.2 - f t q.1 q.2‖
  have hsum : Tendsto (fun N => eLpNorm (∑ q, d N q - 0) p haarAddCircle) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => ∑ q : m × n, eLpNorm (fun t => F N t q.1 q.2 - f t q.1 q.2) p
        haarAddCircle) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun (q : m × n) _ => h q.1 q.2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      fun N => ?_
    rw [sub_zero]
    refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun q _ => ?_)
    exact (eLpNorm_norm _ ((hF N q.1 q.2).sub (hf q.1 q.2))).le
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (one_pos.trans_le hp).ne' hsum).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim] with t ht
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => norm_nonneg _) fun N => ?_
  rw [Finset.sum_apply]
  exact Finset.single_le_sum (f := fun q => d (ns N) q t) (fun q _ => norm_nonneg _)
    (Finset.mem_univ (i, j))

namespace TendstoLTwo

variable {F : ℕ → UnitAddCircle → Matrix m n ℂ} {f : UnitAddCircle → Matrix m n ℂ}

/-- The limit in `L²` of functions with entries in `L²` has entries in `L²`. -/
theorem memLp (h : TendstoLTwo F f) (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle)
    (i : m) (j : n) : MemLp (fun t => f t i j) 2 haarAddCircle := by
  obtain ⟨N, hN⟩ := ((h i j).eventually_lt_const ENNReal.zero_lt_top).exists
  have h1 : MemLp (fun t => F N t i j - f t i j) 2 haarAddCircle := hN
  exact ((hF N i j).sub h1).ae_eq (ae_of_all _ fun t => sub_sub_cancel _ _)

/-- Convergence in `L²` depends on the values almost everywhere. -/
theorem congr_ae {G : ℕ → UnitAddCircle → Matrix m n ℂ} {g : UnitAddCircle → Matrix m n ℂ}
    (h : TendstoLTwo F f) (hF : ∀ N, ∀ᵐ t ∂haarAddCircle, F N t = G N t)
    (hf : ∀ᵐ t ∂haarAddCircle, f t = g t) : TendstoLTwo G g := by
  intro i j
  refine (h i j).congr fun N => eLpNorm_congr_ae ?_
  filter_upwards [hF N, hf] with t h1 h2
  rw [h1, h2]

/-- Convergence in `L²` of the transposed functions. -/
theorem transpose (h : TendstoLTwo F f) : TendstoLTwo (fun N t => (F N t)ᵀ) fun t => (f t)ᵀ :=
  fun i j => h j i

/-- Convergence in `L²` implies the convergence of the Fourier coefficients. -/
theorem tendsto_matFourierCoeff (h : TendstoLTwo F f)
    (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle) (k : ℤ) :
    Tendsto (fun N => matFourierCoeff (F N) k) atTop (𝓝 (matFourierCoeff f k)) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  simpa [matFourierCoeff] using tendsto_fourierCoeff_mul (v := fun _ => 1) (memLp_const 1)
    (fun N => hF N i j) (h.memLp hF i j) (h i j) k

/-- `H²` is closed in `L²`. -/
theorem isHardyTwo (h : TendstoLTwo F f) (hF : ∀ N, IsHardyTwo (F N)) : IsHardyTwo f := by
  refine ⟨h.memLp fun N => (hF N).1, fun k hk => ?_⟩
  have h1 := h.tendsto_matFourierCoeff (fun N => (hF N).1) k
  simp only [fun N => (hF N).2 k hk] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- A sequence that converges in `L²` has a subsequence that converges almost everywhere. -/
theorem exists_seq_tendsto_ae [Finite m] [Finite n] (h : TendstoLTwo F f)
    (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ t ∂haarAddCircle, Tendsto (fun N => F (ns N) t) atTop (𝓝 (f t)) :=
  exists_seq_tendsto_ae_of_eLpNorm one_le_two (fun N i j => (hF N i j).aestronglyMeasurable)
    (fun i j => (h.memLp hF i j).aestronglyMeasurable) h

/-- Multiplication on the left by a bounded function is continuous in `L²`. -/
theorem bounded_mul [Fintype m] {G : UnitAddCircle → Matrix l m ℂ} {C : ℝ}
    (hG : ∀ i j, AEStronglyMeasurable (fun t => G t i j) haarAddCircle)
    (hGC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖G t i j‖ ≤ C) (h : TendstoLTwo F f)
    (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle) :
    TendstoLTwo (fun N t => G t * F N t) fun t => G t * f t := by
  intro i j
  have h0 : Tendsto (fun N => ∑ o, ENNReal.ofReal C *
      eLpNorm (fun t => F N t o j - f t o j) 2 haarAddCircle) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun o _ =>
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) (h o j) (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
    fun N => ?_
  have e : (fun t => (G t * F N t) i j - (G t * f t) i j) =
      ∑ o, fun t => G t i o * (F N t o j - f t o j) := by
    ext t
    simp [Matrix.mul_apply, mul_sub]
  dsimp only
  rw [e]
  refine (eLpNorm_sum_le one_le_two).trans (Finset.sum_le_sum fun o _ => ?_)
  have hmeas : AEStronglyMeasurable (fun t => G t i o * (F N t o j - f t o j)) haarAddCircle :=
    (hG i o).mul ((hF N o j).sub (h.memLp hF o j)).aestronglyMeasurable
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas (hGC.mono fun t ht => ?_) 2
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ht i o) (norm_nonneg _)

/-- Multiplication on the right by a bounded function is continuous in `L²`. -/
theorem mul_bounded [Fintype n] {G : UnitAddCircle → Matrix n l ℂ} {C : ℝ}
    (hG : ∀ i j, AEStronglyMeasurable (fun t => G t i j) haarAddCircle)
    (hGC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖G t i j‖ ≤ C) (h : TendstoLTwo F f)
    (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle) :
    TendstoLTwo (fun N t => F N t * G t) fun t => f t * G t := by
  have key := (h.transpose.bounded_mul (G := fun t => (G t)ᵀ) (fun i j => hG j i)
    (hGC.mono fun t ht i j => ht j i) fun N i j => hF N j i).transpose
  simpa only [← Matrix.transpose_mul, Matrix.transpose_transpose] using key

/-- Multiplication on the left by a continuous function is continuous in `L²`. -/
theorem continuous_mul [Fintype m] [Finite l] {G : UnitAddCircle → Matrix l m ℂ}
    (hG : Continuous G) (h : TendstoLTwo F f)
    (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle) :
    TendstoLTwo (fun N t => G t * F N t) fun t => G t * f t := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hG
  exact h.bounded_mul (fun i j => (hG.matrix_elem i j).aestronglyMeasurable) (ae_of_all _ hC) hF

/-- Multiplication on the right by a continuous function is continuous in `L²`. -/
theorem mul_continuous [Fintype n] [Finite l] {G : UnitAddCircle → Matrix n l ℂ}
    (hG : Continuous G) (h : TendstoLTwo F f)
    (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle) :
    TendstoLTwo (fun N t => F N t * G t) fun t => f t * G t := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hG
  exact h.mul_bounded (fun i j => (hG.matrix_elem i j).aestronglyMeasurable) (ae_of_all _ hC) hF

/-- Multiplication on the left by a function of `L²` is continuous from `L²` to `L¹`: the Fourier
coefficients of the products converge. -/
theorem tendsto_matFourierCoeff_mul_left [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    (hg : ∀ i j, MemLp (fun t => g t i j) 2 haarAddCircle) (h : TendstoLTwo F f)
    (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle) (k : ℤ) :
    Tendsto (fun N => matFourierCoeff (fun t => g t * F N t) k) atTop
      (𝓝 (matFourierCoeff (fun t => g t * f t) k)) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have e {u : UnitAddCircle → Matrix m n ℂ} (hu : ∀ i j, MemLp (fun t => u t i j) 2 haarAddCircle) :
      matFourierCoeff (fun t => g t * u t) k i j =
        ∑ o, fourierCoeff (fun t => g t i o * u t o j) k := by
    have e1 : (fun t => (g t * u t) i j) = ∑ o, fun t => g t i o * u t o j := by
      ext t
      simp [Matrix.mul_apply]
    have hint (o : m) : Integrable (fun t => g t i o * u t o j) haarAddCircle :=
      (hg i o).integrable_mul (hu o j)
    rw [matFourierCoeff, Matrix.of_apply, e1, fourierCoeff.sum _ _ fun o _ => hint o,
      Finset.sum_apply]
  simp only [e (h.memLp hF), fun N => e (hF N)]
  exact tendsto_finsetSum _ fun o _ =>
    tendsto_fourierCoeff_mul (hg i o) (fun N => hF N o j) (h.memLp hF o j) (h o j) k

end TendstoLTwo

/-- Iterated limits in `L²`: if `φ K N → f K` for `N → ∞` and `f K → g` for `K → ∞`, then
`φ K (ν K) → g` for some `ν`. -/
theorem exists_tendstoLTwo_diagonal [Finite m] [Finite n]
    {φ : ℕ → ℕ → UnitAddCircle → Matrix m n ℂ} {f : ℕ → UnitAddCircle → Matrix m n ℂ}
    {g : UnitAddCircle → Matrix m n ℂ} (h1 : ∀ K, TendstoLTwo (φ K) (f K))
    (h2 : TendstoLTwo f g) : ∃ ν : ℕ → ℕ, TendstoLTwo (fun K => φ K (ν K)) g := by
  have h3 (K : ℕ) : ∃ N, ∀ i j,
      eLpNorm (fun t => φ K N t i j - f K t i j) 2 haarAddCircle ≤ (K : ℝ≥0∞)⁻¹ := by
    refine Eventually.exists (f := atTop) (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
    exact (h1 K i j).eventually (Iic_mem_nhds (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top K)))
  choose ν hν using h3
  refine ⟨ν, fun i j => ?_⟩
  have h4 : Tendsto (fun K : ℕ => (K : ℝ≥0∞)⁻¹ +
      eLpNorm (fun t => f K t i j - g t i j) 2 haarAddCircle) atTop (𝓝 0) := by
    simpa only [add_zero] using ENNReal.tendsto_inv_nat_nhds_zero.add (h2 i j)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4 (fun _ => zero_le)
    fun K => ?_
  have h5 : (fun t => φ K (ν K) t i j - g t i j) =
      (fun t => φ K (ν K) t i j - f K t i j) + fun t => f K t i j - g t i j := by
    ext t
    simp only [Pi.add_apply, sub_add_sub_cancel]
  rw [h5]
  exact (eLpNorm_add_le one_le_two).trans (add_le_add (hν K i j) le_rfl)

/-- The analytic polynomials are dense in `H²`. -/
theorem IsHardyTwo.exists_tendsto_circPoly {f : UnitAddCircle → Matrix m n ℂ} (hf : IsHardyTwo f) :
    ∃ c : ℕ → ℤ →₀ Matrix m n ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
      TendstoLTwo (fun N => circPoly (c N)) f := by
  refine ⟨fun N => ∑ k ∈ Finset.Icc (-N : ℤ) N, Finsupp.single k (matFourierCoeff f k),
    fun N k hk => ?_, fun i j => (tendsto_eLpNorm_partialSum (hf.1 i j)).congr fun N => ?_⟩
  · by_contra hlt
    refine Finsupp.mem_support_iff.1 hk ?_
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : k = q
    · rw [← hq, Finsupp.single_eq_same, hf.2 k (by omega)]
    · exact Finsupp.single_eq_of_ne hq
  · have h1 (t : UnitAddCircle) : circPoly (∑ k ∈ Finset.Icc (-N : ℤ) N,
        Finsupp.single k (matFourierCoeff f k)) t i j =
        ∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t * fourierCoeff (fun t => f t i j) k := by
      rw [circPoly_sum, Matrix.sum_apply]
      simp only [circPoly_single]
      rfl
    simp only [h1]

/-! ### Fejér means -/

/-- The Fejér kernel `F_K = K⁻¹ |Σ_{0 ≤ j < K} e_j|²`. -/
noncomputable def fejerKernel (K : ℕ) (t : UnitAddCircle) : ℝ :=
  ‖∑ j ∈ Finset.range K, fourier (j : ℤ) t‖ ^ 2 / K

/-- The coefficients of the `K`-th Fejér mean of `f`: `(1 − |k| / K) f̂ (k)` if `|k| < K`, and `0`
otherwise. -/
noncomputable def fejerCoeff (f : UnitAddCircle → Matrix m n ℂ) (K : ℕ) : ℤ →₀ Matrix m n ℂ :=
  Finsupp.onFinset (Finset.Ioo (-(K : ℤ)) K)
    (fun k => if |k| < (K : ℤ) then ((1 - |(k : ℝ)| / K : ℝ) : ℂ) • matFourierCoeff f k else 0)
    (fun k hk => by
      rw [Finset.mem_Ioo, ← abs_lt]
      by_contra h
      exact hk (ite_eq_right h))

/-- The weights `1 − |k| / K`, `|k| < K`, of the Fejér means. -/
private noncomputable def fejerWeight (K : ℕ) (k : ℤ) : ℝ := 1 - |(k : ℝ)| / K

/-- The coefficients of the Fejér means of order `|k| < K`. -/
private theorem fejerCoeff_apply (f : UnitAddCircle → Matrix m n ℂ) {K : ℕ} {k : ℤ}
    (hk : k ∈ Finset.Ioo (-(K : ℤ)) K) :
    fejerCoeff f K k = (fejerWeight K k : ℂ) • matFourierCoeff f k := by
  rw [Finset.mem_Ioo, ← abs_lt] at hk
  simp [fejerCoeff, fejerWeight, hk]

/-- There are `max (K − |k|, 0)` pairs `(i, j)` with `0 ≤ i, j < K` and `i − j = k`. -/
private theorem card_filter_sub_eq (K : ℕ) (k : ℤ) :
    ((Finset.range K ×ˢ Finset.range K).filter fun q => (q.1 : ℤ) - q.2 = k).card =
      (K - |k|).toNat := by
  rw [abs_eq_max_neg, ← Finset.card_range (K - max k (-k)).toNat]
  refine Finset.card_nbij' (fun q => min q.1 q.2)
    (fun a => (a + (max k 0).toNat, a + (max (-k) 0).toNat)) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq,
      Finset.coe_range, Set.mem_Iio] at hq ⊢
    omega
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq,
      Finset.coe_range, Set.mem_Iio] at ha ⊢
    omega
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at hq
    ext <;> dsimp only <;> omega
  · intro a _
    dsimp only
    omega

/-- The Fejér kernel as a trigonometric polynomial: `F_K = Σ_{|k| < K} (1 − |k| / K) e_k`. -/
private theorem fejerKernel_eq_sum (K : ℕ) (t : UnitAddCircle) :
    (fejerKernel K t : ℂ) =
      ∑ k ∈ Finset.Ioo (-(K : ℤ)) K, (fejerWeight K k : ℂ) * fourier k t := by
  have h1 : ((‖∑ j ∈ Finset.range K, fourier (j : ℤ) t‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ Finset.range K ×ˢ Finset.range K, fourier ((q.1 : ℤ) - q.2) t := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum,
      ← Finset.sum_product']
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← fourier_neg, ← fourier_add, sub_eq_add_neg]
  have h2 : ∀ q ∈ Finset.range K ×ˢ Finset.range K,
      (q.1 : ℤ) - q.2 ∈ Finset.Ioo (-(K : ℤ)) K := fun q hq => by
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Ioo] at hq ⊢
    omega
  rw [fejerKernel, Complex.ofReal_div, h1, ← Finset.sum_fiberwise_of_maps_to' h2
    fun k => fourier k t, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Ioo, ← abs_lt] at hk
  have hK : (0 : ℝ) < K := by
    have := (abs_nonneg k).trans_lt hk
    exact_mod_cast this
  have hcard : (((K - |k|).toNat : ℕ) : ℝ) = K - |(k : ℝ)| := by
    have h3 : (((K - |k|).toNat : ℕ) : ℤ) = K - |k| := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (Int.cast (R := ℝ)) h3
  have hw : fejerWeight K k = (K - |(k : ℝ)|) / K := by rw [fejerWeight, sub_div, div_self hK.ne']
  rw [Finset.sum_const, card_filter_sub_eq, nsmul_eq_mul, hw, ← hcard]
  push_cast
  ring

/-- The Fejér kernel is continuous. -/
private theorem continuous_fejerKernel (K : ℕ) : Continuous (fejerKernel K) := by
  have : Continuous fun t : UnitAddCircle => ∑ j ∈ Finset.range K, fourier (j : ℤ) t :=
    continuous_finsetSum _ fun j _ => (fourier (j : ℤ)).continuous
  exact (this.norm.pow 2).div_const _

/-- The Fejér kernel is bounded. -/
private theorem exists_norm_fejerKernel_le (K : ℕ) : ∃ C : ℝ, ∀ t, ‖fejerKernel K t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_fejerKernel K)).isBounded.exists_norm_le
  exact ⟨C, fun t => hC _ ⟨t, rfl⟩⟩

/-- The characters are multiplicative. -/
private theorem fourier_sub_apply (k : ℤ) (t s : UnitAddCircle) :
    fourier k (t - s) = fourier k t * fourier (-k) s := by
  rw [fourier_apply, fourier_apply, fourier_apply, sub_eq_add_neg, smul_add, smul_neg, neg_smul,
    toCircle_add, Circle.coe_mul]

/-- The Fejér means of an integrable scalar function. -/
private noncomputable def fejerMean (u : UnitAddCircle → ℂ) (K : ℕ) (t : UnitAddCircle) : ℂ :=
  ∫ s, (fejerKernel K (t - s) : ℂ) * u s ∂haarAddCircle

/-- The Fejér means are trigonometric polynomials. -/
private theorem fejerMean_eq_sum {u : UnitAddCircle → ℂ} (hu : Integrable u haarAddCircle) (K : ℕ)
    (t : UnitAddCircle) : fejerMean u K t =
      ∑ k ∈ Finset.Ioo (-(K : ℤ)) K, (fejerWeight K k : ℂ) * fourierCoeff u k * fourier k t := by
  have e (s : UnitAddCircle) : (fejerKernel K (t - s) : ℂ) * u s =
      ∑ k ∈ Finset.Ioo (-(K : ℤ)) K,
        (fejerWeight K k : ℂ) * fourier k t * (fourier (-k) s • u s) := by
    rw [fejerKernel_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fourier_sub_apply, smul_eq_mul]
    ring
  simp only [fejerMean, e]
  rw [integral_finsetSum _ fun k _ => (hu.fourier_smul (-k)).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, fourierCoeff]
  ring

/-- The Fejér means of an integrable function are its averages for the Fejér kernel. -/
theorem circPoly_fejerCoeff_apply {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) (K : ℕ) (t : UnitAddCircle) (i : m)
    (j : n) : circPoly (fejerCoeff f K) t i j =
      ∫ s, (fejerKernel K (t - s) : ℂ) * f s i j ∂haarAddCircle := by
  have h1 : circPoly (fejerCoeff f K) t =
      ∑ k ∈ Finset.Ioo (-(K : ℤ)) K, fourier k t • fejerCoeff f K k :=
    Finsupp.onFinset_sum _ fun k => smul_zero _
  refine Eq.trans ?_ (fejerMean_eq_sum (hf i j) K t).symm
  rw [h1, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [fejerCoeff_apply f hk, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_comm]
  rfl

/-- The Fejér kernel is nonnegative. -/
theorem fejerKernel_nonneg (K : ℕ) (t : UnitAddCircle) : 0 ≤ fejerKernel K t :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg K)

/-- The weight of order `0` is `1`. -/
private theorem fejerWeight_zero (K : ℕ) : fejerWeight K 0 = 1 := by
  simp [fejerWeight]

/-- `0` is one of the orders of the Fejér means. -/
private theorem zero_mem_Ioo {K : ℕ} (hK : 0 < K) : (0 : ℤ) ∈ Finset.Ioo (-(K : ℤ)) K := by
  rw [Finset.mem_Ioo]
  omega

/-- The Fejér kernel has integral `1`. -/
theorem integral_fejerKernel {K : ℕ} (hK : 0 < K) : ∫ t, fejerKernel K t ∂haarAddCircle = 1 := by
  have h1 := fejerMean_eq_sum (integrable_const (1 : ℂ)) K 0
  simp only [fejerMean, zero_sub, mul_one, fourierCoeff_const, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', zero_mem_Ioo hK, ite_true, fejerWeight_zero] at h1
  rw [integral_neg_eq_self (fun s => (fejerKernel K s : ℂ)) haarAddCircle,
    integral_complex_ofReal, fourier_zero, mul_one] at h1
  exact Complex.ofReal_injective h1

/-- The translates of the Fejér kernel have integral `1`. -/
private theorem integral_fejerKernel_sub {K : ℕ} (hK : 0 < K) (t : UnitAddCircle) :
    ∫ s, fejerKernel K (t - s) ∂haarAddCircle = 1 := by
  rw [integral_sub_left_eq_self (fejerKernel K) haarAddCircle, integral_fejerKernel hK]

/-- The constant coefficient of the Fejér means of `f` is that of `f`. -/
theorem fejerCoeff_zero (f : UnitAddCircle → Matrix m n ℂ) {K : ℕ} (hK : 0 < K) :
    fejerCoeff f K 0 = matFourierCoeff f 0 := by
  rw [fejerCoeff_apply f (zero_mem_Ioo hK), fejerWeight_zero, Complex.ofReal_one, one_smul]

/-- The Fejér means of an analytic function are analytic polynomials. -/
theorem nonneg_of_mem_support_fejerCoeff {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ k : ℤ, k < 0 → matFourierCoeff f k = 0) (K : ℕ) :
    ∀ k ∈ (fejerCoeff f K).support, 0 ≤ k := by
  intro k hk
  by_contra hneg
  refine Finsupp.mem_support_iff.1 hk ?_
  simp [fejerCoeff, hf k (not_le.1 hneg)]

/-- The Fejér means of a bounded function are bounded by the same constant. -/
theorem norm_circPoly_fejerCoeff_le {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) {C : ℝ} {i : m} {j : n}
    (hC : ∀ᵐ t ∂haarAddCircle, ‖f t i j‖ ≤ C) {K : ℕ} (hK : 0 < K) (t : UnitAddCircle) :
    ‖circPoly (fejerCoeff f K) t i j‖ ≤ C := by
  have hint : Integrable (fun s => fejerKernel K (t - s) * C) haarAddCircle :=
    integrable_haar_of_continuous
      (((continuous_fejerKernel K).comp (continuous_sub_left t)).mul continuous_const)
  rw [circPoly_fejerCoeff_apply hf]
  refine (norm_integral_le_of_norm_le hint ?_).trans_eq ?_
  · filter_upwards [hC] with s hs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left hs (fejerKernel_nonneg _ _)
  · rw [integral_mul_const, integral_fejerKernel_sub hK, one_mul]

/-- The Fejér means of a Hermitian function are Hermitian. -/
theorem isHermitian_circPoly_fejerCoeff {f : UnitAddCircle → Matrix n n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle)
    (hH : ∀ᵐ t ∂haarAddCircle, (f t).IsHermitian) (K : ℕ) (t : UnitAddCircle) :
    (circPoly (fejerCoeff f K) t).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, circPoly_fejerCoeff_apply hf, circPoly_fejerCoeff_apply hf,
    Complex.star_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [hH] with s hs
  rw [map_mul, Complex.conj_ofReal, ← hs.apply i j, Complex.star_def]

/-- The Fejér means are continuous. -/
private theorem continuous_fejerMean {u : UnitAddCircle → ℂ} (hu : Integrable u haarAddCircle)
    (K : ℕ) : Continuous (fejerMean u K) := by
  rw [funext (fejerMean_eq_sum hu K)]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (fourier k).continuous

/-- The Fejér means are contractions of `L¹`. -/
private theorem integral_norm_fejerMean_le {u : UnitAddCircle → ℂ} (hu : Integrable u haarAddCircle)
    {K : ℕ} (hK : 0 < K) :
    ∫ t, ‖fejerMean u K t‖ ∂haarAddCircle ≤ ∫ t, ‖u t‖ ∂haarAddCircle := by
  have hint : Integrable (fun q : UnitAddCircle × UnitAddCircle =>
      fejerKernel K (q.1 - q.2) * ‖u q.2‖) (haarAddCircle.prod haarAddCircle) := by
    obtain ⟨C, hC⟩ := exists_norm_fejerKernel_le K
    exact (hu.norm.comp_snd haarAddCircle).bdd_mul (c := C)
      ((continuous_fejerKernel K).comp continuous_sub).aestronglyMeasurable
      (ae_of_all _ fun q => hC _)
  calc ∫ t, ‖fejerMean u K t‖ ∂haarAddCircle
      ≤ ∫ t, ∫ s, fejerKernel K (t - s) * ‖u s‖ ∂haarAddCircle ∂haarAddCircle := by
        refine integral_mono (integrable_haar_of_continuous (continuous_fejerMean hu K).norm)
          hint.integral_prod_left fun t => ?_
        refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ ?_))
        intro s
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg _ _)]
    _ = ∫ s, ∫ t, fejerKernel K (t - s) * ‖u s‖ ∂haarAddCircle ∂haarAddCircle :=
        integral_integral_swap hint
    _ = ∫ s, ‖u s‖ ∂haarAddCircle := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        dsimp only
        rw [integral_mul_const, integral_sub_right_eq_self, integral_fejerKernel hK, one_mul]

/-- The trigonometric polynomials are dense in `L¹`. -/
private theorem exists_integral_norm_sub_circPoly_le {u : UnitAddCircle → ℂ}
    (hu : Integrable u haarAddCircle) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, ∫ t, ‖u t - circPoly c t‖ ∂haarAddCircle ≤ ε := by
  obtain ⟨g, hg, hgint⟩ := hu.exists_boundedContinuous_integral_sub_le (half_pos hε)
  have hmem : g.toContinuousMap ∈
      (Submodule.span ℂ (Set.range (fourier (T := 1)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.1 hmem (ε / 2) (half_pos hε)
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hp
  refine ⟨c, ?_⟩
  have hpoly (t : UnitAddCircle) : ‖g t - circPoly c t‖ ≤ ε / 2 := by
    rw [dist_eq_norm] at hdist
    refine le_trans (le_of_eq ?_) ((ContinuousMap.norm_coe_le_norm _ t).trans hdist.le)
    rw [ContinuousMap.sub_apply, circPoly, Finsupp.sum, Finsupp.sum, ContinuousMap.sum_apply]
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hint1 : Integrable (fun t => ‖u t - g t‖) haarAddCircle := (hu.sub hgint).norm
  have hint2 : Integrable (fun t => ‖u t - g t‖ + ε / 2) haarAddCircle :=
    hint1.add (integrable_const _)
  have hint3 : Integrable (fun t => ‖u t - circPoly c t‖) haarAddCircle :=
    (hu.sub (integrable_haar_of_continuous (continuous_circPoly c))).norm
  calc ∫ t, ‖u t - circPoly c t‖ ∂haarAddCircle
      ≤ ∫ t, (‖u t - g t‖ + ε / 2) ∂haarAddCircle :=
        integral_mono hint3 hint2 fun t =>
          (norm_sub_le_norm_sub_add_norm_sub _ (g t) _).trans (by gcongr; exact hpoly t)
    _ = ∫ t, ‖u t - g t‖ ∂haarAddCircle + ε / 2 := by
        rw [integral_add hint1 (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ ε := by linarith

/-- The Fourier coefficients of a scalar trigonometric polynomial are its coefficients. -/
private theorem fourierCoeff_circPoly (c : ℤ →₀ ℂ) (k : ℤ) : fourierCoeff (circPoly c) k = c k :=
  integral_fourier_smul_circPoly c k

/-- The weights of the Fejér means converge to `1`. -/
private theorem tendsto_fejerWeight (k : ℤ) :
    Tendsto (fun K => fejerWeight K k) atTop (𝓝 1) := by
  simpa [fejerWeight] using (tendsto_const_div_atTop_nhds_zero_nat |(k : ℝ)|).const_sub 1

/-- The Fejér means of a trigonometric polynomial converge to it in `L¹`. -/
private theorem tendsto_fejerMean_circPoly (c : ℤ →₀ ℂ) :
    Tendsto (fun K => ∫ t, ‖fejerMean (circPoly c) K t - circPoly c t‖ ∂haarAddCircle) atTop
      (𝓝 0) := by
  have hc : Integrable (circPoly c) haarAddCircle :=
    integrable_haar_of_continuous (continuous_circPoly c)
  have hlim : Tendsto (fun K => ∑ k ∈ c.support, |fejerWeight K k - 1| * ‖c k‖) atTop (𝓝 0) := by
    have h1 (k : ℤ) : Tendsto (fun K => |fejerWeight K k - 1| * ‖c k‖) atTop (𝓝 0) := by
      simpa using (((tendsto_fejerWeight k).sub_const 1).abs).mul_const ‖c k‖
    simpa using tendsto_finsetSum c.support fun k _ => h1 k
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun K => integral_nonneg fun t => norm_nonneg _) ?_
  have hev : ∀ᶠ K : ℕ in atTop, ∀ k ∈ c.support, k ∈ Finset.Ioo (-(K : ℤ)) K := by
    refine (Filter.eventually_all_finset _).2 fun k _ => ?_
    filter_upwards [eventually_gt_atTop k.natAbs] with K hK
    rw [Finset.mem_Ioo]
    omega
  filter_upwards [hev] with K hK
  have e (t : UnitAddCircle) : fejerMean (circPoly c) K t - circPoly c t =
      ∑ k ∈ c.support, ((fejerWeight K k : ℂ) - 1) * c k * fourier k t := by
    rw [fejerMean_eq_sum hc, ← Finset.sum_subset hK fun k _ hk => by
      rw [fourierCoeff_circPoly, Finsupp.notMem_support_iff.1 hk, mul_zero, zero_mul], circPoly,
      Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fourierCoeff_circPoly, smul_eq_mul]
    ring
  have hb (t : UnitAddCircle) : ‖fejerMean (circPoly c) K t - circPoly c t‖ ≤
      ∑ k ∈ c.support, |fejerWeight K k - 1| * ‖c k‖ := by
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_fourier_apply_eq_one, mul_one, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine (integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (integrable_const _)
    (ae_of_all _ hb)).trans_eq ?_
  rw [integral_const, probReal_univ, one_smul]

/-- The integrands of the Fejér means are integrable. -/
private theorem integrable_fejerKernel_mul {u : UnitAddCircle → ℂ} (hu : Integrable u haarAddCircle)
    (K : ℕ) (t : UnitAddCircle) :
    Integrable (fun s => (fejerKernel K (t - s) : ℂ) * u s) haarAddCircle := by
  obtain ⟨C, hC⟩ := exists_norm_fejerKernel_le K
  refine hu.bdd_mul (c := C) (Complex.continuous_ofReal.comp ((continuous_fejerKernel K).comp
    (continuous_sub_left t))).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  rw [Complex.norm_real]
  exact hC _

/-- `‖σ_K u − u‖₁ ≤ ‖σ_K p − p‖₁ + 2 ‖u − p‖₁` for the Fejér means `σ_K`, `K ≥ 1`. -/
private theorem integral_norm_fejerMean_sub_le {u p : UnitAddCircle → ℂ}
    (hu : Integrable u haarAddCircle) (hp : Integrable p haarAddCircle) {K : ℕ} (hK : 0 < K) :
    ∫ t, ‖fejerMean u K t - u t‖ ∂haarAddCircle ≤
      ∫ t, ‖fejerMean p K t - p t‖ ∂haarAddCircle + 2 * ∫ t, ‖u t - p t‖ ∂haarAddCircle := by
  have hd : Integrable (fun t => u t - p t) haarAddCircle := hu.sub hp
  have hint {v : UnitAddCircle → ℂ} (hv : Integrable v haarAddCircle) :
      Integrable (fejerMean v K) haarAddCircle :=
    integrable_haar_of_continuous (continuous_fejerMean hv K)
  have i1 : Integrable (fun t => ‖fejerMean p K t - p t‖) haarAddCircle := ((hint hp).sub hp).norm
  have i2 : Integrable (fun t => ‖fejerMean (fun t => u t - p t) K t‖) haarAddCircle :=
    (hint hd).norm
  have i3 : Integrable (fun t => ‖u t - p t‖) haarAddCircle := hd.norm
  have i23 : Integrable (fun t => ‖fejerMean (fun t => u t - p t) K t‖ + ‖u t - p t‖)
      haarAddCircle := i2.add i3
  have hle (t : UnitAddCircle) : ‖fejerMean u K t - u t‖ ≤ ‖fejerMean p K t - p t‖ +
      (‖fejerMean (fun t => u t - p t) K t‖ + ‖u t - p t‖) := by
    have e1 : fejerMean (fun t => u t - p t) K t = fejerMean u K t - fejerMean p K t := by
      simp only [fejerMean, mul_sub]
      exact integral_sub (integrable_fejerKernel_mul hu K t) (integrable_fejerKernel_mul hp K t)
    have e2 : fejerMean u K t - u t = (fejerMean p K t - p t) +
        (fejerMean (fun t => u t - p t) K t - (u t - p t)) := by
      rw [e1]
      ring
    rw [e2]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  calc ∫ t, ‖fejerMean u K t - u t‖ ∂haarAddCircle
      ≤ ∫ t, (‖fejerMean p K t - p t‖ +
          (‖fejerMean (fun t => u t - p t) K t‖ + ‖u t - p t‖)) ∂haarAddCircle :=
        integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (i1.add i23) (ae_of_all _ hle)
    _ ≤ _ := by
        rw [integral_add i1 i23, integral_add i2 i3]
        linarith [integral_norm_fejerMean_le hd hK]

/-- The Fejér means of an integrable scalar function converge to it in `L¹`. -/
private theorem tendsto_fejerMean {u : UnitAddCircle → ℂ} (hu : Integrable u haarAddCircle) :
    Tendsto (fun K => ∫ t, ‖fejerMean u K t - u t‖ ∂haarAddCircle) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop'.2 fun ε hε => ?_
  obtain ⟨c, hc⟩ := exists_integral_norm_sub_circPoly_le hu (half_pos (half_pos hε))
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop'.1 (tendsto_fejerMean_circPoly c) (ε / 2) (half_pos hε)
  refine ⟨K₀, fun K hK => ?_⟩
  have h1 := integral_norm_fejerMean_sub_le hu
    (integrable_haar_of_continuous (continuous_circPoly c)) (pos_of_gt hK)
  have h2 := hK₀ K hK
  rw [Real.dist_0_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)] at h2 ⊢
  linarith

/-- The Fejér means of an integrable function converge to it in `L¹`. -/
theorem tendsto_integral_norm_fejerCoeff_sub {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) (i : m) (j : n) :
    Tendsto (fun K => ∫ t, ‖circPoly (fejerCoeff f K) t i j - f t i j‖ ∂haarAddCircle) atTop
      (𝓝 0) := by
  simp only [circPoly_fejerCoeff_apply hf]
  exact tendsto_fejerMean (hf i j)

/-- A subsequence of the Fejér means of an integrable function converges to it almost everywhere. -/
theorem exists_seq_tendsto_fejerCoeff [Finite m] [Finite n] {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ (∀ N, 0 < ns N) ∧ ∀ᵐ t ∂haarAddCircle,
      Tendsto (fun N => circPoly (fejerCoeff f (ns N)) t) atTop (𝓝 (f t)) := by
  have hcont (K : ℕ) (i : m) (j : n) : Continuous fun t => circPoly (fejerCoeff f K) t i j :=
    (continuous_circPoly_matrix _).matrix_elem i j
  have hlim (i : m) (j : n) : Tendsto (fun N => eLpNorm (fun t =>
      circPoly (fejerCoeff f (N + 1)) t i j - f t i j) 1 haarAddCircle) atTop (𝓝 0) := by
    have h1 := ENNReal.tendsto_ofReal ((tendsto_integral_norm_fejerCoeff_sub hf i j).comp
      (tendsto_add_atTop_nat 1))
    rw [ENNReal.ofReal_zero] at h1
    refine h1.congr fun N => ?_
    have hint : Integrable (fun t => circPoly (fejerCoeff f (N + 1)) t i j - f t i j)
        haarAddCircle :=
      (integrable_haar_of_continuous (hcont (N + 1) i j)).sub (hf i j)
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable]
    exact ofReal_integral_norm_eq_lintegral_enorm hint
  obtain ⟨ns, hns, h⟩ := exists_seq_tendsto_ae_of_eLpNorm (f := f) le_rfl
    (fun N i j => (hcont (N + 1) i j).aestronglyMeasurable)
    (fun i j => (hf i j).aestronglyMeasurable) hlim
  exact ⟨fun N => ns N + 1, fun a b hab => Nat.add_lt_add_right (hns hab) 1,
    fun N => Nat.succ_pos _, h⟩

/-! ### Products with bounded analytic functions -/

/-- The Fourier coefficients of the product of a trigonometric polynomial `P = Σ_q c_q e_q` and a
function `f` with integrable entries: `(P f)^ (k) = Σ_q c_q f̂ (k − q)`. -/
theorem matFourierCoeff_circPoly_mul [Fintype m] (c : ℤ →₀ Matrix l m ℂ)
    {f : UnitAddCircle → Matrix m n ℂ} (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle)
    (k : ℤ) : matFourierCoeff (fun t => circPoly c t * f t) k =
      ∑ q ∈ c.support, c q * matFourierCoeff f (k - q) := by
  ext i j
  have e : (fun t => (circPoly c t * f t) i j) =
      ∑ q ∈ c.support, fun t => fourier q t • (c q * f t) i j := by
    ext t
    rw [circPoly, Finsupp.sum, Matrix.sum_mul, Matrix.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun q _ => by rw [Matrix.smul_mul, Matrix.smul_apply]
  have hint (q : ℤ) : Integrable (fun t => (c q * f t) i j) haarAddCircle :=
    integrable_continuous_mul continuous_const hf i j
  rw [matFourierCoeff, Matrix.of_apply, e,
    fourierCoeff.sum _ _ fun q _ => (hint q).fourier_smul q, Finset.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [fourierCoeff_fourier_smul, ← matFourierCoeff_const_mul _ hf]
  rfl

/-- If `G_N → g` boundedly and almost everywhere, the Fourier coefficients of `G_N f` converge to
those of `g f`. -/
private theorem tendsto_matFourierCoeff_of_bounded [Fintype m]
    {G : ℕ → UnitAddCircle → Matrix l m ℂ} {g : UnitAddCircle → Matrix l m ℂ}
    {f : UnitAddCircle → Matrix m n ℂ} {C : ℝ}
    (hG : ∀ N i j, AEStronglyMeasurable (fun t => G N t i j) haarAddCircle)
    (hGC : ∀ N t i j, ‖G N t i j‖ ≤ C)
    (hlim : ∀ᵐ t ∂haarAddCircle, Tendsto (fun N => G N t) atTop (𝓝 (g t)))
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) (k : ℤ) :
    Tendsto (fun N => matFourierCoeff (fun t => G N t * f t) k) atTop
      (𝓝 (matFourierCoeff (fun t => g t * f t) k)) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hmeas (N : ℕ) : AEStronglyMeasurable (fun t => (G N t * f t) i j) haarAddCircle :=
    aestronglyMeasurable_mul (hG N) (fun i j => (hf i j).aestronglyMeasurable) i j
  refine tendsto_integral_of_dominated_convergence (fun t => ∑ o, C * ‖f t o j‖)
    (fun N => (fourier (-k)).continuous.aestronglyMeasurable.smul (hmeas N))
    (integrable_finsetSum _ fun o _ => (hf o j).norm.const_mul C)
    (fun N => ae_of_all _ fun t => ?_) ?_
  · rw [norm_smul, norm_fourier_apply_eq_one, one_mul]
    dsimp only
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun o _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hGC N t i o) (norm_nonneg _)
  · filter_upwards [hlim] with t ht
    have h1 : Tendsto (fun N => G N t * f t) atTop (𝓝 (g t * f t)) :=
      ((continuous_id.matrix_mul continuous_const).tendsto _).comp ht
    exact ((((continuous_id.matrix_elem i j).tendsto _).comp h1).const_smul _)

/-- `IsHardyOne.bounded_mul` for functions with finitely many rows. -/
private theorem IsHardyOne.bounded_mul_of_finite [Fintype m] [Finite l]
    {g : UnitAddCircle → Matrix l m ℂ} {f : UnitAddCircle → Matrix m n ℂ} {C : ℝ}
    (hg : IsHardyOne g) (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖g t i j‖ ≤ C) (hf : IsHardyOne f) :
    IsHardyOne (fun t => g t * f t) ∧
      matFourierCoeff (fun t => g t * f t) 0 = matFourierCoeff g 0 * matFourierCoeff f 0 := by
  obtain ⟨ns, -, hpos, hlim⟩ := exists_seq_tendsto_fejerCoeff hg.1
  have key (k : ℤ) := tendsto_matFourierCoeff_of_bounded
    (fun N i j => ((continuous_circPoly_matrix _).matrix_elem i j).aestronglyMeasurable)
    (fun N t i j => norm_circPoly_fejerCoeff_le hg.1 (hC.mono fun t ht => ht i j) (hpos N) t)
    hlim hf.1 k
  simp only [matFourierCoeff_circPoly_mul _ hf.1] at key
  -- the Fourier coefficients of negative order of `f` vanish, and the Fejér means are analytic
  have hzero (N : ℕ) (k q : ℤ) (hq : q ∈ (fejerCoeff g (ns N)).support) (hkq : k < q) :
      fejerCoeff g (ns N) q * matFourierCoeff f (k - q) = 0 := by
    rw [hf.2 _ (by omega), Matrix.mul_zero]
  refine ⟨⟨fun i j => ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun o _ => (hf.1 o j).bdd_mul (hg.1 i o).aestronglyMeasurable
      (hC.mono fun t ht => ht i o)
  · refine tendsto_nhds_unique (key k) (tendsto_const_nhds.congr fun N => ?_)
    refine (Finset.sum_eq_zero fun q hq => hzero N k q hq ?_).symm
    exact hk.trans_le (nonneg_of_mem_support_fejerCoeff hg.2 (ns N) q hq)
  · refine tendsto_nhds_unique (key 0) (tendsto_const_nhds.congr fun N => ?_)
    rw [Finset.sum_eq_single 0 (fun q hq hq0 => hzero N 0 q hq
      ((nonneg_of_mem_support_fejerCoeff hg.2 (ns N) q hq).lt_of_ne' hq0))
      (fun h0 => by rw [Finsupp.notMem_support_iff.1 h0, Matrix.zero_mul]), sub_zero,
      fejerCoeff_zero g (hpos N)]

/-- The product of a bounded analytic function and a function of `H¹` is in `H¹`, and its constant
coefficient is the product of the constant coefficients. -/
theorem IsHardyOne.bounded_mul [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {f : UnitAddCircle → Matrix m n ℂ} {C : ℝ} (hg : IsHardyOne g)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖g t i j‖ ≤ C) (hf : IsHardyOne f) :
    IsHardyOne (fun t => g t * f t) ∧
      matFourierCoeff (fun t => g t * f t) 0 = matFourierCoeff g 0 * matFourierCoeff f 0 := by
  have key (i : l) := (hg.submatrix (fun _ : Unit => i) id).bounded_mul_of_finite
    (hC.mono fun t ht _ j => ht i j) hf
  exact ⟨⟨fun i j => (key i).1.1 () j, fun k hk =>
    Matrix.ext fun i j => congrFun (congrFun ((key i).1.2 k hk) ()) j⟩,
    Matrix.ext fun i j => congrFun (congrFun (key i).2 ()) j⟩

/-- The product of a function of `H¹` and a bounded analytic function is in `H¹`, and its constant
coefficient is the product of the constant coefficients. -/
theorem IsHardyOne.mul_bounded [Fintype m] {f : UnitAddCircle → Matrix l m ℂ}
    {g : UnitAddCircle → Matrix m n ℂ} {C : ℝ} (hf : IsHardyOne f) (hg : IsHardyOne g)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖g t i j‖ ≤ C) :
    IsHardyOne (fun t => f t * g t) ∧
      matFourierCoeff (fun t => f t * g t) 0 = matFourierCoeff f 0 * matFourierCoeff g 0 := by
  have key := hg.transpose.bounded_mul (hC.mono fun t ht i j => ht j i) hf.transpose
  simp only [← Matrix.transpose_mul, matFourierCoeff_transpose] at key
  exact ⟨key.1.transpose, Matrix.transpose_injective key.2⟩

/-- The product of a bounded analytic function and a function of `H²` is in `H²`. -/
theorem IsHardyTwo.bounded_mul [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {f : UnitAddCircle → Matrix m n ℂ} {C : ℝ} (hg : IsHardyTwo g)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖g t i j‖ ≤ C) (hf : IsHardyTwo f) :
    IsHardyTwo fun t => g t * f t :=
  ⟨memLp_bounded_mul (fun i j => (hg.1 i j).aestronglyMeasurable) hC hf.1,
    fun _ hk => matFourierCoeff_mul_of_neg hg hf hk⟩

/-- The product of a function of `H²` and a bounded analytic function is in `H²`. -/
theorem IsHardyTwo.mul_bounded [Fintype m] {f : UnitAddCircle → Matrix l m ℂ}
    {g : UnitAddCircle → Matrix m n ℂ} {C : ℝ} (hf : IsHardyTwo f) (hg : IsHardyTwo g)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖g t i j‖ ≤ C) : IsHardyTwo fun t => f t * g t := by
  simpa only [← Matrix.transpose_mul, Matrix.transpose_transpose] using
    (hg.transpose.bounded_mul (hC.mono fun t ht i j => ht j i) hf.transpose).transpose

end HarmonicAnalysis
