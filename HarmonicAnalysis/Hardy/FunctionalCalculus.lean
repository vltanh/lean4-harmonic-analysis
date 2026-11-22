/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Hardy.Approximation
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Functions of matrices and of matrix-valued functions

* The matrices `Mᴴ M`: their entries, trace and determinant. Matrices of full rank; the range of a
  product and of `M Mᴴ`.
* The trace of a matrix-valued function on the circle: integrability, mean value, and limits of the
  integrals (`tendsto_integral_trace_mul`, `TendstoLTwo.tendsto_integral_trace`). The determinant
  and the inverse: measurability.
* The continuous functional calculus of Hermitian matrices: trace and determinant of `φ (W)`,
  measurability of `t ↦ φ (W t)` for a Hermitian matrix-valued function `W` on the circle.
* The square root of a positive semidefinite function, which has entries in `L²` if the function has
  integrable entries.
* The exponential of matrices.

The traces and determinants that are real numbers in the mathematics (those of Hermitian matrices)
are represented by their real parts.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexOrder Topology

namespace HarmonicAnalysis

/-! ### The matrices `Mᴴ M` -/

section ConjTransposeMul

variable {l m n : Type*} [Fintype m]

/-- `(Mᴴ M)_jj = Σ_i |M_ij|²`. -/
theorem conjTranspose_mul_self_apply_self (M : Matrix m n ℂ) (j : n) :
    (Mᴴ * M) j j = ((∑ i, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul',
    Complex.ofReal_sum, Complex.ofReal_pow]

/-- `|M_ij|² ≤ Re (Mᴴ M)_jj`. -/
theorem norm_apply_sq_le_conjTranspose_mul_self (M : Matrix m n ℂ) (i : m) (j : n) :
    ‖M i j‖ ^ 2 ≤ ((Mᴴ * M) j j).re := by
  rw [conjTranspose_mul_self_apply_self, Complex.ofReal_re]
  exact Finset.single_le_sum (f := fun i => ‖M i j‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- The entries of a matrix with orthonormal columns are bounded by `1`. -/
theorem norm_apply_le_one_of_conjTranspose_mul_self [DecidableEq n] {M : Matrix m n ℂ}
    (hM : Mᴴ * M = 1) (i : m) (j : n) : ‖M i j‖ ≤ 1 := by
  have h := norm_apply_sq_le_conjTranspose_mul_self M i j
  rw [hM, Matrix.one_apply_eq, Complex.one_re] at h
  exact (sq_le_one_iff₀ (norm_nonneg _)).1 h

/-- `Re tr (Mᴴ M) = Σ |M_ij|²`. -/
theorem trace_conjTranspose_mul_self_re [Fintype n] (M : Matrix m n ℂ) :
    (Mᴴ * M).trace.re = ∑ j, ∑ i, ‖M i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, conjTranspose_mul_self_apply_self, Complex.re_sum,
    Complex.ofReal_re]

/-- `|M_ij| ≤ √K` if `Re tr (Mᴴ M) ≤ K`. -/
theorem norm_apply_le_sqrt_of_trace_le [Fintype n] {M : Matrix m n ℂ} {K : ℝ}
    (h : (Mᴴ * M).trace.re ≤ K) (i : m) (j : n) : ‖M i j‖ ≤ √K := by
  refine Real.le_sqrt_of_sq_le (le_trans ?_ h)
  rw [trace_conjTranspose_mul_self_re, ← Finset.sum_product_right']
  exact Finset.single_le_sum (f := fun q : m × n => ‖M q.1 q.2‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ (i, j))

/-- `Re det (Mᴴ M) = |det M|²`. -/
theorem det_conjTranspose_mul_self_re [DecidableEq m] (M : Matrix m m ℂ) :
    (Mᴴ * M).det.re = ‖M.det‖ ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- `log det (Mᴴ M) = 2 log |det M|`. -/
theorem log_det_conjTranspose_mul_self_re [DecidableEq m] (M : Matrix m m ℂ) :
    Real.log (Mᴴ * M).det.re = 2 * Real.log ‖M.det‖ := by
  rw [det_conjTranspose_mul_self_re, Real.log_pow, Nat.cast_ofNat]

/-- `Mᴴ M` is positive definite if `M` is invertible. -/
theorem posDef_conjTranspose_mul_self [DecidableEq m] {M : Matrix m m ℂ} (hM : M.det ≠ 0) :
    (Mᴴ * M).PosDef :=
  .conjTranspose_mul_self M (Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hM)))

/-- If `X (Xᴴ A) = A`, then `(Xᴴ A)ᴴ (Xᴴ A) = Aᴴ A`. -/
theorem conjTranspose_mul_self_of_mul_eq [Fintype l] {X : Matrix l m ℂ} {A : Matrix l n ℂ}
    (h : X * (Xᴴ * A) = A) : (Xᴴ * A)ᴴ * (Xᴴ * A) = Aᴴ * A := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h]

/-- If `W = Bᴴ B`, then `Qᴴ W Q = (B Q)ᴴ (B Q)`. -/
theorem conjTranspose_mul_mul_eq [Fintype n] {B : Matrix m n ℂ} {W : Matrix n n ℂ}
    {Q : Matrix n l ℂ} (h : Bᴴ * B = W) : Qᴴ * W * Q = (B * Q)ᴴ * (B * Q) := by
  rw [← h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end ConjTransposeMul

/-! ### Rank and range -/

section Range

variable {l m n : Type*} [Fintype n]

/-- A square matrix of full rank is invertible. -/
theorem det_ne_zero_of_rank_eq [DecidableEq n] {M : Matrix n n ℂ} (h : M.rank = Fintype.card n) :
    M.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_surjective_iff_isUnit.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 h))).ne_zero

/-- The range of a product is contained in that of its left factor. -/
theorem range_mul_le [Fintype l] (M : Matrix m n ℂ) (N : Matrix n l ℂ) :
    LinearMap.range (M * N).mulVecLin ≤ LinearMap.range M.mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- The range of `M Mᴴ` is that of `M`. -/
theorem range_mul_conjTranspose [Fintype m] (M : Matrix m n ℂ) :
    LinearMap.range (M * Mᴴ).mulVecLin = LinearMap.range M.mulVecLin :=
  Submodule.eq_of_le_of_finrank_eq (range_mul_le M Mᴴ) (Matrix.rank_self_mul_conjTranspose M)

end Range

variable {m n : Type*} [Fintype m] [Fintype n]

/-! ### Trace, determinant and inverse of a matrix-valued function -/

/-- The real part of the trace of a function with integrable entries is integrable. -/
theorem integrable_trace_re {W : UnitAddCircle → Matrix n n ℂ}
    (hW : ∀ i j, Integrable (fun t => W t i j) haarAddCircle) :
    Integrable (fun t => (W t).trace.re) haarAddCircle :=
  (integrable_finsetSum Finset.univ fun i _ => hW i i).re

/-- The mean of the trace is the trace of the constant coefficient. -/
theorem integral_trace {f : UnitAddCircle → Matrix n n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) :
    ∫ t, (f t).trace ∂haarAddCircle = (matFourierCoeff f 0).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, matFourierCoeff, Matrix.of_apply, fourierCoeff,
    neg_zero, fourier_zero, one_smul]
  exact integral_finsetSum _ fun i _ => hf i i

/-- The mean of the real part of the trace is the real part of the trace of the constant
coefficient. -/
theorem integral_trace_re {f : UnitAddCircle → Matrix n n ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) :
    ∫ t, (f t).trace.re ∂haarAddCircle = (matFourierCoeff f 0).trace.re := by
  have h : Integrable (fun t => (f t).trace) haarAddCircle :=
    integrable_finsetSum _ fun i _ => hf i i
  rw [← integral_trace hf]
  exact integral_re h

/-- The mean of the real part of the trace of a trigonometric polynomial. -/
theorem integral_trace_circPoly_re (c : ℤ →₀ Matrix n n ℂ) :
    ∫ t, (circPoly c t).trace.re ∂haarAddCircle = (c 0).trace.re := by
  rw [integral_trace_re fun i j => integrable_haar_of_continuous
    ((continuous_circPoly_matrix c).matrix_elem i j), matFourierCoeff_circPoly]

/-- `|Re tr (E A)| ≤ M Σ |A_ki|` if the entries of `E` are bounded by `M`. -/
private theorem norm_trace_mul_re_le {E A : Matrix n n ℂ} {M : ℝ} (hE : ∀ i j, ‖E i j‖ ≤ M) :
    ‖(E * A).trace.re‖ ≤ ∑ i, ∑ k, M * ‖A k i‖ := by
  refine (Complex.abs_re_le_norm _).trans
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hE i k) (norm_nonneg _)

/-- If the continuous functions `E_N` converge to `E` boundedly and almost everywhere, then
`∫ Re tr (E_N W) → ∫ Re tr (E W)` for every function `W` with integrable entries. -/
theorem tendsto_integral_trace_mul {E : ℕ → UnitAddCircle → Matrix n n ℂ}
    {E' W : UnitAddCircle → Matrix n n ℂ} {M : ℝ} (hE : ∀ N, Continuous (E N))
    (hM : ∀ N t i j, ‖E N t i j‖ ≤ M)
    (hlim : ∀ᵐ t ∂haarAddCircle, Tendsto (fun N => E N t) atTop (𝓝 (E' t)))
    (hW : ∀ i j, Integrable (fun t => W t i j) haarAddCircle) :
    Tendsto (fun N => ∫ t, (E N t * W t).trace.re ∂haarAddCircle) atTop
      (𝓝 (∫ t, (E' t * W t).trace.re ∂haarAddCircle)) := by
  refine tendsto_integral_of_dominated_convergence (fun t => ∑ i, ∑ k, M * ‖W t k i‖)
    (fun N => (integrable_trace_re (integrable_continuous_mul (hE N) hW)).aestronglyMeasurable)
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => (hW k i).norm.const_mul M)
    (fun N => ae_of_all _ fun t => norm_trace_mul_re_le (hM N t)) ?_
  filter_upwards [hlim] with t ht
  have hc : Continuous fun A : Matrix n n ℂ => (A * W t).trace.re :=
    Complex.continuous_re.comp (continuous_id.matrix_mul continuous_const).matrix_trace
  exact (hc.tendsto _).comp ht

/-- The mean of `Re tr (Fᴴ F)` is the sum of the squares of the `L²` norms of the entries of `F`. -/
theorem integral_trace_conjTranspose_mul_self {F : UnitAddCircle → Matrix m n ℂ}
    (hF : ∀ i j, MemLp (fun t => F t i j) 2 haarAddCircle) :
    ∫ t, ((F t)ᴴ * F t).trace.re ∂haarAddCircle =
      ∑ j, ∑ i, ∫ t, ‖F t i j‖ ^ 2 ∂haarAddCircle := by
  simp only [trace_conjTranspose_mul_self_re]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    (hF i j).integrable_norm_pow two_ne_zero]
  exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun i _ =>
    (hF i j).integrable_norm_pow two_ne_zero

/-- Convergence in `L²` implies the convergence of the integrals of `Re tr (Fᴴ F)`. -/
theorem TendstoLTwo.tendsto_integral_trace {F : ℕ → UnitAddCircle → Matrix m n ℂ}
    {f : UnitAddCircle → Matrix m n ℂ} (h : TendstoLTwo F f)
    (hF : ∀ N i j, MemLp (fun t => F N t i j) 2 haarAddCircle) :
    Tendsto (fun N => ∫ t, ((F N t)ᴴ * F N t).trace.re ∂haarAddCircle) atTop
      (𝓝 (∫ t, ((f t)ᴴ * f t).trace.re ∂haarAddCircle)) := by
  rw [integral_trace_conjTranspose_mul_self (h.memLp hF),
    funext fun N => integral_trace_conjTranspose_mul_self (hF N)]
  exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun i _ =>
    tendsto_integral_norm_sq (fun N => hF N i j) (h.memLp hF i j) (h i j)

/-- `|f̂ (0)|² ≤ ∫ |f|²`. -/
theorem norm_fourierCoeff_zero_sq_le {f : UnitAddCircle → ℂ}
    (hf : MemLp f 2 haarAddCircle) :
    ‖fourierCoeff f 0‖ ^ 2 ≤ ∫ t, ‖f t‖ ^ 2 ∂haarAddCircle := by
  have h1 : ‖fourierCoeff f 0‖ ≤ ∫ t, ‖f t‖ ∂haarAddCircle := by
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ fun t => ?_))
    simp
  refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
  exact (convexOn_pow 2).map_integral_le (continuousOn_pow 2) isClosed_Ici
    (ae_of_all _ fun t => norm_nonneg _) (hf.integrable one_le_two).norm
    (hf.integrable_norm_pow two_ne_zero)

/-- `Re tr (F̂ (0)ᴴ F̂ (0)) ≤ ∫ Re tr (Fᴴ F)`. -/
theorem trace_matFourierCoeff_zero_le {F : UnitAddCircle → Matrix m n ℂ}
    (hF : ∀ i j, MemLp (fun t => F t i j) 2 haarAddCircle) :
    ((matFourierCoeff F 0)ᴴ * matFourierCoeff F 0).trace.re ≤
      ∫ t, ((F t)ᴴ * F t).trace.re ∂haarAddCircle := by
  rw [integral_trace_conjTranspose_mul_self hF, trace_conjTranspose_mul_self_re]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
    norm_fourierCoeff_zero_sq_le (hF i j)

variable [DecidableEq n]

/-- The determinant of a function with measurable entries is measurable. -/
theorem aestronglyMeasurable_det {W : UnitAddCircle → Matrix n n ℂ}
    (hW : ∀ i j, AEStronglyMeasurable (fun t => W t i j) haarAddCircle) :
    AEStronglyMeasurable (fun t => (W t).det) haarAddCircle := by
  simp only [Matrix.det_apply]
  exact Finset.aestronglyMeasurable_fun_sum _ fun σ _ =>
    (Finset.aestronglyMeasurable_fun_prod _ fun i _ => hW (σ i) i).const_smul _

/-- The entries of the inverse of a matrix-valued function with measurable entries are
measurable. -/
theorem aestronglyMeasurable_inv {W : UnitAddCircle → Matrix n n ℂ}
    (hW : ∀ i j, AEStronglyMeasurable (fun t => W t i j) haarAddCircle) (i j : n) :
    AEStronglyMeasurable (fun t => (W t)⁻¹ i j) haarAddCircle := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  refine (aestronglyMeasurable_det hW).inv₀.mul (aestronglyMeasurable_det fun a b => ?_)
  by_cases h : a = j
  · simp only [h, Matrix.updateRow_self]
    exact aestronglyMeasurable_const
  · simpa only [Matrix.updateRow_ne h] using hW a b

/-! ### The functional calculus -/

omit [DecidableEq n] [Fintype n] in
/-- A matrix-valued function with measurable entries is measurable. -/
private theorem aestronglyMeasurable_of_entries [Finite n] {W : UnitAddCircle → Matrix n n ℂ}
    (hW : ∀ i j, AEStronglyMeasurable (fun t => W t i j) haarAddCircle) :
    AEStronglyMeasurable (fun t i j => W t i j) haarAddCircle :=
  (AEMeasurable.of_eval fun i =>
    AEMeasurable.of_eval fun j => (hW i j).aemeasurable).aestronglyMeasurable

open scoped Matrix.Norms.L2Operator in
/-- `A ↦ φ ((A + Aᴴ) / 2)` is continuous on the space of matrices. -/
private theorem continuous_cfc_half_add {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous fun A : Matrix n n ℂ => cfc φ ((2⁻¹ : ℝ) • (A + Aᴴ)) := by
  have h0 : Continuous fun A : Matrix n n ℂ => Aᴴ := continuous_id.matrix_conjTranspose
  have h : Continuous fun A : Matrix n n ℂ => (2⁻¹ : ℝ) • (A + Aᴴ) :=
    (continuous_id.add h0).const_smul (2⁻¹ : ℝ)
  refine h.cfc_of_mem_nhdsSet φ (s := Set.univ) univ_mem (fun A => ?_) hφ.continuousOn
  exact IsSelfAdjoint.smul (IsSelfAdjoint.all _)
    (Matrix.isHermitian_add_transpose_self A).isSelfAdjoint

/-- A continuous function of a measurable Hermitian matrix-valued function is measurable. -/
theorem aestronglyMeasurable_cfc {W : UnitAddCircle → Matrix n n ℂ}
    (hW : ∀ i j, AEStronglyMeasurable (fun t => W t i j) haarAddCircle)
    (hH : ∀ᵐ t ∂haarAddCircle, (W t).IsHermitian) {φ : ℝ → ℝ} (hφ : Continuous φ) (i j : n) :
    AEStronglyMeasurable (fun t => cfc φ (W t) i j) haarAddCircle := by
  have h : Continuous fun A : n → n → ℂ => cfc φ ((2⁻¹ : ℝ) • (Matrix.of A + (Matrix.of A)ᴴ)) i j :=
    (continuous_cfc_half_add hφ).matrix_elem i j
  refine (h.comp_aestronglyMeasurable (aestronglyMeasurable_of_entries hW)).congr ?_
  filter_upwards [hH] with t ht
  have h2 : (2⁻¹ : ℝ) • (W t + (W t)ᴴ) = W t := by
    rw [ht.eq, ← two_smul ℝ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  exact congrArg (fun A : Matrix n n ℂ => cfc φ A i j) h2

/-- The real part of the trace of a function of a Hermitian matrix is the sum of the values of the
function at the eigenvalues. -/
theorem trace_cfc_re {W : Matrix n n ℂ} (hW : W.IsHermitian) (φ : ℝ → ℝ) :
    (cfc φ W).trace.re = ∑ i, φ (hW.eigenvalues i) := by
  rw [hW.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal,
    Complex.re_sum]
  rfl

/-- The determinant of a function of a Hermitian matrix is the product of the values of the function
at the eigenvalues. -/
theorem det_cfc {W : Matrix n n ℂ} (hW : W.IsHermitian) (φ : ℝ → ℝ) :
    (cfc φ W).det = ∏ i, ((φ (hW.eigenvalues i) : ℝ) : ℂ) := by
  rw [hW.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm,
    ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.det_diagonal]
  rfl

/-- The real part of the trace of a Hermitian matrix is the sum of the eigenvalues. -/
theorem trace_re_eq_sum_eigenvalues {W : Matrix n n ℂ} (hW : W.IsHermitian) :
    W.trace.re = ∑ i, hW.eigenvalues i := by
  rw [← trace_cfc_re hW fun s => s, cfc_id' ℝ W hW.isSelfAdjoint]

/-! ### The square root -/

open scoped MatrixOrder in
/-- The square root of a positive semidefinite matrix is positive semidefinite. (The functional
calculus of a matrix that is not Hermitian is zero.) -/
theorem posSemidef_cfc_sqrt (W : Matrix n n ℂ) : (cfc Real.sqrt W).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.1 (cfc_nonneg fun x _ => Real.sqrt_nonneg x)

open scoped MatrixOrder in
/-- `W^{1/2} W^{1/2} = W` for a positive semidefinite matrix `W`. -/
theorem cfc_sqrt_mul_self {W : Matrix n n ℂ} (hW : W.PosSemidef) :
    cfc Real.sqrt W * cfc Real.sqrt W = W := by
  rw [← cfc_mul Real.sqrt Real.sqrt W]
  conv_rhs => rw [← cfc_id ℝ W hW.isHermitian.isSelfAdjoint]
  exact cfc_congr fun x hx =>
    Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hW.nonneg hx)

open scoped MatrixOrder in
/-- A positive semidefinite matrix `R` with `R² = W` is `W^{1/2}`. -/
theorem eq_cfc_sqrt {R W : Matrix n n ℂ} (hR : R.PosSemidef) (h : R * R = W) :
    R = cfc Real.sqrt W := by
  have hW : W.PosSemidef := by
    have h2 := Matrix.posSemidef_conjTranspose_mul_self R
    rwa [hR.isHermitian.eq, h] at h2
  rw [← CFC.sqrt_unique h hR.nonneg,
    CFC.sqrt_unique (cfc_sqrt_mul_self hW) (posSemidef_cfc_sqrt W).nonneg]

omit [Fintype n] [DecidableEq n] in
/-- If `Aᴴ A = W`, `A` is measurable and the diagonal entries of `W` are integrable, the entries of
`A` are in `L²`. -/
theorem memLp_of_conjTranspose_mul_self {A : UnitAddCircle → Matrix m n ℂ}
    {W : UnitAddCircle → Matrix n n ℂ}
    (hA : ∀ i j, AEStronglyMeasurable (fun t => A t i j) haarAddCircle)
    (hW : ∀ j, Integrable (fun t => W t j j) haarAddCircle)
    (h : ∀ᵐ t ∂haarAddCircle, (A t)ᴴ * A t = W t) (i : m) (j : n) :
    MemLp (fun t => A t i j) 2 haarAddCircle := by
  rw [memLp_two_iff_integrable_sq_norm (hA i j)]
  refine (hW j).mono ((hA i j).norm.pow 2) ?_
  filter_upwards [h] with t ht
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 := norm_apply_sq_le_conjTranspose_mul_self (A t) i j
  rw [ht] at h1
  exact h1.trans (Complex.re_le_norm _)

/-- The square root of a positive semidefinite function with integrable entries has its entries in
`L²`. -/
theorem memLp_cfc_sqrt {W : UnitAddCircle → Matrix n n ℂ}
    (hW : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hpos : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) (i j : n) :
    MemLp (fun t => cfc Real.sqrt (W t) i j) 2 haarAddCircle := by
  refine memLp_of_conjTranspose_mul_self (aestronglyMeasurable_cfc
    (fun i j => (hW i j).aestronglyMeasurable) (hpos.mono fun t ht => ht.isHermitian)
      Real.continuous_sqrt) (fun j => hW j j) ?_ i j
  filter_upwards [hpos] with t ht
  rw [(posSemidef_cfc_sqrt (W t)).isHermitian.eq, cfc_sqrt_mul_self ht]

/-! ### The exponential -/

open scoped Matrix.Norms.L2Operator in
/-- The matrix exponential is continuous. -/
theorem continuous_matrix_exp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ (Matrix n n ℂ)
  exact NormedSpace.exp_continuous

open scoped Matrix.Norms.L2Operator in
/-- The exponential of a Hermitian matrix in terms of the functional calculus. -/
theorem matrix_exp_eq_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    NormedSpace.exp A = cfc Real.exp A :=
  (CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint).symm

/-- `det e^A = e^{tr A}` for a Hermitian matrix `A`. -/
theorem det_matrix_exp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp A).det = ((Real.exp A.trace.re : ℝ) : ℂ) := by
  rw [matrix_exp_eq_cfc hA, det_cfc hA, trace_re_eq_sum_eigenvalues hA, Real.exp_sum,
    Complex.ofReal_prod]

/-- `e^A e^{−A} = 1`. -/
theorem exp_mul_exp_neg (A : Matrix n n ℂ) : NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [Matrix.exp_neg,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp A))]

/-- `e^{A/2} e^{A/2} = e^A`. -/
theorem exp_half_mul_self (A : Matrix n n ℂ) :
    NormedSpace.exp ((2⁻¹ : ℝ) • A) * NormedSpace.exp ((2⁻¹ : ℝ) • A) = NormedSpace.exp A := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
  norm_num

/-- `e^{A/2}` is Hermitian if `A` is. -/
theorem isHermitian_exp_half {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp ((2⁻¹ : ℝ) • A)).IsHermitian :=
  Matrix.IsHermitian.exp (hA.smul (IsSelfAdjoint.all _))

/-- `(e^{A/2})ᴴ e^{A/2} = e^A` if `A` is Hermitian. -/
theorem conjTranspose_exp_half_mul_self {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp ((2⁻¹ : ℝ) • A))ᴴ * NormedSpace.exp ((2⁻¹ : ℝ) • A) = NormedSpace.exp A := by
  rw [(isHermitian_exp_half hA).eq, exp_half_mul_self]

/-- The exponential of a Hermitian matrix is positive definite. -/
theorem posDef_matrix_exp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp A).PosDef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (NormedSpace.exp ((2⁻¹ : ℝ) • A))
  rw [conjTranspose_exp_half_mul_self hA] at h
  exact h.posDef_iff_isUnit.2 (Matrix.isUnit_exp A)

end HarmonicAnalysis
