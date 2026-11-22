module

public import VectorValuedHarmonicAnalysis.Hardy.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Szegő and Riesz factorization of matrix-valued functions

* `exists_szego_factorization`: if `a : 𝕋 → M_n (ℂ)` is continuous with invertible values, then
  `a = Ψ h` almost everywhere, with `Ψ` unitary-valued, `h ∈ H²` and `h⁻¹ ∈ H²` (Szegő
  factorization).
* `exists_riesz_factorization`: for `δ > 0`, an analytic matrix polynomial `f` is a product
  `f = g h` almost everywhere of `g, h ∈ H²`, with `‖g (t)‖_{S_{2p}}² ≤ ‖f (t)‖_{S_p}` and
  `‖h (t)‖_{S_{2p}}² ≤ ‖f (t)‖_{S_p} + δ` for almost every `t` and every `p ≥ 1`.

D. Sarason (1967) proved that every `f ∈ H¹ (C_1)` is a product `g h` with
`‖f‖_{H¹ (C_1)} = ‖g‖_{H² (C_2)} ‖h‖_{H² (C_2)}`; the matrix case goes back to Helson and
Lowdenslager. F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley inequalities*,
Ark. Mat. 29 (1991), use this theorem (pp. 243, 249) and the equality (β), p. 252, its analogue in
the mixed norms of `L¹ (𝕋; C_p)` and `L² (𝕋; C_{2p})`. Here the factorization is proved for analytic
polynomials whose coefficients are finite matrices, and the norms are controlled up to `δ`.

## The proof

The proof is that of T. N. Bekjan and Q. Xu, *Riesz and Szegő type factorizations for noncommutative
Hardy spaces*, J. Operator Theory 62 (2009), 215–231 (arXiv:0705.1947), Theorem 3.1, the case
`p = q = 2` (Arveson's argument), and Theorem 3.4, for the algebras `M = L^∞ (𝕋; M_n)` and
`A = H^∞ (𝕋; M_n)`, whose diagonal is `M_n`. Let `x` be the projection of `a` on the closure
`[a A_0]` of `a A_0` in `L²` and `y = a − x`. Then `yᴴ y` is a constant positive definite matrix
`D`; `Ψ = y D^{-1/2}` is the unitary part of `y`, and `h = Ψᴴ a`. For the Riesz factorization of `f`
one takes `a = (fᴴ f + η²)^{1/4}`, with `η = δ / (n + 1)`, and `g = f a⁻² · a Ψ = f h⁻¹`.

Departures from the source, possible because the diagonal is `M_n` and `f` is a polynomial:

* `D` is a constant positive definite matrix, so `A_0 D^{1/2} = A_0`: the orthogonal decomposition
  (3.2) and the equalities (3.3) of the source are not needed.
* The source proves `Φ (h) Φ (h⁻¹) = 1`, where `Φ` is the mean, and then `Ψ = y Φ (h⁻¹)`. Here
  `Φ (h⁻¹)` is the explicit matrix `D^{-1/2}`: `h⁻¹ = a⁻¹ Ψ = a⁻¹ y D^{-1/2} =
  (1 − a⁻¹ x) D^{-1/2}`, and `a⁻¹ x` has no Fourier coefficients of order `≤ 0`.
* `g = f h⁻¹` is in `H²` because it is the product of a polynomial and a function in `H²`;
  Proposition 3.3 of the source is not needed.
* Theorem 3.4 of the source bounds the norms of `g` and `h` in `L^{2p} (M)`. The bounds here are
  pointwise, for almost every `t` and all `p ≥ 1` at once; the source's construction yields them.
  Integrated, they give the norms of `L^{2p} (M)` as well as the mixed norms of (β).
-/

@[expose] public section

open MeasureTheory AddCircle BanachProbability
open scoped ENNReal Matrix ComplexOrder ComplexConjugate

namespace VectorValuedHarmonicAnalysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The columns of `a e_k` -/

/-- The column `e_k a v`, a continuous `ℂⁿ`-valued function. -/
private noncomputable def column (a : UnitAddCircle → Matrix n n ℂ) (k : ℤ) (v : n → ℂ)
    (t : UnitAddCircle) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fourier k t • (a t).mulVec v)

omit [DecidableEq n] in
private theorem memLp_column {a : UnitAddCircle → Matrix n n ℂ} (ha : Continuous a) (k : ℤ)
    (v : n → ℂ) : MemLp (column a k v) 2 haarAddCircle := by
  refine MemLp.of_eval_piLp fun i => ?_
  have hc : Continuous fun t => column a k v t i := by
    simp only [column, Pi.smul_apply, smul_eq_mul, PiLp.toLp_apply]
    exact (fourier k).continuous.mul ((continuous_apply i).comp (ha.matrix_mulVec continuous_const))
  exact hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `[a A_0]` for `r = 1` and `[a A]` for `r = 0`: the closed span in `L² (𝕋; ℂⁿ)` of the columns
`e_k a v`, `k ≥ r`. -/
private noncomputable def columnSpace {a : UnitAddCircle → Matrix n n ℂ} (ha : Continuous a)
    (r : ℤ) : Submodule ℂ (Lp (EuclideanSpace ℂ n) 2 (haarAddCircle (T := 1))) :=
  (Submodule.span ℂ {f | ∃ k : ℤ, r ≤ k ∧ ∃ v : n → ℂ,
    f = (memLp_column ha k v).toLp}).topologicalClosure

omit [DecidableEq n] in
private theorem column_mem_columnSpace {a : UnitAddCircle → Matrix n n ℂ} (ha : Continuous a)
    {r k : ℤ} (hk : r ≤ k) (v : n → ℂ) : (memLp_column ha k v).toLp ∈ columnSpace ha r :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, hk, v, rfl⟩)

omit [DecidableEq n] in
/-- A vector orthogonal to the columns `e_k a v`, `k ≥ r`, is orthogonal to their closed span. -/
private theorem inner_eq_zero_of_mem_columnSpace {a : UnitAddCircle → Matrix n n ℂ}
    (ha : Continuous a) {r : ℤ} {w f : Lp (EuclideanSpace ℂ n) 2 (haarAddCircle (T := 1))}
    (hw : ∀ k : ℤ, r ≤ k → ∀ v : n → ℂ, inner ℂ w (memLp_column ha k v).toLp = 0)
    (hf : f ∈ columnSpace ha r) : inner ℂ w f = 0 := by
  have hle : columnSpace ha r ≤ LinearMap.ker (innerSL ℂ w).toLinearMap := by
    refine Submodule.topologicalClosure_minimal _ ?_ (innerSL ℂ w).isClosed_ker
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, v, rfl⟩
    exact hw k hk v
  exact hle hf

omit [DecidableEq n] in
private theorem inner_column (a : UnitAddCircle → Matrix n n ℂ) (k : ℤ) (v : n → ℂ)
    (t : UnitAddCircle) (x : EuclideanSpace ℂ n) :
    inner ℂ (column a k v t) x = fourier (-k) t * (star v ⬝ᵥ ((a t)ᴴ).mulVec x.ofLp) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, column, fourier_neg, star_smul, dotProduct_smul,
    Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  rfl

omit [DecidableEq n] in
/-- `y ⟂ [a A_0]` implies `y ⟂ [a A] A_0`: multiplication by `e_k`, `k ≥ 1`, maps `[a A]` into
`[a A_0]`. -/
private theorem fourierCoeff_inner_eq_zero {a : UnitAddCircle → Matrix n n ℂ} (ha : Continuous a)
    {y f : Lp (EuclideanSpace ℂ n) 2 (haarAddCircle (T := 1))} (hy : y ∈ (columnSpace ha 1)ᗮ)
    (hf : f ∈ columnSpace ha 0) {k : ℤ} (hk : k < 0) :
    fourierCoeff (fun t => inner ℂ (y t) (f t)) k = 0 := by
  have hw : MemLp (fun t => fourier k t • y t) 2 haarAddCircle := by
    refine (Lp.memLp y).of_le ((fourier k).continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable y)) (ae_of_all _ fun t => ?_)
    rw [norm_smul, norm_fourier_apply_eq_one, one_mul]
  have h0 : inner ℂ hw.toLp f = 0 := by
    refine inner_eq_zero_of_mem_columnSpace ha (r := 0) (fun m hm v => ?_) hf
    have h1 : inner ℂ y (memLp_column ha (m - k) v).toLp = 0 :=
      (Submodule.mem_orthogonal' _ _).1 hy _ (column_mem_columnSpace ha (by omega) v)
    rw [← h1, L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hw.coeFn_toLp, (memLp_column ha m v).coeFn_toLp,
      (memLp_column ha (m - k) v).coeFn_toLp] with t h1 h2 h3
    rw [h1, h2, h3, inner_smul_left, ← fourier_neg, ← inner_smul_right, column, column,
      ← WithLp.toLp_smul, smul_smul, ← fourier_add, neg_add_eq_sub]
  rw [← h0, L2.inner_def, fourierCoeff]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLp] with t h1
  rw [h1, inner_smul_left, ← fourier_neg, smul_eq_mul]

/-- For `x ∈ [a A_0]`, `a⁻¹ x ∈ [A_0]`: the Fourier coefficients of `a⁻¹ x` of order `≤ 0` vanish.
-/
private theorem fourierCoeff_inv_mulVec_eq_zero {a : UnitAddCircle → Matrix n n ℂ}
    (ha : Continuous a) (hinv : Continuous fun t => (a t)⁻¹) (hunit : ∀ t, IsUnit (a t))
    {f : Lp (EuclideanSpace ℂ n) 2 (haarAddCircle (T := 1))} (hf : f ∈ columnSpace ha 1) {k : ℤ}
    (hk : k ≤ 0) (i : n) : fourierCoeff (fun t => ((a t)⁻¹).mulVec (f t).ofLp i) k = 0 := by
  have hb : Continuous fun t => ((a t)⁻¹)ᴴ := hinv.matrix_conjTranspose
  have hw (t : UnitAddCircle) (x : EuclideanSpace ℂ n) :
      inner ℂ (column (fun t => ((a t)⁻¹)ᴴ) k (Pi.single i 1) t) x =
        fourier (-k) t * ((a t)⁻¹).mulVec x.ofLp i := by
    rw [inner_column, Matrix.conjTranspose_conjTranspose, ← Pi.single_star, star_one,
      single_one_dotProduct]
  have h0 : inner ℂ (memLp_column hb k (Pi.single i 1)).toLp f = 0 := by
    refine inner_eq_zero_of_mem_columnSpace ha (r := 1) (fun m hm v => ?_) hf
    have h1 : fourierCoeff (fun t : UnitAddCircle => v i * fourier m t) k = 0 := by
      rw [fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_eq_of_ne (by omega), mul_zero]
    rw [← h1, L2.inner_def, fourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_column hb k (Pi.single i 1)).coeFn_toLp,
      (memLp_column ha m v).coeFn_toLp] with t h1 h2
    rw [h1, h2, hw, column, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hunit t)), Matrix.one_mulVec]
    simp [mul_comm]
  rw [← h0, L2.inner_def, fourierCoeff]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_column hb k (Pi.single i 1)).coeFn_toLp] with t h1
  rw [h1, hw, smul_eq_mul]

/-! ### Products with continuous and constant matrices -/

omit [Fintype n] [DecidableEq n] in
/-- The product of a continuous function and an `L²` function is in `L²`. -/
private theorem memLp_continuous_mul {φ u : UnitAddCircle → ℂ} (hφ : Continuous φ)
    (hu : MemLp u 2 haarAddCircle) : MemLp (fun t => φ t * u t) 2 haarAddCircle := by
  have h : MemLp φ ∞ haarAddCircle :=
    hφ.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) _
  exact h.fun_mul hu

omit [DecidableEq n] in
/-- The product of a continuous matrix and a matrix with entries in `L²` has entries in `L²`. -/
private theorem memLp_continuous_matrix_mul {l m : Type*} {B : UnitAddCircle → Matrix l n ℂ}
    (hB : Continuous B) {Y : UnitAddCircle → Matrix n m ℂ}
    (hY : ∀ i j, MemLp (fun t => Y t i j) 2 haarAddCircle) (i : l) (j : m) :
    MemLp (fun t => (B t * Y t) i j) 2 haarAddCircle := by
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ fun o _ => memLp_continuous_mul (hB.matrix_elem i o) (hY o j)

omit [DecidableEq n] in
private theorem matFourierCoeff_mul_const {l m : Type*} {f : UnitAddCircle → Matrix l n ℂ}
    (hf : ∀ i j, MemLp (fun t => f t i j) 2 haarAddCircle) (R : Matrix n m ℂ) (k : ℤ) :
    matFourierCoeff (fun t => f t * R) k = matFourierCoeff f k * R := by
  ext i j
  have e : (fun t => (f t * R) i j) = ∑ o, fun t => R o j * f t i o := by
    ext t
    simp [Matrix.mul_apply, mul_comm]
  rw [matFourierCoeff, Matrix.of_apply, e, fourierCoeff.sum _ _ fun o _ =>
    ((hf i o).const_mul _).integrable one_le_two, Finset.sum_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun o _ => by rw [fourierCoeff.const_mul, mul_comm]; rfl

omit [DecidableEq n] in
private theorem matFourierCoeff_const_mul {l m : Type*} {f : UnitAddCircle → Matrix n m ℂ}
    (hf : ∀ i j, Integrable (fun t => f t i j) haarAddCircle) (R : Matrix l n ℂ) (k : ℤ) :
    matFourierCoeff (fun t => R * f t) k = R * matFourierCoeff f k := by
  ext i j
  have e : (fun t => (R * f t) i j) = ∑ o, fun t => R i o * f t o j := by
    ext t
    simp [Matrix.mul_apply]
  rw [matFourierCoeff, Matrix.of_apply, e, fourierCoeff.sum _ _ fun o _ =>
    (hf o j).const_mul _, Finset.sum_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun o _ => by rw [fourierCoeff.const_mul]; rfl

/-! ### The orthogonal part of `a`

Bekjan–Xu, proof of Theorem 3.1: `y = a − x`, where `x` is the projection of `a` on `[a A_0]`. -/

section OrthogonalPart

variable {a : UnitAddCircle → Matrix n n ℂ}

omit [DecidableEq n] in
private theorem completeSpace_columnSpace (ha : Continuous a) (r : ℤ) :
    CompleteSpace (columnSpace ha r) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

attribute [local instance] completeSpace_columnSpace

/-- The columns of `x`. -/
private noncomputable def projCol (ha : Continuous a) (j : n) :
    Lp (EuclideanSpace ℂ n) 2 (haarAddCircle (T := 1)) :=
  (columnSpace ha 1).starProjection (memLp_column ha 0 (Pi.single j 1)).toLp

/-- The columns of `y`. -/
private noncomputable def orthCol (ha : Continuous a) (j : n) :
    Lp (EuclideanSpace ℂ n) 2 (haarAddCircle (T := 1)) :=
  (memLp_column ha 0 (Pi.single j 1)).toLp - projCol ha j

/-- The function `y`. -/
private noncomputable def orthPart (ha : Continuous a) (t : UnitAddCircle) : Matrix n n ℂ :=
  Matrix.of fun i j => (orthCol ha j t).ofLp i

private theorem projCol_mem (ha : Continuous a) (j : n) : projCol ha j ∈ columnSpace ha 1 :=
  Submodule.starProjection_apply_mem _ _

/-- `y ⟂ [a A_0]`. -/
private theorem orthCol_mem_orthogonal (ha : Continuous a) (j : n) :
    orthCol ha j ∈ (columnSpace ha 1)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

/-- `y ∈ [a A]`. -/
private theorem orthCol_mem_columnSpace (ha : Continuous a) (j : n) :
    orthCol ha j ∈ columnSpace ha 0 := by
  refine Submodule.sub_mem _ (column_mem_columnSpace ha le_rfl _) ?_
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_) (projCol_mem ha j)
  rintro _ ⟨k, hk, v, rfl⟩
  exact ⟨k, by omega, v, rfl⟩

private theorem stronglyMeasurable_orthPart (ha : Continuous a) (i j : n) :
    StronglyMeasurable fun t => orthPart ha t i j :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_stronglyMeasurable
    (Lp.stronglyMeasurable (orthCol ha j))

private theorem memLp_orthPart (ha : Continuous a) (i j : n) :
    MemLp (fun t => orthPart ha t i j) 2 haarAddCircle :=
  (Lp.memLp (orthCol ha j)).eval_piLp i

/-- `yᴴ y` has no Fourier coefficients of negative order, because `y ⟂ [y A_0]`. -/
private theorem matFourierCoeff_orthPart_self (ha : Continuous a) {k : ℤ} (hk : k < 0) :
    matFourierCoeff (fun t => (orthPart ha t)ᴴ * orthPart ha t) k = 0 := by
  ext i j
  rw [matFourierCoeff, Matrix.of_apply, Matrix.zero_apply,
    ← fourierCoeff_inner_eq_zero ha (orthCol_mem_orthogonal ha i) (orthCol_mem_columnSpace ha j) hk]
  congr 1
  ext t
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- `yᴴ a` has no Fourier coefficients of negative order, because `y ⟂ [a A_0]`. -/
private theorem matFourierCoeff_orthPart_mul (ha : Continuous a) {k : ℤ} (hk : k < 0) :
    matFourierCoeff (fun t => (orthPart ha t)ᴴ * a t) k = 0 := by
  ext i j
  have hcol (t : UnitAddCircle) (i : n) : (column a 0 (Pi.single j 1) t).ofLp i = a t i j := by
    simp [column]
  rw [matFourierCoeff, Matrix.of_apply, Matrix.zero_apply,
    ← fourierCoeff_inner_eq_zero ha (orthCol_mem_orthogonal ha i)
      (column_mem_columnSpace ha le_rfl (Pi.single j 1)) hk]
  refine congrFun (fourierCoeff_congr_ae ?_) k
  filter_upwards [(memLp_column ha 0 (Pi.single j 1)).coeFn_toLp] with t ht
  rw [ht, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp only [dotProduct, hcol]
  rfl

/-- `a⁻¹ y = 1 − a⁻¹ x`. -/
private theorem inv_mul_orthPart_ae (ha : Continuous a) (ha' : ∀ t, IsUnit (a t)) (i j : n) :
    (fun t => ((a t)⁻¹ * orthPart ha t) i j) =ᵐ[haarAddCircle]
      (fun _ => (1 : Matrix n n ℂ) i j) +
        fun t => (-1 : ℂ) * ((a t)⁻¹).mulVec (projCol ha j t).ofLp i := by
  filter_upwards [(memLp_column ha 0 (Pi.single j 1)).coeFn_toLp,
    Lp.coeFn_sub (memLp_column ha 0 (Pi.single j 1)).toLp (projCol ha j)] with t h1 h2
  have h3 : (orthCol ha j t).ofLp = (a t).mulVec (Pi.single j 1) - (projCol ha j t).ofLp := by
    rw [orthCol, h2, Pi.sub_apply, h1]
    simp [column]
  have h4 : ((a t)⁻¹ * orthPart ha t) i j = ((a t)⁻¹).mulVec (orthCol ha j t).ofLp i := rfl
  rw [h4, h3, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (ha' t))]
  simp [sub_eq_add_neg]

/-- `a⁻¹ y − 1 = −a⁻¹ x` has no Fourier coefficients of order `≤ 0`, because `a⁻¹ x ∈ [A_0]`. -/
private theorem matFourierCoeff_inv_mul_orthPart (ha : Continuous a) (ha' : ∀ t, IsUnit (a t))
    (hinv : Continuous fun t => (a t)⁻¹) {k : ℤ} (hk : k ≤ 0) :
    matFourierCoeff (fun t => (a t)⁻¹ * orthPart ha t) k = if k = 0 then 1 else 0 := by
  ext i j
  have hint : Integrable (fun t => ((a t)⁻¹).mulVec (projCol ha j t).ofLp i) haarAddCircle := by
    refine MemLp.integrable (q := 2) one_le_two ?_
    simp only [Matrix.mulVec, dotProduct]
    exact memLp_finsetSum _ fun o _ =>
      memLp_continuous_mul (hinv.matrix_elem i o) ((Lp.memLp (projCol ha j)).eval_piLp o)
  rw [matFourierCoeff, Matrix.of_apply, fourierCoeff_congr_ae (inv_mul_orthPart_ae ha ha' i j),
    fourierCoeff.add (integrable_const _) (hint.const_mul _), Pi.add_apply,
    fourierCoeff.const_mul, fourierCoeff_inv_mulVec_eq_zero ha hinv ha' (projCol_mem ha j) hk,
    fourierCoeff_const, mul_zero, add_zero]
  split_ifs <;> simp

end OrthogonalPart

/-! ### `yᴴ y` is constant and positive definite -/

omit [DecidableEq n] in
private theorem integrable_conjTranspose_mul {X Y : UnitAddCircle → Matrix n n ℂ}
    (hX : ∀ i j, MemLp (fun t => X t i j) 2 haarAddCircle)
    (hY : ∀ i j, MemLp (fun t => Y t i j) 2 haarAddCircle) (i j : n) :
    Integrable (fun t => ((X t)ᴴ * Y t) i j) haarAddCircle := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact integrable_finsetSum _ fun o _ => (hX o i).star.integrable_mul (hY o j)

omit [DecidableEq n] in
/-- Bekjan–Xu, proof of Theorem 3.1: `yᴴ y ∈ [A]_1 ∩ [A^*]_1 = L¹ (D)`. -/
private theorem exists_ae_conjTranspose_mul_self_eq {Y : UnitAddCircle → Matrix n n ℂ}
    (hY : ∀ i j, MemLp (fun t => Y t i j) 2 haarAddCircle)
    (h0 : ∀ k : ℤ, k < 0 → matFourierCoeff (fun t => (Y t)ᴴ * Y t) k = 0) :
    ∃ D : Matrix n n ℂ, ∀ᵐ t ∂haarAddCircle, (Y t)ᴴ * Y t = D := by
  have hconj (g : UnitAddCircle → ℂ) (k : ℤ) :
      fourierCoeff (fun t => conj (g t)) k = conj (fourierCoeff g (-k)) := by
    rw [fourierCoeff, fourierCoeff, ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [smul_eq_mul, map_mul, fourier_neg, Complex.conj_conj]
  have hneg (i j : n) (k : ℤ) (hk : k < 0) :
      fourierCoeff (fun t => ((Y t)ᴴ * Y t) i j) k = 0 := congrFun (congrFun (h0 k hk) i) j
  have hherm (i j : n) : (fun t => ((Y t)ᴴ * Y t) i j) =
      fun t => conj (((Y t)ᴴ * Y t) j i) := by
    ext t
    simp [Matrix.mul_apply, mul_comm]
  refine ⟨matFourierCoeff (fun t => (Y t)ᴴ * Y t) 0, ?_⟩
  have key : ∀ᵐ t ∂haarAddCircle, ∀ i j, ((Y t)ᴴ * Y t) i j =
      fourierCoeff (fun t => ((Y t)ᴴ * Y t) i j) 0 := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    refine ae_eq_const_of_fourierCoeff_eq_zero (integrable_conjTranspose_mul hY hY i j)
      fun k hk => ?_
    rcases lt_or_gt_of_ne hk with hk | hk
    · exact hneg i j k hk
    · rw [hherm, hconj, hneg j i (-k) (by omega), map_zero]
  filter_upwards [key] with t ht
  ext i j
  exact ht i j

/-- Bekjan–Xu, proof of Theorem 3.1: `y` is of full support, that is, the constant `yᴴ y` is
positive definite, because `τ (a⁻¹ y d) = τ (d)`. -/
private theorem posDef_of_ae_conjTranspose_mul_self_eq {a Y : UnitAddCircle → Matrix n n ℂ}
    (hinv : Continuous fun t => (a t)⁻¹) (hY : ∀ i j, MemLp (fun t => Y t i j) 2 haarAddCircle)
    (h0 : matFourierCoeff (fun t => (a t)⁻¹ * Y t) 0 = 1) {D : Matrix n n ℂ}
    (hD : ∀ᵐ t ∂haarAddCircle, (Y t)ᴴ * Y t = D) : D.PosDef := by
  obtain ⟨t₀, ht₀⟩ := hD.exists
  have hpsd : D.PosSemidef := ht₀ ▸ Matrix.posSemidef_conjTranspose_mul_self _
  rw [hpsd.posDef_iff_mulVec_injective]
  refine (injective_iff_map_eq_zero D.mulVecLin).2 fun v hv => ?_
  -- `y v = 0` almost everywhere, hence `0 = ∫ a⁻¹ y v = v`
  have hYv : ∀ᵐ t ∂haarAddCircle, (a t)⁻¹ * Y t * Matrix.replicateCol Unit v = 0 := by
    filter_upwards [hD] with t ht
    have : (Y t).mulVec v = 0 := by
      rw [← Matrix.conjTranspose_mul_self_mulVec_eq_zero, ht]
      exact hv
    rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, this]
    ext i j
    simp
  have h1 := matFourierCoeff_mul_const (memLp_continuous_matrix_mul hinv hY)
    (Matrix.replicateCol Unit v) 0
  rw [h0, Matrix.one_mul, matFourierCoeff_congr_ae hYv] at h1
  ext i
  have h2 := congrFun (congrFun h1 i) ()
  simpa [matFourierCoeff, fourierCoeff] using h2.symm

open scoped MatrixOrder in
/-- `R = D^{-1/2}`, the inverse of the constant matrix `|y|`. -/
private theorem exists_inv_sqrt {D : Matrix n n ℂ} (hD : D.PosDef) :
    ∃ R : Matrix n n ℂ, Rᴴ * D * R = 1 := by
  have h1 : CFC.sqrt D * CFC.sqrt D = D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have h2 : (CFC.sqrt D)ᴴ = CFC.sqrt D :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg D)).isHermitian
  have h3 : IsUnit (CFC.sqrt D).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 hD.isUnit
    rw [← h1, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  refine ⟨(CFC.sqrt D)⁻¹, ?_⟩
  rw [Matrix.conjTranspose_nonsing_inv, h2]
  calc (CFC.sqrt D)⁻¹ * D * (CFC.sqrt D)⁻¹
      = (CFC.sqrt D)⁻¹ * (CFC.sqrt D * CFC.sqrt D) * (CFC.sqrt D)⁻¹ := by rw [h1]
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h3, Matrix.one_mul,
        Matrix.mul_nonsing_inv _ h3]

/-- The unitary part `y |y|⁻¹` of `y`, redefined on a null set so as to be unitary everywhere. -/
private theorem exists_unitary {Y : UnitAddCircle → Matrix n n ℂ}
    (hY : ∀ i j, StronglyMeasurable fun t => Y t i j) {D R : Matrix n n ℂ}
    (hD : ∀ᵐ t ∂haarAddCircle, (Y t)ᴴ * Y t = D) (hR : Rᴴ * D * R = 1) :
    ∃ Ψ : UnitAddCircle → Matrix n n ℂ, (∀ i j, StronglyMeasurable fun t => Ψ t i j) ∧
      (∀ t, Ψ t ∈ Matrix.unitaryGroup n ℂ) ∧ ∀ᵐ t ∂haarAddCircle, Ψ t = Y t * R := by
  classical
  have hm (i j : n) : StronglyMeasurable fun t => (Y t * R) i j := by
    simp only [Matrix.mul_apply]
    exact Finset.stronglyMeasurable_fun_sum _ fun o _ => (hY i o).mul_const _
  have hset : MeasurableSet {t | Y t * R ∈ Matrix.unitaryGroup n ℂ} := by
    have : {t | Y t * R ∈ Matrix.unitaryGroup n ℂ} =
        ⋂ i, ⋂ j, {t | ((Y t * R)ᴴ * (Y t * R)) i j = (1 : Matrix n n ℂ) i j} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.mem_unitaryGroup_iff',
        Matrix.star_eq_conjTranspose, ← Matrix.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    refine StronglyMeasurable.measurableSet_eq_fun ?_ stronglyMeasurable_const
    simp only [Matrix.mul_apply (M := (Y _ * R)ᴴ), Matrix.conjTranspose_apply]
    exact Finset.stronglyMeasurable_fun_sum _ fun o _ => (hm o i).star.mul (hm o j)
  refine ⟨fun t => if Y t * R ∈ Matrix.unitaryGroup n ℂ then Y t * R else 1, fun i j => ?_,
    fun t => ?_, ?_⟩
  · simp only [apply_ite (fun A : Matrix n n ℂ => A i j)]
    exact StronglyMeasurable.ite hset (hm i j) stronglyMeasurable_const
  · beta_reduce
    split_ifs with h
    · exact h
    · exact one_mem _
  · filter_upwards [hD] with t ht
    rw [ite_eq_left]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc (Y t)ᴴ, ht, ← Matrix.mul_assoc, hR]

/-! ### The Szegő factorization -/

omit [DecidableEq n] in
/-- `h = Ψᴴ a = D^{-1/2} yᴴ a` is in `H²`. -/
private theorem isHardyTwo_conjTranspose_mul {a Y Ψ : UnitAddCircle → Matrix n n ℂ}
    (ha : Continuous a) (hY : ∀ i j, MemLp (fun t => Y t i j) 2 haarAddCircle)
    (hΨ2 : ∀ i j, MemLp (fun t => Ψ t i j) 2 haarAddCircle) {R : Matrix n n ℂ}
    (hΨ : ∀ᵐ t ∂haarAddCircle, Ψ t = Y t * R)
    (hYa : ∀ k : ℤ, k < 0 → matFourierCoeff (fun t => (Y t)ᴴ * a t) k = 0) :
    IsHardyTwo fun t => (Ψ t)ᴴ * a t := by
  refine ⟨fun i j => ?_, fun k hk => ?_⟩
  · have := (memLp_continuous_matrix_mul ha.matrix_conjTranspose hΨ2 j i).star
    refine (memLp_congr_ae (ae_of_all _ fun t => ?_)).1 this
    rw [Pi.star_apply, ← Matrix.conjTranspose_apply, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  · have e : ∀ᵐ t ∂haarAddCircle, (Ψ t)ᴴ * a t = Rᴴ * ((Y t)ᴴ * a t) := by
      filter_upwards [hΨ] with t ht
      rw [ht, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [matFourierCoeff_congr_ae e, matFourierCoeff_const_mul
      (integrable_conjTranspose_mul hY (memLp_entry_of_continuous ha)), hYa k hk, Matrix.mul_zero]

omit [DecidableEq n] in
/-- `h⁻¹ = a⁻¹ Ψ = a⁻¹ y D^{-1/2} = (1 − a⁻¹ x) D^{-1/2}` is in `H²`. (Here `b = a⁻¹`.) -/
private theorem isHardyTwo_inv_mul {b Y Ψ : UnitAddCircle → Matrix n n ℂ} (hb : Continuous b)
    (hY : ∀ i j, MemLp (fun t => Y t i j) 2 haarAddCircle)
    (hΨ2 : ∀ i j, MemLp (fun t => Ψ t i j) 2 haarAddCircle) {R : Matrix n n ℂ}
    (hΨ : ∀ᵐ t ∂haarAddCircle, Ψ t = Y t * R)
    (hbY : ∀ k : ℤ, k < 0 → matFourierCoeff (fun t => b t * Y t) k = 0) :
    IsHardyTwo fun t => b t * Ψ t := by
  refine ⟨memLp_continuous_matrix_mul hb hΨ2, fun k hk => ?_⟩
  have e : ∀ᵐ t ∂haarAddCircle, b t * Ψ t = b t * Y t * R := by
    filter_upwards [hΨ] with t ht
    rw [ht, Matrix.mul_assoc]
  rw [matFourierCoeff_congr_ae e, matFourierCoeff_mul_const (memLp_continuous_matrix_mul hb hY),
    hbY k hk, Matrix.zero_mul]

/-- **Szegő factorization** (Bekjan–Xu (2009), Theorem 3.1, for the algebra `H^∞ (𝕋; M_n)` and a
continuous function): if `a : 𝕋 → M_n (ℂ)` is continuous with invertible values, then `a = Ψ h`
almost everywhere, with `Ψ` unitary-valued, `h ∈ H²` and `h⁻¹ ∈ H²`. -/
theorem exists_szego_factorization {a : UnitAddCircle → Matrix n n ℂ} (ha : Continuous a)
    (ha' : ∀ t, IsUnit (a t)) :
    ∃ Ψ h : UnitAddCircle → Matrix n n ℂ, (∀ i j, StronglyMeasurable fun t => Ψ t i j) ∧
      (∀ t, Ψ t ∈ Matrix.unitaryGroup n ℂ) ∧ IsHardyTwo h ∧ IsHardyTwo (fun t => (h t)⁻¹) ∧
      ∀ᵐ t ∂haarAddCircle, a t = Ψ t * h t := by
  have hdet (t : UnitAddCircle) : IsUnit (a t).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (ha' t)
  have hinv : Continuous fun t => (a t)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    exact (ha.matrix_det.inv₀ fun t => (hdet t).ne_zero).smul ha.matrix_adjugate
  have hY := memLp_orthPart ha
  -- `yᴴ y = D` is a constant positive definite matrix and `Ψ = y D^{-1/2}`
  obtain ⟨D, hD⟩ := exists_ae_conjTranspose_mul_self_eq hY fun _ =>
    matFourierCoeff_orthPart_self ha
  obtain ⟨R, hR⟩ := exists_inv_sqrt (posDef_of_ae_conjTranspose_mul_self_eq hinv hY
    (by rw [matFourierCoeff_inv_mul_orthPart ha ha' hinv le_rfl, ite_eq_left rfl]) hD)
  obtain ⟨Ψ, hΨm, hΨu, hΨ⟩ := exists_unitary (stronglyMeasurable_orthPart ha) hD hR
  have hΨ2 (i j : n) : MemLp (fun t => Ψ t i j) 2 haarAddCircle :=
    MemLp.of_bound (hΨm i j).aestronglyMeasurable 1
      (ae_of_all _ fun t => entry_norm_bound_of_unitary (hΨu t) i j)
  have h1 (t : UnitAddCircle) : Ψ t * (Ψ t)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 (hΨu t)
  have h2 (t : UnitAddCircle) : (Ψ t)ᴴ * Ψ t = 1 := Matrix.mem_unitaryGroup_iff'.1 (hΨu t)
  -- `h = Ψᴴ a`, `h⁻¹ = a⁻¹ Ψ`
  have hi (t : UnitAddCircle) : ((Ψ t)ᴴ * a t)⁻¹ = (a t)⁻¹ * Ψ t := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (a t), Matrix.mul_nonsing_inv _ (hdet t),
      Matrix.one_mul, h2]
  refine ⟨Ψ, fun t => (Ψ t)ᴴ * a t, hΨm, hΨu, isHardyTwo_conjTranspose_mul ha hY hΨ2 hΨ fun _ =>
    matFourierCoeff_orthPart_mul ha, ?_,
    ae_of_all _ fun t => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]⟩
  simp only [hi]
  refine isHardyTwo_inv_mul hinv hY hΨ2 hΨ fun k hk => ?_
  rw [matFourierCoeff_inv_mul_orthPart ha ha' hinv hk.le, ite_eq_right hk.ne]

/-! ### Functions of `fᴴ f` -/

/-- `U diag (d) Uᴴ`. -/
private noncomputable def conjDiag (U : Matrix n n ℂ) (d : n → ℝ) : Matrix n n ℂ :=
  U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ

private theorem conjDiag_mul {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (d e : n → ℝ) :
    conjDiag U d * conjDiag U e = conjDiag U (d * e) := by
  have h : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  simp only [conjDiag, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ, h, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _)
    (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  simp only [Pi.mul_apply, Complex.ofReal_mul]

private theorem conjTranspose_conjDiag (U : Matrix n n ℂ) (d : n → ℝ) :
    (conjDiag U d)ᴴ = conjDiag U d := by
  rw [conjDiag, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  congr 3
  ext i
  simp

private theorem conjDiag_mul_eq_one {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    {d : n → ℝ} (hd : ∀ i, d i ≠ 0) : conjDiag U d * conjDiag U d⁻¹ = 1 := by
  have h : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have e : d * d⁻¹ = 1 := by
    ext i
    simp [hd i]
  rw [conjDiag_mul hU, e, conjDiag]
  simpa using h

private theorem isUnit_conjDiag {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) {d : n → ℝ}
    (hd : ∀ i, d i ≠ 0) : IsUnit (conjDiag U d) :=
  IsUnit.of_mul_eq_one _ (conjDiag_mul_eq_one hU hd)

/-- The Schatten norms of a matrix that is unitarily conjugate to `diag (d)`. -/
private theorem complexSchattenNorm_conjDiag {q : ℝ} (hq : 0 < q) {U V : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) {d : n → ℝ}
    (hd : ∀ i, 0 ≤ d i) : complexSchattenNorm (ENNReal.ofReal q) (Vᴴ * conjDiag U d * V) =
      (∑ i, d i ^ q) ^ (1 / q) := by
  have hVU : Vᴴ * U ∈ Matrix.unitaryGroup n ℂ := mul_mem (Unitary.star_mem hV) hU
  have e : Vᴴ * conjDiag U d * V =
      Vᴴ * U * Matrix.diagonal (fun i => (d i : ℂ)) * (Vᴴ * U)ᴴ := by
    rw [conjDiag, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [e, complexSchattenNorm_unitary_mul_diagonal_mul hq hVU hVU]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd _)]

/-- `fᴴ f = U diag (s_i²) Uᴴ` and `φ (fᴴ f) = U diag (φ (s_i²)) Uᴴ`. -/
private theorem exists_cfc_eq_conjDiag (F : Matrix n n ℂ) : ∃ U ∈ Matrix.unitaryGroup n ℂ,
    ∀ φ : ℝ → ℝ, cfc φ (Fᴴ * F) = conjDiag U fun i => φ (complexSingularValue F i ^ 2) := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self F
  refine ⟨hH.eigenvectorUnitary, hH.eigenvectorUnitary.2, fun φ => ?_⟩
  rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, conjDiag]
  congr 3
  ext i
  rw [complexSingularValue, Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg F i)]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The functional calculus of `fᴴ f` is continuous. -/
private theorem continuous_cfc_conjTranspose_mul_self {f : UnitAddCircle → Matrix n n ℂ}
    (hf : Continuous f) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous fun t => cfc φ ((f t)ᴴ * f t) :=
  (hf.matrix_conjTranspose.matrix_mul hf).cfc_of_mem_nhdsSet φ (s := Set.univ) Filter.univ_mem
    (fun t => (Matrix.isHermitian_conjTranspose_mul_self (f t)).isSelfAdjoint) hφ.continuousOn

private theorem complexSchattenNorm_eq_sum {p : ℝ} (hp : 0 < p) (F : Matrix n n ℂ) :
    complexSchattenNorm (ENNReal.ofReal p) F =
      (∑ i, complexSingularValue F i ^ p) ^ (1 / p) := by
  rw [complexSchattenNorm, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]

private theorem complexSchattenNorm_two_mul_sq {p : ℝ} (hp : 0 < p) (A : Matrix n n ℂ) :
    complexSchattenNorm (ENNReal.ofReal (2 * p)) A ^ 2 =
      complexSchattenNorm (ENNReal.ofReal p) (Aᴴ * A) := by
  rw [← complexSchattenNorm_conjTranspose_mul_self (by simp [hp])]
  congr 1
  rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_comm,
    ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

omit [DecidableEq n] in
/-- Minkowski's inequality in `ℓ^p`: `‖(s² + η²)^{1/2}‖_p ≤ ‖s‖_p + η n`. -/
private theorem sum_sqrt_rpow_le {p η : ℝ} (hp : 1 ≤ p) (hη : 0 ≤ η) {s : n → ℝ}
    (hs : ∀ i, 0 ≤ s i) : (∑ i, √(s i ^ 2 + η ^ 2) ^ p) ^ (1 / p) ≤
      (∑ i, s i ^ p) ^ (1 / p) + η * Fintype.card n := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hle (i : n) : √(s i ^ 2 + η ^ 2) ≤ s i + η := by
    rw [Real.sqrt_le_left (add_nonneg (hs i) hη)]
    nlinarith [mul_nonneg (hs i) hη]
  have hcard : (∑ _i : n, η ^ p) ^ (1 / p) ≤ η * Fintype.card n := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard' : (Fintype.card n : ℝ) ≤ (Fintype.card n : ℝ) ^ p := by
      rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
      · rw [h0, Nat.cast_zero]
        positivity
      · exact Real.self_le_rpow_of_one_le (by exact_mod_cast h0) hp
    calc (Fintype.card n * η ^ p) ^ (1 / p) ≤ ((η * Fintype.card n) ^ p) ^ (1 / p) := by
          rw [Real.mul_rpow hη (Nat.cast_nonneg _), mul_comm]
          gcongr
      _ = η * Fintype.card n := by
          rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne']
  calc (∑ i, √(s i ^ 2 + η ^ 2) ^ p) ^ (1 / p)
      ≤ (∑ i, (s i + η) ^ p) ^ (1 / p) := by
        refine Real.rpow_le_rpow (by positivity) (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (hle i) hp0.le
    _ ≤ (∑ i, s i ^ p) ^ (1 / p) + (∑ _i : n, η ^ p) ^ (1 / p) :=
        Real.Lp_add_le_of_nonneg _ hp (fun i _ => hs i) fun _ _ => hη
    _ ≤ _ := by gcongr

/-! ### The Riesz factorization -/

omit [DecidableEq n] in
/-- `H²` is stable under the multiplication by analytic polynomials. (With `h⁻¹ ∈ H²` this gives
`g = f h⁻¹ ∈ H²`; for a polynomial `f`, Proposition 3.3 of Bekjan–Xu is not needed.) -/
private theorem isHardyTwo_trigPoly_mul {c : ℤ →₀ Matrix n n ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k)
    {h : UnitAddCircle → Matrix n n ℂ} (hh : IsHardyTwo h) :
    IsHardyTwo fun t => trigPoly c t * h t :=
  ⟨memLp_continuous_matrix_mul (continuous_trigPoly_matrix c) hh.1,
    fun _ => matFourierCoeff_mul_of_neg (isHardyTwo_trigPoly hc) hh⟩

/-- `hᴴ h = a²`, so `‖h‖_{2p}² = ‖(s² + η²)^{1/2}‖_p ≤ ‖s‖_p + η n`. -/
private theorem norm_unitary_mul_conjDiag_sq_le {U Ψ : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hΨ : Ψ ∈ Matrix.unitaryGroup n ℂ) {η p : ℝ} (hη : 0 ≤ η)
    (hp : 1 ≤ p) {s : n → ℝ} (hs : ∀ i, 0 ≤ s i) :
    complexSchattenNorm (ENNReal.ofReal (2 * p))
        (Ψᴴ * conjDiag U fun i => √√(s i ^ 2 + η ^ 2)) ^ 2 ≤
      (∑ i, s i ^ p) ^ (1 / p) + η * Fintype.card n := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hΨ1 : Ψ * Ψᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hΨ
  have e : (fun i => √√(s i ^ 2 + η ^ 2)) * (fun i => √√(s i ^ 2 + η ^ 2)) =
      fun i => √(s i ^ 2 + η ^ 2) := by
    ext i
    exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hHH : (Ψᴴ * conjDiag U fun i => √√(s i ^ 2 + η ^ 2))ᴴ *
      (Ψᴴ * conjDiag U fun i => √√(s i ^ 2 + η ^ 2)) =
      (1 : Matrix n n ℂ)ᴴ * conjDiag U (fun i => √(s i ^ 2 + η ^ 2)) * 1 := by
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, conjTranspose_conjDiag, Matrix.mul_assoc,
      ← Matrix.mul_assoc Ψ, hΨ1, Matrix.one_mul, conjDiag_mul hU, e]
  rw [complexSchattenNorm_two_mul_sq hp0, hHH,
    complexSchattenNorm_conjDiag hp0 hU (one_mem _) fun i => Real.sqrt_nonneg _]
  exact sum_sqrt_rpow_le hp hη hs

/-- `s² / (s² + η²)^{1/2} ≤ s`. -/
private theorem inv_mul_sq_mul_inv_le {s η : ℝ} (hs : 0 ≤ s) (hη : 0 < η) :
    (√√(s ^ 2 + η ^ 2))⁻¹ * s ^ 2 * (√√(s ^ 2 + η ^ 2))⁻¹ ≤ s := by
  have h1 : √√(s ^ 2 + η ^ 2) * √√(s ^ 2 + η ^ 2) = √(s ^ 2 + η ^ 2) :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have h2 : s ≤ √(s ^ 2 + η ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h3 : 0 < √(s ^ 2 + η ^ 2) := Real.sqrt_pos.2 (by positivity)
  calc (√√(s ^ 2 + η ^ 2))⁻¹ * s ^ 2 * (√√(s ^ 2 + η ^ 2))⁻¹
      = s ^ 2 / (√√(s ^ 2 + η ^ 2) * √√(s ^ 2 + η ^ 2)) := by
        rw [div_eq_mul_inv, mul_inv]
        ring
    _ ≤ s := by
        rw [h1, div_le_iff₀ h3]
        exact (sq s).trans_le (mul_le_mul_of_nonneg_left h2 hs)

/-- `gᴴ g = Ψᴴ a⁻¹ fᴴ f a⁻¹ Ψ`, so `‖g‖_{2p}² = ‖s² / (s² + η²)^{1/2}‖_p ≤ ‖s‖_p`. -/
private theorem norm_mul_conjDiag_mul_unitary_sq_le {F U Ψ : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hΨ : Ψ ∈ Matrix.unitaryGroup n ℂ) {η p : ℝ} (hη : 0 < η)
    (hp : 1 ≤ p) {s : n → ℝ} (hs : ∀ i, 0 ≤ s i) (hF : Fᴴ * F = conjDiag U fun i => s i ^ 2) :
    complexSchattenNorm (ENNReal.ofReal (2 * p))
        (F * (conjDiag U (fun i => (√√(s i ^ 2 + η ^ 2))⁻¹) * Ψ)) ^ 2 ≤
      (∑ i, s i ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hG : (F * (conjDiag U (fun i => (√√(s i ^ 2 + η ^ 2))⁻¹) * Ψ))ᴴ *
      (F * (conjDiag U (fun i => (√√(s i ^ 2 + η ^ 2))⁻¹) * Ψ)) =
      Ψᴴ * conjDiag U (fun i =>
        (√√(s i ^ 2 + η ^ 2))⁻¹ * s i ^ 2 * (√√(s i ^ 2 + η ^ 2))⁻¹) * Ψ := by
    have e1 (A : Matrix n n ℂ) (hA : Aᴴ = A) :
        (F * (A * Ψ))ᴴ * (F * (A * Ψ)) = Ψᴴ * (A * (Fᴴ * F) * A) * Ψ := by
      simp only [Matrix.conjTranspose_mul, hA, Matrix.mul_assoc]
    rw [e1 _ (conjTranspose_conjDiag _ _), hF, conjDiag_mul hU, conjDiag_mul hU]
    rfl
  rw [complexSchattenNorm_two_mul_sq hp0, hG,
    complexSchattenNorm_conjDiag hp0 hU hΨ fun i => by positivity]
  refine Real.rpow_le_rpow (by positivity) (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  exact Real.rpow_le_rpow (by positivity) (inv_mul_sq_mul_inv_le (hs i) hη) hp0.le

/-- The pointwise part of Bekjan–Xu, Theorem 3.4: if `a = (fᴴ f + η²)^{1/4} = Ψ h` with `Ψ` unitary
and `g = f h⁻¹`, then `g h = f`, `‖g‖_{2p}² ≤ ‖f‖_p` and `‖h‖_{2p}² ≤ ‖f‖_p + η n`. -/
private theorem riesz_pointwise {F H Ψ : Matrix n n ℂ} {η : ℝ} (hη : 0 < η)
    (hΨ : Ψ ∈ Matrix.unitaryGroup n ℂ)
    (hH : cfc (fun s : ℝ => √√(s + η ^ 2)) (Fᴴ * F) = Ψ * H) :
    F = F * H⁻¹ * H ∧
      (∀ p : ℝ, 1 ≤ p → complexSchattenNorm (ENNReal.ofReal (2 * p)) (F * H⁻¹) ^ 2 ≤
        complexSchattenNorm (ENNReal.ofReal p) F) ∧
      ∀ p : ℝ, 1 ≤ p → complexSchattenNorm (ENNReal.ofReal (2 * p)) H ^ 2 ≤
        complexSchattenNorm (ENNReal.ofReal p) F + η * Fintype.card n := by
  obtain ⟨U, hU, hcfc⟩ := exists_cfc_eq_conjDiag F
  have hΨ1 : Ψ * Ψᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hΨ
  have hΨ2 : Ψᴴ * Ψ = 1 := Matrix.mem_unitaryGroup_iff'.1 hΨ
  have hs0 (i : n) : 0 ≤ complexSingularValue F i := Real.sqrt_nonneg _
  have hFF : Fᴴ * F = conjDiag U fun i => complexSingularValue F i ^ 2 := by
    have h1 := hcfc id
    rwa [cfc_id ℝ _ (Matrix.isHermitian_conjTranspose_mul_self F).isSelfAdjoint] at h1
  obtain ⟨d, hd⟩ : ∃ d : n → ℝ, d = fun i => √√(complexSingularValue F i ^ 2 + η ^ 2) := ⟨_, rfl⟩
  have hd0 (i : n) : d i ≠ 0 := by
    rw [hd]
    exact (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))).ne'
  have hA : conjDiag U d = Ψ * H := by
    rw [hd, ← hH, hcfc]
  have hinv : conjDiag U d * conjDiag U d⁻¹ = 1 := conjDiag_mul_eq_one hU hd0
  have hH' : H = Ψᴴ * conjDiag U d := by
    rw [hA, ← Matrix.mul_assoc, hΨ2, Matrix.one_mul]
  have hHinv : H⁻¹ = conjDiag U d⁻¹ * Ψ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hH', Matrix.mul_assoc, ← Matrix.mul_assoc (conjDiag U d), hinv, Matrix.one_mul, hΨ2]
  refine ⟨?_, fun p hp => ?_, fun p hp => ?_⟩
  · have h1 : H⁻¹ * H = 1 := by
      rw [hHinv, hH', Matrix.mul_assoc, ← Matrix.mul_assoc Ψ, hΨ1, Matrix.one_mul,
        mul_eq_one_comm.1 hinv]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · rw [hHinv, hd, complexSchattenNorm_eq_sum (one_pos.trans_le hp)]
    exact norm_mul_conjDiag_mul_unitary_sq_le hU hΨ hη hp hs0 hFF
  · rw [hH', hd, complexSchattenNorm_eq_sum (one_pos.trans_le hp)]
    exact norm_unitary_mul_conjDiag_sq_le hU hΨ hη.le hp hs0

/-- **Riesz factorization of analytic matrix polynomials** (Sarason (1967); Bekjan–Xu (2009),
Theorem 3.4, with pointwise bounds): `f = g h` almost everywhere, with `g, h ∈ H²`, and, for almost
every `t` and all `p ≥ 1`, `‖g (t)‖_{S_{2p}}² ≤ ‖f (t)‖_{S_p}` and
`‖h (t)‖_{S_{2p}}² ≤ ‖f (t)‖_{S_p} + δ`. -/
theorem exists_riesz_factorization {c : ℤ →₀ Matrix n n ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ g h : UnitAddCircle → Matrix n n ℂ, IsHardyTwo g ∧ IsHardyTwo h ∧
      (∀ᵐ t ∂haarAddCircle, trigPoly c t = g t * h t) ∧
      (∀ᵐ t ∂haarAddCircle, ∀ p : ℝ, 1 ≤ p →
        complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ≤
          complexSchattenNorm (ENNReal.ofReal p) (trigPoly c t)) ∧
      (∀ᵐ t ∂haarAddCircle, ∀ p : ℝ, 1 ≤ p →
        complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ≤
          complexSchattenNorm (ENNReal.ofReal p) (trigPoly c t) + δ) := by
  let η : ℝ := δ / (Fintype.card n + 1)
  have hη : 0 < η := by positivity
  have hηδ : η * Fintype.card n ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- `a = (fᴴ f + η²)^{1/4}`
  let a (t : UnitAddCircle) : Matrix n n ℂ :=
    cfc (fun s : ℝ => √√(s + η ^ 2)) ((trigPoly c t)ᴴ * trigPoly c t)
  have ha : Continuous a :=
    continuous_cfc_conjTranspose_mul_self (continuous_trigPoly_matrix c) (by fun_prop)
  have ha' (t : UnitAddCircle) : IsUnit (a t) := by
    obtain ⟨U, hU, hcfc⟩ := exists_cfc_eq_conjDiag (trigPoly c t)
    rw [show a t = _ from hcfc _]
    exact isUnit_conjDiag hU fun i => (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))).ne'
  obtain ⟨Ψ, h, -, hΨ, hh, hhinv, hfac⟩ := exists_szego_factorization ha ha'
  have key : ∀ᵐ t ∂haarAddCircle, _ := hfac.mono fun t ht => riesz_pointwise hη (hΨ t) ht
  refine ⟨fun t => trigPoly c t * (h t)⁻¹, h, isHardyTwo_trigPoly_mul hc hhinv, hh,
    key.mono fun t ht => ht.1, key.mono fun t ht => ht.2.1, key.mono fun t ht p hp => ?_⟩
  exact (ht.2.2 p hp).trans (by gcongr)

end VectorValuedHarmonicAnalysis
