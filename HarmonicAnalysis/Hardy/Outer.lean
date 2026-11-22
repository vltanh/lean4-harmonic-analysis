/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Hardy.FunctionalCalculus
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Outer functions and the factorization of `AᴴA`

Part of the theory of H. Helson and D. Lowdenslager, *Prediction theory and Fourier series in
several variables. II*, Acta Math. 106 (1961), 175–213, §§9–10, for functions on the circle with
values in the matrices of any shape. (Theorems 8, 12 and 13 of this article are in
`RangeFunction.lean`; the corollary of Theorem 10 and Theorem 11 are not included.) Some steps are
those of the first article with this title, Acta Math. 99 (1958), 165–202.

Helson and Lowdenslager consider products `W = A Aᴴ` and left-outer functions; transposing exchanges
them with the products `Aᴴ A` and the right-outer functions considered here, used, in the equivalent
form below, by D. Sarason, *Generalized interpolation in H^∞*, Trans. Amer. Math. Soc. 127 (1967),
179–203, §10. Moreover they work with the canonical process in `L² (W)`, which is multiplied by
`e_{-n}`, so that the manifolds `M_n` increase with `n` (p. 202); here this process is realized by
the columns of the functions `A e_k` in `L²`, and the manifolds `M_k` decrease.

* `IsOuter A`: `A ∈ H²`, and the closure in `L²` of the functions `A (1 + P)`, `P` an analytic
  trigonometric polynomial without constant term, contains a constant.
* `exists_innovation`: for `A` with entries in `L²` let `M_k` be the closed span of the columns of
  `A e_j`, `j ≥ k`. An orthonormal basis of the orthogonal complement of `M_1` in `M_0` (the
  innovation of the process) is a matrix-valued function `X` with `Xᴴ X = 1`; `Xᴴ A` is analytic,
  and the functions `A Q`, `Q` an analytic polynomial, approximate `X`. If `A ∈ H²`, the process has
  no remote past, `⋂ M_k = 0`, and `A = X (Xᴴ A)`.
* `isOuter_of_dense`: `A ∈ H²` is outer if the functions `A Q`, `Q` an analytic polynomial, are
  dense in `H²`.
* `IsOuter.range_eq` (Theorem 9): the range of an outer function is almost everywhere the range of
  its constant coefficient.
* `exists_isOuter`: if `A ∈ H²`, there is an outer function `B` whose constant coefficient is
  surjective, with at most as many rows as `A` has columns, such that `Bᴴ B = Aᴴ A`.
* `IsOuter.exists_tendsto_iff` (Theorem 10): the closure of `{A Q}`, `Q` an analytic polynomial, is
  the set of the functions of `H²` whose range is contained in that of `Â (0)`. So an outer function
  is outer in the sense of Sarason: its range is almost everywhere a fixed subspace `𝒲`, and the
  functions `A G`, `G` a vector-valued polynomial, are dense in `H² (𝒲)`. (The converse also holds;
  it is not used.)
* `IsOuter.isHardyTwo_of_bounded_mul`: if `B` is outer with surjective constant coefficient and `Q`
  is bounded, `Q B ∈ H²` implies `Q ∈ H²`.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped Matrix Topology

namespace HarmonicAnalysis

variable {l m n : Type*}

/-- A matrix polynomial with given columns. -/
private theorem exists_circPoly_columns [Finite l] (d : l → ℤ →₀ (n → ℂ)) :
    ∃ c : ℤ →₀ Matrix n l ℂ, (∀ k ∈ c.support, ∃ j, k ∈ (d j).support) ∧
      ∀ t i j, circPoly c t i j = circPoly (d j) t i := by
  classical
  cases nonempty_fintype l
  let U : Finset ℤ := Finset.univ.biUnion fun j => (d j).support
  let c : ℤ →₀ Matrix n l ℂ := Finsupp.onFinset U (fun k => Matrix.of fun i j => d j k i)
    fun k hk => by
      by_contra h
      refine hk ?_
      ext i j
      have hj : k ∉ (d j).support := fun hj => h (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hj⟩)
      rw [Matrix.of_apply, Finsupp.notMem_support_iff.1 hj]
      rfl
  refine ⟨c, fun k hk => ?_, fun t i j => ?_⟩
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (Finsupp.support_onFinset_subset hk)
    exact ⟨j, hj⟩
  · have h1 : circPoly c t = ∑ k ∈ U, fourier k t • c k :=
      Finsupp.sum_of_support_subset _ Finsupp.support_onFinset_subset _ fun _ _ => smul_zero _
    have h2 : circPoly (d j) t = ∑ k ∈ U, fourier k t • d j k :=
      Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun j => (d j).support)
        (Finset.mem_univ j)) _ fun _ _ => smul_zero _
    rw [h1, h2, Matrix.sum_apply, Finset.sum_apply]
    rfl

/-! ### Matrices -/

/-- The entries of `Xᴴ` are bounded by `1` if the columns of `X` are orthonormal. -/
private theorem norm_conjTranspose_apply_le_one [Fintype m] [DecidableEq l]
    {X : UnitAddCircle → Matrix m l ℂ} (hX : ∀ᵐ t ∂haarAddCircle, (X t)ᴴ * X t = 1) :
    ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖(X t)ᴴ i j‖ ≤ 1 := by
  filter_upwards [hX] with t ht j i
  rw [Matrix.conjTranspose_apply, norm_star]
  exact norm_apply_le_one_of_conjTranspose_mul_self ht i j

/-- A matrix over a field has an inner inverse. -/
private theorem exists_mul_mul_eq [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    ∃ D : Matrix n m ℂ, M * D * M = M := by
  classical
  obtain ⟨s, hs⟩ := M.mulVecLin.rangeRestrict.exists_rightInverse_of_surjective
    M.mulVecLin.range_rangeRestrict
  obtain ⟨g, hg⟩ := s.exists_extend
  refine ⟨LinearMap.toMatrix' g, Matrix.ext_iff_mulVec.2 fun v => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  have h1 : g (M.mulVecLin v) = s (M.mulVecLin.rangeRestrict v) :=
    LinearMap.congr_fun hg (M.mulVecLin.rangeRestrict v)
  have h2 := LinearMap.congr_fun hs (M.mulVecLin.rangeRestrict v)
  have h3 := congrArg Subtype.val h2
  rw [Matrix.mulVecLin_apply] at h1
  rw [h1]
  exact h3

/-- The range of a limit of matrices `M Q_N` is contained in that of `M`. -/
private theorem range_le_of_tendsto [Fintype n] [Fintype l] {M : Matrix m n ℂ}
    {Q : ℕ → Matrix n l ℂ} {F : Matrix m l ℂ} (h : Tendsto (fun N => M * Q N) atTop (𝓝 F)) :
    LinearMap.range F.mulVecLin ≤ LinearMap.range M.mulVecLin := by
  rintro _ ⟨v, rfl⟩
  have h1 : Continuous fun B : Matrix m l ℂ => B.mulVec v :=
    continuous_id.matrix_mulVec continuous_const
  refine (LinearMap.range M.mulVecLin).closed_of_finiteDimensional.mem_of_tendsto
    ((h1.tendsto F).comp h) (Eventually.of_forall fun N => ?_)
  exact ⟨(Q N).mulVec v, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]; rfl⟩

/-- `F = M D F` if `M D M = M` and the range of `F` is contained in that of `M`. -/
private theorem mul_mul_eq_of_range_le [Fintype m] [Fintype n] [Fintype l] {M : Matrix m n ℂ}
    {D : Matrix n m ℂ} (hD : M * D * M = M) {F : Matrix m l ℂ}
    (h : LinearMap.range F.mulVecLin ≤ LinearMap.range M.mulVecLin) : M * (D * F) = F := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨u, hu⟩ := h ⟨v, rfl⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hu
  rw [← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← hu, Matrix.mulVec_mulVec, hD]

/-! ### The Hilbert space of the columns -/

section Columns

variable [Fintype m]

/-- The Hilbert space of the square-summable functions with values in the column vectors. -/
private abbrev ColLp (m : Type*) [Fintype m] : Type _ :=
  Lp (EuclideanSpace ℂ m) 2 (haarAddCircle (T := 1))

/-- Multiplication by `e_k`, an isometry. -/
private noncomputable def shift (k : ℤ) : ColLp m →ₗᵢ[ℂ] ColLp m where
  toFun f := (memLp_fourier_smul k (Lp.memLp f)).toLp
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_fourier_smul k (Lp.memLp (f + g))).coeFn_toLp,
      Lp.coeFn_add f g, (memLp_fourier_smul k (Lp.memLp f)).coeFn_toLp,
      (memLp_fourier_smul k (Lp.memLp g)).coeFn_toLp,
      Lp.coeFn_add (memLp_fourier_smul k (Lp.memLp f)).toLp
        (memLp_fourier_smul k (Lp.memLp g)).toLp] with t h1 h2 h3 h4 h5
    rw [h1, h5, Pi.add_apply, h3, h4, h2, Pi.add_apply, smul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_fourier_smul k (Lp.memLp (c • f))).coeFn_toLp,
      Lp.coeFn_smul c f, (memLp_fourier_smul k (Lp.memLp f)).coeFn_toLp,
      Lp.coeFn_smul c (memLp_fourier_smul k (Lp.memLp f)).toLp] with t h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h3, h2, Pi.smul_apply, smul_comm]
  norm_map' f := by
    change ‖(memLp_fourier_smul k (Lp.memLp f)).toLp‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae (memLp_fourier_smul k (Lp.memLp f)).aestronglyMeasurable
      (Lp.aestronglyMeasurable f) (ae_of_all _ fun t => ?_)
    rw [norm_smul, norm_fourier_apply_eq_one, one_mul]

private theorem coeFn_shift (k : ℤ) (f : ColLp m) :
    shift k f =ᵐ[haarAddCircle] fun t => fourier k t • f t :=
  (memLp_fourier_smul k (Lp.memLp f)).coeFn_toLp

private theorem shift_shift (k r : ℤ) (f : ColLp m) : shift k (shift r f) = shift (k + r) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_shift k (shift r f), coeFn_shift r f, coeFn_shift (k + r) f] with t h1 h2 h3
  rw [h1, h2, h3, smul_smul, fourier_add]

private theorem shift_zero (f : ColLp m) : shift 0 f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_shift 0 f] with t h1
  rw [h1, fourier_zero, one_smul]

/-- The inner products with `e_k f` are the Fourier coefficients of the pointwise inner products
with `f`. -/
private theorem inner_shift_left (k : ℤ) (f g : ColLp m) :
    inner ℂ (shift k f) g = fourierCoeff (fun t => inner ℂ (f t) (g t)) k := by
  rw [L2.inner_def, fourierCoeff]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_shift k f] with t h1
  rw [h1, inner_smul_left, ← fourier_neg, smul_eq_mul]

/-- The adjoint of the multiplication by `e_k` is the multiplication by `e_{-k}`. -/
private theorem inner_shift_comm (k : ℤ) (f g : ColLp m) :
    inner ℂ (shift k f) g = inner ℂ f (shift (-k) g) := by
  rw [← LinearIsometry.inner_map_map (shift (-k)) (shift k f) g, shift_shift, neg_add_cancel,
    shift_zero]

/-- `M_r`, the closed span of the functions `e_k a_j`, `k ≥ r`. (Helson–Lowdenslager (1961), p. 202,
take the index with the opposite sign, so that the manifolds increase.) -/
private noncomputable def past (a : n → ColLp m) (r : ℤ) : Submodule ℂ (ColLp m) :=
  (Submodule.span ℂ {f | ∃ k : ℤ, r ≤ k ∧ ∃ j, f = shift k (a j)}).topologicalClosure

private theorem completeSpace_past (a : n → ColLp m) (r : ℤ) : CompleteSpace (past a r) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

attribute [local instance] completeSpace_past

private theorem shift_mem_past (a : n → ColLp m) {r k : ℤ} (hk : r ≤ k) (j : n) :
    shift k (a j) ∈ past a r :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, hk, j, rfl⟩)

/-- `M_r` is the smallest closed subspace that contains the `e_k a_j`, `k ≥ r`. -/
private theorem past_le {a : n → ColLp m} {r : ℤ} {K : Submodule ℂ (ColLp m)}
    (hK : IsClosed (K : Set (ColLp m))) (h : ∀ k : ℤ, r ≤ k → ∀ j, shift k (a j) ∈ K) :
    past a r ≤ K := by
  refine Submodule.topologicalClosure_minimal _ ?_ hK
  rw [Submodule.span_le]
  rintro _ ⟨k, hk, j, rfl⟩
  exact h k hk j

private theorem past_anti (a : n → ColLp m) {r s : ℤ} (h : r ≤ s) : past a s ≤ past a r :=
  past_le (Submodule.isClosed_topologicalClosure _) fun _ hk j => shift_mem_past a (h.trans hk) j

/-- `e_k M_r ⊆ M_{r + k}`. -/
private theorem shift_mem_past_add {a : n → ColLp m} {r : ℤ} (k : ℤ) {f : ColLp m}
    (hf : f ∈ past a r) : shift k f ∈ past a (r + k) := by
  have hle : past a r ≤ (past a (r + k)).comap (shift k).toLinearMap := by
    refine past_le ?_ fun s hs j => ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage (shift k).continuous
    · change shift k (shift s (a j)) ∈ past a (r + k)
      rw [shift_shift]
      exact shift_mem_past a (by omega) j
  exact hle hf

/-- A vector orthogonal to the functions `e_k a_j`, `k ≥ r`, is orthogonal to `M_r`. -/
private theorem inner_eq_zero_of_mem_past {a : n → ColLp m} {r : ℤ} {w f : ColLp m}
    (hw : ∀ k : ℤ, r ≤ k → ∀ j, inner ℂ w (shift k (a j)) = 0) (hf : f ∈ past a r) :
    inner ℂ w f = 0 := by
  have hle : past a r ≤ LinearMap.ker (innerSL ℂ w).toLinearMap :=
    past_le (innerSL ℂ w).isClosed_ker hw
  exact hle hf

/-! ### The innovation -/

/-- The innovation `R = M_0 ⊖ M_1`. -/
private noncomputable def innovation (a : n → ColLp m) : Submodule ℂ (ColLp m) :=
  past a 0 ⊓ (past a 1)ᗮ

private theorem mem_past_zero (a : n → ColLp m) (j : n) : a j ∈ past a 0 := by
  simpa only [shift_zero] using shift_mem_past a (le_refl 0) j

/-- The component orthogonal to `M_1` of an element of `M_0` is in the innovation. -/
private theorem sub_starProjection_mem_innovation {a : n → ColLp m} {u : ColLp m}
    (hu : u ∈ past a 0) : u - (past a 1).starProjection u ∈ innovation a :=
  ⟨Submodule.sub_mem _ hu (past_anti a (by norm_num) (Submodule.starProjection_apply_mem _ _)),
    Submodule.sub_starProjection_mem_orthogonal _⟩

/-- Helson–Lowdenslager (1961), p. 202: the dimension of the innovation is "evidently" at most the
number of the `a_j`, because it is spanned by their components orthogonal to `M_1`: if `P` is the
projection onto `M_1`, the continuous map `1 - P` maps `a_j` to `a_j - P a_j`, and `e_k a_j` to `0`
for `k ≥ 1`, hence `M_0` into the span of the `a_j - P a_j`; and it fixes the innovation. -/
private theorem innovation_eq_span [Finite n] (a : n → ColLp m) :
    innovation a = Submodule.span ℂ (Set.range fun j => a j - (past a 1).starProjection (a j)) := by
  apply le_antisymm
  · set G := Submodule.span ℂ (Set.range fun j => a j - (past a 1).starProjection (a j))
    have : FiniteDimensional ℂ G := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    let Q : ColLp m →L[ℂ] ColLp m := ContinuousLinearMap.id ℂ _ - (past a 1).starProjection
    have hle : past a 0 ≤ G.comap Q.toLinearMap := by
      refine past_le (G.closed_of_finiteDimensional.preimage Q.continuous) fun k hk j => ?_
      change shift k (a j) - (past a 1).starProjection (shift k (a j)) ∈ G
      rcases hk.eq_or_lt with rfl | hk
      · rw [shift_zero]
        exact Submodule.subset_span ⟨j, rfl⟩
      · have h1 : shift k (a j) ∈ past a 1 := shift_mem_past a hk j
        rw [Submodule.starProjection_eq_self_iff.2 h1, sub_self]
        exact Submodule.zero_mem _
    intro x hx
    have h1 : x - (past a 1).starProjection x ∈ G := hle hx.1
    rwa [(Submodule.starProjection_apply_eq_zero_iff _).2 hx.2, sub_zero] at h1
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact sub_starProjection_mem_innovation (mem_past_zero a j)

/-- An orthonormal basis of the innovation, whose dimension is at most the number of the `a_j`. -/
private theorem exists_orthonormal_innovation [Fintype n] (a : n → ColLp m) :
    ∃ q : ℕ, q ≤ Fintype.card n ∧ ∃ x : Fin q → ColLp m, Orthonormal ℂ x ∧
      (∀ i, x i ∈ innovation a) ∧ ∀ v ∈ innovation a, ∑ i, inner ℂ (x i) v • x i = v := by
  have hfin : FiniteDimensional ℂ (innovation a) := by
    rw [innovation_eq_span]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let b := stdOrthonormalBasis ℂ (innovation a)
  refine ⟨Module.finrank ℂ (innovation a), ?_, fun i => (b i : ColLp m), ?_, fun i => (b i).2,
    fun v hv => ?_⟩
  · rw [innovation_eq_span]
    exact finrank_range_le_card _
  · exact b.orthonormal.comp_linearIsometry (innovation a).subtypeₗᵢ
  · have h1 := congrArg (innovation a).subtype (b.sum_repr' ⟨v, hv⟩)
    rw [map_sum] at h1
    exact h1

/-! ### Families of columns and matrix-valued functions -/

/-- The matrix-valued function with the columns `a_j`. -/
private noncomputable def toMat (a : n → ColLp m) (t : UnitAddCircle) : Matrix m n ℂ :=
  Matrix.of fun i j => (a j t).ofLp i

private theorem memLp_toMat (a : n → ColLp m) (i : m) (j : n) :
    MemLp (fun t => toMat a t i j) 2 haarAddCircle :=
  (Lp.memLp (a j)).eval_piLp i

/-- A matrix-valued function with entries in `L²` is given by its columns. -/
private theorem exists_toMat [Finite n] {A : UnitAddCircle → Matrix m n ℂ}
    (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle) :
    ∃ a : n → ColLp m, ∀ᵐ t ∂haarAddCircle, toMat a t = A t := by
  have h (j : n) : MemLp (fun t => (WithLp.toLp 2 fun i => A t i j : EuclideanSpace ℂ m)) 2
      haarAddCircle := MemLp.of_eval_piLp fun i => hA i j
  refine ⟨fun j => (h j).toLp, ?_⟩
  have h1 := ae_all_iff.2 fun j => (h j).coeFn_toLp
  filter_upwards [h1] with t ht
  ext i j
  rw [toMat, Matrix.of_apply, ht j]

/-- The entries of `aᴴ b` are the pointwise inner products of the columns. -/
private theorem conjTranspose_toMat_mul_apply (a : l → ColLp m) (b : n → ColLp m)
    (t : UnitAddCircle) (i : l) (j : n) :
    ((toMat a t)ᴴ * toMat b t) i j = inner ℂ (a i t) (b j t) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- The Fourier coefficients of `aᴴ b` are the inner products of the `e_k a_i` and the `b_j`. -/
private theorem matFourierCoeff_conjTranspose_toMat_mul (a : l → ColLp m) (b : n → ColLp m)
    (k : ℤ) (i : l) (j : n) :
    matFourierCoeff (fun t => (toMat a t)ᴴ * toMat b t) k i j = inner ℂ (shift k (a i)) (b j) := by
  rw [inner_shift_left, matFourierCoeff, Matrix.of_apply]
  simp only [conjTranspose_toMat_mul_apply]

/-- Convergence of the columns in `L²` implies convergence of the matrix-valued functions. -/
private theorem tendstoLTwo_toMat {F : ℕ → l → ColLp m} {f : l → ColLp m}
    (h : ∀ j, Tendsto (fun N => F N j) atTop (𝓝 (f j))) :
    TendstoLTwo (fun N => toMat (F N)) (toMat f) := by
  intro i j
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 (h j)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
    fun N => ?_
  refine eLpNorm_mono ((memLp_toMat (F N) i j).sub (memLp_toMat f i j)).aestronglyMeasurable
    fun t => ?_
  exact PiLp.norm_apply_le (F N j t - f j t) i

/-! ### The past and the polynomials -/

/-- The linear combinations of the `e_k a_j`, `k ≥ r`, are products of `a` and polynomials with
coefficients of order `≥ r`. -/
private theorem exists_circPoly_of_mem_span [Fintype n] {a : n → ColLp m} {r : ℤ} {y : ColLp m}
    (hy : y ∈ Submodule.span ℂ {f | ∃ k : ℤ, r ≤ k ∧ ∃ j, f = shift k (a j)}) :
    ∃ d : ℤ →₀ (n → ℂ), (∀ k < r, d k = 0) ∧
      ∀ᵐ t ∂haarAddCircle, (y t).ofLp = (toMat a t).mulVec (circPoly d t) := by
  classical
  induction hy using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, hk, j, rfl⟩ := hf
    refine ⟨Finsupp.single k (Pi.single j 1), fun s hs => ?_, ?_⟩
    · exact Finsupp.single_eq_of_ne (by omega)
    · filter_upwards [coeFn_shift k (a j)] with t ht
      rw [ht, circPoly_single, Matrix.mulVec_smul, Matrix.mulVec_single_one]
      rfl
  | zero =>
    refine ⟨0, fun s _ => rfl, ?_⟩
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℂ m) 2 (haarAddCircle (T := 1))] with t ht
    rw [ht, circPoly_zero, Matrix.mulVec_zero]
    rfl
  | add f g _ _ hf hg =>
    obtain ⟨d, hd, hfd⟩ := hf
    obtain ⟨e, he, hge⟩ := hg
    refine ⟨d + e, fun s hs => ?_, ?_⟩
    · rw [Finsupp.add_apply, hd s hs, he s hs, add_zero]
    · filter_upwards [Lp.coeFn_add f g, hfd, hge] with t h1 h2 h3
      rw [h1, circPoly_add, Matrix.mulVec_add, ← h2, ← h3]
      rfl
  | smul z f _ hf =>
    obtain ⟨d, hd, hfd⟩ := hf
    refine ⟨z • d, fun s hs => ?_, ?_⟩
    · rw [Finsupp.smul_apply, hd s hs, smul_zero]
    · filter_upwards [Lp.coeFn_smul z f, hfd] with t h1 h2
      rw [h1, circPoly_smul, Matrix.mulVec_smul, ← h2]
      rfl

/-- If the columns of `f` are in `M_r`, there are polynomials `c_N` with coefficients of order `≥ r`
such that `a c_N → f` in `L²`. -/
private theorem exists_tendsto_of_mem_past [Fintype n] [Finite l] {a : n → ColLp m} {r : ℤ}
    {f : l → ColLp m} (hf : ∀ j, f j ∈ past a r) :
    ∃ c : ℕ → ℤ →₀ Matrix n l ℂ, (∀ N, ∀ k ∈ (c N).support, r ≤ k) ∧
      TendstoLTwo (fun N t => toMat a t * circPoly (c N) t) (toMat f) := by
  have h1 (j : l) := mem_closure_iff_seq_limit.1 (hf j)
  choose y hy hlim using h1
  have h2 (N : ℕ) (j : l) := exists_circPoly_of_mem_span (hy j N)
  choose d hd hyd using h2
  have h3 (N : ℕ) := exists_circPoly_columns (d N)
  choose c hc hcd using h3
  refine ⟨c, fun N k hk => ?_, fun i j => ?_⟩
  · obtain ⟨j, hj⟩ := hc N k hk
    by_contra hlt
    exact Finsupp.mem_support_iff.1 hj (hd N j k (by omega))
  · refine (tendstoLTwo_toMat (F := fun N j => y j N) hlim i j).congr fun N => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hyd N j] with t ht
    have h4 : toMat (fun j => y j N) t i j = (y j N t).ofLp i := rfl
    have h5 : (fun o => circPoly (c N) t o j) = circPoly (d N j) t := funext fun o => hcd N t o j
    rw [h4, ht, ← h5]
    rfl

/-! ### The innovation as a matrix-valued function -/

/-- Helson–Lowdenslager (1961), p. 202, "The subspaces `R_n` are mutually perpendicular" (the
analogue of (1958), (51) and (52)): the functions `e_k x`, `k ≠ 0`, are orthogonal to the innovation
if `x` is in it. -/
private theorem inner_shift_innovation {a : n → ColLp m} {x y : ColLp m} (hx : x ∈ innovation a)
    (hy : y ∈ innovation a) {k : ℤ} (hk : k ≠ 0) : inner ℂ (shift k x) y = 0 := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · rw [inner_shift_comm]
    exact Submodule.inner_left_of_mem_orthogonal
      (past_anti a (by omega) (shift_mem_past_add (-k) hy.1)) hx.2
  · exact Submodule.inner_right_of_mem_orthogonal
      (past_anti a (by omega) (shift_mem_past_add k hx.1)) hy.2

/-- Helson–Lowdenslager (1958), (54) and (64): an orthonormal basis of the innovation is orthonormal
at almost every point. -/
private theorem conjTranspose_mul_self_eq_one [Finite l] [DecidableEq l] {a : n → ColLp m}
    {x : l → ColLp m} (hx : Orthonormal ℂ x) (hxa : ∀ i, x i ∈ innovation a) :
    ∀ᵐ t ∂haarAddCircle, (toMat x t)ᴴ * toMat x t = 1 := by
  have key : ∀ᵐ t ∂haarAddCircle, ∀ i j, ((toMat x t)ᴴ * toMat x t) i j =
      (1 : Matrix l l ℂ) i j := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    have h1 (k : ℤ) : fourierCoeff (fun t => ((toMat x t)ᴴ * toMat x t) i j) k =
        inner ℂ (shift k (x i)) (x j) := matFourierCoeff_conjTranspose_toMat_mul x x k i j
    have h2 := ae_eq_const_of_fourierCoeff_eq_zero
      (integrable_conjTranspose_mul_self (memLp_toMat x) i j)
      fun k hk => by rw [h1, inner_shift_innovation (hxa i) (hxa j) hk]
    rw [h1, shift_zero, orthonormal_iff_ite.1 hx] at h2
    filter_upwards [h2] with t ht
    rw [ht, Matrix.one_apply]
  filter_upwards [key] with t ht
  ext i j
  exact ht i j

/-- Helson–Lowdenslager (1958), (66) and (67): `xᴴ a` is analytic, because the innovation is
orthogonal to the `e_k a_j`, `k ≥ 1`; (1961), p. 202, "The sum contains only terms with `i ≥ 0`". -/
private theorem isHardyTwo_conjTranspose_toMat_mul [Finite l] {a : n → ColLp m}
    {x : l → ColLp m} (hx : Orthonormal ℂ x) (hxa : ∀ i, x i ∈ innovation a) :
    IsHardyTwo fun t => (toMat x t)ᴴ * toMat a t := by
  classical
  refine ⟨memLp_bounded_mul (fun i j => (memLp_toMat x j i).star.aestronglyMeasurable)
    (norm_conjTranspose_apply_le_one (conjTranspose_mul_self_eq_one hx hxa)) (memLp_toMat a),
    fun k hk => ?_⟩
  ext i j
  rw [matFourierCoeff_conjTranspose_toMat_mul, inner_shift_comm]
  exact Submodule.inner_left_of_mem_orthogonal (shift_mem_past a (by omega) j) (hxa i).2

/-- `(x, u - P u) = (x, u)` for `x` in the innovation, which is orthogonal to `M_1`; `P` is the
projection onto `M_1`. -/
private theorem inner_sub_starProjection {a : n → ColLp m} {x : ColLp m} (hx : x ∈ innovation a)
    (u : ColLp m) : inner ℂ x (u - (past a 1).starProjection u) = inner ℂ x u := by
  rw [inner_sub_right, Submodule.inner_left_of_mem_orthogonal
    (Submodule.starProjection_apply_mem _ _) hx.2, sub_zero]

/-- The constant coefficient of `xᴴ a` is the matrix of the inner products `(x_i, a_j)`. -/
private theorem matFourierCoeff_zero_conjTranspose_toMat_mul (a : n → ColLp m) (x : l → ColLp m)
    (i : l) (j : n) :
    matFourierCoeff (fun t => (toMat x t)ᴴ * toMat a t) 0 i j = inner ℂ (x i) (a j) := by
  rw [matFourierCoeff_conjTranspose_toMat_mul, shift_zero]

/-- The component of `a` orthogonal to `M_1` is `x B₀`, where `x` is an orthonormal basis of the
innovation and `B₀` the constant coefficient of `xᴴ a`. -/
private theorem toMat_sub_starProjection [Finite n] [Fintype l] {a : n → ColLp m} {x : l → ColLp m}
    (hxa : ∀ i, x i ∈ innovation a) (hx : ∀ v ∈ innovation a, ∑ i, inner ℂ (x i) v • x i = v) :
    ∀ᵐ t ∂haarAddCircle, toMat a t - toMat (fun j => (past a 1).starProjection (a j)) t =
      toMat x t * matFourierCoeff (fun t => (toMat x t)ᴴ * toMat a t) 0 := by
  have key : ∀ᵐ t ∂haarAddCircle, ∀ j, a j t - (past a 1).starProjection (a j) t =
      ∑ i, inner ℂ (x i) (a j) • x i t := by
    refine ae_all_iff.2 fun j => ?_
    have h1 := hx _ (sub_starProjection_mem_innovation (mem_past_zero a j))
    simp only [inner_sub_starProjection (hxa _)] at h1
    have h2 : ∀ᵐ t ∂haarAddCircle, ∀ i, (inner ℂ (x i) (a j) • x i : ColLp m) t =
        inner ℂ (x i) (a j) • x i t := ae_all_iff.2 fun i => Lp.coeFn_smul _ _
    filter_upwards [Lp.coeFn_sub (a j) ((past a 1).starProjection (a j)), h2,
      Lp.coeFn_fun_finsetSum (μ := haarAddCircle) Finset.univ
        fun i => (inner ℂ (x i) (a j) • x i : ColLp m)] with t h3 h4 h5
    rw [← Pi.sub_apply, ← h3, ← h1, h5]
    exact Finset.sum_congr rfl fun i _ => h4 i
  filter_upwards [key] with t ht
  ext i j
  rw [Matrix.mul_apply]
  simp only [matFourierCoeff_zero_conjTranspose_toMat_mul]
  have h1 := congrArg (fun v : EuclideanSpace ℂ m => v.ofLp i) (ht j)
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at h1
  refine Eq.trans h1 (Finset.sum_congr rfl fun o _ => mul_comm _ _)

/-- Helson–Lowdenslager (1958), pp. 187 and 190 ("Let `I + H` be the unique element of minimal norm
in the closure of this set"): the component `x B₀` of `a` orthogonal to `M_1`, where `B₀` is the
constant coefficient of `xᴴ a`, is approximated by functions `a (1 + P)`. -/
private theorem exists_tendsto_innovation [Fintype n] [DecidableEq n] [Fintype l] {a : n → ColLp m}
    {x : l → ColLp m} (hxa : ∀ i, x i ∈ innovation a)
    (hx : ∀ v ∈ innovation a, ∑ i, inner ℂ (x i) v • x i = v) :
    ∃ c : ℕ → ℤ →₀ Matrix n n ℂ, (∀ N, ∀ k ∈ (c N).support, 0 < k) ∧
      TendstoLTwo (fun N t => toMat a t * (1 + circPoly (c N) t))
        fun t => toMat x t * matFourierCoeff (fun s => (toMat x s)ᴴ * toMat a s) 0 := by
  obtain ⟨c, hc, hlim⟩ := exists_tendsto_of_mem_past
    (f := fun j => (past a 1).starProjection (a j)) (r := 1)
    fun j => Submodule.starProjection_apply_mem (past a 1) (a j)
  refine ⟨fun N => -c N, fun N k hk => ?_, fun i j => (hlim i j).congr fun N => ?_⟩
  · rw [Finsupp.support_neg] at hk
    exact hc N k hk
  · rw [← eLpNorm_neg]
    refine eLpNorm_congr_ae ?_
    filter_upwards [toMat_sub_starProjection hxa hx] with t ht
    have h1 : circPoly (-c N) t = -circPoly (c N) t := by
      rw [← neg_one_smul ℂ (c N), circPoly_smul, neg_one_smul]
    rw [h1, Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, ← ht]
    simp only [Pi.neg_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply]
    ring

/-! ### The remote past -/

/-- The constant function equal to the `i`-th unit vector. -/
private noncomputable def unitLp [DecidableEq m] (i : m) : ColLp m :=
  (memLp_const (EuclideanSpace.single i (1 : ℂ))).toLp

/-- The Fourier coefficients of the components of `f` are inner products. -/
private theorem inner_shift_unitLp [DecidableEq m] (k : ℤ) (i : m) (f : ColLp m) :
    inner ℂ (shift k (unitLp i)) f = fourierCoeff (fun t => (f t).ofLp i) k := by
  rw [inner_shift_left]
  refine congrFun (fourierCoeff_congr_ae ?_) k
  filter_upwards [(memLp_const (μ := haarAddCircle) (p := 2)
    (EuclideanSpace.single i (1 : ℂ))).coeFn_toLp] with t ht
  rw [unitLp, ht, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- If the `a_j` are analytic, the Fourier coefficients of order `< r` of the elements of `M_r`
vanish. -/
private theorem inner_shift_unitLp_of_mem_past [DecidableEq m] {a : n → ColLp m}
    (ha : IsHardyTwo (toMat a)) {r : ℤ} {f : ColLp m} (hf : f ∈ past a r) {k : ℤ} (hk : k < r)
    (i : m) : inner ℂ (shift k (unitLp i)) f = 0 := by
  refine inner_eq_zero_of_mem_past (fun s hs j => ?_) hf
  have h1 : fourierCoeff (fun t => (a j t).ofLp i) (k - s) = 0 :=
    congrFun (congrFun (ha.2 (k - s) (by omega)) i) j
  rw [inner_shift_comm, shift_shift, neg_add_eq_sub, ← neg_sub k s, ← inner_shift_comm,
    inner_shift_unitLp, h1]

/-- Helson–Lowdenslager (1961), p. 202: if the `a_j` are analytic, there is no remote past. -/
private theorem eq_zero_of_forall_mem_past {a : n → ColLp m} (ha : IsHardyTwo (toMat a))
    {f : ColLp m} (hf : ∀ p : ℕ, f ∈ past a p) : f = 0 := by
  classical
  have h1 := ae_eq_zero_of_matFourierCoeff_eq_zero (f := toMat fun _ : Unit => f)
    (fun i j => (memLp_toMat _ i j).integrable one_le_two) fun k => by
      ext i j
      refine (inner_shift_unitLp k i f).symm.trans ?_
      exact inner_shift_unitLp_of_mem_past ha (hf (k.toNat + 1)) (by omega) i
  refine Lp.ext ?_
  filter_upwards [h1, Lp.coeFn_zero (EuclideanSpace ℂ m) 2 (haarAddCircle (T := 1))] with t ht h2
  rw [h2]
  ext i
  exact congrFun (congrFun ht i) ()

/-- Helson–Lowdenslager (1961), p. 202, "since `Y` has no remote past, they span together the same
manifold as all the `M_n`": if the `a_j` are analytic, an element of `M_0` orthogonal to the spaces
`e_k R`, `k ≥ 0`, vanishes. -/
private theorem eq_zero_of_forall_inner_shift [Fintype l] {a : n → ColLp m}
    (ha : IsHardyTwo (toMat a)) {x : l → ColLp m} (hxa : ∀ i, x i ∈ innovation a)
    (hx : ∀ v ∈ innovation a, ∑ i, inner ℂ (x i) v • x i = v) {f : ColLp m} (hf : f ∈ past a 0)
    (hfx : ∀ k : ℤ, 0 ≤ k → ∀ i, inner ℂ (shift k (x i)) f = 0) : f = 0 := by
  refine eq_zero_of_forall_mem_past ha fun p => ?_
  induction p with
  | zero => exact hf
  | succ p ih =>
    -- `u = e_{-p} f` is in `M_0` and orthogonal to `R`, hence in `M_1`
    have hu : shift (-p) f ∈ past a 0 := by
      have h1 := shift_mem_past_add (-p) ih
      rwa [add_neg_cancel] at h1
    have h2 := hx _ (sub_starProjection_mem_innovation hu)
    have h3 (i : l) : inner ℂ (x i) (shift (-p) f) = 0 := by
      rw [← inner_shift_comm]
      exact hfx p (by omega) i
    simp only [inner_sub_starProjection (hxa _), h3, zero_smul, Finset.sum_const_zero] at h2
    have h4 : shift (-p) f ∈ past a 1 := by
      rw [sub_eq_zero.1 h2.symm]
      exact Submodule.starProjection_apply_mem _ _
    have h5 := shift_mem_past_add p h4
    rwa [shift_shift, add_neg_cancel, shift_zero, add_comm] at h5

/-- Helson–Lowdenslager (1961), p. 202: the `e_k x_i` are "an orthonormal process having the same
past". If the `a_j` are analytic, they are in the closed span of the functions `e_k x_i`, `k ≥ 0`.
(The converse is clear, because the `x_i` are in `M_0`.) -/
private theorem mem_past_innovation [Fintype l] {a : n → ColLp m} (ha : IsHardyTwo (toMat a))
    {x : l → ColLp m} (hxa : ∀ i, x i ∈ innovation a)
    (hx : ∀ v ∈ innovation a, ∑ i, inner ℂ (x i) v • x i = v) (j : n) : a j ∈ past x 0 := by
  have hle : past x 0 ≤ past a 0 := by
    refine past_le (Submodule.isClosed_topologicalClosure _) fun k hk i => ?_
    exact past_anti a (by omega) (shift_mem_past_add k (hxa i).1)
  have h1 : a j - (past x 0).starProjection (a j) = 0 := by
    refine eq_zero_of_forall_inner_shift ha hxa hx (Submodule.sub_mem _ (mem_past_zero a j)
      (hle (Submodule.starProjection_apply_mem _ _))) fun k hk i => ?_
    exact Submodule.inner_right_of_mem_orthogonal (shift_mem_past x hk i)
      (Submodule.sub_starProjection_mem_orthogonal _)
  rw [sub_eq_zero.1 h1]
  exact Submodule.starProjection_apply_mem _ _

/-- Helson–Lowdenslager (1961), p. 202: if `a` is analytic, it is a moving average of its
innovation, `a = x (xᴴ a)`. -/
private theorem toMat_mul_conjTranspose_mul [Finite n] [Fintype l] [DecidableEq l]
    {a : n → ColLp m} (ha : IsHardyTwo (toMat a)) {x : l → ColLp m}
    (hX : ∀ᵐ t ∂haarAddCircle, (toMat x t)ᴴ * toMat x t = 1) (hxa : ∀ i, x i ∈ innovation a)
    (hx : ∀ v ∈ innovation a, ∑ i, inner ℂ (x i) v • x i = v) :
    ∀ᵐ t ∂haarAddCircle, toMat x t * ((toMat x t)ᴴ * toMat a t) = toMat a t := by
  obtain ⟨c, -, hlim⟩ := exists_tendsto_of_mem_past (mem_past_innovation ha hxa hx)
  obtain ⟨ns, -, hns⟩ := hlim.exists_seq_tendsto_ae
    fun N => memLp_mul_continuous (memLp_toMat x) (continuous_circPoly_matrix (c N))
  filter_upwards [hX, hns] with t h1 h2
  have h3 : Tendsto (fun N => toMat x t * ((toMat x t)ᴴ * (toMat x t * circPoly (c (ns N)) t)))
      atTop (𝓝 (toMat x t * ((toMat x t)ᴴ * toMat a t))) := by
    have h4 : Continuous fun M : Matrix m n ℂ => toMat x t * ((toMat x t)ᴴ * M) :=
      continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id)
    exact (h4.tendsto _).comp h2
  refine tendsto_nhds_unique h3 (h2.congr fun N => ?_)
  rw [← Matrix.mul_assoc (toMat x t)ᴴ, h1, Matrix.one_mul]

end Columns

/-! ### Approximation by the functions `A Q` -/

section Approximation

variable [Fintype n]

/-- The closure of the set of the functions `A Q`, `Q` an analytic polynomial, is invariant under
multiplication by analytic polynomials (Helson–Lowdenslager (1961), p. 205). If it contains the
bounded function `M`, it contains `M Q` for every analytic polynomial `Q`, hence `M G` for every
`G ∈ H²`. -/
private theorem exists_tendsto_mul [Finite l] [Finite m] {r : Type*} [Fintype r]
    {A : UnitAddCircle → Matrix m n ℂ} (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle)
    {M : UnitAddCircle → Matrix m r ℂ} {C : ℝ}
    (hM : ∀ i j, AEStronglyMeasurable (fun t => M t i j) haarAddCircle)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖M t i j‖ ≤ C) {d : ℕ → ℤ →₀ Matrix n r ℂ}
    (hd : ∀ N, ∀ k ∈ (d N).support, 0 ≤ k)
    (hlim : TendstoLTwo (fun N t => A t * circPoly (d N) t) M) {G : UnitAddCircle → Matrix r l ℂ}
    (hG : IsHardyTwo G) :
    ∃ c : ℕ → ℤ →₀ Matrix n l ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
      TendstoLTwo (fun N t => A t * circPoly (c N) t) fun t => M t * G t := by
  obtain ⟨Q, hQ, hQG⟩ := hG.exists_tendsto_circPoly
  choose e he het using fun K N => exists_circPoly_mul (hd N) (hQ K)
  -- `A d_N Q_K → M Q_K` for `N → ∞`
  have h1 (K : ℕ) : TendstoLTwo (fun N t => A t * circPoly (e K N) t)
      fun t => M t * circPoly (Q K) t := by
    simpa only [het, Matrix.mul_assoc] using
      hlim.mul_continuous (continuous_circPoly_matrix (Q K)) fun N =>
        memLp_mul_continuous hA (continuous_circPoly_matrix (d N))
  -- `M Q_K → M G` for `K → ∞`
  have h2 := hQG.bounded_mul hM hC
    fun K => memLp_entry_of_continuous (continuous_circPoly_matrix (Q K))
  obtain ⟨ν, hν⟩ := exists_tendstoLTwo_diagonal h1 h2
  exact ⟨fun K => e K (ν K), fun K => he K (ν K), hν⟩

/-- If `A P_N → F` in `L²` and the columns of `X` are orthonormal, then `Xᴴ A P_N → Xᴴ F`
(Helson–Lowdenslager (1961), p. 203, with `F = X G`, so that `Xᴴ F = G`). -/
private theorem tendsto_conjTranspose_mul [Fintype m] [DecidableEq l] {r : Type*}
    {A : UnitAddCircle → Matrix m n ℂ} (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle)
    {X : UnitAddCircle → Matrix m l ℂ} (hX2 : ∀ i j, MemLp (fun t => X t i j) 2 haarAddCircle)
    (hX : ∀ᵐ t ∂haarAddCircle, (X t)ᴴ * X t = 1) {P : ℕ → UnitAddCircle → Matrix n r ℂ}
    (hP : ∀ N, Continuous (P N)) {F : UnitAddCircle → Matrix m r ℂ}
    {G : UnitAddCircle → Matrix l r ℂ} (hG : ∀ᵐ t ∂haarAddCircle, (X t)ᴴ * F t = G t)
    (hlim : TendstoLTwo (fun N t => A t * P N t) F) :
    TendstoLTwo (fun N t => (X t)ᴴ * A t * P N t) G :=
  (hlim.bounded_mul (G := fun t => (X t)ᴴ) (fun i j => (hX2 j i).star.aestronglyMeasurable)
    (norm_conjTranspose_apply_le_one hX) fun N => memLp_mul_continuous hA (hP N)).congr_ae
    (fun _ => ae_of_all _ fun _ => (Matrix.mul_assoc _ _ _).symm) hG

/-- The rank `q` of the process of the columns of `A` (the number of the columns of the innovation
`X`) is at most the rank of `A (t)` at almost every point, because functions `A Q_N` converge to
`X`. So it is at most `r` if `Aᴴ A = Cᴴ C`, where `C` has `r` rows, since then the rank of `A (t)`
is that of `C (t)`. This is the last step of the argument of Helson–Lowdenslager (1961), p. 207, for
which they give no proof: if `W` has a factor "with fewer than `q` columns", then "the canonical
process in `L² (W)` would have rank smaller than `q`, which is false". -/
private theorem le_rank_of_tendsto [Fintype m] {q : ℕ} {A : UnitAddCircle → Matrix m n ℂ}
    (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle)
    {X : UnitAddCircle → Matrix m (Fin q) ℂ} (hX : ∀ᵐ t ∂haarAddCircle, (X t)ᴴ * X t = 1)
    {d : ℕ → ℤ →₀ Matrix n (Fin q) ℂ}
    (hlim : TendstoLTwo (fun N t => A t * circPoly (d N) t) X) :
    ∀ᵐ t ∂haarAddCircle, q ≤ (A t).rank := by
  obtain ⟨ns, -, hns⟩ := hlim.exists_seq_tendsto_ae fun N =>
    memLp_mul_continuous hA (continuous_circPoly_matrix (d N))
  filter_upwards [hX, hns] with t h1 h2
  calc q = ((X t)ᴴ * X t).rank := by rw [h1, Matrix.rank_one, Fintype.card_fin]
    _ ≤ (X t).rank := Matrix.rank_mul_le_right _ _
    _ ≤ (A t).rank := Submodule.finrank_mono (range_le_of_tendsto h2)

end Approximation

variable [Fintype n] [DecidableEq n]

/-! ### Outer functions -/

/-- If the entries of `A` are in `L²`, so are those of `A (1 + P)` for every trigonometric
polynomial `P`. -/
theorem memLp_mul_one_add {A : UnitAddCircle → Matrix m n ℂ}
    (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle) (c : ℤ →₀ Matrix n n ℂ) (i : m) (j : n) :
    MemLp (fun t => (A t * (1 + circPoly c t) : Matrix m n ℂ) i j) 2 haarAddCircle :=
  memLp_mul_continuous hA (continuous_const.add (continuous_circPoly_matrix c)) i j

/-- Helson–Lowdenslager (1961), p. 203, (125)–(127): `A ∈ H²` is (right-)outer if the closure in
`L²` of the functions `A (1 + P)`, where `P` is an analytic trigonometric polynomial without
constant term, contains a constant function. "Evidently the constant matrix can only be the constant
term of `A`", so that the definition takes `Â (0)` for it. -/
def IsOuter (A : UnitAddCircle → Matrix m n ℂ) : Prop :=
  IsHardyTwo A ∧ ∃ c : ℕ → ℤ →₀ Matrix n n ℂ, (∀ N, ∀ k ∈ (c N).support, 0 < k) ∧
    TendstoLTwo (fun N t => A t * (1 + circPoly (c N) t)) fun _ => matFourierCoeff A 0

/-- Helson–Lowdenslager (1961), §9, p. 202, and (1958), (49), (51), (52), (54), (63)–(67): the
innovation `X` of the columns of `A`. The entries of `A` are in `L²`; `X` has at most as many
columns as `A`, which are orthonormal at almost every point, and `Xᴴ A` is analytic; the functions
`A (1 + P)`, with `P` an analytic polynomial without constant term, approximate `X B₀`, where `B₀`
is the constant coefficient of `Xᴴ A`. If `A` is analytic, there is no remote past, so that
`A = X (Xᴴ A)`. Finally (for p. 203 of (1961)), the columns of `X` are in the past of `A`, the
closed span of the columns of the functions `A e_k`, `k ≥ 0`, and the functions `A Q`, `Q` an
analytic polynomial, approximate `X`. -/
theorem exists_innovation [Fintype m] {A : UnitAddCircle → Matrix m n ℂ}
    (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle) :
    ∃ (q : ℕ) (X : UnitAddCircle → Matrix m (Fin q) ℂ), q ≤ Fintype.card n ∧
      (∀ i j, MemLp (fun t => X t i j) 2 haarAddCircle) ∧
      (∀ᵐ t ∂haarAddCircle, (X t)ᴴ * X t = 1) ∧ IsHardyTwo (fun t => (X t)ᴴ * A t) ∧
      (∃ c : ℕ → ℤ →₀ Matrix n n ℂ, (∀ N, ∀ k ∈ (c N).support, 0 < k) ∧
        TendstoLTwo (fun N t => A t * (1 + circPoly (c N) t))
          fun t => X t * matFourierCoeff (fun s => (X s)ᴴ * A s) 0) ∧
      (IsHardyTwo A → ∀ᵐ t ∂haarAddCircle, X t * ((X t)ᴴ * A t) = A t) ∧
      ∃ d : ℕ → ℤ →₀ Matrix n (Fin q) ℂ, (∀ N, ∀ k ∈ (d N).support, 0 ≤ k) ∧
        TendstoLTwo (fun N t => A t * circPoly (d N) t) X := by
  obtain ⟨a, ha⟩ := exists_toMat hA
  obtain ⟨q, hq, x, hx, hxa, hxs⟩ := exists_orthonormal_innovation a
  have hX := conjTranspose_mul_self_eq_one hx hxa
  have hB : ∀ᵐ t ∂haarAddCircle, (toMat x t)ᴴ * toMat a t = (toMat x t)ᴴ * A t := by
    filter_upwards [ha] with t ht
    rw [ht]
  have hB0 := matFourierCoeff_congr_ae hB 0
  have hB2 := (isHardyTwo_conjTranspose_toMat_mul hx hxa).congr_ae hB
  obtain ⟨d, hd, hdlim⟩ := exists_tendsto_of_mem_past fun i => (hxa i).1
  have hdA := hdlim.congr_ae (G := fun N t => A t * circPoly (d N) t)
    (fun N => ha.mono fun t ht => by rw [ht]) (ae_of_all _ fun _ => rfl)
  refine ⟨q, toMat x, hq, memLp_toMat x, hX, hB2, ?_, fun hA2 => ?_, d, hd, hdA⟩
  · obtain ⟨c, hc, hlim⟩ := exists_tendsto_innovation hxa hxs
    rw [← hB0]
    refine ⟨c, hc, hlim.congr_ae (fun N => ?_) (ae_of_all _ fun _ => rfl)⟩
    filter_upwards [ha] with t ht
    rw [ht]
  · have ha2 : IsHardyTwo (toMat a) := hA2.congr_ae (ha.mono fun _ h => h.symm)
    filter_upwards [ha, toMat_mul_conjTranspose_mul ha2 hX hxa hxs] with t h1 h2
    rw [← h1, h2]

/-- Helson–Lowdenslager (1958), (77) and p. 194: let `1 + H` be the limit of the `1 + P_N` in the
extremal problem for `Aᴴ A`. If `A (1 + H) = X B̂ (0)`, where `B = Xᴴ A`, then the functions
`B (1 + P_N)` converge to `B (1 + H) = B̂ (0)`, which means that `B` is outer ((1961), p. 204).
(`exists_isOuter` follows (1961), p. 203, instead: the functions `B Q` are dense in `H²`.) -/
theorem isOuter_conjTranspose_mul [Fintype m] [Fintype l] [DecidableEq l]
    {A : UnitAddCircle → Matrix m n ℂ} (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle)
    {X : UnitAddCircle → Matrix m l ℂ} (hX2 : ∀ i j, MemLp (fun t => X t i j) 2 haarAddCircle)
    (hX : ∀ᵐ t ∂haarAddCircle, (X t)ᴴ * X t = 1) (hB : IsHardyTwo fun t => (X t)ᴴ * A t)
    {c : ℕ → ℤ →₀ Matrix n n ℂ} (hc : ∀ N, ∀ k ∈ (c N).support, 0 < k)
    (hlim : TendstoLTwo (fun N t => A t * (1 + circPoly (c N) t))
      fun t => X t * matFourierCoeff (fun s => (X s)ᴴ * A s) 0) :
    IsOuter fun t => (X t)ᴴ * A t :=
  ⟨hB, c, hc, tendsto_conjTranspose_mul hA hX2 hX
    (fun N => continuous_const.add (continuous_circPoly_matrix (c N)))
    (hX.mono fun t ht => by rw [← Matrix.mul_assoc, ht, Matrix.one_mul]) hlim⟩

/-- A function formed from rows of an outer function is outer. -/
theorem IsOuter.submatrix {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A) (r : l → m) :
    IsOuter fun t => (A t).submatrix r id := by
  obtain ⟨hA2, c, hc, hlim⟩ := hA
  exact ⟨hA2.submatrix r id, c, hc, fun i j => hlim (r i) j⟩

/-- Helson–Lowdenslager (1961), p. 203: if the functions `A Q`, `Q` an analytic polynomial, are
dense in `H²`, the functions `A (1 + P)`, `P` an analytic polynomial without constant term, "are
dense in the subset of `H²` containing all functions with the same constant term as `A`": if `A Q`
approximates `e_{-1} (F - A)`, then `A (1 + e_1 Q)` approximates `F`. -/
private theorem exists_tendsto_mul_one_add_of_dense {A : UnitAddCircle → Matrix m n ℂ}
    (hA : IsHardyTwo A) (h : ∀ G : UnitAddCircle → Matrix m n ℂ, IsHardyTwo G →
      ∃ c : ℕ → ℤ →₀ Matrix n n ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
        TendstoLTwo (fun N t => A t * circPoly (c N) t) G)
    {F : UnitAddCircle → Matrix m n ℂ} (hF : IsHardyTwo F)
    (h0 : matFourierCoeff F 0 = matFourierCoeff A 0) :
    ∃ c : ℕ → ℤ →₀ Matrix n n ℂ, (∀ N, ∀ k ∈ (c N).support, 0 < k) ∧
      TendstoLTwo (fun N t => A t * (1 + circPoly (c N) t)) F := by
  obtain ⟨c, hc, hlim⟩ := h _ ((hF.sub hA).fourier_neg_one_smul (by
    rw [matFourierCoeff_sub hF.isHardyOne.1 hA.isHardyOne.1, h0, sub_self]))
  choose d hd hdt using fun N => exists_circPoly_fourier_smul (hc N)
  have h1 := hlim.mul_continuous (G := fun t => fourier 1 t • (1 : Matrix n n ℂ))
    ((fourier 1).continuous.smul continuous_const) fun N =>
      memLp_mul_continuous hA.1 (continuous_circPoly_matrix (c N))
  refine ⟨d, hd, fun i j => (h1 i j).congr fun N => ?_⟩
  congr 1
  ext t
  dsimp only
  rw [hdt, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    ← fourier_add, add_neg_cancel, fourier_zero, one_smul, Matrix.mul_add, Matrix.mul_one,
    Matrix.mul_smul, Matrix.add_apply, Matrix.sub_apply]
  ring

/-- Helson–Lowdenslager (1961), p. 203: if the functions `A Q`, `Q` an analytic polynomial, are
dense in `H²`, the functions `A (1 + P)` are dense in the set of the functions of `H²` "with the
same constant term as `A`, and so `A` is outer". -/
theorem isOuter_of_dense {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyTwo A)
    (h : ∀ G : UnitAddCircle → Matrix m n ℂ, IsHardyTwo G →
      ∃ c : ℕ → ℤ →₀ Matrix n n ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
        TendstoLTwo (fun N t => A t * circPoly (c N) t) G) : IsOuter A :=
  ⟨hA, exists_tendsto_mul_one_add_of_dense hA h (isHardyTwo_const _)
    (by rw [matFourierCoeff_const, ite_eq_left rfl])⟩

/-- Helson–Lowdenslager (1961), proof of Theorem 9, first part: the range of `Â (0)` is contained in
the range of `A` almost everywhere. -/
private theorem IsOuter.range_matFourierCoeff_le [Finite m] {A : UnitAddCircle → Matrix m n ℂ}
    (hA : IsOuter A) : ∀ᵐ t ∂haarAddCircle,
      LinearMap.range (matFourierCoeff A 0).mulVecLin ≤ LinearMap.range (A t).mulVecLin := by
  obtain ⟨hA2, c, -, hlim⟩ := hA
  obtain ⟨ns, -, hns⟩ := hlim.exists_seq_tendsto_ae fun N => memLp_mul_one_add hA2.1 (c N)
  filter_upwards [hns] with t ht
  exact range_le_of_tendsto ht

/-- Helson–Lowdenslager (1961), proof of Theorem 9, second part: if `L Â (0) = 0`, then `Z = L A`
vanishes. The functions `Z (1 + P_N)` converge to `L Â (0) = 0`. If `Ẑ (i) = 0` for `i < p`, then
the coefficient of order `p` of `Z P_N` vanishes, because `P_N` has no constant term, hence
`Ẑ (p) = 0`. -/
private theorem IsOuter.matFourierCoeff_mul_eq_zero [Fintype m] [Finite l]
    {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A) {L : Matrix l m ℂ}
    (hL : L * matFourierCoeff A 0 = 0) (k : ℤ) : matFourierCoeff (fun t => L * A t) k = 0 := by
  obtain ⟨hA2, c, hc, hlim⟩ := hA
  have hZ : IsHardyTwo fun t => L * A t := hA2.const_mul L
  have h1 := hlim.continuous_mul (continuous_const (y := L)) fun N => memLp_mul_one_add hA2.1 (c N)
  simp only [← Matrix.mul_assoc, hL] at h1
  have h2 (k : ℤ) := h1.tendsto_matFourierCoeff (fun N => memLp_mul_one_add hZ.1 (c N)) k
  have h3 (p : ℕ) : matFourierCoeff (fun t => L * A t) p = 0 := by
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      have h4 := h2 p
      rw [matFourierCoeff_const, ite_self] at h4
      refine tendsto_nhds_unique (tendsto_const_nhds.congr fun N => ?_) h4
      obtain ⟨d, hd, hd0, hdt⟩ := exists_circPoly_eq_one_add_mul (hc N) (1 : Matrix n n ℂ)
      simp only [Matrix.mul_one] at hdt
      simp only [← hdt]
      rw [matFourierCoeff_mul hZ (isHardyTwo_circPoly hd), Finset.sum_range_succ,
        Finset.sum_eq_zero fun q hq => by rw [ih q (Finset.mem_range.1 hq), Matrix.zero_mul],
        zero_add, sub_self, matFourierCoeff_circPoly, hd0, Matrix.mul_one]
  rcases lt_or_ge k 0 with hk | hk
  · exact hZ.2 k hk
  · have h5 := h3 k.toNat
    rwa [Int.toNat_of_nonneg hk] at h5

/-- Helson–Lowdenslager (1961), proof of Theorem 9, second part: `L A = 0` if `L Â (0) = 0`. -/
private theorem IsOuter.mul_ae_eq_zero [Fintype m] [Finite l] {A : UnitAddCircle → Matrix m n ℂ}
    (hA : IsOuter A) {L : Matrix l m ℂ} (hL : L * matFourierCoeff A 0 = 0) :
    ∀ᵐ t ∂haarAddCircle, L * A t = 0 :=
  ae_eq_zero_of_matFourierCoeff_eq_zero (hA.1.const_mul L).isHardyOne.1
    (hA.matFourierCoeff_mul_eq_zero hL)

/-- Helson–Lowdenslager (1961), Theorem 9: the range of an outer function is almost everywhere that
of its constant coefficient. -/
theorem IsOuter.range_eq [Finite m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A) :
    ∀ᵐ t ∂haarAddCircle, LinearMap.range (A t).mulVecLin =
      LinearMap.range (matFourierCoeff A 0).mulVecLin := by
  classical
  cases nonempty_fintype m
  set M := matFourierCoeff A 0
  obtain ⟨D, hD⟩ := exists_mul_mul_eq M
  -- the null space of `L = 1 - M D` is the range of `M`
  set L : Matrix m m ℂ := 1 - M * D with hLdef
  have hL : L * M = 0 := by rw [hLdef, Matrix.sub_mul, Matrix.one_mul, hD, sub_self]
  filter_upwards [hA.mul_ae_eq_zero hL, hA.range_matFourierCoeff_le] with t h1 h2
  refine le_antisymm ?_ h2
  have h3 : A t = M * (D * A t) := by
    rw [hLdef, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    rw [← Matrix.mul_assoc, ← h1]
  rw [h3]
  exact range_mul_le _ _

/-- Helson–Lowdenslager (1961), p. 207: "`B` is of rank `q` at each point", where `q` is the rank of
the process and `B = Xᴴ A`; hence the rank of the constant coefficient of `B` is `q`, by Theorem 9
(p. 209, "`B₀` is non-singular if `B` is outer and of full rank"). In the source, if the rank of
`B (t)`, which does not depend on `t` by Theorem 9, were smaller than `q`, "we could restrict `B` to
the complement of its null-space (which is constant because `B` is outer) and find an analytic
function `C` with fewer than `q` columns such that `C C* = W`", and "the canonical process in
`L² (W)` would have rank smaller than `q`". The last step, for which the source gives no proof, is
`le_rank_of_tendsto`; as this bounds `q` by the rank of `A (t)`, which is that of `B (t)` because
`A = X B`, the function `C` is not needed. -/
private theorem rank_of_isOuter [Fintype m] {q : ℕ} {A : UnitAddCircle → Matrix m n ℂ}
    (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle)
    {X : UnitAddCircle → Matrix m (Fin q) ℂ} (hX : ∀ᵐ t ∂haarAddCircle, (X t)ᴴ * X t = 1)
    {d : ℕ → ℤ →₀ Matrix n (Fin q) ℂ}
    (hlim : TendstoLTwo (fun N t => A t * circPoly (d N) t) X)
    (hXA : ∀ᵐ t ∂haarAddCircle, X t * ((X t)ᴴ * A t) = A t)
    (hB : IsOuter fun t => (X t)ᴴ * A t) :
    (matFourierCoeff (fun t => (X t)ᴴ * A t) 0).rank = q := by
  obtain ⟨t, h1, h2, h3⟩ := ((le_rank_of_tendsto hA hX hlim).and (hXA.and hB.range_eq)).exists
  refine le_antisymm ((Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin q)) (h1.trans ?_)
  calc (A t).rank = (X t * ((X t)ᴴ * A t)).rank := by rw [h2]
    _ ≤ ((X t)ᴴ * A t).rank := Matrix.rank_mul_le_right _ _
    _ = _ := congrArg (fun K : Submodule ℂ (Fin q → ℂ) => Module.finrank ℂ K) h3

/-- Helson–Lowdenslager (1961), corollary on p. 202, pp. 203 and 207: if `A ∈ H²`, then
`Aᴴ A = Bᴴ B` for an outer function `B` whose constant coefficient is surjective, with at most as
many rows as `A` has columns. Let `X` be the innovation and `B = Xᴴ A`, so that `A Q = X (B Q)` for
every analytic polynomial `Q` (129). The columns of `X` are in the past of `A`, so that the
functions `A Q` approximate `X`, hence `X G` for every `G ∈ H²`, "but this implies, because `X` is
orthonormal, that the functions" `B Q` "are dense in `H²`", so that `B` is outer
(`isOuter_of_dense`). The constant coefficient of `B` is surjective because `B` "is of rank `q` at
each point" (`rank_of_isOuter`). -/
theorem exists_isOuter [Fintype m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyTwo A) :
    ∃ (q : ℕ) (B : UnitAddCircle → Matrix (Fin q) n ℂ), q ≤ Fintype.card n ∧ IsOuter B ∧
      (matFourierCoeff B 0).rank = q ∧ ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = (A t)ᴴ * A t := by
  obtain ⟨q, X, hq, hX2, hX, hB, -, hH, d, hd, hlim⟩ := exists_innovation hA.1
  have hBo : IsOuter fun t => (X t)ᴴ * A t := isOuter_of_dense hB fun G hG => by
    obtain ⟨c, hc, hlim⟩ := exists_tendsto_mul hA.1 (fun i j => (hX2 i j).aestronglyMeasurable)
      (hX.mono fun t ht => norm_apply_le_one_of_conjTranspose_mul_self ht) hd hlim hG
    refine ⟨c, hc, tendsto_conjTranspose_mul hA.1 hX2 hX
      (fun N => continuous_circPoly_matrix (c N)) ?_ hlim⟩
    filter_upwards [hX] with t ht
    rw [← Matrix.mul_assoc, ht, Matrix.one_mul]
  exact ⟨q, _, hq, hBo, rank_of_isOuter hA.1 hX hlim (hH hA) hBo,
    (hH hA).mono fun t ht => conjTranspose_mul_self_of_mul_eq ht⟩

/-- Helson–Lowdenslager (1961), proof of Theorem 10: the closure of the functions `A Q` contains
`Â (0)`, hence `Â (0) Q` for every analytic polynomial `Q`, hence `Â (0) G` for every `G ∈ H²`. -/
private theorem IsOuter.exists_tendsto_matFourierCoeff_mul [Finite l] [Finite m]
    {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A) {G : UnitAddCircle → Matrix n l ℂ}
    (hG : IsHardyTwo G) :
    ∃ c : ℕ → ℤ →₀ Matrix n l ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
      TendstoLTwo (fun N t => A t * circPoly (c N) t) fun t => matFourierCoeff A 0 * G t := by
  obtain ⟨hA2, p, hp, hlim⟩ := hA
  choose d hd _ hdt using fun N => exists_circPoly_eq_one_add_mul (hp N) (1 : Matrix n n ℂ)
  simp only [Matrix.mul_one] at hdt
  simp only [← hdt] at hlim
  obtain ⟨C, hC⟩ := exists_bound_of_continuous
    (f := fun _ : UnitAddCircle => matFourierCoeff A 0) continuous_const
  exact exists_tendsto_mul (M := fun _ => matFourierCoeff A 0) hA2.1
    (fun _ _ => aestronglyMeasurable_const) (ae_of_all _ hC) hd hlim hG

/-- Helson–Lowdenslager (1961), Theorem 10: if `A` is outer, the closure in `L²` of the functions
`A Q`, `Q` an analytic trigonometric polynomial, consists of the functions of `H²` whose range is
contained in that of `A` almost everywhere, that is, in the range of `Â (0)`. (That the closure is
contained in `H²` is `TendstoLTwo.isHardyTwo`.) The source proves the case that `Â (0)` is
surjective, "and the general case follows easily"; here a matrix `D` with `Â (0) D Â (0) = Â (0)`
takes the place of the right inverse of `Â (0)`, and `F = Â (0) (D F)`. -/
theorem IsOuter.exists_tendsto_iff [Fintype l] [Finite m] {A : UnitAddCircle → Matrix m n ℂ}
    (hA : IsOuter A) {F : UnitAddCircle → Matrix m l ℂ} (hF : IsHardyTwo F) :
    (∃ c : ℕ → ℤ →₀ Matrix n l ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
        TendstoLTwo (fun N t => A t * circPoly (c N) t) F) ↔
      ∀ᵐ t ∂haarAddCircle, LinearMap.range (F t).mulVecLin ≤
        LinearMap.range (matFourierCoeff A 0).mulVecLin := by
  refine ⟨fun ⟨c, _, hlim⟩ => ?_, fun h => ?_⟩
  · obtain ⟨ns, -, hns⟩ := hlim.exists_seq_tendsto_ae
      fun N => memLp_mul_continuous hA.1.1 (continuous_circPoly_matrix (c N))
    filter_upwards [hns, hA.range_eq] with t h1 h2
    exact h2 ▸ range_le_of_tendsto h1
  · cases nonempty_fintype m
    obtain ⟨D, hD⟩ := exists_mul_mul_eq (matFourierCoeff A 0)
    obtain ⟨c, hc, hlim⟩ := hA.exists_tendsto_matFourierCoeff_mul (hF.const_mul D)
    refine ⟨c, hc, hlim.congr_ae (fun N => ae_of_all _ fun _ => rfl) ?_⟩
    filter_upwards [h] with t ht
    exact mul_mul_eq_of_range_le hD ht

/-- If `A` is outer and its constant coefficient is surjective, the functions `A Q`, `Q` an analytic
trigonometric polynomial, approximate the identity matrix in `L²`. -/
theorem IsOuter.exists_tendsto_one [Fintype m] [DecidableEq m]
    {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A)
    (h0 : (matFourierCoeff A 0).rank = Fintype.card m) :
    ∃ c : ℕ → ℤ →₀ Matrix n m ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
      TendstoLTwo (fun N t => A t * circPoly (c N) t) fun _ => 1 := by
  refine (hA.exists_tendsto_iff (isHardyTwo_const 1)).2
    (ae_of_all _ fun t => le_top.trans_eq (Eq.symm ?_))
  exact LinearMap.range_eq_top.2 (Matrix.mulVec_surjective_iff_rank_eq_card.2 h0)

/-- If `B` is outer and its constant coefficient is surjective, a bounded function `Q` such that
`Q B` is in `H²` is in `H²`: if the functions `B P`, `P` an analytic polynomial, approximate `1`,
then the functions `Q B P` approximate `Q`, "which consequently must be analytic"
(Helson–Lowdenslager (1961), p. 208). -/
theorem IsOuter.isHardyTwo_of_bounded_mul [Fintype m]
    {B : UnitAddCircle → Matrix m n ℂ} (hB : IsOuter B)
    (h0 : (matFourierCoeff B 0).rank = Fintype.card m) {Q : UnitAddCircle → Matrix l m ℂ} {C : ℝ}
    (hQ : ∀ i j, AEStronglyMeasurable (fun t => Q t i j) haarAddCircle)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖Q t i j‖ ≤ C) (hQB : IsHardyTwo fun t => Q t * B t) :
    IsHardyTwo Q := by
  classical
  obtain ⟨c, hc, hlim⟩ := hB.exists_tendsto_one h0
  have h1 := hlim.bounded_mul hQ hC fun N =>
    memLp_mul_continuous hB.1.1 (continuous_circPoly_matrix (c N))
  simp only [Matrix.mul_one] at h1
  refine h1.isHardyTwo fun N => ?_
  obtain ⟨D, hD⟩ := exists_bound_of_continuous (continuous_circPoly_matrix (c N))
  simpa only [Matrix.mul_assoc] using hQB.mul_bounded (isHardyTwo_circPoly (hc N)) (ae_of_all _ hD)

end HarmonicAnalysis
