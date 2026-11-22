module

public import VectorValuedHarmonicAnalysis.Hardy.Szego

/-!
# Analytic range functions and the factorization of positive functions of any rank

A range function on the circle is a function whose values are subspaces of `ℂᵐ`; it is analytic if
it is almost everywhere the range of a function of `H²`. Following H. Helson and D. Lowdenslager,
*Prediction theory and Fourier series in several variables. II*, Acta Math. 106 (1961), 175–213,
§§10–11:

* `isOuter_iff_integral_log_norm_det` (Theorem 8): a square matrix-valued function `A ∈ H²` with
  `det Â (0) ≠ 0` is outer if and only if `∫ log |det A| = log |det Â (0)|`.
* `IsAnalyticRange.exists_isometry` (Theorem 12): every analytic range function is almost everywhere
  the range of a left-outer function whose values are isometries (partial isometries in the source's
  statement; its proof gives `Vᴴ V = 1`).
* `exists_mul_conjTranspose_eq_iff` (Theorem 13): a positive semidefinite function `W` with
  integrable entries is `A Aᴴ` for some `A ∈ H²` if and only if its range is analytic and
  `∫ log Δ W > −∞`, where `Δ W` is the determinant of `W` on its range (`rangeDet`).
* `isFactorable_iff`: Theorem 13 in the form of D. Sarason, *Generalized interpolation in H^∞*,
  Trans. Amer. Math. Soc. 127 (1967), 179–203, Lemma 10.1: `R = Bᴴ B` for some `B ∈ H²` if and only
  if the range function of `R` is conjugate analytic and `∫ log Δ R > −∞`.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexOrder Topology

namespace VectorValuedHarmonicAnalysis

/-! ### Matrices -/

/-- A square matrix of full rank is invertible. -/
private theorem det_ne_zero_of_rank_eq {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (h : M.rank = Fintype.card n) : M.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_surjective_iff_isUnit.1
    (Matrix.mulVec_surjective_iff_rank_eq_card.2 h))).ne_zero

/-- A positive semidefinite matrix `Y` with `det (1 + Y) = 1` is zero. -/
private theorem eq_zero_of_det_one_add_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {Y : Matrix n n ℂ} (hY : Y.PosSemidef) (h : (1 + Y).det = 1) : Y = 0 := by
  have hH := hY.isHermitian
  have h1 : 1 + Y = cfc (fun s : ℝ => 1 + s) Y := by
    rw [cfc_const_add (1 : ℝ) (fun s => s) Y (ha := hH.isSelfAdjoint),
      cfc_id' ℝ Y hH.isSelfAdjoint, map_one]
  have h2 : ∏ i, (1 + hH.eigenvalues i) = 1 := by
    rw [h1, det_cfc hH, ← Complex.ofReal_prod] at h
    exact_mod_cast h
  refine hH.eigenvalues_eq_zero_iff.1 (funext fun i => ?_)
  have h3 : 1 + hH.eigenvalues i ≤ ∏ i, (1 + hH.eigenvalues i) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    refine le_mul_of_one_le_right (add_nonneg zero_le_one (hY.eigenvalues_nonneg i)) ?_
    exact Finset.one_le_prod₀ fun j _ => le_add_of_nonneg_right (hY.eigenvalues_nonneg j)
  rw [h2, add_le_iff_nonpos_right] at h3
  exact le_antisymm h3 (hY.eigenvalues_nonneg i)

/-- `Mᴴ M` is positive definite if `M` is invertible. -/
private theorem posDef_conjTranspose_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.det ≠ 0) : (Mᴴ * M).PosDef := by
  rw [(Matrix.posSemidef_conjTranspose_mul_self M).posDef_iff_det_ne_zero, Matrix.det_mul,
    Matrix.det_conjTranspose]
  exact mul_ne_zero (star_ne_zero.2 hM) hM

/-- If `Mᴴ M ≤ C`, `M` is invertible and the determinants of `Mᴴ M` and `C` are the same, then
`C = Mᴴ M`. -/
private theorem eq_of_det_eq {n : Type*} [Fintype n] [DecidableEq n] {M C : Matrix n n ℂ}
    (hM : M.det ≠ 0) (hle : (C - Mᴴ * M).PosSemidef) (hdet : C.det = (Mᴴ * M).det) :
    C = Mᴴ * M := by
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hM)
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hM)
  have h1' : M⁻¹ᴴ * Mᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have h2' : Mᴴ * M⁻¹ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have h3 : 1 + M⁻¹ᴴ * (C - Mᴴ * M) * M⁻¹ = M⁻¹ᴴ * C * M⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc _ Mᴴ, h1', Matrix.one_mul, h1]
    abel
  have h4 : (M⁻¹ᴴ * C * M⁻¹).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdet, ← Matrix.det_mul, ← Matrix.det_mul,
      ← Matrix.mul_assoc, h1', Matrix.one_mul, h1, Matrix.det_one]
  have h5 := eq_zero_of_det_one_add_eq_one (hle.conjTranspose_mul_mul_same M⁻¹) (h3 ▸ h4)
  have h6 : Mᴴ * (M⁻¹ᴴ * (C - Mᴴ * M) * M⁻¹) * M = C - Mᴴ * M := by
    rw [Matrix.mul_assoc Mᴴ, Matrix.mul_assoc _ M⁻¹, h2, Matrix.mul_one, ← Matrix.mul_assoc, h2',
      Matrix.one_mul]
  rw [h5, Matrix.mul_zero, Matrix.zero_mul] at h6
  exact sub_eq_zero.1 h6.symm

/-- If `Mᴴ M ≤ C`, `M` is invertible and the determinants of `Mᴴ M` and `C` are the same, then
`C = Mᴴ M` (Helson–Lowdenslager (1961), (131): "with equality if and only if `C = A₀ A₀*`"). -/
private theorem eq_of_log_det_eq {n : Type*} [Fintype n] [DecidableEq n] {M C : Matrix n n ℂ}
    (hM : M.det ≠ 0) (hle : (C - Mᴴ * M).PosSemidef)
    (hlog : Real.log C.det.re = Real.log (Mᴴ * M).det.re) : C = Mᴴ * M := by
  have hMM := posDef_conjTranspose_mul_self hM
  have hC : C.PosDef := by simpa using hMM.add_posSemidef hle
  have h1 := Complex.pos_iff.1 hMM.det_pos
  have h2 := Complex.pos_iff.1 hC.det_pos
  exact eq_of_det_eq hM hle <| Complex.ext (Real.log_injOn_pos h2.1 h1.1 hlog) (h2.2 ▸ h1.2)

/-- The range of a product is contained in that of its left factor. -/
private theorem range_mul_le {l m n : Type*} [Fintype n] [Fintype l] (M : Matrix m n ℂ)
    (N : Matrix n l ℂ) :
    LinearMap.range (M * N).mulVecLin ≤ LinearMap.range M.mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- The range of `M Mᴴ` is that of `M`: `W = A Aᴴ` "is a positive semi-definite matrix function of
order `p` with the same range function" (Helson–Lowdenslager (1961), p. 207). -/
private theorem range_mul_conjTranspose {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    LinearMap.range (M * Mᴴ).mulVecLin = LinearMap.range M.mulVecLin :=
  Submodule.eq_of_le_of_finrank_eq (range_mul_le M Mᴴ) (Matrix.rank_self_mul_conjTranspose M)

/-! ### Theorem 8 -/

/-- The mean of a positive semidefinite function is positive semidefinite. -/
private theorem posSemidef_matFourierCoeff_zero {n : Type*} [Finite n]
    {K : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => K t i j) haarAddCircle)
    (hK : ∀ᵐ t ∂haarAddCircle, (K t).PosSemidef) : (matFourierCoeff K 0).PosSemidef := by
  cases nonempty_fintype n
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, matFourierCoeff, Matrix.of_apply, Matrix.of_apply]
    simp only [fourierCoeff, neg_zero, fourier_zero, one_smul, ← starRingEnd_apply]
    rw [← integral_conj]
    refine integral_congr_ae (hK.mono fun t ht => ?_)
    exact ht.isHermitian.apply i j
  · have h1 (M : Matrix n n ℂ) : star x ⬝ᵥ M.mulVec x =
        ((Matrix.replicateCol Unit x)ᴴ * (M * Matrix.replicateCol Unit x)) () () := by
      simp [Matrix.mul_apply, dotProduct, Matrix.mulVec]
    have h2 (i : n) (j : Unit) :
        Integrable (fun t => (K t * Matrix.replicateCol Unit x) i j) haarAddCircle :=
      integrable_mul_continuous hint continuous_const i j
    rw [h1, ← matFourierCoeff_mul_const hint, ← matFourierCoeff_const_mul _ h2, matFourierCoeff,
      Matrix.of_apply]
    simp only [← h1, fourierCoeff, neg_zero, fourier_zero, one_smul]
    exact integral_nonneg_of_ae (hK.mono fun t ht => ht.dotProduct_mulVec_nonneg x)

/-- The constant coefficient of the adjoint function is the adjoint of the constant coefficient. -/
private theorem matFourierCoeff_zero_conjTranspose {m n : Type*}
    (F : UnitAddCircle → Matrix m n ℂ) :
    matFourierCoeff (fun t => (F t)ᴴ) 0 = (matFourierCoeff F 0)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, matFourierCoeff, matFourierCoeff, Matrix.of_apply,
    Matrix.of_apply]
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul, Matrix.conjTranspose_apply,
    ← starRingEnd_apply]
  exact integral_conj

/-- Parseval's identity for a function `F = F₀ + …` such that `Fᴴ F = C` is constant: the mean of
`(F − F₀)ᴴ (F − F₀)` is `C − F₀ᴴ F₀`. -/
private theorem matFourierCoeff_zero_sub {m n : Type*} [Fintype m]
    {F : UnitAddCircle → Matrix m n ℂ} (hF : ∀ i j, MemLp (fun t => F t i j) 2 haarAddCircle)
    {C : Matrix n n ℂ} (hC : ∀ᵐ t ∂haarAddCircle, (F t)ᴴ * F t = C) :
    matFourierCoeff (fun t => (F t - matFourierCoeff F 0)ᴴ * (F t - matFourierCoeff F 0)) 0 =
      C - (matFourierCoeff F 0)ᴴ * matFourierCoeff F 0 := by
  obtain ⟨F₀, hF₀⟩ : ∃ M, M = matFourierCoeff F 0 := ⟨_, rfl⟩
  have hF1 (i : m) (j : n) : Integrable (fun t => F t i j) haarAddCircle :=
    (hF i j).integrable one_le_two
  have hF2 (i : n) (j : m) : Integrable (fun t => (F t)ᴴ i j) haarAddCircle :=
    (hF j i).star.integrable one_le_two
  have h1 := matFourierCoeff_const_mul F₀ᴴ hF1 0
  have h2 := matFourierCoeff_mul_const hF2 F₀ 0
  rw [matFourierCoeff_zero_conjTranspose, ← hF₀] at h2
  rw [← hF₀] at h1 ⊢
  have h3 (i j : n) : Integrable (fun t => (F₀ᴴ * F t) i j) haarAddCircle :=
    integrable_continuous_mul continuous_const hF1 i j
  have h4 (i j : n) : Integrable (fun t => ((F t)ᴴ * F₀) i j) haarAddCircle :=
    integrable_mul_continuous hF2 continuous_const i j
  ext i j
  have h5 : ∀ᵐ t ∂haarAddCircle, ((F t - F₀)ᴴ * (F t - F₀)) i j =
      (C + F₀ᴴ * F₀) i j - ((F₀ᴴ * F t) i j + ((F t)ᴴ * F₀) i j) := by
    filter_upwards [hC] with t ht
    rw [← ht, ← Matrix.add_apply, ← Matrix.sub_apply, Matrix.conjTranspose_sub, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub]
    refine congrArg (fun M : Matrix n n ℂ => M i j) ?_
    abel
  have h6 : Integrable (fun t => (F₀ᴴ * F t) i j + ((F t)ᴴ * F₀) i j) haarAddCircle :=
    (h3 i j).add (h4 i j)
  have h1' := congrFun₂ h1 i j
  have h2' := congrFun₂ h2 i j
  rw [matFourierCoeff, Matrix.of_apply] at h1' h2' ⊢
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at h1' h2' ⊢
  rw [integral_congr_ae h5, integral_sub (integrable_const _) h6, integral_add (h3 i j) (h4 i j),
    h1', h2', integral_const, probReal_univ, one_smul, Matrix.add_apply, Matrix.sub_apply]
  ring

/-- Helson–Lowdenslager (1961), p. 204: if `F = F₀ + …` and `Fᴴ F = C` is constant, then
`F₀ᴴ F₀ ≤ C`. -/
private theorem posSemidef_sub_conjTranspose_mul {m n : Type*} [Fintype m] [Finite n]
    {F : UnitAddCircle → Matrix m n ℂ} (hF : ∀ i j, MemLp (fun t => F t i j) 2 haarAddCircle)
    {C : Matrix n n ℂ} (hC : ∀ᵐ t ∂haarAddCircle, (F t)ᴴ * F t = C) :
    (C - (matFourierCoeff F 0)ᴴ * matFourierCoeff F 0).PosSemidef := by
  have h1 (i : m) (j : n) : MemLp (fun t => (F t - matFourierCoeff F 0) i j) 2 haarAddCircle :=
    (hF i j).sub (memLp_const _)
  rw [← matFourierCoeff_zero_sub hF hC]
  exact posSemidef_matFourierCoeff_zero
    (integrable_mul_of_memLp (g := fun t => (F t - matFourierCoeff F 0)ᴴ)
      (fun i j => (h1 j i).star) h1)
    (ae_of_all _ fun t => Matrix.posSemidef_conjTranspose_mul_self _)

/-- Helson–Lowdenslager (1961), p. 204: if `F = F₀ + …` is not constant and `Fᴴ F = C` is constant,
then "`C − F₀ᴴ F₀` is positive semi-definite and not `0`". -/
private theorem ae_eq_of_eq_conjTranspose_mul {m n : Type*} [Fintype m] [Finite n]
    {F : UnitAddCircle → Matrix m n ℂ} (hF : ∀ i j, MemLp (fun t => F t i j) 2 haarAddCircle)
    {C : Matrix n n ℂ} (hC : ∀ᵐ t ∂haarAddCircle, (F t)ᴴ * F t = C)
    (h : C = (matFourierCoeff F 0)ᴴ * matFourierCoeff F 0) :
    ∀ᵐ t ∂haarAddCircle, F t = matFourierCoeff F 0 := by
  cases nonempty_fintype n
  have h1 (i : m) (j : n) : MemLp (fun t => (F t - matFourierCoeff F 0) i j) 2 haarAddCircle :=
    (hF i j).sub (memLp_const _)
  have h2 (i j : n) : Integrable (fun t =>
      ((F t - matFourierCoeff F 0)ᴴ * (F t - matFourierCoeff F 0)) i j) haarAddCircle :=
    integrable_mul_of_memLp (g := fun t => (F t - matFourierCoeff F 0)ᴴ)
      (fun i j => (h1 j i).star) h1 i j
  have h3 := integral_trace_re h2
  rw [matFourierCoeff_zero_sub hF hC, h, sub_self, Matrix.trace_zero, Complex.zero_re,
    integral_eq_zero_iff_of_nonneg (fun t => ?_) (integrable_trace_re h2)] at h3
  · filter_upwards [h3] with t ht
    rw [Pi.zero_apply, trace_conjTranspose_mul_self_re] at ht
    ext i j
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ => sq_nonneg _).1 ht j (Finset.mem_univ j)
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).1 h4 i (Finset.mem_univ i)
    rw [sq_eq_zero_iff, norm_eq_zero, Matrix.sub_apply, sub_eq_zero] at h5
    exact h5
  · rw [Pi.zero_apply, trace_conjTranspose_mul_self_re]
    positivity

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Helson–Lowdenslager (1961), p. 204: if `A` is outer, then `A (1 + H) = A₀` and `C = A₀ᴴ A₀`, so
that (131) is an equality. Here the infimum (44) of the first paper, for `W = Aᴴ A`, is computed
from the limit `A₀` of the functions `A (1 + P)` (`IsOuter.szegoInf_eq`) and not from the element of
smallest norm, so that its uniqueness is not used. -/
private theorem integral_log_norm_det_of_isOuter {A : UnitAddCircle → Matrix n n ℂ} (hA : IsOuter A)
    (h0 : (matFourierCoeff A 0).det ≠ 0) :
    ∫ t, Real.log ‖(A t).det‖ ∂haarAddCircle = Real.log ‖(matFourierCoeff A 0).det‖ := by
  cases isEmpty_or_nonempty n
  · simp [Matrix.det_isEmpty]
  have hn : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨hdet, hlog, -⟩ := integrable_log_det_of_isHardyTwo hA.1 h0
  have h1 (t : UnitAddCircle) : Real.log ((A t)ᴴ * A t).det.re = 2 * Real.log ‖(A t).det‖ := by
    rw [det_conjTranspose_mul_self_re, Real.log_pow, Nat.cast_ofNat]
  have h2 := szegoInf_eq (W := fun t => (A t)ᴴ * A t)
    (integrable_mul_of_memLp (g := fun t => (A t)ᴴ) (fun i j => (hA.1.1 j i).star) hA.1.1)
    (hdet.mono fun t ht => posDef_conjTranspose_mul_self ht)
    ((hlog.const_mul 2).congr (ae_of_all _ fun t => (h1 t).symm))
  rw [hA.szegoInf_eq h0 (ae_of_all _ fun _ => rfl), Real.rpow_def_of_pos (norm_pos_iff.2 h0),
    Real.exp_eq_exp] at h2
  simp only [h1, integral_const_mul] at h2
  field_simp at h2
  linarith

/-- `2 ∫ log |det A| = log det C` for the constant `C = B₀ᴴ B₀` of the extremal problem for
`W = Aᴴ A` (Helson–Lowdenslager (1961), p. 204: "We have moreover `det C = exp ∫ log det W`"); here
`W = Bᴴ B` with `B = Xᴴ A` outer. -/
private theorem two_mul_integral_log_norm_det {q : ℕ} (e : Fin q ≃ n)
    {A : UnitAddCircle → Matrix n n ℂ} {B : UnitAddCircle → Matrix (Fin q) n ℂ} (hB : IsOuter B)
    (hrank : (matFourierCoeff B 0).rank = q)
    (hBA : ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = (A t)ᴴ * A t) :
    2 * ∫ t, Real.log ‖(A t).det‖ ∂haarAddCircle =
      Real.log ((matFourierCoeff B 0)ᴴ * matFourierCoeff B 0).det.re := by
  have h1 (M : Matrix (Fin q) n ℂ) : (Mᴴ * M).det.re = ‖(M.submatrix e.symm id).det‖ ^ 2 := by
    rw [← det_conjTranspose_mul_self_re, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
  have h2 : (matFourierCoeff (fun t => (B t).submatrix e.symm id) 0).det ≠ 0 := by
    refine det_ne_zero_of_rank_eq ?_
    rw [← Fintype.card_congr e, Fintype.card_fin]
    exact (Matrix.rank_submatrix (matFourierCoeff B 0) e.symm (Equiv.refl n)).trans hrank
  have h3 := integral_log_norm_det_of_isOuter (hB.submatrix e.symm) h2
  have h4 : ∀ᵐ t ∂haarAddCircle,
      Real.log ‖((B t).submatrix e.symm id).det‖ = Real.log ‖(A t).det‖ := by
    filter_upwards [hBA] with t ht
    have h5 := h1 (B t)
    rw [ht, det_conjTranspose_mul_self_re] at h5
    rw [(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h5]
  rw [integral_congr_ae h4] at h3
  rw [h3, h1, Real.log_pow, Nat.cast_ofNat]
  rfl

/-- The extremal problem for `W = Aᴴ A` (Helson–Lowdenslager (1961), p. 204): the limit
`F = A (1 + H) = A₀ + …` of functions `A (1 + P)`; "`(1 + H)ᴴ W (1 + H)` is a constant positive
semi-definite matrix `C`", and `log det C = ∫ log det W` (the source's (131) lacks the logarithms of
the determinants on the right). In the notation of `exists_innovation`, `F = X B₀` and `C = B₀ᴴ B₀`;
`C` is not singular because `A₀ = X̂ (0) B₀` is not. -/
private theorem exists_extremal {A : UnitAddCircle → Matrix n n ℂ} (hA : IsHardyTwo A)
    (h0 : (matFourierCoeff A 0).det ≠ 0) :
    ∃ (c : ℕ → ℤ →₀ Matrix n n ℂ) (F : UnitAddCircle → Matrix n n ℂ) (C : Matrix n n ℂ),
      (∀ N, ∀ k ∈ (c N).support, 0 < k) ∧
      TendstoLTwo (fun N t => A t * (1 + trigPoly (c N) t)) F ∧
      (∀ i j, MemLp (fun t => F t i j) 2 haarAddCircle) ∧
      matFourierCoeff F 0 = matFourierCoeff A 0 ∧ (∀ᵐ t ∂haarAddCircle, (F t)ᴴ * F t = C) ∧
      2 * ∫ t, Real.log ‖(A t).det‖ ∂haarAddCircle = Real.log C.det.re := by
  obtain ⟨q, X, hq, hX2, hX, hB, hrank, ⟨c, hc, hlim⟩, hH⟩ := exists_innovation hA.1
  obtain ⟨hXH, hXA⟩ := hH hA
  have hBo := isOuter_conjTranspose_mul hA.1 hX2 hX hB hc hlim
  obtain ⟨B₀, hB₀⟩ : ∃ M, M = matFourierCoeff (fun s => (X s)ᴴ * A s) 0 := ⟨_, rfl⟩
  rw [← hB₀] at hlim hrank
  have hF0 : matFourierCoeff A 0 = matFourierCoeff X 0 * B₀ := by
    rw [hB₀, ← hXH.matFourierCoeff_mul_zero hB, matFourierCoeff_congr_ae hXA]
  have hBA : ∀ᵐ t ∂haarAddCircle, ((X t)ᴴ * A t)ᴴ * ((X t)ᴴ * A t) = (A t)ᴴ * A t := by
    filter_upwards [hXA] with t ht
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ht]
  obtain ⟨e⟩ : Nonempty (Fin q ≃ n) := by
    refine ⟨Fintype.equivOfCardEq (le_antisymm (by rwa [Fintype.card_fin]) ?_)⟩
    calc Fintype.card n = (matFourierCoeff X 0 * B₀).rank := by
          rw [← hF0, Matrix.rank_of_det_ne_zero h0]
      _ ≤ B₀.rank := Matrix.rank_mul_le_right _ _
      _ = Fintype.card (Fin q) := by rw [hrank, Fintype.card_fin]
  refine ⟨c, fun t => X t * B₀, B₀ᴴ * B₀, hc, hlim, memLp_mul_continuous hX2 continuous_const, ?_,
    ?_, ?_⟩
  · rw [matFourierCoeff_mul_const (fun i j => (hX2 i j).integrable one_le_two), hF0]
  · filter_upwards [hX] with t ht
    rw [← conjTranspose_mul_mul_eq ht, Matrix.mul_one]
  · rw [two_mul_integral_log_norm_det e hBo (hB₀ ▸ hrank) hBA, hB₀]

/-- Helson–Lowdenslager (1961), Theorem 8: a square function `A ∈ H²` whose constant coefficient is
not singular is outer if and only if `∫ log |det A| = log |det Â (0)|`. -/
theorem isOuter_iff_integral_log_norm_det {A : UnitAddCircle → Matrix n n ℂ} (hA : IsHardyTwo A)
    (h0 : (matFourierCoeff A 0).det ≠ 0) :
    IsOuter A ↔
      ∫ t, Real.log ‖(A t).det‖ ∂haarAddCircle = Real.log ‖(matFourierCoeff A 0).det‖ := by
  refine ⟨fun h => integral_log_norm_det_of_isOuter h h0, fun h => ?_⟩
  obtain ⟨c, F, C, hc, hlim, hF, hF0, hFC, hlog⟩ := exists_extremal hA h0
  -- `A₀ᴴ A₀ ≤ C`, with equality of the determinants
  have hle := posSemidef_sub_conjTranspose_mul hF hFC
  have hdet : Real.log C.det.re =
      Real.log ((matFourierCoeff F 0)ᴴ * matFourierCoeff F 0).det.re := by
    rw [← hlog, h, hF0, det_conjTranspose_mul_self_re, Real.log_pow, Nat.cast_ofNat]
  have hCA := eq_of_log_det_eq (hF0 ▸ h0) hle hdet
  -- hence `A (1 + H) = A₀`
  refine ⟨hA, c, hc, hlim.congr_ae (fun N => ae_of_all _ fun t => rfl) ?_⟩
  rw [← hF0]
  exact ae_eq_of_eq_conjTranspose_mul hF hFC hCA

/-! ### Analytic range functions and Theorem 12 -/

/-- Helson–Lowdenslager (1961), §10: `A ∈ H²` is left-outer if the closure in `L²` of the functions
`(1 + P) A`, with `P` an analytic trigonometric polynomial without constant term, contains a
constant, that is, if the transposed function is outer. -/
def IsLeftOuter (A : UnitAddCircle → Matrix m n ℂ) : Prop := IsOuter fun t => (A t)ᵀ

/-- A range function, a function whose values are subspaces of `ℂᵐ`, is analytic if it is almost
everywhere the range of a function of `H²`. -/
def IsAnalyticRange (𝔥 : UnitAddCircle → Submodule ℂ (m → ℂ)) : Prop :=
  ∃ (k : ℕ) (A : UnitAddCircle → Matrix m (Fin k) ℂ), IsHardyTwo A ∧
    ∀ᵐ t ∂haarAddCircle, LinearMap.range (A t).mulVecLin = 𝔥 t

/-- A range function is conjugate analytic if it is almost everywhere the range of the adjoint of a
function of `H²`. -/
def IsConjAnalyticRange (𝔥 : UnitAddCircle → Submodule ℂ (m → ℂ)) : Prop :=
  ∃ (k : ℕ) (B : UnitAddCircle → Matrix (Fin k) m ℂ), IsHardyTwo B ∧
    ∀ᵐ t ∂haarAddCircle, LinearMap.range ((B t)ᴴ).mulVecLin = 𝔥 t

omit [DecidableEq n] in
/-- Helson–Lowdenslager (1961), proof of Theorem 12: "there is a left-outer function `B` such that
`W = B B*`, and `B` can be chosen to have `q` columns, where `q` is the rank of the canonical
process"; "`B` is of rank `q` at each point". Departure from the source: the
source shows the last assertion by restricting `B` to the complement of its null space; here the
rank of `B` is that of its constant coefficient (Theorem 9), which is `q` by the construction of
`B`. -/
private theorem exists_isLeftOuter {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyTwo A) :
    ∃ (q : ℕ) (B : UnitAddCircle → Matrix m (Fin q) ℂ), IsLeftOuter B ∧
      (∀ᵐ t ∂haarAddCircle, (B t).rank = q) ∧
      ∀ᵐ t ∂haarAddCircle, B t * (B t)ᴴ = A t * (A t)ᴴ := by
  obtain ⟨q, C, -, hC, hrank, hCA⟩ := exists_isOuter hA.transpose
  refine ⟨q, fun t => (C t)ᵀ, hC, ?_, ?_⟩
  · filter_upwards [hC.range_eq] with t ht
    rw [Matrix.rank_transpose, Matrix.rank, ht]
    exact hrank
  · filter_upwards [hCA] with t ht
    have h1 := congrArg Matrix.transpose ht
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    exact h1

omit [Fintype n] [DecidableEq n] in
/-- A left-outer function is in `H²`. -/
private theorem IsLeftOuter.isHardyTwo {A : UnitAddCircle → Matrix m n ℂ} (hA : IsLeftOuter A) :
    IsHardyTwo A :=
  hA.1.transpose

omit [DecidableEq m] in
/-- Helson–Lowdenslager (1961), (136)–(137): `Bᴴ B = Dᴴ D` for an outer function `D`, if `B` has `q`
columns and rank `q` at almost every point. "Since `W̃'` has full rank `D` must have exactly `q`
columns and be of full rank." -/
private theorem exists_isOuter_square {q : ℕ} {B : UnitAddCircle → Matrix m (Fin q) ℂ}
    (hB : IsHardyTwo B) (hrank : ∀ᵐ t ∂haarAddCircle, (B t).rank = q) :
    ∃ D : UnitAddCircle → Matrix (Fin q) (Fin q) ℂ, IsOuter D ∧ (matFourierCoeff D 0).det ≠ 0 ∧
      (∀ᵐ t ∂haarAddCircle, (D t).det ≠ 0) ∧ ∀ᵐ t ∂haarAddCircle, (D t)ᴴ * D t = (B t)ᴴ * B t := by
  obtain ⟨r, D, hr, hD, hD0, hDB⟩ := exists_isOuter hB
  rw [Fintype.card_fin] at hr
  have h1 : ∀ᵐ t ∂haarAddCircle, (D t).rank = q := by
    filter_upwards [hrank, hDB] with t h1 h2
    rw [← Matrix.rank_conjTranspose_mul_self, h2, Matrix.rank_conjTranspose_mul_self, h1]
  obtain ⟨t, ht⟩ := h1.exists
  obtain rfl : r = q := le_antisymm hr (ht ▸ (D t).rank_le_height)
  refine ⟨D, hD, det_ne_zero_of_rank_eq (by rw [hD0, Fintype.card_fin]), ?_, hDB⟩
  filter_upwards [h1] with t ht
  exact det_ne_zero_of_rank_eq (by rw [ht, Fintype.card_fin])

/-- The entries of `D⁻¹` are measurable if those of `D` are. -/
private theorem aestronglyMeasurable_inv {D : UnitAddCircle → Matrix n n ℂ}
    (hD : ∀ i j, AEStronglyMeasurable (fun t => D t i j) haarAddCircle) (i j : n) :
    AEStronglyMeasurable (fun t => (D t)⁻¹ i j) haarAddCircle := by
  have h1 : AEStronglyMeasurable (fun t => ((D t).updateRow j (Pi.single i 1)).det)
      haarAddCircle := by
    refine aestronglyMeasurable_det fun a b => ?_
    by_cases ha : a = j
    · subst ha
      simpa using aestronglyMeasurable_const
    · simpa [Matrix.updateRow_ne ha] using hD a b
  have h2 : AEStronglyMeasurable (fun t => ((D t).det)⁻¹) haarAddCircle :=
    (aestronglyMeasurable_det hD).aemeasurable.inv.aestronglyMeasurable
  refine (h2.mul h1).congr (ae_of_all _ fun t => ?_)
  simp [Matrix.inv_def, Matrix.adjugate_apply, Ring.inverse_eq_inv']

omit [DecidableEq m] in
/-- Helson–Lowdenslager (1961), (138): if `Dᴴ D = Bᴴ B` with `D` invertible, "it is obvious that
`V* V` is the identity matrix of order `q`" for `V = B D⁻¹`. -/
private theorem conjTranspose_mul_self_mul_inv {B : Matrix m n ℂ} {D : Matrix n n ℂ}
    (hD : D.det ≠ 0) (h : Dᴴ * D = Bᴴ * B) : (B * D⁻¹)ᴴ * (B * D⁻¹) = 1 := by
  have h1 : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.2 hD)
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, ← h, Matrix.mul_assoc, h1,
    Matrix.mul_one, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]

omit [DecidableEq m] [DecidableEq n] in
/-- Helson–Lowdenslager (1961), proofs of Theorems 12 and 13: `A Aᴴ = (V D) (V D)ᴴ` with `V`
analytic and isometric and `D` outer, square, of full rank; `B = V D` is left-outer with trivial
null space. (In the proof of Theorem 13 the source takes `V` left-outer, which it does not prove for
`V = B D⁻¹`, p. 208; only `Vᴴ V = 1` is needed.) -/
private theorem exists_isometry_mul {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyTwo A) :
    ∃ (q : ℕ) (V : UnitAddCircle → Matrix m (Fin q) ℂ)
      (D : UnitAddCircle → Matrix (Fin q) (Fin q) ℂ), IsHardyTwo V ∧
      (∀ᵐ t ∂haarAddCircle, (V t)ᴴ * V t = 1) ∧ IsOuter D ∧ (matFourierCoeff D 0).det ≠ 0 ∧
      (∀ᵐ t ∂haarAddCircle, (D t).det ≠ 0) ∧
      ∀ᵐ t ∂haarAddCircle, V t * D t * (V t * D t)ᴴ = A t * (A t)ᴴ := by
  classical
  obtain ⟨q, B, hB, hrank, hBA⟩ := exists_isLeftOuter hA
  obtain ⟨D, hD, hD0, hDt, hDB⟩ := exists_isOuter_square hB.isHardyTwo hrank
  have hV : ∀ᵐ t ∂haarAddCircle, (B t * (D t)⁻¹)ᴴ * (B t * (D t)⁻¹) = 1 := by
    filter_upwards [hDt, hDB] with t h1 h2
    exact conjTranspose_mul_self_mul_inv h1 h2
  have hVD : ∀ᵐ t ∂haarAddCircle, B t * (D t)⁻¹ * D t = B t := by
    filter_upwards [hDt] with t h1
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h1), Matrix.mul_one]
  refine ⟨q, fun t => B t * (D t)⁻¹, D, ?_, hV, hD, hD0, hDt, ?_⟩
  · -- if `D Q` approximates `1`, then `B Q` approximates `V`
    refine hD.isHardyTwo_of_bounded_mul (Matrix.rank_of_det_ne_zero hD0) (C := 1) (fun i j => ?_) ?_
      (hB.isHardyTwo.congr_ae (hVD.mono fun t ht => ht.symm))
    · simp only [Matrix.mul_apply]
      exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        (hB.isHardyTwo.1 i k).aestronglyMeasurable.mul
          (aestronglyMeasurable_inv (fun a b => (hD.1.1 a b).aestronglyMeasurable) k j)
    · filter_upwards [hV] with t ht
      exact norm_apply_le_one_of_conjTranspose_mul_self ht
  · filter_upwards [hVD, hBA] with t h1 h2
    rw [h1, h2]

omit [DecidableEq m] [DecidableEq n] in
/-- Helson–Lowdenslager (1961), p. 208: if `V Vᴴ = U Uᴴ`, `Vᴴ V = 1` and the null space of `U` is
trivial, "obviously `U* U` is the identity of order `q`". -/
private theorem conjTranspose_mul_self_eq_one {q r : ℕ} {U : Matrix m (Fin q) ℂ}
    {V : Matrix m (Fin r) ℂ} (hV : Vᴴ * V = 1) (hU : U.rank = q) (h : U * Uᴴ = V * Vᴴ) :
    Uᴴ * U = 1 := by
  have h1 : U * Uᴴ * (U * Uᴴ) = U * Uᴴ := by
    rw [h, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  have h2 : IsUnit (Uᴴ * U) := (Matrix.isUnit_iff_isUnit_det _).2 <| isUnit_iff_ne_zero.2 <|
    det_ne_zero_of_rank_eq (by rw [Matrix.rank_conjTranspose_mul_self, hU, Fintype.card_fin])
  have h3 : Uᴴ * U * (Uᴴ * U * (Uᴴ * U)) = Uᴴ * U * (Uᴴ * U * 1) := by
    simpa only [Matrix.mul_assoc, Matrix.mul_one] using congrArg (fun M => Uᴴ * (M * U)) h1
  exact h2.mul_left_cancel (h2.mul_left_cancel h3)

/-- Helson–Lowdenslager (1961), Theorem 12: every analytic range function is almost everywhere the
range of a left-outer function whose values are isometries (partial isometries in the source's
statement; its proof gives `Vᴴ V = 1`). -/
theorem IsAnalyticRange.exists_isometry {𝔥 : UnitAddCircle → Submodule ℂ (m → ℂ)}
    (h : IsAnalyticRange 𝔥) :
    ∃ (q : ℕ) (V : UnitAddCircle → Matrix m (Fin q) ℂ), IsLeftOuter V ∧
      (∀ᵐ t ∂haarAddCircle, (V t)ᴴ * V t = 1) ∧
      ∀ᵐ t ∂haarAddCircle, LinearMap.range (V t).mulVecLin = 𝔥 t := by
  obtain ⟨k, A, hA, hAh⟩ := h
  obtain ⟨q, V, D, hV, hVV, -, -, hD, hVD⟩ := exists_isometry_mul hA
  -- "since `V` is analytic, we can write `V V*` as `U U*`, where `U` is left-outer"
  obtain ⟨r, U, hU, hrank, hUV⟩ := exists_isLeftOuter hV
  refine ⟨r, U, hU, ?_, ?_⟩
  · filter_upwards [hVV, hrank, hUV] with t h1 h2 h3
    exact conjTranspose_mul_self_eq_one h1 h2 h3
  · filter_upwards [hAh, hVD, hUV, hD] with t h1 h2 h3 h4
    have h5 : LinearMap.range (V t * D t).mulVecLin = LinearMap.range (V t).mulVecLin := by
      refine le_antisymm (range_mul_le _ _) ?_
      refine (congrArg _ ?_).trans_le (range_mul_le (V t * D t) (D t)⁻¹)
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h4), Matrix.mul_one]
    rw [← range_mul_conjTranspose, h3, range_mul_conjTranspose, ← h5, ← range_mul_conjTranspose, h2,
      range_mul_conjTranspose, h1]

/-! ### The determinant on the range -/

/-- `Δ W`, the determinant of the restriction of the Hermitian matrix `W` to its range: the product
of its eigenvalues different from zero. -/
noncomputable def rangeDet (W : Matrix n n ℂ) : ℝ :=
  ((W.charpoly.roots.filter (· ≠ 0)).prod).re

/-- The roots different from zero of `X^k p` are those of `p`. -/
private theorem filter_roots_X_pow_mul {p : Polynomial ℂ} (hp : p ≠ 0) (k : ℕ) :
    (Polynomial.X ^ k * p).roots.filter (· ≠ 0) = p.roots.filter (· ≠ 0) := by
  rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hp),
    Polynomial.roots_X_pow, Multiset.filter_add, Multiset.nsmul_singleton, Multiset.filter_eq_nil.2,
    zero_add]
  intro a ha
  rw [Multiset.eq_of_mem_replicate ha]
  exact not_not.2 rfl

/-- If the roots of the characteristic polynomial of `M` are the real numbers `d_i`, then `Δ M` is
the product of those different from zero. -/
private theorem rangeDet_eq_prod {M : Matrix n n ℂ} {d : n → ℝ}
    (h : M.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((d i : ℝ) : ℂ))) :
    rangeDet M = ∏ i with d i ≠ 0, d i := by
  have h1 : M.charpoly.roots = Finset.univ.val.map fun i => ((d i : ℝ) : ℂ) := by
    rw [h, Polynomial.roots_prod _ _
      (Finset.prod_ne_zero_iff.2 fun i _ => Polynomial.X_sub_C_ne_zero _)]
    simp
  have h2 : (M.charpoly.roots.filter (· ≠ 0)).prod = ((∏ i with d i ≠ 0, d i : ℝ) : ℂ) := by
    rw [h1, Multiset.filter_map, Complex.ofReal_prod, Finset.prod, Finset.filter_val]
    simp
  rw [rangeDet, h2, Complex.ofReal_re]

/-- `Δ (V Y Vᴴ) = det Y` for an isometry `V` and a positive definite matrix `Y`. -/
theorem rangeDet_mul_mul_conjTranspose {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) {Y : Matrix n n ℂ}
    (hY : Y.PosDef) : rangeDet (V * Y * Vᴴ) = Y.det.re := by
  have h1 := Matrix.charpoly_mul_comm' V (Y * Vᴴ)
  rw [Matrix.mul_assoc Y, hV, Matrix.mul_one, ← Matrix.mul_assoc] at h1
  have h2 := congrArg (fun p : Polynomial ℂ => p.roots.filter (· ≠ 0)) h1
  simp only [filter_roots_X_pow_mul (Matrix.charpoly_monic _).ne_zero] at h2
  have h3 : rangeDet (V * Y * Vᴴ) = rangeDet Y := by rw [rangeDet, h2, rangeDet]
  rw [h3, rangeDet_eq_prod (d := hY.isHermitian.eigenvalues) hY.isHermitian.charpoly_eq,
    Finset.filter_true_of_mem fun i _ => (hY.eigenvalues_pos i).ne',
    hY.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  rfl

/-- `Δ (Rᵀ) = Δ R`. -/
theorem rangeDet_transpose (R : Matrix n n ℂ) : rangeDet Rᵀ = rangeDet R := by
  rw [rangeDet, rangeDet, Matrix.charpoly_transpose]

/-- `Δ (R²) = (Δ R)²` for a positive semidefinite matrix `R`. -/
theorem rangeDet_mul_self {R : Matrix n n ℂ} (hR : R.PosSemidef) :
    rangeDet (R * R) = rangeDet R ^ 2 := by
  have hH := hR.isHermitian
  have h2 : (R * R).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((hH.eigenvalues i ^ 2 : ℝ) : ℂ)) := by
    conv_lhs => rw [hH.spectral_theorem, ← map_mul, Unitary.conjStarAlgAut_apply,
      Matrix.charpoly_mul_comm, ← mul_assoc]
    simp [Matrix.diagonal_mul_diagonal, Matrix.charpoly_diagonal, pow_two]
  rw [rangeDet_eq_prod (d := hH.eigenvalues) hH.charpoly_eq, rangeDet_eq_prod h2, ← Finset.prod_pow]
  simp

/-! ### Theorem 13 and Sarason's Lemma 10.1 -/

omit [DecidableEq m] in
/-- Helson–Lowdenslager (1961), proof of Theorem 13: `V* W V` is positive definite if `V` is an
isometry with the same range as `W`. -/
private theorem posDef_conjTranspose_mul_mul {q : ℕ} {W : Matrix m m ℂ} {V : Matrix m (Fin q) ℂ}
    (hW : W.PosSemidef) (hV : Vᴴ * V = 1)
    (h : LinearMap.range V.mulVecLin = LinearMap.range W.mulVecLin) : (Vᴴ * W * V).PosDef ∧
      V * (Vᴴ * W * V) * Vᴴ = W := by
  -- `V Vᴴ` is the identity on the range of `W`
  have h1 : V * Vᴴ * W = W := by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨u, hu⟩ : W.mulVecLin v ∈ LinearMap.range V.mulVecLin := h ▸ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hu
    rw [← Matrix.mulVec_mulVec, ← hu, Matrix.mulVec_mulVec, Matrix.mul_assoc, hV, Matrix.mul_one]
  have h2 : W * (V * Vᴴ) = W := by
    have h3 := congrArg Matrix.conjTranspose h1
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hW.isHermitian.eq] at h3
  have h4 : V * (Vᴴ * W * V) * Vᴴ = W := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2]
  refine ⟨?_, h4⟩
  rw [(hW.conjTranspose_mul_mul_same V).posDef_iff_det_ne_zero]
  refine det_ne_zero_of_rank_eq (le_antisymm (Matrix.rank_le_card_width _) ?_)
  have h5 : V.rank = Fintype.card (Fin q) := by
    rw [← Matrix.rank_conjTranspose_mul_self, hV, Matrix.rank_one]
  have h6 : W.rank = V.rank := by rw [Matrix.rank, Matrix.rank, h]
  calc Fintype.card (Fin q) = (V * (Vᴴ * W * V) * Vᴴ).rank := by rw [h4, h6, h5]
    _ ≤ (V * (Vᴴ * W * V)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (Vᴴ * W * V).rank := Matrix.rank_mul_le_right _ _

omit [DecidableEq m] in
/-- The entries of `Vᴴ W V` are integrable if those of `W` are and `V` is bounded. -/
private theorem integrable_conjTranspose_mul_mul {q : ℕ} {W : UnitAddCircle → Matrix m m ℂ}
    {V : UnitAddCircle → Matrix m (Fin q) ℂ} {C : ℝ}
    (hW : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hV : ∀ i j, AEStronglyMeasurable (fun t => V t i j) haarAddCircle)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖V t i j‖ ≤ C) (i j : Fin q) :
    Integrable (fun t => ((V t)ᴴ * W t * V t) i j) haarAddCircle := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  have h1 : Integrable (fun t => star (V t b i) * W t b a) haarAddCircle :=
    (hW b a).bdd_mul (c := C) (hV b i).star (hC.mono fun t ht => by simpa using ht b i)
  refine (h1.bdd_mul (c := C) (hV a j) (hC.mono fun t ht => ht a j)).congr (ae_of_all _ fun t => ?_)
  exact mul_comm _ _

/-- Helson–Lowdenslager (1961), (140): `log Δ W = log det (D Dᴴ)` for `W = (V D) (V D)ᴴ`, `V` an
isometry. -/
private theorem log_rangeDet_mul_mul_conjTranspose {q : ℕ} {V : Matrix m (Fin q) ℂ}
    (hV : Vᴴ * V = 1) {D : Matrix (Fin q) (Fin q) ℂ} (hD : D.det ≠ 0) :
    Real.log (rangeDet (V * D * (V * D)ᴴ)) = 2 * Real.log ‖D.det‖ := by
  have h1 : (Dᴴ * D).det = (D * Dᴴ).det := Matrix.det_mul_comm _ _
  have h2 : (D * Dᴴ).PosDef := by
    have h3 : Dᴴ.det ≠ 0 := by rwa [Matrix.det_conjTranspose, star_ne_zero]
    simpa using posDef_conjTranspose_mul_self h3
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc V, ← Matrix.mul_assoc D, ← Matrix.mul_assoc V,
    rangeDet_mul_mul_conjTranspose hV h2, ← h1, det_conjTranspose_mul_self_re, Real.log_pow]
  norm_num

/-- `M Mᴴ` is the transpose of `Nᴴ N` for `M = Nᵀ`. -/
private theorem transpose_mul_conjTranspose_transpose {k n : Type*} [Fintype k]
    (N : Matrix k n ℂ) : Nᵀ * (Nᵀ)ᴴ = (Nᴴ * N)ᵀ := by
  rw [Matrix.transpose_mul]
  rfl

/-- Helson–Lowdenslager (1961), Theorem 13, the sufficiency: "the factorization theorem for
functions of full rank [10, 20] shows that `V* W V` has the form `B B*`", hence
`W = (V B) (V B)*`. -/
private theorem exists_mul_conjTranspose_eq {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef)
    (hrange : IsAnalyticRange (fun t => LinearMap.range (W t).mulVecLin))
    (hlog : Integrable (fun t => Real.log (rangeDet (W t))) haarAddCircle) :
    ∃ (k : ℕ) (A : UnitAddCircle → Matrix n (Fin k) ℂ), IsHardyTwo A ∧
      ∀ᵐ t ∂haarAddCircle, A t * (A t)ᴴ = W t := by
  obtain ⟨q, V, hV, hVV, hVW⟩ := hrange.exists_isometry
  have hV1 : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖V t i j‖ ≤ 1 :=
    hVV.mono fun t ht => norm_apply_le_one_of_conjTranspose_mul_self ht
  have hY : ∀ᵐ t ∂haarAddCircle, ((V t)ᴴ * W t * V t).PosDef ∧
      V t * ((V t)ᴴ * W t * V t) * (V t)ᴴ = W t := by
    filter_upwards [hW, hVV, hVW] with t h1 h2 h3
    exact posDef_conjTranspose_mul_mul h1 h2 h3
  have hlogY : Integrable (fun t => Real.log (((V t)ᴴ * W t * V t)ᵀ).det.re) haarAddCircle := by
    refine hlog.congr ?_
    filter_upwards [hVV, hY] with t h1 h2
    conv_lhs => rw [← h2.2]
    rw [rangeDet_mul_mul_conjTranspose h1 h2.1, Matrix.det_transpose]
  obtain ⟨B, hB, -, hBY, -⟩ := exists_isOuter_of_integrable_log_det
    (W := fun t => ((V t)ᴴ * W t * V t)ᵀ) (fun i j => integrable_conjTranspose_mul_mul hint
      (fun a b => (hV.isHardyTwo.1 a b).aestronglyMeasurable) hV1 j i)
    (hY.mono fun t ht => ht.1.transpose) hlogY
  refine ⟨q, fun t => V t * (B t)ᵀ, hV.isHardyTwo.bounded_mul hV1 hB.1.transpose, ?_⟩
  filter_upwards [hY, hBY] with t h1 h2
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (B t)ᵀ,
    transpose_mul_conjTranspose_transpose, h2, Matrix.transpose_transpose, ← Matrix.mul_assoc, h1.2]

/-- Helson–Lowdenslager (1961), Theorem 13: a positive semidefinite function `W` with integrable
entries is `A Aᴴ` for some `A ∈ H²` if and only if the range of `W` is an analytic range function
and `∫ log Δ W > −∞`. (`Δ W ≤ (1 + tr W)ⁿ`, so that the last condition is the integrability of
`log Δ W`.) -/
theorem exists_mul_conjTranspose_eq_iff {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) :
    (∃ (k : ℕ) (A : UnitAddCircle → Matrix n (Fin k) ℂ), IsHardyTwo A ∧
        ∀ᵐ t ∂haarAddCircle, A t * (A t)ᴴ = W t) ↔
      IsAnalyticRange (fun t => LinearMap.range (W t).mulVecLin) ∧
        Integrable (fun t => Real.log (rangeDet (W t))) haarAddCircle := by
  refine ⟨?_, fun h => exists_mul_conjTranspose_eq hint hW h.1 h.2⟩
  rintro ⟨k, A, hA, hAW⟩
  refine ⟨⟨k, A, hA, ?_⟩, ?_⟩
  · filter_upwards [hAW] with t ht
    rw [← ht, range_mul_conjTranspose]
  · obtain ⟨q, V, D, -, hV, hD, hD0, hDt, hVD⟩ := exists_isometry_mul hA
    refine ((integrable_log_det_of_isHardyTwo hD.1 hD0).2.1.const_mul 2).congr ?_
    filter_upwards [hAW, hV, hDt, hVD] with t h1 h2 h3 h4
    rw [← h1, ← h4, log_rangeDet_mul_mul_conjTranspose h2 h3]

/-- Sarason (1967), §10.2: a positive function `R` is factorable if it is `Bᴴ B` for an analytic
square-integrable function `B` (with any number of rows; by `IsFactorable.exists_isOuter`, as many
rows as columns suffice). -/
def IsFactorable (R : UnitAddCircle → Matrix n n ℂ) : Prop :=
  ∃ (k : ℕ) (B : UnitAddCircle → Matrix (Fin k) n ℂ), IsHardyTwo B ∧
    ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = R t

/-- The range of `(Bᵀ)ᴴ`, the complex conjugate of `B`, consists of the complex conjugates of the
elements of the range of `B`. -/
private theorem mem_range_conjTranspose_transpose {k m : Type*} [Fintype k] (B : Matrix m k ℂ)
    (v : m → ℂ) : v ∈ LinearMap.range ((Bᵀ)ᴴ).mulVecLin ↔ star v ∈ LinearMap.range B.mulVecLin := by
  have h1 (u : k → ℂ) : star (B.mulVec u) = ((Bᵀ)ᴴ).mulVec (star u) := by
    rw [Matrix.star_mulVec, ← Matrix.vecMul_transpose]
    rfl
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨star u, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, ← star_star u, ← h1, star_star, star_star]
  · rintro ⟨u, hu⟩
    refine ⟨star u, ?_⟩
    rw [Matrix.mulVecLin_apply, ← h1, ← Matrix.mulVecLin_apply, hu, star_star]

/-- The range of a Hermitian matrix `R` is that of `Bᴴ` if and only if the range of `Rᵀ` is that of
`Bᵀ`: complex conjugation. -/
private theorem range_conjTranspose_eq_iff {k m : Type*} [Fintype k] [Fintype m]
    {R : Matrix m m ℂ} (hR : R.IsHermitian) (B : Matrix k m ℂ) :
    LinearMap.range (Bᵀ).mulVecLin = LinearMap.range (Rᵀ).mulVecLin ↔
      LinearMap.range (Bᴴ).mulVecLin = LinearMap.range R.mulVecLin := by
  have h1 (v : m → ℂ) : v ∈ LinearMap.range (Bᴴ).mulVecLin ↔
      star v ∈ LinearMap.range (Bᵀ).mulVecLin := mem_range_conjTranspose_transpose Bᵀ v
  have h2 (v : m → ℂ) : v ∈ LinearMap.range R.mulVecLin ↔
      star v ∈ LinearMap.range (Rᵀ).mulVecLin := by
    rw [← mem_range_conjTranspose_transpose, Matrix.transpose_transpose, hR.eq]
  constructor
  · intro h
    ext v
    rw [h1, h2, h]
  · intro h
    ext v
    have h3 := SetLike.ext_iff.1 h (star v)
    rwa [h1, h2, star_star] at h3

/-- Sarason (1967), Lemma 10.1 (Helson–Lowdenslager's Theorem 13): a positive semidefinite function
`R` with integrable entries is factorable if and only if its range function is conjugate analytic
and `∫ log Δ R > −∞`. -/
theorem isFactorable_iff {R : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => R t i j) haarAddCircle)
    (hR : ∀ᵐ t ∂haarAddCircle, (R t).PosSemidef) :
    IsFactorable R ↔ IsConjAnalyticRange (fun t => LinearMap.range (R t).mulVecLin) ∧
      Integrable (fun t => Real.log (rangeDet (R t))) haarAddCircle := by
  have key := exists_mul_conjTranspose_eq_iff (W := fun t => (R t)ᵀ) (fun i j => hint j i)
    (hR.mono fun t ht => ht.transpose)
  simp only [rangeDet_transpose] at key
  have h1 : IsFactorable R ↔ ∃ (k : ℕ) (A : UnitAddCircle → Matrix n (Fin k) ℂ), IsHardyTwo A ∧
      ∀ᵐ t ∂haarAddCircle, A t * (A t)ᴴ = (R t)ᵀ := by
    constructor
    · rintro ⟨k, B, hB, hBR⟩
      refine ⟨k, fun t => (B t)ᵀ, hB.transpose, hBR.mono fun t ht => ?_⟩
      rw [transpose_mul_conjTranspose_transpose, ht]
    · rintro ⟨k, A, hA, hAR⟩
      refine ⟨k, fun t => (A t)ᵀ, hA.transpose, hAR.mono fun t ht => ?_⟩
      have h2 := transpose_mul_conjTranspose_transpose (A t)ᵀ
      rw [Matrix.transpose_transpose, ht] at h2
      exact (Matrix.transpose_injective h2).symm
  have h2 : IsConjAnalyticRange (fun t => LinearMap.range (R t).mulVecLin) ↔
      IsAnalyticRange fun t => LinearMap.range ((R t)ᵀ).mulVecLin := by
    constructor
    · rintro ⟨k, B, hB, hBR⟩
      refine ⟨k, fun t => (B t)ᵀ, hB.transpose, ?_⟩
      filter_upwards [hR, hBR] with t h1 h2
      exact (range_conjTranspose_eq_iff h1.isHermitian (B t)).2 h2
    · rintro ⟨k, A, hA, hAR⟩
      refine ⟨k, fun t => (A t)ᵀ, hA.transpose, ?_⟩
      filter_upwards [hR, hAR] with t h1 h2
      exact (range_conjTranspose_eq_iff h1.isHermitian (A t)ᵀ).1 h2
  rw [h1, h2, key]

end VectorValuedHarmonicAnalysis
