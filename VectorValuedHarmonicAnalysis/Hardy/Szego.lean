module

public import VectorValuedHarmonicAnalysis.Hardy.Outer
public import VectorValuedHarmonicAnalysis.Hardy.Jensen
public import VectorValuedHarmonicAnalysis.Hardy.GeometricMean
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Szegő's theorem for matrix-valued functions

Let `W` be a positive semidefinite function on the circle with values in the matrices of order `n`
and integrable entries. H. Helson and D. Lowdenslager, *Prediction theory and Fourier series in
several variables*, Acta Math. 99 (1958), 165–202, §5, prove:

* (Theorem 8, for absolutely continuous measures) `exp ((1/n) ∫ log det W)` is the infimum of
  `∫ (1/n) tr (Qᴴ W Q)` over the analytic trigonometric polynomials `Q` whose constant coefficient
  has determinant `1`; it is zero if `log det W` is not integrable (`szegoInf_eq`,
  `posDef_of_szegoInf_pos`); it is `|det B̂ (0)|^{2/n}` if `W = Bᴴ B` with `B` outer and
  `det B̂ (0) ≠ 0` (`IsOuter.szegoInf_eq`);
* (Theorem 9) `W = Bᴴ B` for some `B ∈ H²` with `det B̂ (0) ≠ 0` if and only if `log det W` is
  integrable; then `B` can be chosen outer, with `∫ log |det B| = log |det B̂ (0)|`
  (`exists_isOuter_of_integrable_log_det`, `integrable_log_det_of_isHardyTwo`).

The source writes the integrands in (44) and (55) as `tr ((A₀ + P)ᴴ (A₀ + P) W)`, which is
`tr (Q W Qᴴ)` for `Q = A₀ + P`, and `W = B Bᴴ`, and normalizes the trace; the statements here are
the transposed ones, with the usual trace. The infimum is written out in `szegoInf`. The integral of
a function that is not integrable is zero in Lean, so that "`∫ log det W > −∞`" is stated as: `W` is
positive definite almost everywhere and `log det W` is integrable. The singular part of a
matrix-valued measure, which does not change the infimum (the source, (53)), is not considered.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexOrder Topology

namespace VectorValuedHarmonicAnalysis

/-! ### Preliminaries -/

open scoped Matrix.Norms.Frobenius in
/-- `tr (Mᴴ M)` is the square of the Frobenius norm. -/
private theorem trace_conjTranspose_mul_self_eq_frobenius {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) : (Mᴴ * M).trace.re = ‖M‖ ^ 2 := by
  rw [trace_conjTranspose_mul_self_re, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by positivity), Finset.sum_comm]
  simp only [Real.rpow_ofNat]

open scoped Matrix.Norms.Frobenius in
/-- The Cauchy–Schwarz inequality `tr ((M N)ᴴ (M N)) ≤ tr (Mᴴ M) tr (Nᴴ N)`. -/
private theorem trace_conjTranspose_mul_self_mul_le {l m n : Type*} [Fintype l] [Fintype m]
    [Fintype n] (M : Matrix l m ℂ) (N : Matrix m n ℂ) :
    ((M * N)ᴴ * (M * N)).trace.re ≤ (Mᴴ * M).trace.re * (Nᴴ * N).trace.re := by
  simp only [trace_conjTranspose_mul_self_eq_frobenius, ← mul_pow]
  gcongr
  exact Matrix.frobenius_norm_mul M N

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `W = Bᴴ B`, then `log det W = 2 log |det B|`. -/
private theorem log_det_re_eq {B W : Matrix n n ℂ} (h : Bᴴ * B = W) :
    Real.log W.det.re = 2 * Real.log ‖B.det‖ := by
  rw [← h, det_conjTranspose_mul_self_re, Real.log_pow]
  norm_num

omit [DecidableEq n] in
/-- The entries of `Qᴴ W Q` are integrable if those of `W` are integrable and `Q` is continuous. -/
private theorem integrable_conjTranspose_mul_mul {W Q : UnitAddCircle → Matrix n n ℂ}
    (hW : ∀ i j, Integrable (fun t => W t i j) haarAddCircle) (hQ : Continuous Q) (i j : n) :
    Integrable (fun t => ((Q t)ᴴ * W t * Q t) i j) haarAddCircle :=
  integrable_mul_continuous (integrable_continuous_mul hQ.matrix_conjTranspose hW) hQ i j

/-- `det (W + ε) = ∏ (λ_i + ε)`, where `λ_i` are the eigenvalues of `W`. -/
private theorem det_add_smul_one_re {W : Matrix n n ℂ} (hW : W.IsHermitian) (ε : ℝ) :
    (W + ε • (1 : Matrix n n ℂ)).det.re = ∏ i, (hW.eigenvalues i + ε) := by
  have h : W + ε • (1 : Matrix n n ℂ) = cfc (fun s : ℝ => s + ε) W := by
    rw [cfc_add_const ε (fun s => s) W (ha := hW.isSelfAdjoint), cfc_id' ℝ W hW.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
  rw [h, det_cfc hW, ← Complex.ofReal_prod, Complex.ofReal_re]

omit [Fintype n] in
/-- The matrix `W + ε` is positive definite if `W` is positive semidefinite and `ε > 0`. -/
private theorem posDef_add_smul_one {W : Matrix n n ℂ} (hW : W.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (W + ε • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hW (Matrix.PosDef.one.smul hε)

/-- The determinant of `W + ε` is increasing in `ε ≥ 0` if `W` is positive semidefinite. -/
private theorem det_add_smul_one_re_mono {W : Matrix n n ℂ} (hW : W.PosSemidef) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    (W + ε • (1 : Matrix n n ℂ)).det.re ≤ (W + δ • (1 : Matrix n n ℂ)).det.re := by
  rw [det_add_smul_one_re hW.isHermitian, det_add_smul_one_re hW.isHermitian]
  exact Finset.prod_le_prod₀ (fun i _ => add_nonneg (hW.eigenvalues_nonneg i) hε)
    fun i _ => by gcongr

/-- `ε^n ≤ det (W + ε)` if `W` is positive semidefinite. -/
private theorem pow_le_det_add_smul_one_re {W : Matrix n n ℂ} (hW : W.PosSemidef) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ε ^ Fintype.card n ≤ (W + ε • (1 : Matrix n n ℂ)).det.re := by
  rw [det_add_smul_one_re hW.isHermitian, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => hε)
    fun i _ => le_add_of_nonneg_left (hW.eigenvalues_nonneg i)

omit [Fintype n] in
/-- The entries of `W + ε` are integrable if those of `W` are. -/
private theorem integrable_add_smul_one {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle) (ε : ℝ) (i j : n) :
    Integrable (fun t => (W t + ε • (1 : Matrix n n ℂ)) i j) haarAddCircle :=
  (hint i j).add (integrable_const _)

/-! ### The infimum, and (76) -/

/-- The infimum of `∫ (1/n) tr (Qᴴ W Q)` over the analytic trigonometric polynomials `Q` whose
constant coefficient has determinant `1`. -/
noncomputable def szegoInf (W : UnitAddCircle → Matrix n n ℂ) : ℝ :=
  ⨅ c : {c : ℤ →₀ Matrix n n ℂ // (∀ k ∈ c.support, 0 ≤ k) ∧ (c 0).det = 1},
    (∫ t, ((trigPoly c.1 t)ᴴ * W t * trigPoly c.1 t).trace.re ∂haarAddCircle) / Fintype.card n

/-- The constant polynomial `1` belongs to the set over which the infimum is taken. -/
private theorem nonempty_szego :
    Nonempty {c : ℤ →₀ Matrix n n ℂ // (∀ k ∈ c.support, 0 ≤ k) ∧ (c 0).det = 1} :=
  ⟨Finsupp.single 0 1, fun k hk => by
    rw [(Finsupp.mem_support_single k 0 _).1 hk |>.1], by simp⟩

/-- The infimum is at most its value at any polynomial. -/
private theorem szegoInf_le {W : UnitAddCircle → Matrix n n ℂ}
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) {c : ℤ →₀ Matrix n n ℂ}
    (hc : ∀ k ∈ c.support, 0 ≤ k) (h1 : (c 0).det = 1) :
    szegoInf W ≤ (∫ t, ((trigPoly c t)ᴴ * W t * trigPoly c t).trace.re ∂haarAddCircle) /
      Fintype.card n := by
  refine ciInf_le ⟨0, ?_⟩ (⟨c, hc, h1⟩ :
    {c : ℤ →₀ Matrix n n ℂ // (∀ k ∈ c.support, 0 ≤ k) ∧ (c 0).det = 1})
  rintro _ ⟨d, rfl⟩
  refine div_nonneg (integral_nonneg_of_ae ?_) (Nat.cast_nonneg _)
  filter_upwards [hW] with t ht
  exact (Complex.nonneg_iff.1 (ht.conjTranspose_mul_mul_same _).trace_nonneg).1

/-- Helson–Lowdenslager (1958), (76): if `W = Bᴴ B` with `B ∈ H²`, then
`|det B̂ (0)|^{2/n} ≤ ∫ (1/n) tr (Qᴴ W Q)` for every analytic polynomial `Q` with
`det Q̂ (0) = 1`. -/
theorem norm_det_rpow_le_szegoInf [Nonempty n] {W B : UnitAddCircle → Matrix n n ℂ}
    (hB : IsHardyTwo B) (hBW : ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = W t) :
    ‖(matFourierCoeff B 0).det‖ ^ (2 / Fintype.card n : ℝ) ≤ szegoInf W := by
  have := nonempty_szego (n := n)
  refine le_ciInf fun ⟨c, hc, h1⟩ => ?_
  have e : ∫ t, ((trigPoly c t)ᴴ * W t * trigPoly c t).trace.re ∂haarAddCircle =
      ∫ t, ((B t * trigPoly c t)ᴴ * (B t * trigPoly c t)).trace.re ∂haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards [hBW] with t ht
    rw [conjTranspose_mul_mul_eq ht]
  have h0 : matFourierCoeff (fun t => B t * trigPoly c t) 0 = matFourierCoeff B 0 * c 0 := by
    rw [hB.matFourierCoeff_mul_zero (isHardyTwo_trigPoly hc), matFourierCoeff_trigPoly]
  calc ‖(matFourierCoeff B 0).det‖ ^ (2 / Fintype.card n : ℝ)
      = ‖(matFourierCoeff B 0 * c 0).det‖ ^ (2 / Fintype.card n : ℝ) := by
        rw [Matrix.det_mul, h1, mul_one]
    _ ≤ ((matFourierCoeff B 0 * c 0)ᴴ * (matFourierCoeff B 0 * c 0)).trace.re / Fintype.card n :=
        norm_det_rpow_le_trace _
    _ ≤ _ := by
        rw [e, ← h0]
        gcongr
        exact trace_matFourierCoeff_zero_le
          (memLp_mul_continuous hB.1 (continuous_trigPoly_matrix c))

/-! ### Lemma 6 -/

/-- If `A (1 + P_N) → F` in `L²`, where `Fᴴ F = Cᴴ C` with a constant matrix `C`, then the infimum
for `W = Aᴴ A` is at most `(1/n) tr ((C D)ᴴ (C D))` if `det D = 1`: the polynomials `(1 + P_N) D`
belong to the set over which the infimum is taken (Helson–Lowdenslager (1958), pp. 190–191, 194). -/
private theorem szegoInf_le_trace_of_tendsto {m q : Type*} [Fintype m] [Fintype q]
    {W : UnitAddCircle → Matrix n n ℂ} {A F : UnitAddCircle → Matrix m n ℂ} {C : Matrix q n ℂ}
    (hA : ∀ i j, MemLp (fun t => A t i j) 2 haarAddCircle)
    (hAW : ∀ᵐ t ∂haarAddCircle, (A t)ᴴ * A t = W t)
    (hFC : ∀ᵐ t ∂haarAddCircle, (F t)ᴴ * F t = Cᴴ * C) {c : ℕ → ℤ →₀ Matrix n n ℂ}
    (hc : ∀ N, ∀ k ∈ (c N).support, 0 < k)
    (hlim : TendstoLTwo (fun N t => A t * (1 + trigPoly (c N) t)) F) {D : Matrix n n ℂ}
    (hD : D.det = 1) : szegoInf W ≤ ((C * D)ᴴ * (C * D)).trace.re / Fintype.card n := by
  choose d hd hd0 hdt using fun N => exists_trigPoly_eq_one_add_mul (hc N) D
  have hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef := by
    filter_upwards [hAW] with t ht
    exact ht ▸ Matrix.posSemidef_conjTranspose_mul_self _
  have h2 := (hlim.mul_continuous (continuous_const (y := D)) fun N =>
    memLp_mul_one_add hA (c N)).tendsto_integral_trace fun N =>
      memLp_mul_continuous (memLp_mul_one_add hA (c N)) continuous_const
  have e1 (N : ℕ) : ∫ t, ((A t * (1 + trigPoly (c N) t) * D)ᴴ *
      (A t * (1 + trigPoly (c N) t) * D)).trace.re ∂haarAddCircle =
      ∫ t, ((trigPoly (d N) t)ᴴ * W t * trigPoly (d N) t).trace.re ∂haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards [hAW] with t ht
    rw [conjTranspose_mul_mul_eq ht, hdt, Matrix.mul_assoc]
  have e2 : ∫ t, ((F t * D)ᴴ * (F t * D)).trace.re ∂haarAddCircle =
      ((C * D)ᴴ * (C * D)).trace.re := by
    rw [integral_congr_ae (g := fun _ => ((C * D)ᴴ * (C * D)).trace.re) ?_, integral_const,
      probReal_univ, one_smul]
    filter_upwards [hFC] with t ht
    rw [← conjTranspose_mul_mul_eq ht, ← conjTranspose_mul_mul_eq rfl]
  rw [e2] at h2
  refine ge_of_tendsto' (h2.div_const _) fun N => ?_
  rw [e1]
  exact szegoInf_le hW (hd N) (by rw [hd0, hD])

/-- If `C` is not injective, there are matrices `D` with determinant `1` for which `tr (Dᴴ Cᴴ C D)`
is as small as we please (Helson–Lowdenslager (1958), p. 190): the columns of `D` are a vector of
the kernel and multiples by `s` of vectors of the standard basis. -/
private theorem exists_det_eq_one_trace_le {q : Type*} [Fintype q] {C : Matrix q n ℂ} {v : n → ℂ}
    (hv : v ≠ 0) (hCv : C.mulVec v = 0) {s : ℝ} (hs : 0 < s) :
    ∃ D : Matrix n n ℂ, D.det = 1 ∧
      ((C * D)ᴴ * (C * D)).trace.re ≤ s ^ 2 * (Cᴴ * C).trace.re := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hv
  let d (j : n) : ℂ := if j = i₀ then (v i₀ * ∏ j ∈ Finset.univ.erase i₀, (s : ℂ))⁻¹ else s
  let U : Matrix n n ℂ := (1 : Matrix n n ℂ).updateCol i₀ v
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hU : U.det = v i₀ := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one, Module.End.one_apply]
  have hprod : ∏ j, d j = (v i₀)⁻¹ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
    have h1 : ∏ j ∈ Finset.univ.erase i₀, d j = ∏ j ∈ Finset.univ.erase i₀, (s : ℂ) :=
      Finset.prod_congr rfl fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj)
    have h2 : d i₀ = (v i₀ * ∏ j ∈ Finset.univ.erase i₀, (s : ℂ))⁻¹ := ite_eq_left rfl
    have h3 : ∏ j ∈ Finset.univ.erase i₀, (s : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => hs0
    rw [h1, h2, mul_inv, mul_assoc, inv_mul_cancel₀ h3, mul_one]
  refine ⟨U * Matrix.diagonal d, ?_, ?_⟩
  · rw [Matrix.det_mul, hU, Matrix.det_diagonal, hprod, mul_inv_cancel₀ hi₀]
  have hentry (i : q) (j : n) : ‖(C * (U * Matrix.diagonal d)) i j‖ ^ 2 ≤ s ^ 2 * ‖C i j‖ ^ 2 := by
    rw [← Matrix.mul_assoc, Matrix.mul_diagonal, Matrix.mul_apply]
    by_cases hj : j = i₀
    · have : ∑ k, C i k * U k j = 0 := by
        simpa [U, hj, Matrix.mulVec, dotProduct] using congrFun hCv i
      rw [this, zero_mul, norm_zero, zero_pow two_ne_zero]
      positivity
    · have : ∑ k, C i k * U k j = C i j := by
        simp [U, Matrix.updateCol_ne hj, Matrix.one_apply]
      rw [this, show d j = s from ite_eq_right hj, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hs.le, mul_pow, mul_comm]
  rw [trace_conjTranspose_mul_self_re, trace_conjTranspose_mul_self_re, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hentry i j

/-- "We assert that `C` is non-singular" (Helson–Lowdenslager (1958), p. 190). -/
private theorem card_le_rank_of_szegoInf_pos {q : Type*} [Fintype q]
    {W : UnitAddCircle → Matrix n n ℂ} {C : Matrix q n ℂ} (hpos : 0 < szegoInf W)
    (hle : ∀ D : Matrix n n ℂ, D.det = 1 →
      szegoInf W ≤ ((C * D)ᴴ * (C * D)).trace.re / Fintype.card n) :
    Fintype.card n ≤ C.rank := by
  by_contra! hlt
  have hker : LinearMap.ker C.mulVecLin ≠ ⊥ := by
    intro h
    have h1 := C.mulVecLin.finrank_range_add_finrank_ker
    rw [h, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at h1
    exact hlt.ne h1
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hlim : Tendsto (fun s : ℝ => s ^ 2 * (Cᴴ * C).trace.re / Fintype.card n)
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Continuous fun s : ℝ => s ^ 2 * (Cᴴ * C).trace.re / Fintype.card n := by fun_prop
    simpa using (h1.tendsto 0).mono_left nhdsWithin_le_nhds
  refine absurd hpos (not_lt.2 (ge_of_tendsto hlim ?_))
  filter_upwards [self_mem_nhdsWithin] with s hs
  obtain ⟨D, hD, hDs⟩ := exists_det_eq_one_trace_le hv0 hv hs
  refine (hle D hD).trans ?_
  gcongr

/-- A square matrix of rank `n` is invertible. -/
private theorem det_ne_zero_of_card_le_rank {M : Matrix n n ℂ} (h : Fintype.card n ≤ M.rank) :
    M.det ≠ 0 := by
  have h1 := Matrix.mulVec_surjective_iff_rank_eq_card.2 (le_antisymm M.rank_le_card_width h)
  exact ((Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_surjective_iff_isUnit.1 h1)).ne_zero

/-- The factorization furnished by a square matrix-valued function `X` with orthonormal columns, the
columns being indexed by any set (Helson–Lowdenslager (1958), (64)–(66)). In the source, with the
conventions used here, `X = A (1 + H) C^{−1/2}`, where `1 + H` is the limit of the polynomials
`1 + P_N` and `C` is the constant matrix `(1 + H)ᴴ W (1 + H)`. -/
private theorem exists_isOuter_of_innovation {q : Type*} [Finite q] [DecidableEq q] (e : q ≃ n)
    {A : UnitAddCircle → Matrix n n ℂ} {X : UnitAddCircle → Matrix n q ℂ}
    (hXX : ∀ᵐ t ∂haarAddCircle, (X t)ᴴ * X t = 1) (hB : IsOuter fun t => (X t)ᴴ * A t)
    (hrank : Fintype.card n ≤ (matFourierCoeff (fun t => (X t)ᴴ * A t) 0).rank) :
    ∃ B : UnitAddCircle → Matrix n n ℂ, IsOuter B ∧ (matFourierCoeff B 0).det ≠ 0 ∧
      ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = (A t)ᴴ * A t := by
  cases nonempty_fintype q
  refine ⟨_, hB.submatrix e.symm, det_ne_zero_of_card_le_rank ?_, ?_⟩
  · exact hrank.trans_eq (Matrix.rank_submatrix _ e.symm (Equiv.refl n)).symm
  · filter_upwards [hXX] with t ht
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (X t), (Matrix.mul_eq_one_comm_of_equiv e).1 ht, Matrix.one_mul]

/-- Helson–Lowdenslager (1958), Lemma 6: if the infimum is positive, then `W = Bᴴ B` for an outer
function `B` with `det B̂ (0) ≠ 0`; that `B` is outer is (77) and the remark after it, p. 194. -/
theorem exists_isOuter_of_szegoInf_pos {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) (hpos : 0 < szegoInf W) :
    ∃ B : UnitAddCircle → Matrix n n ℂ, IsOuter B ∧ (matFourierCoeff B 0).det ≠ 0 ∧
      ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = W t := by
  have hA := memLp_cfc_sqrt hint hW
  have hAW : ∀ᵐ t ∂haarAddCircle,
      (cfc Real.sqrt (W t))ᴴ * cfc Real.sqrt (W t) = W t := by
    filter_upwards [hW] with t ht
    rw [(posSemidef_cfc_sqrt (W t)).isHermitian.eq, cfc_sqrt_mul_self ht]
  obtain ⟨q, X, hq, hX, hXX, hB, hrank, ⟨c, hc, hlim⟩, -⟩ := exists_innovation hA
  have hFC : ∀ᵐ t ∂haarAddCircle,
      (X t * matFourierCoeff (fun s => (X s)ᴴ * cfc Real.sqrt (W s)) 0)ᴴ *
        (X t * matFourierCoeff (fun s => (X s)ᴴ * cfc Real.sqrt (W s)) 0) =
      (matFourierCoeff (fun s => (X s)ᴴ * cfc Real.sqrt (W s)) 0)ᴴ *
        matFourierCoeff (fun s => (X s)ᴴ * cfc Real.sqrt (W s)) 0 := by
    filter_upwards [hXX] with t ht
    rw [← conjTranspose_mul_mul_eq ht, Matrix.mul_one]
  have hcard := card_le_rank_of_szegoInf_pos hpos fun D hD =>
    szegoInf_le_trace_of_tendsto hA hAW hFC hc hlim hD
  have e : Fin q ≃ n := Fintype.equivOfCardEq <| by
    rw [Fintype.card_fin]
    exact le_antisymm hq (hcard.trans_eq hrank)
  obtain ⟨B, h1, h2, h3⟩ := exists_isOuter_of_innovation e hXX
    (isOuter_conjTranspose_mul hA hX hXX hB hc hlim) hcard
  refine ⟨B, h1, h2, ?_⟩
  filter_upwards [h3, hAW] with t h3 h4
  rw [h3, h4]

/-! ### The factorization (68) -/

/-- `tr e^Ψ` is bounded if `Ψ` is continuous. -/
private theorem exists_trace_exp_le {f : UnitAddCircle → Matrix n n ℂ} (hf : Continuous f) :
    ∃ K : ℝ, 0 < K ∧ ∀ t, (NormedSpace.exp (f t)).trace.re ≤ K := by
  have h1 : Continuous fun t => (NormedSpace.exp (f t)).trace.re :=
    Complex.continuous_re.comp (continuous_matrix_exp.comp hf).matrix_trace
  obtain ⟨K, hK⟩ := (isCompact_range h1).bddAbove
  exact ⟨max K 1, lt_max_of_lt_right one_pos, fun t => (hK ⟨t, rfl⟩).trans (le_max_left _ _)⟩

/-- `tr (Qᴴ Q) ≤ tr e^Ψ tr (Qᴴ e^{−Ψ} Q)`: a form of "the eigenvalues of `e^{−Ψ}` are bounded from
zero" (Helson–Lowdenslager (1958), p. 191). -/
private theorem trace_le_trace_exp_mul {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (Q : Matrix n n ℂ) :
    (Qᴴ * Q).trace.re ≤
      (NormedSpace.exp H).trace.re * (Qᴴ * NormedSpace.exp (-H) * Q).trace.re := by
  have h1 : NormedSpace.exp ((2⁻¹ : ℝ) • H) * (NormedSpace.exp ((2⁻¹ : ℝ) • -H) * Q) = Q := by
    rw [← Matrix.mul_assoc, smul_neg,
      mul_eq_one_comm.1 (exp_neg_mul_exp ((2⁻¹ : ℝ) • H)), Matrix.one_mul]
  have h2 := trace_conjTranspose_mul_self_mul_le (NormedSpace.exp ((2⁻¹ : ℝ) • H))
    (NormedSpace.exp ((2⁻¹ : ℝ) • -H) * Q)
  rwa [h1, conjTranspose_exp_half_mul_self hH,
    ← conjTranspose_mul_mul_eq (conjTranspose_exp_half_mul_self hH.neg)] at h2

/-- "`‖A‖² ≥ 1` for each analytic trigonometric polynomial `A` whose leading coefficient has
determinant one. Therefore the infimum is positive" for the weight `e^{−Ψ}` (Helson–Lowdenslager
(1958), p. 191). -/
private theorem szegoInf_exp_neg_pos [Nonempty n] {c : ℤ →₀ Matrix n n ℂ}
    (hc : ∀ t, (trigPoly c t).IsHermitian) :
    0 < szegoInf fun t => NormedSpace.exp (-trigPoly c t) := by
  have := nonempty_szego (n := n)
  have hcont := continuous_trigPoly_matrix c
  obtain ⟨K, hK0, hK⟩ := exists_trace_exp_le hcont
  refine lt_of_lt_of_le (inv_pos.2 hK0) (le_ciInf fun ⟨d, hd, hd1⟩ => ?_)
  have hd' := continuous_trigPoly_matrix d
  have h1 : 1 ≤ szegoInf fun _ : UnitAddCircle => (1 : Matrix n n ℂ) := by
    have h := norm_det_rpow_le_szegoInf (isHardyTwo_const (1 : Matrix n n ℂ))
      (W := fun _ => 1) (ae_of_all _ fun t => by simp)
    rwa [matFourierCoeff_const, ite_eq_left rfl, Matrix.det_one, norm_one, Real.one_rpow] at h
  have h2 := h1.trans (szegoInf_le (ae_of_all _ fun _ => Matrix.PosSemidef.one) hd hd1)
  have hint {g : UnitAddCircle → Matrix n n ℂ} (hg : Continuous g) :
      Integrable (fun t => (g t).trace.re) haarAddCircle :=
    integrable_haar_of_continuous (Complex.continuous_re.comp hg.matrix_trace)
  have h3 : ∫ t, ((trigPoly d t)ᴴ * 1 * trigPoly d t).trace.re ∂haarAddCircle ≤
      K * ∫ t, ((trigPoly d t)ᴴ * NormedSpace.exp (-trigPoly c t) *
        trigPoly d t).trace.re ∂haarAddCircle := by
    rw [← integral_const_mul]
    refine integral_mono (hint ((hd'.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      hd')) ((hint ((hd'.matrix_conjTranspose.matrix_mul
        (continuous_matrix_exp.comp hcont.neg)).matrix_mul hd')).const_mul K) fun t => ?_
    simp only [Matrix.mul_one]
    refine (trace_le_trace_exp_mul (hc t) _).trans (mul_le_mul_of_nonneg_right (hK t) ?_)
    exact (Complex.nonneg_iff.1 ((posDef_matrix_exp
      (hc t).neg).posSemidef.conjTranspose_mul_mul_same _).trace_nonneg).1
  rw [inv_le_iff_one_le_mul₀' hK0, ← mul_div_assoc]
  exact h2.trans (by gcongr)

/-- (70), (72) and the sequel (Helson–Lowdenslager (1958), p. 192): if `B` and `Q` are bounded
analytic functions with `Q B = 1` and `∫ log |det B| = 0`, then `|det Q̂ (0)| = 1`. -/
private theorem norm_det_matFourierCoeff_eq_one {B Q : UnitAddCircle → Matrix n n ℂ} {C C' : ℝ}
    (hB : IsHardyTwo B) (hBC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖B t i j‖ ≤ C) (hQ : IsHardyTwo Q)
    (hQC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖Q t i j‖ ≤ C')
    (hQB : ∀ᵐ t ∂haarAddCircle, Q t * B t = 1)
    (hlog : ∫ t, Real.log ‖(B t).det‖ ∂haarAddCircle = 0) :
    ‖(matFourierCoeff Q 0).det‖ = 1 := by
  have h1 : matFourierCoeff Q 0 * matFourierCoeff B 0 = 1 := by
    rw [← hQ.matFourierCoeff_mul_zero hB, matFourierCoeff_congr_ae hQB, matFourierCoeff_const,
      ite_eq_left rfl]
  have h2 : (matFourierCoeff Q 0).det * (matFourierCoeff B 0).det = 1 := by
    rw [← Matrix.det_mul, h1, Matrix.det_one]
  have hQ0 := left_ne_zero_of_mul_eq_one h2
  have hB0 := right_ne_zero_of_mul_eq_one h2
  have h3 : ∫ t, Real.log ‖(Q t).det‖ ∂haarAddCircle = 0 := by
    rw [← neg_eq_zero, ← integral_neg, ← hlog]
    refine integral_congr_ae ?_
    filter_upwards [hQB] with t ht
    have h := congrArg Matrix.det ht
    rw [Matrix.det_mul, Matrix.det_one] at h
    rw [eq_inv_of_mul_eq_one_left h, norm_inv, Real.log_inv, neg_neg]
  have h4 := (log_norm_det_le_integral_log_norm_det hB.isHardyOne hBC hB0).2.2
  have h5 := (log_norm_det_le_integral_log_norm_det hQ.isHardyOne hQC hQ0).2.2
  have h6 : Real.log ‖(matFourierCoeff Q 0).det‖ + Real.log ‖(matFourierCoeff B 0).det‖ = 0 := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hQ0) (norm_ne_zero_iff.2 hB0), ← norm_mul, h2, norm_one,
      Real.log_one]
  exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 hQ0) (by linarith)

/-- "By assumption `Ψ` satisfies (57)": if `Bᴴ B = e^{−Ψ}` and `∫ tr Ψ = 0`, then
`∫ log |det B| = 0` (Helson–Lowdenslager (1958), p. 192). -/
private theorem integral_log_norm_det_eq_zero {c : ℤ →₀ Matrix n n ℂ}
    (hc : ∀ t, (trigPoly c t).IsHermitian) (h0 : (c 0).trace = 0)
    {B : UnitAddCircle → Matrix n n ℂ}
    (hB : ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = NormedSpace.exp (-trigPoly c t)) :
    ∫ t, Real.log ‖(B t).det‖ ∂haarAddCircle = 0 := by
  have h1 : ∀ᵐ t ∂haarAddCircle,
      Real.log ‖(B t).det‖ = (2⁻¹ : ℝ) * -(trigPoly c t).trace.re := by
    filter_upwards [hB] with t ht
    have h2 := log_det_re_eq ht
    rw [det_matrix_exp (hc t).neg, Complex.ofReal_re, Real.log_exp, Matrix.trace_neg,
      Complex.neg_re] at h2
    linarith
  have h3 : ∫ t, (trigPoly c t).trace.re ∂haarAddCircle = 0 := by
    rw [integral_trace_re fun i j => integrable_haar_of_continuous
      ((continuous_trigPoly_matrix c).matrix_elem i j), matFourierCoeff_trigPoly, h0,
      Complex.zero_re]
  rw [integral_congr_ae h1, integral_const_mul, integral_neg, h3, neg_zero, mul_zero]

/-- Helson–Lowdenslager (1958), (69)–(72): if `∫ tr Ψ = 0`, then `e^Ψ = Q Qᴴ` for a bounded analytic
function `Q` with `|det Q̂ (0)| = 1`. -/
private theorem exists_bounded_analytic_norm_det_eq_one [Nonempty n] {c : ℤ →₀ Matrix n n ℂ}
    (hc : ∀ t, (trigPoly c t).IsHermitian) (h0 : (c 0).trace = 0) :
    ∃ (Q : UnitAddCircle → Matrix n n ℂ) (C : ℝ), IsHardyTwo Q ∧
      (∀ᵐ t ∂haarAddCircle, ∀ i j, ‖Q t i j‖ ≤ C) ∧ ‖(matFourierCoeff Q 0).det‖ = 1 ∧
      ∀ᵐ t ∂haarAddCircle, Q t * (Q t)ᴴ = NormedSpace.exp (trigPoly c t) := by
  have hcont := continuous_trigPoly_matrix c
  have hexp := continuous_matrix_exp.comp hcont
  obtain ⟨B, hB, hB0, hBW⟩ := exists_isOuter_of_szegoInf_pos
    (W := fun t => NormedSpace.exp (-trigPoly c t))
    (fun i j => integrable_haar_of_continuous
      ((continuous_matrix_exp.comp hcont.neg).matrix_elem i j))
    (ae_of_all _ fun t => (posDef_matrix_exp (hc t).neg).posSemidef) (szegoInf_exp_neg_pos hc)
  obtain ⟨K, -, hK⟩ := exists_trace_exp_le hcont
  obtain ⟨K', -, hK'⟩ := exists_trace_exp_le hcont.neg
  have hinv (t : UnitAddCircle) :
      NormedSpace.exp (trigPoly c t) * NormedSpace.exp (-trigPoly c t) = 1 :=
    mul_eq_one_comm.1 (exp_neg_mul_exp (trigPoly c t))
  have hBC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖B t i j‖ ≤ √K' := by
    filter_upwards [hBW] with t ht
    exact norm_apply_le_sqrt_of_trace_le (ht ▸ hK' t)
  have hQB : ∀ᵐ t ∂haarAddCircle, NormedSpace.exp (trigPoly c t) * (B t)ᴴ * B t = 1 := by
    filter_upwards [hBW] with t ht
    rw [Matrix.mul_assoc, ht, hinv]
  have hQQ : ∀ᵐ t ∂haarAddCircle, (NormedSpace.exp (trigPoly c t) * (B t)ᴴ) *
      (NormedSpace.exp (trigPoly c t) * (B t)ᴴ)ᴴ = NormedSpace.exp (trigPoly c t) := by
    filter_upwards [hQB] with t ht
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, ht,
      Matrix.one_mul, (hc t).exp.eq]
  have hQC : ∀ᵐ t ∂haarAddCircle, ∀ i j,
      ‖(NormedSpace.exp (trigPoly c t) * (B t)ᴴ) i j‖ ≤ √K := by
    filter_upwards [hQQ] with t ht i j
    rw [← norm_star, ← Matrix.conjTranspose_apply]
    refine norm_apply_le_sqrt_of_trace_le ?_ j i
    rw [Matrix.conjTranspose_conjTranspose, ht]
    exact hK t
  have hQm (i j : n) : AEStronglyMeasurable
      (fun t => (NormedSpace.exp (trigPoly c t) * (B t)ᴴ) i j) haarAddCircle :=
    (integrable_continuous_mul hexp (f := fun t => (B t)ᴴ)
      (fun i j => (hB.1.1 j i).star.integrable one_le_two) i j).aestronglyMeasurable
  -- "the inverse of `B` is the limit in `L²` of a sequence of analytic trigonometric polynomials"
  have hQ := hB.isHardyTwo_of_bounded_mul (Matrix.rank_of_isUnit _
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hB0))) hQm hQC
    ((isHardyTwo_const 1).congr_ae (hQB.mono fun t ht => ht.symm))
  exact ⟨_, _, hQ, hQC, norm_det_matFourierCoeff_eq_one hB.1 hBC hQ hQC hQB
    (integral_log_norm_det_eq_zero hc h0 hBW), hQQ⟩

/-- Helson–Lowdenslager (1958), (68): the exponential of a Hermitian trigonometric polynomial `Ψ`
with `∫ tr Ψ = 0` is `Q Qᴴ` for a bounded analytic function `Q` with `det Q̂ (0) = 1` (the
boundedness is in the proof, after (71)). -/
theorem exists_bounded_analytic_mul_conjTranspose_eq_exp {c : ℤ →₀ Matrix n n ℂ}
    (hc : ∀ t, (trigPoly c t).IsHermitian) (h0 : (c 0).trace = 0) :
    ∃ (Q : UnitAddCircle → Matrix n n ℂ) (C : ℝ), IsHardyTwo Q ∧
      (∀ᵐ t ∂haarAddCircle, ∀ i j, ‖Q t i j‖ ≤ C) ∧ (matFourierCoeff Q 0).det = 1 ∧
      ∀ᵐ t ∂haarAddCircle, Q t * (Q t)ᴴ = NormedSpace.exp (trigPoly c t) := by
  cases isEmpty_or_nonempty n
  · exact ⟨fun _ => 1, 0, isHardyTwo_const 1, ae_of_all _ fun _ i => isEmptyElim i,
      Matrix.det_isEmpty, ae_of_all _ fun _ => Subsingleton.elim _ _⟩
  obtain ⟨Q, C, hQ, hC, hdet, hQQ⟩ := exists_bounded_analytic_norm_det_eq_one hc h0
  -- multiplication by a constant of modulus `1` makes the determinant equal to `1`
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (matFourierCoeff Q 0).det⁻¹
    (Fintype.card_pos (α := n))
  have hz1 : ‖z‖ = 1 := by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg z) (Fintype.card_ne_zero (α := n))).1 ?_
    rw [← norm_pow, hz, norm_inv, hdet, inv_one]
  have hcoeff (k : ℤ) : matFourierCoeff (fun t => z • Q t) k = z • matFourierCoeff Q k := by
    ext i j
    exact fourierCoeff.const_mul _ z k
  refine ⟨fun t => z • Q t, C, ⟨fun i j => (hQ.1 i j).const_mul z, fun k hk => ?_⟩, ?_, ?_, ?_⟩
  · rw [hcoeff, hQ.2 k hk, smul_zero]
  · filter_upwards [hC] with t ht i j
    rw [Matrix.smul_apply, norm_smul, hz1, one_mul]
    exact ht i j
  · rw [hcoeff, Matrix.det_smul, hz, inv_mul_cancel₀]
    rw [← norm_ne_zero_iff, hdet]
    exact one_ne_zero
  · filter_upwards [hQQ] with t ht
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ht,
      Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]
    simp

/-! ### Theorem 8 -/

/-- "The last inequality remains true when `A` ranges merely over trigonometric polynomials": a
bounded analytic function is boundedly the limit of its Fejér means (Helson–Lowdenslager (1958), pp.
192–193). -/
private theorem szegoInf_le_of_bounded {W Q : UnitAddCircle → Matrix n n ℂ} {C : ℝ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) (hQ : IsHardyOne Q)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖Q t i j‖ ≤ C) (h1 : (matFourierCoeff Q 0).det = 1) :
    szegoInf W ≤ (∫ t, (Q t * (Q t)ᴴ * W t).trace.re ∂haarAddCircle) / Fintype.card n := by
  obtain ⟨ns, -, hns, hlim⟩ := exists_seq_tendsto_fejerCoeff hQ.1
  have hcont (N : ℕ) := continuous_trigPoly_matrix (fejerCoeff Q (ns N))
  have hbd (N : ℕ) (t : UnitAddCircle) (i j : n) : ‖trigPoly (fejerCoeff Q (ns N)) t i j‖ ≤ C :=
    norm_trigPoly_fejerCoeff_le hQ.1 (hC.mono fun t ht => ht i j) (hns N) t
  have h2 := tendsto_integral_trace_mul (M := ∑ _k : n, C * C)
    (fun N => (hcont N).matrix_mul (hcont N).matrix_conjTranspose) (fun N t i j => ?_)
    (hlim.mono fun t ht =>
      ((continuous_id.matrix_mul continuous_id.matrix_conjTranspose).tendsto _).comp ht) hint
  · refine ge_of_tendsto' (h2.div_const _) fun N => ?_
    simp only [← Matrix.trace_mul_cycle _ (W _)]
    exact szegoInf_le hW (nonneg_of_mem_support_fejerCoeff hQ.2 _)
      (by rw [fejerCoeff_zero _ (hns N), h1])
  · rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
    exact mul_le_mul (hbd N t i k) (hbd N t j k) (norm_nonneg _)
      ((norm_nonneg _).trans (hbd N t i k))

/-- `det (Qᴴ W Q) = |det Q|² det W`. -/
private theorem det_conjTranspose_mul_mul_re (Q W : Matrix n n ℂ) :
    (Qᴴ * W * Q).det.re = ‖Q.det‖ ^ 2 * W.det.re := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, mul_right_comm, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

/-- "The opposite inequality can be deduced directly from the one-dimensional version of Theorem 2"
(Helson–Lowdenslager (1958), p. 193): (58) for `Qᴴ W Q` and Jensen's inequality for `det Q`. -/
private theorem exp_integral_log_det_le_trace [Nonempty n] {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef)
    (hlog : Integrable (fun t => Real.log (W t).det.re) haarAddCircle) {c : ℤ →₀ Matrix n n ℂ}
    (hc : ∀ k ∈ c.support, 0 ≤ k) (h1 : (c 0).det = 1) :
    Real.exp ((∫ t, Real.log (W t).det.re ∂haarAddCircle) / Fintype.card n) ≤
      (∫ t, ((trigPoly c t)ᴴ * W t * trigPoly c t).trace.re ∂haarAddCircle) / Fintype.card n := by
  have hcont := continuous_trigPoly_matrix c
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hcont
  have h0 : (matFourierCoeff (trigPoly c) 0).det = 1 := by rw [matFourierCoeff_trigPoly, h1]
  obtain ⟨hne, hQlog, hQ⟩ := log_norm_det_le_integral_log_norm_det
    (isHardyTwo_trigPoly hc).isHardyOne (ae_of_all _ hC) (h0.symm ▸ one_ne_zero)
  rw [h0, norm_one, Real.log_one] at hQ
  have hV : ∀ᵐ t ∂haarAddCircle, ((trigPoly c t)ᴴ * W t * trigPoly c t).PosDef := by
    filter_upwards [hW, hne] with t ht hdet
    exact ht.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)))
  have hlogV : ∀ᵐ t ∂haarAddCircle, 2 * Real.log ‖(trigPoly c t).det‖ + Real.log (W t).det.re =
      Real.log ((trigPoly c t)ᴴ * W t * trigPoly c t).det.re := by
    filter_upwards [hW, hne] with t ht hdet
    rw [det_conjTranspose_mul_mul_re, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 hdet))
      (Complex.pos_iff.1 ht.det_pos).1.ne', Real.log_pow]
    norm_num
  refine le_trans ?_ (exp_integral_log_det_le (integrable_conjTranspose_mul_mul hint hcont) hV
    (((hQlog.const_mul 2).add hlog).congr hlogV))
  rw [← integral_congr_ae hlogV, integral_add (hQlog.const_mul 2) hlog, integral_const_mul]
  gcongr
  linarith

/-- Helson–Lowdenslager (1958), Theorem 8 (for an absolutely continuous measure): if `log det W` is
integrable, `exp ((1/n) ∫ log det W)` is the infimum of `∫ (1/n) tr (Qᴴ W Q)` over the analytic
polynomials `Q` with `det Q̂ (0) = 1`. -/
theorem szegoInf_eq [Nonempty n] {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef)
    (hlog : Integrable (fun t => Real.log (W t).det.re) haarAddCircle) :
    szegoInf W = Real.exp ((∫ t, Real.log (W t).det.re ∂haarAddCircle) / Fintype.card n) := by
  have := nonempty_szego (n := n)
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_ciInf fun c => exp_integral_log_det_le_trace hint hW hlog c.2.1 c.2.2)
  obtain ⟨c, hc, hc0, hle⟩ := exists_integral_exp_trigPoly_le hint hW hlog hε
  obtain ⟨Q, C, hQ, hC, hdet, hQQ⟩ := exists_bounded_analytic_mul_conjTranspose_eq_exp hc hc0
  refine (szegoInf_le_of_bounded hint (hW.mono fun t ht => ht.posSemidef) hQ.isHardyOne hC
    hdet).trans (le_of_eq_of_le ?_ hle)
  rw [integral_congr_ae (hQQ.mono fun t ht => congrArg (fun M => (M * W t).trace.re) ht)]

/-- `log det W ≤ tr W`. -/
private theorem log_det_le_trace [Nonempty n] {W : Matrix n n ℂ} (hW : W.PosDef) :
    Real.log W.det.re ≤ W.trace.re := by
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have h1 := (log_det_div_card_le_log_trace hW).trans
    (Real.log_le_self (div_nonneg (Complex.pos_iff.1 hW.trace_pos).1.le hn.le))
  exact (div_le_div_iff_of_pos_right hn).1 h1

/-- "`log (w + ε)` is summable for each `ε > 0`" (Helson–Lowdenslager (1958), p. 172). -/
private theorem integrable_log_det_add_smul_one [Nonempty n] {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t => Real.log (W t + ε • (1 : Matrix n n ℂ)).det.re) haarAddCircle := by
  have hV := integrable_add_smul_one hint ε
  have hmeas : AEStronglyMeasurable (fun t => Real.log (W t + ε • (1 : Matrix n n ℂ)).det.re)
      haarAddCircle := by
    have h1 := aestronglyMeasurable_det fun i j => (hV i j).aestronglyMeasurable
    exact (Real.measurable_log.comp_aemeasurable
      (Complex.measurable_re.comp_aemeasurable h1.aemeasurable)).aestronglyMeasurable
  refine ((integrable_const |Real.log (ε ^ Fintype.card n)|).add
    (integrable_trace_re hV)).mono' hmeas ?_
  filter_upwards [hW] with t ht
  have h1 := log_det_le_trace (posDef_add_smul_one ht hε)
  have h2 := Real.log_le_log (by positivity) (pow_le_det_add_smul_one_re ht hε.le)
  have h3 := (Complex.pos_iff.1 (posDef_add_smul_one ht hε).trace_pos).1
  have h4 := neg_abs_le (Real.log (ε ^ Fintype.card n))
  have h5 := abs_nonneg (Real.log (ε ^ Fintype.card n))
  rw [Pi.add_apply, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The infimum for `W + ε` is at least that for `W`. -/
private theorem szegoInf_le_szegoInf_add_smul_one {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    szegoInf W ≤ szegoInf fun t => W t + ε • (1 : Matrix n n ℂ) := by
  have := nonempty_szego (n := n)
  refine le_ciInf fun ⟨c, hc, h1⟩ => (szegoInf_le hW hc h1).trans ?_
  have hcont := continuous_trigPoly_matrix c
  refine div_le_div_of_nonneg_right (integral_mono
    (integrable_trace_re (integrable_conjTranspose_mul_mul hint hcont)) (integrable_trace_re
      (integrable_conjTranspose_mul_mul (integrable_add_smul_one hint ε) hcont)) fun t => ?_)
    (Nat.cast_nonneg _)
  have h2 : 0 ≤ ((trigPoly c t)ᴴ * (ε • (1 : Matrix n n ℂ)) * trigPoly c t).trace.re :=
    (Complex.nonneg_iff.1 (((Matrix.PosSemidef.one (n := n) (R := ℂ)).smul
      hε.le).conjTranspose_mul_mul_same _).trace_nonneg).1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  linarith

/-- Helson–Lowdenslager (1958), Theorem 8 (for an absolutely continuous measure): the infimum is
zero unless `W` is positive definite almost everywhere and `log det W` is integrable. -/
theorem posDef_of_szegoInf_pos {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) (hpos : 0 < szegoInf W) :
    (∀ᵐ t ∂haarAddCircle, (W t).PosDef) ∧
      Integrable (fun t => Real.log (W t).det.re) haarAddCircle := by
  cases isEmpty_or_nonempty n
  · exact absurd hpos (by simp [szegoInf])
  -- the limiting process of Lemma 1 of the source, carried out for the infimum of Theorem 8
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hε (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
  have hanti : Antitone fun k : ℕ => 1 / ((k : ℝ) + 1) := fun _ _ => Nat.one_div_le_one_div
  have hle1 (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 := by
    simpa using hanti (Nat.zero_le k)
  have hlim (t : UnitAddCircle) : Tendsto (fun k : ℕ =>
      (W t + (1 / ((k : ℝ) + 1)) • (1 : Matrix n n ℂ)).det.re) atTop (𝓝 (W t).det.re) := by
    have hcont : Continuous fun ε : ℝ => (W t + ε • (1 : Matrix n n ℂ)).det.re := by fun_prop
    have h := hcont.tendsto 0
    simp only [zero_smul, add_zero] at h
    exact h.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : ∀ᵐ t ∂haarAddCircle, ∀ k : ℕ,
      Real.log (W t + (1 / ((k : ℝ) + 1)) • (1 : Matrix n n ℂ)).det.re ≤
        (W t + (1 : ℝ) • (1 : Matrix n n ℂ)).trace.re := by
    filter_upwards [hW] with t ht k
    have h3 := Real.log_le_log (Complex.pos_iff.1 (posDef_add_smul_one ht (hε k)).det_pos).1
      (det_add_smul_one_re_mono ht (hε k).le (hle1 k))
    exact h3.trans (log_det_le_trace (posDef_add_smul_one ht one_pos))
  have hlower (k : ℕ) : Fintype.card n * Real.log (szegoInf W) ≤
      ∫ t, Real.log (W t + (1 / ((k : ℝ) + 1)) • (1 : Matrix n n ℂ)).det.re ∂haarAddCircle := by
    have h3 := szegoInf_le_szegoInf_add_smul_one hint hW (hε k)
    rw [szegoInf_eq (integrable_add_smul_one hint _) (hW.mono fun t ht =>
      posDef_add_smul_one ht (hε k)) (integrable_log_det_add_smul_one hint hW (hε k)),
      ← Real.log_le_iff_le_exp hpos, le_div_iff₀ hn] at h3
    rwa [mul_comm]
  obtain ⟨h1, h2, -⟩ := pos_and_integrable_log
    (hW.mono fun t ht k => (Complex.pos_iff.1 (posDef_add_smul_one ht (hε k)).det_pos).1)
    (hW.mono fun t ht i j hij => det_add_smul_one_re_mono ht (hε j).le (hanti hij))
    (ae_of_all _ hlim) (integrable_trace_re (integrable_add_smul_one hint 1))
    (fun k => integrable_log_det_add_smul_one hint hW (hε k)) hupper hlower
  refine ⟨?_, h2⟩
  filter_upwards [hW, h1] with t ht hdet
  refine ht.posDef_iff_det_ne_zero.2 fun h => ?_
  rw [h, Complex.zero_re] at hdet
  exact lt_irrefl _ hdet

/-! ### Theorem 9 -/

/-- "It is an elementary fact that `(det C)^{1/n} = inf tr (A₀ C A₀*)`" (Helson–Lowdenslager (1958),
p. 193): the infimum is attained at a multiple `D` of the inverse. -/
private theorem exists_det_eq_one_trace_eq [Nonempty n] {M : Matrix n n ℂ} (hM : M.det ≠ 0) :
    ∃ D : Matrix n n ℂ, D.det = 1 ∧
      ((M * D)ᴴ * (M * D)).trace.re / Fintype.card n = ‖M.det‖ ^ (2 / Fintype.card n : ℝ) := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq M.det (Fintype.card_pos (α := n))
  refine ⟨z • M⁻¹, ?_, ?_⟩
  · rw [Matrix.det_smul, hz, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_inv_cancel₀ hM]
  have h1 : M * z • M⁻¹ = z • 1 := by
    rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM)]
  have h2 : ‖M.det‖ ^ (2 / Fintype.card n : ℝ) = ‖z‖ ^ 2 := by
    rw [← hz, norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z),
      mul_div_cancel₀ _ hn, Real.rpow_two]
  rw [h1, h2, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, Matrix.trace_smul, Matrix.trace_one, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, smul_eq_mul, Complex.re_ofReal_mul, Complex.natCast_re,
    Complex.normSq_eq_norm_sq, mul_div_cancel_right₀ _ hn]

/-- Helson–Lowdenslager (1958), (75), pp. 193–194: if `W = Bᴴ B` with `B` outer and
`det B̂ (0) ≠ 0`, the infimum is `|det B̂ (0)|^{2/n}`. -/
theorem IsOuter.szegoInf_eq [Nonempty n] {W B : UnitAddCircle → Matrix n n ℂ}
    (hB : IsOuter B) (h0 : (matFourierCoeff B 0).det ≠ 0)
    (hBW : ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = W t) :
    szegoInf W = ‖(matFourierCoeff B 0).det‖ ^ (2 / Fintype.card n : ℝ) := by
  refine le_antisymm ?_ (norm_det_rpow_le_szegoInf hB.1 hBW)
  obtain ⟨D, hD, hDn⟩ := exists_det_eq_one_trace_eq h0
  obtain ⟨hB2, c, hc, hlim⟩ := hB
  exact (szegoInf_le_trace_of_tendsto (F := fun _ => matFourierCoeff B 0)
    (C := matFourierCoeff B 0) hB2.1 hBW (ae_of_all _ fun _ => rfl) hc hlim hD).trans_eq hDn

/-- Helson–Lowdenslager (1958), Theorem 9, the sufficiency: if `W` is positive definite almost
everywhere and `log det W` is integrable, then `W = Bᴴ B` for an outer function `B` with
`det B̂ (0) ≠ 0` and `∫ log |det B| = log |det B̂ (0)|`. -/
theorem exists_isOuter_of_integrable_log_det {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef)
    (hlog : Integrable (fun t => Real.log (W t).det.re) haarAddCircle) :
    ∃ B : UnitAddCircle → Matrix n n ℂ, IsOuter B ∧ (matFourierCoeff B 0).det ≠ 0 ∧
      (∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = W t) ∧
      ∫ t, Real.log ‖(B t).det‖ ∂haarAddCircle = Real.log ‖(matFourierCoeff B 0).det‖ := by
  cases isEmpty_or_nonempty n
  · refine ⟨fun _ => 1, ⟨isHardyTwo_const 1, fun _ => 0, fun N k hk => ?_, fun i => isEmptyElim i⟩,
      ?_, ae_of_all _ fun _ => Subsingleton.elim _ _, ?_⟩
    · simp at hk
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero
    · simp [Matrix.det_isEmpty]
  have hn : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hinf := szegoInf_eq hint hW hlog
  obtain ⟨B, hB, h0, hBW⟩ := exists_isOuter_of_szegoInf_pos hint
    (hW.mono fun t ht => ht.posSemidef) (hinf ▸ Real.exp_pos _)
  refine ⟨B, hB, h0, hBW, ?_⟩
  rw [integral_congr_ae (hBW.mono fun t ht => log_det_re_eq ht), integral_const_mul,
    hB.szegoInf_eq h0 hBW, Real.rpow_def_of_pos (norm_pos_iff.2 h0), Real.exp_eq_exp]
    at hinf
  field_simp at hinf
  linarith

/-- Helson–Lowdenslager (1958), Theorem 9, the necessity, with (76): if `B ∈ H²` and
`det B̂ (0) ≠ 0`, then `log |det B|` is integrable and `∫ log |det B| ≥ log |det B̂ (0)|`. -/
theorem integrable_log_det_of_isHardyTwo {B : UnitAddCircle → Matrix n n ℂ} (hB : IsHardyTwo B)
    (h0 : (matFourierCoeff B 0).det ≠ 0) :
    (∀ᵐ t ∂haarAddCircle, (B t).det ≠ 0) ∧
      Integrable (fun t => Real.log ‖(B t).det‖) haarAddCircle ∧
      Real.log ‖(matFourierCoeff B 0).det‖ ≤ ∫ t, Real.log ‖(B t).det‖ ∂haarAddCircle := by
  cases isEmpty_or_nonempty n
  · simp [Matrix.det_isEmpty]
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hint := integrable_mul_of_memLp (g := fun t => (B t)ᴴ) (fun i j => (hB.1 j i).star) hB.1
  have h1 := norm_det_rpow_le_szegoInf hB (ae_of_all _ fun t => rfl)
  obtain ⟨hpos, hlog⟩ := posDef_of_szegoInf_pos hint
    (ae_of_all _ fun t => Matrix.posSemidef_conjTranspose_mul_self _)
    ((Real.rpow_pos_of_pos (norm_pos_iff.2 h0) _).trans_le h1)
  rw [szegoInf_eq hint hpos hlog, Real.rpow_def_of_pos (norm_pos_iff.2 h0), Real.exp_le_exp] at h1
  simp only [log_det_re_eq rfl] at hlog h1
  rw [integral_const_mul] at h1
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hpos] with t ht hdet
    have h2 := ht.det_pos
    rw [Matrix.det_mul, hdet, mul_zero] at h2
    exact lt_irrefl _ h2
  · simpa using hlog.const_mul 2⁻¹
  · field_simp at h1
    linarith

end VectorValuedHarmonicAnalysis
