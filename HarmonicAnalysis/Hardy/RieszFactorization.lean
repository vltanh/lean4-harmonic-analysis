module

public import VectorValuedHarmonicAnalysis.Hardy.RangeFunction

/-!
# The Riesz factorization of matrix-valued functions of `H¹`

D. Sarason, *Generalized interpolation in H^∞*, Trans. Amer. Math. Soc. 127 (1967), 179–203, Theorem
4: every function `A ∈ H¹` is a product `A = A₁ A₂` of functions of `H²` such that
`A₂ᴴ A₂ = (Aᴴ A)^{1/2}` and `A₁ᴴ A₁ = A₂ A₂ᴴ`. Consequently, at almost every point,
`‖A₁‖_{S_{2p}}² = ‖A₂‖_{S_{2p}}² = ‖A‖_{S_p}` for every `0 < p < ∞`
(`complexSchattenNorm_sq_of_factorization`). Sarason considers functions whose values are operators
on one separable Hilbert space; here the values are matrices, and rectangular matrices are allowed.

* `IsFactorable.exists_isOuter` (Lemma 10.3): a factorable function is `Bᴴ B` with `B` outer.
* `isFactorable_cfc_sqrt` (Lemma 10.4): `(Aᴴ A)^{1/2}` is factorable if `A ∈ H¹`.
* `exists_mul_eq_of_isHardyOne` (Theorem 4).
* `complexSchattenNorm_sq_of_factorization`: the Schatten norms of the factors.

(Lemma 10.1 is `isFactorable_iff`; Lemmas 10.2 and 10.5 concern infinite dimension and are not
needed.)
-/

@[expose] public section

open MeasureTheory AddCircle Filter BanachProbability
open scoped ENNReal Matrix ComplexOrder Topology

namespace VectorValuedHarmonicAnalysis

/-! ### Preliminaries -/

section Preliminaries

variable {l m n : Type*}

/-- A function is in `H¹` if its columns are. -/
private theorem isHardyOne_of_columns {f : UnitAddCircle → Matrix l m ℂ}
    (h : ∀ j, IsHardyOne fun t => (f t).submatrix id fun _ : Unit => j) : IsHardyOne f :=
  ⟨fun i j => (h j).1 i (), fun k hk =>
    Matrix.ext fun i j => congrFun (congrFun ((h j).2 k hk) i) ()⟩

/-- A function is in `H²` if its columns are. -/
private theorem isHardyTwo_of_columns {f : UnitAddCircle → Matrix l m ℂ}
    (h : ∀ j, IsHardyTwo fun t => (f t).submatrix id fun _ : Unit => j) : IsHardyTwo f :=
  ⟨fun i j => (h j).1 i (), fun k hk =>
    Matrix.ext fun i j => congrFun (congrFun ((h j).2 k hk) i) ()⟩

/-- A bounded function of `H¹` is in `H²`. -/
private theorem IsHardyOne.isHardyTwo_of_bounded {f : UnitAddCircle → Matrix l m ℂ} {C : ℝ}
    (hf : IsHardyOne f) (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖f t i j‖ ≤ C) : IsHardyTwo f :=
  ⟨fun i j => .of_bound (hf.1 i j).aestronglyMeasurable C (hC.mono fun _ ht => ht i j), hf.2⟩

/-- Sarason (1967), end of the proof of Theorem 4: if `B` is outer and its constant coefficient is
surjective, a function `Q` with entries in `L²` such that `Q B` is analytic is analytic. There are
analytic polynomials `G_N` such that `B G_N → 1` in `L²`; by Schwarz's inequality,
`(Q B) G_N → Q` in `L¹`, and `(Q B) G_N` is analytic. (With a `1 × 1` outer function this is also
the "well-known property of outer functions" used at the end of the proof of Lemma 10.4, for which
Sarason cites Hoffman, p. 75. The case of a bounded `Q` is `IsOuter.isHardyTwo_of_bounded_mul`, the
argument of Helson–Lowdenslager (1961), p. 208.) -/
private theorem IsOuter.isHardyTwo_of_isHardyOne_mul [Fintype m] [Fintype n] [DecidableEq n]
    {B : UnitAddCircle → Matrix m n ℂ} (hB : IsOuter B)
    (h0 : (matFourierCoeff B 0).rank = Fintype.card m) {Q : UnitAddCircle → Matrix l m ℂ}
    (hQ : ∀ i j, MemLp (fun t => Q t i j) 2 haarAddCircle)
    (hQB : IsHardyOne fun t => Q t * B t) : IsHardyTwo Q := by
  classical
  obtain ⟨c, hc, hlim⟩ := hB.exists_tendsto_one h0
  refine ⟨hQ, fun k hk => ?_⟩
  have h1 := hlim.tendsto_matFourierCoeff_mul_left hQ (fun N =>
    memLp_mul_continuous hB.1.1 (continuous_trigPoly_matrix (c N))) k
  simp only [Matrix.mul_one] at h1
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun N => Eq.symm ?_)
  obtain ⟨D, hD⟩ := exists_bound_of_continuous (continuous_trigPoly_matrix (c N))
  simpa only [Matrix.mul_assoc] using
    (hQB.mul_bounded (isHardyTwo_trigPoly (hc N)).isHardyOne (ae_of_all _ hD)).1.2 k hk

end Preliminaries

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Sarason (1967), Lemma 10.3: a factorable function is `Bᴴ B` with `B` outer. The constant
coefficient of `B` is surjective, and `B` has at most as many rows as columns. (Proved in Helson's
book, cited by Sarason; here by Helson–Lowdenslager (1961), `exists_isOuter`. For Sarason's
definition of outer functions see Outer.lean.) -/
theorem IsFactorable.exists_isOuter {R : UnitAddCircle → Matrix n n ℂ} (hR : IsFactorable R) :
    ∃ (q : ℕ) (B : UnitAddCircle → Matrix (Fin q) n ℂ), q ≤ Fintype.card n ∧ IsOuter B ∧
      (matFourierCoeff B 0).rank = q ∧ ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = R t := by
  obtain ⟨k, A, hA, hAR⟩ := hR
  obtain ⟨q, B, hq, hB, hrank, hBA⟩ := VectorValuedHarmonicAnalysis.exists_isOuter hA
  refine ⟨q, B, hq, hB, hrank, ?_⟩
  filter_upwards [hBA, hAR] with t h1 h2
  rw [h1, h2]

/-! ### Lemma 10.4, bounded functions -/

omit [DecidableEq n] in
/-- The range of `R²` is that of `R`, for a Hermitian matrix `R`. -/
private theorem range_mul_self {R : Matrix n n ℂ} (hR : R.IsHermitian) :
    LinearMap.range (R * R).mulVecLin = LinearMap.range R.mulVecLin := by
  simpa only [hR.eq] using range_mul_conjTranspose R

omit [Fintype n] [DecidableEq n] in
/-- `Aᴴ A` is factorable if `A ∈ H²`. -/
private theorem IsHardyTwo.isFactorable {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyTwo A) :
    IsFactorable fun t => (A t)ᴴ * A t :=
  ⟨Fintype.card m, _, hA.submatrix (Fintype.equivFin m).symm id, ae_of_all _ fun t => by
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]⟩

/-- `(Aᴴ A)^{1/2}` is measurable if `A` is. -/
private theorem aestronglyMeasurable_cfc_sqrt {A : UnitAddCircle → Matrix m n ℂ}
    (hA : ∀ i j, AEStronglyMeasurable (fun t => A t i j) haarAddCircle) (i j : n) :
    AEStronglyMeasurable (fun t => cfc Real.sqrt ((A t)ᴴ * A t) i j) haarAddCircle :=
  aestronglyMeasurable_cfc (aestronglyMeasurable_mul (f := fun t => (A t)ᴴ)
    (fun i j => (hA j i).star) hA) (ae_of_all _ fun t =>
      Matrix.isHermitian_conjTranspose_mul_self (A t)) Real.continuous_sqrt i j

/-- The entries of `(Aᴴ A)^{1/2}` are bounded by the sum of the absolute values of those of `A`. -/
private theorem norm_cfc_sqrt_apply_le (A : Matrix m n ℂ) (i j : n) :
    ‖cfc Real.sqrt (Aᴴ * A) i j‖ ≤ ∑ a, ∑ b, ‖A a b‖ := by
  have h0 : 0 ≤ ∑ a, ∑ b, ‖A a b‖ := by positivity
  have h1 := norm_apply_sq_le_conjTranspose_mul_self (cfc Real.sqrt (Aᴴ * A)) i j
  rw [(posSemidef_cfc_sqrt _).isHermitian.eq,
    cfc_sqrt_mul_self (Matrix.posSemidef_conjTranspose_mul_self A),
    conjTranspose_mul_self_apply_self, Complex.ofReal_re] at h1
  refine le_of_sq_le_sq (h1.trans ?_) h0
  refine (Finset.sum_sq_le_sq_sum_of_nonneg fun a _ => norm_nonneg (A a j)).trans ?_
  gcongr with a
  exact Finset.single_le_sum (f := fun b => ‖A a b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- Sarason (1967), proof of Lemma 10.4, first part: "Consider first the case where `A` is bounded.
In this case, if `R = (Aᴴ A)^{1/2}`, then `R²` is factorable, and so it satisfies the necessary and
sufficient conditions of Lemma 10.1. From this it is immediate that `R` satisfies these conditions
also, and therefore `R` is factorable." -/
private theorem isFactorable_cfc_sqrt_of_bounded {A : UnitAddCircle → Matrix m n ℂ} {C : ℝ}
    (hA : IsHardyOne A) (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖A t i j‖ ≤ C) :
    IsFactorable fun t => cfc Real.sqrt ((A t)ᴴ * A t) := by
  have hA2 := hA.isHardyTwo_of_bounded hC
  have hint := integrable_conjTranspose_mul_self hA2.1
  have hpos : ∀ᵐ t ∂haarAddCircle, ((A t)ᴴ * A t).PosSemidef :=
    ae_of_all _ fun t => Matrix.posSemidef_conjTranspose_mul_self (A t)
  have hR (t : UnitAddCircle) : (cfc Real.sqrt ((A t)ᴴ * A t)).PosSemidef := posSemidef_cfc_sqrt _
  have hsq (t : UnitAddCircle) :
      cfc Real.sqrt ((A t)ᴴ * A t) * cfc Real.sqrt ((A t)ᴴ * A t) = (A t)ᴴ * A t :=
    cfc_sqrt_mul_self (Matrix.posSemidef_conjTranspose_mul_self (A t))
  obtain ⟨⟨k, B, hB, hrange⟩, hlog⟩ := (isFactorable_iff hint hpos).1 hA2.isFactorable
  refine (isFactorable_iff (fun i j => (memLp_cfc_sqrt hint hpos i j).integrable one_le_two)
    (ae_of_all _ hR)).2 ⟨⟨k, B, hB, ?_⟩, (hlog.const_mul 2⁻¹).congr (ae_of_all _ fun t => ?_)⟩
  · filter_upwards [hrange] with t ht
    rw [ht, ← range_mul_self (hR t).isHermitian, hsq]
  · simp only
    rw [← hsq t, rangeDet_mul_self (hR t).isHermitian, hsq t, Real.log_pow]
    push_cast
    ring

/-! ### Lemma 10.4, the general case -/

/-- "By a classical theorem of Szegő": if `w` is positive and integrable and `log w` is integrable,
then `w = |h|²` for an outer function `h` with `ĥ (0) ≠ 0`. This is Theorem 9 of
Helson–Lowdenslager (1958) for `1 × 1` matrices. -/
private theorem exists_isOuter_norm_sq_eq {w : UnitAddCircle → ℝ} (h0 : ∀ t, 0 < w t)
    (hw : Integrable w haarAddCircle)
    (hlog : Integrable (fun t => Real.log (w t)) haarAddCircle) :
    ∃ h : UnitAddCircle → Matrix Unit Unit ℂ, IsOuter h ∧
      (matFourierCoeff h 0).rank = Fintype.card Unit ∧
      ∀ᵐ t ∂haarAddCircle, ‖h t () ()‖ ^ 2 = w t := by
  obtain ⟨h, hh, hdet, hhw, -⟩ := exists_isOuter_of_integrable_log_det
    (W := fun t => Matrix.diagonal fun _ : Unit => (w t : ℂ)) (fun _ _ => hw.ofReal)
    (ae_of_all _ fun t => Matrix.PosDef.diagonal fun _ => by simpa using h0 t)
    (by simpa using hlog)
  refine ⟨h, hh, Matrix.rank_of_det_ne_zero hdet, ?_⟩
  filter_upwards [hhw] with t ht
  have h1 := congrFun (congrFun ht ()) ()
  rw [conjTranspose_mul_self_apply_self, Matrix.diagonal_apply_eq] at h1
  simpa using Complex.ofReal_injective h1

/-- The weight `1/N` where `N ≥ 1`, and `1` elsewhere, satisfies the conditions of Szegő's theorem,
if `N` is integrable. -/
private theorem integrable_weight {N : UnitAddCircle → ℝ} (hN0 : ∀ t, 0 ≤ N t)
    (hN : Integrable N haarAddCircle) :
    Integrable (fun t => (max 1 (N t))⁻¹) haarAddCircle ∧
      Integrable (fun t => Real.log (max 1 (N t))⁻¹) haarAddCircle := by
  have hm : AEMeasurable (fun t => (max 1 (N t))⁻¹) haarAddCircle :=
    (aemeasurable_const.max hN.aemeasurable).inv
  have h1 (t : UnitAddCircle) : 1 ≤ max 1 (N t) := le_max_left _ _
  refine ⟨.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun t => ?_),
    hN.mono' (Real.measurable_log.comp_aemeasurable hm).aestronglyMeasurable
      (ae_of_all _ fun t => ?_)⟩
  · rw [Real.norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans (h1 t)))]
    exact inv_le_one_of_one_le₀ (h1 t)
  · rw [Real.log_inv, norm_neg, Real.norm_of_nonneg (Real.log_nonneg (h1 t))]
    refine (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le (h1 t))).trans ?_
    rw [sub_le_iff_le_add]
    exact max_le (le_add_of_nonneg_left (hN0 t)) (le_add_of_nonneg_right zero_le_one)

/-- `((z² A)ᴴ (z² A))^{1/2} = |z|² (Aᴴ A)^{1/2}`. -/
private theorem cfc_sqrt_sq_smul (z : ℂ) (A : Matrix m n ℂ) :
    cfc Real.sqrt ((z ^ 2 • A)ᴴ * (z ^ 2 • A)) =
      ((‖z‖ ^ 2 : ℝ) : ℂ) • cfc Real.sqrt (Aᴴ * A) := by
  refine (eq_cfc_sqrt ((posSemidef_cfc_sqrt _).smul ?_) ?_).symm
  · exact_mod_cast sq_nonneg ‖z‖
  · rw [Matrix.smul_mul, Matrix.mul_smul,
      cfc_sqrt_mul_self (Matrix.posSemidef_conjTranspose_mul_self A), Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    rw [star_pow, Complex.star_def, ← mul_pow, Complex.conj_mul']
    push_cast
    ring

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- The product of `h²` and a function of `H¹`, where `h` is a bounded analytic scalar function, is
in `H¹`. -/
private theorem IsHardyOne.sq_smul {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyOne A)
    {h : UnitAddCircle → Matrix Unit Unit ℂ} (hh : IsHardyTwo h) {C : ℝ}
    (hC : ∀ᵐ t ∂haarAddCircle, ‖h t () ()‖ ≤ C) :
    IsHardyOne fun t => h t () () ^ 2 • A t := by
  have hC' : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖h t i j‖ ≤ C := hC.mono fun t ht _ _ => ht
  refine isHardyOne_of_columns fun j => ?_
  refine (((hA.submatrix id fun _ : Unit => j).mul_bounded hh.isHardyOne hC').1.mul_bounded
    hh.isHardyOne hC').1.congr_ae (ae_of_all _ fun t => Matrix.ext fun a b => ?_)
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.smul_apply, id, smul_eq_mul,
    Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit, pow_two]
  exact (mul_assoc _ _ _).trans (mul_comm _ _)

omit [Fintype n] [DecidableEq n] in
/-- Sarason (1967), end of the proof of Lemma 10.4: let `h` be an outer scalar function with
`ĥ (0) ≠ 0` and `B₀ ∈ H²`. If the entries of `B = h⁻¹ B₀` are in `L²`, then `B ∈ H²`. -/
private theorem IsHardyTwo.inv_smul {k : Type*} {B₀ : UnitAddCircle → Matrix k n ℂ}
    (hB₀ : IsHardyTwo B₀) {h : UnitAddCircle → Matrix Unit Unit ℂ} (hh : IsOuter h)
    (h0 : (matFourierCoeff h 0).rank = Fintype.card Unit)
    (hne : ∀ᵐ t ∂haarAddCircle, h t () () ≠ 0)
    (hB : ∀ i j, MemLp (fun t => ((h t () ())⁻¹ • B₀ t) i j) 2 haarAddCircle) :
    IsHardyTwo fun t => (h t () ())⁻¹ • B₀ t := by
  refine isHardyTwo_of_columns fun j => hh.isHardyTwo_of_isHardyOne_mul h0 (fun i _ => hB i j) ?_
  refine (hB₀.submatrix id fun _ : Unit => j).isHardyOne.congr_ae ?_
  filter_upwards [hne] with t ht
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.smul_apply, id, smul_eq_mul,
    Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit]
  rw [mul_right_comm, inv_mul_cancel₀ ht, one_mul]

/-- Sarason (1967), proof of Lemma 10.4, second part: if `h` is an outer scalar function,
`|h|² ≤ 1`, and `h² A` is bounded, then `(Aᴴ A)^{1/2}` is factorable. "The operator function `h² A`
is then bounded and analytic, and so `|h|² (Aᴴ A)^{1/2}` is factorable by what we just proved.
Therefore, there is an analytic operator function `B₀` such that `|h|² (Aᴴ A)^{1/2} = B₀ᴴ B₀`.
Setting `B = h⁻¹ B₀`, we have `(Aᴴ A)^{1/2} = Bᴴ B`, and it only remains to show that `B` is
analytic." -/
private theorem isFactorable_cfc_sqrt_of_isOuter {A : UnitAddCircle → Matrix m n ℂ}
    (hA : IsHardyOne A) {h : UnitAddCircle → Matrix Unit Unit ℂ} (hh : IsOuter h)
    (h0 : (matFourierCoeff h 0).rank = Fintype.card Unit)
    (hne : ∀ᵐ t ∂haarAddCircle, h t () () ≠ 0) (h1 : ∀ᵐ t ∂haarAddCircle, ‖h t () ()‖ ≤ 1)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖(h t () () ^ 2 • A t) i j‖ ≤ 1) :
    IsFactorable fun t => cfc Real.sqrt ((A t)ᴴ * A t) := by
  obtain ⟨k, B₀, hB₀, hBA⟩ := isFactorable_cfc_sqrt_of_bounded (hA.sq_smul hh.1 h1) hC
  have hBB : ∀ᵐ t ∂haarAddCircle, ((h t () ())⁻¹ • B₀ t)ᴴ * ((h t () ())⁻¹ • B₀ t) =
      cfc Real.sqrt ((A t)ᴴ * A t) := by
    filter_upwards [hBA, hne] with t ht htne
    rw [cfc_sqrt_sq_smul] at ht
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, ht, smul_smul, smul_smul]
    convert one_smul ℂ (cfc Real.sqrt ((A t)ᴴ * A t)) using 2
    rw [Complex.star_def, Complex.conj_mul', norm_inv]
    push_cast
    rw [← mul_pow, inv_mul_cancel₀ (by simpa using htne), one_pow]
  have hA1 (i : m) (j : n) := (hA.1 i j).aestronglyMeasurable
  have hN : Integrable (fun t => ∑ a, ∑ b, ‖A t a b‖) haarAddCircle :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hA.1 a b).norm
  refine ⟨k, _, hB₀.inv_smul hh h0 hne (memLp_of_conjTranspose_mul_self (fun i j => ?_)
    (fun j => ?_) hBB), hBB⟩
  · exact (hh.1.1 () ()).aestronglyMeasurable.inv₀.mul (hB₀.1 i j).aestronglyMeasurable
  · exact hN.mono' (aestronglyMeasurable_cfc_sqrt hA1 j j)
      (ae_of_all _ fun t => norm_cfc_sqrt_apply_le (A t) j j)

/-- Sarason (1967), Lemma 10.4: if `A ∈ H¹`, then `(Aᴴ A)^{1/2}` is factorable. (The source's lemma
is for operator-valued functions whose values have finite rank almost everywhere.) -/
theorem isFactorable_cfc_sqrt {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyOne A) :
    IsFactorable fun t => cfc Real.sqrt ((A t)ᴴ * A t) := by
  -- the norm of `A (z)`: the operator norm in the source, here the sum of the absolute values of
  -- the entries (any norm will do)
  let N (t : UnitAddCircle) : ℝ := ∑ a, ∑ b, ‖A t a b‖
  have hN0 (t : UnitAddCircle) : 0 ≤ N t := by positivity
  have hN : Integrable N haarAddCircle :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hA.1 a b).norm
  have hpos (t : UnitAddCircle) : 0 < max 1 (N t) := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨hw, hlog⟩ := integrable_weight hN0 hN
  obtain ⟨h, hh, h0, hhw⟩ := exists_isOuter_norm_sq_eq (fun t => inv_pos.2 (hpos t)) hw hlog
  refine isFactorable_cfc_sqrt_of_isOuter hA hh h0 ?_ ?_ ?_
  · filter_upwards [hhw] with t ht h1
    rw [h1, norm_zero, zero_pow two_ne_zero] at ht
    exact (inv_pos.2 (hpos t)).ne ht
  · filter_upwards [hhw] with t ht
    refine (sq_le_one_iff₀ (norm_nonneg _)).1 (ht.trans_le ?_)
    exact inv_le_one_of_one_le₀ (le_max_left _ _)
  · filter_upwards [hhw] with t ht i j
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow, ht, inv_mul_le_one₀ (hpos t)]
    refine le_trans ?_ (le_max_right _ _)
    exact (Finset.single_le_sum (f := fun b => ‖A t i b‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun a => ∑ b, ‖A t a b‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))

/-! ### Theorem 4 -/

/-- The partial isometry `J` of the polar decomposition `A = J R`, `R = (Aᴴ A)^{1/2} = Mᴴ M`, for
a matrix `M` with linearly independent rows: `J = A R⁺`, where `R⁺ = Mᴴ (M Mᴴ)⁻² M` is the inverse
of `R` on its range and zero on the orthogonal complement. This formula takes the place of the
"standard argument" of the source for the measurability of `J`. -/
private noncomputable def polarFactor {q : Type*} [Fintype q] [DecidableEq q] (A : Matrix m n ℂ)
    (M : Matrix q n ℂ) : Matrix m n ℂ :=
  A * (Mᴴ * ((M * Mᴴ)⁻¹ * (M * Mᴴ)⁻¹) * M)

section Polar

variable {q : Type*} [Fintype q] [DecidableEq q] {A : Matrix m n ℂ} {M : Matrix q n ℂ}

omit [Fintype m] [DecidableEq n] in
/-- `J Mᴴ = A Mᴴ (M Mᴴ)⁻¹`. -/
private theorem polarFactor_mul_conjTranspose (hM : IsUnit (M * Mᴴ).det) :
    polarFactor A M * Mᴴ = A * Mᴴ * (M * Mᴴ)⁻¹ := by
  rw [polarFactor, Matrix.mul_assoc, Matrix.mul_assoc _ M, Matrix.mul_assoc Mᴴ,
    Matrix.nonsing_inv_mul_cancel_right _ _ hM, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The polar decomposition `A = J R`, for `R = Mᴴ M` with `R² = Aᴴ A`. -/
private theorem polarFactor_mul_eq (hM : IsUnit (M * Mᴴ).det)
    (h : Aᴴ * A = Mᴴ * M * (Mᴴ * M)) : polarFactor A M * (Mᴴ * M) = A := by
  -- `A (1 - Mᴴ (M Mᴴ)⁻¹ M) = 0`, as `A` vanishes on the null space of `M`
  classical
  let P : Matrix n n ℂ := 1 - Mᴴ * (M * Mᴴ)⁻¹ * M
  have hMP : M * P = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hM, Matrix.one_mul, sub_self]
  have hAP : A * P = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Aᴴ, h]
    simp only [Matrix.mul_assoc, hMP, Matrix.mul_zero]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hAP
  rw [← Matrix.mul_assoc, polarFactor_mul_conjTranspose hM, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc Mᴴ]
  exact hAP.symm

omit [DecidableEq n] in
/-- `Jᴴ J A₂ᴴ = A₂ᴴ`, the equality from which (15) gives `A₁ᴴ A₁ = A₂ A₂ᴴ`. In the source, because
`Jᴴ J` is the projection onto the closure of the range of `A₂ᴴ`; here by computation. -/
private theorem polarFactor_conjTranspose_mul_mul (hM : IsUnit (M * Mᴴ).det)
    (h : Aᴴ * A = Mᴴ * M * (Mᴴ * M)) :
    (polarFactor A M)ᴴ * polarFactor A M * Mᴴ = Mᴴ := by
  have hG : ((M * Mᴴ)⁻¹)ᴴ = (M * Mᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have h1 : Aᴴ * (A * Mᴴ) = Mᴴ * (M * Mᴴ) * (M * Mᴴ) := by
    rw [← Matrix.mul_assoc, h]
    simp only [Matrix.mul_assoc]
  rw [Matrix.mul_assoc, polarFactor_mul_conjTranspose hM, polarFactor, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc _ Aᴴ, ← Matrix.mul_assoc Aᴴ, h1, Matrix.mul_nonsing_inv_cancel_right _ _ hM]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG]
  rw [Matrix.mul_assoc Mᴴ, Matrix.mul_assoc _ M, ← Matrix.mul_assoc M, Matrix.mul_assoc _ _ (_ * _),
    Matrix.nonsing_inv_mul_cancel_left _ _ hM, Matrix.nonsing_inv_mul _ hM, Matrix.mul_one]

/-- The factor `A₁ = J A₂ᴴ` satisfies `A = A₁ A₂` and, by (15) of the source,
`A₁ᴴ A₁ = A₂ Jᴴ J A₂ᴴ = A₂ A₂ᴴ`. -/
private theorem polarFactor_factorization (hM : IsUnit (M * Mᴴ).det)
    (h : Mᴴ * M = cfc Real.sqrt (Aᴴ * A)) :
    polarFactor A M * Mᴴ * M = A ∧
      (polarFactor A M * Mᴴ)ᴴ * (polarFactor A M * Mᴴ) = M * Mᴴ := by
  have h2 : Aᴴ * A = Mᴴ * M * (Mᴴ * M) := by
    rw [h, cfc_sqrt_mul_self (Matrix.posSemidef_conjTranspose_mul_self A)]
  refine ⟨by rw [Matrix.mul_assoc, polarFactor_mul_eq hM h2], ?_⟩
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (polarFactor A M)ᴴ, polarFactor_conjTranspose_mul_mul hM h2]

end Polar

/-- An outer function whose constant coefficient is surjective is surjective almost everywhere, by
Helson–Lowdenslager (1961), Theorem 9. -/
private theorem IsOuter.isUnit_det_mul_conjTranspose {q : ℕ}
    {B : UnitAddCircle → Matrix (Fin q) n ℂ} (hB : IsOuter B)
    (h0 : (matFourierCoeff B 0).rank = q) :
    ∀ᵐ t ∂haarAddCircle, IsUnit (B t * (B t)ᴴ).det := by
  filter_upwards [hB.range_eq] with t ht
  refine isUnit_iff_ne_zero.2 (det_ne_zero_of_rank_eq ?_)
  rw [Matrix.rank_self_mul_conjTranspose, Fintype.card_fin, Matrix.rank, ht]
  exact h0

/-- Sarason (1967), "Completion of the proof of Theorem 4", with `𝒲 = ℂ^q`, `q ≤ n`, in place of a
subspace of `ℂⁿ`: `R = (Aᴴ A)^{1/2}` is `A₂ᴴ A₂` with `A₂` outer, and `A₁ = J A₂ᴴ`, where `A = J R`
is the polar decomposition. The entries of `A₁` are in `L²` because `A₁ᴴ A₁ = A₂ A₂ᴴ`. -/
private theorem exists_mul_eq_of_isHardyOne_fin {A : UnitAddCircle → Matrix m n ℂ}
    (hA : IsHardyOne A) :
    ∃ (q : ℕ) (A₁ : UnitAddCircle → Matrix m (Fin q) ℂ) (A₂ : UnitAddCircle → Matrix (Fin q) n ℂ),
      q ≤ Fintype.card n ∧ IsHardyTwo A₁ ∧ IsHardyTwo A₂ ∧ ∀ᵐ t ∂haarAddCircle,
        A t = A₁ t * A₂ t ∧ (A₂ t)ᴴ * A₂ t = cfc Real.sqrt ((A t)ᴴ * A t) ∧
          (A₁ t)ᴴ * A₁ t = A₂ t * (A₂ t)ᴴ := by
  obtain ⟨q, A₂, hq, hA₂, hrank, hR⟩ := (isFactorable_cfc_sqrt hA).exists_isOuter
  have hunit := hA₂.isUnit_det_mul_conjTranspose hrank
  let A₁ (t : UnitAddCircle) : Matrix m (Fin q) ℂ := polarFactor (A t) (A₂ t) * (A₂ t)ᴴ
  have hfact : ∀ᵐ t ∂haarAddCircle, A₁ t * A₂ t = A t ∧ (A₁ t)ᴴ * A₁ t = A₂ t * (A₂ t)ᴴ := by
    filter_upwards [hunit, hR] with t h1 h2
    exact polarFactor_factorization h1 h2
  have hstar (i : n) (j : Fin q) : MemLp (fun t => (A₂ t)ᴴ i j) 2 haarAddCircle :=
    (hA₂.1.1 j i).star
  -- `A₁ = J A₂ᴴ` is measurable
  have hm (i : m) (j : Fin q) : AEStronglyMeasurable (fun t => A₁ t i j) haarAddCircle := by
    have hA2 (i j) := (hA₂.1.1 i j).aestronglyMeasurable
    have hA2' (i j) := (hstar i j).aestronglyMeasurable
    have hG := aestronglyMeasurable_inv (aestronglyMeasurable_mul hA2 hA2')
    exact aestronglyMeasurable_mul (aestronglyMeasurable_mul
      (fun i j => (hA.1 i j).aestronglyMeasurable) (aestronglyMeasurable_mul
        (aestronglyMeasurable_mul hA2' (aestronglyMeasurable_mul hG hG)) hA2)) hA2' i j
  have hA₁ := memLp_of_conjTranspose_mul_self hm
    (fun j => integrable_mul_of_memLp hA₂.1.1 hstar j j) (hfact.mono fun t ht => ht.2)
  refine ⟨q, A₁, A₂, hq, hA₂.isHardyTwo_of_isHardyOne_mul (by rw [hrank, Fintype.card_fin]) hA₁
    (hA.congr_ae (hfact.mono fun t ht => ht.1.symm)), hA₂.1, ?_⟩
  filter_upwards [hfact, hR] with t h1 h2
  exact ⟨h1.1.symm, h2, h1.2⟩

/-- Sarason (1967), Theorem 4, in finite dimension: a function `A ∈ H¹` is a product `A = A₁ A₂` of
functions of `H²` such that `A₂ᴴ A₂ = (Aᴴ A)^{1/2}` and `A₁ᴴ A₁ = A₂ A₂ᴴ`. -/
theorem exists_mul_eq_of_isHardyOne {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyOne A) :
    ∃ (A₁ : UnitAddCircle → Matrix m n ℂ) (A₂ : UnitAddCircle → Matrix n n ℂ), IsHardyTwo A₁ ∧
      IsHardyTwo A₂ ∧ ∀ᵐ t ∂haarAddCircle, A t = A₁ t * A₂ t ∧
        (A₂ t)ᴴ * A₂ t = cfc Real.sqrt ((A t)ᴴ * A t) ∧ (A₁ t)ᴴ * A₁ t = A₂ t * (A₂ t)ᴴ := by
  obtain ⟨q, A₁, A₂, hq, hA₁, hA₂, h⟩ := exists_mul_eq_of_isHardyOne_fin hA
  -- an isometry `E` of `ℂ^q` into `ℂⁿ`
  let e : Fin q ↪ n := (Fin.castLEEmb hq).trans (Fintype.equivFin n).symm.toEmbedding
  let E : Matrix n (Fin q) ℂ := (1 : Matrix n n ℂ).submatrix id e
  have hE : Eᴴ * E = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    exact (Matrix.submatrix_mul_equiv 1 1 e (Equiv.refl n) e).trans
      (by rw [Matrix.mul_one, Matrix.submatrix_one e e.injective])
  refine ⟨fun t => A₁ t * Eᴴ, fun t => E * A₂ t, hA₁.mul_const _, hA₂.const_mul _, ?_⟩
  filter_upwards [h] with t ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ, hE, Matrix.one_mul, h1]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ, hE, Matrix.one_mul, h2]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ _ Eᴴ, h3, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

/-! ### The Schatten norms of the factors -/

/-- The Schatten norms of `A` depend only on `Aᴴ A`. -/
private theorem complexSchattenNorm_congr {l : Type*} [Fintype l] {A : Matrix m n ℂ}
    {B : Matrix l n ℂ} (h : Aᴴ * A = Bᴴ * B) (q : ℝ≥0∞) :
    complexSchattenNorm q A = complexSchattenNorm q B := by
  simp only [complexSchattenNorm, complexSingularValue, h]

/-- `‖A‖_{S_{2p}}² = ‖Aᴴ A‖_{S_p}`. -/
private theorem complexSchattenNorm_two_mul_sq {p : ℝ} (hp : 0 < p) (A : Matrix m n ℂ) :
    complexSchattenNorm (ENNReal.ofReal (2 * p)) A ^ 2 =
      complexSchattenNorm (ENNReal.ofReal p) (Aᴴ * A) := by
  rw [← complexSchattenNorm_conjTranspose_mul_self (by simp [hp])]
  congr 1
  rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_comm,
    ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

/-- The Schatten norms of the factors of Sarason's theorem:
`‖A₁‖_{S_{2p}}² = ‖A₂‖_{S_{2p}}² = ‖A‖_{S_p}`. -/
theorem complexSchattenNorm_sq_of_factorization {p : ℝ} (hp : 0 < p) {A A₁ : Matrix m n ℂ}
    {A₂ : Matrix n n ℂ} (h₂ : A₂ᴴ * A₂ = cfc Real.sqrt (Aᴴ * A)) (h₁ : A₁ᴴ * A₁ = A₂ * A₂ᴴ) :
    complexSchattenNorm (ENNReal.ofReal (2 * p)) A₁ ^ 2 =
        complexSchattenNorm (ENNReal.ofReal p) A ∧
      complexSchattenNorm (ENNReal.ofReal (2 * p)) A₂ ^ 2 =
        complexSchattenNorm (ENNReal.ofReal p) A := by
  have h3 : complexSchattenNorm (ENNReal.ofReal (2 * p)) A₂ ^ 2 =
      complexSchattenNorm (ENNReal.ofReal p) A := by
    rw [complexSchattenNorm_two_mul_sq hp, h₂]
    refine complexSchattenNorm_congr ?_ _
    rw [(posSemidef_cfc_sqrt _).isHermitian.eq,
      cfc_sqrt_mul_self (Matrix.posSemidef_conjTranspose_mul_self A)]
  refine ⟨?_, h3⟩
  rw [← h3, ← complexSchattenNorm_conjTranspose _ A₂]
  simp only [complexSchattenNorm_two_mul_sq hp, h₁, Matrix.conjTranspose_conjTranspose]

end VectorValuedHarmonicAnalysis
