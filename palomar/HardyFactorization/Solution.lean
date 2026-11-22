module

public import HarmonicAnalysis.Hardy.RieszFactorization

/-!
# Solution: Szegő and Riesz factorization of matrix-valued functions on the circle

The statements of `palomar/HardyFactorization/Challenge.lean`, word for word, proved from the
library. The library uses the Schatten norms of BanachProbability, which are those of the Challenge
by definition (`complexSchattenNorm_eq`).
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexOrder Topology

namespace HardyFactorizationChallenge

open HarmonicAnalysis

/-- The Schatten norms of the Challenge are those of BanachProbability. -/
theorem complexSchattenNorm_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (q : ℝ≥0∞)
    (A : Matrix m n ℂ) :
    HarmonicAnalysis.complexSchattenNorm q A = BanachProbability.complexSchattenNorm q A :=
  rfl

theorem jensen {f : UnitAddCircle → ℂ} (hf : Integrable f haarAddCircle)
    (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0) (h0 : fourierCoeff f 0 ≠ 0) :
    (∀ᵐ t ∂haarAddCircle, f t ≠ 0) ∧ Integrable (fun t => Real.log ‖f t‖) haarAddCircle ∧
      Real.log ‖fourierCoeff f 0‖ ≤ ∫ t, Real.log ‖f t‖ ∂haarAddCircle :=
  log_norm_fourierCoeff_zero_le_integral_log_norm hf hneg h0

variable {l m n : Type*} [Fintype n] [DecidableEq n]

theorem exists_outer [Fintype m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyTwo A) :
    ∃ (q : ℕ) (B : UnitAddCircle → Matrix (Fin q) n ℂ), q ≤ Fintype.card n ∧ IsOuter B ∧
      (matFourierCoeff B 0).rank = q ∧ ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = (A t)ᴴ * A t :=
  exists_isOuter hA

theorem outer_range [Finite m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A) :
    ∀ᵐ t ∂haarAddCircle, LinearMap.range (A t).mulVecLin =
      LinearMap.range (matFourierCoeff A 0).mulVecLin :=
  hA.range_eq

theorem outer_closure [Fintype l] [Finite m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A)
    {F : UnitAddCircle → Matrix m l ℂ} :
    (∃ c : ℕ → ℤ →₀ Matrix n l ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
        TendstoLTwo (fun N t => A t * circPoly (c N) t) F) ↔
      IsHardyTwo F ∧ ∀ᵐ t ∂haarAddCircle, LinearMap.range (F t).mulVecLin ≤
        LinearMap.range (matFourierCoeff A 0).mulVecLin := by
  refine ⟨fun h => ?_, fun h => (hA.exists_tendsto_iff h.1).2 h.2⟩
  obtain ⟨c, hc, hlim⟩ := h
  have hF : IsHardyTwo F := hlim.isHardyTwo fun N => by
    obtain ⟨C, hC⟩ := exists_bound_of_continuous (continuous_circPoly_matrix (c N))
    exact hA.1.mul_bounded (isHardyTwo_circPoly (hc N)) (ae_of_all _ hC)
  exact ⟨hF, (hA.exists_tendsto_iff hF).1 ⟨c, hc, hlim⟩⟩

theorem szego [Nonempty n] {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) :
    ((∀ᵐ t ∂haarAddCircle, (W t).PosDef) ∧
        Integrable (fun t => Real.log (W t).det.re) haarAddCircle →
      szegoInf W = Real.exp ((∫ t, Real.log (W t).det.re ∂haarAddCircle) / Fintype.card n)) ∧
    (¬ ((∀ᵐ t ∂haarAddCircle, (W t).PosDef) ∧
        Integrable (fun t => Real.log (W t).det.re) haarAddCircle) → szegoInf W = 0) := by
  refine ⟨fun h => szegoInf_eq hint h.1 h.2, fun h => ?_⟩
  by_contra h0
  exact h (posDef_of_szegoInf_pos hint hW ((szegoInf_nonneg hW).lt_of_ne' h0))

theorem spectral_factorization {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (_hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) :
    ((∃ B : UnitAddCircle → Matrix n n ℂ, IsHardyTwo B ∧ (matFourierCoeff B 0).det ≠ 0 ∧
        ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = W t) ↔
      (∀ᵐ t ∂haarAddCircle, (W t).PosDef) ∧
        Integrable (fun t => Real.log (W t).det.re) haarAddCircle) ∧
    ((∀ᵐ t ∂haarAddCircle, (W t).PosDef) ∧
        Integrable (fun t => Real.log (W t).det.re) haarAddCircle →
      ∃ B : UnitAddCircle → Matrix n n ℂ, IsOuter B ∧ (matFourierCoeff B 0).det ≠ 0 ∧
        (∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = W t) ∧
        Integrable (fun t => Real.log ‖(B t).det‖) haarAddCircle ∧
        ∫ t, Real.log ‖(B t).det‖ ∂haarAddCircle = Real.log ‖(matFourierCoeff B 0).det‖) := by
  have key : (∀ᵐ t ∂haarAddCircle, (W t).PosDef) ∧
        Integrable (fun t => Real.log (W t).det.re) haarAddCircle →
      ∃ B : UnitAddCircle → Matrix n n ℂ, IsOuter B ∧ (matFourierCoeff B 0).det ≠ 0 ∧
        (∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = W t) ∧
        Integrable (fun t => Real.log ‖(B t).det‖) haarAddCircle ∧
        ∫ t, Real.log ‖(B t).det‖ ∂haarAddCircle = Real.log ‖(matFourierCoeff B 0).det‖ := by
    rintro ⟨hpos, hlog⟩
    obtain ⟨B, hB, h0, hBW, h⟩ := exists_isOuter_of_integrable_log_det hint hpos hlog
    exact ⟨B, hB, h0, hBW, (integrable_log_det_of_isHardyTwo hB.1 h0).2.1, h⟩
  refine ⟨⟨?_, fun h => ?_⟩, key⟩
  · rintro ⟨B, hB, h0, hBW⟩
    obtain ⟨hdet, hlog, -⟩ := integrable_log_det_of_isHardyTwo hB h0
    refine ⟨?_, (hlog.const_mul 2).congr ?_⟩
    · filter_upwards [hdet, hBW] with t h1 h2
      exact h2 ▸ posDef_conjTranspose_mul_self h1
    · filter_upwards [hBW] with t ht
      rw [← ht, log_det_conjTranspose_mul_self_re]
  · obtain ⟨B, hB, h0, hBW, -⟩ := key h
    exact ⟨B, hB.1, h0, hBW⟩

theorem outer_iff {A : UnitAddCircle → Matrix n n ℂ} (hA : IsHardyTwo A)
    (h0 : (matFourierCoeff A 0).det ≠ 0) :
    Integrable (fun t => Real.log ‖(A t).det‖) haarAddCircle ∧
      (IsOuter A ↔
        ∫ t, Real.log ‖(A t).det‖ ∂haarAddCircle = Real.log ‖(matFourierCoeff A 0).det‖) :=
  ⟨(integrable_log_det_of_isHardyTwo hA h0).2.1, isOuter_iff_integral_log_norm_det hA h0⟩

theorem analytic_range [Fintype m] [DecidableEq m] {𝔥 : UnitAddCircle → Submodule ℂ (m → ℂ)}
    (h : IsAnalyticRange 𝔥) :
    ∃ (q : ℕ) (V : UnitAddCircle → Matrix m (Fin q) ℂ), IsLeftOuter V ∧
      (∀ᵐ t ∂haarAddCircle, (V t)ᴴ * V t = 1) ∧
      ∀ᵐ t ∂haarAddCircle, LinearMap.range (V t).mulVecLin = 𝔥 t :=
  h.exists_isometry

theorem factorization {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) :
    (∃ (k : ℕ) (A : UnitAddCircle → Matrix n (Fin k) ℂ), IsHardyTwo A ∧
        ∀ᵐ t ∂haarAddCircle, A t * (A t)ᴴ = W t) ↔
      IsAnalyticRange (fun t => LinearMap.range (W t).mulVecLin) ∧
        Integrable (fun t => Real.log (rangeDet (W t))) haarAddCircle :=
  exists_mul_conjTranspose_eq_iff hint hW

theorem riesz_factorization [Fintype m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyOne A) :
    ∃ (A₁ : UnitAddCircle → Matrix m n ℂ) (A₂ : UnitAddCircle → Matrix n n ℂ), IsHardyTwo A₁ ∧
      IsHardyTwo A₂ ∧ ∀ᵐ t ∂haarAddCircle, A t = A₁ t * A₂ t ∧
        ((A₂ t)ᴴ * A₂ t) ^ 2 = (A t)ᴴ * A t ∧ (A₁ t)ᴴ * A₁ t = A₂ t * (A₂ t)ᴴ ∧
        ∀ p : ℝ, 0 < p →
          HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (2 * p)) (A₁ t) ^ 2 =
            HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal p) (A t) ∧
          HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (2 * p)) (A₂ t) ^ 2 =
            HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal p) (A t) := by
  obtain ⟨A₁, A₂, h₁, h₂, h⟩ := exists_mul_eq_of_isHardyOne hA
  refine ⟨A₁, A₂, h₁, h₂, ?_⟩
  filter_upwards [h] with t ⟨ha, hb, hc⟩
  refine ⟨ha, ?_, hc, fun p hp => complexSchattenNorm_sq_of_factorization hp hb hc⟩
  rw [hb, sq, cfc_sqrt_mul_self (Matrix.posSemidef_conjTranspose_mul_self (A t))]

theorem rangeDet_eq {q : ℕ} {W : Matrix n n ℂ} {V : Matrix n (Fin q) ℂ} (hW : W.PosSemidef)
    (hV : Vᴴ * V = 1) (h : LinearMap.range V.mulVecLin = LinearMap.range W.mulVecLin) :
    rangeDet W = (Vᴴ * W * V).det.re :=
  rangeDet_eq_det_conjTranspose_mul_mul hW hV h

end HardyFactorizationChallenge
