module

public import HarmonicAnalysis.Paley.Rademacher

/-!
# Solution: Paley's inequality and the lower Khintchine inequality in the Schatten classes

The statements of `palomar/PaleySchatten/Challenge.lean`, word for word, proved from the library.
The library uses the Schatten norms of BanachProbability, which are those of the Challenge by
definition (`complexSchattenNorm_eq`), and writes the square functions as norms of block rows and
block columns.
-/

@[expose] public section

open MeasureTheory AddCircle
open scoped ENNReal Matrix

namespace PaleySchattenChallenge

open HarmonicAnalysis

/-- The Schatten norms of the Challenge are those of BanachProbability. -/
theorem complexSchattenNorm_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (q : ℝ≥0∞)
    (A : Matrix m n ℂ) :
    HarmonicAnalysis.complexSchattenNorm q A = BanachProbability.complexSchattenNorm q A :=
  rfl

/-- `ofReal (p / 2) = ofReal p / 2`. -/
private theorem ofReal_div_two (p : ℝ) : ENNReal.ofReal (p / 2) = ENNReal.ofReal p / 2 := by
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- `‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p}` as the norm of a block row. -/
private theorem sqrt_row {n : Type*} [Fintype n] [DecidableEq n] {p : ℝ} (hp : 0 < p) {K : ℕ}
    (a : Fin K → Matrix n n ℂ) :
    √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, a k * (a k)ᴴ)) =
      BanachProbability.complexSchattenNorm (ENNReal.ofReal p) (BanachProbability.blockRow a) := by
  rw [complexSchattenNorm_eq, ofReal_div_two,
    ← BanachProbability.complexSchattenNorm_blockRow_sq (by simpa using hp),
    Real.sqrt_sq (BanachProbability.complexSchattenNorm_nonneg _ _)]

/-- `‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p}` as the norm of a block column. -/
private theorem sqrt_col {n : Type*} [Fintype n] [DecidableEq n] {p : ℝ} (hp : 0 < p) {K : ℕ}
    (b : Fin K → Matrix n n ℂ) :
    √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, (b k)ᴴ * b k)) =
      BanachProbability.complexSchattenNorm (ENNReal.ofReal p) (BanachProbability.blockCol b) := by
  rw [complexSchattenNorm_eq, ofReal_div_two,
    ← BanachProbability.complexSchattenNorm_blockCol_sq (by simpa using hp),
    Real.sqrt_sq (BanachProbability.complexSchattenNorm_nonneg _ _)]

theorem paley : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 →
    ∀ f : UnitAddCircle → Matrix n n ℂ, IsHardyOne f → ∀ K : ℕ,
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k : Fin K, matFourierCoeff f (2 ^ (k : ℕ)) = a k + b k) ∧
      √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, a k * (a k)ᴴ)) +
        √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, (b k)ᴴ * b k)) ≤
      M * ∫ t, HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal p) (f t) ∂haarAddCircle := by
  obtain ⟨M, hM, h⟩ := paley_schatten_of_isHardyOne
  refine ⟨M, hM, fun n _ _ p hp1 hp2 f hf K => ?_⟩
  obtain ⟨a, b, hab, hle⟩ := h n p hp1 hp2 f hf K
  refine ⟨a, b, hab, ?_⟩
  rw [sqrt_row (by linarith), sqrt_col (by linarith)]
  exact hle

theorem khintchine_lower : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ),
    1 ≤ p → p ≤ 2 → ∀ (K : ℕ) (A : Fin K → Matrix n n ℂ),
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k, A k = a k + b k) ∧
      √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, a k * (a k)ᴴ)) +
        √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, (b k)ᴴ * b k)) ≤
      M * ((∑ ε : Fin K → Bool, HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal p)
        (∑ k, (if ε k then (1 : ℝ) else -1) • A k)) / 2 ^ K) := by
  obtain ⟨M, hM, h⟩ := rademacher_schatten_le
  refine ⟨M, hM, fun n _ _ p hp1 hp2 K A => ?_⟩
  obtain ⟨a, b, hab, hle⟩ := h n p hp1 hp2 K A
  refine ⟨a, b, hab, ?_⟩
  rw [sqrt_row (by linarith), sqrt_col (by linarith)]
  exact hle

theorem schatten_conjTranspose_mul_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {q : ℝ≥0∞} (hq : q ≠ 0) (B : Matrix m n ℂ) :
    HarmonicAnalysis.complexSchattenNorm (q / 2) (Bᴴ * B) =
      HarmonicAnalysis.complexSchattenNorm q B ^ 2 :=
  BanachProbability.complexSchattenNorm_conjTranspose_mul_self hq B

theorem schatten_two_sq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (B : Matrix m n ℂ) :
    HarmonicAnalysis.complexSchattenNorm 2 B ^ 2 = ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  have h := Matrix.isHermitian_conjTranspose_mul_self B
  rw [Finset.sum_comm, ← trace_conjTranspose_mul_self_re, trace_re_eq_sum_eigenvalues h,
    HarmonicAnalysis.complexSchattenNorm, ite_eq_right ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Real.rpow_nonneg
      (by exact Real.sqrt_nonneg _) _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HarmonicAnalysis.complexSingularValue, Real.rpow_ofNat,
    Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg B i)]

end PaleySchattenChallenge
