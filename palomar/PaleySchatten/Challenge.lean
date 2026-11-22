module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Basic.Real.Sign
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.UniformOn

/-!
# Challenge: Paley's inequality and the lower Khintchine inequality in the Schatten classes

Paley's inequality for functions with values in the Schatten class `S_p`, `1 ≤ p ≤ 2`, and the lower
noncommutative Khintchine inequality, with constants that do not depend on `p` or on the size of the
matrices, after

* [LPP] F. Lust-Piquard, G. Pisier, *Non commutative Khintchine and Paley inequalities*, Ark. Mat.
  29 (1991), 241–260: Theorems 0.1, 0.3, II.1 a) (i) and III.1 (i), Corollary III.4;
* [P] G. Pisier, *Non-commutative vector valued `L_p`-spaces and completely `p`-summing maps*,
  Astérisque 247 (1998): Theorem 8.4.1 (ii), p. 105.

## Conventions

* The circle is `𝕋 = ℝ / ℤ` (`UnitAddCircle`) with its Haar probability measure `haarAddCircle`.
  `IsHardyOne f`: the entries of `f : 𝕋 → M_n (ℂ)` are integrable, and the matrices `f̂ (k)` of
  their Fourier coefficients (`matFourierCoeff f k`) vanish for `k < 0`. ([LPP, p. 244] defines
  `H¹ (S_p)` as the closure of the analytic polynomials in `L¹ (𝕋; S_p)`, which for matrices of a
  fixed size is the same class, by Fejér means; not formalized here.)
* `complexSchattenNorm q A` is the Schatten norm `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}`, `s_i` the singular
  values of `A`; `ENNReal.ofReal p` is a real exponent, also below `1`. [LPP] writes `C_p`.
* The row and column square functions are `(Σ a_k a_kᴴ)^{1/2}` and `(Σ b_kᴴ b_k)^{1/2}`, and their
  `S_p` norms are written as `‖Σ a_k a_kᴴ‖_{S_{p/2}}^{1/2}` and `‖Σ b_kᴴ b_k‖_{S_{p/2}}^{1/2}`: by
  `schatten_conjTranspose_mul_self`, `‖Bᴴ B‖_{S_{p/2}} = ‖B‖_{S_p}²` for every `B`, in particular
  for the positive semidefinite square roots `B`. The infimum of the sum of the two norms over the
  decompositions `x_k = a_k + b_k` is the norm `|||(x_k)|||_p` of [LPP, (0.4)] (for `p = 1`) and
  [P, p. 106], that of `S_p (ℓ²_L) + S_p (ℓ²_R)`. The theorems bound it by exhibiting a
  decomposition.
* The signs `ε_k = ±1` are the coordinates of the cube `Fin K → Bool`, and the expectation `E` is
  the average over the cube.

## Statements

* `paley` ([LPP, Theorem III.1 (i)], for the Paley projection, `C_E = S_p` and finite sequences; for
  `p = 1` [LPP, Theorems 0.3 and II.1 a) (i)], without the constant `1 + √2`): there is an absolute
  `M` with `|||(f̂ (2^k))_{k < K}|||_p ≤ M ∫ ‖f‖_{S_p}` for `1 ≤ p ≤ 2`, `f ∈ H¹ (𝕋; M_n)`, all `n`,
  `K`.
* `khintchine_lower` ([LPP, Corollary III.4], left-hand inequality, with signs; for `p = 1` the
  right-hand inequality of [LPP, Theorem 0.1]; [P, Theorem 8.4.1 (ii)], left-hand inequality): there
  is an absolute `M` with `|||(A_k)|||_p ≤ M E ‖Σ ε_k A_k‖_{S_p}` for `1 ≤ p ≤ 2` and all finite
  families of square matrices of the same size.
* `schatten_conjTranspose_mul_self`, `schatten_two_sq`: checks of the definitions.

Not formalized: the easy inequalities in the other direction ([LPP, (I.14)]); general `H¹–ℓ²`
multipliers and symmetric sequence spaces; infinite dimension.

The definitions are copied word for word from `HarmonicAnalysis/Hardy/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in `palomar/PaleySchatten/Solution.lean`.
-/

@[expose] public section

open MeasureTheory AddCircle
open scoped ENNReal Matrix

namespace HarmonicAnalysis

-- BEGIN SHARED DEFINITIONS: hardyOne

/-- The `k`-th Fourier coefficient of a matrix-valued function, entry by entry. -/
noncomputable def matFourierCoeff {m n : Type*} (f : UnitAddCircle → Matrix m n ℂ) (k : ℤ) :
    Matrix m n ℂ :=
  Matrix.of fun i j => fourierCoeff (fun t => f t i j) k

/-- The matrix-valued Hardy class `H¹`: integrable entries, vanishing Fourier coefficients of
negative order. -/
def IsHardyOne {m n : Type*} (f : UnitAddCircle → Matrix m n ℂ) : Prop :=
  (∀ i j, Integrable (fun t => f t i j) haarAddCircle) ∧ ∀ k : ℤ, k < 0 → matFourierCoeff f k = 0

-- END SHARED DEFINITIONS: hardyOne

-- BEGIN SHARED DEFINITIONS: schatten

/-- The singular values of `A ∈ ℂ^{m×n}`, indexed by the columns: `s_i = √λ_i (Aᴴ A)`. -/
protected noncomputable def complexSingularValue {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) (i : n) : ℝ :=
  √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The Schatten `q`-norm of a complex matrix: `‖A‖_{S_q} = (Σ_i s_i^q)^{1/q}` for `q < ∞`,
`‖A‖_{S_∞} = max_i s_i`. -/
protected noncomputable def complexSchattenNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (q : ℝ≥0∞) (A : Matrix m n ℂ) : ℝ :=
  if q = ⊤ then ⨆ i, HarmonicAnalysis.complexSingularValue A i
  else (∑ i, HarmonicAnalysis.complexSingularValue A i ^ q.toReal) ^ (1 / q.toReal)

-- END SHARED DEFINITIONS: schatten

end HarmonicAnalysis

namespace PaleySchattenChallenge

open HarmonicAnalysis

/-- **Paley's inequality in the Schatten classes** ([LPP, Theorem III.1 (i)], for the Paley
projection and `C_E = S_p`): there is an absolute constant `M` such that for `1 ≤ p ≤ 2`, every size
`n`, every `f ∈ H¹ (𝕋; M_n (ℂ))` and every `K`, `f̂ (2^k) = a_k + b_k`, `k < K`, with
`‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M ∫_𝕋 ‖f (t)‖_{S_p} dt`. -/
theorem paley : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 →
    ∀ f : UnitAddCircle → Matrix n n ℂ, IsHardyOne f → ∀ K : ℕ,
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k : Fin K, matFourierCoeff f (2 ^ (k : ℕ)) = a k + b k) ∧
      √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, a k * (a k)ᴴ)) +
        √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, (b k)ᴴ * b k)) ≤
      M * ∫ t, HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal p) (f t) ∂haarAddCircle := by
  sorry

/-- **The lower Khintchine inequality in the Schatten classes** ([LPP, Corollary III.4 and Theorem
0.1], with signs; [P, Theorem 8.4.1 (ii)]): there is an absolute constant `M` such that for
`1 ≤ p ≤ 2`, every size `n`, every `K` and all `A_1, …, A_K ∈ M_n (ℂ)`, `A_k = a_k + b_k` with
`‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M E ‖Σ ε_k A_k‖_{S_p}`. -/
theorem khintchine_lower : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ),
    1 ≤ p → p ≤ 2 → ∀ (K : ℕ) (A : Fin K → Matrix n n ℂ),
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k, A k = a k + b k) ∧
      √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, a k * (a k)ᴴ)) +
        √(HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (p / 2)) (∑ k, (b k)ᴴ * b k)) ≤
      M * ((∑ ε : Fin K → Bool, HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal p)
        (∑ k, (if ε k then (1 : ℝ) else -1) • A k)) / 2 ^ K) := by
  sorry

/-- `‖Bᴴ B‖_{S_{q/2}} = ‖B‖_{S_q}²`, `q ≠ 0`; this identifies the norms of the square functions. -/
theorem schatten_conjTranspose_mul_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {q : ℝ≥0∞} (hq : q ≠ 0) (B : Matrix m n ℂ) :
    HarmonicAnalysis.complexSchattenNorm (q / 2) (Bᴴ * B) =
      HarmonicAnalysis.complexSchattenNorm q B ^ 2 := by
  sorry

/-- `‖B‖_{S_2}² = Σ |B_{ij}|²`. -/
theorem schatten_two_sq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (B : Matrix m n ℂ) :
    HarmonicAnalysis.complexSchattenNorm 2 B ^ 2 = ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  sorry

end PaleySchattenChallenge
