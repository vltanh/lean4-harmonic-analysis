module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Basic.Real.Sign
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.UniformOn

/-!
# Challenge: Szegő and Riesz factorization of matrix-valued functions on the circle

Outer functions, Szegő's theorem, the factorization of positive semidefinite functions and the
Riesz factorization of `H¹`, for matrix-valued functions on the circle, after

* [HL1] H. Helson, D. Lowdenslager, *Prediction theory and Fourier series in several variables*,
  Acta Math. 99 (1958), 165–202: Theorem 2 (circle), Theorems 8 and 9 (Theorem 10 is a case of [S]);
* [HL2] H. Helson, D. Lowdenslager, *Prediction theory and Fourier series in several variables. II*,
  Acta Math. 106 (1961), 175–213: §§9–11, Theorems 8, 9, 10, 12 and 13;
* [S] D. Sarason, *Generalized interpolation in `H^∞`*, Trans. Amer. Math. Soc. 127 (1967),
  179–203: Theorem 4.

## Conventions

* The circle is `𝕋 = ℝ / ℤ` (`UnitAddCircle`) with its Haar probability measure `haarAddCircle`;
  `fourier k` is `e_k (t) = e^{2πi k t}`. Matrices are complex, with finite index types. Functions
  are defined everywhere; "a.e." equalities and inequalities are with respect to this measure.
* `matFourierCoeff f k` is the matrix `f̂ (k)` of the Fourier coefficients of the entries, and
  `circPoly c = Σ c_k e_k` a trigonometric polynomial with matrix coefficients. A function is
  analytic if `f̂ (k) = 0` for `k < 0`; `IsHardyOne`, `IsHardyTwo` are the classes `H¹`, `H²` of the
  analytic functions with entries in `L¹`, `L²`. Convergence in `L²` is that of the entries.
* [HL1] and [HL2] consider `W = B Bᴴ`, left-outer functions (from `(1 + P) A`) and rows. Theorems 8
  and 9 of [HL1], the outer factor and Theorems 8, 9, 10 of [HL2] are stated for the transposed
  functions: `W = Bᴴ B`, right-outer functions (`IsOuter`, from `A (1 + P)`) and columns, as in [S].
  `IsLeftOuter A`: the transposed function is outer. The trace is the usual one ([HL1]: `tr 1 = 1`).
* "`∫ log det W > −∞`" is stated as: `W` is positive definite a.e. and `log det W` is integrable
  (Lean's integral of a function that is not integrable is `0`; the positive part of `log det W` is
  always integrable, as `log det W ≤ tr W`).
* `rangeDet W` is `Δ W`, the determinant of `W` on its range (`rangeDet_eq`, a check), and
  `complexSchattenNorm (ENNReal.ofReal p) A` the Schatten norm `‖A‖_{S_p}`, `p` real.

## Statements

* `jensen` ([HL1, Theorem 2 and corollary], circle): `∫ log |f| ≥ log |f̂ (0)|`, scalar `f ∈ H¹`.
* `exists_outer` ([HL2, pp. 202–203, 207]): `Aᴴ A = Bᴴ B` with `B` outer, for `A ∈ H²`.
* `outer_range`, `outer_closure`, `outer_iff` ([HL2, Theorems 9, 10, 8]): the range of an outer
  function; the closure of `{A Q}`; outer if and only if `∫ log |det A| = log |det Â (0)|`.
* `szego` ([HL1, Theorem 8], absolutely continuous measures): `exp ((1/n) ∫ log det W)` is the
  infimum of `∫ (1/n) tr (Qᴴ W Q)`, `Q` an analytic polynomial with `det Q̂ (0) = 1`.
* `spectral_factorization` ([HL1, Theorem 9]): `W = Bᴴ B`, `B ∈ H²`, `det B̂ (0) ≠ 0`, if and only
  if `∫ log det W > −∞`; and then also with `B` outer.
* `analytic_range`, `factorization` ([HL2, Theorems 12, 13]): analytic range functions are the
  ranges of analytic isometries; `W = A Aᴴ`, `A ∈ H²`, if and only if the range of `W` is analytic
  and `∫ log Δ W > −∞` (any rank).
* `riesz_factorization` ([S, Theorem 4], finite dimension): `A = A₁ A₂` for `A ∈ H¹`, `A₁, A₂ ∈ H²`,
  `A₂ᴴ A₂ = (Aᴴ A)^{1/2}`, `A₁ᴴ A₁ = A₂ A₂ᴴ`; hence `‖A₁‖²_{S_{2p}} = ‖A₂‖²_{S_{2p}} = ‖A‖_{S_p}`.

The definitions are copied word for word from `HarmonicAnalysis/VectorValued/Defs.lean` and
`HarmonicAnalysis/Hardy/Defs.lean` (kept in sync by `scripts/sync_challenge_defs.py`); the theorems
are proved in `palomar/HardyFactorization/Solution.lean`.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexOrder Topology

namespace HarmonicAnalysis

-- BEGIN SHARED DEFINITIONS: circle

/-- The trigonometric polynomial `Σ_n c_n e_n` on `𝕋 = ℝ / ℤ`, with coefficients in a complex vector
space. -/
noncomputable def circPoly {V : Type*} [AddCommMonoid V] [Module ℂ V] (c : ℤ →₀ V)
    (t : UnitAddCircle) : V :=
  c.sum fun n x => fourier n t • x

-- END SHARED DEFINITIONS: circle

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

-- BEGIN SHARED DEFINITIONS: hardyTwo

/-- The matrix-valued Hardy class `H²`: entries in `L²`, vanishing Fourier coefficients of negative
order. -/
def IsHardyTwo {m n : Type*} (f : UnitAddCircle → Matrix m n ℂ) : Prop :=
  (∀ i j, MemLp (fun t => f t i j) 2 haarAddCircle) ∧ ∀ k : ℤ, k < 0 → matFourierCoeff f k = 0

-- END SHARED DEFINITIONS: hardyTwo

-- BEGIN SHARED DEFINITIONS: outer

/-- Convergence in `L²` of matrix-valued functions, entry by entry. -/
def TendstoLTwo {m n : Type*} (F : ℕ → UnitAddCircle → Matrix m n ℂ)
    (f : UnitAddCircle → Matrix m n ℂ) : Prop :=
  ∀ i j, Tendsto (fun N => eLpNorm (fun t => F N t i j - f t i j) 2 haarAddCircle) atTop (𝓝 0)

/-- Helson–Lowdenslager (1961), p. 203, (125)–(127): `A ∈ H²` is (right-)outer if the closure in
`L²` of the functions `A (1 + P)`, where `P` is an analytic trigonometric polynomial without
constant term, contains a constant function. "Evidently the constant matrix can only be the constant
term of `A`", so that the definition takes `Â (0)` for it. -/
def IsOuter {m n : Type*} [Fintype n] [DecidableEq n] (A : UnitAddCircle → Matrix m n ℂ) : Prop :=
  IsHardyTwo A ∧ ∃ c : ℕ → ℤ →₀ Matrix n n ℂ, (∀ N, ∀ k ∈ (c N).support, 0 < k) ∧
    TendstoLTwo (fun N t => A t * (1 + circPoly (c N) t)) fun _ => matFourierCoeff A 0

-- END SHARED DEFINITIONS: outer

-- BEGIN SHARED DEFINITIONS: szego

/-- The infimum of `∫ (1/n) tr (Qᴴ W Q)` over the analytic trigonometric polynomials `Q` whose
constant coefficient has determinant `1`. -/
noncomputable def szegoInf {n : Type*} [Fintype n] [DecidableEq n]
    (W : UnitAddCircle → Matrix n n ℂ) : ℝ :=
  ⨅ c : {c : ℤ →₀ Matrix n n ℂ // (∀ k ∈ c.support, 0 ≤ k) ∧ (c 0).det = 1},
    (∫ t, ((circPoly c.1 t)ᴴ * W t * circPoly c.1 t).trace.re ∂haarAddCircle) / Fintype.card n

-- END SHARED DEFINITIONS: szego

-- BEGIN SHARED DEFINITIONS: range

/-- Helson–Lowdenslager (1961), §10: `A ∈ H²` is left-outer if the closure in `L²` of the functions
`(1 + P) A`, with `P` an analytic trigonometric polynomial without constant term, contains a
constant, that is, if the transposed function is outer. -/
def IsLeftOuter {m n : Type*} [Fintype m] [DecidableEq m] (A : UnitAddCircle → Matrix m n ℂ) :
    Prop :=
  IsOuter fun t => (A t)ᵀ

/-- A range function, a function whose values are subspaces of `ℂᵐ`, is analytic if it is almost
everywhere the range of a function of `H²`. -/
def IsAnalyticRange {m : Type*} (𝔥 : UnitAddCircle → Submodule ℂ (m → ℂ)) : Prop :=
  ∃ (k : ℕ) (A : UnitAddCircle → Matrix m (Fin k) ℂ), IsHardyTwo A ∧
    ∀ᵐ t ∂haarAddCircle, LinearMap.range (A t).mulVecLin = 𝔥 t

/-- `Δ W`, the determinant of the restriction of the Hermitian matrix `W` to its range: the product
of its eigenvalues different from zero. -/
noncomputable def rangeDet {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) : ℝ :=
  ((W.charpoly.roots.filter (· ≠ 0)).prod).re

-- END SHARED DEFINITIONS: range

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

namespace HardyFactorizationChallenge

open HarmonicAnalysis

/-- **Jensen's inequality** ([HL1, Theorem 2 and its corollary], for the circle): for an integrable
`f` with `f̂ (k) = 0` for `k < 0` and `f̂ (0) ≠ 0`, `f ≠ 0` a.e., `log |f|` is integrable and
`∫ log |f| ≥ log |f̂ (0)|`. -/
theorem jensen {f : UnitAddCircle → ℂ} (hf : Integrable f haarAddCircle)
    (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0) (h0 : fourierCoeff f 0 ≠ 0) :
    (∀ᵐ t ∂haarAddCircle, f t ≠ 0) ∧ Integrable (fun t => Real.log ‖f t‖) haarAddCircle ∧
      Real.log ‖fourierCoeff f 0‖ ≤ ∫ t, Real.log ‖f t‖ ∂haarAddCircle := by
  sorry

variable {l m n : Type*} [Fintype n] [DecidableEq n]

/-- **The outer factor** ([HL2, pp. 202–203 and 207], transposed): for `A ∈ H²` there is an outer
`B`, with at most as many rows as `A` has columns and `B̂ (0)` surjective, with `Bᴴ B = Aᴴ A`. -/
theorem exists_outer [Fintype m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyTwo A) :
    ∃ (q : ℕ) (B : UnitAddCircle → Matrix (Fin q) n ℂ), q ≤ Fintype.card n ∧ IsOuter B ∧
      (matFourierCoeff B 0).rank = q ∧ ∀ᵐ t ∂haarAddCircle, (B t)ᴴ * B t = (A t)ᴴ * A t := by
  sorry

/-- **The range of an outer function** is a.e. that of its constant coefficient ([HL2, Theorem 9],
transposed). -/
theorem outer_range [Finite m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A) :
    ∀ᵐ t ∂haarAddCircle, LinearMap.range (A t).mulVecLin =
      LinearMap.range (matFourierCoeff A 0).mulVecLin := by
  sorry

/-- **The closure in `L²` of the functions `A Q`**, `Q` an analytic polynomial, for an outer `A`
([HL2, Theorem 10], transposed): the functions of `H²` whose range is a.e. contained in that of
`Â (0)`. -/
theorem outer_closure [Fintype l] [Finite m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsOuter A)
    {F : UnitAddCircle → Matrix m l ℂ} :
    (∃ c : ℕ → ℤ →₀ Matrix n l ℂ, (∀ N, ∀ k ∈ (c N).support, 0 ≤ k) ∧
        TendstoLTwo (fun N t => A t * circPoly (c N) t) F) ↔
      IsHardyTwo F ∧ ∀ᵐ t ∂haarAddCircle, LinearMap.range (F t).mulVecLin ≤
        LinearMap.range (matFourierCoeff A 0).mulVecLin := by
  sorry

/-- **Szegő's theorem for matrices** ([HL1, Theorem 8], for the absolutely continuous measure
`W dt`, transposed): for a positive semidefinite `W` with integrable entries, the infimum of
`∫ (1/n) tr (Qᴴ W Q)` over the analytic polynomials `Q` with `det Q̂ (0) = 1` (`szegoInf W`) is
`exp ((1/n) ∫ log det W)` if `∫ log det W > −∞`, and `0` if not. -/
theorem szego [Nonempty n] {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) :
    ((∀ᵐ t ∂haarAddCircle, (W t).PosDef) ∧
        Integrable (fun t => Real.log (W t).det.re) haarAddCircle →
      szegoInf W = Real.exp ((∫ t, Real.log (W t).det.re ∂haarAddCircle) / Fintype.card n)) ∧
    (¬ ((∀ᵐ t ∂haarAddCircle, (W t).PosDef) ∧
        Integrable (fun t => Real.log (W t).det.re) haarAddCircle) → szegoInf W = 0) := by
  sorry

/-- **Factorization of positive functions of full rank** ([HL1, Theorem 9], transposed): for a
positive semidefinite `W` with integrable entries, `W = Bᴴ B` for some `B ∈ H²` with
`det B̂ (0) ≠ 0` if and only if `∫ log det W > −∞`; and then `B` can be chosen outer, with
`∫ log |det B| = log |det B̂ (0)|`. -/
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
  sorry

/-- **Outer functions of full rank** ([HL2, Theorem 8], transposed): a square `A ∈ H²` with
`det Â (0) ≠ 0` is outer if and only if `∫ log |det A| = log |det Â (0)|`. (`log |det A|` is
integrable in any case.) -/
theorem outer_iff {A : UnitAddCircle → Matrix n n ℂ} (hA : IsHardyTwo A)
    (h0 : (matFourierCoeff A 0).det ≠ 0) :
    Integrable (fun t => Real.log ‖(A t).det‖) haarAddCircle ∧
      (IsOuter A ↔
        ∫ t, Real.log ‖(A t).det‖ ∂haarAddCircle = Real.log ‖(matFourierCoeff A 0).det‖) := by
  sorry

/-- **Analytic range functions** ([HL2, Theorem 12]): every analytic range function is a.e. the
range of a left-outer function whose values are isometries (partial isometries in the source's
statement; its proof gives `Vᴴ V = 1`). -/
theorem analytic_range [Fintype m] [DecidableEq m] {𝔥 : UnitAddCircle → Submodule ℂ (m → ℂ)}
    (h : IsAnalyticRange 𝔥) :
    ∃ (q : ℕ) (V : UnitAddCircle → Matrix m (Fin q) ℂ), IsLeftOuter V ∧
      (∀ᵐ t ∂haarAddCircle, (V t)ᴴ * V t = 1) ∧
      ∀ᵐ t ∂haarAddCircle, LinearMap.range (V t).mulVecLin = 𝔥 t := by
  sorry

/-- **Factorization of positive functions of any rank** ([HL2, Theorem 13]): a positive semidefinite
`W` with integrable entries is `A Aᴴ` for some `A ∈ H²` if and only if its range function is
analytic and `∫ log Δ W > −∞` (as `Δ W ≤ (1 + tr W)ⁿ`, this means: `log Δ W` is integrable). -/
theorem factorization {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosSemidef) :
    (∃ (k : ℕ) (A : UnitAddCircle → Matrix n (Fin k) ℂ), IsHardyTwo A ∧
        ∀ᵐ t ∂haarAddCircle, A t * (A t)ᴴ = W t) ↔
      IsAnalyticRange (fun t => LinearMap.range (W t).mulVecLin) ∧
        Integrable (fun t => Real.log (rangeDet (W t))) haarAddCircle := by
  sorry

/-- **The Riesz factorization of `H¹`** ([S, Theorem 4], for matrices; that `A = A₁ A₂` with
`A₁, A₂ ∈ H²` is [HL1, Theorem 10] if `Â (0)` is non-singular): every `A ∈ H¹` is a.e. `A₁ A₂` with
`A₁, A₂ ∈ H²`, `A₂ᴴ A₂ = (Aᴴ A)^{1/2}` (that is, `(A₂ᴴ A₂)² = Aᴴ A`) and `A₁ᴴ A₁ = A₂ A₂ᴴ`; hence
`‖A₁‖²_{S_{2p}} = ‖A₂‖²_{S_{2p}} = ‖A‖_{S_p}` for every `0 < p < ∞`. -/
theorem riesz_factorization [Fintype m] {A : UnitAddCircle → Matrix m n ℂ} (hA : IsHardyOne A) :
    ∃ (A₁ : UnitAddCircle → Matrix m n ℂ) (A₂ : UnitAddCircle → Matrix n n ℂ), IsHardyTwo A₁ ∧
      IsHardyTwo A₂ ∧ ∀ᵐ t ∂haarAddCircle, A t = A₁ t * A₂ t ∧
        ((A₂ t)ᴴ * A₂ t) ^ 2 = (A t)ᴴ * A t ∧ (A₁ t)ᴴ * A₁ t = A₂ t * (A₂ t)ᴴ ∧
        ∀ p : ℝ, 0 < p →
          HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (2 * p)) (A₁ t) ^ 2 =
            HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal p) (A t) ∧
          HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal (2 * p)) (A₂ t) ^ 2 =
            HarmonicAnalysis.complexSchattenNorm (ENNReal.ofReal p) (A t) := by
  sorry

/-- `Δ W` is the determinant of `W` on its range: `Δ W = det (Vᴴ W V)` if the columns of `V` are an
orthonormal basis of the range of the positive semidefinite matrix `W`. -/
theorem rangeDet_eq {q : ℕ} {W : Matrix n n ℂ} {V : Matrix n (Fin q) ℂ} (hW : W.PosSemidef)
    (hV : Vᴴ * V = 1) (h : LinearMap.range V.mulVecLin = LinearMap.range W.mulVecLin) :
    rangeDet W = (Vᴴ * W * V).det.re := by
  sorry

end HardyFactorizationChallenge
