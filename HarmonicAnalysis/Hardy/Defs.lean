/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Basic.Real.Sign
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.UniformOn

/-!
# Definitions: matrix-valued Hardy functions, outer functions, range functions, Schatten norms

The definitions that the headline theorems for matrix-valued functions on the circle use, in marked
blocks that `scripts/sync_challenge_defs.py` copies word for word into the Challenges of `palomar/`
(see `HarmonicAnalysis.VectorValued.Defs`). Their theory is in the modules named with each block.

* `hardyOne`, `hardyTwo`: Fourier coefficients and the Hardy classes `H¹`, `H²` (`Hardy/Basic.lean`,
  `Hardy/Approximation.lean`);
* `outer`: convergence in `L²`, outer functions (`Hardy/Approximation.lean`, `Hardy/Outer.lean`);
* `szego`: the infimum of Szegő's theorem (`Hardy/Szego.lean`);
* `range`: left-outer functions, analytic range functions, the determinant on the range
  (`Hardy/RangeFunction.lean`);
* `schatten`: Schatten norms of complex matrices, a copy of `BanachProbability.complexSchattenNorm`,
  which the library uses (the two are equal by definition; the names are protected, so that they do
  not hide the others).
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexOrder Topology

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
