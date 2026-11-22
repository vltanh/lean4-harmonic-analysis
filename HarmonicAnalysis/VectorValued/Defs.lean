/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Basic.Real.Sign
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.UniformOn

/-!
# Definitions: UMD constants, Rademacher sums, trigonometric polynomials, dyadic blocks

The definitions that the headline theorems for functions with values in Banach spaces use, in marked
blocks that `scripts/sync_challenge_defs.py` copies word for word into the Challenges of `palomar/`.
A Challenge declares them again and imports only Mathlib, so this module and
`HarmonicAnalysis.Hardy.Defs`, which holds the definitions for matrix-valued functions, import the
same modules of Mathlib as these Challenges. Their theory is in the modules named with each block.

* `umd`: the UMD constants, a copy of `BanachProbability.IsUMDBound`, which the library uses (the
  two are equal by definition; the name is protected, so that it does not hide the other one);
* `circle`: vector-valued trigonometric polynomials (`VectorValued/CircPoly.lean`);
* `rademacher`: norms of Rademacher sums of functions (`VectorValued/RademacherNorm.lean`);
* `dyadic`: the dyadic intervals of the line and the dyadic blocks of `ℤ`
  (`VectorValued/LittlewoodPaley/`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace HarmonicAnalysis

-- BEGIN SHARED DEFINITIONS: umd

/-- `β` is a `UMD_p` constant of the Banach space `X`: for every probability space and filtration,
every `X`-valued martingale `Y` with `Y₀ = 0` and every sequence of predictable signs
`σ_k ∈ {±1}` (`σ_{k+1}` is `ℱ_k`-measurable),
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. The probability spaces range over
`Type`. -/
protected def IsUMDBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X) (σ : ℕ → Ω → ℝ),
    Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, σ n ω = 1 ∨ σ n ω = -1) →
      (∀ k, StronglyMeasurable[ℱ k] (σ (k + 1))) →
      ∀ n, eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖)
          (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ

-- END SHARED DEFINITIONS: umd

-- BEGIN SHARED DEFINITIONS: circle

/-- The trigonometric polynomial `Σ_n c_n e_n` on `𝕋 = ℝ / ℤ`, with coefficients in a complex vector
space. -/
noncomputable def circPoly {V : Type*} [AddCommMonoid V] [Module ℂ V] (c : ℤ →₀ V)
    (t : UnitAddCircle) : V :=
  c.sum fun n x => fourier n t • x

-- END SHARED DEFINITIONS: circle

-- BEGIN SHARED DEFINITIONS: rademacher

/-- The `L^p` norm of the Rademacher sum `Σ_k ε_k f_k` over `α × {±1}^K`, where `{±1}^K` carries the
uniform probability and `true`, `false` stand for the signs `1`, `−1`. -/
noncomputable def eLpNormRad {α : Type*} [MeasurableSpace α] {K : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Fin K → α → E) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  eLpNorm (fun z : α × (Fin K → Bool) => ∑ k, (if z.2 k then (1 : ℝ) else -1) • f k z.1)
    (ENNReal.ofReal p) (μ.prod (ProbabilityTheory.uniformOn Set.univ))

-- END SHARED DEFINITIONS: rademacher

-- BEGIN SHARED DEFINITIONS: dyadic

/-- The intervals of HNVW I, Corollary 5.3.25 (p. 419): `I_0 = (−1, 1)`, and `I_k = (2^{k−1}, 2^k)`,
`I_{−k} = (−2^k, −2^{k−1})` for `k > 0`. -/
def lineBlock (k : ℤ) : Set ℝ :=
  if k = 0 then Set.Ioo (-1) 1 else if 0 < k then Set.Ioo (2 ^ (k.natAbs - 1)) (2 ^ k.natAbs)
  else Set.Ioo (-2 ^ k.natAbs) (-2 ^ (k.natAbs - 1))

/-- The dyadic blocks of `ℤ` (HNVW I, p. 464): `Ĩ_0 = {0}`, `Ĩ_k = [2^{k−1}, 2^k)`,
`Ĩ_{−k} = (−2^k, −2^{k−1}]`, `k > 0`. -/
def dyadicBlock (k : ℤ) : Set ℤ :=
  if k = 0 then {0} else if 0 < k then Set.Ico (2 ^ (k.natAbs - 1)) (2 ^ k.natAbs)
  else Set.Ioc (-2 ^ k.natAbs) (-2 ^ (k.natAbs - 1))

open scoped Classical in
/-- `Δ̃_s f = Σ_{n ∈ s} c_n e_n`, for a set `s` of frequencies. -/
noncomputable def trigBlock {V : Type*} [AddCommMonoid V] [Module ℂ V] (s : Set ℤ) (c : ℤ →₀ V) :
    UnitAddCircle → V :=
  circPoly (c.filter (· ∈ s))

-- END SHARED DEFINITIONS: dyadic

end HarmonicAnalysis
