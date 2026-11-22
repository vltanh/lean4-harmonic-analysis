/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Torus.Smooth
public import HarmonicAnalysis.BeurlingAhlfors.Transference

/-!
# The Beurling–Ahlfors transform on smooth periodic functions

On `ℤ²`-periodic functions on `ℝ² ≅ ℂ`, the powers `𝓑^k` of the Beurling–Ahlfors transform are
the Fourier multipliers `UnitAddTorus.periodicMultiplier` with the symbols `m (ν)^k`,
`m (ξ) = ξ̄ / ξ` (`HarmonicAnalysis.beurlingSymbol`), `ν = n₀ + i n₁`
(`HarmonicAnalysis.latticePoint`):

* the symbols are bounded, hence polynomially bounded
  (`HarmonicAnalysis.isPolyBounded_beurlingSymbol_pow`);
* `𝓑 (∂̄g) = ∂g` for every smooth periodic `g`
  (`HarmonicAnalysis.periodicMultiplier_beurlingSymbol_dzbarPi`), by comparing coefficients:
  `m (ν) πi ν = πi ν̄`;
* on trigonometric polynomials, `𝓑^k` is the torus multiplier `HarmonicAnalysis.torusBeurlingPow`
  (`HarmonicAnalysis.periodicMultiplier_trigPoly`).
-/

@[expose] public section

noncomputable section

open Complex
open scoped ComplexConjugate Real ContDiff

namespace HarmonicAnalysis

open UnitAddTorus

/-- The symbols `m (n₀ + i n₁)^k` of `𝓑^k` on `𝕋²` are polynomially bounded (by `1`). -/
theorem isPolyBounded_beurlingSymbol_pow (k : ℕ) :
    IsPolyBounded fun n => beurlingSymbol (latticePoint n) ^ k := by
  sorry

/-- `𝓑 (∂̄g) = ∂g` for every smooth `ℤ²`-periodic `g : ℝ² → ℂ`. -/
theorem periodicMultiplier_beurlingSymbol_dzbarPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) :
    periodicMultiplier (fun n => beurlingSymbol (latticePoint n)) (dzbarPi g) = dzPi g := by
  sorry

/-- On trigonometric polynomials, `𝓑^k` is the torus multiplier `torusBeurlingPow k`. -/
theorem periodicMultiplier_trigPoly (k : ℕ) (c : (Fin 2 → ℤ) →₀ ℂ) :
    periodicMultiplier (fun n => beurlingSymbol (latticePoint n) ^ k)
        (fun x => trigPoly c (ofPi x)) =
      fun x => torusBeurlingPow k c (ofPi x) := by
  sorry

end HarmonicAnalysis
