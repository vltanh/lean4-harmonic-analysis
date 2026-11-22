module

public import VectorValuedHarmonicAnalysis.Dyadic.Average

/-!
# The truncated Hilbert transform on UMD spaces

`H_{ε,R} f (x) = π⁻¹ ∫_{ε < |x − y| < R} f (y) / (x − y) dy` (`truncatedHilbert ε R f`). On a UMD
space the truncations `H_{ε, 2^n ε}` are bounded on `L^p (ℝ; X)`, `1 < p < ∞`, uniformly in `ε > 0`
and `n` (`eLpNorm_truncatedHilbert_le`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Section 5.1.b,
pp. 384–386: with `φ = haarCorrelation haarSplit`, `Φ (x) = ∫_0^x φ` and
`ψ (x) = x⁻¹ Φ (x) 1_{[−1, 1]} (x)`,

`∫_ε^R φ_t * f dt/t = ψ_ε * f − ψ_R * f − (π/8) H_{ε,R} f` (`integral_dilateConv_eq`, (5.23)),

where the left-hand side is an average of the shifts of `Dyadic.Average` over the dilations `t`. The
book shows that the error terms `ψ_ε * f`, `ψ_R * f` tend to `0`; here they are bounded by
`‖ψ‖_1 ‖f‖_p ≤ 2 ‖f‖_p`, which gives the bound for the truncations, with the constant
`(8/π) (2 log 2 · β² + 4) ≤ 4 β² + 11`.
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal

namespace VectorValuedHarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The truncated Hilbert transform `H_{ε,R} f (x) = π⁻¹ ∫_{ε < |x − y| < R} f (y) / (x − y) dy`. -/
noncomputable def truncatedHilbert (ε R : ℝ) (f : ℝ → X) (x : ℝ) : X :=
  Real.pi⁻¹ • ∫ y in {y | ε < |x - y| ∧ |x - y| < R}, (x - y)⁻¹ • f y

/-- The function `φ` of HNVW I, Example 5.1.11 and Theorem 5.1.13: the odd one, for the kernel
(5.19). -/
noncomputable def hilbertProfile : ℝ → ℝ := haarCorrelation haarSplit

/-- HNVW I, (5.22): `ψ (x) = x⁻¹ ∫_0^x φ · 1_{[−1, 1]} (x)`. -/
noncomputable def hilbertError (x : ℝ) : ℝ :=
  (Set.Icc (-1 : ℝ) 1).indicator (fun x => x⁻¹ * ∫ s in (0 : ℝ)..x, hilbertProfile s) x

/-- `∫_0^1 φ = −1/8` (HNVW I, p. 385). -/
theorem integral_hilbertProfile : ∫ s in (0 : ℝ)..1, hilbertProfile s = -1 / 8 := by
  sorry

theorem hilbertProfile_neg (x : ℝ) : hilbertProfile (-x) = -hilbertProfile x := by
  sorry

/-- HNVW I, (5.23). -/
theorem integral_dilateConv_eq {f : ℝ → X} (hf : LocallyIntegrable f) {ε R : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R) (x : ℝ) :
    ∫ t in ε..R, t⁻¹ • dilateConv hilbertProfile t f x =
      dilateConv hilbertError ε f x - dilateConv hilbertError R f x -
        (Real.pi / 8) • truncatedHilbert ε R f x := by
  sorry

/-- **The truncated Hilbert transform on UMD spaces** (HNVW I, Theorem 5.1.13, for the truncations).
-/
theorem eLpNorm_truncatedHilbert_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hfm : StronglyMeasurable f) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    eLpNorm (truncatedHilbert ε (2 ^ n * ε) f) (ENNReal.ofReal p) volume ≤
      (4 * β ^ 2 + 11) * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

end VectorValuedHarmonicAnalysis
