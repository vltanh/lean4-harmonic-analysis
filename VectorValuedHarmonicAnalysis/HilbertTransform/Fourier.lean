module

public import VectorValuedHarmonicAnalysis.HilbertTransform.Truncated
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Basic.Real.Sign

/-!
# The Fourier multiplier `sgn` on UMD spaces

Let `X` be a complex Banach space. For `G ∈ L¹ (ℝ; X)`, `f = 𝓕⁻ G` is a bounded continuous function,
and a bounded measurable `m` acts on it by `T_m f = 𝓕⁻ (m G)` (HNVW's class `Ľ¹`). The truncated
Hilbert transform acts with the symbol
`−i sgn (ξ) m_{ε,R} (ξ)`, `|m_{ε,R}| ≤ 2`, `m_{ε,R} → 1` (`truncatedHilbert_fourierInv`,
`abs_hilbertSymbol_le`, `tendsto_hilbertSymbol`; Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis
in Banach spaces I* (2016), Lemma 5.2.1, pp. 388–389: Cauchy's theorem on a half annulus). With
Fatou's lemma, on a UMD space `X`, `‖𝓕⁻ (sgn · G)‖_p ≤ (4 β² + 11) ‖𝓕⁻ G‖_p`
(`eLpNorm_fourierInv_sign_le`): the Hilbert transform is bounded on `L^p (ℝ; X)`, `1 < p < ∞`.
-/

@[expose] public section

open MeasureTheory BanachProbability Filter Topology
open scoped ENNReal FourierTransform

namespace VectorValuedHarmonicAnalysis

/-- HNVW I, Lemma 5.2.1: the function `m_{ε,R}`,
`−i sgn (ξ) m_{ε,R} (ξ) = π⁻¹ ∫_{ε < |x| < R} e^{−2πi x ξ} dx / x`, that is,
`m_{ε,R} (ξ) = (2/π) ∫_ε^R sin (2π |ξ| x) / x dx`. -/
noncomputable def hilbertSymbol (ε R ξ : ℝ) : ℝ :=
  2 / Real.pi * ∫ x in ε..R, Real.sin (2 * Real.pi * |ξ| * x) / x

/-- HNVW I, Lemma 5.2.1: `|m_{ε,R}| ≤ 2`. -/
theorem abs_hilbertSymbol_le {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (ξ : ℝ) :
    |hilbertSymbol ε R ξ| ≤ 2 := by
  sorry

/-- HNVW I, Lemma 5.2.1: `m_{ε,R} (ξ) → 1` as `ε → 0` and `R → ∞`, `ξ ≠ 0`. -/
theorem tendsto_hilbertSymbol {ξ : ℝ} (hξ : ξ ≠ 0) :
    Tendsto (fun z : ℝ × ℝ => hilbertSymbol z.1 z.2 ξ) (𝓝[>] 0 ×ˢ atTop) (𝓝 1) := by
  sorry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- HNVW I, Lemma 5.2.1: the truncated Hilbert transform as a Fourier multiplier. -/
theorem truncatedHilbert_fourierInv {G : ℝ → X} (hG : Integrable G) {ε R : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ R) :
    truncatedHilbert ε R (𝓕⁻ G) =
      𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ) * (hilbertSymbol ε R ξ : ℂ)) • G ξ := by
  sorry

/-- The bound for the Hilbert transform in terms of a `UMD_p` constant. -/
noncomputable def hilbertBound (β : ℝ≥0∞) : ℝ≥0∞ := 4 * β ^ 2 + 11

/-- **The Hilbert transform on UMD spaces** (HNVW I, Theorem 5.1.13 and Lemma 5.2.1): the Fourier
multiplier `sgn` is bounded on `L^p (ℝ; X)`, `1 < p < ∞`. -/
theorem eLpNorm_fourierInv_sign_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  sorry

end VectorValuedHarmonicAnalysis
