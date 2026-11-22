module

public import VectorValuedHarmonicAnalysis.HilbertTransform.Fourier

/-!
# The Littlewood–Paley inequality on the line for UMD spaces

Let `X` be a complex UMD space, `1 < p < ∞` and `I_k = (2^k, 2^{k+1})`. For `f = 𝓕⁻ G ∈ L^p (ℝ; X)`,
`G ∈ L¹`, and
`Δ_{I_k} f = 𝓕⁻ (1_{I_k} G)`,

`‖Σ_{0 ≤ k < K} ε_k Δ_{I_k} f‖_{L^p (ℝ × Ω; X)} ≤ C β ħ ‖f‖_{L^p (ℝ; X)}`
(`eLpNormRad_fourierInv_indicator_le`),

where `β` is a `UMD_p` constant of `X` and `ħ = hilbertBound β` the bound of the Hilbert transform.

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Section 5.3,
pp. 412–419: the interval multipliers from the Hilbert transform, Lemma 5.3.21 (a randomised Mihlin
theorem, from (5.36)), Lemma 5.3.22 (which is Proposition 5.1.10), Lemma 5.3.23 (the multipliers
`1_I / φ̂_I`) and Theorem 5.3.24, right-hand inequality, for the intervals `(2^k, 2^{k+1})`, `k ≥ 0`
(the intervals of `(0, 1)` are reached by dilation, the negative ones by reflection).
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal FourierTransform

namespace VectorValuedHarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `φ̂ (ξ) = sin⁴ (πξ/2) / (πξ/2)²`, the Fourier transform of `φ = h * h̃` (HNVW I, proof of Lemma
5.3.23). -/
theorem fourier_haarCorrelation_haar {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ξ =
      ((Real.sin (Real.pi * ξ / 2) ^ 4 / (Real.pi * ξ / 2) ^ 2 : ℝ) : ℂ) := by
  sorry

/-- The convolution `φ_t * 𝓕⁻ G` as a Fourier multiplier. -/
theorem dilateConv_fourierInv {φ : ℝ → ℝ} (hφ : Integrable φ) {t : ℝ} (ht : 0 < t) {G : ℝ → X}
    (hG : Integrable G) :
    dilateConv φ t (𝓕⁻ G) = 𝓕⁻ fun ξ => 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) (t * ξ) • G ξ := by
  sorry

variable [CompleteSpace X]

/-- HNVW I, p. 413–414: the randomised bound for intervals, from the Hilbert transform. For any
`a_k < b_k`, `‖Σ ε_k Δ_{(a_k, b_k)} f_k‖ ≤ 4 ħ ‖Σ ε_k f_k‖`. -/
theorem eLpNormRad_fourierInv_Ioo_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) {a b : Fin K → ℝ}
    (hab : ∀ k, a k ≤ b k) :
    eLpNormRad (fun k => 𝓕⁻ ((Set.Ioo (a k) (b k)).indicator (G k))) p volume ≤
      4 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  sorry

/-- HNVW I, Lemmas 5.3.21 and 5.3.23: the randomised bound for the multipliers
`1_{I_k} / φ̂ (2^{−k−1} ·)`. -/
theorem eLpNormRad_fourierInv_div_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) :
    eLpNormRad (fun k => 𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator fun ξ =>
        (𝓕 (fun x : ℝ => ((haarCorrelation haar x : ℝ) : ℂ)) ((2 ^ ((k : ℕ) + 1))⁻¹ * ξ))⁻¹ •
          G k ξ)) p volume ≤
      36 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  sorry

/-- The Littlewood–Paley constant. -/
noncomputable def littlewoodPaleyBound (β : ℝ≥0∞) : ℝ≥0∞ := 72 * hilbertBound β * β

/-- **The Littlewood–Paley inequality on the line** (HNVW I, Theorem 5.3.24, right-hand inequality),
for the intervals `(2^k, 2^{k+1})`, `0 ≤ k < K`. -/
theorem eLpNormRad_fourierInv_indicator_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) :
    eLpNormRad (fun k : Fin K =>
        𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator G)) p volume ≤
      littlewoodPaleyBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  sorry

end VectorValuedHarmonicAnalysis
