module

public import VectorValuedHarmonicAnalysis.Dyadic.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Averages of dyadic shifts are convolutions

Averaging the dyadic shift with kernel `k` over the translates of the dyadic system turns its part
of generation `j` into the convolution with `φ_{2^{−j}}`, where `φ (x) = ∫ k (x + u) h (u) du`
(`haarCorrelation k`) and `φ_t (x) = t⁻¹ φ (t⁻¹ x)` (`intervalIntegral_dyadicShift_translate`; HNVW
I, Lemma 5.1.9, p. 381). With the bounds for the dyadic shifts this gives, on a UMD space `X` (HNVW
I, Proposition 5.1.10, p. 383, for finitely many generations):

* `‖Σ_j ε_j φ_{2^{−j}} * f‖_{L^p (ℝ × Ω)} ≤ 2 β ‖f‖_p`, for `k = h` (`eLpNormRad_dilateConv_le`);
* `‖Σ_j φ_{t 2^{−j}} * f‖_p ≤ 2 β² ‖f‖_p`, for `k = haarSplit` and every `t > 0`
  (`eLpNorm_sum_dilateConv_le`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), pp. 379–384.
The book averages over the random dyadic systems `𝒟^ω`, `ω ∈ {0, 1}^ℤ`; for the generations `j ≥ 0`
only, `𝒟^ω` is the translate of the standard system by a point of `[0, 1)`, uniformly distributed.
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal

namespace VectorValuedHarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- HNVW I, (5.14): `φ (x) = ∫ k (x + u) h (u) du`. -/
noncomputable def haarCorrelation (k : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, k (x + u) * haar u

/-- The convolution `φ_t * f`, `φ_t (x) = t⁻¹ φ (t⁻¹ x)`. -/
noncomputable def dilateConv (φ : ℝ → ℝ) (t : ℝ) (f : ℝ → X) (x : ℝ) : X :=
  ∫ y, (t⁻¹ * φ (t⁻¹ * (x - y))) • f y

/-- HNVW I, Lemma 5.1.9: averaging over the translates of the dyadic system gives a convolution. -/
theorem intervalIntegral_dyadicShift_translate {k : ℝ → ℝ} (hk : k = haar ∨ k = haarSplit) (j : ℕ)
    {f : ℝ → X} (hf : LocallyIntegrable f) (x : ℝ) :
    ∫ u in (0 : ℝ)..1, dyadicShift k j (fun y => f (y + u)) (x - u) =
      dilateConv (haarCorrelation k) (((2 : ℝ) ^ j)⁻¹) f x := by
  sorry

/-- HNVW I, Proposition 5.1.10, second inequality, for the generations `0 ≤ j < n`. -/
theorem eLpNormRad_dilateConv_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) (hfm : StronglyMeasurable f) (n : ℕ) :
    eLpNormRad (fun j : Fin n => dilateConv (haarCorrelation haar) (((2 : ℝ) ^ (j : ℕ))⁻¹) f) p
        volume ≤
      2 * β * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

/-- HNVW I, Proposition 5.1.10, first inequality, before the integration over the dilations. -/
theorem eLpNorm_sum_dilateConv_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) (hfm : StronglyMeasurable f) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    eLpNorm (fun x => ∑ j ∈ Finset.range n,
        dilateConv (haarCorrelation haarSplit) (t * ((2 : ℝ) ^ j)⁻¹) f x) (ENNReal.ofReal p)
        volume ≤
      2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

end VectorValuedHarmonicAnalysis
