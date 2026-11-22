module

public import VectorValuedHarmonicAnalysis.Dyadic.Martingale
public import VectorValuedHarmonicAnalysis.RademacherNorm

/-!
# Dyadic shifts on UMD spaces

Let `X` be a UMD space, `β` a `UMD_p` constant of `X`, `1 < p < ∞`. For `f ∈ L^p (ℝ; X)`,

* `‖Σ_{j < n} ε_j k_I ⟨h_I, f⟩‖_{L^p (ℝ × Ω)} ≤ 2 β ‖f‖_p` for the Haar projections (`k = h`) and
  for the shift with the kernel `k = haarSplit` (`eLpNormRad_dyadicShift_le`);
* `‖Σ_{j < n} Σ_I k_I ⟨h_I, f⟩‖_{L^p} ≤ 2 β² ‖f‖_p` for `k = haarSplit`
  (`eLpNorm_sum_dyadicShift_le`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Propositions
5.1.4 and 5.1.5, pp. 376–378, for the finitely many generations `0 ≤ j < n` (the factor `2`, which
the book does not have, comes from stopping at generation `0`; the book's shifts are over all
generations).
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal

namespace VectorValuedHarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem stronglyMeasurable_dyadicShift {k : ℝ → ℝ} (hk : Measurable k) (j : ℕ) {f : ℝ → X}
    (hf : LocallyIntegrable f) : StronglyMeasurable (dyadicShift k j f) := by
  sorry

/-- HNVW I, Propositions 5.1.4 and 5.1.5 (right-hand inequalities), for the generations `0 ≤ j < n`.
-/
theorem eLpNormRad_dyadicShift_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {k : ℝ → ℝ} (hk : k = haar ∨ k = haarSplit) {f : ℝ → X}
    (hf : MemLp f (ENNReal.ofReal p) volume) (n : ℕ) :
    eLpNormRad (fun j : Fin n => dyadicShift k j f) p volume ≤
      2 * β * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

/-- HNVW I, Proposition 5.1.5, for the kernel `haarSplit` and the generations `0 ≤ j < n`. -/
theorem eLpNorm_sum_dyadicShift_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) (n : ℕ) :
    eLpNorm (fun x => ∑ j ∈ Finset.range n, dyadicShift haarSplit j f x) (ENNReal.ofReal p) volume ≤
      2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

end VectorValuedHarmonicAnalysis
