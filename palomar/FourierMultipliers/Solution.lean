module

public import HarmonicAnalysis.BeurlingAhlfors.LowerBound
public import HarmonicAnalysis.FourierMultiplier.Extension
public import HarmonicAnalysis.Transference.Homogeneous

/-!
# Solution

The statements of `palomar/FourierMultipliers/Challenge.lean`, word for word, proved from the
library.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace FourierMultipliersChallenge

open HarmonicAnalysis HarmonicAnalysis.BeurlingAhlfors Filter Topology

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem multiplierNorm_spec {m : V → ℂ} (hm : Measurable m) (hb : ∃ C : ℝ, ∀ ξ, ‖m ξ‖ ≤ C) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    (multiplierNorm m p ≠ ∞ →
      ∃! T : Lp ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
          Lp ℂ (ENNReal.ofReal p) (volume : Measure V),
        ∀ f : 𝓢(V, ℂ), T (f.toLp (ENNReal.ofReal p)) =ᵐ[volume] fourierMultiplier m f) ∧
    ∀ T : Lp ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure V),
      (∀ f : 𝓢(V, ℂ), T (f.toLp (ENNReal.ofReal p)) =ᵐ[volume] fourierMultiplier m f) →
        ‖T‖ₑ = multiplierNorm m p :=
  ⟨existsUnique_extension_of_multiplierNorm_ne_top hm hb, fun _ hT => enorm_eq_multiplierNorm hT⟩

theorem multiplierNorm_conjExponent {m : V → ℂ} (hm : Measurable m)
    (hb : ∃ C : ℝ, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p = multiplierNorm m (p / (p - 1)) :=
  HarmonicAnalysis.multiplierNorm_conjExponent hm hb hp

end Euclidean

theorem transference {m : ℂ → ℂ} (hm : ∀ ξ ≠ 0, ContinuousAt m ξ) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝[>] 0)) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤
        liminf (fun j => torusMultiplierNorm (fun k => m (ε j * latticePoint k)) p) atTop ∧
      (liminf (fun j => torusMultiplierNorm (fun k => m (ε j * latticePoint k)) p) atTop ≠ ∞ →
        ∃ C : ℝ, ∀ ξ, ‖m ξ‖ ≤ C) := by
  have hR : Tendsto (fun j => (ε j)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp hε
  have h1 := multiplierNorm_le_liminf_torusMultiplierNorm hm hR hp
  have h2 := exists_norm_le_of_liminf_torusMultiplierNorm_ne_top hm hR (zero_lt_one.trans hp)
  simp only [torusMultiplierNorm_div_inv] at h1 h2
  exact ⟨h1, h2⟩

theorem transference_homogeneous {m : ℂ → ℂ} (hm : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hh : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ torusMultiplierNorm (fun k => m (latticePoint k)) p := by
  refine multiplierNorm_le_torusMultiplierNorm hm (fun t ht ξ => ?_) hp
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [mul_zero]
  · exact hh t ht ξ hξ

theorem beurlingPow_dzbar_iterate (k : ℕ) (F : 𝓢(ℂ, ℂ)) :
    beurlingPow k (dzbar^[k] F) = dz^[k] F ∧ (beurlingPow 1)^[k] (dzbar^[k] F) = dz^[k] F :=
  ⟨HarmonicAnalysis.beurlingPow_dzbar_iterate k F, iterate_beurlingPow_one_dzbar_iterate k F⟩

theorem beurlingPowNorm_conjExponent (k : ℕ) {p : ℝ} (hp : 1 < p) :
    beurlingPowNorm k p = beurlingPowNorm k (p / (p - 1)) :=
  HarmonicAnalysis.beurlingPowNorm_conjExponent k hp

theorem beurlingKappa_two {p : ℝ} (hp : 0 < p) :
    beurlingKappa 2 p = (p - 1) * (2 * p - 1) / (p + 1) :=
  HarmonicAnalysis.beurlingKappa_two hp

theorem dragicevic_limit {p : ℝ} (hp : 1 < p) :
    Tendsto (fun α : ℝ => eLpNorm (dz^[2] (testFun 2 α)) (ENNReal.ofReal p) volume /
        eLpNorm (dzbar^[2] (testFun 2 α)) (ENNReal.ofReal p) volume)
      (𝓝[<] p⁻¹) (𝓝 (ENNReal.ofReal (beurlingKappa 2 p))) :=
  tendsto_eLpNorm_div_testFun hp

theorem dragicevic_lower_bound {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 p) ≤ beurlingPowNorm 2 p :=
  beurlingKappa_two_le_beurlingPowNorm_two hp

theorem dragicevic_lower_bound_pStar {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 (pStar p)) ≤ beurlingPowNorm 2 p :=
  beurlingKappa_two_pStar_le_beurlingPowNorm_two hp

theorem pStar_sub_one_lt_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    ENNReal.ofReal (pStar p - 1) < beurlingPowNorm 2 p :=
  HarmonicAnalysis.pStar_sub_one_lt_beurlingPowNorm_two hp hp2

end FourierMultipliersChallenge
