module

public import BanachProbability.SignCube.Bridge
public import BanachProbability.RandomSums.Contraction

/-!
# Norms of Rademacher sums of functions

For functions `f_1, …, f_K : α → E` and independent fair signs `ε_k`,
`eLpNormRad f p μ = ‖Σ_k ε_k f_k‖_{L^p (α × {±1}^K; E)}`, the norm of the Rademacher sum in `L^p` of
the product of `μ` with the uniform probability on the signs. Facts: the `p`-th power is the average
over the signs (`eLpNormRad_rpow`); bounds that hold for every fixed choice of signs
(`eLpNormRad_le_of_forall`); the triangle inequality; Kahane's contraction principle for pointwise
multipliers (`eLpNormRad_smul_le`); Minkowski's integral inequality (`eLpNormRad_integral_le`).
-/

@[expose] public section

open MeasureTheory BanachProbability BanachProbability.SignCube
open scoped ENNReal

namespace VectorValuedHarmonicAnalysis

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `L^p` norm of the Rademacher sum `Σ_k ε_k f_k` over `α × {±1}^K`. -/
noncomputable def eLpNormRad (f : Fin K → α → E) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  eLpNorm (fun z : α × (Fin K → Bool) => ∑ k, coin (z.2 k) • f k z.1) (ENNReal.ofReal p)
    (μ.prod (ProbabilityTheory.uniformOn Set.univ))

/-- `‖Σ ε_k f_k‖_p^p` is the average over the signs of the `p`-th powers of the norms of
`Σ ε_k f_k`. -/
theorem eLpNormRad_rpow [SFinite μ] {p : ℝ} (hp : 0 < p) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad f p μ ^ p = ((2 : ℝ≥0∞) ^ K)⁻¹ * ∑ ε : Fin K → Bool,
      eLpNorm (fun x => ∑ k, coin (ε k) • f k x) (ENNReal.ofReal p) μ ^ p := by
  sorry

/-- The `p`-th power as an integral of averages over the sign cube. -/
theorem eLpNormRad_rpow_eq_lintegral [SFinite μ] {p : ℝ} (hp : 0 < p) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad f p μ ^ p = ∫⁻ x, ENNReal.ofReal (SignCube.lpNorm (fun y => ‖y‖) p
      (fun ε : Fin K → Bool => ∑ k, coin (ε k) • f k x) ^ p) ∂μ := by
  sorry

/-- A bound that holds for every fixed choice of signs holds for the Rademacher sums. -/
theorem eLpNormRad_le_of_forall [SFinite μ] {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SFinite ν] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ} (hp : 0 < p)
    {f : Fin K → α → E} (hf : ∀ k, AEStronglyMeasurable (f k) μ) {g : Fin K → β → F}
    (hg : ∀ k, AEStronglyMeasurable (g k) ν) {C : ℝ≥0∞}
    (h : ∀ ε : Fin K → Bool, eLpNorm (fun x => ∑ k, coin (ε k) • f k x) (ENNReal.ofReal p) μ ≤
      C * eLpNorm (fun x => ∑ k, coin (ε k) • g k x) (ENNReal.ofReal p) ν) :
    eLpNormRad f p μ ≤ C * eLpNormRad g p ν := by
  sorry

theorem eLpNormRad_congr_ae [SFinite μ] {p : ℝ} {f g : Fin K → α → E} (h : ∀ k, f k =ᵐ[μ] g k) :
    eLpNormRad f p μ = eLpNormRad g p μ := by
  sorry

theorem eLpNormRad_add_le [SFinite μ] {p : ℝ} (hp : 1 ≤ p) {f g : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) (hg : ∀ k, AEStronglyMeasurable (g k) μ) :
    eLpNormRad (fun k x => f k x + g k x) p μ ≤ eLpNormRad f p μ + eLpNormRad g p μ := by
  sorry

/-- **Kahane's contraction principle** for pointwise multipliers `c_k (x) ∈ ℂ`, `|c_k (x)| ≤ 1`,
with the factor `2` (real signs). -/
theorem eLpNormRad_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SFinite μ] {p : ℝ}
    (hp : 1 ≤ p) {c : Fin K → α → ℂ} (hc : ∀ k x, ‖c k x‖ ≤ 1)
    (hcm : ∀ k, AEStronglyMeasurable (c k) μ) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad (fun k x => c k x • f k x) p μ ≤ 2 * eLpNormRad f p μ := by
  sorry

/-- Subsets of the Rademacher sum: a Rademacher sum dominates each partial one. -/
theorem eLpNormRad_indicator_le [SFinite μ] {p : ℝ} (hp : 1 ≤ p) (s : Set (Fin K))
    {f : Fin K → α → E} (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad (s.indicator f) p μ ≤ eLpNormRad f p μ := by
  sorry

/-- Minkowski's integral inequality for Rademacher sums:
`‖Σ_k ε_k ∫ F_k (s, ·) dν‖ ≤ ∫ ‖Σ_k ε_k F_k (s, ·)‖ dν`. -/
theorem eLpNormRad_integral_le [SFinite μ] {S : Type*} [MeasurableSpace S] {ν : Measure S}
    [SFinite ν] {p : ℝ} (hp : 1 ≤ p) {F : Fin K → S → α → E}
    (hF : ∀ k, StronglyMeasurable (Function.uncurry (F k)))
    (hFi : ∀ k, ∀ᵐ x ∂μ, Integrable (fun s => F k s x) ν) :
    eLpNormRad (fun k x => ∫ s, F k s x ∂ν) p μ ≤ ∫⁻ s, eLpNormRad (fun k => F k s) p μ ∂ν := by
  sorry

end VectorValuedHarmonicAnalysis
