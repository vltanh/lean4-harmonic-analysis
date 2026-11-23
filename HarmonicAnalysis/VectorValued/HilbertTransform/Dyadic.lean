/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.HilbertTransform.Truncated
import all HarmonicAnalysis.VectorValued.HilbertTransform.Fourier

/-!
# The Hilbert transform on UMD spaces, by dyadic shifts

On a UMD space `X`, with a `UMD_p` constant `β`, `1 < p < ∞`, and for `f = 𝓕⁻ G ∈ L^p` with
`G ∈ L¹`, that is, `f ∈ L^p ∩ Ľ¹`,

`‖𝓕⁻ (−i sgn · G)‖_p = ‖𝓕⁻ (sgn · G)‖_p ≤ (4 β² + 11) ‖𝓕⁻ G‖_p`
(`eLpNorm_fourierInv_neg_I_sign_le_dyadic`, `eLpNorm_fourierInv_sign_le_dyadic`).

This is the inequality for the Hilbert transform on the class `L^p ∩ Ľ¹`; its extension to all of
`L^p (ℝ; X)` by density is not carried out here.

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016),
Theorem 5.1.13, pp. 385–386, for the bound, and Proposition 5.2.2, p. 389.

Departure from the source: in the book the bound is that of Theorem 5.1.13 for the limit `H f` of
the truncations in `L^p`. Here the truncations are bounded uniformly
(`eLpNorm_truncatedHilbert_le`, `VectorValued.HilbertTransform.Truncated`), the limit is the
pointwise one of Proposition 5.2.2 (`tendsto_truncatedHilbert_fourierInv`,
`VectorValued.HilbertTransform.Fourier`, whose private lemmas on the symbols are used here), and the
bound passes to it by Fatou's lemma.
-/

@[expose] public section

open MeasureTheory BanachProbability Filter Topology
open scoped ENNReal FourierTransform

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The bound `4 β² + 11` for the Hilbert transform from the dyadic shifts (HNVW I, Theorem 5.1.13);
`hilbertBound` is Burkholder's `2 β² + 1`. -/
noncomputable def dyadicHilbertBound (β : ℝ≥0∞) : ℝ≥0∞ := 4 * β ^ 2 + 11

/-- The truncations `ε_i = 2^{−i}`, `R_i = 2^i = 2^{2i} ε_i`. -/
private theorem tendsto_two_pow : Tendsto (fun i : ℕ => (((2 : ℝ) ^ i)⁻¹, 2 ^ (2 * i) *
    ((2 : ℝ) ^ i)⁻¹)) atTop (𝓝[>] 0 ×ˢ atTop) := by
  have hR : ∀ i : ℕ, 2 ^ (2 * i) * ((2 : ℝ) ^ i)⁻¹ = 2 ^ i := fun i => by
    rw [two_mul, pow_add, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  have hpow : Tendsto (fun i : ℕ => (2 : ℝ) ^ i) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  simp_rw [hR]
  exact (tendsto_nhdsWithin_iff.2 ⟨hpow.inv_tendsto_atTop, Eventually.of_forall fun i =>
    inv_pos.2 (pow_pos two_pos i)⟩).prodMk hpow

/-- **The Hilbert transform on UMD spaces** (HNVW I, Theorem 5.1.13 and Proposition 5.2.2): the
inequality `‖H f‖_p ≤ (4 β² + 11) ‖f‖_p`, `1 < p < ∞`, for the functions `f = 𝓕⁻ G ∈ L^p` with
`G ∈ L¹` (the book's `L^p ∩ Ľ¹`), where `H f = 𝓕⁻ (−i sgn · G)`. The extension to `L^p (ℝ; X)` by
density is not part of the statement.

Departure from the source: the book has `H_{ε,R} f → H f` in `L^p`. Here the limit is the pointwise
one of Proposition 5.2.2, for `ε = 2^{−i}` and `R = 2^i`, and the uniform bound of the truncations
passes to it by Fatou's lemma. -/
theorem eLpNorm_fourierInv_neg_I_sign_le_dyadic [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) (ENNReal.ofReal p) volume ≤
      dyadicHilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hε : ∀ i : ℕ, 0 < ((2 : ℝ) ^ i)⁻¹ := fun i => by positivity
  -- the truncations are continuous functions
  have hcont : ∀ i : ℕ,
      Continuous (truncatedHilbert ((2 : ℝ) ^ i)⁻¹ (2 ^ (2 * i) * ((2 : ℝ) ^ i)⁻¹) (𝓕⁻ G)) := by
    intro i
    have hεR := le_mul_of_one_le_left (hε i).le (one_le_pow₀ (n := 2 * i) one_le_two)
    rw [truncatedHilbert_fourierInv hG (hε i) hεR]
    exact continuous_fourierInv_of_integrable (integrable_symbol_smul hG
      (measurable_truncatedSymbol _ _) (norm_truncatedSymbol_le (hε i) hεR))
  have hsym : Integrable fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ :=
    integrable_symbol_smul hG
      (measurable_const.mul (Complex.measurable_ofReal.comp measurable_realSign)) (C := 1)
      fun ξ => by
        rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real]
        exact abs_sign_le ξ
  -- Fatou's lemma
  exact (Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p) (μ := volume)
    (fun i => (hcont i).aestronglyMeasurable) _
    (continuous_fourierInv_of_integrable hsym).aestronglyMeasurable
    (ae_of_all _ fun x => (tendsto_truncatedHilbert_fourierInv hG x).comp tendsto_two_pow)).trans
      ((liminf_le_liminf (Eventually.of_forall fun i =>
        eLpNorm_truncatedHilbert_le hp hβ hf (hε i) (2 * i))).trans (liminf_const _).le)

/-- `eLpNorm_fourierInv_neg_I_sign_le_dyadic` for the multiplier `sgn`:
`‖𝓕⁻ (sgn · G)‖_p ≤ (4 β² + 11) ‖𝓕⁻ G‖_p`. -/
theorem eLpNorm_fourierInv_sign_le_dyadic [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      dyadicHilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have h := eLpNorm_fourierInv_neg_I_sign_le_dyadic hp hβ hG hf
  rwa [fourierInv_neg_I_smul, eLpNorm_const_smul, enorm_neg, ← ofReal_norm, Complex.norm_I,
    ENNReal.ofReal_one, one_mul] at h

end HarmonicAnalysis
