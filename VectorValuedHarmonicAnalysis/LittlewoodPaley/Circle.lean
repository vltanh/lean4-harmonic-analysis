module

public import VectorValuedHarmonicAnalysis.LittlewoodPaley.Line
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# The Littlewood–Paley inequality on the circle for UMD spaces

`𝕋 = ℝ / ℤ` with its normalised Haar measure, `e_n (t) = e^{2πi n t}`. For a trigonometric
polynomial `f = Σ_n c_n e_n` (`trigPoly c`) with coefficients in a complex UMD space `X`, and the
dyadic blocks `Ĩ_0 = {0}`, `Ĩ_k = [2^{k−1}, 2^k) ∩ ℤ`, `Ĩ_{−k} = −Ĩ_k` for `k > 0` (`dyadicBlock`),
let
`Δ̃_k f = Σ_{n ∈ Ĩ_k} c_n e_n`. **Theorem** (`eLpNormRad_dyadicBlock_le`): for `1 < p < ∞`,

`‖Σ_{|k| ≤ K} ε_k Δ̃_k f‖_{L^p (Ω × 𝕋; X)} ≤ C_β ‖f‖_{L^p (𝕋; X)}`,

with a constant that depends only on a `UMD_p` constant `β` of `X`.

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Theorem 5.7.10
(2), right-hand inequality, pp. 464–466: transference from the line (Proposition 5.7.1 and Lemma
5.7.3, pp. 458–459), with the dilation trick that moves the dyadic points off the lattice. The
left-hand inequality and the operator-valued statement (1) of that theorem are not treated.

Also: the projections onto single frequencies are randomised bounded
(`eLpNormRad_singleFrequency_le`), by the contraction principle.
-/

@[expose] public section

open MeasureTheory BanachProbability AddCircle
open scoped ENNReal

namespace VectorValuedHarmonicAnalysis

/-- The trigonometric polynomial `Σ_n c_n e_n` on `𝕋 = ℝ / ℤ`. -/
noncomputable def trigPoly {V : Type*} [AddCommMonoid V] [Module ℂ V] (c : ℤ →₀ V)
    (t : UnitAddCircle) : V :=
  c.sum fun n x => fourier n t • x

/-- The dyadic blocks of `ℤ` (HNVW I, p. 464): `Ĩ_0 = {0}`, `Ĩ_k = [2^{k−1}, 2^k)`,
`Ĩ_{−k} = (−2^k, −2^{k−1}]`, `k > 0`. -/
def dyadicBlock (k : ℤ) : Set ℤ :=
  if k = 0 then {0} else if 0 < k then Set.Ico (2 ^ (k.natAbs - 1)) (2 ^ k.natAbs)
  else Set.Ioc (-2 ^ k.natAbs) (-2 ^ (k.natAbs - 1))

open scoped Classical in
/-- `Δ̃_s f = Σ_{n ∈ s} c_n e_n`, for a set `s` of frequencies. -/
noncomputable def trigBlock {V : Type*} [AddCommMonoid V] [Module ℂ V] (s : Set ℤ) (c : ℤ →₀ V) :
    UnitAddCircle → V :=
  trigPoly (c.filter (· ∈ s))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem continuous_trigPoly (c : ℤ →₀ X) : Continuous (trigPoly c) := by
  sorry

/-- HNVW I, Lemma 5.7.3: `ε ∫_ℝ ‖f (ρ x)‖^p |θ (ε x)|^p dx → ‖f‖_{L^p (𝕋)}^p ‖θ‖_{L^p (ℝ)}^p` as
`ε → 0⁺`, for a continuous `f` on `𝕋`, `ρ > 0` and an integrable `w = |θ|^p`. -/
theorem tendsto_integral_dilate {g : UnitAddCircle → ℝ} (hg : Continuous g) {w : ℝ → ℝ}
    (hw : Integrable w) {ρ : ℝ} (hρ : 0 < ρ) :
    Filter.Tendsto (fun ε : ℝ => ε * ∫ x : ℝ, g (ρ * x : ℝ) * w (ε * x)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∫ t, g t ∂haarAddCircle) * ∫ x, w x)) := by
  sorry

variable [CompleteSpace X]

/-- The Littlewood–Paley inequality on `𝕋` for the blocks `Ĩ_{k+1} = [2^k, 2^{k+1})`, `0 ≤ k < K`.
-/
theorem eLpNormRad_dyadicBlock_succ_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun k : Fin K => trigBlock (dyadicBlock ((k : ℕ) + 1)) c) p haarAddCircle ≤
      littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle := by
  sorry

/-- **The Littlewood–Paley inequality on the circle** (HNVW I, Theorem 5.7.10 (2), right-hand
inequality): for a complex UMD space `X`, `1 < p < ∞` and a trigonometric polynomial
`f = Σ c_n e_n`, `‖Σ_{|k| ≤ K} ε_k Δ̃_k f‖_{L^p (Ω × 𝕋; X)} ≤ C_β ‖f‖_{L^p (𝕋; X)}`. -/
theorem eLpNormRad_dyadicBlock_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun k : Fin (2 * K + 1) => trigBlock (dyadicBlock ((k : ℕ) - K)) c) p
        haarAddCircle ≤
      (2 * littlewoodPaleyBound β + 1) * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle := by
  sorry

omit [CompleteSpace X] in
/-- The projections onto single frequencies are randomised bounded: for trigonometric polynomials
`f_k = Σ_n c_k (n) e_n` and any `n_k ∈ ℤ`, `‖Σ ε_k c_k (n_k) e_{n_k}‖ ≤ 4 ‖Σ ε_k f_k‖`. -/
theorem eLpNormRad_singleFrequency_le {p : ℝ} (hp : 1 ≤ p) {K : ℕ} (c : Fin K → ℤ →₀ X)
    (n : Fin K → ℤ) :
    eLpNormRad (fun k (t : UnitAddCircle) => fourier (n k) t • c k (n k)) p haarAddCircle ≤
      4 * eLpNormRad (fun k => trigPoly (c k)) p haarAddCircle := by
  sorry

end VectorValuedHarmonicAnalysis
