module

public import HarmonicAnalysis.VectorValued.LittlewoodPaley.Circle
import HarmonicAnalysis.VectorValued.LittlewoodPaley.Signs
import BanachProbability.UMD.Hilbert

/-!
# Solution: Littlewood–Paley theory for functions with values in UMD spaces

The statements of `palomar/VectorValuedLittlewoodPaley/Challenge.lean`, word for word, proved from
the library. The library uses the UMD constants of BanachProbability, which are those of the
Challenge by definition (`isUMDBound_iff`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace VectorValuedLittlewoodPaleyChallenge

open HarmonicAnalysis AddCircle Filter
open scoped FourierTransform SchwartzMap Topology

/-- The UMD constants of the Challenge are those of BanachProbability. -/
theorem isUMDBound_iff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} {β : ℝ≥0∞} :
    HarmonicAnalysis.IsUMDBound X p β ↔ BanachProbability.IsUMDBound X p β :=
  Iff.rfl

theorem truncatedHilbert_bounded {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : HarmonicAnalysis.IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    eLpNorm (fun x => Real.pi⁻¹ • ∫ y in {y | ε < |x - y| ∧ |x - y| < 2 ^ n * ε}, (x - y)⁻¹ • f y)
        (ENNReal.ofReal p) volume ≤
      (4 * β ^ 2 + 11) * eLpNorm f (ENNReal.ofReal p) volume :=
  eLpNorm_truncatedHilbert_le hp (isUMDBound_iff.1 hβ) hf hε n

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem hilbert_multiplier {G : ℝ → X} (hG : Integrable G) (x : ℝ) :
    Tendsto (fun z : ℝ × ℝ =>
        Real.pi⁻¹ • ∫ y in {y | z.1 < |x - y| ∧ |x - y| < z.2}, (x - y)⁻¹ • 𝓕⁻ G y)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (𝓕⁻ (fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) x)) :=
  tendsto_truncatedHilbert_fourierInv hG x

variable [CompleteSpace X]

theorem hilbert_bounded {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : HarmonicAnalysis.IsUMDBound X p β)
    {G : ℝ → X} (hG : Integrable G) (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) (ENNReal.ofReal p) volume ≤
      (4 * β ^ 2 + 11) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume :=
  eLpNorm_fourierInv_neg_I_sign_le hp (isUMDBound_iff.1 hβ) hG hf

/-- The constants of the library. -/
private theorem littlewoodPaley_const (β : ℝ≥0∞) :
    2 * littlewoodPaleyBound β + hilbertBound β = (144 * β + 1) * (4 * β ^ 2 + 11) := by
  rw [littlewoodPaleyBound, hilbertBound]
  ring

theorem littlewoodPaley_line {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : HarmonicAnalysis.IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    eLpNormRad (fun i : Fin (2 * K + 1) =>
        𝓕⁻ ({ξ | ρ * ξ ∈ lineBlock ((i : ℕ) - K)}.indicator G)) p volume ≤
      (144 * β + 1) * (4 * β ^ 2 + 11) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume :=
  littlewoodPaley_const β ▸ eLpNormRad_lineBlock_dilate_le hp (isUMDBound_iff.1 hβ) hG hf K hρ

theorem littlewoodPaley_circle {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : HarmonicAnalysis.IsUMDBound X p β) (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun i : Fin (2 * K + 1) => trigBlock (dyadicBlock ((i : ℕ) - K)) c) p
        haarAddCircle ≤
      (144 * β + 1) * (4 * β ^ 2 + 11) *
        eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle :=
  littlewoodPaley_const β ▸ eLpNormRad_dyadicBlock_le hp (isUMDBound_iff.1 hβ) c K

theorem transference {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] {p : ℝ}
    (hp : 1 < p) {m : ℝ → X →L[ℂ] Y} (hb : ∃ M : ℝ, ∀ ξ, ‖m ξ‖ ≤ M)
    (hm : ∀ x, AEStronglyMeasurable (fun ξ => m ξ x) volume)
    (hc : ∀ (k : ℤ) (x : X), ContinuousAt (fun ξ => m ξ x) k) {C : ℝ≥0∞}
    (hC : ∀ G : 𝓢(ℝ, X), eLpNorm (𝓕⁻ fun ξ => m ξ (G ξ)) (ENNReal.ofReal p) volume ≤
      C * eLpNorm (𝓕⁻ (G : ℝ → X)) (ENNReal.ofReal p) volume) (a : ℤ →₀ X) :
    eLpNorm (fun t : UnitAddCircle => a.sum fun k x => fourier k t • m k x) (ENNReal.ofReal p)
        haarAddCircle ≤
      C * eLpNorm (circPoly a) (ENNReal.ofReal p) haarAddCircle :=
  let ⟨_, hM⟩ := hb
  eLpNorm_circPoly_multiplier_le hp hM hm hc hC a

end

theorem hilbert_bounded_innerProductSpace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {p : ℝ} (hp : 1 < p) {G : ℝ → H} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (4 * (max p (p / (p - 1)) - 1) ^ 2 + 11) *
        eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  let _ : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have hβ : BanachProbability.IsUMDBound H p (ENNReal.ofReal (max p (p / (p - 1)) - 1)) :=
    (BanachProbability.isUMDBound_umdConst hp).mono
      (BanachProbability.umdConst_le_of_innerProductSpace hp)
  have h0 : 0 ≤ max p (p / (p - 1)) - 1 := by
    have := le_max_left p (p / (p - 1))
    linarith
  refine (eLpNorm_fourierInv_neg_I_sign_le hp hβ hG hf).trans_eq ?_
  rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow h0, ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat, hilbertBound]

theorem mihlin_multiplier : ∃ C : NNReal, ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (p : ℝ), 1 < p → ∀ β : ℝ≥0∞, HarmonicAnalysis.IsUMDBound X p β →
    ∀ (m : ℝ → ℂ) (c : ℝ), ContDiffOn ℝ 2 m {0}ᶜ →
    (∀ k ≤ 2, ∀ ξ ≠ 0, |ξ| ^ k * ‖iteratedDeriv k m ξ‖ ≤ c) → ∀ G : ℝ → X, Integrable G →
      eLpNorm (𝓕⁻ fun ξ => m ξ • G ξ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal c * (C * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierInv_mihlin_le
  exact ⟨C, fun X _ _ _ p hp β hβ m c hm hc G hG =>
    hC X p hp β (isUMDBound_iff.1 hβ) m c ⟨hm, hc⟩ G hG⟩

/-- The multiplier is that of the library, except at `0`. -/
private theorem ae_eq_dyadicSign {ε ε' : ℤ → ℝ} {m : ℝ → ℝ}
    (hm : ∀ j : ℤ, ∀ ξ ∈ Set.Ico ((2 : ℝ) ^ j) (2 ^ (j + 1)), m ξ = ε j)
    (hm' : ∀ j : ℤ, ∀ ξ ∈ Set.Ioc (-(2 : ℝ) ^ (j + 1)) (-2 ^ j), m ξ = ε' j) {ξ : ℝ} (hξ : ξ ≠ 0) :
    m ξ = dyadicSign ε ξ + dyadicSign ε' (-ξ) := by
  rcases lt_or_gt_of_ne hξ with h | h
  · have h1 : 0 < -ξ := neg_pos.2 h
    have h2 := Int.zpow_log_le_self one_lt_two h1
    have h3 := Int.lt_zpow_succ_log_self one_lt_two (-ξ)
    push_cast at h2 h3
    rw [hm' (Int.log 2 (-ξ)) ξ ⟨by linarith, by linarith⟩, dyadicSign, dyadicSign,
      ite_eq_right h.not_gt, ite_eq_left h1, zero_add]
  · have h2 := Int.zpow_log_le_self one_lt_two h
    have h3 := Int.lt_zpow_succ_log_self one_lt_two ξ
    push_cast at h2 h3
    rw [hm (Int.log 2 ξ) ξ ⟨h2, h3⟩, dyadicSign, dyadicSign, ite_eq_left h,
      ite_eq_right (by linarith), add_zero]

theorem littlewoodPaley_signs : ∃ C : NNReal, ∀ (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p → ∀ β : ℝ≥0∞,
    HarmonicAnalysis.IsUMDBound X p β → ∀ ε ε' : ℤ → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) →
    (∀ j, ε' j = 1 ∨ ε' j = -1) → ∀ m : ℝ → ℝ,
    (∀ j : ℤ, ∀ ξ ∈ Set.Ico ((2 : ℝ) ^ j) (2 ^ (j + 1)), m ξ = ε j) →
    (∀ j : ℤ, ∀ ξ ∈ Set.Ioc (-(2 : ℝ) ^ (j + 1)) (-2 ^ j), m ξ = ε' j) →
    ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => (m ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * (4 * β ^ 2 + 11) ^ 2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ∧
      eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * (4 * β ^ 2 + 11) ^ 2 *
          eLpNorm (𝓕⁻ fun ξ => (m ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierInv_dyadicSign_le
  refine ⟨C, fun X _ _ _ p hp β hβ ε ε' hε hε' m hm hm' G hG hf => ?_⟩
  have h : 𝓕⁻ (fun ξ => (m ξ : ℂ) • G ξ) =
      𝓕⁻ fun ξ => ((dyadicSign ε ξ + dyadicSign ε' (-ξ) : ℝ) : ℂ) • G ξ := by
    funext x
    refine Real.fourierInv_congr_ae ?_ x
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ξ hξ
    rw [ae_eq_dyadicSign hm hm' hξ]
  rw [h]
  exact hC X p hp β (isUMDBound_iff.1 hβ) ε ε' hε hε' G hG hf

theorem eLpNormRad_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p) {K : ℕ} {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad f p μ ^ p = ((2 : ℝ≥0∞) ^ K)⁻¹ * ∑ ε : Fin K → Bool,
      eLpNorm (fun x => ∑ k, (if ε k then (1 : ℝ) else -1) • f k x) (ENNReal.ofReal p) μ ^ p :=
  HarmonicAnalysis.eLpNormRad_rpow hp hf

end VectorValuedLittlewoodPaleyChallenge
