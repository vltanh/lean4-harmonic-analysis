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

attribute [local instance] fact_zero_lt_two_pi

/-- The norm over `(a, a + 2π]` of a function on the circle. -/
private theorem eLpNorm_coe {X : Type*} [NormedAddCommGroup X] {q : ℝ≥0∞} (hq : q ≠ ⊤)
    {F : AddCircle (2 * Real.pi) → X} (hF : AEStronglyMeasurable F haarAddCircle) (a : ℝ) :
    eLpNorm (fun θ : ℝ => F θ) q (volume.restrict (Set.Ioc a (a + 2 * Real.pi))) =
      ENNReal.ofReal (2 * Real.pi) ^ (1 / q).toReal * eLpNorm F q haarAddCircle := by
  have hF' : AEStronglyMeasurable F (ENNReal.ofReal (2 * Real.pi) • haarAddCircle) :=
    hF.smul_measure _
  have h := eLpNorm_comp_measurePreserving (p := q) (g := F) (μ := volume.restrict _)
    (by rw [volume_eq_smul_haarAddCircle]; exact hF')
    (AddCircle.measurePreserving_mk (2 * Real.pi) a)
  rw [volume_eq_smul_haarAddCircle, eLpNorm_smul_measure_of_ne_top hq _ _ hF, smul_eq_mul] at h
  exact h

theorem conjugate_polynomial {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : HarmonicAnalysis.IsUMDBound X p β) (N : ℕ) (a b : ℕ → X)
    (r : ℝ) :
    eLpNorm (fun θ : ℝ => ∑ k ∈ Finset.Icc 1 N,
        r ^ k • (Real.sin (k * θ) • a k - Real.cos (k * θ) • b k)) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) ≤
      β ^ 2 * eLpNorm (fun θ : ℝ => ∑ k ∈ Finset.Icc 1 N,
        r ^ k • (Real.cos (k * θ) • a k + Real.sin (k * θ) • b k)) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
  have hz : ∀ (θ : ℝ) (k : ℕ), ((r : ℂ) * fourier 1 (θ : AddCircle (2 * Real.pi))) ^ k =
      (r ^ k * Real.cos (k * θ) : ℝ) + (r ^ k * Real.sin (k * θ) : ℝ) * Complex.I := fun θ k => by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [fourier_coe_apply, mul_pow, ← Complex.exp_nat_mul,
      show (k : ℂ) * (2 * Real.pi * Complex.I * (1 : ℤ) * θ / (2 * Real.pi : ℝ)) =
        ((k * θ : ℝ) : ℂ) * Complex.I by push_cast; field_simp, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hre : ∀ (θ : ℝ) (k : ℕ), (((r : ℂ) * fourier 1 (θ : AddCircle (2 * Real.pi))) ^ k).re =
      r ^ k * Real.cos (k * θ) := fun θ k => by
    rw [hz, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
  have him : ∀ (θ : ℝ) (k : ℕ), (((r : ℂ) * fourier 1 (θ : AddCircle (2 * Real.pi))) ^ k).im =
      r ^ k * Real.sin (k * θ) := fun θ k => by
    rw [hz, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
      zero_add]
  have hc : Continuous fun θ : AddCircle (2 * Real.pi) => (r : ℂ) * fourier 1 θ :=
    continuous_const.mul (map_continuous (fourier 1))
  have h := eLpNorm_conjHarmPoly_le hp (isUMDBound_iff.1 hβ) N a b r
  have hu := eLpNorm_coe (q := ENNReal.ofReal p) ENNReal.ofReal_ne_top
    ((continuous_harmPoly N a b).comp hc).aestronglyMeasurable 0
  have hv := eLpNorm_coe (q := ENNReal.ofReal p) ENNReal.ofReal_ne_top
    ((continuous_harmPoly N (-b) a).comp hc).aestronglyMeasurable 0
  simp only [Function.comp_def, ← conjHarmPoly_eq, zero_add] at hu hv
  simp only [harmPoly, conjHarmPoly, hre, him, mul_smul, ← smul_sub, ← smul_add] at hu hv h
  rw [hu, hv, mul_left_comm]
  gcongr

theorem conjugate_truncated {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : HarmonicAnalysis.IsUMDBound X p β) {f : ℝ → X}
    (hper : Function.Periodic f (2 * Real.pi))
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    eLpNorm (fun θ => (2 * Real.pi)⁻¹ • ∫ t in {t | ε < |t| ∧ |t| < Real.pi},
        Real.cot (t / 2) • f (θ - t)) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) ≤
      (2 * β ^ 2 + 1) * eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
  have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
  -- the function on the circle
  set F : AddCircle (2 * Real.pi) → X := hper.lift
  have hF : ∀ t : ℝ, F t = f t := hper.lift_coe
  have hmp : MeasurePreserving
      (fun x : AddCircle (2 * Real.pi) => (equivIoc (2 * Real.pi) (-Real.pi) x : ℝ)) volume
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
    have h := (measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
      (measurableSet_Ioc (a := -Real.pi) (b := -Real.pi + 2 * Real.pi))).comp
      (measurePreserving_equivIoc (T := 2 * Real.pi) (a := -Real.pi))
    exact ⟨h.measurable, h.map_eq.trans (by rw [hpi])⟩
  have hFm : MemLp F (ENNReal.ofReal p) haarAddCircle := by
    have h : MemLp F (ENNReal.ofReal p) volume := by
      refine (hf.comp_measurePreserving hmp).ae_eq (ae_of_all _ fun x => ?_)
      rw [Function.comp_apply, ← hF, coe_equivIoc]
    have hT : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
    have h' := h.smul_measure (c := (ENNReal.ofReal (2 * Real.pi))⁻¹) (ENNReal.inv_ne_top.2 hT)
    rwa [volume_eq_smul_haarAddCircle, smul_smul, ENNReal.inv_mul_cancel hT ENNReal.ofReal_ne_top,
      one_smul] at h'
  have h := eLpNorm_truncatedConj_le hp (isUMDBound_iff.1 hβ) hFm hε0 hε1
  have hu := eLpNorm_coe (q := ENNReal.ofReal p) ENNReal.ofReal_ne_top hFm.aestronglyMeasurable
    (-Real.pi)
  have hv := eLpNorm_coe (q := ENNReal.ofReal p) ENNReal.ofReal_ne_top
    (stronglyMeasurable_truncatedConj hFm.aestronglyMeasurable ε).aestronglyMeasurable (-Real.pi)
  simp only [hpi, truncatedConj, ← coe_sub, hF] at hu hv
  rw [hu, hv, mul_left_comm]
  gcongr
  exact h

theorem hilbertTruncation_bounded {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : HarmonicAnalysis.IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (fun x => Real.pi⁻¹ • ∫ t in {t | ε < |t|}, t⁻¹ • f (x - t)) (ENNReal.ofReal p)
        volume ≤
      (2 * β ^ 2 + 1) * eLpNorm f (ENNReal.ofReal p) volume :=
  eLpNorm_hilbertTrunc_le hp (isUMDBound_iff.1 hβ) hf hε

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
      (2 * β ^ 2 + 1) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume :=
  eLpNorm_fourierInv_neg_I_sign_le hp (isUMDBound_iff.1 hβ) hG hf

/-- The constants of the library. -/
private theorem littlewoodPaley_const (β : ℝ≥0∞) :
    2 * littlewoodPaleyBound β + dyadicHilbertBound β = (144 * β + 1) * (4 * β ^ 2 + 11) := by
  rw [littlewoodPaleyBound, dyadicHilbertBound]
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
      ENNReal.ofReal (2 * (max p (p / (p - 1)) - 1) ^ 2 + 1) *
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
    ENNReal.ofReal_pow h0, ENNReal.ofReal_ofNat, ENNReal.ofReal_one, hilbertBound]

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
        C * β ^ 8 * (2 * β ^ 2 + 1) ^ 2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ∧
      eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * (2 * β ^ 2 + 1) ^ 2 *
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
