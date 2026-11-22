module

public import BanachProbability.SignCube.Bridge
public import BanachProbability.RandomSums.Contraction
import Mathlib.MeasureTheory.Integral.Prod

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

/-! ### Averages over the signs -/

/-- The average over the cube of nonnegative numbers, in `[0, ∞]`. -/
private theorem rad_ofReal_avg {a : (Fin K → Bool) → ℝ} (ha : ∀ ε, 0 ≤ a ε) :
    ENNReal.ofReal (avg a) = ((2 : ℝ≥0∞) ^ K)⁻¹ * ∑ ε, ENNReal.ofReal (a ε) := by
  rw [avg, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_sum_of_nonneg fun ε _ => ha ε,
    ENNReal.div_eq_inv_mul, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- The integral over the uniform probability on the cube is the average. -/
private theorem rad_lintegral_uniformOn (G : (Fin K → Bool) → ℝ≥0∞) :
    ∫⁻ η, G η ∂(ProbabilityTheory.uniformOn Set.univ) = ((2 : ℝ≥0∞) ^ K)⁻¹ * ∑ η, G η := by
  rw [lintegral_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  have hμ : (ProbabilityTheory.uniformOn (Set.univ : Set (Fin K → Bool))) {η} =
      ((2 : ℝ≥0∞) ^ K)⁻¹ := by
    rw [← ofReal_measureReal, uniformOn_singleton, one_div,
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [hμ, mul_comm]

/-- The `p`-th power of the `L^p` norm is the integral of the `p`-th power of the norm. -/
private theorem rad_eLpNorm_rpow {S F : Type*} [NormedAddCommGroup F] {mS : MeasurableSpace S}
    {ν : Measure S} {p : ℝ} (hp : 0 < p) {f : S → F} (hf : AEStronglyMeasurable f ν) :
    eLpNorm f (ENNReal.ofReal p) ν ^ p = ∫⁻ z, ‖f z‖ₑ ^ p ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- The Rademacher sum of measurable functions is measurable on the product. -/
private theorem rad_aestronglyMeasurable {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) (ν : Measure (Fin K → Bool)) [SFinite ν] :
    AEStronglyMeasurable (fun z : α × (Fin K → Bool) => ∑ k, coin (z.2 k) • f k z.1)
      (μ.prod ν) :=
  Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
    ((StronglyMeasurable.of_discrete (f := fun η : Fin K → Bool => coin (η k))).comp_measurable
      measurable_snd).aestronglyMeasurable.smul (hf k).comp_fst

/-- The signed sum of measurable functions is measurable. -/
private theorem rad_aestronglyMeasurable_sum {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) (ε : Fin K → Bool) :
    AEStronglyMeasurable (fun x => ∑ k, coin (ε k) • f k x) μ :=
  Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hf k).const_smul _

/-- `‖Σ ε_k f_k‖_p^p` is the average over the signs of the `p`-th powers of the norms of
`Σ ε_k f_k`. -/
theorem eLpNormRad_rpow [SFinite μ] {p : ℝ} (hp : 0 < p) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad f p μ ^ p = ((2 : ℝ≥0∞) ^ K)⁻¹ * ∑ ε : Fin K → Bool,
      eLpNorm (fun x => ∑ k, coin (ε k) • f k x) (ENNReal.ofReal p) μ ^ p := by
  have hm := rad_aestronglyMeasurable hf (ProbabilityTheory.uniformOn Set.univ)
  rw [eLpNormRad, rad_eLpNorm_rpow hp hm, lintegral_prod_symm _ (hm.enorm.pow_const p),
    rad_lintegral_uniformOn]
  congr 1
  exact Finset.sum_congr rfl fun η _ =>
    (rad_eLpNorm_rpow hp (rad_aestronglyMeasurable_sum hf η)).symm

/-- The `p`-th power as an integral of averages over the sign cube. -/
theorem eLpNormRad_rpow_eq_lintegral [SFinite μ] {p : ℝ} (hp : 0 < p) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad f p μ ^ p = ∫⁻ x, ENNReal.ofReal (SignCube.lpNorm (fun y => ‖y‖) p
      (fun ε : Fin K → Bool => ∑ k, coin (ε k) • f k x) ^ p) ∂μ := by
  have hm := rad_aestronglyMeasurable hf (ProbabilityTheory.uniformOn Set.univ)
  rw [eLpNormRad, rad_eLpNorm_rpow hp hm, lintegral_prod _ (hm.enorm.pow_const p)]
  refine lintegral_congr fun x => ?_
  rw [rad_lintegral_uniformOn, lpNorm_rpow (fun _ => norm_nonneg _) hp,
    rad_ofReal_avg fun _ => Real.rpow_nonneg (norm_nonneg _) _]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]

/-- A bound that holds for every fixed choice of signs holds for the Rademacher sums. -/
theorem eLpNormRad_le_of_forall [SFinite μ] {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SFinite ν] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ} (hp : 0 < p)
    {f : Fin K → α → E} (hf : ∀ k, AEStronglyMeasurable (f k) μ) {g : Fin K → β → F}
    (hg : ∀ k, AEStronglyMeasurable (g k) ν) {C : ℝ≥0∞}
    (h : ∀ ε : Fin K → Bool, eLpNorm (fun x => ∑ k, coin (ε k) • f k x) (ENNReal.ofReal p) μ ≤
      C * eLpNorm (fun x => ∑ k, coin (ε k) • g k x) (ENNReal.ofReal p) ν) :
    eLpNormRad f p μ ≤ C * eLpNormRad g p ν := by
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.mul_rpow_of_nonneg _ _ hp.le, eLpNormRad_rpow hp hf,
    eLpNormRad_rpow hp hg, mul_left_comm, Finset.mul_sum (a := C ^ p)]
  refine mul_le_mul_right (Finset.sum_le_sum fun ε _ => ?_) _
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  exact ENNReal.rpow_le_rpow (h ε) hp.le

/-- The norm of a Rademacher sum depends only on the classes of the functions. -/
theorem eLpNormRad_congr_ae [SFinite μ] {p : ℝ} {f g : Fin K → α → E} (h : ∀ k, f k =ᵐ[μ] g k) :
    eLpNormRad f p μ = eLpNormRad g p μ := by
  refine eLpNorm_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.2 h)] with z hz
  exact Finset.sum_congr rfl fun k _ => by rw [hz k]

/-- The triangle inequality. -/
theorem eLpNormRad_add_le [SFinite μ] {p : ℝ} (hp : 1 ≤ p) {f g : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) (hg : ∀ k, AEStronglyMeasurable (g k) μ) :
    eLpNormRad (fun k x => f k x + g k x) p μ ≤ eLpNormRad f p μ + eLpNormRad g p μ := by
  -- the measurability hypotheses are not needed: the norm of a non-measurable function is `∞`
  have _ := And.intro hf hg
  unfold eLpNormRad
  simp only [smul_add, Finset.sum_add_distrib]
  exact eLpNorm_add_le (ENNReal.one_le_ofReal.2 hp)

/-- **Kahane's contraction principle** for pointwise multipliers `c_k (x) ∈ ℂ`, `|c_k (x)| ≤ 1`,
with the factor `2` (real signs). -/
theorem eLpNormRad_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SFinite μ] {p : ℝ}
    (hp : 1 ≤ p) {c : Fin K → α → ℂ} (hc : ∀ k x, ‖c k x‖ ≤ 1)
    (hcm : ∀ k, AEStronglyMeasurable (c k) μ) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad (fun k x => c k x • f k x) p μ ≤ 2 * eLpNormRad f p μ := by
  have hp0 : 0 < p := by linarith
  rw [← ENNReal.rpow_le_rpow_iff hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    eLpNormRad_rpow_eq_lintegral hp0 (f := fun k x => c k x • f k x)
      (fun k => (hcm k).smul (hf k)),
    eLpNormRad_rpow_eq_lintegral hp0 hf, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x => ?_
  have h2 : (2 : ℝ≥0∞) ^ p = ENNReal.ofReal ((2 : ℝ) ^ p) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg zero_le_two hp0.le, ENNReal.ofReal_ofNat]
  rw [h2, ← ENNReal.ofReal_mul (by positivity),
    ← Real.mul_rpow zero_le_two (lpNorm_nonneg (fun _ => norm_nonneg _) _ _)]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (lpNorm_nonneg (fun _ => norm_nonneg _) _ _)
    (lpNorm_sum_coin_smul_le_two_mul hp (fun k => hc k x) fun k => f k x) hp0.le)

/-- A comparison of the Rademacher averages at each point. -/
private theorem rad_le_of_lpNorm_le [SFinite μ] {L : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {p : ℝ} (hp : 0 < p) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) {g : Fin L → α → F}
    (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (h : ∀ x, SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin K → Bool => ∑ k, coin (ε k) • f k x) ≤
      SignCube.lpNorm (fun y => ‖y‖) p (fun ε : Fin L → Bool => ∑ k, coin (ε k) • g k x)) :
    eLpNormRad f p μ ≤ eLpNormRad g p μ := by
  rw [← ENNReal.rpow_le_rpow_iff hp, eLpNormRad_rpow_eq_lintegral hp hf,
    eLpNormRad_rpow_eq_lintegral hp hg]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (lpNorm_nonneg (fun _ => norm_nonneg _) _ _) (h x) hp.le)

/-- Subsets of the Rademacher sum: a Rademacher sum dominates each partial one. -/
theorem eLpNormRad_indicator_le [SFinite μ] {p : ℝ} (hp : 1 ≤ p) (s : Set (Fin K))
    {f : Fin K → α → E} (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad (s.indicator f) p μ ≤ eLpNormRad f p μ := by
  classical
  have hm : ∀ k, AEStronglyMeasurable (s.indicator f k) μ := fun k => by
    by_cases hk : k ∈ s
    · rw [Set.indicator_of_mem hk]
      exact hf k
    · rw [Set.indicator_of_notMem hk]
      exact aestronglyMeasurable_const
  refine rad_le_of_lpNorm_le (by linarith) hm hf fun x => ?_
  have hx : ∀ k, s.indicator f k x = (if k ∈ s then (1 : ℝ) else 0) • f k x := fun k => by
    by_cases hk : k ∈ s
    · rw [Set.indicator_of_mem hk, ite_eq_left hk, one_smul]
    · rw [Set.indicator_of_notMem hk, ite_eq_right hk, zero_smul, Pi.zero_apply]
  simp only [hx]
  refine lpNorm_sum_coin_smul_le hp (fun k => ?_) fun k => f k x
  split_ifs <;> simp

/-- The marginal of the uniform measure on `{±1}^L` along an injection `Fin K → Fin L` is the
uniform measure on `{±1}^K`. -/
private theorem rad_avg_comp {L : ℕ} {σ : Fin K → Fin L} (hσ : Function.Injective σ)
    (g : (Fin K → Bool) → ℝ) : avg (fun ω : Fin L → Bool => g (ω ∘ σ)) = avg g := by
  -- extend a sign vector on `Fin K` by `1`
  set e : (Fin K → Bool) → Fin L → Bool := fun ε => Function.extend σ ε fun _ => true with he
  have h1 : ∀ ε ω, mul (e ε) ω ∘ σ = mul (ω ∘ σ) ε := fun ε ω => by
    funext k
    simp only [mul, Function.comp_apply, he, hσ.extend_apply]
    cases ε k <;> cases ω (σ k) <;> rfl
  have hswap : avg (fun ε : Fin K → Bool => avg fun ω : Fin L → Bool => g (mul (e ε) ω ∘ σ)) =
      avg fun ω : Fin L → Bool => avg fun ε : Fin K → Bool => g (mul (ω ∘ σ) ε) := by
    simp only [avg, h1, Finset.sum_div]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [div_right_comm]
  have h2 : ∀ ε, avg (fun ω : Fin L → Bool => g (mul (e ε) ω ∘ σ)) =
      avg fun ω : Fin L → Bool => g (ω ∘ σ) := fun ε => avg_mul_left (e ε) fun ω => g (ω ∘ σ)
  simpa only [h2, avg_mul_left, avg_const] using hswap

/-- Reindexing: a Rademacher sum over part of the indices is dominated by the whole sum. -/
theorem eLpNormRad_comp_le [SFinite μ] {L : ℕ} {p : ℝ} (hp : 1 ≤ p) {σ : Fin K → Fin L}
    (hσ : Function.Injective σ) {f : Fin L → α → E} (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad (fun k => f (σ k)) p μ ≤ eLpNormRad f p μ := by
  classical
  refine rad_le_of_lpNorm_le (by linarith) (fun k => hf (σ k)) hf fun x => ?_
  have hsum : ∀ ω : Fin L → Bool, ∑ k, coin ((ω ∘ σ) k) • f (σ k) x =
      ∑ l, coin (ω l) • (if l ∈ Set.range σ then (1 : ℝ) else 0) • f l x := fun ω => by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image σ)) fun l _ hl => ?_,
      Finset.sum_image fun a _ b _ hab => hσ hab]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ite_eq_left (Set.mem_range_self k), one_smul, Function.comp_apply]
    · rw [ite_eq_right (by simpa using hl), zero_smul, smul_zero]
  have hK : SignCube.lpNorm (fun y => ‖y‖) p
      (fun ε : Fin K → Bool => ∑ k, coin (ε k) • f (σ k) x) =
      SignCube.lpNorm (fun y => ‖y‖) p (fun ω : Fin L → Bool =>
        ∑ l, coin (ω l) • (if l ∈ Set.range σ then (1 : ℝ) else 0) • f l x) := by
    unfold SignCube.lpNorm
    rw [← rad_avg_comp hσ]
    simp only [hsum]
  rw [hK]
  refine lpNorm_sum_coin_smul_le hp (fun l => ?_) fun l => f l x
  split_ifs <;> simp

/-! ### Minkowski's integral inequality -/

/-- Minkowski's integral inequality for a finite measure `κ`. With `F (x) = ∫ h (x, y) dy` and
`G = min (F, n)`, by Tonelli's theorem and Hölder's inequality,
`∫ G^p ≤ ∫ F G^{p − 1} = ∫ ∫ h (x, y) G (x)^{p − 1} dx dy` is at most the right side times
`(∫ G^p)^{1 − 1/p}`, and `∫ G^p` is finite; let `n → ∞`. -/
private theorem rad_lintegral_rpow_lintegral_le_of_finite {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] {κ : Measure β} {ν : Measure γ} [IsFiniteMeasure κ] [SFinite ν]
    {h : β → γ → ℝ≥0∞} (hh : Measurable (Function.uncurry h)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, (∫⁻ y, h x y ∂ν) ^ p ∂κ ≤ (∫⁻ y, (∫⁻ x, h x y ^ p ∂κ) ^ (1 / p) ∂ν) ^ p := by
  have hp0 : 0 < p := by linarith
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  set q := p / (p - 1)
  set F : β → ℝ≥0∞ := fun x => ∫⁻ y, h x y ∂ν
  have hF : Measurable F := hh.lintegral_prod_right'
  set T := ∫⁻ y, (∫⁻ x, h x y ^ p ∂κ) ^ (1 / p) ∂ν
  have hy : ∀ y, Measurable fun x => h x y := fun y => hh.comp measurable_prodMk_right
  -- the estimate for the truncations
  have key : ∀ n : ℕ, ∫⁻ x, (min (F x) n) ^ p ∂κ ≤ T ^ p := by
    intro n
    set G : β → ℝ≥0∞ := fun x => min (F x) n
    have hG : Measurable G := hF.min measurable_const
    set I := ∫⁻ x, G x ^ p ∂κ
    have hI : I ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x =>
        ENNReal.rpow_le_rpow (min_le_right (F x) (n : ℝ≥0∞)) hp0.le)
      rw [lintegral_const]
      exact ENNReal.mul_ne_top (by simp [hp0.le]) (measure_ne_top κ _)
    have hle : I ≤ T * I ^ (1 / q) := by
      calc I ≤ ∫⁻ x, ∫⁻ y, h x y * G x ^ (p - 1) ∂ν ∂κ := by
            refine lintegral_mono fun x => ?_
            have hhx : Measurable (h x) := hh.comp measurable_prodMk_left
            rw [lintegral_mul_const _ hhx]
            conv_lhs => rw [show p = 1 + (p - 1) by ring,
              ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
            exact mul_le_mul_left (min_le_left _ _) _
        _ = ∫⁻ y, ∫⁻ x, h x y * G x ^ (p - 1) ∂κ ∂ν :=
            lintegral_lintegral_swap
              (hh.mul ((hG.comp measurable_fst).pow_const (p - 1))).aemeasurable
        _ ≤ ∫⁻ y, (∫⁻ x, h x y ^ p ∂κ) ^ (1 / p) * I ^ (1 / q) ∂ν := by
            refine lintegral_mono fun y => ?_
            have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq κ hpq (f := fun x => h x y)
              (g := fun x => G x ^ (p - 1)) (hy y).aemeasurable (hG.pow_const _).aemeasurable
            have hGq : ∀ x, (G x ^ (p - 1)) ^ q = G x ^ p := fun x => by
              rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
            simpa only [Pi.mul_apply, hGq] using hH
        _ = T * I ^ (1 / q) :=
            lintegral_mul_const _ ((hh.pow_const p).lintegral_prod_left'.pow_const _)
    rcases eq_or_ne I 0 with h0 | h0
    · rw [h0]
      exact zero_le
    have hq0 : I ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) hI).ne'
    have hqt : I ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg hI
    have hroot : I ^ (1 / p) ≤ T := by
      rw [← ENNReal.mul_le_mul_iff_left hq0 hqt, ← ENNReal.rpow_add _ _ h0 hI,
        hpq.one_div_add_one_div, div_one, ENNReal.rpow_one]
      exact hle
    calc I = (I ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
      _ ≤ T ^ p := ENNReal.rpow_le_rpow hroot hp0.le
  -- monotone convergence
  have hsup : ∀ x, F x ^ p = ⨆ n : ℕ, (min (F x) n) ^ p := fun x => by
    have hF' : F x = ⨆ n : ℕ, min (F x) n := by
      rw [← inf_iSup_eq (F x) fun n : ℕ => (n : ℝ≥0∞), ENNReal.iSup_natCast, inf_top_eq]
    have e := (ENNReal.orderIsoRpow p hp0).map_iSup fun n : ℕ => min (F x) (n : ℝ≥0∞)
    simp only [ENNReal.orderIsoRpow_apply] at e
    rw [← e, ← hF']
  calc ∫⁻ x, F x ^ p ∂κ = ∫⁻ x, ⨆ n : ℕ, (min (F x) n) ^ p ∂κ := lintegral_congr hsup
    _ = ⨆ n : ℕ, ∫⁻ x, (min (F x) n) ^ p ∂κ :=
        lintegral_iSup (fun n => (hF.min measurable_const).pow_const p) fun m n hmn x =>
          ENNReal.rpow_le_rpow (min_le_min_left _ (Nat.cast_le.2 hmn)) hp0.le
    _ ≤ T ^ p := iSup_le key

/-- Minkowski's integral inequality: `∫ (∫ h (x, y) dy)^p dx ≤ (∫ (∫ h (x, y)^p dx)^{1/p} dy)^p`
for `1 ≤ p`, with s-finite measures (`κ` is a sum of finite measures). -/
private theorem rad_lintegral_rpow_lintegral_le {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] {κ : Measure β} {ν : Measure γ} [SFinite κ] [SFinite ν]
    {h : β → γ → ℝ≥0∞} (hh : Measurable (Function.uncurry h)) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (∫⁻ y, h x y ∂ν) ^ p ∂κ ≤ (∫⁻ y, (∫⁻ x, h x y ^ p ∂κ) ^ (1 / p) ∂ν) ^ p := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp only [ENNReal.rpow_one, div_one]
    rw [lintegral_lintegral_swap hh.aemeasurable]
  have hp0 : 0 < p := by linarith
  conv_lhs => rw [← sum_sfiniteSeq κ]
  rw [lintegral_sum_measure, tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← lintegral_finsetSum_measure]
  have hle : ∑ i ∈ s, sfiniteSeq κ i ≤ κ := by
    conv_rhs => rw [← sum_sfiniteSeq κ]
    exact Measure.le_iff.2 fun t ht => by
      rw [Measure.finsetSum_apply, Measure.sum_apply _ ht]
      exact _root_.sum_le_tsum s
  refine (rad_lintegral_rpow_lintegral_le_of_finite hh hp1).trans ?_
  gcongr

/-- Minkowski's integral inequality for Rademacher sums:
`‖Σ_k ε_k ∫ F_k (s, ·) dν‖ ≤ ∫ ‖Σ_k ε_k F_k (s, ·)‖ dν`. -/
theorem eLpNormRad_integral_le [SFinite μ] {S : Type*} [MeasurableSpace S] {ν : Measure S}
    [SFinite ν] {p : ℝ} (hp : 1 ≤ p) {F : Fin K → S → α → E}
    (hF : ∀ k, StronglyMeasurable (Function.uncurry (F k)))
    (hFi : ∀ k, ∀ᵐ x ∂μ, Integrable (fun s => F k s x) ν) :
    eLpNormRad (fun k x => ∫ s, F k s x ∂ν) p μ ≤ ∫⁻ s, eLpNormRad (fun k => F k s) p μ ∂ν := by
  have hp0 : 0 < p := by linarith
  set P : Measure (α × (Fin K → Bool)) := μ.prod (ProbabilityTheory.uniformOn Set.univ) with hP
  have hFs : ∀ k s, StronglyMeasurable (F k s) := fun k s =>
    (hF k).comp_measurable measurable_prodMk_left
  have hLm : ∀ k, StronglyMeasurable fun x => ∫ s, F k s x ∂ν := fun k => (hF k).integral_prod_left
  -- the norms `‖Σ_k ε_k F_k (s, x)‖`, measurable in all variables
  set h : α × (Fin K → Bool) → S → ℝ≥0∞ := fun z s => ‖∑ k, coin (z.2 k) • F k s z.1‖ₑ with hh
  have hhm : Measurable (Function.uncurry h) := by
    refine StronglyMeasurable.enorm (Finset.stronglyMeasurable_fun_sum _ fun k _ => ?_)
    exact ((StronglyMeasurable.of_discrete
      (f := fun η : Fin K → Bool => coin (η k))).comp_measurable
        (measurable_snd.comp measurable_fst)).smul
      ((hF k).comp_measurable (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have hpt : ∀ᵐ z ∂P, ‖∑ k, coin (z.2 k) • ∫ s, F k s z.1 ∂ν‖ₑ ≤ ∫⁻ s, h z s ∂ν := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.2 hFi)] with z hz
    have : ∑ k, coin (z.2 k) • ∫ s, F k s z.1 ∂ν = ∫ s, ∑ k, coin (z.2 k) • F k s z.1 ∂ν := by
      rw [integral_finsetSum _ fun k _ => (hz k).fun_smul (coin (z.2 k))]
      exact Finset.sum_congr rfl fun k _ => (integral_smul _ _).symm
    rw [this]
    exact enorm_integral_le_lintegral_enorm _
  have hr : ∀ s, eLpNormRad (fun k => F k s) p μ = (∫⁻ z, h z s ^ p ∂P) ^ (1 / p) := fun s => by
    have e := rad_eLpNorm_rpow hp0 (rad_aestronglyMeasurable (μ := μ)
      (fun k => (hFs k s).aestronglyMeasurable) (ProbabilityTheory.uniformOn Set.univ))
    rw [hh, hP, ← e, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one, eLpNormRad]
  simp only [hr]
  rw [← ENNReal.rpow_le_rpow_iff hp0, eLpNormRad, rad_eLpNorm_rpow hp0
    (rad_aestronglyMeasurable (fun k => (hLm k).aestronglyMeasurable) _)]
  exact (lintegral_mono_ae (hpt.mono fun z hz => ENNReal.rpow_le_rpow hz hp0.le)).trans
    (rad_lintegral_rpow_lintegral_le hhm hp)

end VectorValuedHarmonicAnalysis
