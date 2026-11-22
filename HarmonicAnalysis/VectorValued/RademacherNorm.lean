module

public import BanachProbability.SignCube.Bridge
public import BanachProbability.RandomSums.Contraction
import HarmonicAnalysis.FourierMultiplier.Density
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Norms of Rademacher sums of functions

For functions `f_1, …, f_K : α → E` and independent fair signs `ε_k`,
`eLpNormRad f p μ = ‖Σ_k ε_k f_k‖_{L^p (α × {±1}^K; E)}`, the norm of the Rademacher sum in `L^p` of
the product of `μ` with the uniform probability on the signs. Facts:

* the `p`-th power is the average over the signs (`eLpNormRad_rpow`,
  `eLpNormRad_rpow_eq_lintegral`), and bounds that hold for every fixed choice of signs hold for the
  Rademacher sums (`eLpNormRad_le_of_forall`);
* the triangle inequality (`eLpNormRad_add_le`), scalar factors (`eLpNormRad_fun_const_smul`), sums
  with one term (`eLpNormRad_one`), measure-preserving maps (`eLpNormRad_comp_measurePreserving`);
* Kahane's contraction principle for pointwise multipliers (`eLpNormRad_smul_le`), the invariance
  under pointwise signs (`eLpNormRad_sign_smul`), partial sums (`eLpNormRad_indicator_le`,
  `eLpNormRad_comp_le`);
* Minkowski's integral inequality (`eLpNormRad_integral_le`).

Sources: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016) and *II*
(2017): the contraction principle is Proposition 3.2.10 of volume I, pp. 181–182, and Theorem 6.1.13
of volume II, p. 9; Minkowski's integral inequality is Proposition 1.2.22 of volume I, p. 24, with
the exponents `1` and `p`.

The signs are real throughout the package, also in complex spaces, where the book uses complex
Rademacher variables. This costs a factor in the contraction principle for complex scalars: the best
constant is `1` for complex Rademacher variables and `π / 2` for real signs; here the
constant `2 ≥ π / 2` is used.
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
theorem eLpNorm_ofReal_rpow_eq_lintegral {S F : Type*} [NormedAddCommGroup F]
    {mS : MeasurableSpace S} {ν : Measure S} {p : ℝ} (hp : 0 < p) {f : S → F}
    (hf : AEStronglyMeasurable f ν) :
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
theorem eLpNormRad_rpow {p : ℝ} (hp : 0 < p) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad f p μ ^ p = ((2 : ℝ≥0∞) ^ K)⁻¹ * ∑ ε : Fin K → Bool,
      eLpNorm (fun x => ∑ k, coin (ε k) • f k x) (ENNReal.ofReal p) μ ^ p := by
  have hm := rad_aestronglyMeasurable hf (ProbabilityTheory.uniformOn Set.univ)
  rw [eLpNormRad, eLpNorm_ofReal_rpow_eq_lintegral hp hm, lintegral_prod _ (hm.enorm.pow_const p)]
  simp only [rad_lintegral_uniformOn]
  rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum' _ fun ε _ =>
    (rad_aestronglyMeasurable_sum hf ε).enorm.pow_const p]
  congr 1
  exact Finset.sum_congr rfl fun ε _ =>
    (eLpNorm_ofReal_rpow_eq_lintegral hp (rad_aestronglyMeasurable_sum hf ε)).symm

/-- The `p`-th power as an integral of averages over the sign cube. -/
theorem eLpNormRad_rpow_eq_lintegral {p : ℝ} (hp : 0 < p) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad f p μ ^ p = ∫⁻ x, ENNReal.ofReal (SignCube.lpNorm (fun y => ‖y‖) p
      (fun ε : Fin K → Bool => ∑ k, coin (ε k) • f k x) ^ p) ∂μ := by
  have hm := rad_aestronglyMeasurable hf (ProbabilityTheory.uniformOn Set.univ)
  rw [eLpNormRad, eLpNorm_ofReal_rpow_eq_lintegral hp hm, lintegral_prod _ (hm.enorm.pow_const p)]
  refine lintegral_congr fun x => ?_
  rw [rad_lintegral_uniformOn, lpNorm_rpow (fun _ => norm_nonneg _) hp,
    rad_ofReal_avg fun _ => Real.rpow_nonneg (norm_nonneg _) _]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]

/-- A bound that holds for every fixed choice of signs holds for the Rademacher sums. -/
theorem eLpNormRad_le_of_forall {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ} (hp : 0 < p)
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
theorem eLpNormRad_congr_ae {p : ℝ} {f g : Fin K → α → E} (h : ∀ k, f k =ᵐ[μ] g k) :
    eLpNormRad f p μ = eLpNormRad g p μ := by
  refine eLpNorm_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.2 h)] with z hz
  exact Finset.sum_congr rfl fun k _ => by rw [hz k]

/-- The triangle inequality. (The measurability hypotheses are not used in the proof.) -/
theorem eLpNormRad_add_le {p : ℝ} (hp : 1 ≤ p) {f g : Fin K → α → E}
    (_hf : ∀ k, AEStronglyMeasurable (f k) μ) (_hg : ∀ k, AEStronglyMeasurable (g k) μ) :
    eLpNormRad (fun k x => f k x + g k x) p μ ≤ eLpNormRad f p μ + eLpNormRad g p μ := by
  unfold eLpNormRad
  simp only [smul_add, Finset.sum_add_distrib]
  exact eLpNorm_add_le (ENNReal.one_le_ofReal.2 hp)

/-- Scalar factors. -/
theorem eLpNormRad_fun_const_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E]
    [NormSMulClass 𝕜 E] [SMulCommClass ℝ 𝕜 E] (c : 𝕜) (f : Fin K → α → E) (p : ℝ) :
    eLpNormRad (fun k x => c • f k x) p μ = ‖c‖ₑ * eLpNormRad f p μ := by
  rw [eLpNormRad, eLpNormRad, ← eLpNorm_const_smul]
  congr 1
  funext z
  simp only [Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

/-- The Rademacher sum with one term. -/
theorem eLpNormRad_one {p : ℝ} (hp : 0 < p) {f : α → E} (hf : AEStronglyMeasurable f μ) :
    eLpNormRad (fun _ : Fin 1 => f) p μ = eLpNorm f (ENNReal.ofReal p) μ := by
  refine ENNReal.rpow_left_injective hp.ne' ?_
  have h : ∀ ε : Fin 1 → Bool, eLpNorm (fun x => ∑ k, coin (ε k) • f x) (ENNReal.ofReal p) μ =
      eLpNorm f (ENNReal.ofReal p) μ := fun ε => by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rcases coin_eq_one_or_eq_neg_one (ε default) with h | h
    · simp only [h, one_smul]
    · simp only [h, neg_smul, one_smul]
      exact eLpNorm_neg f _ _
  simp only
  rw [eLpNormRad_rpow hp fun _ => hf]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, nsmul_eq_mul, ← mul_assoc, Fintype.card_fin, pow_one, Nat.cast_ofNat]
  rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- Measure-preserving maps, such as the translations and the reflection of the line, preserve the
norms of Rademacher sums. -/
theorem eLpNormRad_comp_measurePreserving {β : Type*} [MeasurableSpace β] {ν : Measure β} {p : ℝ}
    (hp : 0 < p) {f : Fin K → α → E} (hf : ∀ k, AEStronglyMeasurable (f k) μ) {φ : β → α}
    (hφ : MeasurePreserving φ ν μ) :
    eLpNormRad (fun k x => f k (φ x)) p ν = eLpNormRad f p μ := by
  refine ENNReal.rpow_left_injective hp.ne' ?_
  simp only
  rw [eLpNormRad_rpow hp hf, eLpNormRad_rpow hp (f := fun k x => f k (φ x)) fun k =>
    (hf k).comp_measurePreserving hφ]
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1
  exact eLpNorm_comp_measurePreserving (rad_aestronglyMeasurable_sum hf ε) hφ

/-- **Kahane's contraction principle** for pointwise multipliers `c_k (x) ∈ ℂ`, `|c_k (x)| ≤ 1`, and
real signs, with the factor `2` (HNVW I, Proposition 3.2.10, (3.15), with the best factor `π / 2`;
HNVW II, Theorem 6.1.13 (ii)). -/
theorem eLpNormRad_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℝ}
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

/-- Multiplying the terms by signs that depend on the point does not change the norm of a Rademacher
sum: for each `x` the families `(ε_k s_k (x))` and `(ε_k)` have the same law. -/
theorem eLpNormRad_sign_smul {p : ℝ} (hp : 0 < p) {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) {s : Fin K → α → ℝ}
    (hs : ∀ k x, s k x = 1 ∨ s k x = -1) (hsm : ∀ k, Measurable (s k)) :
    eLpNormRad (fun k x => s k x • f k x) p μ = eLpNormRad f p μ := by
  refine ENNReal.rpow_left_injective hp.ne' ?_
  simp only
  rw [eLpNormRad_rpow_eq_lintegral hp hf, eLpNormRad_rpow_eq_lintegral hp
    (f := fun k x => s k x • f k x) fun k => (hsm k).aestronglyMeasurable.smul (hf k)]
  refine lintegral_congr fun x => ?_
  -- the signs `s_k (x)`, as a sign vector
  set σ : Fin K → Bool := fun k => decide (s k x = 1) with hσ
  have hcoin : ∀ k, coin (σ k) = s k x := fun k => by
    rcases hs k x with h | h
    · simp [hσ, h]
    · simp [hσ, h]
      norm_num
  rw [SignCube.lpNorm, SignCube.lpNorm, ← avg_mul_left σ fun ε => ‖∑ k, coin (ε k) • f k x‖ ^ p]
  simp only [coin_mul_apply, hcoin, smul_smul, mul_comm]

/-- A comparison of the Rademacher averages at each point. -/
private theorem rad_le_of_lpNorm_le {L : ℕ} {F : Type*} [NormedAddCommGroup F]
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
theorem eLpNormRad_indicator_le {p : ℝ} (hp : 1 ≤ p) (s : Set (Fin K))
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
theorem eLpNormRad_comp_le {L : ℕ} {p : ℝ} (hp : 1 ≤ p) {σ : Fin K → Fin L}
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

/-- Minkowski's integral inequality `‖∫ h (·, y) dy‖_p ≤ ∫ ‖h (·, y)‖_p dy` (HNVW I, Proposition
1.2.22, for the exponents `1` and `p`), for measurable `h ≥ 0` and s-finite measures.

Departure from the source: the book takes the norm inside a Bochner integral in `L^p`, for step
functions, and uses their density. Here the weighted Jensen inequality
`(∫ a (y) g (x, y) dy)^p ≤ (∫ a)^{p − 1} ∫ a (y) g (x, y)^p dy`, integrated in `x`, is applied to
`a (y) = ‖h (·, y)‖_p` and `g = h / a`, for which `∫ g (x, y)^p dx ≤ 1`. -/
private theorem rad_lintegral_rpow_lintegral_le {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] {κ : Measure β} {ν : Measure γ} [SFinite κ] [SFinite ν]
    {h : β → γ → ℝ≥0∞} (hh : Measurable (Function.uncurry h)) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (∫⁻ y, h x y ∂ν) ^ p ∂κ ≤ (∫⁻ y, (∫⁻ x, h x y ^ p ∂κ) ^ (1 / p) ∂ν) ^ p := by
  have hp0 : 0 < p := by linarith
  set a : γ → ℝ≥0∞ := fun y => (∫⁻ x, h x y ^ p ∂κ) ^ (1 / p)
  have ha : Measurable a := (hh.pow_const p).lintegral_prod_left'.pow_const _
  have hap : ∀ y, a y ^ p = ∫⁻ x, h x y ^ p ∂κ := fun y => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hhy : ∀ y, Measurable fun x => h x y := fun y => hh.comp measurable_prodMk_right
  rcases eq_or_ne (∫⁻ y, a y ∂ν) ⊤ with hT | hT
  · rw [hT, ENNReal.top_rpow_of_pos hp0]
    exact le_top
  have hk : Measurable (Function.uncurry fun x y => h x y / a y) := hh.div (ha.comp measurable_snd)
  -- `h = a (h / a)`: `a < ∞` almost everywhere, and `h (·, y) = 0` almost everywhere if `a (y) = 0`
  have hyx : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ, h x y = a y * (h x y / a y) := by
    filter_upwards [ae_lt_top ha hT] with y hy
    rcases eq_or_ne (a y) 0 with h0 | h0
    · have h1 : ∫⁻ x, h x y ^ p ∂κ = 0 := by rw [← hap, h0, ENNReal.zero_rpow_of_pos hp0]
      filter_upwards [(lintegral_eq_zero_iff ((hhy y).pow_const p)).1 h1] with x hx
      rw [(ENNReal.rpow_eq_zero_iff_of_pos hp0).1 hx, ENNReal.zero_div, mul_zero]
    · exact ae_of_all _ fun x => (ENNReal.mul_div_cancel h0 hy.ne).symm
  have hxy := (Measure.ae_ae_comm (p := fun y x => h x y = a y * (h x y / a y))
    (measurableSet_eq_fun (hh.comp measurable_swap)
      ((ha.comp measurable_fst).mul (hk.comp measurable_swap)))).1 hyx
  calc ∫⁻ x, (∫⁻ y, h x y ∂ν) ^ p ∂κ
      = ∫⁻ x, (∫⁻ y, a y * (h x y / a y) ∂ν) ^ p ∂κ :=
        lintegral_congr_ae (hxy.mono fun x hx => by simp only; rw [lintegral_congr_ae hx])
    _ ≤ (∫⁻ y, a y ∂ν) ^ (p - 1) * ∫⁻ y, a y * ∫⁻ x, (h x y / a y) ^ p ∂κ ∂ν :=
        HarmonicAnalysis.lintegral_rpow_lintegral_mul_le ha hk hp
    _ ≤ (∫⁻ y, a y ∂ν) ^ (p - 1) * ∫⁻ y, a y ∂ν := by
        gcongr with y
        refine mul_le_of_le_one_right zero_le ?_
        simp_rw [ENNReal.div_rpow_of_nonneg _ _ hp0.le, div_eq_mul_inv]
        rw [lintegral_mul_const _ ((hhy y).pow_const p), ← hap]
        exact ENNReal.mul_inv_le_one _
    _ = (∫⁻ y, a y ∂ν) ^ p := by
        conv_lhs => rw [← ENNReal.rpow_one (∫⁻ y, a y ∂ν), ← ENNReal.rpow_mul, one_mul]
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, sub_add_cancel]

/-- Minkowski's integral inequality for Rademacher sums:
`‖Σ_k ε_k ∫ F_k (s, ·) dν‖ ≤ ∫ ‖Σ_k ε_k F_k (s, ·)‖ dν` (HNVW I, Proposition 1.2.22, for the
exponents `1` and `p`). -/
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
    have e := eLpNorm_ofReal_rpow_eq_lintegral hp0 (rad_aestronglyMeasurable (μ := μ)
      (fun k => (hFs k s).aestronglyMeasurable) (ProbabilityTheory.uniformOn Set.univ))
    rw [hh, hP, ← e, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one, eLpNormRad]
  simp only [hr]
  rw [← ENNReal.rpow_le_rpow_iff hp0, eLpNormRad, eLpNorm_ofReal_rpow_eq_lintegral hp0
    (rad_aestronglyMeasurable (fun k => (hLm k).aestronglyMeasurable) _)]
  exact (lintegral_mono_ae (hpt.mono fun z hz => ENNReal.rpow_le_rpow hz hp0.le)).trans
    (rad_lintegral_rpow_lintegral_le hhm hp)

end VectorValuedHarmonicAnalysis
