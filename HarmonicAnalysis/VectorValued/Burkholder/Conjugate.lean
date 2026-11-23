/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Burkholder.RandomWalk
public import HarmonicAnalysis.VectorValued.CircPoly
public import Mathlib.Probability.ProductMeasure
import BanachProbability.UMD.Hilbert
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-!
# Conjugate trigonometric polynomials on UMD spaces

D. L. Burkholder, *A geometric condition that implies the existence of certain singular integrals of
Banach-space-valued functions* (1983), pp. 278–279 and 281–282: the end of the proof of Lemma 2. For
`u`, `v` of (18), (19) with coefficients in a Banach space with the `UMD_p` constant `β`,
`1 < p < ∞`,

`‖v (r e^{iθ})‖_p ≤ β² ‖u (r e^{iθ})‖_p` for `r ≥ 0` (`eLpNorm_conjHarmPoly_le`).

The walk `Z_n` runs on an infinite sequence of fair signs with the law `signLaw`, the product of the
uniform laws of the two signs; `eLpNorm_signLaw` says that the norm in `L^p` of a function of the
first `N` signs is an average over the cube. The steps of the paper are the following.

* `ae_exists_one_le_norm_walk`: by (20), `τ < ∞` almost everywhere. `ae_tendsto_walk_exitTime` is
  (21) and `ae_norm_exitPlace_mem` is (23); (22) is `norm_walk_exitTime_le`.
* `exists_eLpNorm_conjHarmPoly_exitPlace_le`: the inequality for `Z_{τ ∧ n}`
  (`exists_lpNorm_conjHarmPoly_walk_le`) gives the one for `Z_τ` when `n → ∞`, since `u`, `v` are
  continuous and bounded on the disc `|z| ≤ 2`.
* `exists_eLpNorm_conjHarmPoly_rotate_le`, `exists_eLpNorm_conjHarmPoly_norm_exitPlace_le`: the same
  for `u^α (z) = u (e^{iα} z)`, then the integration in `α`.
* `eLpNorm_conjHarmPoly_fourier_le`: `δ → 0` gives the case `r = 1`.

`eLpNorm_conj_circPoly_le` is the result for trigonometric polynomials with coefficients in a
complex space on `ℝ / ℤ`, the conjugate of which is `Σ_n (−i sgn n) c_n e_n`.

## Departures from the source

* The paper integrates the `p`-th powers in `α`, and its constant `c_p (B)` changes from line to
  line. Here Minkowski's inequality in `L^p (dα)` (`eLpNorm_prod_le_of_forall`) keeps the constant
  `β²`.
* The paper takes a finite constant. For `β = ∞` the inequality says that `v` vanishes on the circle
  when `u` does, which follows from the case of `X = ℝ`, by the functionals `φ ∈ X*`
  (`conjHarmPoly_fourier_eq_zero`).
* The paper writes the signs as Rademacher functions on `[0, 1]`.
-/

@[expose] public section

open MeasureTheory BanachProbability AddCircle Filter Topology
open scoped ENNReal Real

namespace HarmonicAnalysis

/-- `0 < 2π`, for the circle `ℝ / 2πℤ`. -/
theorem fact_zero_lt_two_pi : Fact (0 < 2 * π) :=
  ⟨Real.two_pi_pos⟩

attribute [local instance] fact_zero_lt_two_pi

/-- The law of a sequence of independent fair signs. -/
noncomputable def signLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ => ProbabilityTheory.uniformOn (Set.univ : Set Bool)

open scoped Classical in
/-- The exit place `Z_τ`, `τ = inf {n : |Z_n| ≥ 1}` (`0` on the null set `τ = ∞`). -/
noncomputable def exitPlace (δ : ℝ) (ω : ℕ → Bool) : ℂ :=
  if h : ∃ n, 1 ≤ ‖walk δ ω n‖ then walk δ ω (Nat.find h) else 0

/-! ### The law of a sequence of fair signs -/

/-- The law of a sequence of signs is a probability measure. -/
private theorem isProbabilityMeasure_signLaw : IsProbabilityMeasure signLaw := by
  unfold signLaw
  infer_instance

attribute [local instance] isProbabilityMeasure_signLaw

/-- The law of the first `N` signs is the uniform law of the cube. -/
private theorem measurePreserving_restrict_signLaw (N : ℕ) :
    MeasurePreserving (fun (ω : ℕ → Bool) (i : Fin N) => ω i) signLaw
      (ProbabilityTheory.uniformOn Set.univ) := by
  have hm : Measurable fun (ω : ℕ → Bool) (i : Fin N) => ω i :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  refine ⟨hm, Measure.ext_of_singleton fun ε => ?_⟩
  have hpre : (fun (ω : ℕ → Bool) (i : Fin N) => ω i) ⁻¹' {ε} =
      Set.pi (Finset.range N) fun j => {extendSigns ε j} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_pi, Finset.mem_coe,
      Finset.mem_range]
    refine ⟨fun h j hj => ?_, fun h i => ?_⟩
    · simp only [extendSigns, hj, dite_true]
      exact h ⟨j, hj⟩
    · simpa [extendSigns] using h i i.2
  have hbool : ∀ b : Bool, (ProbabilityTheory.uniformOn (Set.univ : Set Bool)) {b} = 2⁻¹ :=
    fun b => by rw [ProbabilityTheory.uniformOn_univ, Measure.count_singleton]; simp
  rw [Measure.map_apply hm (measurableSet_singleton ε), hpre, signLaw,
    Measure.infinitePi_pi _ fun _ _ => MeasurableSet.of_discrete,
    Finset.prod_congr rfl fun j _ => hbool _, ProbabilityTheory.uniformOn_univ,
    Measure.count_singleton]
  simp [ENNReal.inv_pow]

/-- A function of the first `N` signs is measurable. -/
private theorem measurable_of_dependsOn {E : Type*} [MeasurableSpace E] {N : ℕ}
    {F : (ℕ → Bool) → E} (hF : ∀ ω, F (extendSigns fun i : Fin N => ω i) = F ω) :
    Measurable F := by
  have h : F = (fun ε : Fin N → Bool => F (extendSigns ε)) ∘ fun ω i => ω i :=
    funext fun ω => (hF ω).symm
  rw [h]
  exact Measurable.of_discrete.comp (measurePreserving_restrict_signLaw N).measurable

/-- A function of the first `N` signs is strongly measurable. -/
private theorem stronglyMeasurable_of_dependsOn {E : Type*} [TopologicalSpace E] {N : ℕ}
    {F : (ℕ → Bool) → E} (hF : ∀ ω, F (extendSigns fun i : Fin N => ω i) = F ω) :
    StronglyMeasurable F := by
  have h : F = (fun ε : Fin N → Bool => F (extendSigns ε)) ∘ fun ω i => ω i :=
    funext fun ω => (hF ω).symm
  rw [h]
  exact StronglyMeasurable.of_discrete.comp_measurable
    (measurePreserving_restrict_signLaw N).measurable

/-- The `L^p` norm of a function of the first `N` signs is an average over the cube. -/
private theorem eLpNorm_signLaw {E : Type*} [NormedAddCommGroup E] {N : ℕ}
    {F : (ℕ → Bool) → E} (hF : ∀ ω, F (extendSigns fun i : Fin N => ω i) = F ω) {p : ℝ}
    (hp : 0 < p) :
    eLpNorm F (ENNReal.ofReal p) signLaw = ENNReal.ofReal
      (SignCube.lpNorm (fun x => ‖x‖) p fun ε : Fin N → Bool => F (extendSigns ε)) := by
  rw [← SignCube.eLpNorm_uniformOn _ hp, ← eLpNorm_comp_measurePreserving
    AEStronglyMeasurable.of_discrete (measurePreserving_restrict_signLaw N)]
  exact congrArg (fun G => eLpNorm G (ENNReal.ofReal p) signLaw) (funext fun ω => (hF ω).symm)

/-- `Z_m`, `m ≤ n`, depends only on the first `2n` signs. -/
private theorem walk_extendSigns (δ : ℝ) (ω : ℕ → Bool) {m n : ℕ} (hmn : m ≤ n) :
    walk δ (extendSigns fun i : Fin (2 * n) => ω i) m = walk δ ω m := by
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have h1 : 2 * k < 2 * n := by omega
  have h2 : 2 * k + 1 < 2 * n := by omega
  simp [extendSigns, h1, h2]

/-- `τ ∧ n` depends only on the first `2n` signs. -/
private theorem exitTime_extendSigns (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    exitTime δ (extendSigns fun i : Fin (2 * n) => ω i) n = exitTime δ ω n := by
  classical
  have hle : ∀ ω' : ℕ → Bool, exitTime δ ω' n ≤ n := fun ω' => Nat.find_min' _ (Or.inl rfl)
  refine le_antisymm ?_ ?_
  · refine Nat.find_min' _ ?_
    have h := Nat.find_spec (p := fun m => m = n ∨ 1 ≤ ‖walk δ ω m‖) ⟨n, Or.inl rfl⟩
    rw [walk_extendSigns δ ω (hle ω)]
    exact h
  · refine Nat.find_min' _ ?_
    have h := Nat.find_spec
      (p := fun m => m = n ∨ 1 ≤ ‖walk δ (extendSigns fun i : Fin (2 * n) => ω i) m‖)
      ⟨n, Or.inl rfl⟩
    rw [← walk_extendSigns δ ω (hle (extendSigns fun i : Fin (2 * n) => ω i))]
    exact h

/-- `Z_{τ ∧ n}` depends only on the first `2n` signs. -/
private theorem walk_exitTime_extendSigns (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    walk δ (extendSigns fun i : Fin (2 * n) => ω i)
      (exitTime δ (extendSigns fun i : Fin (2 * n) => ω i) n) =
        walk δ ω (exitTime δ ω n) := by
  rw [exitTime_extendSigns, walk_extendSigns]
  exact Nat.find_min' _ (Or.inl rfl)

/-! ### The exit time is finite almost everywhere -/

/-- If `τ = ∞`, then `τ ∧ n = n`. -/
private theorem exitTime_eq_of_forall_lt {δ : ℝ} {ω : ℕ → Bool}
    (h : ¬ ∃ n, 1 ≤ ‖walk δ ω n‖) (n : ℕ) : exitTime δ ω n = n := by
  classical
  have hs := Nat.find_spec (p := fun m => m = n ∨ 1 ≤ ‖walk δ ω m‖) ⟨n, Or.inl rfl⟩
  exact hs.resolve_right fun h' => h ⟨_, h'⟩

/-- (20) for `p = 2` and the law of an infinite sequence of signs: `δ ‖(τ ∧ n)^{1/2}‖_2 ≤ 2`. -/
private theorem eLpNorm_sqrt_exitTime_le {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (n : ℕ) :
    eLpNorm (fun ω => √(exitTime δ ω n)) (ENNReal.ofReal 2) signLaw ≤ ENNReal.ofReal (2 / δ) := by
  rw [eLpNorm_signLaw (N := 2 * n) (fun ω => by rw [exitTime_extendSigns]) two_pos]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := lpNorm_sqrt_exitTime_le (p := 2) one_lt_two hδ0 hδ n
  rw [le_div_iff₀ hδ0, mul_comm]
  norm_num at h ⊢
  exact h

/-- `τ` is finite almost everywhere, by (20). -/
theorem ae_exists_one_le_norm_walk {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∀ᵐ ω ∂signLaw, ∃ n, 1 ≤ ‖walk δ ω n‖ := by
  have hA : MeasurableSet {ω | ¬ ∃ n, 1 ≤ ‖walk δ ω n‖} := by
    rw [show {ω | ¬ ∃ n, 1 ≤ ‖walk δ ω n‖} = (⋃ n, {ω | 1 ≤ ‖walk δ ω n‖})ᶜ by ext; simp]
    exact (MeasurableSet.iUnion fun n => measurableSet_le measurable_const (measurable_of_dependsOn
      (N := 2 * n) fun ω => walk_extendSigns δ ω le_rfl).norm).compl
  rw [ae_iff]
  set A : Set (ℕ → Bool) := {ω | ¬ ∃ n, 1 ≤ ‖walk δ ω n‖}
  -- `n^{1/2} P (τ = ∞)^{1/2} ≤ ‖(τ ∧ n)^{1/2}‖_2 ≤ 2 / δ`
  have hle : ∀ k : ℕ, k * signLaw A ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (2 / δ) := by
    intro k
    have h1 : eLpNorm (A.indicator fun _ => (k : ℝ)) (ENNReal.ofReal 2) signLaw ≤
        ENNReal.ofReal (2 / δ) := by
      refine (eLpNorm_mono_ae (aestronglyMeasurable_const.indicator hA)
        (ae_of_all _ fun ω => ?_)).trans (eLpNorm_sqrt_exitTime_le hδ0 hδ (k ^ 2))
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, exitTime_eq_of_forall_lt hω, Nat.cast_pow,
          Real.sqrt_sq (Nat.cast_nonneg k)]
      · rw [Set.indicator_of_notMem hω, norm_zero]
        exact norm_nonneg _
    rwa [eLpNorm_indicator_const hA.nullMeasurableSet (by simp) (by simp),
      ENNReal.toReal_ofReal zero_le_two, Real.enorm_natCast] at h1
  by_contra h0
  have h0' : signLaw A ^ (1 / (2 : ℝ)) ≠ 0 := by simp [h0]
  have htop : signLaw A ^ (1 / (2 : ℝ)) ≠ ∞ := by simp [measure_ne_top]
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (r := ENNReal.ofReal (2 / δ) / signLaw A ^ (1 / (2 : ℝ)))
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top h0')
  exact absurd (hle k) (not_le.2 ((ENNReal.div_lt_iff (Or.inl h0') (Or.inl htop)).1 hk))

/-! ### The exit place -/

/-- `τ ∧ n = τ` for `n ≥ τ`. -/
private theorem walk_exitTime_eq_exitPlace {δ : ℝ} {ω : ℕ → Bool} (h : ∃ n, 1 ≤ ‖walk δ ω n‖) :
    ∃ m, ∀ n, m ≤ n → walk δ ω (exitTime δ ω n) = exitPlace δ ω := by
  classical
  refine ⟨Nat.find h, fun n hn => ?_⟩
  rw [exitPlace, dite_eq_left h]
  congr 1
  refine le_antisymm (Nat.find_min' _ (Or.inr (Nat.find_spec h))) ?_
  have hs := Nat.find_spec (p := fun m => m = n ∨ 1 ≤ ‖walk δ ω m‖) ⟨n, Or.inl rfl⟩
  rcases hs with hs | hs
  · exact hn.trans hs.ge
  · exact Nat.find_min' h hs

/-- (21): `lim Z_{τ ∧ n} = Z_τ` almost everywhere. -/
theorem ae_tendsto_walk_exitTime {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∀ᵐ ω ∂signLaw, Tendsto (fun n => walk δ ω (exitTime δ ω n)) atTop (𝓝 (exitPlace δ ω)) := by
  filter_upwards [ae_exists_one_le_norm_walk hδ0 hδ] with ω hω
  obtain ⟨m, hm⟩ := walk_exitTime_eq_exitPlace hω
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  exact (hm n hn).symm

/-- (23): `1 ≤ |Z_τ| ≤ 1 + 2δ` almost everywhere. -/
theorem ae_norm_exitPlace_mem {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    ∀ᵐ ω ∂signLaw, ‖exitPlace δ ω‖ ∈ Set.Icc 1 (1 + 2 * δ) := by
  classical
  filter_upwards [ae_exists_one_le_norm_walk hδ0 hδ] with ω hω
  obtain ⟨m, hm⟩ := walk_exitTime_eq_exitPlace hω
  refine ⟨?_, (hm m le_rfl) ▸ norm_walk_exitTime_le hδ0 hδ ω m⟩
  rw [exitPlace, dite_eq_left hω]
  exact Nat.find_spec hω

/-- `Z_τ` is measurable (outside a null set). -/
private theorem aemeasurable_exitPlace {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    AEMeasurable (exitPlace δ) signLaw :=
  aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (measurable_of_dependsOn (N := 2 * n)
    fun ω => walk_exitTime_extendSigns δ ω n).aemeasurable) (ae_tendsto_walk_exitTime hδ0 hδ)

/-! ### Bounded convergence -/

/-- The bounded convergence theorem for `L^p` norms. -/
private theorem tendsto_eLpNorm_of_bounded {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] {μ : Measure Ω} [IsFiniteMeasure μ] {p : ℝ} (hp : 0 < p)
    {f : ℕ → Ω → E} {g : Ω → E} {C : ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hC : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ C) (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => eLpNorm (f n) (ENNReal.ofReal p) μ) atTop
      (𝓝 (eLpNorm g (ENNReal.ofReal p) μ)) := by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have heq : ∀ u : Ω → E, AEStronglyMeasurable u μ → eLpNorm u (ENNReal.ofReal p) μ =
      (∫⁻ ω, ‖u ω‖ₑ ^ p ∂μ) ^ (1 / p) := fun u hu => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hu,
      ENNReal.toReal_ofReal hp.le]
  rw [heq g hg]
  simp only [heq _ (hf _)]
  refine Tendsto.ennrpow_const _ ?_
  refine tendsto_lintegral_of_dominated_convergence' (fun _ => ENNReal.ofReal C ^ p)
    (fun n => (hf n).enorm.pow_const p) (fun n => ?_) ?_ ?_
  · filter_upwards [hC n] with ω hω
    rw [← ofReal_norm]
    gcongr
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      (measure_ne_top _ _)
  · filter_upwards [hlim] with ω hω
    exact (hω.enorm).ennrpow_const p

/-! ### The inequality for `Z_τ` -/

/-- The walk stays in the disc `|z| ≤ 2` up to the exit time, by (22). -/
private theorem norm_walk_exitTime_le_two {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (ω : ℕ → Bool)
    (n : ℕ) : ‖walk δ ω (exitTime δ ω n)‖ ≤ 2 :=
  (norm_walk_exitTime_le hδ0 hδ ω n).trans (by linarith)

/-- A continuous function is bounded on the closed disc `|z| ≤ 2`. -/
private theorem exists_norm_le_of_norm_le_two {E : Type*} [NormedAddCommGroup E] {F : ℂ → E}
    (hF : Continuous F) : ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ 2 → ‖F z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun z hz => hC z (by simpa using hz)⟩

/-- `lim_n ‖F (Z_{τ ∧ n})‖_p = ‖F (Z_τ)‖_p` for continuous `F`, by (21) and (22). -/
private theorem tendsto_lpNorm_walk {E : Type*} [NormedAddCommGroup E] {F : ℂ → E}
    (hF : Continuous F) {p : ℝ} (hp : 0 < p) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p
        fun ε : Fin (2 * n) → Bool => F (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n))))
      atTop (𝓝 (eLpNorm (fun ω => F (exitPlace δ ω)) (ENNReal.ofReal p) signLaw)) := by
  have hdep : ∀ (n : ℕ) (ω : ℕ → Bool),
      F (walk δ (extendSigns fun i : Fin (2 * n) => ω i)
        (exitTime δ (extendSigns fun i : Fin (2 * n) => ω i) n)) =
          F (walk δ ω (exitTime δ ω n)) := fun n ω => by rw [walk_exitTime_extendSigns]
  obtain ⟨C, hC⟩ := exists_norm_le_of_norm_le_two hF
  refine Tendsto.congr (fun n => eLpNorm_signLaw
    (F := fun ω => F (walk δ ω (exitTime δ ω n))) (hdep n) hp) ?_
  refine tendsto_eLpNorm_of_bounded hp (C := C)
    (fun n => (stronglyMeasurable_of_dependsOn
      (F := fun ω => F (walk δ ω (exitTime δ ω n))) (hdep n)).aestronglyMeasurable)
    (fun n => ae_of_all _ fun ω => hC _ (norm_walk_exitTime_le_two hδ0 hδ ω n)) ?_
  filter_upwards [ae_tendsto_walk_exitTime hδ0 hδ] with ω hω
  exact (hF.tendsto _).comp hω

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The functions (19) are continuous. -/
private theorem continuous_conjHarmPoly (N : ℕ) (a b : ℕ → X) :
    Continuous (conjHarmPoly N a b) := by
  rw [funext (conjHarmPoly_eq N a b)]
  exact continuous_harmPoly N (-b) a

/-- `‖v (Z_τ)‖_p ≤ β² ‖u (Z_τ)‖_p + (β² + 1) C_p γ δ` (p. 282). -/
private theorem exists_eLpNorm_conjHarmPoly_exitPlace_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (β : ℝ≥0∞),
      β ≠ ∞ → IsUMDBound X p β → ∀ (N : ℕ) (a b : ℕ → X) (δ : ℝ), 0 < δ → δ < 1 / 2 →
        eLpNorm (fun ω => conjHarmPoly N a b (exitPlace δ ω)) (ENNReal.ofReal p) signLaw ≤
          β ^ 2 * eLpNorm (fun ω => harmPoly N a b (exitPlace δ ω)) (ENNReal.ofReal p) signLaw +
            (β ^ 2 + 1) * ENNReal.ofReal (C * harmConst N a b * δ) := by
  obtain ⟨C, hC0, hC⟩ := exists_lpNorm_conjHarmPoly_walk_le hp
  refine ⟨C, hC0, fun X _ _ _ β hβt hβ N a b δ hδ0 hδ => ?_⟩
  have hp0 : 0 < p := zero_lt_one.trans hp
  refine le_of_tendsto_of_tendsto'
    (tendsto_lpNorm_walk (continuous_conjHarmPoly N a b) hp0 hδ0 hδ)
    ((ENNReal.Tendsto.const_mul (tendsto_lpNorm_walk (continuous_harmPoly N a b) hp0 hδ0 hδ)
      (Or.inr (ENNReal.pow_ne_top hβt))).add_const _) (hC X β hβ N a b δ hδ0 hδ)

/-- The same inequality for the rotated functions `u^α`, `v^α`, with `2γ` in place of `γ`. -/
private theorem exists_eLpNorm_conjHarmPoly_rotate_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (β : ℝ≥0∞),
      β ≠ ∞ → IsUMDBound X p β → ∀ (N : ℕ) (a b : ℕ → X) (δ : ℝ), 0 < δ → δ < 1 / 2 →
        ∀ ζ : ℂ, ‖ζ‖ = 1 →
        eLpNorm (fun ω => conjHarmPoly N a b (ζ * exitPlace δ ω)) (ENNReal.ofReal p) signLaw ≤
          β ^ 2 * eLpNorm (fun ω => harmPoly N a b (ζ * exitPlace δ ω)) (ENNReal.ofReal p)
            signLaw + (β ^ 2 + 1) * ENNReal.ofReal (C * (2 * harmConst N a b) * δ) := by
  obtain ⟨C, hC0, hC⟩ := exists_eLpNorm_conjHarmPoly_exitPlace_le hp
  refine ⟨C, hC0, fun X _ _ _ β hβt hβ N a b δ hδ0 hδ ζ hζ => ?_⟩
  simp only [conjHarmPoly_rotate, harmPoly_rotate]
  refine (hC X β hβt hβ N _ _ δ hδ0 hδ).trans ?_
  gcongr
  exact harmConst_rotate_le N a b hζ

/-! ### Rotations -/

/-- The `p`-th power of the `L^p` norm, as an integral. -/
private theorem eLpNorm_rpow_eq_lintegral {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] {μ : Measure Ω} {p : ℝ} (hp : 0 < p) {u : Ω → E}
    (hu : AEStronglyMeasurable u μ) :
    eLpNorm u (ENNReal.ofReal p) μ ^ p = ∫⁻ ω, ‖u ω‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hu,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- The `L^p` norm as the power `1 / p` of an integral. -/
private theorem eLpNorm_eq_rpow_lintegral {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] {μ : Measure Ω} {p : ℝ} (hp : 0 < p) {u : Ω → E}
    (hu : AEStronglyMeasurable u μ) :
    eLpNorm u (ENNReal.ofReal p) μ = (∫⁻ ω, ‖u ω‖ₑ ^ p ∂μ) ^ (1 / p) := by
  rw [← eLpNorm_rpow_eq_lintegral hp hu, ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
    ENNReal.rpow_one]

/-- The integration in `α`: if `‖v (α, ·)‖_p ≤ K ‖u (α, ·)‖_p + c` for every `α`, then
`‖v‖_p ≤ K ‖u‖_p + c` on the product with a probability measure, by Minkowski's inequality.
Departure from the source: the paper integrates the `p`-th powers, which changes the constant. -/
private theorem eLpNorm_prod_le_of_forall {A Ω E : Type*} {mA : MeasurableSpace A}
    {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E] {ν : Measure A} [IsProbabilityMeasure ν]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 ≤ p) {u v : A × Ω → E}
    (hu : AEStronglyMeasurable u (ν.prod μ)) (hv : AEStronglyMeasurable v (ν.prod μ))
    {K c : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ α, eLpNorm (fun ω => v (α, ω)) (ENNReal.ofReal p) μ ≤
      K * eLpNorm (fun ω => u (α, ω)) (ENNReal.ofReal p) μ + c) :
    eLpNorm v (ENNReal.ofReal p) (ν.prod μ) ≤
      K * eLpNorm u (ENNReal.ofReal p) (ν.prod μ) + c := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  set H : A → ℝ≥0∞ := fun α => (∫⁻ ω, ‖u (α, ω)‖ₑ ^ p ∂μ) ^ (1 / p) with hH
  have hHm : AEMeasurable H ν := ((hu.enorm.pow_const p).lintegral_prod_right').pow_const _
  have hHp : ∀ α, H α ^ p = ∫⁻ ω, ‖u (α, ω)‖ₑ ^ p ∂μ := fun α => by
    rw [hH, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hle : ∫⁻ z, ‖v z‖ₑ ^ p ∂(ν.prod μ) ≤
      ∫⁻ α, ((fun α => K * H α) + fun _ => c : A → ℝ≥0∞) α ^ p ∂ν := by
    rw [lintegral_prod _ (hv.enorm.pow_const p)]
    refine lintegral_mono_ae ?_
    filter_upwards [hu.prodMk_left, hv.prodMk_left] with α hα hα'
    rw [← eLpNorm_rpow_eq_lintegral hp0 hα']
    refine ENNReal.rpow_le_rpow ((h α).trans ?_) hp0.le
    rw [eLpNorm_eq_rpow_lintegral hp0 hα]
    rfl
  rw [eLpNorm_eq_rpow_lintegral hp0 hv, eLpNorm_eq_rpow_lintegral hp0 hu]
  refine (ENNReal.rpow_le_rpow hle (by positivity)).trans
    ((ENNReal.lintegral_Lp_add_le (hHm.const_mul K) aemeasurable_const hp).trans ?_)
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · simp only [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hHp]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le hK),
      lintegral_prod _ (hu.enorm.pow_const p),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
      mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  · rw [lintegral_const, measure_univ, mul_one, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne',
      ENNReal.rpow_one]

/-- `Z = |Z| e^{iφ}`. -/
private theorem exists_eq_norm_mul_fourier (z : ℂ) :
    ∃ φ : AddCircle (2 * π), z = ‖z‖ * fourier 1 φ := by
  refine ⟨(Complex.arg z : ℝ), ?_⟩
  rw [fourier_one, toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul, Circle.coe_exp,
    Complex.norm_mul_exp_arg_mul_I]

/-- By the translation invariance of `dα`, `∫ |F (e^{iα} z)|^p dα = ∫ |F (|z| e^{iα})|^p dα`. -/
private theorem lintegral_rotate {E : Type*} [NormedAddCommGroup E] (F : ℂ → E) (p : ℝ) (z : ℂ) :
    ∫⁻ α : AddCircle (2 * π), ‖F (fourier 1 α * z)‖ₑ ^ p ∂haarAddCircle =
      ∫⁻ α : AddCircle (2 * π), ‖F (‖z‖ * fourier 1 α)‖ₑ ^ p ∂haarAddCircle := by
  obtain ⟨φ, hφ⟩ := exists_eq_norm_mul_fourier z
  rw [← lintegral_add_right_eq_self (μ := haarAddCircle)
    (fun α : AddCircle (2 * π) => ‖F (‖z‖ * fourier 1 α)‖ₑ ^ p) φ]
  refine lintegral_congr fun α => ?_
  have h : (fourier 1 α : ℂ) * z = ‖z‖ * fourier 1 (α + φ) := by
    conv_lhs => rw [hφ]
    rw [fourier_one, fourier_one, fourier_one, toCircle_add, Circle.coe_mul]
    ring
  rw [h]

/-- `F (Z_τ)`, rotated, is measurable on the product. -/
private theorem aestronglyMeasurable_rotate {E : Type*} [NormedAddCommGroup E] {F : ℂ → E}
    (hF : Continuous F) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) {g : ℂ → ℂ} (hg : Continuous g) :
    AEStronglyMeasurable
      (fun z : AddCircle (2 * π) × (ℕ → Bool) => F (g (exitPlace δ z.2) * fourier 1 z.1))
      (haarAddCircle.prod signLaw) := by
  refine hF.comp_aestronglyMeasurable (AEMeasurable.aestronglyMeasurable ?_)
  refine AEMeasurable.mul ?_ ?_
  · exact hg.measurable.comp_aemeasurable
      ((aemeasurable_exitPlace hδ0 hδ).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd)
  · exact ((map_continuous (fourier 1)).measurable.comp measurable_fst).aemeasurable

/-- Fubini's theorem: `E ∫ |F (e^{iα} Z_τ)|^p dα = E ∫ |F (|Z_τ| e^{iα})|^p dα`. -/
private theorem eLpNorm_rotate_exitPlace {E : Type*} [NormedAddCommGroup E] {F : ℂ → E}
    (hF : Continuous F) {p : ℝ} (hp : 0 < p) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    eLpNorm (fun z : AddCircle (2 * π) × (ℕ → Bool) => F (fourier 1 z.1 * exitPlace δ z.2))
        (ENNReal.ofReal p) (haarAddCircle.prod signLaw) =
      eLpNorm (fun z : AddCircle (2 * π) × (ℕ → Bool) => F (‖exitPlace δ z.2‖ * fourier 1 z.1))
        (ENNReal.ofReal p) (haarAddCircle.prod signLaw) := by
  have h1 := aestronglyMeasurable_rotate hF hδ0 hδ continuous_id
  have h2 := aestronglyMeasurable_rotate hF hδ0 hδ
    (Complex.continuous_ofReal.comp continuous_norm)
  simp only [id_eq, mul_comm (exitPlace δ _)] at h1
  simp only [Function.comp_def] at h2
  rw [eLpNorm_eq_rpow_lintegral hp h1, eLpNorm_eq_rpow_lintegral hp h2,
    lintegral_prod_symm _ (h1.enorm.pow_const p), lintegral_prod_symm _ (h2.enorm.pow_const p)]
  simp only [lintegral_rotate F p]

/-- The numbers `δ_m = 1 / (m + 3)`, with limit `0`. -/
private theorem tendsto_delta : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 3)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

/-- `0 < δ_m < 1/2`. -/
private theorem delta_mem (m : ℕ) : 0 < 1 / ((m : ℝ) + 3) ∧ 1 / ((m : ℝ) + 3) < 1 / 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact ⟨by positivity, one_div_lt_one_div_of_lt two_pos (by linarith)⟩

/-- `δ → 0`: `lim ‖F (|Z_τ| e^{iα})‖_p = ‖F (e^{iα})‖_p` for continuous `F`, by (23) and the
dominated convergence theorem. -/
private theorem tendsto_eLpNorm_exitPlace {E : Type*} [NormedAddCommGroup E] {F : ℂ → E}
    (hF : Continuous F) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun m : ℕ => eLpNorm (fun z : AddCircle (2 * π) × (ℕ → Bool) =>
        F (‖exitPlace (1 / ((m : ℝ) + 3)) z.2‖ * fourier 1 z.1))
      (ENNReal.ofReal p) (haarAddCircle.prod signLaw)) atTop
      (𝓝 (eLpNorm (fun α : AddCircle (2 * π) => F (fourier 1 α)) (ENNReal.ofReal p)
        haarAddCircle)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_norm_le_two hF
  have hmem : ∀ᵐ z : AddCircle (2 * π) × (ℕ → Bool) ∂(haarAddCircle.prod signLaw), ∀ m : ℕ,
      ‖exitPlace (1 / ((m : ℝ) + 3)) z.2‖ ∈ Set.Icc 1 (1 + 2 * (1 / ((m : ℝ) + 3))) :=
    ae_all_iff.2 fun m => Measure.quasiMeasurePreserving_snd.ae
      (ae_norm_exitPlace_mem (delta_mem m).1 (delta_mem m).2)
  have hfst : eLpNorm (fun α : AddCircle (2 * π) => F (fourier 1 α)) (ENNReal.ofReal p)
      haarAddCircle = eLpNorm (fun z : AddCircle (2 * π) × (ℕ → Bool) => F (fourier 1 z.1))
        (ENNReal.ofReal p) (haarAddCircle.prod signLaw) :=
    (eLpNorm_comp_measurePreserving (hF.comp (map_continuous (fourier 1))).aestronglyMeasurable
      measurePreserving_fst).symm
  rw [hfst]
  refine tendsto_eLpNorm_of_bounded hp (C := C) (fun m => ?_) (fun m => ?_) ?_
  · exact aestronglyMeasurable_rotate hF (delta_mem m).1 (delta_mem m).2
      (Complex.continuous_ofReal.comp continuous_norm)
  · filter_upwards [hmem] with z hz
    refine hC _ ?_
    rw [norm_mul, fourier_one, Circle.norm_coe, mul_one, Complex.norm_real, norm_norm]
    linarith [(hz m).2, (delta_mem m).2]
  · filter_upwards [hmem] with z hz
    have hlim : Tendsto (fun m : ℕ => ‖exitPlace (1 / ((m : ℝ) + 3)) z.2‖) atTop (𝓝 1) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun m => (hz m).1) fun m => (hz m).2
      simpa using (tendsto_delta.const_mul 2).const_add 1
    have h := (hF.tendsto ((1 : ℝ) * fourier 1 z.1)).comp
      ((Complex.continuous_ofReal.tendsto 1 |>.comp hlim).mul_const (fourier 1 z.1))
    simpa [Function.comp_def] using h

/-- The integration in `α`: `(E ∫ |v (|Z_τ| e^{iα})|^p dα)^{1/p} ≤
β² (E ∫ |u (|Z_τ| e^{iα})|^p dα)^{1/p} + 2 (β² + 1) C_p γ δ` (p. 282). -/
private theorem exists_eLpNorm_conjHarmPoly_norm_exitPlace_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ,
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (β : ℝ≥0∞),
      β ≠ ∞ → IsUMDBound X p β → ∀ (N : ℕ) (a b : ℕ → X) (δ : ℝ), 0 < δ → δ < 1 / 2 →
        eLpNorm (fun z : AddCircle (2 * π) × (ℕ → Bool) =>
            conjHarmPoly N a b (‖exitPlace δ z.2‖ * fourier 1 z.1))
          (ENNReal.ofReal p) (haarAddCircle.prod signLaw) ≤
        β ^ 2 * eLpNorm (fun z : AddCircle (2 * π) × (ℕ → Bool) =>
            harmPoly N a b (‖exitPlace δ z.2‖ * fourier 1 z.1))
          (ENNReal.ofReal p) (haarAddCircle.prod signLaw) +
        (β ^ 2 + 1) * ENNReal.ofReal (C * (2 * harmConst N a b) * δ) := by
  obtain ⟨C, -, hC⟩ := exists_eLpNorm_conjHarmPoly_rotate_le hp
  refine ⟨C, fun X _ _ _ β hβt hβ N a b δ hδ0 hδ => ?_⟩
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hu := continuous_harmPoly N a b
  have hv := continuous_conjHarmPoly N a b
  have h1 := aestronglyMeasurable_rotate hu hδ0 hδ continuous_id
  have h2 := aestronglyMeasurable_rotate hv hδ0 hδ continuous_id
  simp only [id_eq, mul_comm (exitPlace δ _)] at h1 h2
  rw [← eLpNorm_rotate_exitPlace hu hp0 hδ0 hδ, ← eLpNorm_rotate_exitPlace hv hp0 hδ0 hδ]
  refine eLpNorm_prod_le_of_forall hp.le h1 h2 (ENNReal.pow_ne_top hβt) fun α => ?_
  have h := hC X β hβt hβ N a b δ hδ0 hδ (fourier 1 α) (by rw [fourier_one, Circle.norm_coe])
  exact h

/-- The case `r = 1` of Lemma 2, for a finite UMD constant. -/
private theorem eLpNorm_conjHarmPoly_fourier_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβt : β ≠ ∞) (hβ : IsUMDBound X p β) (N : ℕ) (a b : ℕ → X) :
    eLpNorm (fun θ : AddCircle (2 * π) => conjHarmPoly N a b (fourier 1 θ)) (ENNReal.ofReal p)
        haarAddCircle ≤
      β ^ 2 * eLpNorm (fun θ : AddCircle (2 * π) => harmPoly N a b (fourier 1 θ))
        (ENNReal.ofReal p) haarAddCircle := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain ⟨C, hC⟩ := exists_eLpNorm_conjHarmPoly_norm_exitPlace_le hp
  have hlim : Tendsto (fun m : ℕ => (β ^ 2 + 1) * ENNReal.ofReal
      (C * (2 * harmConst N a b) * (1 / ((m : ℝ) + 3)))) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := β ^ 2 + 1) (ENNReal.tendsto_ofReal
      (tendsto_delta.const_mul (C * (2 * harmConst N a b)))) (Or.inr (by simp [hβt]))
    simpa using h
  have hlim' := (ENNReal.Tendsto.const_mul (tendsto_eLpNorm_exitPlace
    (continuous_harmPoly N a b) hp0) (Or.inr (ENNReal.pow_ne_top (n := 2) hβt))).add hlim
  rw [add_zero] at hlim'
  exact le_of_tendsto_of_tendsto' (tendsto_eLpNorm_exitPlace (continuous_conjHarmPoly N a b) hp0)
    hlim' fun m => hC X β hβt hβ N a b _ (delta_mem m).1 (delta_mem m).2

/-! ### The case `β = ∞` -/

/-- A continuous function on the circle that vanishes almost everywhere is zero. -/
private theorem eq_zero_of_eLpNorm_eq_zero {E : Type*} [NormedAddCommGroup E]
    {f : AddCircle (2 * π) → E} (hf : Continuous f) {p : ℝ} (hp : 0 < p)
    (h : eLpNorm f (ENNReal.ofReal p) haarAddCircle = 0) : f = 0 :=
  (Continuous.ae_eq_iff_eq (haarAddCircle (T := 2 * π)) hf continuous_zero).1
    ((eLpNorm_eq_zero_iff (by simpa using hp)).1 h)

/-- If `u` vanishes on the unit circle, then so does `v`: for the functions `φ ∘ u` with values in
`ℝ`, `φ ∈ X*`, this is Lemma 2 with a finite UMD constant of `ℝ`. Departure from the source: the
paper has a finite constant; this is the case `β = ∞`. -/
private theorem conjHarmPoly_fourier_eq_zero {p : ℝ} (hp : 1 < p) (N : ℕ) (a b : ℕ → X)
    (h : ∀ θ : AddCircle (2 * π), harmPoly N a b (fourier 1 θ) = 0) (θ : AddCircle (2 * π)) :
    conjHarmPoly N a b (fourier 1 θ) = 0 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => ?_
  have hu : ∀ z, φ (harmPoly N a b z) = harmPoly N (fun k => φ (a k)) (fun k => φ (b k)) z :=
    fun z => by simp [harmPoly, map_sum]
  have hv : ∀ z, φ (conjHarmPoly N a b z) =
      conjHarmPoly N (fun k => φ (a k)) (fun k => φ (b k)) z := fun z => by
    simp [conjHarmPoly, map_sum]
  have hle := eLpNorm_conjHarmPoly_fourier_le hp
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (umdConst_le_of_innerProductSpace (H := ℝ) hp))
    (isUMDBound_umdConst hp) N (fun k => φ (a k)) fun k => φ (b k)
  simp only [← hu, ← hv, h, map_zero, eLpNorm_fun_zero, mul_zero, nonpos_iff_eq_zero] at hle
  exact congrFun (eq_zero_of_eLpNorm_eq_zero (φ.continuous.comp
    ((continuous_conjHarmPoly N a b).comp (map_continuous (fourier 1)))) hp0 hle) θ

/-- The case `r = 1` of Lemma 2. -/
private theorem eLpNorm_conjHarmPoly_fourier_le' [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) (N : ℕ) (a b : ℕ → X) :
    eLpNorm (fun θ : AddCircle (2 * π) => conjHarmPoly N a b (fourier 1 θ)) (ENNReal.ofReal p)
        haarAddCircle ≤
      β ^ 2 * eLpNorm (fun θ : AddCircle (2 * π) => harmPoly N a b (fourier 1 θ))
        (ENNReal.ofReal p) haarAddCircle := by
  by_cases hβt : β = ∞
  · by_cases h0 : eLpNorm (fun θ : AddCircle (2 * π) => harmPoly N a b (fourier 1 θ))
        (ENNReal.ofReal p) haarAddCircle = 0
    · have hu := eq_zero_of_eLpNorm_eq_zero
        ((continuous_harmPoly N a b).comp (map_continuous (fourier 1))) (zero_lt_one.trans hp) h0
      rw [funext (conjHarmPoly_fourier_eq_zero hp N a b fun θ => congrFun hu θ), eLpNorm_fun_zero]
      exact zero_le
    · rw [hβt, ENNReal.top_pow two_ne_zero, ENNReal.top_mul h0]
      exact le_top
  · exact eLpNorm_conjHarmPoly_fourier_le hp hβt hβ N a b

variable [CompleteSpace X]

/-- **Lemma 2** of Burkholder (1983): for `u`, `v` of (18), (19), `1 < p < ∞` and `r ≥ 0`,
`‖v (r e^{iθ})‖_p ≤ β² ‖u (r e^{iθ})‖_p`, where the norms are those of `L^p (dθ / 2π)`. -/
theorem eLpNorm_conjHarmPoly_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β) (N : ℕ)
    (a b : ℕ → X) {r : ℝ} (_hr : 0 ≤ r) :
    eLpNorm (fun θ : AddCircle (2 * π) => conjHarmPoly N a b (r * fourier 1 θ))
        (ENNReal.ofReal p) haarAddCircle ≤
      β ^ 2 * eLpNorm (fun θ : AddCircle (2 * π) => harmPoly N a b (r * fourier 1 θ))
        (ENNReal.ofReal p) haarAddCircle := by
  -- the case `r = 1` for `r^k a_k`, `r^k b_k`; the hypothesis `r ≥ 0` is not needed
  simp only [conjHarmPoly_rotate, harmPoly_rotate]
  exact eLpNorm_conjHarmPoly_fourier_le' hp hβ N _ _

/-! ### Trigonometric polynomials on `ℝ / ℤ` -/

/-- The norms of `Φ (e^{2πit})` on `ℝ / ℤ` and of `Φ (e^{iθ})` on `ℝ / 2πℤ` are equal. -/
private theorem eLpNorm_unitAddCircle_eq {E : Type*} [NormedAddCommGroup E] {Φ : ℂ → E}
    (hΦ : Continuous Φ) (q : ℝ≥0∞) :
    eLpNorm (fun t : UnitAddCircle => Φ (fourier 1 t)) q haarAddCircle =
      eLpNorm (fun θ : AddCircle (2 * π) => Φ (fourier 1 θ)) q haarAddCircle := by
  have hpi : 2 * π ≠ 0 := Real.two_pi_pos.ne'
  have hmp : MeasurePreserving (equivAddCircle (1 : ℝ) (2 * π) one_ne_zero hpi).toAddMonoidHom
      haarAddCircle haarAddCircle :=
    AddMonoidHom.measurePreserving (continuous_equivAddCircle _ _ one_ne_zero hpi)
      (equivAddCircle (1 : ℝ) (2 * π) one_ne_zero hpi).surjective (by simp)
  refine Eq.trans ?_ (eLpNorm_comp_measurePreserving (p := q)
    (hΦ.comp (map_continuous (fourier (T := 2 * π) 1))).aestronglyMeasurable hmp)
  refine congrArg (fun G => eLpNorm G q haarAddCircle) (funext fun t => ?_)
  induction t using QuotientAddGroup.induction_on with
  | H x =>
    have h : (fourier 1 (x : UnitAddCircle) : ℂ) =
        fourier 1 ((x * ((1 : ℝ)⁻¹ * (2 * π)) : ℝ) : AddCircle (2 * π)) := by
      rw [fourier_one, fourier_one, toCircle_apply_mk, toCircle_apply_mk]
      congr 2
      field_simp
    exact congrArg Φ h

/-- A sum over the integers `0 < |n| ≤ N`. -/
private theorem sum_Icc_neg_eq {E : Type*} [AddCommGroup E] (f : ℤ → E) (hf : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-N : ℤ) N, f n = ∑ k ∈ Finset.Icc 1 N, (f k + f (-k)) := by
  induction N with
  | zero => simp [hf]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih, add_comm (∑ n ∈ _, f n)]
    push_cast
    exact Finset.sum_Icc_succ_eq_add_endpoints f

/-- A sum over the support of `c`, `c_0 = 0`, as a sum over `k = 1, …, N` of the terms `±k`. -/
private theorem exists_sum_eq {V : Type*} [AddCommGroup V] (c : ℤ →₀ V) (hc : c 0 = 0) :
    ∃ N : ℕ, ∀ g : ℤ → V → V, (∀ n, g n 0 = 0) →
      c.sum g = ∑ k ∈ Finset.Icc 1 N, (g k (c k) + g (-k) (c (-k))) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ∈ c.support, n.natAbs ≤ N :=
    ⟨c.support.sup Int.natAbs, fun n hn => Finset.le_sup (f := Int.natAbs) hn⟩
  refine ⟨N, fun g hg => ?_⟩
  rw [← sum_Icc_neg_eq (fun n => g n (c n)) (by rw [hc, hg]) N, Finsupp.sum]
  refine Finset.sum_subset (fun n hn => ?_) fun n _ hn => ?_
  · have := hN n hn
    rw [Finset.mem_Icc]
    omega
  · rw [Finsupp.notMem_support_iff.1 hn, hg]

/-- `w x + w̄ y = Re w (x + y) + Im w i (x − y)`. -/
private theorem smul_add_conj_smul {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (w : ℂ) (x y : V) :
    w • x + (starRingEnd ℂ) w • y = w.re • (x + y) + w.im • Complex.I • (x - y) := by
  have h : ∀ (r : ℝ) (z : V), r • z = (r : ℂ) • z := fun r z => by
    rw [← smul_one_smul ℂ r z, Complex.real_smul, mul_one]
  obtain ⟨u, v⟩ := w
  have h1 : (starRingEnd ℂ) ⟨u, v⟩ = u - v * Complex.I := by apply Complex.ext <;> simp
  change (⟨u, v⟩ : ℂ) • x + (starRingEnd ℂ) ⟨u, v⟩ • y = u • (x + y) + v • Complex.I • (x - y)
  rw [h, h, h1, Complex.mk_eq_add_mul_I]
  module

/-- `−i w x + i w̄ y = Im w (x + y) − Re w i (x − y)`. -/
private theorem smul_add_conj_smul' {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (w : ℂ) (x y : V) :
    w • (-Complex.I) • x + (starRingEnd ℂ) w • Complex.I • y =
      w.im • (x + y) - w.re • Complex.I • (x - y) := by
  have h := smul_add_conj_smul (-Complex.I * w) x y
  have hre : (-Complex.I * w).re = w.im := by simp
  have him : (-Complex.I * w).im = -w.re := by simp
  have hconj : (starRingEnd ℂ) (-Complex.I * w) = Complex.I * (starRingEnd ℂ) w := by simp
  rw [hre, him, hconj, neg_smul, ← sub_eq_add_neg] at h
  rw [← h, smul_smul, smul_smul, mul_comm w, mul_comm Complex.I]

/-- `e_k (t) = e_1 (t)^k`. -/
private theorem fourier_natCast (k : ℕ) (t : UnitAddCircle) :
    (fourier (k : ℤ) t : ℂ) = fourier 1 t ^ k := by
  rw [fourier_apply, fourier_one, natCast_zsmul, toCircle_nsmul, Circle.coe_pow]

/-- Lemma 2 for a complex space and the functions `e_n (t) = e^{2πi n t}` on `ℝ / ℤ`: if `c_0 = 0`,
`‖Σ_n (−i sgn n) c_n e_n‖_p ≤ β² ‖Σ_n c_n e_n‖_p`. -/
theorem eLpNorm_conj_circPoly_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β) (c : ℤ →₀ X)
    (hc : c 0 = 0) :
    eLpNorm (fun t : UnitAddCircle => c.sum fun n x =>
        fourier n t • (-Complex.I * (n.sign : ℂ)) • x) (ENNReal.ofReal p) haarAddCircle ≤
      β ^ 2 * eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  obtain ⟨N, hN⟩ := exists_sum_eq c hc
  -- `a_k = c_k + c_{−k}`, `b_k = i (c_k − c_{−k})`
  set a : ℕ → X := fun k => c k + c (-k)
  set b : ℕ → X := fun k => Complex.I • (c k - c (-k))
  have hu : circPoly c = fun t : UnitAddCircle => harmPoly N a b (fourier 1 t) := by
    funext t
    rw [circPoly, hN (fun n x => fourier n t • x) fun n => smul_zero _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fourier_neg, fourier_natCast, smul_add_conj_smul]
  have hv : (fun t : UnitAddCircle => c.sum fun n x =>
      fourier n t • (-Complex.I * (n.sign : ℂ)) • x) =
        fun t : UnitAddCircle => conjHarmPoly N a b (fourier 1 t) := by
    funext t
    rw [hN (fun n x => fourier n t • (-Complex.I * (n.sign : ℂ)) • x) fun n => by simp]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : 0 < (k : ℤ) := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    rw [Int.sign_neg, Int.sign_eq_one_of_pos hk0, fourier_neg, fourier_natCast]
    simp only [Int.cast_one, Int.cast_neg, mul_one, mul_neg, neg_neg]
    exact smul_add_conj_smul' _ _ _
  rw [hu, hv, eLpNorm_unitAddCircle_eq (continuous_harmPoly N a b),
    eLpNorm_unitAddCircle_eq (continuous_conjHarmPoly N a b)]
  exact eLpNorm_conjHarmPoly_fourier_le' hp hβ N a b

end HarmonicAnalysis
