/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.McConnell.PoissonKernel
import BanachProbability.UMD.Incremental

/-!
# Chains with independent Cauchy increments

T. R. McConnell, *On Fourier multiplier transformations of Banach-valued functions*, Trans. Amer.
Math. Soc. 285 (1984), 739–757, Section 2, considers for a Brownian motion in the half-plane the
place `X (y)` of the first hit of the line of height `y`, under the measures `P_{(x', A)}` (start at
`(x', A)`), `P_{(x', A)}^{/x}` (conditioned to exit at `x`) and `P^x`. Only the finite-dimensional
distributions of the process `X (y)` are used, and these are the following. For heights
`y_0 ≤ y_1 ≤ ⋯ ≤ y_N` the increments `ξ_i = X (y_{i+1}) − X (y_i)` are independent, with the
symmetric Cauchy laws with parameters `y_{i+1} − y_i` (`chainLaw y N` is their joint law,
`chainSum ξ i = X (y_i) − X (y_0)`). Under `P^x` the process starts at `X (y_0) = x`, where
`y_0 = 0` (Lemma 2.3); under `P_{(x', A)}`, `A = y_N`, it starts at `X (y_N) = x'` and runs through
the heights in decreasing order.

* `map_chainSum`: under `P^x` (`y_0 = 0`), `X (y_i)` has the Cauchy law with parameter `y_i` centred
  at `x` (p. 745 and Lemma 2.3).
* `lintegral_chainLaw_reverse`: `∫ P^x dx = ∫ P_{(x', A)} dx'`, in the source from (2.3) and (2.6),
  here from the translation invariance of Lebesgue measure.
* `eLpNorm_sum_smul_le`, `eLpNorm_sum_complex_smul_le`: Burkholder's inequality (2.1) for a sequence
  of martingale differences that are functions of independent variables, with deterministic
  coefficients. The order of the variables is that of `P_{(x', A)}`: the variable with the largest
  index comes first.
* `map_two_chains`: Lemma 3.2.
-/

@[expose] public section

open MeasureTheory Filter BanachProbability
open scoped ENNReal Topology

namespace HarmonicAnalysis

/-! ### Replacing one coordinate -/

/-- In a product of probability measures `ν_j`, replacing the `i`-th coordinate by an independent
variable with the law `ν_i` does not change the law. -/
private theorem measurePreserving_update {N : ℕ} (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (i : Fin N) :
    MeasurePreserving (fun w : (Fin N → ℝ) × ℝ => Function.update w.1 i w.2)
      ((Measure.pi ν).prod (ν i)) (Measure.pi ν) := by
  have hm : Measurable fun w : (Fin N → ℝ) × ℝ => Function.update w.1 i w.2 := by
    refine measurable_pi_iff.2 fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · simpa using measurable_snd
    · simp only [Function.update_of_ne hj]
      fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  have hpre : (fun w : (Fin N → ℝ) × ℝ => Function.update w.1 i w.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext w
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · refine fun h => ⟨fun j => ?_, by simpa using h i⟩
      rcases eq_or_ne j i with rfl | hj
      · simp
      · simpa only [Function.update_of_ne hj] using h j
    · rintro ⟨h, hi⟩ j
      rcases eq_or_ne j i with rfl | hj
      · simpa using hi
      · simpa only [Function.update_of_ne hj] using h j
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => ν j (s j)) (Finset.mem_univ i),
    Function.update_self, measure_univ, one_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-! ### The law of a chain -/

/-- The joint law of the increments `ξ_i = X (y_{i+1}) − X (y_i)`, `0 ≤ i < N`: independent, with
the symmetric Cauchy laws with parameters `y_{i+1} − y_i`. -/
noncomputable def chainLaw (y : ℕ → ℝ) (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun i : Fin N => cauchyLaw (y (i + 1) - y i)

instance isProbabilityMeasure_chainLaw (y : ℕ → ℝ) (N : ℕ) :
    IsProbabilityMeasure (chainLaw y N) := by
  unfold chainLaw
  infer_instance

/-- `X (y_i) − X (y_0)`, the sum of the increments `ξ_j`, `j < i`. -/
def chainSum {N : ℕ} (ξ : Fin N → ℝ) (i : ℕ) : ℝ :=
  ∑ j : Fin N, if (j : ℕ) < i then ξ j else 0

/-- `X (y_0) − X (y_0) = 0`. -/
theorem chainSum_zero {N : ℕ} (ξ : Fin N → ℝ) : chainSum ξ 0 = 0 := by
  simp [chainSum]

/-- `X (y_{i+1}) = X (y_i) + ξ_i`. -/
theorem chainSum_succ {N : ℕ} (ξ : Fin N → ℝ) (i : Fin N) :
    chainSum ξ (i + 1) = chainSum ξ i + ξ i := by
  have h : ∀ j : Fin N, (if (j : ℕ) < i + 1 then ξ j else 0) =
      (if (j : ℕ) < i then ξ j else 0) + if i = j then ξ j else 0 := by
    intro j
    rcases lt_trichotomy (j : ℕ) i with h | h | h
    · simp [h, h.trans (Nat.lt_succ_self _), Fin.ext_iff, h.ne']
    · simp [h, Fin.ext_iff]
    · simp [h.not_gt, Nat.not_lt.2 (Nat.succ_le_of_lt h), Fin.ext_iff, h.ne]
  simp only [chainSum, h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `X (y_i)` is a continuous function of the increments. -/
theorem continuous_chainSum {N : ℕ} (i : ℕ) : Continuous fun ξ : Fin N → ℝ => chainSum ξ i := by
  unfold chainSum
  refine continuous_finsetSum _ fun j _ => ?_
  split_ifs
  exacts [continuous_apply j, continuous_const]

/-- Replacing the increment `ξ_i` does not change `X (y_i)`. -/
private theorem chainSum_update {N : ℕ} (ξ : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    chainSum (Function.update ξ i t) i = chainSum ξ i := by
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Function.update_of_ne (Fin.ne_of_lt h)]
  · rfl

/-- For a chain started at `X (y_0) = x`, the variable `X (y_i) − x` has the Cauchy law with
parameter `y_i − y_0` (under `P^x`, where `y_0 = 0`, with parameter `y_i`): McConnell (1984), p. 745
and Lemma 2.3. -/
theorem map_chainSum {y : ℕ → ℝ} (hy : Monotone y) {N i : ℕ} (hi : i ≤ N) :
    (chainLaw y N).map (fun ξ => chainSum ξ i) = cauchyLaw (y i - y 0) := by
  induction i with
  | zero => simp [chainSum_zero, cauchyLaw_zero]
  | succ i ih =>
    -- `X (y_{i+1}) − x = (X (y_i) − x) + ξ_i`, a sum of two independent Cauchy variables
    have hsum : (fun ξ : Fin N → ℝ => chainSum ξ (i + 1)) ∘
        (fun w : (Fin N → ℝ) × ℝ => Function.update w.1 ⟨i, hi⟩ w.2) =
        (fun x : ℝ × ℝ => x.1 + x.2) ∘ Prod.map (fun ξ : Fin N → ℝ => chainSum ξ i) id := by
      funext w
      have h := chainSum_succ (Function.update w.1 ⟨i, hi⟩ w.2) ⟨i, hi⟩
      rw [chainSum_update, Function.update_self] at h
      exact h
    have hm : ∀ j, Measurable fun ξ : Fin N → ℝ => chainSum ξ j := fun j =>
      (continuous_chainSum j).measurable
    have hμ := measurePreserving_update (fun j : Fin N => cauchyLaw (y (j + 1) - y j)) ⟨i, hi⟩
    rw [chainLaw, ← hμ.map_eq, Measure.map_map (hm _) hμ.measurable, hsum,
      ← Measure.map_map (by fun_prop) ((hm i).prodMap measurable_id),
      ← Measure.map_prod_map _ _ (hm i) measurable_id, Measure.map_id]
    have hconv := cauchyLaw_conv (sub_nonneg.2 (hy (Nat.zero_le i)))
      (sub_nonneg.2 (hy (Nat.le_succ i)))
    rw [← ih (Nat.le_of_succ_le hi), chainLaw, Measure.conv] at hconv
    rw [hconv]
    congr 1
    exact (add_comm _ _).trans (sub_add_sub_cancel _ _ _)

/-- The chain up to the height `y_N` is the chain up to `y_{N+1}` without its last increment: the
laws of the process under the measures `P^{x, A}` are consistent (McConnell (1984), p. 745). -/
theorem map_init_chainLaw (y : ℕ → ℝ) (N : ℕ) :
    (chainLaw y (N + 1)).map Fin.init = chainLaw y N := by
  have h := measurePreserving_snd.comp (measurePreserving_piFinSuccAbove
    (fun i : Fin (N + 1) => cauchyLaw (y (i + 1) - y i)) (Fin.last N))
  simpa [chainLaw, Function.comp_def, MeasurableEquiv.piFinSuccAbove] using h.map_eq

/-- `X (y_i)`, `i ≤ N`, does not depend on the increment `ξ_N`. -/
theorem chainSum_init {N : ℕ} (ξ : Fin (N + 1) → ℝ) {i : ℕ} (hi : i ≤ N) :
    chainSum (Fin.init ξ : Fin N → ℝ) i = chainSum ξ i := by
  simp [chainSum, Fin.sum_univ_castSucc, Fin.init, hi.not_gt]

/-- `∫ P^x dx = ∫ P_{(x', A)} dx'`: McConnell (1984), from (2.3) and (2.6) (p. 749), used in (3.10)
and in the displays before Lemma 3.2 (p. 750) and after (3.11) (p. 751). On the left the chain
starts at `X (y_0) = x`, on the right at `X (y_N) = x'`. -/
theorem lintegral_chainLaw_reverse (y : ℕ → ℝ) (N : ℕ) {F : ℝ → (Fin N → ℝ) → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ x, ∫⁻ ξ, F x ξ ∂chainLaw y N =
      ∫⁻ x', ∫⁻ ξ, F (x' - chainSum ξ N) ξ ∂chainLaw y N := by
  have hG : Measurable (Function.uncurry fun x' (ξ : Fin N → ℝ) => F (x' - chainSum ξ N) ξ) :=
    hF.comp ((measurable_fst.sub ((continuous_chainSum N).measurable.comp measurable_snd)).prodMk
      measurable_snd)
  rw [lintegral_lintegral_swap hF.aemeasurable, lintegral_lintegral_swap hG.aemeasurable]
  refine lintegral_congr fun ξ => ?_
  exact (lintegral_sub_right_eq_self (fun x => F x ξ) (chainSum ξ N)).symm

/-! ### Martingale differences on a product space -/

/-- The variables with index `≥ N − k`; the others are replaced by `0`. -/
private def tail (N k : ℕ) (ξ : Fin N → ℝ) (j : Fin N) : ℝ :=
  if N ≤ j + k then ξ j else 0

/-- `tail N k` is measurable. -/
private theorem measurable_tail (N k : ℕ) : Measurable (tail N k) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold tail
  split_ifs
  exacts [measurable_pi_apply j, measurable_const]

/-- The σ-algebras `ℱ_k` generated by the variables with index `≥ N − k`. (McConnell (1984),
Lemma 2.1, where the σ-algebra "may be chosen", takes those generated by the differences.) -/
private def tailFiltration (N : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin N → ℝ)) where
  seq k := MeasurableSpace.comap (tail N k) inferInstance
  mono' k l hkl := by
    have h : tail N k = tail N k ∘ tail N l := by
      funext ξ j
      simp only [tail, Function.comp_apply]
      split_ifs with h1 h2
      exacts [rfl, absurd (h1.trans (Nat.add_le_add_left hkl _)) h2, rfl]
    change MeasurableSpace.comap (tail N k) inferInstance ≤ _
    rw [h, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_tail N k).comap_le
  le' k := (measurable_tail N k).comap_le

section Martingale

variable {X : Type*} [NormedAddCommGroup X] {N : ℕ} {ν : Fin N → Measure ℝ}
  [∀ i, IsProbabilityMeasure (ν i)] {D : Fin N → (Fin N → ℝ) → X}

/-- `Σ_{i ≥ N − k} D_i`. -/
private def tailSum (D : Fin N → (Fin N → ℝ) → X) (k : ℕ) (ξ : Fin N → ℝ) : X :=
  ∑ i : Fin N, if N ≤ i + k then D i ξ else 0

/-- `Y_0 = 0`. -/
private theorem tailSum_zero (ξ : Fin N → ℝ) : tailSum D 0 ξ = 0 :=
  Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)

/-- `Y_N = Σ_i D_i`. -/
private theorem tailSum_self (ξ : Fin N → ℝ) : tailSum D N ξ = ∑ i, D i ξ :=
  Finset.sum_congr rfl fun i _ => ite_eq_left (by omega)

/-- `Y_{k+1} − Y_k = D_{N−1−k}` for `Y_k = Σ_{i ≥ N − k} D_i`. -/
private theorem tailSum_succ (k : Fin N) (ξ : Fin N → ℝ) :
    tailSum D (k + 1) ξ = tailSum D k ξ + D k.rev ξ := by
  have h : ∀ i : Fin N, (if N ≤ i + (k + 1) then D i ξ else 0) =
      (if N ≤ i + k then D i ξ else 0) + if k.rev = i then D i ξ else 0 := by
    intro i
    have h1 : (k.rev : ℕ) = N - (k + 1) := Fin.val_rev k
    have h2 : k.rev = i ↔ N = i + k + 1 := by
      rw [Fin.ext_iff]
      omega
    rcases lt_trichotomy N (i + k + 1) with h | h | h
    · simp [h2, h.ne, show N ≤ i + (k + 1) by omega, show N ≤ i + k by omega]
    · simp [h2, h, show ¬ i + k + 1 ≤ (i : ℕ) + k by omega, ← add_assoc]
    · simp [h2, h.ne', show ¬ N ≤ i + (k + 1) by omega, show ¬ N ≤ i + k by omega]
  simp only [tailSum, h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `Y_k = Y_N` for `k ≥ N`. -/
private theorem tailSum_succ_of_le {k : ℕ} (hk : N ≤ k) (ξ : Fin N → ℝ) :
    tailSum D (k + 1) ξ = tailSum D k ξ := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]

/-- `D_i` is `ℱ_k`-measurable if `i ≥ N − k`: it is a function of the variables with index `≥ i`. -/
private theorem stronglyMeasurable_tail (hDm : ∀ i, StronglyMeasurable (D i))
    (hdep : ∀ i ξ ξ', (∀ j, i ≤ j → ξ j = ξ' j) → D i ξ = D i ξ') {i : Fin N} {k : ℕ}
    (h : N ≤ i + k) : StronglyMeasurable[tailFiltration N k] (D i) := by
  have e : D i = D i ∘ tail N k := by
    funext ξ
    refine hdep i _ _ fun j hj => ?_
    have hj' : (i : ℕ) ≤ j := hj
    exact (ite_eq_left (by omega)).symm
  rw [e]
  exact (hDm i).comp_measurable (comap_measurable _)

/-- `E [D_i | ℱ_k] = 0` for `k ≤ N − 1 − i`: a set `s` in `ℱ_k` does not depend on the `i`-th
variable, and the mean of `D_i` over this variable is zero. -/
private theorem setIntegral_tail_eq_zero [NormedSpace ℝ X]
    (hDm : ∀ i, StronglyMeasurable (D i)) {C : ℝ} (hDC : ∀ i ξ, ‖D i ξ‖ ≤ C)
    (hmean : ∀ i ξ, ∫ t, D i (Function.update ξ i t) ∂ν i = 0) {i : Fin N} {k : ℕ}
    (h : i + k < N) {s : Set (Fin N → ℝ)} (hs : MeasurableSet[tailFiltration N k] s) :
    ∫ ξ in s, D i ξ ∂Measure.pi ν = 0 := by
  have hs' : MeasurableSet s := (tailFiltration N).le k s hs
  -- `s` does not depend on the `i`-th variable
  have hsi : ∀ ξ t, Function.update ξ i t ∈ s ↔ ξ ∈ s := by
    obtain ⟨u, -, rfl⟩ := hs
    intro ξ t
    have e : tail N k (Function.update ξ i t) = tail N k ξ := by
      funext j
      simp only [tail]
      split_ifs with hj
      · rw [Function.update_of_ne (by rintro rfl; omega)]
      · rfl
    simp only [Set.mem_preimage, e]
  have hint : Integrable (s.indicator (D i)) (Measure.pi ν) :=
    (Integrable.of_bound (hDm i).aestronglyMeasurable C (ae_of_all _ (hDC i))).indicator hs'
  -- replace the `i`-th variable by an independent one
  have hμ := measurePreserving_update ν i
  have hrep := integral_map (f := s.indicator (D i)) hμ.measurable.aemeasurable
    (by rw [hμ.map_eq]; exact hint.aestronglyMeasurable)
  rw [hμ.map_eq] at hrep
  rw [← integral_indicator hs', hrep,
    integral_prod (fun w => s.indicator (D i) (Function.update w.1 i w.2))
      (hμ.integrable_comp_of_integrable hint)]
  refine integral_eq_zero_of_ae (ae_of_all _ fun ξ => ?_)
  by_cases hξ : ξ ∈ s
  · simp only [Set.indicator_of_mem ((hsi ξ _).2 hξ)]
    exact hmean i ξ
  · simp only [Set.indicator_of_notMem (mt (hsi ξ _).1 hξ), integral_zero, Pi.zero_apply]

/-- The sums `Y_k = Σ_{i ≥ N − k} D_i` are a martingale for the filtration `ℱ_k`. -/
private theorem martingale_tailSum [NormedSpace ℝ X] [CompleteSpace X]
    (hDm : ∀ i, StronglyMeasurable (D i)) {C : ℝ} (hDC : ∀ i ξ, ‖D i ξ‖ ≤ C)
    (hdep : ∀ i ξ ξ', (∀ j, i ≤ j → ξ j = ξ' j) → D i ξ = D i ξ')
    (hmean : ∀ i ξ, ∫ t, D i (Function.update ξ i t) ∂ν i = 0) :
    Martingale (tailSum D) (tailFiltration N) (Measure.pi ν) := by
  have hDi : ∀ i, Integrable (D i) (Measure.pi ν) := fun i =>
    Integrable.of_bound (hDm i).aestronglyMeasurable C (ae_of_all _ (hDC i))
  have hint : ∀ k, Integrable (tailSum D k) (Measure.pi ν) := by
    intro k
    refine integrable_finsetSum _ fun i _ => ?_
    split_ifs
    exacts [hDi i, integrable_zero _ _ _]
  refine martingale_of_setIntegral_eq_succ (fun k => ?_) hint fun k s hs => ?_
  · refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
    split_ifs with h
    exacts [stronglyMeasurable_tail hDm hdep h, stronglyMeasurable_const]
  · rcases lt_or_ge k N with hk | hk
    · simp only [tailSum_succ (D := D) ⟨k, hk⟩]
      rw [integral_add (hint k).integrableOn (hDi _).integrableOn,
        setIntegral_tail_eq_zero hDm hDC hmean (k := k) _ hs, add_zero]
      rw [Fin.val_rev]
      change N - (k + 1) + k < N
      omega
    · simp only [tailSum_succ_of_le hk]

/-- **Burkholder's inequality**, McConnell (1984), (2.1), for a Banach space with a `UMD_p`
constant `β`: the functions `D_i`, `i = N − 1, …, 0`, of independent variables form a martingale
difference sequence, since `D_i` depends only on the variables with index `≥ i` and its mean over
the `i`-th variable is zero; the coefficients `e_i ∈ [−1, 1]` are deterministic (they lie in the
convex hull of the sequences of signs). -/
theorem eLpNorm_sum_smul_le [NormedSpace ℝ X] [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) (hDm : ∀ i, StronglyMeasurable (D i)) {C : ℝ}
    (hDC : ∀ i ξ, ‖D i ξ‖ ≤ C)
    (hdep : ∀ i ξ ξ', (∀ j, i ≤ j → ξ j = ξ' j) → D i ξ = D i ξ')
    (hmean : ∀ i ξ, ∫ t, D i (Function.update ξ i t) ∂ν i = 0) {e : Fin N → ℝ}
    (he : ∀ i, |e i| ≤ 1) :
    eLpNorm (fun ξ => ∑ i, e i • D i ξ) (ENNReal.ofReal p) (Measure.pi ν) ≤
      β * eLpNorm (fun ξ => ∑ i, D i ξ) (ENNReal.ofReal p) (Measure.pi ν) := by
  -- the transform by the coefficients `e_{N−1}, …, e_0` of the martingale `Y_k = Σ_{i ≥ N − k} D_i`
  have hY := martingale_tailSum (ν := ν) hDm hDC hdep hmean
  have key := ((isUMDBound_iff_isDeterministicUMDBound hp.le).1 hβ).eLpNorm_le_of_norm_le_one
    hp.le hY (fun ξ => tailSum_zero ξ)
    (a := fun n => if h : n - 1 < N then e (Fin.rev ⟨n - 1, h⟩) else 0)
    (fun n => by
      split_ifs
      exacts [he _, by simp]) N
  have hsum : ∀ ξ, (∑ k ∈ Finset.range N,
      (if h : k + 1 - 1 < N then e (Fin.rev ⟨k + 1 - 1, h⟩) else 0) •
        (tailSum D (k + 1) ξ - tailSum D k ξ)) = ∑ i, e i • D i ξ := by
    intro ξ
    rw [Finset.sum_range, ← Equiv.sum_comp Fin.revPerm fun i => e i • D i ξ]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [tailSum_succ]
  have hm : StronglyMeasurable fun ξ => ∑ i, e i • D i ξ :=
    Finset.stronglyMeasurable_fun_sum _ fun i _ => (hDm i).const_smul (e i)
  have hm' : StronglyMeasurable fun ξ => ∑ i, D i ξ :=
    Finset.stronglyMeasurable_fun_sum _ fun i _ => hDm i
  simp only [tailSum_self, hsum] at key
  rwa [eLpNorm_norm _ hm'.aestronglyMeasurable, eLpNorm_norm _ hm.aestronglyMeasurable] at key

/-- The same for complex coefficients of modulus at most `1`, with the factor `2`: their real and
imaginary parts lie in `[−1, 1]`. -/
theorem eLpNorm_sum_complex_smul_le [NormedSpace ℂ X] [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) (hDm : ∀ i, StronglyMeasurable (D i)) {C : ℝ}
    (hDC : ∀ i ξ, ‖D i ξ‖ ≤ C)
    (hdep : ∀ i ξ ξ', (∀ j, i ≤ j → ξ j = ξ' j) → D i ξ = D i ξ')
    (hmean : ∀ i ξ, ∫ t, D i (Function.update ξ i t) ∂ν i = 0) {e : Fin N → ℂ}
    (he : ∀ i, ‖e i‖ ≤ 1) :
    eLpNorm (fun ξ => ∑ i, e i • D i ξ) (ENNReal.ofReal p) (Measure.pi ν) ≤
      2 * β * eLpNorm (fun ξ => ∑ i, D i ξ) (ENNReal.ofReal p) (Measure.pi ν) := by
  have hre := eLpNorm_sum_smul_le hp hβ hDm hDC hdep hmean
    fun i => (Complex.abs_re_le_norm (e i)).trans (he i)
  have him := eLpNorm_sum_smul_le hp hβ hDm hDC hdep hmean
    fun i => (Complex.abs_im_le_norm (e i)).trans (he i)
  have hsum : (fun ξ => ∑ i, e i • D i ξ) =
      (fun ξ => ∑ i, (e i).re • D i ξ) + Complex.I • fun ξ => ∑ i, (e i).im • D i ξ := by
    funext ξ
    simp only [Pi.add_apply, Pi.smul_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← Complex.re_add_im (e i), add_smul, mul_comm, mul_smul, Complex.coe_smul,
      Complex.coe_smul]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  rw [hsum]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_const_smul, show ‖Complex.I‖ₑ = 1 by simp [enorm_eq_nnnorm], one_mul, mul_assoc,
    two_mul]
  exact add_le_add hre him

end Martingale

/-! ### Two independent chains -/

/-- The heights `z_{2i} = 2 y_i`, `z_{2i+1} = y_i + y_{i+1}` (McConnell (1984), p. 751). -/
def zigzag (y : ℕ → ℝ) (j : ℕ) : ℝ :=
  y (j / 2) + y ((j + 1) / 2)

/-- The increments of the first sequence of McConnell (1984), Lemma 3.2 are `ζ_{2i} = ξ_i` and
`ζ_{2i+1} = −ξ̃_i`. -/
private def interleave {N : ℕ} (w : (Fin N → ℝ) × (Fin N → ℝ)) (j : Fin (2 * N)) : ℝ :=
  if (j : ℕ) % 2 = 0 then w.1 ⟨j / 2, by omega⟩ else -w.2 ⟨j / 2, by omega⟩

/-- `ζ_{2i} = ξ_i`. -/
private theorem interleave_even {N : ℕ} (w : (Fin N → ℝ) × (Fin N → ℝ)) (i : Fin N) :
    interleave w ⟨2 * i, by omega⟩ = w.1 i := by
  simp [interleave]

/-- `ζ_{2i+1} = −ξ̃_i`. -/
private theorem interleave_odd {N : ℕ} (w : (Fin N → ℝ) × (Fin N → ℝ)) (i : Fin N) :
    interleave w ⟨2 * i + 1, by omega⟩ = -w.2 i := by
  have h : (2 * (i : ℕ) + 1) / 2 = i := by omega
  simp [interleave, h]

/-- The increments `ζ` are measurable functions of `ξ` and `ξ̃`. -/
private theorem measurable_interleave {N : ℕ} : Measurable (interleave (N := N)) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold interleave
  split_ifs <;> fun_prop

/-- The `j`-th term of the first sequence of McConnell (1984), Lemma 3.2 (without the starting
point), is the sum of the increments `ζ_l`, `l < j`. -/
private theorem chainSum_interleave {N : ℕ} (w : (Fin N → ℝ) × (Fin N → ℝ)) {j : ℕ}
    (hj : j ≤ 2 * N) :
    chainSum (interleave w) j = chainSum w.1 ((j + 1) / 2) - chainSum w.2 (j / 2) := by
  induction j with
  | zero => simp [chainSum_zero]
  | succ j ih =>
    rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
    · have h := chainSum_succ (interleave w) ⟨2 * m, hj⟩
      have h1 := chainSum_succ w.1 ⟨m, by omega⟩
      rw [interleave_even w ⟨m, by omega⟩, ih (by omega)] at h
      refine h.trans ?_
      rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega, h1,
        show 2 * m / 2 = m by omega]
      ring
    · have h := chainSum_succ (interleave w) ⟨2 * m + 1, hj⟩
      have h1 := chainSum_succ w.2 ⟨m, by omega⟩
      rw [interleave_odd w ⟨m, by omega⟩, ih (by omega)] at h
      refine h.trans ?_
      rw [show (2 * m + 1 + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
        h1, show (2 * m + 1) / 2 = m by omega]
      ring

/-- A product over `Fin (2 N)`, by parity. -/
private theorem prod_fin_two_mul {M : Type*} [CommMonoid M] {N : ℕ} (f : Fin (2 * N) → M) :
    ∏ j, f j = (∏ i : Fin N, f ⟨2 * i, by omega⟩) * ∏ i : Fin N, f ⟨2 * i + 1, by omega⟩ := by
  set g : ℕ → M := fun j => if h : j < 2 * N then f ⟨j, h⟩ else 1
  have h : ∀ n, ∏ j ∈ Finset.range (2 * n), g j =
      (∏ i ∈ Finset.range n, g (2 * i)) * ∏ i ∈ Finset.range n, g (2 * i + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, Finset.prod_range_succ, Finset.prod_range_succ, ih,
        Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc, mul_mul_mul_comm]
  have h1 := h N
  simp only [Finset.prod_range] at h1
  have h2 : ∀ j : Fin (2 * N), g j = f j := fun j => dite_eq_left j.2
  have h3 : ∀ i : Fin N, g (2 * i) = f ⟨2 * i, by omega⟩ := fun i => dite_eq_left _
  have h4 : ∀ i : Fin N, g (2 * i + 1) = f ⟨2 * i + 1, by omega⟩ := fun i => dite_eq_left _
  simpa only [h2, h3, h4] using h1

/-- The parameters of the increments of even index, `z_{2i+1} − z_{2i} = y_{i+1} − y_i`. -/
private theorem zigzag_sub_even (y : ℕ → ℝ) (i : ℕ) :
    zigzag y (2 * i + 1) - zigzag y (2 * i) = y (i + 1) - y i := by
  simp only [zigzag, show (2 * i + 1) / 2 = i by omega, show (2 * i + 1 + 1) / 2 = i + 1 by omega,
    show 2 * i / 2 = i by omega]
  ring

/-- The parameters of the increments of odd index, `z_{2i+2} − z_{2i+1} = y_{i+1} − y_i`. -/
private theorem zigzag_sub_odd (y : ℕ → ℝ) (i : ℕ) :
    zigzag y (2 * i + 1 + 1) - zigzag y (2 * i + 1) = y (i + 1) - y i := by
  simp only [zigzag, show (2 * i + 1) / 2 = i by omega, show (2 * i + 1 + 1) / 2 = i + 1 by omega,
    show (2 * i + 1 + 1 + 1) / 2 = i + 1 by omega]
  ring

/-- By the symmetry of the Cauchy law and the comparison of the parameters, the increments `ζ_j` are
independent with the Cauchy laws with parameters `z_{j+1} − z_j`. -/
private theorem map_interleave (y : ℕ → ℝ) (N : ℕ) :
    ((chainLaw y N).prod (chainLaw y N)).map interleave = chainLaw (zigzag y) (2 * N) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : interleave ⁻¹' Set.univ.pi s =
      (Set.univ.pi fun i : Fin N => s ⟨2 * i, by omega⟩) ×ˢ
        Set.univ.pi fun i : Fin N => (fun t : ℝ => -t) ⁻¹' s ⟨2 * i + 1, by omega⟩ := by
    ext w
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    refine ⟨fun h => ⟨fun i => ?_, fun i => ?_⟩, fun h j => ?_⟩
    · simpa only [interleave_even] using h ⟨2 * i, by omega⟩
    · simpa only [interleave_odd] using h ⟨2 * i + 1, by omega⟩
    · obtain ⟨j, hj⟩ := j
      rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
      · simpa only [interleave_even w ⟨m, by omega⟩] using h.1 ⟨m, by omega⟩
      · simpa only [interleave_odd w ⟨m, by omega⟩] using h.2 ⟨m, by omega⟩
  rw [Measure.map_apply measurable_interleave (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    chainLaw, Measure.pi_pi, Measure.pi_pi, prod_fin_two_mul]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [zigzag_sub_even]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [zigzag_sub_odd, ← Measure.map_apply measurable_neg (hs _), map_neg_cauchyLaw]

/-- McConnell (1984), Lemma 3.2: for an independent copy `X̃` of the process, started at `0`, the
sequence `X (y_0) − X̃ (y_0), X (y_1) − X̃ (y_0), X (y_1) − X̃ (y_1), …, X (y_N) − X̃ (y_N)` has the
same distribution as `X (2y_0), X (y_0 + y_1), X (2y_1), …, X (2y_N)`. (Here `y_0 = 0`, as in the
proof there; the starting point `x` of `X` is subtracted on both sides.) -/
theorem map_two_chains (y : ℕ → ℝ) (N : ℕ) :
    ((chainLaw y N).prod (chainLaw y N)).map (fun w (j : Fin (2 * N + 1)) =>
        chainSum w.1 ((j + 1) / 2) - chainSum w.2 (j / 2)) =
      (chainLaw (zigzag y) (2 * N)).map fun ζ (j : Fin (2 * N + 1)) => chainSum ζ j := by
  have hm : Measurable fun (ζ : Fin (2 * N) → ℝ) (j : Fin (2 * N + 1)) => chainSum ζ j :=
    measurable_pi_iff.2 fun j => (continuous_chainSum _).measurable
  rw [← map_interleave, Measure.map_map hm measurable_interleave]
  congr 1
  funext w j
  exact (chainSum_interleave w (Nat.lt_succ_iff.1 j.2)).symm

end HarmonicAnalysis
