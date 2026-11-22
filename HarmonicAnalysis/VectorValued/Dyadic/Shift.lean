/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Dyadic.Martingale
public import HarmonicAnalysis.VectorValued.RademacherNorm
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Dyadic shifts on UMD spaces

Let `X` be a UMD space, `β` a `UMD_p` constant of `X`, `1 < p < ∞`. For `f ∈ L^p (ℝ; X)`, with `Σ_I`
the sum over the dyadic intervals of generation `j`,

* `‖Σ_{j < n} ε_j Σ_I k_I ⟨h_I, f⟩‖_{L^p (ℝ × Ω)} ≤ 2 β ‖f‖_p` for the Haar projections (`k = h`)
  and for the shift with the kernel `k = haarSplit` (`eLpNormRad_dyadicShift_le`);
* `‖Σ_{j < n} Σ_I k_I ⟨h_I, f⟩‖_{L^p} ≤ 2 β² ‖f‖_p` for `k = haarSplit`
  (`eLpNorm_sum_dyadicShift_le`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Propositions
5.1.4 and 5.1.5, pp. 376–378, for the finitely many generations `0 ≤ j < n` and these two kernels
(the factor `2`, which the book does not have, comes from stopping at generation `0`; the book's
shifts are over all generations).

Departure from the source: in the book, Proposition 5.1.4 rests on Theorem 4.2.13 (p. 289), the
unconditionality of the Haar system, with signs `ε_I` indexed by the intervals, and on the equality
of the laws of `(ε_{I_j (x)})_j` and `(ε_j)_j`; the left half of Proposition 5.1.5 is deduced from
that of Proposition 5.1.4, for the Haar expansion of the shift. Here the randomised UMD property is
applied directly, on each unit interval `[m, m + 1)`, a probability space, to the dyadic martingale
`E_j f − E_0 f`, and, for the left half of Proposition 5.1.5, to the martingale `Σ_{j < i} S_j f` of
the partial sums of the shift. The restriction to finitely many generations makes this
simplification possible.
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The part of generation `j` of a dyadic shift is, on each interval of generation `j`, a
measurable scalar function times a constant vector, hence strongly measurable. -/
theorem stronglyMeasurable_dyadicShift {k : ℝ → ℝ} (hk : Measurable k) (j : ℕ) (f : ℝ → X) :
    StronglyMeasurable (dyadicShift k j f) := by
  have hfl : Measurable fun x : ℝ => ⌊2 ^ j * x⌋ :=
    Int.measurable_floor.comp (measurable_const_mul ((2 : ℝ) ^ j))
  exact ((hk.comp (measurable_const_mul ((2 : ℝ) ^ j)).fract).const_mul _).stronglyMeasurable.smul
    ((StronglyMeasurable.of_discrete
      (f := fun n : ℤ => ∫ y, haar (2 ^ j * y - n) • f y)).comp_measurable hfl)

omit [CompleteSpace X] in
/-- The parts of generation `j` of the shift with kernel `haarSplit` and of the Haar expansion
differ by the sign `h ({2^(j+1) x})`. -/
private theorem dyadicShift_haarSplit (j : ℕ) (f : ℝ → X) (x : ℝ) :
    dyadicShift haarSplit j f x = haar (Int.fract (2 ^ (j + 1) * x)) • dyadicShift haar j f x := by
  rw [dyadicShift, dyadicShift, haarSplit_fract, smul_smul, mul_left_comm]

omit [CompleteSpace X] in
/-- The Haar projection of generation `j` is constant on the intervals of generation `j + 1`. -/
private theorem dyadicShift_haar_congr (j : ℕ) (f : ℝ → X) (x y : ℝ)
    (h : ⌊2 ^ (j + 1) * x⌋ = ⌊2 ^ (j + 1) * y⌋) :
    dyadicShift haar j f x = dyadicShift haar j f y := by
  rw [dyadicShift, dyadicShift, haar_fract, haar_fract, floor_two_pow_mul j x,
    floor_two_pow_mul j y, h]

/-- The unit interval `[m, m + 1)` with Lebesgue measure, a probability space. -/
private noncomputable abbrev unitMeasure (m : ℤ) : Measure ℝ :=
  volume.restrict (Set.Ico (m : ℝ) (m + 1))

private instance (m : ℤ) : IsProbabilityMeasure (unitMeasure m) :=
  ⟨by simp⟩

/-- The line is the union of the unit intervals `[m, m + 1)`. -/
private theorem lintegral_eq_tsum_unit (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x = ∑' m : ℤ, ∫⁻ x, g x ∂unitMeasure m := by
  rw [← lintegral_iUnion (fun _ => measurableSet_Ico) (Set.pairwise_disjoint_Ico_intCast ℝ),
    iUnion_Ico_intCast, Measure.restrict_univ]

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem eLpNorm_rpow_eq_tsum {p : ℝ} (hp : 0 < p) {f : ℝ → X}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f (ENNReal.ofReal p) volume ^ p =
      ∑' m : ℤ, eLpNorm f (ENNReal.ofReal p) (unitMeasure m) ^ p := by
  rw [eLpNorm_ofReal_rpow_eq_lintegral hp hf, lintegral_eq_tsum_unit]
  exact tsum_congr fun m => (eLpNorm_ofReal_rpow_eq_lintegral hp hf.restrict).symm

omit [CompleteSpace X] in
private theorem eLpNormRad_rpow_eq_tsum {p : ℝ} (hp : 0 < p) {n : ℕ} {f : Fin n → ℝ → X}
    (hf : ∀ j, AEStronglyMeasurable (f j) volume) :
    eLpNormRad f p volume ^ p = ∑' m : ℤ, eLpNormRad f p (unitMeasure m) ^ p := by
  rw [eLpNormRad_rpow_eq_lintegral hp hf, lintegral_eq_tsum_unit]
  exact tsum_congr fun m => (eLpNormRad_rpow_eq_lintegral hp fun j => (hf j).restrict).symm

/-- Jensen's inequality: averaging over the dyadic intervals does not increase the norm in `L^p` of
a unit interval. -/
private theorem eLpNorm_dyadicAvg_le {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → X} (hf : LocallyIntegrable f)
    (j : ℕ) (m : ℤ) : eLpNorm (dyadicAvg j f) p (unitMeasure m) ≤ eLpNorm f p (unitMeasure m) := by
  have hf' : IntegrableOn f (Set.Ico (m : ℝ) (m + 1)) :=
    (hf.integrableOn_isCompact isCompact_Icc).mono_set Set.Ico_subset_Icc_self
  rw [eLpNorm_congr_ae (dyadicAvg_ae_eq_condExp m hf' j)]
  exact eLpNorm_condExp_le_eLpNorm f hp

/-- HNVW I, Proposition 5.1.4 (right-hand inequality) on a unit interval: the randomised UMD
property for the martingale `E_j f − E_0 f`. -/
private theorem eLpNormRad_haar_unit_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : LocallyIntegrable f) (n : ℕ) (m : ℤ) :
    eLpNormRad (fun j : Fin n => dyadicShift haar j f) p (unitMeasure m) ≤
      2 * β * eLpNorm f (ENNReal.ofReal p) (unitMeasure m) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using hp.le
  have hM := martingale_dyadicAvg hf m
  have hY := hM.sub (martingale_const_fun dyadicFiltration (unitMeasure m)
    (hM.stronglyAdapted 0) (hM.integrable 0))
  have key := hβ.isUpperRandomisedUMDBound (by linarith) ℝ _ (unitMeasure m) dyadicFiltration _ hY
    (fun x => by simp) n
  have hL : eLpNormRad (fun j : Fin n => dyadicShift haar j f) p (unitMeasure m) =
      eLpNorm (randomisedSum ((fun j => dyadicAvg j f) - fun _ => dyadicAvg 0 f) n)
        (ENNReal.ofReal p) ((unitMeasure m).prod (ProbabilityTheory.uniformOn Set.univ)) := by
    rw [eLpNormRad_eq]
    congr 1
    funext z
    rw [randomisedSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dyadicShift_haar hf]
    simp only [Pi.sub_apply, sub_sub_sub_cancel_right]
  rw [hL]
  refine key.trans ?_
  rw [mul_comm 2 β, mul_assoc, two_mul]
  gcongr
  exact (eLpNorm_sub_le hp1).trans
    (add_le_add (eLpNorm_dyadicAvg_le hp1 hf n m) (eLpNorm_dyadicAvg_le hp1 hf 0 m))

/-- HNVW I, Proposition 5.1.4 (right-hand inequality), for the generations `0 ≤ j < n`. -/
private theorem eLpNormRad_haar_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) (n : ℕ) :
    eLpNormRad (fun j : Fin n => dyadicShift haar j f) p volume ≤
      2 * β * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hfl : LocallyIntegrable f := hf.locallyIntegrable (by simpa using hp.le)
  rw [← ENNReal.rpow_le_rpow_iff hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    eLpNormRad_rpow_eq_tsum hp0 fun j =>
      (stronglyMeasurable_dyadicShift measurable_haar j f).aestronglyMeasurable,
    eLpNorm_rpow_eq_tsum hp0 hf.aestronglyMeasurable, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun m => ?_
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  exact ENNReal.rpow_le_rpow (eLpNormRad_haar_unit_le hp hβ hfl n m) hp0.le

/-- The values of the Haar functions on the dyadic intervals are signs. -/
private theorem haar_fract_eq (j : ℕ) (x : ℝ) :
    haar (Int.fract (2 ^ j * x)) = 1 ∨ haar (Int.fract (2 ^ j * x)) = -1 := by
  rw [haar_fract]
  split_ifs <;> simp

private theorem measurable_haar_fract (j : ℕ) :
    Measurable fun x : ℝ => haar (Int.fract (2 ^ j * x)) :=
  measurable_haar.comp (measurable_const_mul ((2 : ℝ) ^ j)).fract

omit [CompleteSpace X] in
/-- The equality of the randomised norms for the kernels `haarSplit` and `haar` (HNVW I, proof of
Proposition 5.1.5; as `|k_I| = |h_I|` here, the contraction principle of the book becomes the
invariance of Rademacher sums under signs). -/
private theorem eLpNormRad_haarSplit {p : ℝ} (hp : 0 < p) (f : ℝ → X) (n : ℕ) :
    eLpNormRad (fun j : Fin n => dyadicShift haarSplit j f) p volume =
      eLpNormRad (fun j : Fin n => dyadicShift haar j f) p volume := by
  rw [← eLpNormRad_sign_smul hp (f := fun j : Fin n => dyadicShift haar j f)
    (fun j => (stronglyMeasurable_dyadicShift measurable_haar j f).aestronglyMeasurable)
    (s := fun j x => haar (Int.fract (2 ^ ((j : ℕ) + 1) * x))) (fun j x => haar_fract_eq _ x)
    fun j => measurable_haar_fract _]
  congr 1
  funext j x
  exact dyadicShift_haarSplit j f x

/-- HNVW I, Propositions 5.1.4 and 5.1.5 (right-hand inequalities), for the generations `0 ≤ j < n`.
-/
theorem eLpNormRad_dyadicShift_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {k : ℝ → ℝ} (hk : k = haar ∨ k = haarSplit) {f : ℝ → X}
    (hf : MemLp f (ENNReal.ofReal p) volume) (n : ℕ) :
    eLpNormRad (fun j : Fin n => dyadicShift k j f) p volume ≤
      2 * β * eLpNorm f (ENNReal.ofReal p) volume := by
  rcases hk with rfl | rfl
  · exact eLpNormRad_haar_le hp hβ hf n
  · rw [eLpNormRad_haarSplit (by linarith)]
    exact eLpNormRad_haar_le hp hβ hf n

/-- The filtration of the dyadic intervals, shifted by one generation. -/
private noncomputable def shiftedFiltration : Filtration ℕ Real.measurableSpace where
  seq i := dyadicFiltration (i + 1)
  mono' _ _ h := dyadicFiltration.mono (by omega)
  le' i := dyadicFiltration.le (i + 1)

omit [CompleteSpace X] in
private theorem integrable_haarSplit (f : ℝ → X) (j : ℕ) (m : ℤ) :
    Integrable (dyadicShift haarSplit j f) (unitMeasure m) := by
  refine integrableOn_smul_comp_floor j m (fun n : ℤ => ∫ y, haar (2 ^ j * y - n) • f y)
    (c := fun x => 2 ^ j * haarSplit (Int.fract (2 ^ j * x)))
    ((measurable_haarSplit.comp (measurable_const_mul ((2 : ℝ) ^ j)).fract).const_mul _)
    (C := 2 ^ j) fun x => ?_
  rw [haarSplit_fract, abs_mul, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity)
    ((mul_le_of_le_one_left (abs_nonneg _) (abs_haar_le_one _)).trans (abs_haar_le_one _))

omit [CompleteSpace X] in
/-- `S_j f` is constant on the intervals of generation `j + 2`. -/
private theorem stronglyMeasurable_haarSplit {f : ℝ → X} (hf : LocallyIntegrable f) (j : ℕ) :
    StronglyMeasurable[dyadicFiltration (j + 2)] (dyadicShift haarSplit j f) := by
  have h1 : StronglyMeasurable[dyadicFiltration (j + 2)] (dyadicShift haar j f) := by
    rw [dyadicShift_haar hf]
    exact ((stronglyMeasurable_dyadicAvg (j + 1) f).mono (dyadicFiltration.mono (by omega))).sub
      ((stronglyMeasurable_dyadicAvg j f).mono (dyadicFiltration.mono (by omega)))
  have h2 : StronglyMeasurable[dyadicFiltration (j + 2)]
      fun x : ℝ => haar (Int.fract (2 ^ (j + 1) * x)) := by
    simp only [haar_fract]
    exact (StronglyMeasurable.of_discrete
      (f := fun n : ℤ => if Even n then (1 : ℝ) else -1)).comp_measurable
        (comap_measurable fun x : ℝ => ⌊2 ^ (j + 2) * x⌋)
  simp only [funext (dyadicShift_haarSplit j f)]
  exact h2.smul h1

/-- On a unit interval, `Σ_{j < i} S_j f`, with `S_j f` the part of generation `j` of the shift with
the kernel `haarSplit`, is a martingale for the filtration shifted by one generation: `S_j f` is
constant on the intervals of generation `j + 2`, with mean zero on those of generation `j + 1`. -/
private theorem martingale_haarSplit {f : ℝ → X} (hf : LocallyIntegrable f) (m : ℤ) :
    Martingale (fun i x => ∑ j ∈ Finset.range i, dyadicShift haarSplit j f x) shiftedFiltration
      (unitMeasure m) := by
  refine martingale_of_condExp_sub_eq_zero_nat (fun i => ?_) (fun i => ?_) fun i => ?_
  · refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    exact (stronglyMeasurable_haarSplit hf j).mono
      (dyadicFiltration.mono (by have := Finset.mem_range.1 hj; omega))
  · exact integrable_finsetSum _ fun j _ => integrable_haarSplit f j m
  · have h : ((fun x => ∑ j ∈ Finset.range (i + 1), dyadicShift haarSplit j f x) -
        fun x => ∑ j ∈ Finset.range i, dyadicShift haarSplit j f x) =
        dyadicShift haarSplit i f := by
      funext x
      rw [Pi.sub_apply, Finset.sum_range_succ, add_sub_cancel_left]
    rw [h]
    refine (dyadicAvg_ae_eq_condExp m (integrable_haarSplit f i m) (i + 1)).symm.trans
      (Filter.EventuallyEq.of_eq ?_)
    funext x
    rw [funext (dyadicShift_haarSplit i f)]
    exact dyadicAvg_haar_smul (i + 1) (dyadicShift_haar_congr i f) x

/-- HNVW I, Proposition 5.1.5 (left-hand inequality), on a unit interval: the randomised UMD
property for the martingale `Σ_{j < i} S_j f`. -/
private theorem eLpNorm_sum_unit_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : LocallyIntegrable f) (n : ℕ) (m : ℤ) :
    eLpNorm (fun x => ∑ j ∈ Finset.range n, dyadicShift haarSplit j f x) (ENNReal.ofReal p)
        (unitMeasure m) ≤
      β * eLpNormRad (fun j : Fin n => dyadicShift haarSplit j f) p (unitMeasure m) := by
  refine (hβ.isLowerRandomisedUMDBound (by linarith) ℝ _ (unitMeasure m) shiftedFiltration _
    (martingale_haarSplit hf m) (fun x => by simp) n).trans (le_of_eq ?_)
  rw [eLpNormRad_eq]
  congr 2
  funext z
  simp only [randomisedSum, Finset.sum_range_succ, add_sub_cancel_left]

/-- HNVW I, Proposition 5.1.5, for the kernel `haarSplit` and the generations `0 ≤ j < n`. -/
theorem eLpNorm_sum_dyadicShift_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) (n : ℕ) :
    eLpNorm (fun x => ∑ j ∈ Finset.range n, dyadicShift haarSplit j f x) (ENNReal.ofReal p) volume ≤
      2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hfl : LocallyIntegrable f := hf.locallyIntegrable (by simpa using hp.le)
  have hm : ∀ j, AEStronglyMeasurable (dyadicShift haarSplit j f) volume := fun j =>
    (stronglyMeasurable_dyadicShift measurable_haarSplit j f).aestronglyMeasurable
  have h : eLpNorm (fun x => ∑ j ∈ Finset.range n, dyadicShift haarSplit j f x) (ENNReal.ofReal p)
      volume ≤ β * eLpNormRad (fun j : Fin n => dyadicShift haarSplit j f) p volume := by
    rw [← ENNReal.rpow_le_rpow_iff hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      eLpNormRad_rpow_eq_tsum hp0 fun j => hm j,
      eLpNorm_rpow_eq_tsum hp0 (Finset.aestronglyMeasurable_fun_sum _ fun j _ => hm j),
      ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun m => ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    exact ENNReal.rpow_le_rpow (eLpNorm_sum_unit_le hp hβ hfl n m) hp0.le
  refine h.trans ?_
  calc β * eLpNormRad (fun j : Fin n => dyadicShift haarSplit j f) p volume
      ≤ β * (2 * β * eLpNorm f (ENNReal.ofReal p) volume) := by
        gcongr
        exact eLpNormRad_dyadicShift_le hp hβ (Or.inr rfl) hf n
    _ = 2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume := by ring

end HarmonicAnalysis
