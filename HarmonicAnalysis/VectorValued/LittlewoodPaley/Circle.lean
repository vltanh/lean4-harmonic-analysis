/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.LittlewoodPaley.Line
public import HarmonicAnalysis.VectorValued.Transference
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# The Littlewood–Paley inequality on the circle for UMD spaces

`𝕋 = ℝ / ℤ` with its normalised Haar measure, `e_n (t) = e^{2πi n t}`. For a trigonometric
polynomial `f = Σ_n c_n e_n` (`circPoly c`) with coefficients in a complex UMD space `X`, and the
dyadic blocks `Ĩ_0 = {0}`, `Ĩ_k = [2^{k−1}, 2^k) ∩ ℤ`, `Ĩ_{−k} = −Ĩ_k` for `k > 0` (`dyadicBlock`),
let `Δ̃_k f = Σ_{n ∈ Ĩ_k} c_n e_n`. **Theorem** (`eLpNormRad_dyadicBlock_le`): for `1 < p < ∞`,

`‖Σ_{|k| ≤ K} ε_k Δ̃_k f‖_{L^p (Ω × 𝕋; X)} ≤ C_β ‖f‖_{L^p (𝕋; X)}`,

with a constant that depends only on a `UMD_p` constant `β` of `X`.

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Theorem 5.7.10
(2), right-hand inequality, pp. 464–466: Corollary 5.3.25, for the intervals `I_k` of the line,
says that the multiplier `m (ξ) x = Σ_k ε_k 1_{I_k} (ξ) x`, with values in `Y = L^p (Ω; X)`, is
bounded on the line; its dilates `m (ρ ·)`, for irrational `ρ > 1`, have the same norm and are
continuous at the integers, hence are transferred to `𝕋` by Proposition 5.7.1
(`HarmonicAnalysis.VectorValued.Transference`); and, if `ρ` is near `1`, `ρ j ∈ I_k` exactly when
`j ∈ Ĩ_k`, at the frequencies `j` of `f` ((5.61), (5.62); in (5.60) the intervals are half-open,
here they are open, as in Corollary 5.3.25). The signs are real. In the book all `k ∈ ℤ` are taken
at once; here the sums are finite. The left-hand inequality and the operator-valued statement (1) of
that theorem are not treated.

A shorter transference: `m (ρ ·)` is constant near each integer, so that a cut-off with compactly
supported Fourier transform and Lemma 5.7.3 suffice, without duality and Proposition 5.7.1; see the
module docstring of `HarmonicAnalysis.VectorValued.Transference`.

Also: the projections onto single frequencies are randomised bounded
(`eLpNormRad_singleFrequency_le`), by Jensen's inequality and the contraction principle.
-/

@[expose] public section

open MeasureTheory BanachProbability AddCircle
open scoped ENNReal FourierTransform SchwartzMap

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

open scoped Classical in
private theorem trigBlock_eq_sum (s : Set ℤ) (c : ℤ →₀ X) (t : UnitAddCircle) :
    trigBlock s c t = ∑ j ∈ c.support, if j ∈ s then fourier j t • c j else 0 := by
  rw [trigBlock, circPoly, Finsupp.sum_filter_index, Finsupp.support_filter, Finset.sum_filter]

/-! ### The dilation trick

HNVW I, pp. 465–466: for an irrational `ρ > 1` the functions `1_{I_k} (ρ ·)` are continuous at the
integers; if `ρ < 1 + 1 / N`, they agree with the indicators of `Ĩ_k` at the integers `j` with
`|j| ≤ N`. -/

private theorem mem_dyadicBlock_neg (m n : ℤ) : n ∈ dyadicBlock (-m) ↔ -n ∈ dyadicBlock m := by
  rcases lt_trichotomy m 0 with h | rfl | h
  · rw [dyadicBlock, dyadicBlock, ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), Int.natAbs_neg, Set.mem_Ico, Set.mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · simp [dyadicBlock]
  · rw [dyadicBlock, dyadicBlock, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), Int.natAbs_neg, Set.mem_Ico, Set.mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

private theorem mem_lineBlock_iff_of_pos {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ) (hρN : ρ * N < N + 1)
    {j : ℤ} (hj : |j| ≤ N) (k : ℕ) :
    ρ * j ∈ lineBlock ((k : ℤ) + 1) ↔ j ∈ dyadicBlock ((k : ℤ) + 1) := by
  have hblock : dyadicBlock ((k : ℤ) + 1) = Set.Ico (2 ^ k) (2 ^ (k + 1)) := by
    have h1 : ((k : ℤ) + 1).natAbs = k + 1 := by omega
    rw [dyadicBlock, ite_eq_right (by omega), ite_eq_left (by omega), h1, Nat.add_sub_cancel]
  rw [hblock, lineBlock_natCast_add_one, Set.mem_Ioo, Set.mem_Ico]
  rcases le_or_gt j 0 with hj0 | hj0
  · -- `ρ j ≤ 0`
    have hj0' : (j : ℝ) ≤ 0 := by exact_mod_cast hj0
    have h1 : ρ * j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hj0'
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have h3 : (0 : ℤ) < 2 ^ k := by positivity
    exact ⟨fun h => by linarith [h.1], fun h => by linarith [h.1]⟩
  · -- `j < ρ j < j + 1`
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast (le_abs_self j).trans hj
    have hj1 : (0 : ℝ) < j := by exact_mod_cast hj0
    have h1 : (j : ℝ) < ρ * j := lt_mul_of_one_lt_left hj1 hρ
    have h2 : ρ * j < j + 1 := by nlinarith
    constructor
    · rintro ⟨h3, h4⟩
      constructor
      · rw [← Int.lt_add_one_iff]
        have h5 : (2 : ℝ) ^ k < j + 1 := h3.trans h2
        exact_mod_cast h5
      · have h5 : (j : ℝ) < 2 ^ (k + 1) := h1.trans h4
        exact_mod_cast h5
    · rintro ⟨h3, h4⟩
      constructor
      · have h5 : (2 : ℝ) ^ k ≤ j := by exact_mod_cast h3
        exact h5.trans_lt h1
      · have h5 : (j : ℝ) + 1 ≤ 2 ^ (k + 1) := by exact_mod_cast h4
        exact h2.trans_le h5

/-- `ρ j ∈ I_k` if and only if `j ∈ Ĩ_k` (HNVW I, p. 465). -/
private theorem mem_lineBlock_iff {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ) (hρN : ρ * N < N + 1) {j : ℤ}
    (hj : |j| ≤ N) (k : ℤ) : ρ * j ∈ lineBlock k ↔ j ∈ dyadicBlock k := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    have h := mem_lineBlock_iff_of_pos hρ hρN (j := -j) (by rwa [abs_neg]) n
    rw [mem_lineBlock_neg, mem_dyadicBlock_neg, ← h]
    push_cast
    rw [mul_neg]
  · rw [lineBlock_zero, Set.mem_Ioo, ← abs_lt]
    simp only [dyadicBlock, ite_true, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hj0
      have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj0
      rw [abs_mul, abs_of_pos (by linarith)] at h
      nlinarith
    · rintro rfl
      simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    exact mem_lineBlock_iff_of_pos hρ hρN hj n

/-- The dilation `ρ` for a finite set `s` of frequencies (HNVW I, pp. 465–466): an irrational
`ρ > 1` with `ρ < 1 + 1 / N`, where `|j| ≤ N` for `j ∈ s`. -/
theorem exists_irrational_dilation (s : Finset ℤ) : ∃ (N : ℕ) (ρ : ℝ), Irrational ρ ∧ 1 < ρ ∧
    ρ * N < N + 1 ∧ ∀ j ∈ s, |j| ≤ N := by
  obtain ⟨N, hN, hs⟩ : ∃ N : ℕ, 1 ≤ N ∧ ∀ j ∈ s, |j| ≤ N := by
    refine ⟨s.sup Int.natAbs + 1, by omega, fun j hj => ?_⟩
    have h := Finset.le_sup (f := Int.natAbs) hj
    rw [Int.abs_eq_natAbs]
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨ρ, hρi, hρ1, hρN⟩ := exists_irrational_btwn (lt_add_of_pos_right (1 : ℝ)
    (one_div_pos.2 hN0))
  refine ⟨N, ρ, hρi, hρ1, ?_, hs⟩
  calc ρ * N < (1 + 1 / N) * N := by gcongr
    _ = N + 1 := by field_simp

/-- The indicators of the dilated intervals are continuous at the integers. -/
private theorem continuousAt_indicator_lineBlock {ρ : ℝ} (hρ : Irrational ρ) (k j : ℤ) :
    ContinuousAt (fun ξ => (lineBlock k).indicator (1 : ℝ → ℂ) (ρ * ξ)) j := by
  have hopen : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → ContinuousAt
      (fun ξ => (Set.Ioo (a : ℝ) b).indicator (1 : ℝ → ℂ) (ρ * ξ)) j := by
    intro a b ha hb
    have hne : ∀ n : ℤ, n ≠ 0 → ρ * j ≠ n := by
      intro n hn h
      rcases eq_or_ne j 0 with rfl | hj
      · refine hn ?_
        rw [Int.cast_zero, mul_zero] at h
        exact_mod_cast h.symm
      · exact (hρ.mul_intCast hj).ne_int n h
    have hloc : ∀ᶠ ξ in nhds (ρ * j), (Set.Ioo (a : ℝ) b).indicator (1 : ℝ → ℂ) ξ =
        (Set.Ioo (a : ℝ) b).indicator (1 : ℝ → ℂ) (ρ * j) := by
      by_cases hmem : ρ * j ∈ Set.Ioo (a : ℝ) b
      · filter_upwards [isOpen_Ioo.mem_nhds hmem] with ξ hξ
        rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hmem, Pi.one_apply, Pi.one_apply]
      · have hmem' : ρ * j ∈ (Set.Icc (a : ℝ) b)ᶜ := fun h =>
          hmem ⟨lt_of_le_of_ne h.1 (hne a ha).symm, lt_of_le_of_ne h.2 (hne b hb)⟩
        filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hmem'] with ξ hξ
        rw [Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem fun h => hξ (Set.Ioo_subset_Icc_self h)]
    have hcont : ContinuousAt (fun ξ : ℝ => ρ * ξ) j := by fun_prop
    have hev := hcont.eventually hloc
    exact continuousAt_const.congr (Filter.EventuallyEq.symm hev)
  unfold lineBlock
  split_ifs
  · simpa using hopen (-1) 1 (by norm_num) one_ne_zero
  · simpa using hopen (2 ^ (k.natAbs - 1)) (2 ^ k.natAbs) (by positivity) (by positivity)
  · simpa using hopen (-2 ^ k.natAbs) (-2 ^ (k.natAbs - 1)) (neg_ne_zero.2 (by positivity))
      (neg_ne_zero.2 (by positivity))

/-! ### Rademacher sums as a multiplier

HNVW I, p. 466: `Y = L^p (Ω; X)` and `m (ξ) x = Σ_k ε_k 1_{I_k} (ξ) x`, with `Ω = {±1}^n` (real
signs). Here `Y` is the space of the functions `{±1}^n → X` with the norm of `ℓ^p`; it is
`L^p (Ω; X)` up to the factor `2^{n/p}`. -/

/-- The space of the functions `{±1}^n → X` with the norm of `ℓ^p`. -/
private abbrev SignFun (X : Type*) (p : ℝ) (n : ℕ) : Type _ :=
  PiLp (ENNReal.ofReal p) fun _ : Fin n → Bool => X

section

variable {p : ℝ} {n : ℕ}

/-- `x ↦ ε_k ⊗ x`. -/
private noncomputable def signOp (p : ℝ) {n : ℕ} (k : Fin n) : X →L[ℂ] SignFun X p n :=
  (PiLp.continuousLinearEquiv (ENNReal.ofReal p) ℂ
    (fun _ : Fin n → Bool => X)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi fun ε => SignCube.coin (ε k) • ContinuousLinearMap.id ℂ X

private theorem sum_signOp_apply (f : Fin n → X) (ε : Fin n → Bool) :
    (∑ k, signOp p k (f k)) ε = ∑ k, SignCube.coin (ε k) • f k := by
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rfl

variable [Fact (1 ≤ ENNReal.ofReal p)]

omit [NormedSpace ℂ X] in
private theorem enorm_signFun_rpow (hp : 0 < p) (y : SignFun X p n) :
    ‖y‖ₑ ^ p = ∑ ε, ‖y ε‖ₑ ^ p := by
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ hp.le]
  rw [PiLp.nnnorm_eq_sum ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le, ← NNReal.rpow_mul,
    one_div_mul_cancel hp.ne', NNReal.rpow_one, ENNReal.ofNNReal_finsetSum]

/-- The norm of `Σ_k ε_k ⊗ f_k` in `L^p (μ; Y)`. -/
private theorem eLpNorm_sum_signOp (hp : 0 < p) {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : Fin n → α → X} (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNorm (fun x => ∑ k, signOp p k (f k x)) (ENNReal.ofReal p) μ =
      ((2 : ℝ≥0∞) ^ n) ^ (1 / p) * eLpNormRad f p μ := by
  have hm : AEStronglyMeasurable (fun x => ∑ k, signOp p k (f k x)) μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (signOp p k).continuous.comp_aestronglyMeasurable (hf k)
  have hs : ∀ ε : Fin n → Bool,
      AEStronglyMeasurable (fun x => ∑ k, SignCube.coin (ε k) • f k x) μ := fun ε =>
    Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hf k).const_smul _
  have h1 : eLpNorm (fun x => ∑ k, signOp p k (f k x)) (ENNReal.ofReal p) μ ^ p =
      (2 : ℝ≥0∞) ^ n * eLpNormRad f p μ ^ p := by
    rw [eLpNorm_ofReal_rpow_eq_lintegral hp hm, eLpNormRad_rpow hp hf, ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    simp only [enorm_signFun_rpow hp, sum_signOp_apply]
    rw [lintegral_finsetSum' _ fun ε _ => (hs ε).enorm.pow_const p]
    exact Finset.sum_congr rfl fun ε _ => (eLpNorm_ofReal_rpow_eq_lintegral hp (hs ε)).symm
  rw [← ENNReal.rpow_one (eLpNorm _ _ _), ← mul_one_div_cancel hp.ne', ENNReal.rpow_mul, h1,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- The multiplier `m (ξ) x = Σ_k ε_k 1_{I_{κ k}} (ξ) x`. -/
private noncomputable def signMultiplier (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] {n : ℕ} (κ : Fin n → ℤ) (ξ : ℝ) :
    X →L[ℂ] SignFun X p n :=
  ∑ k, (lineBlock (κ k)).indicator (1 : ℝ → ℂ) ξ • signOp p k

private theorem signMultiplier_apply (κ : Fin n → ℤ) (ξ : ℝ) (x : X) :
    signMultiplier X p κ ξ x =
      ∑ k, (lineBlock (κ k)).indicator (1 : ℝ → ℂ) ξ • signOp p k x := by
  rw [signMultiplier, sum_apply]
  rfl

private theorem norm_indicator_one_le (s : Set ℝ) (ξ : ℝ) : ‖s.indicator (1 : ℝ → ℂ) ξ‖ ≤ 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> simp

private theorem norm_signMultiplier_le (κ : Fin n → ℤ) (ξ : ℝ) :
    ‖signMultiplier X p κ ξ‖ ≤ ∑ k, ‖(signOp p k : X →L[ℂ] SignFun X p n)‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_indicator_one_le _ _)

private theorem signMultiplier_apply_eq_sum (κ : Fin n → ℤ) (G : ℝ → X) (ξ : ℝ) :
    signMultiplier X p κ ξ (G ξ) = ∑ k, signOp p k ((lineBlock (κ k)).indicator G ξ) := by
  classical
  rw [signMultiplier_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> simp

/-- `T_m f = Σ_k ε_k ⊗ Δ_{I_{κ k}} f`. -/
private theorem fourierInv_signMultiplier [CompleteSpace X] (κ : Fin n → ℤ) {G : ℝ → X}
    (hG : Integrable G) (x : ℝ) : 𝓕⁻ (fun ξ => signMultiplier X p κ ξ (G ξ)) x =
      ∑ k, signOp p k (𝓕⁻ ((lineBlock (κ k)).indicator G) x) := by
  have hi : ∀ k, Integrable fun v => expChar v x • (lineBlock (κ k)).indicator G v := fun k =>
    integrable_expChar_smul (hG.indicator (measurableSet_lineBlock _)) x
  have hi' : ∀ k, Integrable fun v =>
      expChar v x • signOp p k ((lineBlock (κ k)).indicator G v) := fun k => by
    simpa only [map_smul] using (signOp p k : X →L[ℂ] SignFun X p n).integrable_comp (hi k)
  simp only [fourierInv_eq_expChar, signMultiplier_apply_eq_sum, Finset.smul_sum]
  rw [integral_finsetSum _ fun k _ => hi' k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← ContinuousLinearMap.integral_comp_comm _ (hi k)]
  simp only [map_smul]

/-- `m (ρ ·) x` is measurable. -/
private theorem aestronglyMeasurable_signMultiplier (κ : Fin n → ℤ) (ρ : ℝ) (x : X) :
    AEStronglyMeasurable (fun ξ => signMultiplier X p κ (ρ * ξ) x) volume := by
  simp only [signMultiplier_apply]
  exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
    ((measurable_one.indicator (measurableSet_lineBlock (κ k))).comp
      (measurable_const_mul ρ)).aestronglyMeasurable.smul_const _

/-- `m (ρ ·) x` is continuous at the integers. -/
private theorem continuousAt_signMultiplier (κ : Fin n → ℤ) {ρ : ℝ} (hρ : Irrational ρ) (j : ℤ)
    (x : X) : ContinuousAt (fun ξ => signMultiplier X p κ (ρ * ξ) x) j := by
  simp only [signMultiplier_apply]
  exact tendsto_finsetSum _ fun k _ =>
    (continuousAt_indicator_lineBlock hρ (κ k) j).tendsto.smul_const _

/-- The bound of the multiplier `m` on the line, from the inequality for the intervals. -/
private theorem eLpNorm_fourierInv_signMultiplier_le [CompleteSpace X] (hp : 0 < p) (κ : Fin n → ℤ)
    {C : ℝ≥0∞} {G : ℝ → X} (hG : Integrable G)
    (h : eLpNormRad (fun k => 𝓕⁻ ((lineBlock (κ k)).indicator G)) p volume ≤
      C * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => signMultiplier X p κ ξ (G ξ)) (ENNReal.ofReal p) volume ≤
      ((2 : ℝ≥0∞) ^ n) ^ (1 / p) * C * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  rw [funext (fourierInv_signMultiplier κ hG), eLpNorm_sum_signOp hp fun k =>
    (continuous_fourierInv_of_integrable (hG.indicator
      (measurableSet_lineBlock _))).aestronglyMeasurable, mul_assoc]
  gcongr

/-- `T̃_{m (ρ ·)} f = Σ_k ε_k ⊗ Δ̃_{κ k} f`, as `m (ρ j) = Σ_k ε_k 1_{Ĩ_k} (j)` at the
frequencies `j` of `f`. -/
private theorem sum_signMultiplier (κ : Fin n → ℤ) {ρ : ℝ} {c : ℤ →₀ X}
    (hρ : ∀ j ∈ c.support, ∀ k, ρ * j ∈ lineBlock k ↔ j ∈ dyadicBlock k) (t : UnitAddCircle) :
    (c.sum fun j y => fourier j t • signMultiplier X p κ (ρ * j) y) =
      ∑ k, signOp p k (trigBlock (dyadicBlock (κ k)) c t) := by
  classical
  simp only [trigBlock_eq_sum, map_sum]
  rw [Finset.sum_comm, Finsupp.sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [signMultiplier_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Set.indicator_apply]
  simp only [hρ j hj]
  split_ifs
  · rw [Pi.one_apply, one_smul, map_smul]
  · rw [zero_smul, smul_zero, map_zero]

end

/-- **Transference of Littlewood–Paley inequalities** (HNVW I, proof of Theorem 5.7.10, (5.62)): an
inequality on the line for the intervals `I_{κ k}` gives the inequality on `𝕋` for the blocks
`Ĩ_{κ k}`, with the same constant. -/
private theorem eLpNormRad_dyadicBlock_le_of_line [CompleteSpace X] {p : ℝ} (hp : 1 < p) {n : ℕ}
    (κ : Fin n → ℤ) {C : ℝ≥0∞} (hline : ∀ G : 𝓢(ℝ, X),
      eLpNormRad (fun k => 𝓕⁻ ((lineBlock (κ k)).indicator G)) p volume ≤
        C * eLpNorm (𝓕⁻ (G : ℝ → X)) (ENNReal.ofReal p) volume) (c : ℤ →₀ X) :
    eLpNormRad (fun k => trigBlock (dyadicBlock (κ k)) c) p haarAddCircle ≤
      C * eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  have hp0 : 0 < p := by linarith
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp.le⟩
  -- Proposition 5.7.1 for the dilate `m (ρ ·)`, with (5.61)
  obtain ⟨N, ρ, hρi, hρ1, hρN, hN⟩ := exists_irrational_dilation c.support
  have h := eLpNorm_circPoly_multiplier_le hp (m := fun ξ => signMultiplier X p κ (ρ * ξ))
    (fun ξ => norm_signMultiplier_le κ _) (aestronglyMeasurable_signMultiplier κ ρ)
    (continuousAt_signMultiplier κ hρi)
    (eLpNorm_fourierInv_multiplier_dilate_le hp0 (fun G =>
      eLpNorm_fourierInv_signMultiplier_le hp0 κ G.integrable (hline G)) (by linarith)) c
  rw [funext (sum_signMultiplier κ fun j hj => mem_lineBlock_iff hρ1 hρN (hN j hj)),
    eLpNorm_sum_signOp hp0 (f := fun k => trigBlock (dyadicBlock (κ k)) c)
    fun k => (continuous_circPoly _).aestronglyMeasurable, mul_assoc,
    ENNReal.mul_le_mul_iff_right] at h
  · exact h
  · exact (ENNReal.rpow_pos (by positivity) (by simp)).ne'
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)

/-- The inverse Fourier transforms of Schwartz functions are in `L^r (ℝ; X)`. -/
theorem memLp_fourierInv (G : 𝓢(ℝ, X)) (r : ℝ≥0∞) : MemLp (𝓕⁻ (G : ℝ → X)) r volume := by
  rw [← SchwartzMap.fourierInv_coe]
  exact (𝓕⁻ G : 𝓢(ℝ, X)).memLp r volume

variable [CompleteSpace X]

/-- The Littlewood–Paley inequality on `𝕋` for the blocks `Ĩ_{k+1} = [2^k, 2^{k+1})`, `0 ≤ k < K`
(HNVW I, Theorem 5.7.10 (2), right-hand inequality, for these blocks), from the inequality on the
positive half-line. -/
theorem eLpNormRad_dyadicBlock_succ_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun k : Fin K => trigBlock (dyadicBlock ((k : ℕ) + 1)) c) p haarAddCircle ≤
      littlewoodPaleyBound β * eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  refine eLpNormRad_dyadicBlock_le_of_line hp (fun k : Fin K => ((k : ℕ) : ℤ) + 1) (fun G => ?_) c
  simp only [lineBlock_natCast_add_one]
  exact eLpNormRad_fourierInv_indicator_le hp hβ G.integrable (memLp_fourierInv G _) K

/-- **The Littlewood–Paley inequality on the circle** (HNVW I, Theorem 5.7.10 (2), right-hand
inequality): for a complex UMD space `X`, `1 < p < ∞` and a trigonometric polynomial
`f = Σ c_n e_n`, `‖Σ_{|k| ≤ K} ε_k Δ̃_k f‖_{L^p (Ω × 𝕋; X)} ≤ C_β ‖f‖_{L^p (𝕋; X)}`, with the
constant of Corollary 5.3.25 (`eLpNormRad_lineBlock_le`). -/
theorem eLpNormRad_dyadicBlock_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun k : Fin (2 * K + 1) => trigBlock (dyadicBlock ((k : ℕ) - K)) c) p
        haarAddCircle ≤
      (2 * littlewoodPaleyBound β + hilbertBound β) *
        eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle :=
  eLpNormRad_dyadicBlock_le_of_line hp (fun k : Fin (2 * K + 1) => ((k : ℕ) : ℤ) - K)
    (fun G => eLpNormRad_lineBlock_le hp hβ G.integrable (memLp_fourierInv G _) K) c

/-! ### Single frequencies -/

omit [NormedSpace ℂ X] [CompleteSpace X] in
/-- Jensen's inequality on the probability space `𝕋`. -/
private theorem eLpNorm_const_integral_le [NormedSpace ℝ X] {p : ℝ} (hp : 1 ≤ p)
    {g : UnitAddCircle → X} (hg : Continuous g) :
    eLpNorm (fun _ : UnitAddCircle => ∫ t, g t ∂haarAddCircle) (ENNReal.ofReal p) haarAddCircle ≤
      eLpNorm g (ENNReal.ofReal p) haarAddCircle := by
  rw [eLpNorm_const' _ (by simpa using by linarith) ENNReal.ofReal_ne_top, measure_univ,
    ENNReal.one_rpow, mul_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
  exact eLpNorm_le_eLpNorm_of_exponent_le (by simpa using hp)

/-- The projections onto single frequencies are randomised bounded: for trigonometric polynomials
`f_k = Σ_n c_k (n) e_n` and any `n_k ∈ ℤ`, `‖Σ ε_k c_k (n_k) e_{n_k}‖ ≤ 4 ‖Σ ε_k f_k‖`. The proof is
by Jensen's inequality, as `c_k (n_k)` is the mean of `e_{−n_k} f_k`, and two applications of the
contraction principle with the factor `2` (real signs). -/
theorem eLpNormRad_singleFrequency_le {p : ℝ} (hp : 1 ≤ p) {K : ℕ} (c : Fin K → ℤ →₀ X)
    (n : Fin K → ℤ) :
    eLpNormRad (fun k (t : UnitAddCircle) => fourier (n k) t • c k (n k)) p haarAddCircle ≤
      4 * eLpNormRad (fun k => circPoly (c k)) p haarAddCircle := by
  have hp0 : 0 < p := by linarith
  have hcont : ∀ k, Continuous fun t : UnitAddCircle => fourier (-n k) t • circPoly (c k) t :=
    fun k => (map_continuous (fourier (-n k))).smul (continuous_circPoly (c k))
  -- the contraction principle
  have h1 : eLpNormRad (fun k (t : UnitAddCircle) => fourier (n k) t • c k (n k)) p haarAddCircle ≤
      2 * eLpNormRad (fun k (_ : UnitAddCircle) => c k (n k)) p haarAddCircle :=
    eLpNormRad_smul_le hp (c := fun k t => fourier (n k) t)
      (f := fun k (_ : UnitAddCircle) => c k (n k)) (fun k t => (norm_fourier_apply_eq_one _ _).le)
      (fun k => (map_continuous (fourier (n k))).aestronglyMeasurable)
      fun k => aestronglyMeasurable_const
  -- Jensen's inequality, for each choice of signs
  have h2 : eLpNormRad (fun k (_ : UnitAddCircle) => c k (n k)) p haarAddCircle ≤
      1 * eLpNormRad (fun k (t : UnitAddCircle) => fourier (-n k) t • circPoly (c k) t) p
        haarAddCircle := by
    refine eLpNormRad_le_of_forall hp0 (fun k => aestronglyMeasurable_const)
      (fun k => (hcont k).aestronglyMeasurable) fun ε => ?_
    have hsum : Continuous fun t : UnitAddCircle =>
        ∑ k, SignCube.coin (ε k) • fourier (-n k) t • circPoly (c k) t :=
      continuous_finsetSum _ fun k _ => (hcont k).const_smul _
    have h3 : ∑ k, SignCube.coin (ε k) • c k (n k) =
        ∫ t, ∑ k, SignCube.coin (ε k) • fourier (-n k) t • circPoly (c k) t ∂haarAddCircle := by
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_smul, integral_fourier_smul_circPoly]
      · exact fun k _ => integrable_haar_of_continuous ((hcont k).const_smul _)
    rw [one_mul, h3]
    exact eLpNorm_const_integral_le hp hsum
  -- the contraction principle
  have h4 : eLpNormRad (fun k (t : UnitAddCircle) => fourier (-n k) t • circPoly (c k) t) p
      haarAddCircle ≤ 2 * eLpNormRad (fun k => circPoly (c k)) p haarAddCircle :=
    eLpNormRad_smul_le hp (c := fun k t => fourier (-n k) t) (f := fun k => circPoly (c k))
      (fun k t => (norm_fourier_apply_eq_one _ _).le)
      (fun k => (map_continuous (fourier (-n k))).aestronglyMeasurable)
      fun k => (continuous_circPoly _).aestronglyMeasurable
  calc _ ≤ 2 * (1 * (2 * eLpNormRad (fun k => circPoly (c k)) p haarAddCircle)) := by
        refine h1.trans ?_
        gcongr
        exact h2.trans (by gcongr)
    _ = 4 * eLpNormRad (fun k => circPoly (c k)) p haarAddCircle := by ring

end HarmonicAnalysis
