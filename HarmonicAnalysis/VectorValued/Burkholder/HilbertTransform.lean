/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Burkholder.ConjugateFunction
public import HarmonicAnalysis.VectorValued.HilbertTransform.Fourier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Hilbert transform on UMD spaces, after Burkholder

D. L. Burkholder, *A geometric condition that implies the existence of certain singular integrals of
Banach-space-valued functions* (1983): for a function `f` on `ℝ` with values in a Banach space `X`,

`H_ε f (x) = π⁻¹ ∫_{|t| > ε} f (x − t) / t dt`  (`hilbertTrunc`; (2), p. 271).

Lemma 4, p. 283 (`eLpNorm_hilbertTrunc_le`): if `X` has a `UMD_p` constant `β`, `1 < p < ∞`, then
`‖H_ε f‖_p ≤ (2 β² + 1) ‖f‖_p` (34) for `f ∈ L^p (ℝ; X)` and `ε > 0`, with the constant
`hilbertBound β` of the inequality (33) for the truncated conjugate function `f̃_ε` on the circle.

The whole proof in the paper is: "This follows from (33) just as it does in the real case; see [14]
or [18]" (M. Riesz, *Sur les fonctions conjuguées*, Math. Z. 27 (1928), 218–244; A. Zygmund,
*Trigonometric Series*, 2nd ed., 1959). The classical argument is written out here. Let first `f`
vanish off `[−A, A]`, and for `R > ε` let `g_R (θ) = f (Rθ)`, `−π < θ ≤ π`, be extended
periodically (`periodize`).

* For `|x| + A < πR` the substitution `t = s / R` gives (`truncatedConj_periodize`)
  `(g_R)~_{ε/R} (x / R) = π⁻¹ ∫_{ε < |s| < πR} (2R)⁻¹ cot (s / (2R)) f (x − s) ds`.
* As `(2R)⁻¹ cot (s / (2R)) → s⁻¹`, with the bound `|s|⁻¹` for `|s| < πR`, this tends to `H_ε f (x)`
  as `R → ∞` (`tendsto_truncatedConj_periodize`).
* By (33), the norm of `x ↦ (g_R)~_{ε/R} (x / R)` in `L^p ((−πR, πR])` is at most
  `(2 β² + 1) ‖f‖_p` (`eLpNorm_truncatedConj_periodize_le`): the dilation by `R` multiplies both
  sides of (33) by the same power of `R`.
* Fatou's lemma, as `R → ∞`, gives (34) for `f` (`eLpNorm_hilbertTrunc_le_of_support`).
* For `f ∈ L^p`, `1_{[−A, A]} f` is as above, `H_ε (1_{[−A, A]} f) → H_ε f` pointwise as `A → ∞`,
  since `t ↦ f (x − t) / t` is integrable over `|t| > ε` by Hölder's inequality, and Fatou's lemma
  gives (34).

The paper goes on to the limits `lim_{ε → 0} T_ε f` (Theorem 2, p. 284), by the maximal function
`T* f`; this is not carried out here. Instead, for `f = 𝓕⁻ G ∈ L^p` with `G ∈ L¹`, where `X` is a
complex space, `H_ε f (x) → 𝓕⁻ (−i sgn · G) (x)` for every `x` (`tendsto_hilbertTrunc_fourierInv`,
from the computation of the symbols in `HilbertTransform.Fourier`). By Fatou's lemma,

`‖𝓕⁻ (−i sgn · G)‖_p = ‖𝓕⁻ (sgn · G)‖_p ≤ (2 β² + 1) ‖𝓕⁻ G‖_p`
(`eLpNorm_fourierInv_neg_I_sign_le`, `eLpNorm_fourierInv_sign_le`).
-/

@[expose] public section

open MeasureTheory BanachProbability AddCircle Filter Topology
open scoped ENNReal Real FourierTransform

namespace HarmonicAnalysis

attribute [local instance] fact_zero_lt_two_pi

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Burkholder (1983), (2): `H_ε f (x) = π⁻¹ ∫_{|t| > ε} f (x − t) / t dt`. -/
noncomputable def hilbertTrunc (ε : ℝ) (f : ℝ → X) (x : ℝ) : X :=
  π⁻¹ • ∫ t in {t : ℝ | ε < |t|}, t⁻¹ • f (x - t)

/-! ### The kernels -/

/-- The kernel `(2R)⁻¹ cot (s / (2R))` of the dilated circle, with the factor `s⁻¹` taken out. -/
private theorem inv_mul_cot {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    (2 * R)⁻¹ * Real.cot (s / (2 * R)) =
      Real.cos (s / (2 * R)) / Real.sinc (s / (2 * R)) * s⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Real.cot_eq_cos_div_sin]
  · rw [Real.cot_eq_cos_div_sin, Real.sinc_of_ne_zero (by positivity)]
    field_simp

/-- `|(2R)⁻¹ cot (s / (2R))| ≤ |s|⁻¹` for `|s| < πR`, as `y cos y ≤ sin y` for `0 ≤ y < π / 2`. -/
private theorem abs_inv_mul_cot_le {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : |s| < π * R) :
    |(2 * R)⁻¹ * Real.cot (s / (2 * R))| ≤ |s|⁻¹ := by
  have hy : |s / (2 * R)| < π / 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * R), div_lt_iff₀ (by positivity)]
    linarith
  have hcos : 0 ≤ Real.cos (s / (2 * R)) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (abs_lt.1 hy).1.le (abs_lt.1 hy).2.le
  rw [inv_mul_cot hR.ne', abs_mul, abs_inv]
  refine mul_le_of_le_one_left (by positivity) ?_
  rw [abs_of_nonneg (div_nonneg hcos (hcos.trans (Real.cos_le_sinc hy)))]
  exact div_le_one_of_le₀ (Real.cos_le_sinc hy) (hcos.trans (Real.cos_le_sinc hy))

/-- `(2R)⁻¹ cot (s / (2R)) → s⁻¹` as `R → ∞`. -/
private theorem tendsto_inv_mul_cot (s : ℝ) :
    Tendsto (fun n : ℕ => (2 * (n : ℝ))⁻¹ * Real.cot (s / (2 * n))) atTop (𝓝 s⁻¹) := by
  have hy : Tendsto (fun n : ℕ => s / (2 * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop two_pos)
  have h : Tendsto (fun n : ℕ => Real.cos (s / (2 * (n : ℝ))) / Real.sinc (s / (2 * (n : ℝ))) * s⁻¹)
      atTop (𝓝 (Real.cos 0 / Real.sinc 0 * s⁻¹)) :=
    (((Real.continuous_cos.tendsto 0).comp hy).div ((Real.continuous_sinc.tendsto 0).comp hy)
      (by simp)).mul_const _
  rw [Real.cos_zero, Real.sinc_zero, div_one, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (inv_mul_cot (by positivity) s).symm

/-- `s ↦ (2R)⁻¹ cot (s / (2R))` is measurable. -/
private theorem measurable_inv_mul_cot (R : ℝ) :
    Measurable fun s : ℝ => (2 * R)⁻¹ * Real.cot (s / (2 * R)) := by
  simp_rw [Real.cot_eq_cos_div_sin]
  fun_prop

/-! ### Periodization -/

/-- The periodic function `g_R` with `g_R (θ) = f (Rθ)` for `−π < θ ≤ π`. -/
private noncomputable def periodize (R : ℝ) (f : ℝ → X) : AddCircle (2 * π) → X :=
  AddCircle.liftIoc (2 * π) (-π) fun θ => f (R * θ)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- `g_R (y / R) = f y` for `−πR < y ≤ πR`. -/
private theorem periodize_coe_div {R : ℝ} (hR : 0 < R) (f : ℝ → X) {y : ℝ} (h1 : -(π * R) < y)
    (h2 : y ≤ π * R) : periodize R f ((y / R : ℝ) : AddCircle (2 * π)) = f y := by
  rw [periodize, AddCircle.liftIoc_coe_apply, mul_div_cancel₀ _ hR.ne']
  rw [Set.mem_Ioc, lt_div_iff₀ hR, div_le_iff₀ hR]
  constructor <;> linarith

omit [NormedSpace ℝ X] in
/-- If `f` vanishes off `[−A, A]`, then `g_R (y / R) = f y` for `|y| < 2πR − A`: where `y / R` is
not in `(−π, π]`, both sides vanish. -/
private theorem periodize_coe_div_of_abs_lt {R : ℝ} (hR : 0 < R) {f : ℝ → X} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ y, A < |y| → f y = 0) (hAR : A < π * R) {y : ℝ} (hy : |y| + A < 2 * (π * R)) :
    periodize R f ((y / R : ℝ) : AddCircle (2 * π)) = f y := by
  obtain ⟨hy1, hy2⟩ := abs_lt.1 (lt_sub_iff_add_lt.2 hy)
  rcases lt_or_ge (-(π * R)) y with h1 | h1
  · rcases le_or_gt y (π * R) with h2 | h2
    · exact periodize_coe_div hR f h1 h2
    · rw [show y / R = (y - 2 * (π * R)) / R + 2 * π by field_simp; ring, AddCircle.coe_add_period,
        periodize_coe_div hR f (by linarith) (by linarith), hA _ (by rw [abs_of_neg] <;> linarith),
        hA _ ((hAR.trans h2).trans_le (le_abs_self y))]
  · rw [← AddCircle.coe_add_period, show y / R + 2 * π = (y + 2 * (π * R)) / R by field_simp,
      periodize_coe_div hR f (by linarith) (by linarith), hA _ (by rw [abs_of_pos] <;> linarith),
      hA _ (by rw [abs_of_neg] <;> linarith)]

/-- `{ε < |s| < b}` is measurable. -/
private theorem measurableSet_annulus (ε b : ℝ) : MeasurableSet {s : ℝ | ε < |s| ∧ |s| < b} :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- `{ε < |s|}` is measurable. -/
private theorem measurableSet_lt_abs (ε : ℝ) : MeasurableSet {s : ℝ | ε < |s|} :=
  measurableSet_lt measurable_const measurable_norm

/-- For `f` that vanishes off `[−A, A]` and `|x| + A < πR`, the substitution `t = s / R` gives
`(g_R)~_{ε/R} (x / R) = π⁻¹ ∫_{ε < |s| < πR} (2R)⁻¹ cot (s / (2R)) f (x − s) ds`. -/
private theorem truncatedConj_periodize {f : ℝ → X} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ y, A < |y| → f y = 0) {R : ℝ} (hR : 0 < R) (ε : ℝ) {x : ℝ} (hx : |x| + A < π * R) :
    truncatedConj (ε / R) (periodize R f) ((x / R : ℝ) : AddCircle (2 * π)) =
      π⁻¹ • ∫ s, {s : ℝ | ε < |s| ∧ |s| < π * R}.indicator
        (fun s => ((2 * R)⁻¹ * Real.cot (s / (2 * R))) • f (x - s)) s := by
  have h : ∀ s : ℝ, {t : ℝ | ε / R < |t| ∧ |t| < π}.indicator (fun t => Real.cot (t / 2) •
      periodize R f ((x / R : ℝ) - (t : ℝ) : AddCircle (2 * π))) (s / R) =
      (2 * R) • {s : ℝ | ε < |s| ∧ |s| < π * R}.indicator
        (fun s => ((2 * R)⁻¹ * Real.cot (s / (2 * R))) • f (x - s)) s := by
    intro s
    have hmem : s / R ∈ {t : ℝ | ε / R < |t| ∧ |t| < π} ↔
        s ∈ {s : ℝ | ε < |s| ∧ |s| < π * R} := by
      simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hR, div_lt_iff₀ hR,
        div_mul_cancel₀ _ hR.ne']
    by_cases hs : s ∈ {s : ℝ | ε < |s| ∧ |s| < π * R}
    · have hxs := abs_sub x s
      have hs2 := hs.2
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hmem.2 hs), ← AddCircle.coe_sub,
        ← sub_div, periodize_coe_div_of_abs_lt hR hA0 hA (by linarith [abs_nonneg x])
          (by linarith), smul_smul, mul_inv_cancel_left₀ (by positivity), div_div, mul_comm R 2]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (mt hmem.1 hs), smul_zero]
  rw [truncatedConj, ← integral_indicator (measurableSet_annulus _ _)]
  have hsub := Measure.integral_comp_div ({t : ℝ | ε / R < |t| ∧ |t| < π}.indicator fun t =>
    Real.cot (t / 2) • periodize R f ((x / R : ℝ) - (t : ℝ) : AddCircle (2 * π))) R
  rw [abs_of_pos hR] at hsub
  rw [← inv_smul_smul₀ hR.ne' (∫ t, _), ← hsub]
  simp_rw [h]
  rw [integral_smul, smul_smul, smul_smul]
  congr 1
  field_simp

/-- For `f ∈ L¹` that vanishes off `[−A, A]`, and every `x`, `(g_R)~_{ε/R} (x / R) → H_ε f (x)` as
`R = n → ∞`, by dominated convergence: the integrands are bounded by `ε⁻¹ ‖f (x − s)‖`. -/
private theorem tendsto_truncatedConj_periodize {f : ℝ → X} (hf : Integrable f) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ y, A < |y| → f y = 0) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Tendsto (fun n : ℕ => truncatedConj (ε / n) (periodize n f)
      ((x / n : ℝ) : AddCircle (2 * π))) atTop (𝓝 (hilbertTrunc ε f x)) := by
  have hlarge : ∀ B : ℝ, ∀ᶠ n : ℕ in atTop, B < π * n := fun B =>
    (tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos).eventually_gt_atTop B
  have hlim : Tendsto (fun n : ℕ => ∫ s, {s : ℝ | ε < |s| ∧ |s| < π * n}.indicator
      (fun s => ((2 * (n : ℝ))⁻¹ * Real.cot (s / (2 * n))) • f (x - s)) s) atTop
      (𝓝 (∫ s, {s : ℝ | ε < |s|}.indicator (fun s => s⁻¹ • f (x - s)) s)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => ε⁻¹ * ‖f (x - s)‖) ?_ ?_
      ((hf.comp_sub_left x).norm.const_mul _) (ae_of_all _ fun s => ?_)
    · exact Eventually.of_forall fun n => ((measurable_inv_mul_cot n).aestronglyMeasurable.smul
        (hf.comp_sub_left x).aestronglyMeasurable).indicator (measurableSet_annulus _ _)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      refine ae_of_all _ fun s => ?_
      by_cases hs : s ∈ {s : ℝ | ε < |s| ∧ |s| < π * n}
      · rw [Set.indicator_of_mem hs, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right ((abs_inv_mul_cot_le (by positivity) hs.2).trans
          (inv_anti₀ hε hs.1.le)) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hs, norm_zero]
        positivity
    · by_cases hs : ε < |s|
      · rw [Set.indicator_of_mem (by exact hs)]
        refine ((tendsto_inv_mul_cot s).smul_const (f (x - s))).congr' ?_
        filter_upwards [hlarge |s|] with n hn
        rw [Set.indicator_of_mem (show s ∈ {s : ℝ | ε < |s| ∧ |s| < π * n} from ⟨hs, hn⟩)]
      · rw [Set.indicator_of_notMem (by exact hs)]
        refine tendsto_const_nhds.congr fun n => ?_
        rw [Set.indicator_of_notMem (fun h : s ∈ {s : ℝ | ε < |s| ∧ |s| < π * n} => hs h.1)]
  rw [integral_indicator (measurableSet_lt_abs ε)] at hlim
  refine (hlim.const_smul π⁻¹).congr' ?_
  filter_upwards [hlarge (|x| + A), eventually_gt_atTop 0] with n hn hn0
  exact (truncatedConj_periodize hA0 hA (by positivity) ε hn).symm

/-! ### Measurability -/

omit [NormedSpace ℝ X] in
/-- `g_R` is strongly measurable, if `f` is. -/
private theorem stronglyMeasurable_periodize {f : ℝ → X} (hf : StronglyMeasurable f) (R : ℝ) :
    StronglyMeasurable (periodize R f) :=
  (hf.comp_measurable (measurable_const_mul R)).comp_measurable
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (2 * π) (-π)).measurable)

/-- `H_ε f` is strongly measurable, if `f` is. -/
private theorem stronglyMeasurable_hilbertTrunc {f : ℝ → X} (hf : StronglyMeasurable f) (ε : ℝ) :
    StronglyMeasurable (hilbertTrunc ε f) := by
  have h : StronglyMeasurable (Function.uncurry fun x t : ℝ => t⁻¹ • f (x - t)) :=
    measurable_snd.inv.stronglyMeasurable.smul
      (hf.comp_measurable (measurable_fst.sub measurable_snd))
  exact h.integral_prod_right.const_smul _

/-- `H_ε f` depends only on the class of `f`. -/
private theorem hilbertTrunc_congr_ae {f g : ℝ → X} (h : f =ᵐ[volume] g) (ε : ℝ) :
    hilbertTrunc ε f = hilbertTrunc ε g := by
  funext x
  have hx : (fun t => f (x - t)) =ᵐ[volume] fun t => g (x - t) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae_eq_comp h
  exact congrArg (π⁻¹ • ·) (integral_congr_ae ((ae_restrict_of_ae hx).mono fun t ht =>
    congrArg (t⁻¹ • ·) ht))

/-! ### The norms of the periodized functions -/

omit [NormedSpace ℝ X] in
/-- The change of variables `y = x / R` in the `L^p` norm. -/
private theorem eLpNorm_comp_div {p : ℝ≥0∞} (hp : p ≠ ⊤) {g : ℝ → X}
    (hg : StronglyMeasurable g) {R : ℝ} (hR : 0 < R) :
    eLpNorm (fun x => g (x / R)) p volume =
      ENNReal.ofReal R ^ (1 / p).toReal * eLpNorm g p volume := by
  have hmap := Real.map_volume_mul_left (inv_ne_zero hR.ne')
  rw [inv_inv, abs_of_pos hR] at hmap
  have h := eLpNorm_map_measure (p := p) (μ := volume) (f := fun x : ℝ => R⁻¹ * x) (g := g)
    hg.aestronglyMeasurable (measurable_const_mul R⁻¹).aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_top hp _ _ hg.aestronglyMeasurable, smul_eq_mul] at h
  rw [h]
  congr 1 with x
  simp [div_eq_inv_mul]

omit [NormedSpace ℝ X] in
/-- The `L^p` norm over the circle, with the measure `dθ`, as a norm over `(−π, π]`. -/
private theorem eLpNorm_indicator_comp_coe {p : ℝ≥0∞} {g : AddCircle (2 * π) → X}
    (hg : StronglyMeasurable g) :
    eLpNorm ((Set.Ioc (-π) π).indicator fun θ : ℝ => g θ) p volume = eLpNorm g p volume := by
  have h := eLpNorm_comp_measurePreserving (p := p) (g := g) hg.aestronglyMeasurable
    (AddCircle.measurePreserving_mk (2 * π) (-π))
  rw [show -π + 2 * π = π by ring] at h
  rw [← h, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet]
  rfl

omit [NormedSpace ℝ X] in
/-- `‖h (x / R)‖_{L^p ((−πR, πR])} = R^{1/p} ‖h‖_p` for a function `h` on the circle. -/
private theorem eLpNorm_indicator_comp_coe_div {p : ℝ≥0∞} (hp : p ≠ ⊤) {h : AddCircle (2 * π) → X}
    (hh : StronglyMeasurable h) {R : ℝ} (hR : 0 < R) :
    eLpNorm (fun x : ℝ => (Set.Ioc (-π) π).indicator (fun θ : ℝ => h θ) (x / R)) p volume =
      ENNReal.ofReal R ^ (1 / p).toReal * eLpNorm h p volume := by
  rw [eLpNorm_comp_div (g := (Set.Ioc (-π) π).indicator fun θ : ℝ => h θ) hp
    ((hh.comp_measurable AddCircle.measurable_mk').indicator measurableSet_Ioc) hR,
    eLpNorm_indicator_comp_coe hh]

omit [NormedSpace ℝ X] in
/-- `R^{1/p} ‖g_R‖_p ≤ ‖f‖_p`. -/
private theorem eLpNorm_periodize_le {p : ℝ≥0∞} (hp : p ≠ ⊤) {f : ℝ → X}
    (hf : StronglyMeasurable f) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal R ^ (1 / p).toReal * eLpNorm (periodize R f) p volume ≤
      eLpNorm f p volume := by
  have hm := stronglyMeasurable_periodize hf R
  rw [← eLpNorm_indicator_comp_coe_div hp hm hR]
  refine eLpNorm_mono ?_ fun x => ?_
  · exact (((hm.comp_measurable AddCircle.measurable_mk').indicator
      measurableSet_Ioc).comp_measurable (measurable_div_const R)).aestronglyMeasurable
  · by_cases hx : x / R ∈ Set.Ioc (-π) π
    · rw [Set.indicator_of_mem hx, periodize_coe_div hR f]
      · have := (lt_div_iff₀ hR).1 hx.1
        linarith
      · exact (div_le_iff₀ hR).1 hx.2
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact norm_nonneg _

/-- (33), with the measure `dθ` on the circle. -/
private theorem eLpNorm_truncatedConj_volume_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {f : AddCircle (2 * π) → X}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    eLpNorm (truncatedConj ε f) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hT : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  have hf' : MemLp f (ENNReal.ofReal p) haarAddCircle := by
    have h := hf.smul_measure (c := (ENNReal.ofReal (2 * π))⁻¹) (ENNReal.inv_ne_top.2 hT)
    rwa [AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
      ENNReal.inv_mul_cancel hT ENNReal.ofReal_ne_top, one_smul] at h
  rw [AddCircle.volume_eq_smul_haarAddCircle,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 ENNReal.ofReal_ne_top,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 ENNReal.ofReal_ne_top, smul_eq_mul, smul_eq_mul,
    mul_left_comm]
  gcongr
  exact eLpNorm_truncatedConj_le hp hβ hf' hε0 hε1

/-- From (33): for `ε < R`, `‖(g_R)~_{ε/R} (x / R)‖_{L^p ((−πR, πR])} ≤ (2 β² + 1) ‖f‖_p`. -/
private theorem eLpNorm_truncatedConj_periodize_le [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {f : ℝ → X} (hfm : StronglyMeasurable f)
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    eLpNorm (fun x : ℝ => (Set.Ioc (-π) π).indicator
      (fun θ : ℝ => truncatedConj (ε / R) (periodize R f) θ) (x / R)) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm f (ENNReal.ofReal p) volume := by
  have hR : 0 < R := hε.trans hεR
  have hm := stronglyMeasurable_periodize hfm R
  have hle := eLpNorm_periodize_le (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top hfm hR
  have hmem : MemLp (periodize R f) (ENNReal.ofReal p) volume := by
    refine ENNReal.lt_top_of_mul_ne_top_right (hle.trans_lt hf.eLpNorm_lt_top).ne ?_
    simp [ENNReal.rpow_eq_zero_iff, hR]
  rw [eLpNorm_indicator_comp_coe_div ENNReal.ofReal_ne_top
    (stronglyMeasurable_truncatedConj hm.aestronglyMeasurable _) hR]
  calc ENNReal.ofReal R ^ (1 / ENNReal.ofReal p).toReal *
        eLpNorm (truncatedConj (ε / R) (periodize R f)) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal R ^ (1 / ENNReal.ofReal p).toReal *
        (hilbertBound β * eLpNorm (periodize R f) (ENNReal.ofReal p) volume) := by
        gcongr
        exact eLpNorm_truncatedConj_volume_le hp hβ hmem (by positivity) ((div_lt_one hR).2 hεR)
    _ ≤ hilbertBound β * eLpNorm f (ENNReal.ofReal p) volume := by
        rw [mul_left_comm]
        gcongr

/-- (34) for a function `f ∈ L^p` that vanishes off `[−A, A]`, by Fatou's lemma. -/
private theorem eLpNorm_hilbertTrunc_le_of_support [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) {f : ℝ → X} (hfm : StronglyMeasurable f)
    (hf : MemLp f (ENNReal.ofReal p) volume) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ y, A < |y| → f y = 0) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (hilbertTrunc ε f) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm f (ENNReal.ofReal p) volume := by
  have hfint : Integrable f := by
    have h1 : IntegrableOn f (Set.Icc (-A) A) :=
      memLp_one_iff_integrable.1 ((hf.restrict _).mono_exponent
        (ENNReal.one_le_ofReal.2 hp.le))
    refine (integrableOn_iff_integrable_of_support_subset fun y hy => ?_).1 h1
    exact abs_le.1 (not_lt.1 (mt (hA y) hy))
  have hlim : ∀ x, Tendsto (fun n : ℕ => (Set.Ioc (-π) π).indicator
      (fun θ : ℝ => truncatedConj (ε / n) (periodize n f) θ) (x / n)) atTop
      (𝓝 (hilbertTrunc ε f x)) := by
    intro x
    refine (tendsto_truncatedConj_periodize hfint hA0 hA hε x).congr' ?_
    filter_upwards [(tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos).eventually_gt_atTop
      |x|, eventually_gt_atTop 0] with n hn hn0
    have hn0' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hx := abs_lt.1 hn
    rw [Set.indicator_of_mem]
    rw [Set.mem_Ioc, lt_div_iff₀ hn0', div_le_iff₀ hn0']
    constructor <;> linarith
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n : ℕ => ?_) _
    (stronglyMeasurable_hilbertTrunc hfm ε).aestronglyMeasurable (ae_of_all _ hlim)).trans ?_
  · exact (((stronglyMeasurable_truncatedConj
      (stronglyMeasurable_periodize hfm n).aestronglyMeasurable _).comp_measurable
      AddCircle.measurable_mk').indicator measurableSet_Ioc).comp_measurable
      (measurable_div_const _) |>.aestronglyMeasurable
  · refine (liminf_le_liminf ?_).trans (liminf_const _).le
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ε] with n hn
    exact eLpNorm_truncatedConj_periodize_le hp hβ hfm hf hε hn

/-! ### The truncated kernel -/

/-- `t⁻¹ ∈ L^q` on `{|t| > ε}`, for `q > 1`. -/
private theorem memLp_inv {q : ℝ} (hq : 1 < q) {ε : ℝ} (hε : 0 < ε) :
    MemLp (fun t : ℝ => t⁻¹) (ENNReal.ofReal q) (volume.restrict {t : ℝ | ε < |t|}) := by
  have hq0 : 0 < q := by linarith
  have h1 : MemLp (fun t : ℝ => (1 + ‖t‖)⁻¹) (ENNReal.ofReal q) volume := by
    rw [← integrable_norm_rpow_iff (Measurable.aestronglyMeasurable (by fun_prop)) (by simpa)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
    refine (integrable_one_add_norm (E := ℝ) (μ := volume) (r := q) (by simpa)).congr
      (ae_of_all _ fun t => ?_)
    have ht : (0 : ℝ) ≤ 1 + ‖t‖ := by positivity
    beta_reduce
    rw [Real.norm_of_nonneg (inv_nonneg.2 ht), Real.inv_rpow ht, Real.rpow_neg ht]
  refine (h1.restrict _).of_le_mul (c := 1 + ε⁻¹) (by fun_prop) ?_
  filter_upwards [ae_restrict_mem (measurableSet_lt_abs ε)] with t ht
  have ht0 : 0 < |t| := hε.trans ht
  have h2 : (0 : ℝ) < 1 + |t| := by positivity
  rw [norm_inv, norm_inv, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖t‖),
    Real.norm_eq_abs, ← div_eq_mul_inv, le_div_iff₀ h2, mul_add, mul_one,
    inv_mul_cancel₀ ht0.ne', add_comm]
  exact add_le_add_right (inv_anti₀ hε (le_of_lt ht)) 1

/-- Hölder's inequality: `t ↦ f (x − t) / t` is integrable over `|t| > ε`, for `f ∈ L^p`. -/
private theorem integrableOn_inv_smul {p : ℝ} (hp : 1 < p) {f : ℝ → X}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    IntegrableOn (fun t => t⁻¹ • f (x - t)) {t : ℝ | ε < |t|} := by
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have : ENNReal.HolderConjugate (ENNReal.ofReal (p / (p - 1))) (ENNReal.ofReal p) :=
    hpq.symm.ennrealOfReal
  have hfx : MemLp (fun t => f (x - t)) (ENNReal.ofReal p) volume :=
    hf.comp_measurePreserving (volume.measurePreserving_sub_left x)
  exact memLp_one_iff_integrable.1 ((memLp_inv hpq.symm.lt hε).smul (hfx.restrict _))

/-! ### Lemma 4 -/

/-- **Lemma 4** of Burkholder (1983), (34): `‖H_ε f‖_p ≤ (2 β² + 1) ‖f‖_p` for `f ∈ L^p (ℝ; X)` and
`ε > 0`.

The paper says that (34) "follows from (33) just as it does in the real case" and refers to M. Riesz
(1927) and to Zygmund's *Trigonometric Series*. The argument is written out here: it is the passage
from the circle to the line by periodization and dilation, for functions that vanish off a bounded
interval (`eLpNorm_hilbertTrunc_le_of_support`), followed by Fatou's lemma for `1_{[−n, n]} f`,
`n → ∞`. -/
theorem eLpNorm_hilbertTrunc_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ}
    (hε : 0 < ε) :
    eLpNorm (hilbertTrunc ε f) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm f (ENNReal.ofReal p) volume := by
  -- we may assume that `f` is strongly measurable
  wlog hfm : StronglyMeasurable f generalizing f
  · have hae := hf.aestronglyMeasurable.ae_eq_mk
    rw [hilbertTrunc_congr_ae hae, eLpNorm_congr_ae hae]
    exact this (hf.ae_eq hae) hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hind : ∀ n : ℕ, StronglyMeasurable ((Set.Icc (-n : ℝ) n).indicator f) := fun n =>
    hfm.indicator measurableSet_Icc
  have hlim : ∀ x, Tendsto (fun n : ℕ => hilbertTrunc ε ((Set.Icc (-n : ℝ) n).indicator f) x)
      atTop (𝓝 (hilbertTrunc ε f x)) := by
    refine fun x => Tendsto.const_smul (tendsto_integral_of_dominated_convergence
      (fun t => ‖t⁻¹ • f (x - t)‖) (fun n => ?_) (integrableOn_inv_smul hp hf hε x).norm
      (fun n => ae_of_all _ fun t => ?_) (ae_of_all _ fun t => ?_)) _
    · exact (measurable_inv.stronglyMeasurable.smul
        ((hind n).comp_measurable (measurable_const_sub x))).aestronglyMeasurable
    · rw [norm_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_indicator_le_norm_self f _) (norm_nonneg _)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop |x - t|] with n hn
      rw [Set.indicator_of_mem (show x - t ∈ Set.Icc (-n : ℝ) n from abs_le.1 hn)]
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n : ℕ =>
    (stronglyMeasurable_hilbertTrunc (hind n) ε).aestronglyMeasurable) _
    (stronglyMeasurable_hilbertTrunc hfm ε).aestronglyMeasurable (ae_of_all _ hlim)).trans ?_
  refine (liminf_le_liminf (Eventually.of_forall fun n => ?_)).trans (liminf_const _).le
  refine (eLpNorm_hilbertTrunc_le_of_support hp hβ (hind n) (hf.indicator
    measurableSet_Icc.nullMeasurableSet)
    (A := n) n.cast_nonneg (fun y hy => Set.indicator_of_notMem (fun h => ?_) _) hε).trans ?_
  · exact hy.not_ge (abs_le.2 h)
  · gcongr
    exact eLpNorm_indicator_le f measurableSet_Icc.nullMeasurableSet

/-! ### The limit as `ε → 0` -/

/-- For `f ∈ L^p`, `H_{ε,R} f (x) → H_ε f (x)` as `R → ∞`, where
`H_{ε,R} f (x) = π⁻¹ ∫_{ε < |x − y| < R} f (y) / (x − y) dy`. -/
private theorem tendsto_truncatedHilbert_atTop {p : ℝ} (hp : 1 < p) {f : ℝ → X}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Tendsto (fun R => truncatedHilbert ε R f x) atTop (𝓝 (hilbertTrunc ε f x)) := by
  have hR : ∀ R, truncatedHilbert ε R f x =
      π⁻¹ • ∫ t in {t : ℝ | ε < |t| ∧ |t| < R}, t⁻¹ • f (x - t) := by
    intro R
    have hS : MeasurableSet {y | ε < |x - y| ∧ |x - y| < R} :=
      (measurable_const_sub x) (measurableSet_annulus ε R)
    rw [truncatedHilbert, ← integral_indicator (measurableSet_annulus ε R),
      ← integral_indicator hS,
      ← integral_sub_left_eq_self ({t : ℝ | ε < |t| ∧ |t| < R}.indicator
        fun t => t⁻¹ • f (x - t)) volume x]
    congr 2 with y
    by_cases h : ε < |x - y| ∧ |x - y| < R <;> simp [h]
  simp_rw [hR]
  have hU : ⋃ R : ℝ, {t : ℝ | ε < |t| ∧ |t| < R} = {t : ℝ | ε < |t|} := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_and_left, and_iff_left_iff_imp]
    exact fun _ => exists_gt |t|
  have h := tendsto_setIntegral_of_monotone (μ := volume) (f := fun t : ℝ => t⁻¹ • f (x - t))
    (s := fun R : ℝ => {t : ℝ | ε < |t| ∧ |t| < R}) (measurableSet_annulus ε)
    (fun R S hRS t ht => ⟨ht.1, ht.2.trans_le hRS⟩) (by
      rw [hU]
      exact integrableOn_inv_smul hp hf hε x)
  rw [hU] at h
  exact h.const_smul _

end

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- For `f = 𝓕⁻ G ∈ L^p`, `G ∈ L¹`, and every `x`, `H_ε f (x) → 𝓕⁻ (−i sgn · G) (x)` as `ε → 0`.

This is not in the paper: `H_ε f` is the limit of the double truncations `H_{ε,R} f` as `R → ∞`, and
these converge as `ε → 0` and `R → ∞` together (`tendsto_truncatedHilbert_fourierInv`). -/
theorem tendsto_hilbertTrunc_fourierInv {p : ℝ} (hp : 1 < p) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (x : ℝ) :
    Tendsto (fun ε => hilbertTrunc ε (𝓕⁻ G) x) (𝓝[>] 0)
      (𝓝 (𝓕⁻ (fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) x)) := by
  -- the joint limit in `ε → 0` and `R → ∞` is an iterated limit
  refine (closed_nhds_basis _).ge_iff.2 fun s hs => ?_
  have h := ((tendsto_truncatedHilbert_fourierInv hG x).eventually_mem hs.1).curry
  rw [mem_map]
  filter_upwards [h, self_mem_nhdsWithin] with ε hε hε0
  exact hs.2.mem_of_tendsto (tendsto_truncatedHilbert_atTop hp hf hε0 x) hε

/-- **The Hilbert transform on UMD spaces** (Burkholder (1983)): for `f = 𝓕⁻ G ∈ L^p` with `G ∈ L¹`,
`‖𝓕⁻ (−i sgn · G)‖_p ≤ (2 β² + 1) ‖f‖_p`, by Lemma 4 and Fatou's lemma as `ε → 0`.

Departure from the source: the paper obtains `H f = lim H_ε f` for all `f ∈ L^p`, almost everywhere
and in `L^p`, from its Theorem 2. Here `f` is in the class of the functions `𝓕⁻ G ∈ L^p`, `G ∈ L¹`,
for which the limit exists everywhere and is identified by its Fourier transform. -/
theorem eLpNorm_fourierInv_neg_I_sign_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hsym : Integrable fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ :=
    hG.bdd_smul 1 (measurable_const.mul
      (Complex.measurable_ofReal.comp measurable_realSign)).aestronglyMeasurable
      (ae_of_all _ fun ξ => by rcases Real.sign_apply_eq ξ with h | h | h <;> simp [h])
  obtain ⟨ε, hε⟩ := (𝓝[>] (0 : ℝ)).exists_seq_tendsto
  have hε0 : ∀ᶠ i in atTop, 0 < ε i := hε.eventually_mem self_mem_nhdsWithin
  -- Fatou's lemma
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p) (μ := volume)
    (fun i => (stronglyMeasurable_hilbertTrunc
      (continuous_fourierInv_of_integrable hG).stronglyMeasurable (ε i)).aestronglyMeasurable) _
    (continuous_fourierInv_of_integrable hsym).aestronglyMeasurable
    (ae_of_all _ fun x => (tendsto_hilbertTrunc_fourierInv hp hG hf x).comp hε)).trans
      ((liminf_le_liminf ?_).trans (liminf_const _).le)
  filter_upwards [hε0] with i hi
  exact eLpNorm_hilbertTrunc_le hp hβ hf hi

/-- `eLpNorm_fourierInv_neg_I_sign_le` for the multiplier `sgn`:
`‖𝓕⁻ (sgn · G)‖_p ≤ (2 β² + 1) ‖𝓕⁻ G‖_p`. -/
theorem eLpNorm_fourierInv_sign_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have h := eLpNorm_fourierInv_neg_I_sign_le hp hβ hG hf
  rwa [fourierInv_neg_I_smul, eLpNorm_const_smul, enorm_neg, ← ofReal_norm, Complex.norm_I,
    ENNReal.ofReal_one, one_mul] at h

end HarmonicAnalysis
