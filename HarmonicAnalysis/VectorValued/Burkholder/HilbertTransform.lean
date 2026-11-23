/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Burkholder.ConjugateFunction
public import HarmonicAnalysis.VectorValued.HilbertTransform.Fourier
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Hilbert transform on UMD spaces, after Burkholder

D. L. Burkholder, *A geometric condition that implies the existence of certain singular integrals of
Banach-space-valued functions* (1983): for a function `f` on `ℝ` with values in a Banach space `X`,

`H_ε f (x) = π⁻¹ ∫_{|t| > ε} f (x − t) / t dt`  (`hilbertTrunc`; (2), p. 271).

Lemma 4, p. 283 (`eLpNorm_hilbertTrunc_le`): if `X` has a `UMD_p` constant `β`, `1 < p < ∞`, then
`‖H_ε f‖_p ≤ (2 β² + 1) ‖f‖_p` (34) for `f ∈ L^p (ℝ; X)` and `ε > 0`, with the constant
`hilbertBound β` of the inequality (33) for the truncated conjugate function `f̃_ε` on the circle.

The whole proof in the paper is: "This follows from (33) just as it does in the real case; see [14]
or [18]", that is, M. Riesz, *Sur les fonctions conjuguées*, Math. Z. 27 (1928), 218–244, and
A. Zygmund, *Trigonometric Series*. Riesz's §18 (pp. 234–235), which was read, passes from his
Theorem II on the circle to his Theorem VII on the line in one pass, for every `f ∈ L^p`. His
argument is followed here, applied to the truncated conjugate functions, as the paper's "follows
from (33)" indicates. For `n ≥ 1` let `g_n (θ) = f (nθ)`, `−π < θ ≤ π`, be extended periodically
(`periodize`), and `f̃_n (x) = (g_n)~_{ε/n} (x / n)`.

* Riesz's (38), truncated: for `|x| + ε < nπ`,
  `f̃_n (x) = π⁻¹ ∫_{y ∈ (−nπ, nπ], |x − y| > ε} (2n)⁻¹ cot ((x − y) / (2n)) f (y) dy`
  (`truncatedConj_periodize`).
* "`lim f̃_n (x) = f̃ (x)`", here `f̃_n (x) → H_ε f (x)`, for every `x`
  (`tendsto_truncatedConj_periodize`). Riesz writes "on démontre très facilement" and leaves the
  proof out ("Nous ne nous y arrêtons pas"); it is written out here, by dominated convergence:
  `|(2n)⁻¹ cot (v / (2n))| ≤ |v|⁻¹` for `|v| ≤ 4n`, from `|cot u| ≤ |u|⁻¹` for `|u| ≤ 2`
  (`abs_cot_le`), and `y ↦ f (y) / (x − y)` is integrable over `|x − y| > ε` by Hölder's inequality
  (`integrableOn_inv_smul`).
* Theorem II, here (33), and the dilation: `‖1_{(−nπ, nπ]} f̃_n‖_p ≤ (2 β² + 1) ‖f‖_p`
  (`eLpNorm_truncatedConj_periodize_le`), the norm of `f` on `(−nπ, nπ]` bounded by `‖f‖_p`.
* For `m ≤ n` the same bound holds on `(−mπ, mπ]`; for fixed `m`, Fatou's lemma as `n → ∞` bounds
  `‖1_{(−mπ, mπ]} H_ε f‖_p` (Riesz: "par le théorème cité de M. Fatou"), and `m → ∞` gives (34)
  (Riesz: "en faisant tendre m vers l'infini", without a reason; here Fatou's lemma again).

Zygmund's book was not consulted; the paper's "or" allows either reference.

The paper then states, without proof (Theorem 2, p. 284), that `lim T_ε f` exists, with bounds for
the maximal function `T* f`; this is not carried out here. Instead, for `f = 𝓕⁻ G ∈ L^p` with
`G ∈ L¹`, where `X` is a complex space, `H_ε f (x) → 𝓕⁻ (−i sgn · G) (x)` for every `x`
(`tendsto_hilbertTrunc_fourierInv`, from the computation of the symbols in
`HilbertTransform.Fourier`). By Fatou's lemma,

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

/-- `cot (u + π) = cot u`. -/
private theorem cot_add_pi (u : ℝ) : Real.cot (u + π) = Real.cot u := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_add_pi, Real.sin_add_pi,
    neg_div_neg_eq]

/-- `w |cos w| ≤ sin w` for `0 ≤ w ≤ 2`: for `w < π / 2` this is `w cos w ≤ sin w`; for
`π / 2 ≤ w ≤ 2`, with `v = w − π / 2 ≤ 0.43`, `w sin v ≤ 2 v ≤ 1 − v² / 2 ≤ cos v`. -/
private theorem mul_abs_cos_le_sin {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 2) :
    w * |Real.cos w| ≤ Real.sin w := by
  rcases lt_or_ge w (π / 2) with h | h
  · have hcos : 0 ≤ Real.cos w :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) h.le
    rw [abs_of_nonneg hcos]
    rcases hw0.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, Real.sin_zero]
    · have h1 := Real.cos_le_sinc (x := w) (by rw [abs_of_pos h0]; exact h)
      rw [Real.sinc_of_ne_zero h0.ne', le_div_iff₀ h0] at h1
      linarith
  · set v := w - π / 2 with hv
    have hv0 : 0 ≤ v := by linarith
    have hv1 : v ≤ 0.43 := by linarith [Real.pi_gt_d2]
    have hcos : Real.cos w = -Real.sin v := by
      rw [show w = v + π / 2 by ring, Real.cos_add_pi_div_two]
    have hsin : Real.sin w = Real.cos v := by
      rw [show w = v + π / 2 by ring, Real.sin_add_pi_div_two]
    have hs0 : 0 ≤ Real.sin v :=
      Real.sin_nonneg_of_nonneg_of_le_pi hv0 (by linarith [Real.pi_gt_three])
    rw [hcos, hsin, abs_neg, abs_of_nonneg hs0]
    nlinarith [Real.sin_le hv0, Real.one_sub_sq_div_two_le_cos (x := v),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - w) hs0, mul_le_mul_of_nonneg_left hv1 hv0]

/-- `|cot u| ≤ |u|⁻¹` for `|u| ≤ 2`. -/
private theorem abs_cot_le {u : ℝ} (hu : |u| ≤ 2) : |Real.cot u| ≤ |u|⁻¹ := by
  have hodd : |Real.cot u| = |Real.cot (|u|)| := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_neg,
        Real.sin_neg, div_neg, abs_neg]
  rw [hodd]
  rcases (abs_nonneg u).eq_or_lt with h0 | h0
  · rw [← h0, Real.cot_eq_cos_div_sin, Real.sin_zero, div_zero, abs_zero, inv_zero]
  have hs : 0 < Real.sin |u| := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_gt_three])
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hs, div_le_iff₀ hs, inv_mul_eq_div,
    le_div_iff₀ h0, mul_comm]
  exact mul_abs_cos_le_sin h0.le hu

/-- `|(2R)⁻¹ cot (v / (2R))| ≤ |v|⁻¹` for `|v| ≤ 4R` (`abs_cot_le`). -/
private theorem abs_inv_mul_cot_le {R : ℝ} (hR : 0 < R) {v : ℝ} (hv : |v| ≤ 4 * R) :
    |(2 * R)⁻¹ * Real.cot (v / (2 * R))| ≤ |v|⁻¹ := by
  have h2R : 0 < 2 * R := by positivity
  have hu : |v / (2 * R)| ≤ 2 := by
    rw [abs_div, abs_of_pos h2R, div_le_iff₀ h2R]
    linarith
  rw [abs_mul, abs_of_pos (inv_pos.2 h2R)]
  refine (mul_le_mul_of_nonneg_left (abs_cot_le hu) (inv_nonneg.2 h2R.le)).trans_eq ?_
  rw [abs_div, abs_of_pos h2R, inv_div, mul_div_assoc', inv_mul_cancel₀ h2R.ne', one_div]

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

/-- `{ε < |s| < b}` is measurable. -/
private theorem measurableSet_annulus (ε b : ℝ) : MeasurableSet {s : ℝ | ε < |s| ∧ |s| < b} :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- `{ε < |s|}` is measurable. -/
private theorem measurableSet_lt_abs (ε : ℝ) : MeasurableSet {s : ℝ | ε < |s|} :=
  measurableSet_lt measurable_const measurable_norm

/-- The kernel `1_{ε < |t|} cot (t / 2)` of `f̃_ε` on `(−π, π]`, extended periodically. -/
private noncomputable def perCot (ε t : ℝ) : ℝ :=
  AddCircle.liftIoc (2 * π) (-π) ({t : ℝ | ε < |t|}.indicator fun t => Real.cot (t / 2))
    (t : AddCircle (2 * π))

/-- The periodic kernel has the period `2π`. -/
private theorem perCot_periodic (ε : ℝ) : Function.Periodic (perCot ε) (2 * π) := fun t => by
  simp only [perCot, AddCircle.coe_add_period]

/-- On `(−π, π]` the periodic kernel is `1_{ε < |t|} cot (t / 2)`. -/
private theorem perCot_of_mem (ε : ℝ) {t : ℝ} (ht : t ∈ Set.Ioc (-π) π) :
    perCot ε t = {t : ℝ | ε < |t|}.indicator (fun t => Real.cot (t / 2)) t := by
  rw [perCot, AddCircle.liftIoc_coe_apply]
  rwa [show -π + 2 * π = π by ring]

/-- The kernel of `f̃_ε`, `1_{ε < |t| < π} cot (t / 2)`, is the periodic kernel on `(−π, π]`; at
`t = π` both vanish, as `cot (π / 2) = 0`. -/
private theorem indicator_annulus_eq (ε : ℝ) (w : ℝ → X) (t : ℝ) :
    {t : ℝ | ε < |t| ∧ |t| < π}.indicator (fun t => Real.cot (t / 2) • w t) t =
      (Set.Ioc (-π) π).indicator (fun t => perCot ε t • w t) t := by
  by_cases ht : t ∈ Set.Ioc (-π) π
  · rw [Set.indicator_of_mem ht, perCot_of_mem ε ht]
    by_cases h1 : ε < |t|
    · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | ε < |t|} from h1)]
      rcases (abs_le.2 ⟨ht.1.le, ht.2⟩).lt_or_eq with h2 | h2
      · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | ε < |t| ∧ |t| < π} from ⟨h1, h2⟩)]
      · have hπ : t = π := by
          rcases (abs_eq Real.pi_pos.le).1 h2 with h | h
          · exact h
          · exact absurd ht.1 (by rw [h]; exact lt_irrefl _)
        rw [Set.indicator_of_notMem (fun (h : t ∈ {t : ℝ | ε < |t| ∧ |t| < π}) => h.2.ne h2), hπ,
          Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, zero_div, zero_smul]
    · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | ε < |t|} from h1),
        Set.indicator_of_notMem (fun (h : t ∈ {t : ℝ | ε < |t| ∧ |t| < π}) => h1 h.1), zero_smul]
  · rw [Set.indicator_of_notMem ht,
      Set.indicator_of_notMem fun (h : t ∈ {t : ℝ | ε < |t| ∧ |t| < π}) =>
        ht ⟨(abs_lt.1 h.2).1, (abs_lt.1 h.2).2.le⟩]

/-- For `y ∈ (−nπ, nπ]` and `|x| + ε < nπ`, the periodic kernel at `(x − y) / n` is
`1_{ε < |x − y|} cot ((x − y) / (2n))`: the distance of `(x − y) / n` to `2πℤ` exceeds `ε / n`
exactly when `|x − y| > ε`, since `|x − y| < 2nπ − ε`. -/
private theorem perCot_div {n ε x y : ℝ} (hn : 0 < n) (hε : 0 < ε) (hx : |x| + ε < π * n)
    (hy : y ∈ Set.Ioc (-(π * n)) (π * n)) :
    perCot (ε / n) ((x - y) / n) =
      {y : ℝ | ε < |x - y|}.indicator (fun y => Real.cot ((x - y) / (2 * n))) y := by
  set t := (x - y) / n with ht
  have hy' : |y| ≤ π * n := abs_le.2 ⟨hy.1.le, hy.2⟩
  have hxy : |x - y| < 2 * (π * n) - ε := by linarith [abs_sub x y]
  have htn : |t| = |x - y| / n := by rw [ht, abs_div, abs_of_pos hn]
  have hiff : ε / n < |t| ↔ ε < |x - y| := by rw [htn, div_lt_div_iff_of_pos_right hn]
  have hcot : Real.cot (t / 2) = Real.cot ((x - y) / (2 * n)) := by rw [ht, div_div, mul_comm n]
  have hεn : 0 < ε / n := div_pos hε hn
  have ht2 : |t| < 2 * π - ε / n := by
    rw [htn, div_lt_iff₀ hn, sub_mul, div_mul_cancel₀ _ hn.ne']
    linarith
  have hfar : π ≤ |t| → y ∈ {y : ℝ | ε < |x - y|} := fun h => by
    rw [htn, le_div_iff₀ hn] at h
    rw [Set.mem_ofPred_eq]
    linarith [abs_nonneg x]
  obtain ⟨ht3, ht4⟩ := abs_lt.1 ht2
  rcases le_or_gt t π with h1 | h1
  · rcases lt_or_ge (-π) t with h2 | h2
    · -- `t ∈ (−π, π]`
      rw [perCot_of_mem _ ⟨h2, h1⟩, Set.indicator_apply, Set.indicator_apply]
      simp only [Set.mem_ofPred_eq, hiff, hcot]
    · -- `t ≤ −π`: `t + 2π ∈ (0, π]`
      rw [← (perCot_periodic _) t, perCot_of_mem _ ⟨by linarith, by linarith⟩,
        Set.indicator_of_mem (show t + 2 * π ∈ {t : ℝ | ε / n < |t|} by
          rw [Set.mem_ofPred_eq, abs_of_pos (by linarith)]
          linarith),
        Set.indicator_of_mem (hfar (by rw [abs_of_neg (by linarith [Real.pi_pos])]; linarith)),
        show (t + 2 * π) / 2 = t / 2 + π by ring, cot_add_pi, hcot]
  · -- `t > π`: `t − 2π ∈ (−π, 0)`
    rw [← (perCot_periodic _).sub_eq t, perCot_of_mem _ ⟨by linarith, by linarith⟩,
      Set.indicator_of_mem (show t - 2 * π ∈ {t : ℝ | ε / n < |t|} by
        rw [Set.mem_ofPred_eq, abs_of_neg (by linarith)]
        linarith),
      Set.indicator_of_mem (hfar (by rw [abs_of_pos (by linarith [Real.pi_pos])]; linarith)),
      ← cot_add_pi ((t - 2 * π) / 2), show (t - 2 * π) / 2 + π = t / 2 by ring, hcot]

/-- **Riesz's (38)**, truncated (§18): for `|x| + ε < nπ`,
`(g_n)~_{ε/n} (x / n) = π⁻¹ ∫_{y ∈ (−nπ, nπ], |x − y| > ε} (2n)⁻¹ cot ((x − y) / (2n)) f (y) dy`.
The substitution `t = x / n − φ` and the periodicity of the integrand in `φ` move the integral to
`φ ∈ (−π, π]`, where `g_n (φ) = f (nφ)`; then `φ = y / n` (`perCot_div`). No support condition on
`f` is needed. -/
private theorem truncatedConj_periodize (f : ℝ → X) {n : ℝ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    {x : ℝ} (hx : |x| + ε < π * n) :
    truncatedConj (ε / n) (periodize n f) ((x / n : ℝ) : AddCircle (2 * π)) =
      π⁻¹ • ∫ y in Set.Ioc (-(π * n)) (π * n), {y : ℝ | ε < |x - y|}.indicator
        (fun y => ((2 * n)⁻¹ * Real.cot ((x - y) / (2 * n))) • f y) y := by
  set G : ℝ → X := fun φ => perCot (ε / n) (x / n - φ) • periodize n f φ with hG
  have hπ : -π ≤ π := by linarith [Real.pi_pos]
  -- the integral over `{ε / n < |t| < π}` as an integral over `(−π, π]`
  have h1 : truncatedConj (ε / n) (periodize n f) ((x / n : ℝ) : AddCircle (2 * π)) =
      (2 * π)⁻¹ • ∫ t in (-π)..π, G (x / n - t) := by
    rw [truncatedConj, intervalIntegral.integral_of_le hπ,
      ← integral_indicator (measurableSet_annulus _ _), ← integral_indicator measurableSet_Ioc]
    congr 2 with t
    rw [indicator_annulus_eq (ε / n) (fun t => periodize n f (((x / n : ℝ) : AddCircle (2 * π)) -
      (t : AddCircle (2 * π)))) t]
    simp only [hG, sub_sub_cancel, AddCircle.coe_sub]
  -- `t = x / n − φ`, and the periodicity in `φ`
  have hGp : Function.Periodic G (2 * π) := fun φ => by
    simp only [hG, sub_add_eq_sub_sub, (perCot_periodic _).sub_eq, AddCircle.coe_add_period]
  have h2 : ∫ t in (-π)..π, G (x / n - t) = ∫ φ in (-π)..π, G φ := by
    rw [intervalIntegral.integral_comp_sub_left G (x / n),
      show x / n - -π = x / n - π + 2 * π by ring, hGp.intervalIntegral_add_eq (x / n - π) (-π),
      show -π + 2 * π = π by ring]
  -- `g_n (φ) = f (nφ)` on `(−π, π]`
  have h3 : ∫ φ in (-π)..π, G φ = ∫ φ in (-π)..π, perCot (ε / n) (x / n - φ) • f (n * φ) := by
    rw [intervalIntegral.integral_of_le hπ, intervalIntegral.integral_of_le hπ]
    refine setIntegral_congr_fun measurableSet_Ioc fun φ hφ => ?_
    simp only [hG, periodize]
    rw [AddCircle.liftIoc_coe_apply (by rwa [show -π + 2 * π = π by ring])]
  -- `φ = y / n`
  have h4 : ∫ φ in (-π)..π, perCot (ε / n) (x / n - φ) • f (n * φ) =
      n⁻¹ • ∫ y in (-(π * n))..(π * n), perCot (ε / n) ((x - y) / n) • f y := by
    have h := intervalIntegral.integral_comp_div
      (fun φ => perCot (ε / n) (x / n - φ) • f (n * φ)) (a := -(π * n)) (b := π * n) hn.ne'
    rw [show -(π * n) / n = -π by field_simp, show π * n / n = π by field_simp] at h
    have h' : ∫ y in (-(π * n))..(π * n), perCot (ε / n) ((x - y) / n) • f y =
        ∫ y in (-(π * n))..(π * n), perCot (ε / n) (x / n - y / n) • f (n * (y / n)) :=
      intervalIntegral.integral_congr fun y _ => by rw [sub_div, mul_div_cancel₀ _ hn.ne']
    rw [h', h, inv_smul_smul₀ hn.ne']
  have h5 : ∫ y in (-(π * n))..(π * n), perCot (ε / n) ((x - y) / n) • f y =
      (2 * n) • ∫ y in Set.Ioc (-(π * n)) (π * n), {y : ℝ | ε < |x - y|}.indicator
        (fun y => ((2 * n)⁻¹ * Real.cot ((x - y) / (2 * n))) • f y) y := by
    rw [intervalIntegral.integral_of_le (by nlinarith [Real.pi_pos]), ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    rw [perCot_div hn hε hx hy, Set.indicator_apply, Set.indicator_apply]
    split_ifs
    · rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    · rw [zero_smul, smul_zero]
  rw [h1, h2, h3, h4, h5, smul_smul, smul_smul]
  congr 1
  field_simp

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
  have h := eLpNorm_comp_mul (g := (Set.Ioc (-π) π).indicator fun θ : ℝ => h θ) hp
    ((hh.comp_measurable AddCircle.measurable_mk').indicator
      measurableSet_Ioc).aestronglyMeasurable (inv_pos.2 hR)
  rw [inv_inv, eLpNorm_indicator_comp_coe hh] at h
  simpa only [div_eq_inv_mul] using h

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

/-! ### The limit `n → ∞` -/

/-- "`lim f̃_n (x) = f̃ (x)`", which Riesz leaves out (§18, "on démontre très facilement … Nous ne
nous y arrêtons pas"), for every `x` and `f ∈ L^p`, `f̃_n (x) = (g_n)~_{ε/n} (x / n)`: by (38)
(`truncatedConj_periodize`) and dominated convergence. For `|x| + πn ≤ 4n` and `y ∈ (−nπ, nπ]`,
`|x − y| ≤ 4n`, so `|(2n)⁻¹ cot ((x − y) / (2n))| ≤ |x − y|⁻¹` (`abs_inv_mul_cot_le`); the bound
`y ↦ 1_{|x − y| > ε} |f (y)| / |x − y|` is integrable by Hölder's inequality
(`integrableOn_inv_smul`); and `(2n)⁻¹ cot (v / (2n)) → v⁻¹`. -/
private theorem tendsto_truncatedConj_periodize {p : ℝ} (hp : 1 < p) {f : ℝ → X}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Tendsto (fun n : ℕ => truncatedConj (ε / n) (periodize n f)
      ((x / n : ℝ) : AddCircle (2 * π))) atTop (𝓝 (hilbertTrunc ε f x)) := by
  have hlarge : ∀ B : ℝ, ∀ᶠ n : ℕ in atTop, B < π * n := fun B =>
    (tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos).eventually_gt_atTop B
  have h4 : ∀ᶠ n : ℕ in atTop, |x| + π * n ≤ 4 * n := by
    have h4π : 0 < 4 - π := by linarith [Real.pi_lt_d2]
    filter_upwards [(tendsto_natCast_atTop_atTop.const_mul_atTop h4π).eventually_ge_atTop |x|]
      with n hn
    linarith
  have hS : MeasurableSet {y : ℝ | ε < |x - y|} :=
    measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm
  -- the limit: `π H_ε f (x) = ∫_{|x − y| > ε} f (y) / (x − y) dy`
  have hint : Integrable fun y => {y : ℝ | ε < |x - y|}.indicator (fun y => (x - y)⁻¹ • f y) y := by
    refine (((integrableOn_inv_smul hp hf hε x).integrable_indicator
      (measurableSet_lt_abs ε)).comp_sub_left x).congr (ae_of_all _ fun y => ?_)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, sub_sub_cancel]
  have hH : hilbertTrunc ε f x =
      π⁻¹ • ∫ y, {y : ℝ | ε < |x - y|}.indicator (fun y => (x - y)⁻¹ • f y) y := by
    rw [hilbertTrunc, ← integral_indicator (measurableSet_lt_abs ε),
      ← integral_sub_left_eq_self _ volume x]
    congr 2 with y
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, sub_sub_cancel]
  have hlim : Tendsto (fun n : ℕ => ∫ y, (Set.Ioc (-(π * n)) (π * n)).indicator
      ({y : ℝ | ε < |x - y|}.indicator
        fun y => ((2 * (n : ℝ))⁻¹ * Real.cot ((x - y) / (2 * n))) • f y) y) atTop
      (𝓝 (∫ y, {y : ℝ | ε < |x - y|}.indicator (fun y => (x - y)⁻¹ • f y) y)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => ‖{y : ℝ | ε < |x - y|}.indicator (fun y => (x - y)⁻¹ • f y) y‖) ?_ ?_ hint.norm
      (ae_of_all _ fun y => ?_)
    · exact Eventually.of_forall fun n => ((((measurable_inv_mul_cot n).comp
        (measurable_const_sub x)).aestronglyMeasurable.smul hf.aestronglyMeasurable).indicator
          hS).indicator
          measurableSet_Ioc
    · filter_upwards [h4, eventually_gt_atTop 0] with n hn hn0
      have hn0' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
      refine ae_of_all _ fun y => ?_
      by_cases hy : y ∈ Set.Ioc (-(π * n)) (π * n) ∧ ε < |x - y|
      · rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem (show y ∈ {y : ℝ | ε < |x - y|} from
          hy.2), Set.indicator_of_mem (show y ∈ {y : ℝ | ε < |x - y|} from hy.2), norm_smul,
          norm_smul, Real.norm_eq_abs, norm_inv, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right (abs_inv_mul_cot_le hn0' ?_) (norm_nonneg _)
        linarith [abs_sub x y, abs_le.2 ⟨hy.1.1.le, hy.1.2⟩]
      · have h0 : (Set.Ioc (-(π * n)) (π * n)).indicator ({y : ℝ | ε < |x - y|}.indicator
            fun y => ((2 * (n : ℝ))⁻¹ * Real.cot ((x - y) / (2 * n))) • f y) y = 0 := by
          by_cases h1 : y ∈ Set.Ioc (-(π * n)) (π * n)
          · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (fun h2 => hy ⟨h1, h2⟩)]
          · rw [Set.indicator_of_notMem h1]
        rw [h0, norm_zero]
        exact norm_nonneg _
    · by_cases hy : ε < |x - y|
      · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | ε < |x - y|} from hy)]
        refine ((tendsto_inv_mul_cot (x - y)).smul_const (f y)).congr' ?_
        filter_upwards [hlarge |y|] with n hn
        rw [Set.indicator_of_mem (show y ∈ Set.Ioc (-(π * n)) (π * n) from
          ⟨by linarith [neg_abs_le y], (le_abs_self y).trans hn.le⟩),
          Set.indicator_of_mem (show y ∈ {y : ℝ | ε < |x - y|} from hy)]
      · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | ε < |x - y|} from hy)]
        refine tendsto_const_nhds.congr fun n => ?_
        by_cases h1 : y ∈ Set.Ioc (-(π * n)) (π * n)
        · rw [Set.indicator_of_mem h1,
            Set.indicator_of_notMem (show y ∉ {y : ℝ | ε < |x - y|} from hy)]
        · rw [Set.indicator_of_notMem h1]
  rw [hH]
  refine (hlim.const_smul π⁻¹).congr' ?_
  filter_upwards [hlarge (|x| + ε), eventually_gt_atTop 0] with n hn hn0
  rw [truncatedConj_periodize f (Nat.cast_pos.2 hn0) hε hn, integral_indicator measurableSet_Ioc]

/-! ### Lemma 4 -/

/-- **Lemma 4** of Burkholder (1983), (34): `‖H_ε f‖_p ≤ (2 β² + 1) ‖f‖_p` for `f ∈ L^p (ℝ; X)` and
`ε > 0`.

The paper says that (34) "follows from (33) just as it does in the real case" and refers to
M. Riesz (1928) and to Zygmund's *Trigonometric Series*. This is Riesz's argument (§18), applied to
the truncations: for `g_n (θ) = f (nθ)`, `−π < θ ≤ π`, extended periodically, and
`f̃_n (x) = (g_n)~_{ε/n} (x / n)`,

* `f̃_n (x) → H_ε f (x)` for every `x` (`tendsto_truncatedConj_periodize`; stated by Riesz without
  proof, here by dominated convergence);
* by (33) and the dilation, `‖1_{(−nπ, nπ]} f̃_n‖_p ≤ (2 β² + 1) ‖f‖_p`
  (`eLpNorm_truncatedConj_periodize_le`), so `‖1_{(−mπ, mπ]} f̃_n‖_p ≤ (2 β² + 1) ‖f‖_p` for
  `m ≤ n`;
* for fixed `m`, Fatou's lemma as `n → ∞` gives `‖1_{(−mπ, mπ]} H_ε f‖_p ≤ (2 β² + 1) ‖f‖_p`, and
  `m → ∞` gives (34) (Riesz: "en faisant tendre m vers l'infini", without a reason; here Fatou's
  lemma again). -/
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
  have hH := stronglyMeasurable_hilbertTrunc hfm ε
  -- `f̃_n (x) = (g_n)~_{ε/n} (x / n)`
  have hm : ∀ n : ℕ, StronglyMeasurable fun x : ℝ =>
      truncatedConj (ε / n) (periodize n f) ((x / n : ℝ) : AddCircle (2 * π)) := fun n =>
    (stronglyMeasurable_truncatedConj (stronglyMeasurable_periodize hfm n).aestronglyMeasurable
      _).comp_measurable (AddCircle.measurable_mk'.comp (measurable_div_const _))
  -- for `m ≤ n`, `‖1_{(−mπ, mπ]} f̃_n‖_p ≤ ‖1_{(−nπ, nπ]} f̃_n‖_p ≤ (2 β² + 1) ‖f‖_p`
  have hmn : ∀ m n : ℕ, m ≤ n → ε < n →
      eLpNorm ((Set.Ioc (-(π * m)) (π * m)).indicator fun x : ℝ =>
        truncatedConj (ε / n) (periodize n f) ((x / n : ℝ) : AddCircle (2 * π)))
          (ENNReal.ofReal p) volume ≤ hilbertBound β * eLpNorm f (ENNReal.ofReal p) volume := by
    intro m n hmn hn
    have hn0 : (0 : ℝ) < n := hε.trans hn
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    refine (eLpNorm_mono ?_ fun x => ?_).trans
      (eLpNorm_truncatedConj_periodize_le hp hβ hfm hf hε hn)
    · exact ((hm n).indicator measurableSet_Ioc).aestronglyMeasurable
    by_cases hx : x ∈ Set.Ioc (-(π * m)) (π * m)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
      rw [Set.mem_Ioc, lt_div_iff₀ hn0, div_le_iff₀ hn0]
      constructor <;> nlinarith [hx.1, hx.2, Real.pi_pos]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact norm_nonneg _
  -- fix `m` and let `n → ∞` (Fatou's lemma)
  have hFm : ∀ m : ℕ, eLpNorm ((Set.Ioc (-(π * m)) (π * m)).indicator (hilbertTrunc ε f))
      (ENNReal.ofReal p) volume ≤ hilbertBound β * eLpNorm f (ENNReal.ofReal p) volume := by
    intro m
    have hI : MeasurableSet (Set.Ioc (-(π * m)) (π * m)) := measurableSet_Ioc
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => ((hm n).indicator hI).aestronglyMeasurable)
      _ (hH.indicator hI).aestronglyMeasurable (ae_of_all _ fun x => ?_)).trans ?_
    · by_cases hx : x ∈ Set.Ioc (-(π * m)) (π * m)
      · simp only [Set.indicator_of_mem hx]
        exact tendsto_truncatedConj_periodize hp hf hε x
      · simp only [Set.indicator_of_notMem hx]
        exact tendsto_const_nhds
    · refine (liminf_le_liminf ?_).trans (liminf_const _).le
      filter_upwards [eventually_ge_atTop m, tendsto_natCast_atTop_atTop.eventually_gt_atTop ε]
        with n hn hn'
      exact hmn m n hn hn'
  -- let `m → ∞` (Fatou's lemma)
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun m : ℕ => (hH.indicator
    measurableSet_Ioc).aestronglyMeasurable) _ hH.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)).trans ((liminf_le_liminf (Eventually.of_forall hFm)).trans
      (liminf_const _).le)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos).eventually_gt_atTop |x|]
    with m hm
  rw [Set.indicator_of_mem (show x ∈ Set.Ioc (-(π * m)) (π * m) from
    ⟨by linarith [neg_abs_le x], (le_abs_self x).trans hm.le⟩)]

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
