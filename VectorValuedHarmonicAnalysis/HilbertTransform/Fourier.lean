module

public import VectorValuedHarmonicAnalysis.HilbertTransform.Truncated
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Fourier multiplier `sgn` on UMD spaces

Let `X` be a complex Banach space. For `G ∈ L¹ (ℝ; X)`, `f = 𝓕⁻ G` is a bounded continuous function,
and a bounded measurable `m` acts on it by `T_m f = 𝓕⁻ (m G)` (HNVW's class `Ľ¹`). The truncated
Hilbert transform acts with the symbol
`−i sgn (ξ) m_{ε,R} (ξ)`, `|m_{ε,R}| ≤ 2`, `m_{ε,R} → 1` (`truncatedHilbert_fourierInv`,
`abs_hilbertSymbol_le`, `tendsto_hilbertSymbol`; Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis
in Banach spaces I* (2016), Lemma 5.2.1, pp. 388–389: Cauchy's theorem on a half annulus). With
Fatou's lemma, on a UMD space `X`, `‖𝓕⁻ (sgn · G)‖_p ≤ (4 β² + 11) ‖𝓕⁻ G‖_p`
(`eLpNorm_fourierInv_sign_le`): the Hilbert transform is bounded on `L^p (ℝ; X)`, `1 < p < ∞`.
-/

@[expose] public section

open MeasureTheory BanachProbability Filter Topology
open scoped ENNReal FourierTransform

namespace VectorValuedHarmonicAnalysis

/-- HNVW I, Lemma 5.2.1: the function `m_{ε,R}`,
`−i sgn (ξ) m_{ε,R} (ξ) = π⁻¹ ∫_{ε < |x| < R} e^{−2πi x ξ} dx / x`, that is,
`m_{ε,R} (ξ) = (2/π) ∫_ε^R sin (2π |ξ| x) / x dx`. -/
noncomputable def hilbertSymbol (ε R ξ : ℝ) : ℝ :=
  2 / Real.pi * ∫ x in ε..R, Real.sin (2 * Real.pi * |ξ| * x) / x

/-! ### Cauchy's theorem on the half annulus -/

/-- The integral over the left half of the circle of radius `r`:
`∫_{π/2}^{3π/2} e^{r e^{iθ}} dθ`. -/
private noncomputable def semicircle (r : ℝ) : ℂ :=
  ∫ θ : ℝ in Real.pi / 2..3 * Real.pi / 2, Complex.exp (r * Complex.exp (θ * Complex.I))

/-- Cauchy's theorem on the half annulus `{ε < |z| < R, Re z < 0}`, for `e^{c z} / z`: in the
coordinate `ζ`, `z = e^ζ`, it is Cauchy's theorem on a rectangle. -/
private theorem two_mul_integral_sin_div (c : ℝ) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ((2 * ∫ x in ε..R, Real.sin (c * x) / x : ℝ) : ℂ) =
      semicircle (c * ε) - semicircle (c * R) := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  set z : ℂ := ⟨Real.log ε, Real.pi / 2⟩
  set w : ℂ := ⟨Real.log R, 3 * Real.pi / 2⟩
  set f : ℂ → ℂ := fun ζ => Complex.exp (c * Complex.exp ζ)
  have hf : Differentiable ℂ f := by fun_prop
  have hcauchy := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w
    hf.differentiableOn
  -- the vertical sides are the semicircles
  have hvert : ∀ {r : ℝ}, 0 < r → ∫ θ : ℝ in Real.pi / 2..3 * Real.pi / 2,
      f ((Real.log r : ℂ) + θ * Complex.I) = semicircle (c * r) := by
    intro r hr
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [f]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr, Complex.ofReal_mul, mul_assoc]
  -- the horizontal sides are the segments of the imaginary axis
  have h1 : ∀ u : ℝ, f (u + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (c * Real.exp u * Complex.I) := fun u => by
    simp only [f]
    rw [Complex.exp_add, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
    push_cast
    ring_nf
  have h2 : ∀ u : ℝ, f (u + ((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(c * Real.exp u * Complex.I)) := fun u => by
    simp only [f]
    rw [show ((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I =
        Real.pi * Complex.I + Real.pi / 2 * Complex.I by push_cast; ring, Complex.exp_add,
      Complex.exp_add (Real.pi * Complex.I), Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
    push_cast
    ring_nf
  have h3 : ∀ u : ℝ, Complex.exp (c * Real.exp u * Complex.I) -
      Complex.exp (-(c * Real.exp u * Complex.I)) =
      (2 * Complex.I) * ((Real.sin (c * Real.exp u) : ℝ) : ℂ) := fun u => by
    have h := Complex.two_sin (c * Real.exp u)
    rw [neg_mul] at h
    rw [Complex.ofReal_sin, Complex.ofReal_mul]
    linear_combination (-Complex.I) * h + (Complex.exp (c * Real.exp u * Complex.I) -
      Complex.exp (-(c * Real.exp u * Complex.I))) * Complex.I_sq
  -- the substitution `x = e^u`
  have h4 : ∫ u in Real.log ε..Real.log R, Real.sin (c * Real.exp u) =
      ∫ x in ε..R, Real.sin (c * x) / x := by
    have h := intervalIntegral.integral_comp_mul_deriv' (a := Real.log ε) (b := Real.log R)
      (f := Real.exp) (f' := Real.exp) (g := fun x => Real.sin (c * x) / x)
      (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn (by
        refine ContinuousOn.div (by fun_prop) continuousOn_id ?_
        rintro _ ⟨u, _, rfl⟩
        exact (Real.exp_pos u).ne')
    rw [Real.exp_log hε, Real.exp_log hR] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [Function.comp_apply]
    rw [div_mul_cancel₀ _ (Real.exp_pos u).ne']
  have hint : ∀ k : ℂ, IntervalIntegrable (fun u : ℝ => f (u + k)) volume (Real.log ε)
      (Real.log R) := fun k =>
    Continuous.intervalIntegrable (hf.continuous.comp (by fun_prop)) _ _
  have hhor : (∫ u : ℝ in Real.log ε..Real.log R, f (u + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) -
      (∫ u : ℝ in Real.log ε..Real.log R, f (u + ((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I)) =
      (2 * Complex.I) * ((∫ x in ε..R, Real.sin (c * x) / x : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_sub (hint _) (hint _)]
    simp_rw [h1, h2, h3]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, h4]
  have hc : (2 * Complex.I) * ((∫ x in ε..R, Real.sin (c * x) / x : ℝ) : ℂ) +
      Complex.I * semicircle (c * R) - Complex.I * semicircle (c * ε) = 0 := by
    rw [← hhor, ← hvert hε, ← hvert hR]
    exact hcauchy
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  refine mul_left_cancel₀ hI ?_
  linear_combination hc

/-- HNVW I, Lemma 5.2.1: the estimate of the integrals over the half circles,
`∫_{π/2}^{3π/2} e^{r cos θ} dθ = 2 ∫_0^{π/2} e^{−r sin θ} dθ`. -/
private theorem norm_semicircle_le (r : ℝ) :
    ‖semicircle r‖ ≤ 2 * ∫ θ in (0 : ℝ)..Real.pi / 2, Real.exp (-(r * Real.sin θ)) := by
  have hcont : Continuous fun θ => Real.exp (-(r * Real.sin θ)) := by fun_prop
  have hpi := Real.pi_pos
  have h1 : ‖semicircle r‖ ≤
      ∫ θ in Real.pi / 2..3 * Real.pi / 2, Real.exp (r * Real.cos θ) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) (ae_of_all _ fun θ _ => ?_)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [Complex.norm_exp, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have h2 : ∫ θ in Real.pi / 2..3 * Real.pi / 2, Real.exp (r * Real.cos θ) =
      ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-(r * Real.sin θ)) := by
    have h := intervalIntegral.integral_comp_add_right (a := 0) (b := Real.pi)
      (fun θ => Real.exp (r * Real.cos θ)) (Real.pi / 2)
    rw [zero_add, show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring] at h
    rw [← h]
    simp only [Real.cos_add_pi_div_two, mul_neg]
  have h3 : ∫ θ in Real.pi / 2..Real.pi, Real.exp (-(r * Real.sin θ)) =
      ∫ θ in (0 : ℝ)..Real.pi / 2, Real.exp (-(r * Real.sin θ)) := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi / 2)
      (fun θ => Real.exp (-(r * Real.sin θ))) Real.pi
    rw [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
    rw [← h]
    simp only [Real.sin_pi_sub]
  rw [two_mul]
  nth_rewrite 2 [← h3]
  rw [intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _), ← h2]
  exact h1

/-- HNVW I, Lemma 5.2.1: the bound `π r⁻¹ (1 − e^{−r})`, by `sin θ ≥ (2/π) θ`. -/
private theorem norm_semicircle_le_div {r : ℝ} (hr : 0 < r) :
    ‖semicircle r‖ ≤ Real.pi / r * (1 - Real.exp (-r)) := by
  have hpi := Real.pi_pos
  have hc : -(2 / Real.pi * r) ≠ 0 := by
    have : 0 < 2 / Real.pi * r := by positivity
    exact neg_ne_zero.2 this.ne'
  have h1 : ∫ θ in (0 : ℝ)..Real.pi / 2, Real.exp (-(r * Real.sin θ)) ≤
      ∫ θ in (0 : ℝ)..Real.pi / 2, Real.exp (-(2 / Real.pi * r) * θ) := by
    refine intervalIntegral.integral_mono_on (by positivity)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun θ hθ => Real.exp_le_exp.2 ?_
    have h := mul_le_mul_of_nonneg_left (Real.mul_le_sin hθ.1 hθ.2) hr.le
    linarith
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp, mul_zero, Real.exp_zero,
    show -(2 / Real.pi * r) * (Real.pi / 2) = -r by field_simp, smul_eq_mul] at h1
  refine (norm_semicircle_le r).trans ((mul_le_mul_of_nonneg_left h1 zero_le_two).trans_eq ?_)
  field_simp
  ring

private theorem norm_semicircle_le_pi {r : ℝ} (hr : 0 ≤ r) : ‖semicircle r‖ ≤ Real.pi := by
  rcases hr.eq_or_lt with rfl | hr
  · refine (norm_semicircle_le 0).trans_eq ?_
    simp
    ring
  · refine (norm_semicircle_le_div hr).trans ?_
    have h : 1 - Real.exp (-r) ≤ r := by linarith [Real.add_one_le_exp (-r)]
    calc Real.pi / r * (1 - Real.exp (-r)) ≤ Real.pi / r * r := by
          have := Real.pi_pos
          gcongr
      _ = Real.pi := div_mul_cancel₀ _ hr.ne'

private theorem hilbertSymbol_eq {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (ξ : ℝ) :
    (hilbertSymbol ε R ξ : ℂ) = (Real.pi : ℂ)⁻¹ *
      (semicircle (2 * Real.pi * |ξ| * ε) - semicircle (2 * Real.pi * |ξ| * R)) := by
  rw [← two_mul_integral_sin_div _ hε hR, hilbertSymbol]
  push_cast
  ring

/-- HNVW I, Lemma 5.2.1: `|m_{ε,R}| ≤ 2`. -/
theorem abs_hilbertSymbol_le {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (ξ : ℝ) :
    |hilbertSymbol ε R ξ| ≤ 2 := by
  have hpi := Real.pi_pos
  have hR : 0 < R := hε.trans_le hεR
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hilbertSymbol_eq hε hR, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hpi.le, ← div_eq_inv_mul, div_le_iff₀ hpi, two_mul]
  exact (norm_sub_le _ _).trans (add_le_add (norm_semicircle_le_pi (by positivity))
    (norm_semicircle_le_pi (by positivity)))

private theorem tendsto_semicircle_zero : Tendsto semicircle (𝓝 0) (𝓝 (Real.pi : ℂ)) := by
  have hcont : Continuous semicircle :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  have h0 : semicircle 0 = Real.pi := by
    simp [semicircle]
    ring
  rw [← h0]
  exact hcont.tendsto 0

private theorem tendsto_semicircle_atTop : Tendsto semicircle atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun r : ℝ => Real.pi / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ h
  filter_upwards [eventually_gt_atTop 0] with r hr
  refine (norm_semicircle_le_div hr).trans ?_
  have := Real.pi_pos
  exact mul_le_of_le_one_right (by positivity) (by linarith [Real.exp_pos (-r)])

/-- HNVW I, Lemma 5.2.1: `m_{ε,R} (ξ) → 1` as `ε → 0` and `R → ∞`, `ξ ≠ 0`. -/
theorem tendsto_hilbertSymbol {ξ : ℝ} (hξ : ξ ≠ 0) :
    Tendsto (fun z : ℝ × ℝ => hilbertSymbol z.1 z.2 ξ) (𝓝[>] 0 ×ˢ atTop) (𝓝 1) := by
  have hc : 0 < 2 * Real.pi * |ξ| := by
    have := Real.pi_pos
    have := abs_pos.2 hξ
    positivity
  have h1 : Tendsto (fun z : ℝ × ℝ => semicircle (2 * Real.pi * |ξ| * z.1)) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (Real.pi : ℂ)) := by
    refine tendsto_semicircle_zero.comp ?_
    have h : Tendsto (fun z : ℝ × ℝ => z.1) (𝓝[>] (0 : ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) :=
      tendsto_fst.mono_right nhdsWithin_le_nhds
    simpa using h.const_mul (2 * Real.pi * |ξ|)
  have h2 : Tendsto (fun z : ℝ × ℝ => semicircle (2 * Real.pi * |ξ| * z.2)) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 0) :=
    tendsto_semicircle_atTop.comp (tendsto_snd.const_mul_atTop hc)
  have h3 : Tendsto (fun z : ℝ × ℝ => ((hilbertSymbol z.1 z.2 ξ : ℝ) : ℂ)) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 ((1 : ℝ) : ℂ)) := by
    have h := (h1.sub h2).const_mul (Real.pi : ℂ)⁻¹
    rw [sub_zero, inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 Real.pi_ne_zero),
      ← Complex.ofReal_one] at h
    refine h.congr' ?_
    have he : ∀ᶠ z : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, 0 < z.1 ∧ 0 < z.2 :=
      (tendsto_fst.eventually self_mem_nhdsWithin).and
        (tendsto_snd.eventually (eventually_gt_atTop 0))
    filter_upwards [he] with z hz
    rw [hilbertSymbol_eq hz.1 hz.2]
  have h := (Complex.continuous_re.tendsto _).comp h3
  simpa [Function.comp_def] using h

/-! ### The truncated Hilbert transform as a Fourier multiplier -/

/-- HNVW I, Lemma 5.2.1: `∫_{ε < |x| < R} e^{−2πi x ξ} dx / x = −i π sgn (ξ) m_{ε,R} (ξ)`. -/
private theorem setIntegral_inv_mul_exp {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (ξ : ℝ) :
    ∫ z in {z : ℝ | ε < |z| ∧ |z| < R},
        ((z⁻¹ : ℝ) : ℂ) * Complex.exp (-(2 * Real.pi * ξ * z * Complex.I)) =
      Real.pi * (-Complex.I * (Real.sign ξ : ℂ) * (hilbertSymbol ε R ξ : ℂ)) := by
  set g : ℝ → ℂ := fun z => ((z⁻¹ : ℝ) : ℂ) * Complex.exp (-(2 * Real.pi * ξ * z * Complex.I))
  have hgm : Measurable g := by fun_prop
  have hgb : ∀ z, ε < |z| → ‖g z‖ ≤ ε⁻¹ := fun z hz => by
    have h1 : ‖Complex.exp (-(2 * Real.pi * ξ * z * Complex.I))‖ = 1 := by
      rw [show -(2 * Real.pi * ξ * z * Complex.I) =
        ((-(2 * Real.pi * ξ * z) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    simp only [g]
    rw [norm_mul, h1, mul_one, Complex.norm_real, norm_inv, Real.norm_eq_abs]
    exact inv_anti₀ hε hz.le
  have hset : {z : ℝ | ε < |z| ∧ |z| < R} = Set.Ioo ε R ∪ Set.Ioo (-R) (-ε) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioo]
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
      exact ⟨fun h => Or.inl h, fun h => h.elim id fun h => by exfalso; linarith [h.2]⟩
    · rw [abs_of_nonpos hz]
      exact ⟨fun h => Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩, fun h => h.elim
        (fun h => by exfalso; linarith [h.1]) fun h => ⟨by linarith [h.2], by linarith [h.1]⟩⟩
  have hi1 : IntegrableOn g (Set.Ioo ε R) := by
    refine Measure.integrableOn_of_bounded (M := ε⁻¹) (by simp) hgm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hgb z (hz.1.trans_le (le_abs_self z))
  have hi2 : IntegrableOn g (Set.Ioo (-R) (-ε)) := by
    refine Measure.integrableOn_of_bounded (M := ε⁻¹) (by simp) hgm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hgb z ((by linarith [hz.2] : ε < -z).trans_le (neg_le_abs z))
  have hdisj : Disjoint (Set.Ioo ε R) (Set.Ioo (-R) (-ε)) := by
    rw [Set.disjoint_left]
    intro z h1 h2
    linarith [h1.1, h2.2]
  have hii1 : IntervalIntegrable g volume ε R := by
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hεR]
  have hii2 : IntervalIntegrable (fun z => g (-z)) volume ε R := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hεR]
    refine Measure.integrableOn_of_bounded (M := ε⁻¹) (by simp)
      (hgm.comp measurable_neg).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hgb _ (by rw [abs_neg]; exact hz.1.trans_le (le_abs_self z))
  have hsum : ∀ z : ℝ, g z + g (-z) = (-2 * Complex.I * (Real.sign ξ : ℂ)) *
      ((Real.sin (2 * Real.pi * |ξ| * z) / z : ℝ) : ℂ) := by
    intro z
    have hsin : Real.sin (2 * Real.pi * ξ * z) =
        Real.sign ξ * Real.sin (2 * Real.pi * |ξ| * z) := by
      rcases lt_trichotomy ξ 0 with h | rfl | h
      · rw [Real.sign_of_neg h, abs_of_neg h, neg_one_mul, ← Real.sin_neg]
        ring_nf
      · simp
      · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]
    have h := Complex.two_sin (2 * Real.pi * ξ * z)
    have hsin' := congrArg (fun r : ℝ => (r : ℂ)) hsin
    simp only [g]
    push_cast at hsin' ⊢
    rw [neg_mul] at h
    rw [show -(2 * (Real.pi : ℂ) * ξ * -(z : ℂ) * Complex.I) = 2 * Real.pi * ξ * z * Complex.I by
      ring, inv_neg, div_eq_mul_inv]
    linear_combination (-2 * Complex.I * (z : ℂ)⁻¹) * hsin' + (Complex.I * (z : ℂ)⁻¹) * h +
      (z : ℂ)⁻¹ * (Complex.exp (-(2 * Real.pi * ξ * z * Complex.I)) -
        Complex.exp (2 * Real.pi * ξ * z * Complex.I)) * Complex.I_sq
  rw [hset, setIntegral_union hdisj measurableSet_Ioo hi1 hi2, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hεR,
    ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_comp_neg,
    ← intervalIntegral.integral_add hii1 hii2]
  simp_rw [hsum]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hilbertSymbol]
  push_cast
  field_simp

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

private theorem truncatedHilbert_eq (ε R : ℝ) (f : ℝ → X) (x : ℝ) :
    truncatedHilbert ε R f x =
      Real.pi⁻¹ • ∫ z in {z : ℝ | ε < |z| ∧ |z| < R}, z⁻¹ • f (x - z) := by
  have hS : MeasurableSet {z : ℝ | ε < |z| ∧ |z| < R} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hSx : MeasurableSet {y | ε < |x - y| ∧ |x - y| < R} :=
    (measurable_const_sub x) hS
  rw [truncatedHilbert, ← integral_indicator hS, ← integral_indicator hSx,
    ← integral_sub_left_eq_self ({z : ℝ | ε < |z| ∧ |z| < R}.indicator
      fun z => z⁻¹ • f (x - z)) volume x]
  congr 2
  funext y
  by_cases h : ε < |x - y| ∧ |x - y| < R <;> simp [h]

/-- HNVW I, Lemma 5.2.1: the truncated Hilbert transform as a Fourier multiplier. -/
theorem truncatedHilbert_fourierInv {G : ℝ → X} (hG : Integrable G) {ε R : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ R) :
    truncatedHilbert ε R (𝓕⁻ G) =
      𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ) * (hilbertSymbol ε R ξ : ℂ)) • G ξ := by
  funext x
  by_cases hX : CompleteSpace X
  swap
  · simp [truncatedHilbert, Real.fourierInv_eq', integral, hX]
  set S : Set ℝ := {z : ℝ | ε < |z| ∧ |z| < R}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hSfin : volume S ≠ ⊤ := by
    refine ((measure_mono (?_ : S ⊆ Set.Icc (-R) R)).trans_lt (by simp)).ne
    exact fun z hz => abs_le.1 hz.2.le
  have hinv : IntegrableOn (fun z : ℝ => ((z⁻¹ : ℝ) : ℂ)) S := by
    refine Measure.integrableOn_of_bounded (M := ε⁻¹) hSfin
      (by fun_prop : Measurable fun z : ℝ => ((z⁻¹ : ℝ) : ℂ)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hS] with z hz
    rw [Complex.norm_real, norm_inv]
    exact inv_anti₀ hε hz.1.le
  have hint : Integrable (Function.uncurry fun z v : ℝ =>
      (((z⁻¹ : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * (v * (x - z)) : ℝ) : ℂ) * Complex.I)) • G v)
      ((volume.restrict S).prod volume) := by
    have h := (hinv.smul_prod hG).bdd_smul 1 (φ := fun p : ℝ × ℝ =>
      Complex.exp (((2 * Real.pi * (p.2 * (x - p.1)) : ℝ) : ℂ) * Complex.I))
      (by fun_prop : Continuous fun p : ℝ × ℝ => Complex.exp
        (((2 * Real.pi * (p.2 * (x - p.1)) : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
      (ae_of_all _ fun p => (Complex.norm_exp_ofReal_mul_I _).le)
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [Pi.smul_apply', Function.uncurry, smul_smul]
    rw [mul_comm]
  have h1 : ∫ z in S, z⁻¹ • 𝓕⁻ G (x - z) = ∫ v, (∫ z in S, ((z⁻¹ : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (v * (x - z)) : ℝ) : ℂ) * Complex.I)) • G v := by
    have h2 : ∀ z : ℝ, z⁻¹ • 𝓕⁻ G (x - z) = ∫ v, (((z⁻¹ : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (v * (x - z)) : ℝ) : ℂ) * Complex.I)) • G v := fun z => by
      rw [Real.fourierInv_eq', ← Complex.coe_smul, ← integral_smul]
      simp only [smul_smul]
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      simp [mul_comm]
    simp_rw [h2]
    rw [integral_integral_swap hint]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only
    rw [integral_smul_const]
  have h3 : ∀ v : ℝ, ∫ z in S, ((z⁻¹ : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (v * (x - z)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * (v * x) : ℝ) : ℂ) * Complex.I) *
        (Real.pi * (-Complex.I * (Real.sign v : ℂ) * (hilbertSymbol ε R v : ℂ))) := fun v => by
    rw [← setIntegral_inv_mul_exp hε hεR, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [mul_left_comm (Complex.exp _), ← Complex.exp_add]
    push_cast
    ring_nf
  rw [truncatedHilbert_eq, h1, Real.fourierInv_eq', ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [h3, ← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  rw [mul_comm (x : ℂ) v]
  field_simp

/-! ### The Hilbert transform on UMD spaces -/

/-- The bound for the Hilbert transform in terms of a `UMD_p` constant. -/
noncomputable def hilbertBound (β : ℝ≥0∞) : ℝ≥0∞ := 4 * β ^ 2 + 11

private theorem measurable_sign : Measurable Real.sign :=
  Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

private theorem abs_sign_le (ξ : ℝ) : |Real.sign ξ| ≤ 1 := by
  rcases Real.sign_apply_eq ξ with h | h | h <;> simp [h]

private theorem continuous_fourierInv {G : ℝ → X} (hG : Integrable G) : Continuous (𝓕⁻ G) := by
  have h : Continuous (𝓕 G) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hG
  rw [show 𝓕⁻ G = fun x => 𝓕 G (-x) from funext fun x => Real.fourierInv_eq_fourier_neg G x]
  exact h.comp continuous_neg

private theorem measurable_hilbertSymbol (ε R : ℝ) : Measurable (hilbertSymbol ε R) := by
  refine measurable_const.mul ?_
  have h : StronglyMeasurable (Function.uncurry fun ξ x : ℝ =>
      Real.sin (2 * Real.pi * |ξ| * x) / x) :=
    (by fun_prop : Measurable (Function.uncurry fun ξ x : ℝ =>
      Real.sin (2 * Real.pi * |ξ| * x) / x)).stronglyMeasurable
  simp_rw [intervalIntegral]
  exact (h.integral_prod_right.sub h.integral_prod_right).measurable

/-- Bounded measurable multipliers act on `L¹`. -/
private theorem integrable_symbol_smul {G : ℝ → X} (hG : Integrable G) {m : ℝ → ℂ}
    (hm : Measurable m) {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C) : Integrable fun ξ => m ξ • G ξ :=
  hG.bdd_smul C hm.aestronglyMeasurable (ae_of_all _ hC)

/-- **The Hilbert transform on UMD spaces** (HNVW I, Theorem 5.1.13 and Lemma 5.2.1): the Fourier
multiplier `sgn` is bounded on `L^p (ℝ; X)`, `1 < p < ∞`. -/
theorem eLpNorm_fourierInv_sign_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hsm : Measurable fun ξ => (Real.sign ξ : ℂ) :=
    Complex.measurable_ofReal.comp measurable_sign
  -- the truncations `ε_i = 2^{−i}`, `R_i = 2^i = 2^{2i} ε_i`
  set ε : ℕ → ℝ := fun i => (2 ^ i)⁻¹
  have hε : ∀ i, 0 < ε i := fun i => by positivity
  have hεR : ∀ i, ε i ≤ 2 ^ (2 * i) * ε i := fun i =>
    le_mul_of_one_le_left (hε i).le (one_le_pow₀ one_le_two)
  set m : ℕ → ℝ → ℂ := fun i ξ => -Complex.I * (Real.sign ξ : ℂ) *
    (hilbertSymbol (ε i) (2 ^ (2 * i) * ε i) ξ : ℂ)
  have hmm : ∀ i, Measurable (m i) := fun i => (measurable_const.mul hsm).mul
    (Complex.measurable_ofReal.comp (measurable_hilbertSymbol _ _))
  have hmb : ∀ i ξ, ‖m i ξ‖ ≤ 2 := fun i ξ => by
    simp only [m]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_mul (abs_sign_le ξ) (abs_hilbertSymbol_le (hε i) (hεR i) ξ) (abs_nonneg _)
      zero_le_one).trans_eq (one_mul 2)
  have hmlim : ∀ ξ, Tendsto (fun i => m i ξ) atTop (𝓝 (-Complex.I * (Real.sign ξ : ℂ))) := by
    intro ξ
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp [m]
    have hpair : Tendsto (fun i => (ε i, 2 ^ (2 * i) * ε i)) atTop (𝓝[>] 0 ×ˢ atTop) := by
      have hR : ∀ i, 2 ^ (2 * i) * ε i = (2 : ℝ) ^ i := fun i => by
        simp only [ε]
        rw [two_mul, pow_add, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
      have hpow : Tendsto (fun i : ℕ => (2 : ℝ) ^ i) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt one_lt_two
      simp_rw [hR]
      exact (tendsto_nhdsWithin_iff.2 ⟨hpow.inv_tendsto_atTop, Eventually.of_forall hε⟩).prodMk hpow
    have h := ((tendsto_hilbertSymbol hξ).comp hpair).ofReal.const_mul
      (-Complex.I * (Real.sign ξ : ℂ))
    simpa [m, Function.comp_def] using h
  -- dominated convergence
  have hlim : ∀ x, Tendsto (fun i => 𝓕⁻ (fun ξ => m i ξ • G ξ) x) atTop
      (𝓝 (𝓕⁻ (fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) x)) := by
    intro x
    simp only [Real.fourierInv_eq']
    refine tendsto_integral_of_dominated_convergence (fun ξ => 2 * ‖G ξ‖) (fun i => ?_)
      (hG.norm.const_mul 2) (fun i => ae_of_all _ fun ξ => ?_) (ae_of_all _ fun ξ => ?_)
    · refine AEStronglyMeasurable.smul
        (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      exact (integrable_symbol_smul hG (hmm i) (hmb i)).aestronglyMeasurable
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_smul]
      exact mul_le_mul_of_nonneg_right (hmb i ξ) (norm_nonneg _)
    · exact ((hmlim ξ).smul_const _).const_smul _
  have hcont : ∀ i, Continuous (𝓕⁻ fun ξ => m i ξ • G ξ) := fun i =>
    continuous_fourierInv (integrable_symbol_smul hG (hmm i) (hmb i))
  have hsym : Integrable fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ :=
    integrable_symbol_smul hG (measurable_const.mul hsm) (C := 1) fun ξ => by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real]
      exact abs_sign_le ξ
  -- the bound for the truncations
  have hbound : ∀ i, eLpNorm (𝓕⁻ fun ξ => m i ξ • G ξ) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
    intro i
    rw [← truncatedHilbert_fourierInv hG (hε i) (hεR i)]
    exact eLpNorm_truncatedHilbert_le hp hβ hf (continuous_fourierInv hG).stronglyMeasurable (hε i)
      (2 * i)
  -- Fatou's lemma
  have hfatou := (Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p) (μ := volume)
    (fun i => (hcont i).aestronglyMeasurable) _ (continuous_fourierInv hsym).aestronglyMeasurable
    (ae_of_all _ hlim)).trans ((liminf_le_liminf (Eventually.of_forall hbound)).trans
      (liminf_const _).le)
  -- the unimodular constant
  have hconst : (𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) =
      (-Complex.I) • 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G ξ := by
    funext x
    rw [Pi.smul_apply, Real.fourierInv_eq', Real.fourierInv_eq', ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [smul_smul]
    congr 1
    ring
  rw [hconst, eLpNorm_const_smul, enorm_neg, ← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one,
    one_mul] at hfatou
  exact hfatou

end VectorValuedHarmonicAnalysis
