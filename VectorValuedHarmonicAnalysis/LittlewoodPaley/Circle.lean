module

public import VectorValuedHarmonicAnalysis.LittlewoodPaley.Line
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The Littlewood–Paley inequality on the circle for UMD spaces

`𝕋 = ℝ / ℤ` with its normalised Haar measure, `e_n (t) = e^{2πi n t}`. For a trigonometric
polynomial `f = Σ_n c_n e_n` (`trigPoly c`) with coefficients in a complex UMD space `X`, and the
dyadic blocks `Ĩ_0 = {0}`, `Ĩ_k = [2^{k−1}, 2^k) ∩ ℤ`, `Ĩ_{−k} = −Ĩ_k` for `k > 0` (`dyadicBlock`),
let
`Δ̃_k f = Σ_{n ∈ Ĩ_k} c_n e_n`. **Theorem** (`eLpNormRad_dyadicBlock_le`): for `1 < p < ∞`,

`‖Σ_{|k| ≤ K} ε_k Δ̃_k f‖_{L^p (Ω × 𝕋; X)} ≤ C_β ‖f‖_{L^p (𝕋; X)}`,

with a constant that depends only on a `UMD_p` constant `β` of `X`.

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), Theorem 5.7.10
(2), right-hand inequality, pp. 464–466: transference from the line (Proposition 5.7.1 and Lemma
5.7.3, pp. 458–459), with the dilation trick that moves the dyadic points off the lattice. The
left-hand inequality and the operator-valued statement (1) of that theorem are not treated.

Also: the projections onto single frequencies are randomised bounded
(`eLpNormRad_singleFrequency_le`), by the contraction principle.
-/

@[expose] public section

open MeasureTheory BanachProbability AddCircle
open scoped ENNReal FourierTransform

namespace VectorValuedHarmonicAnalysis

/-- The trigonometric polynomial `Σ_n c_n e_n` on `𝕋 = ℝ / ℤ`. -/
noncomputable def trigPoly {V : Type*} [AddCommMonoid V] [Module ℂ V] (c : ℤ →₀ V)
    (t : UnitAddCircle) : V :=
  c.sum fun n x => fourier n t • x

/-- The dyadic blocks of `ℤ` (HNVW I, p. 464): `Ĩ_0 = {0}`, `Ĩ_k = [2^{k−1}, 2^k)`,
`Ĩ_{−k} = (−2^k, −2^{k−1}]`, `k > 0`. -/
def dyadicBlock (k : ℤ) : Set ℤ :=
  if k = 0 then {0} else if 0 < k then Set.Ico (2 ^ (k.natAbs - 1)) (2 ^ k.natAbs)
  else Set.Ioc (-2 ^ k.natAbs) (-2 ^ (k.natAbs - 1))

open scoped Classical in
/-- `Δ̃_s f = Σ_{n ∈ s} c_n e_n`, for a set `s` of frequencies. -/
noncomputable def trigBlock {V : Type*} [AddCommMonoid V] [Module ℂ V] (s : Set ℤ) (c : ℤ →₀ V) :
    UnitAddCircle → V :=
  trigPoly (c.filter (· ∈ s))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem continuous_trigPoly (c : ℤ →₀ X) : Continuous (trigPoly c) := by
  unfold trigPoly Finsupp.sum
  exact continuous_finsetSum _ fun n _ => (map_continuous (fourier n)).smul continuous_const

private theorem norm_fourier_apply (n : ℤ) (t : UnitAddCircle) : ‖fourier n t‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- The Fourier coefficients of a trigonometric polynomial. -/
private theorem integral_fourier_smul_trigPoly [CompleteSpace X] (c : ℤ →₀ X) (n : ℤ) :
    ∫ t, fourier (-n) t • trigPoly c t ∂haarAddCircle = c n := by
  have hi : ∀ m : ℤ, Integrable (fun t : UnitAddCircle => fourier (-n) t • fourier m t • c m)
      haarAddCircle := fun m => ((map_continuous (fourier (-n))).smul
    ((map_continuous (fourier m)).smul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hterm : ∀ m : ℤ, ∫ t : UnitAddCircle, fourier (-n) t • fourier m t • c m ∂haarAddCircle =
      if n = m then c m else 0 := fun m => by
    have h := congrFun (fourierCoeff_fourier (T := 1) m) n
    rw [fourierCoeff, Pi.single_apply] at h
    simp only [smul_smul]
    simp only [smul_eq_mul] at h
    rw [integral_smul_const, h]
    split_ifs <;> simp
  simp only [trigPoly, Finsupp.sum, Finset.smul_sum]
  rw [integral_finsetSum _ fun m _ => hi m, Finset.sum_congr rfl fun m _ => hterm m,
    Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

/-! ### Averages of dilates of periodic functions -/

private theorem integrable_dilate_mul (g : C(UnitAddCircle, ℂ)) {w : ℝ → ℝ} (hw : Integrable w)
    (R : ℝ) : Integrable fun y : ℝ => g ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ) := by
  have hc : Continuous fun y : ℝ => g ((R * y : ℝ) : UnitAddCircle) :=
    (map_continuous g).comp ((AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id))
  exact hw.ofReal.bdd_smul ‖g‖ hc.aestronglyMeasurable (ae_of_all _ fun y => g.norm_coe_le_norm _)

private theorem norm_integral_dilate_le (g : C(UnitAddCircle, ℂ)) {w : ℝ → ℝ} (hw : Integrable w)
    (R : ℝ) : ‖∫ y : ℝ, g ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ)‖ ≤ ‖g‖ * ∫ y, ‖w y‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hw.norm.const_mul _) (ae_of_all _ fun y => ?_)
  rw [norm_mul, Complex.norm_real]
  gcongr
  exact g.norm_coe_le_norm _

/-- The Riemann–Lebesgue lemma for the character `e_n`. -/
private theorem tendsto_dilate_fourier {w : ℝ → ℝ} (n : ℤ) :
    Filter.Tendsto (fun R : ℝ => ∫ y : ℝ, fourier n ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ))
      Filter.atTop (nhds ((∫ t : UnitAddCircle, fourier n t ∂haarAddCircle) * ∫ y, (w y : ℂ))) := by
  have hcoef : ∫ t : UnitAddCircle, fourier n t ∂haarAddCircle = if n = 0 then 1 else 0 := by
    have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
    rw [fourierCoeff] at h
    simp only [neg_zero, fourier_zero, one_smul] at h
    rw [h, Pi.single_apply]
    simp only [eq_comm]
  rw [hcoef]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ite_eq_right hn, zero_mul]
    have h1 : ∀ R : ℝ, ∫ y : ℝ, fourier n ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ) =
        FourierTransform.fourier (fun y : ℝ => (w y : ℂ)) (-n * R) := fun R => by
      rw [Real.fourier_real_eq_integral_exp_smul]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [smul_eq_mul]
      rw [fourier_coe_apply]
      congr 2
      push_cast
      ring
    simp_rw [h1]
    refine (Real.zero_at_infty_fourier fun y : ℝ => (w y : ℂ)).comp ?_
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    have hn' : 0 < ‖(-n : ℝ)‖ := by simpa using hn
    simp only [norm_mul]
    exact tendsto_norm_atTop_atTop.const_mul_atTop hn'

/-- `∫ g (R y) w (y) dy → (∫_𝕋 g) (∫ w)` as `R → ∞`: the Riemann–Lebesgue lemma for the characters,
then linearity and uniform approximation. -/
private theorem tendsto_dilate_continuousMap {w : ℝ → ℝ} (hw : Integrable w)
    (g : C(UnitAddCircle, ℂ)) :
    Filter.Tendsto (fun R : ℝ => ∫ y : ℝ, g ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ))
      Filter.atTop (nhds ((∫ t, g t ∂haarAddCircle) * ∫ y, (w y : ℂ))) := by
  have hi : ∀ h : C(UnitAddCircle, ℂ), Integrable (fun t => h t) haarAddCircle := fun h =>
    h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- trigonometric polynomials
  have hspan : ∀ h ∈ Submodule.span ℂ (Set.range (@fourier 1)),
      Filter.Tendsto (fun R : ℝ => ∫ y : ℝ, h ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ))
        Filter.atTop (nhds ((∫ t, h t ∂haarAddCircle) * ∫ y, (w y : ℂ))) := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨n, rfl⟩ := hh
      exact tendsto_dilate_fourier n
    | zero => simp
    | add h₁ h₂ _ _ ih₁ ih₂ =>
      have h3 := ih₁.add ih₂
      simp only [← integral_add (integrable_dilate_mul _ hw _) (integrable_dilate_mul _ hw _),
        ← add_mul, ← integral_add (hi h₁) (hi h₂)] at h3
      exact h3
    | smul a h _ ih =>
      have e1 : ∀ R : ℝ, ∫ y : ℝ, (a • h) ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ) =
          a * ∫ y : ℝ, h ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ) := fun R => by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun y => mul_assoc _ _ _)
      have e2 : ∫ t, (a • h) t ∂haarAddCircle = a * ∫ t, h t ∂haarAddCircle :=
        integral_const_mul a _
      simp only [e1, e2, mul_assoc]
      exact ih.const_mul a
  -- uniform approximation
  have hW : 0 ≤ ∫ y, ‖w y‖ := integral_nonneg fun y => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set W := ∫ y, ‖w y‖
  have hg : g ∈ closure (Submodule.span ℂ (Set.range (@fourier 1)) : Set C(UnitAddCircle, ℂ)) := by
    have h := span_fourier_closure_eq_top (T := 1)
    rw [← Submodule.topologicalClosure_coe, h]
    trivial
  obtain ⟨h, hh, hgh⟩ := Metric.mem_closure_iff.1 hg (δ / (4 * (W + 1))) (by positivity)
  rw [dist_eq_norm] at hgh
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.1 (hspan h hh) (δ / 2) (by positivity)
  have hwn : ‖∫ y, (w y : ℂ)‖ ≤ W := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp [W]
  have hsmall : ‖g - h‖ * W ≤ δ / 4 := by
    calc ‖g - h‖ * W ≤ δ / (4 * (W + 1)) * (W + 1) := by
          gcongr
          linarith
      _ = δ / 4 := by field_simp
  refine ⟨R₀, fun R hR => ?_⟩
  have h1 : ‖(∫ y : ℝ, g ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ)) -
      ∫ y : ℝ, h ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ)‖ ≤ δ / 4 := by
    rw [← integral_sub (integrable_dilate_mul _ hw _) (integrable_dilate_mul _ hw _)]
    simp only [← sub_mul, ← ContinuousMap.sub_apply]
    exact (norm_integral_dilate_le _ hw _).trans hsmall
  have h2 : ‖(∫ t, h t ∂haarAddCircle) * (∫ y, (w y : ℂ)) -
      (∫ t, g t ∂haarAddCircle) * ∫ y, (w y : ℂ)‖ ≤ δ / 4 := by
    rw [← sub_mul, ← integral_sub (hi h) (hi g), norm_mul]
    refine le_trans (mul_le_mul ?_ hwn (norm_nonneg _) (norm_nonneg (g - h))) hsmall
    refine (norm_integral_le_of_norm_le_const (C := ‖g - h‖) (ae_of_all _ fun t => ?_)).trans ?_
    · rw [norm_sub_rev, ← ContinuousMap.sub_apply]
      exact (g - h).norm_coe_le_norm t
    · simp
  have h3 := hR₀ R hR
  rw [dist_eq_norm] at h3 ⊢
  calc _ = ‖((∫ y : ℝ, g ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ)) -
        ∫ y : ℝ, h ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ)) +
        ((∫ y : ℝ, h ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ)) -
          (∫ t, h t ∂haarAddCircle) * ∫ y, (w y : ℂ)) +
        ((∫ t, h t ∂haarAddCircle) * (∫ y, (w y : ℂ)) -
          (∫ t, g t ∂haarAddCircle) * ∫ y, (w y : ℂ))‖ := by
        congr 1
        ring
    _ < δ := by
        refine (norm_add₃_le).trans_lt ?_
        linarith

/-- HNVW I, Lemma 5.7.3: `ε ∫_ℝ ‖f (ρ x)‖^p |θ (ε x)|^p dx → ‖f‖_{L^p (𝕋)}^p ‖θ‖_{L^p (ℝ)}^p` as
`ε → 0⁺`, for a continuous `f` on `𝕋`, `ρ > 0` and an integrable `w = |θ|^p`.

Departure from the source: the book periodises the integral and uses that the Riemann sums
`ε Σ_k w (ε (x + k))` converge to `∫ w` uniformly in `x`, for a Schwartz function `w`. Here `w` is
only integrable, and the proof is by the Riemann–Lebesgue lemma for the characters `g = e_n`,
linearity, and uniform approximation of `g` by trigonometric polynomials. -/
theorem tendsto_integral_dilate {g : UnitAddCircle → ℝ} (hg : Continuous g) {w : ℝ → ℝ}
    (hw : Integrable w) {ρ : ℝ} (hρ : 0 < ρ) :
    Filter.Tendsto (fun ε : ℝ => ε * ∫ x : ℝ, g (ρ * x : ℝ) * w (ε * x)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∫ t, g t ∂haarAddCircle) * ∫ x, w x)) := by
  set g' : C(UnitAddCircle, ℂ) := ⟨fun t => (g t : ℂ), Complex.continuous_ofReal.comp hg⟩
  have h1 := tendsto_dilate_continuousMap hw g'
  have h2 : (∫ t, g' t ∂haarAddCircle) * ∫ y, (w y : ℂ) =
      (((∫ t, g t ∂haarAddCircle) * ∫ x, w x : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_complex_ofReal]
    rfl
  have h3 : ∀ R : ℝ, ∫ y : ℝ, g' ((R * y : ℝ) : UnitAddCircle) * (w y : ℂ) =
      ((∫ y : ℝ, g ((R * y : ℝ) : UnitAddCircle) * w y : ℝ) : ℂ) := fun R => by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp [g']
  simp only [h2, h3] at h1
  have h4 := (Complex.continuous_re.tendsto _).comp h1
  simp only [Function.comp_def, Complex.ofReal_re] at h4
  -- the substitution `x = y / ε`
  have h5 : Filter.Tendsto (fun ε : ℝ => ρ / ε) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop hρ
  refine (h4.comp h5).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have h6 := Measure.integral_comp_mul_left
    (fun y : ℝ => g ((ρ / ε * y : ℝ) : UnitAddCircle) * w y) ε
  have h7 : ∀ x : ℝ, ρ / ε * (ε * x) = ρ * x := fun x => by field_simp
  simp only [h7] at h6
  rw [Function.comp_apply, h6, abs_of_pos (inv_pos.2 hε'), smul_eq_mul,
    mul_inv_cancel_left₀ hε'.ne']

/-! ### Transference

HNVW I, Proposition 5.7.1 and the proof of Theorem 5.7.10. Departure from the source: the book pairs
`T_m (φ (ε ·) f)` with `ψ (ε ·) g`, `g` a trigonometric polynomial, for Schwartz functions `φ`, `ψ`
(Lemma 5.7.2). Here the cut-off `θ` has a compactly supported Fourier transform `η`; then, for small
`ε`, the multiplier `1_{I_k}` maps `θ (ε ·) f (ρ ·)` exactly to `θ (ε ·) (Δ̃_{k+1} f) (ρ ·)`, and
Lemma 5.7.3 is applied on both sides, without duality. -/

/-- The cut-off function: `η` is supported in `(−1, 1)` and `θ = 𝓕⁻ η` is a Schwartz function. -/
private theorem exists_cutoff {p : ℝ} (hp : 0 < p) : ∃ η : ℝ → ℂ, Integrable η ∧
    (∀ ξ, 1 ≤ |ξ| → η ξ = 0) ∧ Continuous (𝓕⁻ η) ∧ Integrable (fun x => ‖𝓕⁻ η x‖ ^ p) ∧
      0 < ∫ x, ‖𝓕⁻ η x‖ ^ p := by
  set b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hbs : HasCompactSupport fun x => (b x : ℂ) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  set η : SchwartzMap ℝ ℂ := hbs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hη : ∀ x, η x = (b x : ℂ) := fun x => rfl
  have hcoe : 𝓕⁻ (η : ℝ → ℂ) = ((𝓕⁻ η : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
    (SchwartzMap.fourierInv_coe η).symm
  have hcont : Continuous (𝓕⁻ (η : ℝ → ℂ)) := by
    rw [hcoe]
    exact (𝓕⁻ η : SchwartzMap ℝ ℂ).continuous
  have hLp : Integrable fun x => ‖𝓕⁻ (η : ℝ → ℂ) x‖ ^ p := by
    have h := ((𝓕⁻ η : SchwartzMap ℝ ℂ).memLp (ENNReal.ofReal p) volume).integrable_norm_rpow
      (by simpa using hp) ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hp.le] at h
    rw [hcoe]
    exact h
  refine ⟨η, η.integrable, fun ξ hξ => ?_, hcont, hLp, ?_⟩
  · rw [hη, b.zero_of_le_dist (by simpa using hξ), Complex.ofReal_zero]
  · rw [integral_pos_iff_support_of_nonneg (fun x => by positivity) hLp]
    have hne : ∃ x, 𝓕⁻ (η : ℝ → ℂ) x ≠ 0 := by
      by_contra! h
      have h0 : (𝓕⁻ η : SchwartzMap ℝ ℂ) = 0 := by
        ext x
        rw [← hcoe, h x]
        rfl
      have h1 : η = 0 := by
        have h2 : 𝓕 (𝓕⁻ η : SchwartzMap ℝ ℂ) = η := FourierTransform.fourier_fourierInv_eq η
        rw [← h2, h0, FourierTransform.fourier_zero]
      have h2 : η 0 = 1 := by
        rw [hη, b.one_of_mem_closedBall (by simp [b]), Complex.ofReal_one]
      rw [h1] at h2
      simp at h2
    obtain ⟨x, hx⟩ := hne
    have hopen : IsOpen (Function.support fun x => ‖𝓕⁻ (η : ℝ → ℂ) x‖ ^ p) :=
      (hcont.norm.rpow_const fun _ => Or.inr hp.le).isOpen_support
    exact hopen.measure_pos volume ⟨x, by
      simpa [Function.mem_support, Real.rpow_eq_zero (norm_nonneg _) hp.ne'] using hx⟩

private theorem fourierInv_eq_exp (G : ℝ → X) (x : ℝ) :
    𝓕⁻ G x = ∫ v, Complex.exp (((2 * Real.pi * (v * x) : ℝ) : ℂ) * Complex.I) • G v := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp [mul_comm]

/-- `G_ε (ξ) = Σ_j ε⁻¹ η ((ξ − ρ j) / ε) c_j`. -/
private noncomputable def bumpSum (η : ℝ → ℂ) (c : ℤ →₀ X) (ρ ε ξ : ℝ) : X :=
  c.sum fun j y => ((ε⁻¹ : ℝ) : ℂ) • η (ε⁻¹ * (ξ - ρ * j)) • y

private theorem integrable_bump {η : ℝ → ℂ} (hη : Integrable η) {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Integrable fun ξ => ((ε⁻¹ : ℝ) : ℂ) * η (ε⁻¹ * (ξ - a)) :=
  ((hη.comp_mul_left' (inv_ne_zero hε.ne')).comp_sub_right a).const_mul _

private theorem integrable_bumpSum {η : ℝ → ℂ} (hη : Integrable η) {ε : ℝ} (hε : 0 < ε)
    (c : ℤ →₀ X) (ρ : ℝ) : Integrable (bumpSum η c ρ ε) := by
  unfold bumpSum Finsupp.sum
  refine integrable_finsetSum _ fun j _ => ?_
  simp only [smul_smul]
  exact (integrable_bump hη hε (ρ * j)).smul_const (c j)

/-- `𝓕⁻ (ε⁻¹ η ((· − a) / ε)) (x) = e^{2πi a x} θ (ε x)`. -/
private theorem fourierInv_bump (η : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (a x : ℝ) :
    ∫ v, Complex.exp (((2 * Real.pi * (v * x) : ℝ) : ℂ) * Complex.I) *
      (((ε⁻¹ : ℝ) : ℂ) * η (ε⁻¹ * (v - a))) =
      𝓕⁻ η (ε * x) * Complex.exp (((2 * Real.pi * (a * x) : ℝ) : ℂ) * Complex.I) := by
  have h1 := integral_sub_right_eq_self (fun u : ℝ =>
    Complex.exp (((2 * Real.pi * ((u + a) * x) : ℝ) : ℂ) * Complex.I) *
      (((ε⁻¹ : ℝ) : ℂ) * η (ε⁻¹ * u))) (μ := volume) a
  have h2 := Measure.integral_comp_mul_left (fun z : ℝ =>
    Complex.exp (((2 * Real.pi * ((ε * z + a) * x) : ℝ) : ℂ) * Complex.I) *
      (((ε⁻¹ : ℝ) : ℂ) * η z)) ε⁻¹
  simp only [sub_add_cancel] at h1
  simp only [mul_inv_cancel_left₀ hε.ne', inv_inv, abs_of_pos hε] at h2
  rw [h1, h2, fourierInv_eq_exp, ← integral_mul_const, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul, Complex.real_smul]
  rw [show (((2 * Real.pi * ((ε * z + a) * x) : ℝ) : ℂ) * Complex.I) =
    ((2 * Real.pi * (z * (ε * x)) : ℝ) : ℂ) * Complex.I +
      ((2 * Real.pi * (a * x) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_add]
  have hε' : (ε : ℂ) ≠ 0 := by simpa using hε.ne'
  push_cast
  field_simp

/-- `𝓕⁻ G_ε (x) = θ (ε x) f (ρ x)`. -/
private theorem fourierInv_bumpSum [CompleteSpace X] {η : ℝ → ℂ} (hη : Integrable η) {ε : ℝ}
    (hε : 0 < ε) (c : ℤ →₀ X) (ρ x : ℝ) : 𝓕⁻ (bumpSum η c ρ ε) x =
      𝓕⁻ η (ε * x) • trigPoly c ((ρ * x : ℝ) : UnitAddCircle) := by
  have hterm : ∀ j : ℤ, ∫ v, Complex.exp (((2 * Real.pi * (v * x) : ℝ) : ℂ) * Complex.I) •
      ((ε⁻¹ : ℝ) : ℂ) • η (ε⁻¹ * (v - ρ * j)) • c j =
      𝓕⁻ η (ε * x) • fourier j ((ρ * x : ℝ) : UnitAddCircle) • c j := fun j => by
    simp only [smul_smul]
    rw [integral_smul_const, fourierInv_bump η hε, fourier_coe_apply]
    congr 3
    push_cast
    ring
  rw [fourierInv_eq_exp]
  simp only [bumpSum, trigPoly, Finsupp.sum, Finset.smul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => hterm j
  · intro j _
    have h := ((integrable_bump hη hε (ρ * j)).smul_const (c j)).bdd_smul 1
      (φ := fun v : ℝ => Complex.exp (((2 * Real.pi * (v * x) : ℝ) : ℂ) * Complex.I))
      (by fun_prop : Continuous fun v : ℝ =>
        Complex.exp (((2 * Real.pi * (v * x) : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
      (ae_of_all _ fun v => (Complex.norm_exp_ofReal_mul_I _).le)
    simpa only [Pi.smul_def', mul_smul] using h

/-- The dilation trick (HNVW I, p. 465): with `ρ = 1 + 1/(2N)`, for `|j| ≤ N` and `ξ` near `ρ j`,
`ξ ∈ (2^k, 2^{k+1})` if and only if `j ∈ Ĩ_{k+1}`. -/
private theorem mem_Ioo_iff_mem_dyadicBlock {N : ℕ} (hN : 1 ≤ N) {j : ℤ} (hj : |j| ≤ N) {ε ξ : ℝ}
    (hε : ε ≤ 1 / (2 * N)) (hξ : |ξ - (1 + 1 / (2 * N)) * j| < ε) (k : ℕ) :
    ξ ∈ Set.Ioo ((2 : ℝ) ^ k) (2 ^ (k + 1)) ↔ j ∈ dyadicBlock ((k : ℤ) + 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (le_abs_self j).trans hj
  have hblock : dyadicBlock ((k : ℤ) + 1) = Set.Ico (2 ^ k) (2 ^ (k + 1)) := by
    have h1 : ((k : ℤ) + 1).natAbs = k + 1 := by omega
    rw [dyadicBlock, ite_eq_right (by omega), ite_eq_left (by omega), h1, Nat.add_sub_cancel]
  have hd : (0 : ℝ) < 1 / (2 * N) := by positivity
  have hd2 : 1 / (2 * (N : ℝ)) ≤ 1 / 2 := by
    gcongr
    linarith
  have hdN : 1 / (2 * (N : ℝ)) * N = 1 / 2 := by field_simp
  rw [abs_lt] at hξ
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  rw [hblock, Set.mem_Ioo, Set.mem_Ico]
  rcases le_or_gt j 0 with hj0 | hj0
  · -- `ξ < 1`
    have hj0' : (j : ℝ) ≤ 0 := by exact_mod_cast hj0
    have h1 : (1 + 1 / (2 * (N : ℝ))) * j ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hj0'
    have h2 : (0 : ℤ) < 2 ^ k := by positivity
    exact ⟨fun h => by linarith [h.1, hξ.2], fun h => by linarith [h.1]⟩
  · -- `j < ξ < j + 1`
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj0
    have h1 : (j : ℝ) < ξ := by
      have h : 1 / (2 * (N : ℝ)) * 1 ≤ 1 / (2 * N) * j := by gcongr
      linarith [hξ.1]
    have h2 : ξ < j + 1 := by
      have h : 1 / (2 * (N : ℝ)) * j ≤ 1 / (2 * N) * N := by gcongr
      linarith [hξ.2]
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

open scoped Classical in
/-- `1_{I_k} G_ε` for small `ε`: the terms with `j ∈ Ĩ_{k+1}`. -/
private theorem indicator_bumpSum {η : ℝ → ℂ} (hη : ∀ ξ, 1 ≤ |ξ| → η ξ = 0) {N : ℕ} (hN : 1 ≤ N)
    {c : ℤ →₀ X} (hc : ∀ j ∈ c.support, |j| ≤ N) {ε : ℝ} (hε : 0 < ε) (hεN : ε ≤ 1 / (2 * N))
    (k : ℕ) :
    (Set.Ioo ((2 : ℝ) ^ k) (2 ^ (k + 1))).indicator (bumpSum η c (1 + 1 / (2 * N)) ε) =
      bumpSum η (c.filter (· ∈ dyadicBlock ((k : ℤ) + 1))) (1 + 1 / (2 * N)) ε := by
  funext ξ
  rw [bumpSum, Finsupp.sum_filter_index, Finsupp.support_filter, Finset.sum_filter,
    Set.indicator_apply, bumpSum, Finsupp.sum]
  have h1 : ∀ a : X, (if ξ ∈ Set.Ioo ((2 : ℝ) ^ k) (2 ^ (k + 1)) then a else 0) =
      (if ξ ∈ Set.Ioo ((2 : ℝ) ^ k) (2 ^ (k + 1)) then (1 : ℂ) else 0) • a := fun a => by
    split_ifs <;> simp
  rw [h1, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← h1]
  by_cases hξ : |ξ - (1 + 1 / (2 * N)) * j| < ε
  · simp only [mem_Ioo_iff_mem_dyadicBlock hN (hc j hj) hεN hξ k]
  · have h2 : η (ε⁻¹ * (ξ - (1 + 1 / (2 * N)) * j)) = 0 := by
      refine hη _ ?_
      rw [abs_mul, abs_of_pos (inv_pos.2 hε), ← div_eq_inv_mul, le_div_iff₀ hε, one_mul]
      exact not_lt.1 hξ
    rw [h2, zero_smul, smul_zero, ite_self, ite_self]

variable [CompleteSpace X]

omit [NormedSpace ℂ X] [CompleteSpace X] in
/-- `‖f‖_p^p = ∫ ‖f‖^p`. -/
private theorem eLpNorm_rpow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ} (hp : 0 < p)
    {f : α → X} (hf : AEStronglyMeasurable f μ) (hi : Integrable (fun x => ‖f x‖ ^ p) μ) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ENNReal.ofReal (∫ x, ‖f x‖ ^ p ∂μ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

omit [CompleteSpace X] in
private theorem integrable_dilate_rpow {p : ℝ} (hp : 0 < p) {θ : ℝ → ℂ}
    (hθ : Integrable fun x => ‖θ x‖ ^ p) {F : UnitAddCircle → X} (hF : Continuous F) (ρ : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable fun x => ‖θ (ε * x) • F ((ρ * x : ℝ) : UnitAddCircle)‖ ^ p := by
  have hc : Continuous fun t => ‖F t‖ ^ p := hF.norm.rpow_const fun _ => Or.inr hp.le
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hc' : Continuous fun x : ℝ => ‖F ((ρ * x : ℝ) : UnitAddCircle)‖ ^ p :=
    hc.comp ((AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id))
  refine ((hθ.comp_mul_left' hε.ne').bdd_smul C hc'.aestronglyMeasurable
    (ae_of_all _ fun x => hC _ ⟨_, rfl⟩)).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.smul_apply', smul_eq_mul]
  rw [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_comm]

omit [CompleteSpace X] in
private theorem continuous_dilate {θ : ℝ → ℂ} (hθ : Continuous θ) {F : UnitAddCircle → X}
    (hF : Continuous F) (ρ ε : ℝ) :
    Continuous fun x => θ (ε * x) • F ((ρ * x : ℝ) : UnitAddCircle) :=
  (hθ.comp (continuous_const.mul continuous_id)).smul
    (hF.comp ((AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id)))

omit [CompleteSpace X] in
/-- HNVW I, Lemma 5.7.3: `ε ‖θ (ε ·) F (ρ ·)‖_{L^p (ℝ)}^p → ‖F‖_{L^p (𝕋)}^p ‖θ‖_{L^p (ℝ)}^p`. -/
private theorem tendsto_eLpNorm_dilate {p : ℝ} (hp : 0 < p) {θ : ℝ → ℂ} (hθc : Continuous θ)
    (hθ : Integrable fun x => ‖θ x‖ ^ p) {F : UnitAddCircle → X} (hF : Continuous F) {ρ : ℝ}
    (hρ : 0 < ρ) :
    Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal ε * eLpNorm (fun x : ℝ =>
        θ (ε * x) • F ((ρ * x : ℝ) : UnitAddCircle)) (ENNReal.ofReal p) volume ^ p)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (eLpNorm F (ENNReal.ofReal p) haarAddCircle ^ p *
        ENNReal.ofReal (∫ x, ‖θ x‖ ^ p))) := by
  have hc : Continuous fun t => ‖F t‖ ^ p := hF.norm.rpow_const fun _ => Or.inr hp.le
  have hi : Integrable (fun t => ‖F t‖ ^ p) haarAddCircle :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [eLpNorm_rpow_eq hp hF.aestronglyMeasurable hi,
    ← ENNReal.ofReal_mul (integral_nonneg fun t => by positivity)]
  refine ((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_integral_dilate hc hθ hρ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  rw [eLpNorm_rpow_eq hp (continuous_dilate hθc hF ρ ε).aestronglyMeasurable
    (integrable_dilate_rpow hp hθ hF ρ hε'), ← ENNReal.ofReal_mul hε'.le, Function.comp_apply]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_comm]

omit [CompleteSpace X] in
/-- `ε ‖Σ_k ε_k θ (ε ·) F_k (ρ ·)‖^p → ‖Σ_k ε_k F_k‖^p ‖θ‖_p^p`. -/
private theorem tendsto_eLpNormRad_dilate {p : ℝ} (hp : 0 < p) {θ : ℝ → ℂ} (hθc : Continuous θ)
    (hθ : Integrable fun x => ‖θ x‖ ^ p) {K : ℕ} {F : Fin K → UnitAddCircle → X}
    (hF : ∀ k, Continuous (F k)) {ρ : ℝ} (hρ : 0 < ρ) :
    Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal ε * eLpNormRad (fun k (x : ℝ) =>
        θ (ε * x) • F k ((ρ * x : ℝ) : UnitAddCircle)) p volume ^ p)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (eLpNormRad F p haarAddCircle ^ p * ENNReal.ofReal (∫ x, ‖θ x‖ ^ p))) := by
  have hsum : ∀ s : Fin K → Bool, Continuous fun t => ∑ k, SignCube.coin (s k) • F k t := fun s =>
    continuous_finsetSum _ fun k _ => (hF k).const_smul _
  have h1 := tendsto_finsetSum Finset.univ fun s (_ : s ∈ (Finset.univ : Finset (Fin K → Bool))) =>
    tendsto_eLpNorm_dilate hp hθc hθ (hsum s) hρ
  have h2 := ENNReal.Tendsto.const_mul (a := ((2 : ℝ≥0∞) ^ K)⁻¹) h1 (Or.inr (by simp))
  rw [eLpNormRad_rpow hp fun k => (hF k).aestronglyMeasurable, mul_assoc, Finset.sum_mul]
  refine h2.congr fun ε => ?_
  rw [eLpNormRad_rpow hp fun k => (continuous_dilate hθc (hF k) ρ ε).aestronglyMeasurable,
    mul_left_comm (ENNReal.ofReal ε), Finset.mul_sum (a := ENNReal.ofReal ε)]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 3
  funext x
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

/-- A trigonometric polynomial with a nonzero coefficient has a nonzero norm. -/
private theorem eLpNorm_trigPoly_ne_zero {p : ℝ} (hp : 0 < p) {c : ℤ →₀ X}
    (hc : c ≠ 0) : eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle ≠ 0 := by
  intro h
  rw [eLpNorm_eq_zero_iff (by simpa using hp),
    (continuous_trigPoly c).ae_eq_iff_eq _ continuous_zero] at h
  refine hc (Finsupp.ext fun n => ?_)
  rw [← integral_fourier_smul_trigPoly c n, h]
  simp

/-- The Littlewood–Paley inequality on `𝕋` for the blocks `Ĩ_{k+1} = [2^k, 2^{k+1})`, `0 ≤ k < K`.
-/
theorem eLpNormRad_dyadicBlock_succ_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun k : Fin K => trigBlock (dyadicBlock ((k : ℕ) + 1)) c) p haarAddCircle ≤
      littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle := by
  have hp0 : 0 < p := by linarith
  obtain ⟨η, hη, hη1, hθc, hθ, hθ0⟩ := exists_cutoff hp0
  set θ : ℝ → ℂ := 𝓕⁻ η
  -- the dilation
  obtain ⟨N, hN, hc⟩ : ∃ N : ℕ, 1 ≤ N ∧ ∀ j ∈ c.support, |j| ≤ N := by
    refine ⟨c.support.sup Int.natAbs + 1, by omega, fun j hj => ?_⟩
    have h := Finset.le_sup (f := Int.natAbs) hj
    rw [Int.abs_eq_natAbs]
    omega
  set ρ : ℝ := 1 + 1 / (2 * N)
  have hρ : 0 < ρ := by positivity
  have hδ : (0 : ℝ) < 1 / (2 * N) := by positivity
  set B : Fin K → UnitAddCircle → X := fun k => trigBlock (dyadicBlock ((k : ℕ) + 1)) c
  have hB : ∀ k, Continuous (B k) := fun k => continuous_trigPoly _
  -- the inequality on the line
  have hline : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (2 * N) →
      eLpNormRad (fun k (x : ℝ) => θ (ε * x) • B k ((ρ * x : ℝ) : UnitAddCircle)) p volume ≤
        littlewoodPaleyBound β * eLpNorm (fun x : ℝ =>
          θ (ε * x) • trigPoly c ((ρ * x : ℝ) : UnitAddCircle)) (ENNReal.ofReal p) volume := by
    intro ε hε hεN
    have hG := integrable_bumpSum hη hε c ρ
    have hinv : 𝓕⁻ (bumpSum η c ρ ε) =
        fun x : ℝ => θ (ε * x) • trigPoly c ((ρ * x : ℝ) : UnitAddCircle) :=
      funext fun x => fourierInv_bumpSum hη hε c ρ x
    have hmem : MemLp (𝓕⁻ (bumpSum η c ρ ε)) (ENNReal.ofReal p) volume := by
      rw [hinv, ← integrable_norm_rpow_iff
        (continuous_dilate hθc (continuous_trigPoly c) ρ ε).aestronglyMeasurable
        (by simpa using hp0) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
      exact integrable_dilate_rpow hp0 hθ (continuous_trigPoly c) ρ hε
    have h := eLpNormRad_fourierInv_indicator_le hp hβ hG hmem K
    have hblock : (fun k : Fin K => 𝓕⁻ ((Set.Ioo ((2 : ℝ) ^ (k : ℕ)) (2 ^ ((k : ℕ) + 1))).indicator
        (bumpSum η c ρ ε))) =
        fun k (x : ℝ) => θ (ε * x) • B k ((ρ * x : ℝ) : UnitAddCircle) := by
      funext k x
      rw [indicator_bumpSum hη1 hN hc hε hεN, fourierInv_bumpSum hη hε]
      rfl
    rwa [hblock, hinv] at h
  -- the limit `ε → 0`
  rcases eq_or_ne c 0 with rfl | hc0
  · have hzero : B = fun k => 0 := by
      funext k t
      simp only [B, trigBlock, trigPoly]
      rw [Finsupp.filter_zero, Finsupp.sum_zero_index]
      rfl
    have h0 : eLpNormRad B p haarAddCircle = 0 := by
      rw [hzero, eLpNormRad]
      simp
    rw [h0]
    exact zero_le
  set W := ENNReal.ofReal (∫ x, ‖θ x‖ ^ p)
  have hW : W ≠ 0 := by simpa [W] using hθ0
  have hlim1 := tendsto_eLpNormRad_dilate hp0 hθc hθ hB hρ
  have hlim2 := ENNReal.Tendsto.const_mul (a := littlewoodPaleyBound β ^ p)
    (tendsto_eLpNorm_dilate hp0 hθc hθ (continuous_trigPoly c) hρ)
    (Or.inl (mul_ne_zero (by simp [ENNReal.rpow_eq_zero_iff, hp0, hp0.not_gt,
      eLpNorm_trigPoly_ne_zero hp0 hc0]) hW))
  have hle := le_of_tendsto_of_tendsto hlim1 hlim2 (by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)]
      with ε hε hεN
    rw [mul_left_comm, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    gcongr
    exact hline ε hε (le_of_lt hεN))
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hW ENNReal.ofReal_ne_top,
    ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.rpow_le_rpow_iff hp0] at hle
  exact hle

/-! ### The whole Littlewood–Paley inequality -/

omit [NormedSpace ℂ X] [CompleteSpace X] in
/-- A bound that holds for every choice of signs. -/
private theorem eLpNormRad_le_of_forall_le [NormedSpace ℝ X] {p : ℝ} (hp : 0 < p) {K : ℕ}
    {f : Fin K → UnitAddCircle → X} (hf : ∀ k, Continuous (f k)) {C : ℝ≥0∞}
    (h : ∀ ε : Fin K → Bool, eLpNorm (fun t => ∑ k, SignCube.coin (ε k) • f k t)
      (ENNReal.ofReal p) haarAddCircle ≤ C) : eLpNormRad f p haarAddCircle ≤ C := by
  rw [← ENNReal.rpow_le_rpow_iff hp, eLpNormRad_rpow hp fun k => (hf k).aestronglyMeasurable]
  calc _ ≤ ((2 : ℝ≥0∞) ^ K)⁻¹ * ∑ _ε : Fin K → Bool, C ^ p := by
        gcongr with ε
        exact h ε
    _ = C ^ p := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, Nat.cast_pow, Nat.cast_ofNat,
          ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

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

omit [NormedSpace ℂ X] [CompleteSpace X] in
/-- Reflections preserve the norms. -/
private theorem eLpNorm_comp_neg (p : ℝ≥0∞) {g : UnitAddCircle → X} (hg : Continuous g) :
    eLpNorm (fun t => g (-t)) p haarAddCircle = eLpNorm g p haarAddCircle :=
  eLpNorm_comp_measurePreserving hg.aestronglyMeasurable (Measure.measurePreserving_neg _)

/-- The coefficients of `f (−·)`. -/
private noncomputable def reflect (c : ℤ →₀ X) : ℤ →₀ X := c.equivMapDomain (Equiv.neg ℤ)

omit [CompleteSpace X] in
private theorem trigPoly_reflect (c : ℤ →₀ X) (t : UnitAddCircle) :
    trigPoly (reflect c) t = trigPoly c (-t) := by
  rw [trigPoly, trigPoly, reflect, Finsupp.sum_equivMapDomain]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Equiv.neg_apply, fourier_apply, neg_smul, smul_neg]

private theorem mem_dyadicBlock_neg (m n : ℤ) : n ∈ dyadicBlock (-m) ↔ -n ∈ dyadicBlock m := by
  rcases lt_trichotomy m 0 with h | rfl | h
  · rw [dyadicBlock, dyadicBlock, ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), Int.natAbs_neg, Set.mem_Ico, Set.mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · simp [dyadicBlock]
  · rw [dyadicBlock, dyadicBlock, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), Int.natAbs_neg, Set.mem_Ico, Set.mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

omit [CompleteSpace X] in
private theorem trigBlock_neg (m : ℤ) (c : ℤ →₀ X) (t : UnitAddCircle) :
    trigBlock (dyadicBlock (-m)) c t = trigBlock (dyadicBlock m) (reflect c) (-t) := by
  classical
  have h : (reflect c).filter (· ∈ dyadicBlock m) =
      reflect (c.filter (· ∈ dyadicBlock (-m))) := by
    ext n
    simp only [reflect, Finsupp.filter_apply, Finsupp.equivMapDomain_apply, mem_dyadicBlock_neg,
      Equiv.neg_symm, Equiv.neg_apply, neg_neg]
  rw [trigBlock, trigBlock, h, trigPoly_reflect, neg_neg]

omit [CompleteSpace X] in
private theorem trigBlock_zero (c : ℤ →₀ X) (t : UnitAddCircle) :
    trigBlock (dyadicBlock 0) c t = c 0 := by
  classical
  have h : c.filter (· ∈ dyadicBlock 0) = Finsupp.single 0 (c 0) := by
    ext n
    simp only [dyadicBlock, Finsupp.filter_apply, Finsupp.single_apply]
    simp only [ite_true, Set.mem_singleton_iff, eq_comm (a := (0 : ℤ))]
    split_ifs with hn
    · rw [hn]
    · rfl
  rw [trigBlock, h, trigPoly, Finsupp.sum_single_index (h := fun n x => fourier n t • x)
    (smul_zero _), fourier_zero, one_smul]

/-- The positive blocks: a permutation of the indices brings them to `Ĩ_1, …, Ĩ_K`. -/
private theorem eLpNormRad_dyadicBlock_pos_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad ({k : Fin (2 * K + 1) | K < (k : ℕ)}.indicator
        fun k => trigBlock (dyadicBlock ((k : ℕ) - K)) c) p haarAddCircle ≤
      littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle := by
  set g : Fin (2 * K + 1) → UnitAddCircle → X := fun j =>
    trigBlock (dyadicBlock ((j : ℕ) + 1)) c
  have hg : ∀ j, AEStronglyMeasurable (g j) haarAddCircle := fun j =>
    (continuous_trigPoly _).aestronglyMeasurable
  set σ : Fin (2 * K + 1) → Fin (2 * K + 1) := fun k =>
    if _h : K < (k : ℕ) then ⟨k - K - 1, by omega⟩ else ⟨(k : ℕ) + K, by omega⟩ with hσdef
  have hσ : Function.Injective σ := by
    intro a b hab
    simp only [hσdef] at hab
    split_ifs at hab <;> rw [Fin.mk.injEq] at hab <;> exact Fin.ext (by omega)
  have h : ({k : Fin (2 * K + 1) | K < (k : ℕ)}.indicator
      fun k => trigBlock (dyadicBlock ((k : ℕ) - K)) c) =
      {k : Fin (2 * K + 1) | K < (k : ℕ)}.indicator fun k => g (σ k) := by
    funext k
    by_cases hk : K < (k : ℕ)
    · rw [Set.indicator_of_mem (by exact hk), Set.indicator_of_mem (by exact hk)]
      simp only [g, hσdef, dite_eq_left hk]
      congr 2
      omega
    · rw [Set.indicator_of_notMem (by exact hk), Set.indicator_of_notMem (by exact hk)]
  rw [h]
  exact (eLpNormRad_indicator_le hp.le _ fun k => hg (σ k)).trans
    ((eLpNormRad_comp_le hp.le hσ hg).trans (eLpNormRad_dyadicBlock_succ_le hp hβ c _))

/-- The negative blocks, by reflection. -/
private theorem eLpNormRad_dyadicBlock_neg_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad ({k : Fin (2 * K + 1) | (k : ℕ) < K}.indicator
        fun k => trigBlock (dyadicBlock ((k : ℕ) - K)) c) p haarAddCircle ≤
      littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle := by
  have hp0 : 0 < p := by linarith
  set h : Fin (2 * K + 1) → UnitAddCircle → X := {k : Fin (2 * K + 1) | K < (k : ℕ)}.indicator
    fun k => trigBlock (dyadicBlock ((k : ℕ) - K)) (reflect c) with hdef
  have hh : ∀ k, Continuous (h k) := fun k => by
    simp only [hdef, Set.indicator_apply]
    split_ifs
    · exact continuous_trigPoly _
    · exact continuous_zero
  have hhn : ∀ k, Continuous fun t => h k (-t) := fun k => (hh k).comp continuous_neg
  have h1 : ({k : Fin (2 * K + 1) | (k : ℕ) < K}.indicator
      fun k => trigBlock (dyadicBlock ((k : ℕ) - K)) c) = fun k t => h (Fin.rev k) (-t) := by
    funext k t
    by_cases hk : (k : ℕ) < K
    · have hk' : K < (Fin.rev k : ℕ) := by
        rw [Fin.val_rev]
        omega
      rw [Set.indicator_of_mem (by exact hk), hdef, Set.indicator_of_mem (by exact hk'),
        ← trigBlock_neg]
      congr 2
      rw [Fin.val_rev]
      omega
    · have hk' : ¬ K < (Fin.rev k : ℕ) := by
        rw [Fin.val_rev]
        omega
      rw [Set.indicator_of_notMem (by exact hk), hdef, Set.indicator_of_notMem (by exact hk')]
      rfl
  have h2 : eLpNormRad (fun k t => h k (-t)) p haarAddCircle ≤
      1 * eLpNormRad h p haarAddCircle := by
    refine eLpNormRad_le_of_forall hp0 (fun k => (hhn k).aestronglyMeasurable)
      (fun k => (hh k).aestronglyMeasurable) fun ε => ?_
    rw [one_mul]
    exact (eLpNorm_comp_neg _ (g := fun t => ∑ k, SignCube.coin (ε k) • h k t)
      (continuous_finsetSum _ fun k _ => (hh k).const_smul _)).le
  have h3 : eLpNorm (trigPoly (reflect c)) (ENNReal.ofReal p) haarAddCircle =
      eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle := by
    rw [← eLpNorm_comp_neg _ (continuous_trigPoly c)]
    exact congrArg (fun f => eLpNorm f _ _) (funext (trigPoly_reflect c))
  rw [h1, ← h3]
  refine (eLpNormRad_comp_le hp.le Fin.rev_injective (f := fun k t => h k (-t))
    fun k => (hhn k).aestronglyMeasurable).trans (h2.trans ?_)
  rw [one_mul]
  exact eLpNormRad_dyadicBlock_pos_le hp hβ (reflect c) K

/-- The zero block is the constant `f̂ (0)`. -/
private theorem eLpNormRad_dyadicBlock_zero_le {p : ℝ} (hp : 1 < p) (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad ({k : Fin (2 * K + 1) | (k : ℕ) = K}.indicator
        fun k => trigBlock (dyadicBlock ((k : ℕ) - K)) c) p haarAddCircle ≤
      eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle := by
  have hp0 : 0 < p := by linarith
  set k₀ : Fin (2 * K + 1) := ⟨K, by omega⟩
  have h1 : ({k : Fin (2 * K + 1) | (k : ℕ) = K}.indicator
      fun k => trigBlock (dyadicBlock ((k : ℕ) - K)) c) =
      fun k (_ : UnitAddCircle) => if k = k₀ then c 0 else 0 := by
    funext k t
    by_cases hk : (k : ℕ) = K
    · rw [Set.indicator_of_mem (by exact hk), ite_eq_left (Fin.ext hk), hk, sub_self,
        trigBlock_zero]
    · rw [Set.indicator_of_notMem (by exact hk), ite_eq_right (fun h => hk (by rw [h]))]
      rfl
  rw [h1]
  refine eLpNormRad_le_of_forall_le hp0 (fun k => continuous_const) fun ε => ?_
  have h2 : (fun _ : UnitAddCircle => ∑ k, SignCube.coin (ε k) • if k = k₀ then c 0 else 0) =
      SignCube.coin (ε k₀) • fun _ : UnitAddCircle => c 0 := by
    funext t
    simp
  have h3 : c 0 = ∫ t, trigPoly c t ∂haarAddCircle := by
    rw [← integral_fourier_smul_trigPoly c 0]
    simp only [neg_zero, fourier_zero, one_smul]
  rw [h2, eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, SignCube.abs_coin,
    ENNReal.ofReal_one, one_mul, h3]
  exact eLpNorm_const_integral_le hp.le (continuous_trigPoly c)

/-- **The Littlewood–Paley inequality on the circle** (HNVW I, Theorem 5.7.10 (2), right-hand
inequality): for a complex UMD space `X`, `1 < p < ∞` and a trigonometric polynomial
`f = Σ c_n e_n`, `‖Σ_{|k| ≤ K} ε_k Δ̃_k f‖_{L^p (Ω × 𝕋; X)} ≤ C_β ‖f‖_{L^p (𝕋; X)}`. -/
theorem eLpNormRad_dyadicBlock_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun k : Fin (2 * K + 1) => trigBlock (dyadicBlock ((k : ℕ) - K)) c) p
        haarAddCircle ≤
      (2 * littlewoodPaleyBound β + 1) * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle := by
  set f : Fin (2 * K + 1) → UnitAddCircle → X := fun k =>
    trigBlock (dyadicBlock ((k : ℕ) - K)) c
  have hm : ∀ (s : Set (Fin (2 * K + 1))) k,
      AEStronglyMeasurable (s.indicator f k) haarAddCircle := fun s k => by
    by_cases hk : k ∈ s
    · rw [Set.indicator_of_mem hk]
      exact (continuous_trigPoly _).aestronglyMeasurable
    · rw [Set.indicator_of_notMem hk]
      exact continuous_zero.aestronglyMeasurable
  set P : Set (Fin (2 * K + 1)) := {k | K < (k : ℕ)}
  set Z : Set (Fin (2 * K + 1)) := {k | (k : ℕ) = K}
  set M : Set (Fin (2 * K + 1)) := {k | (k : ℕ) < K}
  have hsplit : f = fun k t => P.indicator f k t + (Z.indicator f k t + M.indicator f k t) := by
    funext k t
    rcases lt_trichotomy (k : ℕ) K with hk | hk | hk
    · rw [Set.indicator_of_notMem (s := P) (by simp [P, hk.le]), Set.indicator_of_notMem (s := Z)
        (by simp [Z, hk.ne]), Set.indicator_of_mem (s := M) (by exact hk)]
      simp
    · rw [Set.indicator_of_notMem (s := P) (by simp [P, hk]), Set.indicator_of_mem (s := Z)
        (by exact hk), Set.indicator_of_notMem (s := M) (by simp [M, hk])]
      simp
    · rw [Set.indicator_of_mem (s := P) (by exact hk), Set.indicator_of_notMem (s := Z)
        (by simp [Z, hk.ne']), Set.indicator_of_notMem (s := M) (by simp [M, hk.le])]
      simp
  rw [hsplit]
  calc _ ≤ eLpNormRad (P.indicator f) p haarAddCircle +
        (eLpNormRad (Z.indicator f) p haarAddCircle +
          eLpNormRad (M.indicator f) p haarAddCircle) :=
        (eLpNormRad_add_le hp.le (hm P) fun k => (hm Z k).add (hm M k)).trans
          (add_le_add_right (eLpNormRad_add_le hp.le (hm Z) (hm M)) _)
    _ ≤ littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle +
        (eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle +
          littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle) := by
        gcongr
        · exact eLpNormRad_dyadicBlock_pos_le hp hβ c K
        · exact eLpNormRad_dyadicBlock_zero_le hp c K
        · exact eLpNormRad_dyadicBlock_neg_le hp hβ c K
    _ = _ := by ring

/-- The projections onto single frequencies are randomised bounded: for trigonometric polynomials
`f_k = Σ_n c_k (n) e_n` and any `n_k ∈ ℤ`, `‖Σ ε_k c_k (n_k) e_{n_k}‖ ≤ 4 ‖Σ ε_k f_k‖`. -/
theorem eLpNormRad_singleFrequency_le {p : ℝ} (hp : 1 ≤ p) {K : ℕ} (c : Fin K → ℤ →₀ X)
    (n : Fin K → ℤ) :
    eLpNormRad (fun k (t : UnitAddCircle) => fourier (n k) t • c k (n k)) p haarAddCircle ≤
      4 * eLpNormRad (fun k => trigPoly (c k)) p haarAddCircle := by
  have hp0 : 0 < p := by linarith
  have hcont : ∀ k, Continuous fun t : UnitAddCircle => fourier (-n k) t • trigPoly (c k) t :=
    fun k => (map_continuous (fourier (-n k))).smul (continuous_trigPoly (c k))
  -- the contraction principle
  have h1 : eLpNormRad (fun k (t : UnitAddCircle) => fourier (n k) t • c k (n k)) p haarAddCircle ≤
      2 * eLpNormRad (fun k (_ : UnitAddCircle) => c k (n k)) p haarAddCircle :=
    eLpNormRad_smul_le hp (c := fun k t => fourier (n k) t)
      (f := fun k (_ : UnitAddCircle) => c k (n k)) (fun k t => (norm_fourier_apply _ _).le)
      (fun k => (map_continuous (fourier (n k))).aestronglyMeasurable)
      fun k => aestronglyMeasurable_const
  -- Jensen's inequality, for each choice of signs
  have h2 : eLpNormRad (fun k (_ : UnitAddCircle) => c k (n k)) p haarAddCircle ≤
      1 * eLpNormRad (fun k (t : UnitAddCircle) => fourier (-n k) t • trigPoly (c k) t) p
        haarAddCircle := by
    refine eLpNormRad_le_of_forall hp0 (fun k => aestronglyMeasurable_const)
      (fun k => (hcont k).aestronglyMeasurable) fun ε => ?_
    have hsum : Continuous fun t : UnitAddCircle =>
        ∑ k, SignCube.coin (ε k) • fourier (-n k) t • trigPoly (c k) t :=
      continuous_finsetSum _ fun k _ => (hcont k).const_smul _
    have h3 : ∑ k, SignCube.coin (ε k) • c k (n k) =
        ∫ t, ∑ k, SignCube.coin (ε k) • fourier (-n k) t • trigPoly (c k) t ∂haarAddCircle := by
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_smul, integral_fourier_smul_trigPoly]
      · exact fun k _ => ((hcont k).const_smul _).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    rw [one_mul, h3]
    exact eLpNorm_const_integral_le hp hsum
  -- the contraction principle
  have h4 : eLpNormRad (fun k (t : UnitAddCircle) => fourier (-n k) t • trigPoly (c k) t) p
      haarAddCircle ≤ 2 * eLpNormRad (fun k => trigPoly (c k)) p haarAddCircle :=
    eLpNormRad_smul_le hp (c := fun k t => fourier (-n k) t) (f := fun k => trigPoly (c k))
      (fun k t => (norm_fourier_apply _ _).le)
      (fun k => (map_continuous (fourier (-n k))).aestronglyMeasurable)
      fun k => (continuous_trigPoly _).aestronglyMeasurable
  calc _ ≤ 2 * (1 * (2 * eLpNormRad (fun k => trigPoly (c k)) p haarAddCircle)) := by
        refine h1.trans ?_
        gcongr
        exact h2.trans (by gcongr)
    _ = 4 * eLpNormRad (fun k => trigPoly (c k)) p haarAddCircle := by ring

end VectorValuedHarmonicAnalysis
