/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.BeurlingAhlfors.CauchyTransform
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# `‖𝓑‖_p` as the best constant of `‖∂u‖_p ≤ C ‖∂̄u‖_p` on `C_c^∞`

For `1 < p < ∞` and `C ∈ [0, ∞]`, the norm of the Beurling–Ahlfors transform on `L^p (ℂ)` is at
most `C` if and only if `‖∂u‖_p ≤ C ‖∂̄u‖_p` for every smooth compactly supported `u : ℂ → ℂ`
(`HarmonicAnalysis.beurlingPowNorm_one_le_iff`): `‖𝓑‖_p` is the best constant of that inequality
(`HarmonicAnalysis.isLeast_beurlingPowNorm_one`). This is the reduction that
Baernstein–Montgomery-Smith state without proof (1999, §1, remark (b), and §2, (2.4)): the truth
of their Conjecture 3 (Iwaniec's), `∫ |∂̄f|^p ≤ (p* − 1)^p ∫ |∂f|^p` for `f ∈ Ẇ^{1,p}`, which holds
if and only if it holds with `∂f` and `∂̄f` interchanged, "would show that the norm of `S` on
`L^p (ℂ, ℂ)` is precisely `p* − 1`". They state the inequality on `Ẇ^{1,p}`; here it is on
`C_c^∞`, which is what the reduction needs.

## Main results

* `HarmonicAnalysis.exists_hasCompactSupport_tendsto_dz_dzbar` (cut-offs): for a Schwartz function
  `f`, the smooth compactly supported functions `u_n = η_{n+1} f` satisfy `∂u_n → ∂f` and
  `∂̄u_n → ∂̄f` in `L^p`; hence `‖∂u‖_p ≤ C ‖∂̄u‖_p` passes from `C_c^∞` to the Schwartz
  functions, `1 ≤ p < ∞` (`HarmonicAnalysis.eLpNorm_dz_le_of_forall_hasCompactSupport`).
* `HarmonicAnalysis.eLpNorm_beurlingPow_one_le_of_hasCompactFourierSupportOffZero` (the dense
  class): then `‖𝓑 g‖_p ≤ C ‖g‖_p` for the Schwartz functions `g` with Fourier transform in
  `C_c^∞ (ℂ ∖ {0})`, by the inequality for their Cauchy transforms.
* `HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`: then `‖𝓑‖_p ≤ C`, and
  `‖𝓑 g‖_p ≤ C ‖g‖_p` for every Schwartz function `g`
  (`HarmonicAnalysis.eLpNorm_beurlingPow_one_le_of_forall_hasCompactSupport`).
* `HarmonicAnalysis.eLpNorm_dz_le_beurlingPowNorm_one_mul`: conversely,
  `‖∂u‖_p ≤ ‖𝓑‖_p ‖∂̄u‖_p` for smooth compactly supported `u`, by `𝓑 (∂̄u) = ∂u`; with the
  above, `HarmonicAnalysis.beurlingPowNorm_one_le_iff` and
  `HarmonicAnalysis.isLeast_beurlingPowNorm_one`.

## Proof

The proof follows Guerra's proof of Corollary 1.4 of the preprint (2026, §6), which derives an
inequality for `𝓑` from one on `C_c^∞`: "by density" take `h` in a dense class, let `u` be a
potential of `h`, apply the inequality on `C_c^∞` to `η_R u`, where the cut-offs `η_R` (those of
the proof of Corollary 1.2 there) are `1` on the disc of radius `R`, `0` off that of radius `2R`,
with `|Dη_R| ≤ C / R`, and let `R → ∞`. Here `η_R (z) = χ (z / R)`, `χ` a smooth bump function, and
`R = n + 1`. It departs from that proof in three ways.

1. **The gradient case.** Guerra's `h` is real, in `C_c^∞`, its potential is the logarithmic
   potential `u = (1/π) ∫ log |x − y| h (y) dy`, and the inequality is one for Hessians: the
   parts `a₊`, `a₋` of `A = D²u` (`A z = a₊ z + a₋ z̄`) are `h` and `conj (𝓑 h)`. Here `g` is
   complex, the inequality is the one for `∂u`, `∂̄u` of Baernstein–Montgomery-Smith, and the
   potential is the Cauchy transform `f` of `g` (`HarmonicAnalysis.cauchyTransform`), with
   `∂̄f = g` and `∂f = 𝓑 g`. This is the case that the norm of `𝓑` on complex `L^p` needs.
2. **The dense class.** Guerra's is `C_c^∞`, and the passage to the limit rests on the decay of
   the potential (`Du = O (|x|^{−1})`, `D²u = O (|x|^{−2})`), from its kernel. Here it is the
   class of Hytönen–van Neerven–Veraar–Weis, Proposition 2.4.23 (ii): the Schwartz functions with
   Fourier transform in `C_c^∞ (ℂ ∖ {0})`
   (`HarmonicAnalysis.exists_tendsto_hasCompactFourierSupportOffZero`). Their Cauchy transforms
   are Schwartz functions, constructed on the Fourier side, so that no Cauchy kernel and no decay
   estimate are needed, and the cut-offs work for every Schwartz function `f`: in
   `∂ (η_R f) − ∂f = (η_R − 1) ∂f + f ∂η_R`, the first term tends to `0` in `L^p` by dominated
   convergence, and the second is at most `(sup |Dχ| / R) ‖f‖_p`. Guerra's class would also work:
   for `g ∈ C_c^∞` the Cauchy transform is `O (1/|z|)` and `∂f = 𝓑 g = O (1/|z|²)`, so that
   `‖f ∇η_R‖_p = O (R^{2/p − 2}) → 0` for every `p > 1`. The change of class is for economy (it
   avoids the kernel and its estimates), not forced.
3. **The density step, explicit.** Guerra's "by density", from the dense class to all of `L^p`,
   is made explicit for the Schwartz functions `g`, over which `‖𝓑‖_p` is a supremum
   (`HarmonicAnalysis.beurlingPowNorm`): the functions `g_j` of the dense class with `g_j → g` in
   `L^p` have `𝓕 g_j → 𝓕 g` in `L¹`, so that `𝓑 g_j → 𝓑 g` uniformly
   (`HarmonicAnalysis.enorm_fourierMultiplier_sub_le`, `|ξ̄/ξ| ≤ 1`), and Fatou's lemma gives
   `‖𝓑 g‖_p ≤ liminf ‖𝓑 g_j‖_p ≤ C ‖g‖_p`. This does not use the boundedness of `𝓑` on `L^p`,
   which the library does not prove.

The converse is `𝓑 (∂̄u) = ∂u` (`HarmonicAnalysis.beurlingPow_dzbarCLM_pow`) and the definition
of `‖𝓑‖_p`.

## References

* A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
  `∂̄f`*, in: Complex analysis and differential equations (Uppsala, 1997), ed. C. Kiselman, Acta
  Univ. Upsaliensis C 64 (1999), 92–109, [arXiv:math/9709215](https://arxiv.org/abs/math/9709215),
  §1, Conjecture 3 and remark (b); §2, (2.4).
* A. Guerra, *Quasiconvexity of the Burkholder function on symmetric matrices*, preprint,
  [arXiv:2608.23388](https://arxiv.org/abs/2608.23388) (2026), §6: the proofs of Corollaries 1.2
  and 1.4.
* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*,
  Ergebnisse der Mathematik 63, Springer, 2016, Proposition 2.4.23 (ii).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform ENNReal ContDiff

namespace HarmonicAnalysis

/-! ### Cut-offs -/

/-- `½ (∂_x g + s ∂_y g)`: `∂g` for `s = −i`, `∂̄g` for `s = i`. -/
private def wirt (s : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  2⁻¹ * (fderiv ℝ g z 1 + s * fderiv ℝ g z Complex.I)

/-- `∂ = wirt (−i)`. -/
private lemma dz_eq_wirt (g : ℂ → ℂ) : dz g = wirt (-Complex.I) g := by
  funext z
  simp only [dz, wirt, smul_eq_mul, neg_mul, sub_eq_add_neg]

/-- `∂̄ = wirt i`. -/
private lemma dzbar_eq_wirt (g : ℂ → ℂ) : dzbar g = wirt Complex.I g := by
  funext z
  simp only [dzbar, wirt, smul_eq_mul]

/-- `wirt s g` is measurable for every `g`. -/
private lemma measurable_wirt (s : ℂ) (g : ℂ → ℂ) : Measurable (wirt s g) := by
  unfold wirt
  fun_prop

/-- The Leibniz rule `D (c d) = c D d + d D c`. -/
private lemma wirt_mul (s : ℂ) {c d : ℂ → ℂ} {z : ℂ} (hc : DifferentiableAt ℝ c z)
    (hd : DifferentiableAt ℝ d z) :
    wirt s (fun w => c w * d w) z = c z * wirt s d z + d z * wirt s c z := by
  simp only [wirt, fderiv_fun_mul hc hd, add_apply, smul_apply, smul_eq_mul]
  ring

/-- The chain rule for a dilation: `D (ψ (r ·)) (z) = r D ψ (r z)`. -/
private lemma wirt_comp_smul (s : ℂ) (ψ : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    wirt s (fun w => ψ (r • w)) z = r * wirt s ψ (r • z) := by
  have h : fderiv ℝ (fun w => ψ (r • w)) z = r • fderiv ℝ ψ (r • z) := fderiv_comp_smul r
  unfold wirt
  rw [h]
  simp only [smul_apply, Complex.real_smul]
  ring

/-- The bump function `χ`: `1` on the closed unit disc, `0` off the disc of radius `2`. -/
private def bump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off `η_R (z) = χ (z / R)`. -/
private def cutoff (R : ℝ) (z : ℂ) : ℂ := (bump (R⁻¹ • z) : ℂ)

/-- `η_R` is smooth. -/
private lemma contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff R) :=
  (Complex.ofRealCLM.contDiff.comp bump.contDiff).comp (contDiff_const_smul R⁻¹)

/-- `η_R` has compact support. -/
private lemma hasCompactSupport_cutoff {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (cutoff R) :=
  (bump.hasCompactSupport.comp_left Complex.ofReal_zero).comp_smul (inv_ne_zero hR)

/-- `η_R = 1` on the closed disc of radius `R`. -/
private lemma cutoff_eq_one {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) : cutoff R z = 1 := by
  rw [cutoff, bump.one_of_mem_closedBall, Complex.ofReal_one]
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
    inv_mul_le_iff₀ hR]
  change ‖z‖ ≤ R * 1
  rwa [mul_one]

/-- `|η_R − 1| ≤ 1`, since `0 ≤ η_R ≤ 1`. -/
private lemma norm_cutoff_sub_one_le (R : ℝ) (z : ℂ) : ‖cutoff R z - 1‖ ≤ 1 := by
  rw [cutoff, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_le]
  constructor <;> linarith [bump.nonneg (x := R⁻¹ • z), bump.le_one (x := R⁻¹ • z)]

/-- `|∂η_R|, |∂̄η_R| ≤ K / R`, `K` a bound of `|∂χ|`, `|∂̄χ|`. -/
private lemma exists_norm_wirt_cutoff_le (s : ℂ) :
    ∃ K, ∀ R : ℝ, 0 < R → ∀ z, ‖wirt s (cutoff R) z‖ ≤ R⁻¹ * K := by
  set ψ : ℂ → ℂ := fun z => (bump z : ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp bump.contDiff
  have hcont : Continuous (wirt s ψ) := by
    have := hψ.continuous_fderiv (by simp)
    unfold wirt
    fun_prop
  have hsupp : HasCompactSupport (wirt s ψ) := by
    refine ((bump.hasCompactSupport.comp_left Complex.ofReal_zero).fderiv (𝕜 := ℝ)).mono ?_
    intro z hz
    rw [Function.mem_support] at hz ⊢
    contrapose hz
    have h0 : fderiv ℝ ψ z = 0 := hz
    simp [wirt, h0]
  obtain ⟨K, hK⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨K, fun R hR z => ?_⟩
  have h : cutoff R = fun w => ψ (R⁻¹ • w) := rfl
  rw [h, wirt_comp_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  exact mul_le_mul_of_nonneg_left (hK _) (inv_nonneg.2 hR.le)

/-- Dominated convergence in `L^p`, `0 < p < ∞`: if `|c_n| ≤ 1`, `c_n (z) = 0` for large `n` and
`h ∈ L^p`, then `‖c_n h‖_p → 0`. -/
private lemma tendsto_eLpNorm_mul_of_eventually_zero {c : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {p : ℝ}
    (hp : 0 < p) (hc : ∀ n, Continuous (c n)) (hcb : ∀ n z, ‖c n z‖ ≤ 1)
    (hlim : ∀ z, ∀ᶠ n in atTop, c n z = 0) (hh : MemLp h (ENNReal.ofReal p) volume) :
    Tendsto (fun n => eLpNorm (fun z => c n z * h z) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun z => c n z * h z) volume := fun n =>
    (hc n).aestronglyMeasurable.mul hh.aestronglyMeasurable
  have hint : Tendsto (fun n => ∫⁻ z, ‖c n z * h z‖ₑ ^ p) atTop (𝓝 (∫⁻ _ : ℂ, 0)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun z => ‖h z‖ₑ ^ p)
      (fun n => (hmeas n).enorm.pow_const p) (fun n => ae_of_all _ fun z => ?_) ?_
      (ae_of_all _ fun z => ?_)
    · refine ENNReal.rpow_le_rpow ?_ hp.le
      rw [enorm_mul]
      calc ‖c n z‖ₑ * ‖h z‖ₑ ≤ 1 * ‖h z‖ₑ := by
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_one.2 (hcb n z)
        _ = ‖h z‖ₑ := one_mul _
    · rw [← eLpNorm_ofReal_rpow_eq_lintegral hp hh.aestronglyMeasurable]
      exact ENNReal.rpow_ne_top_of_nonneg hp.le hh.eLpNorm_lt_top.ne
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim z] with n hn
      simp [hn, ENNReal.zero_rpow_of_pos hp]
  rw [lintegral_zero] at hint
  have h1 := hint.ennrpow_const (1 / p)
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h1
  refine h1.congr fun n => ?_
  rw [← eLpNorm_ofReal_rpow_eq_lintegral hp (hmeas n), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- For `u_n = η_{n+1} f`: `‖∂u_n − ∂f‖_p → 0` and `‖∂̄u_n − ∂̄f‖_p → 0` (`s = ∓i`). -/
private lemma tendsto_wirt_cutoff_mul (s : ℂ) (f : 𝓢(ℂ, ℂ)) {p : ℝ} (hp : 0 < p)
    (hf : MemLp (wirt s f) (ENNReal.ofReal p) volume) :
    Tendsto (fun n : ℕ => eLpNorm (fun z => wirt s (fun w => cutoff ((n : ℝ) + 1) w * f w) z -
      wirt s f z) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  set P := ENNReal.ofReal p
  obtain ⟨K, hK⟩ := exists_norm_wirt_cutoff_le s
  have hR : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  -- `(η_R − 1) ∂f → 0`, by dominated convergence
  have h1 : Tendsto (fun n : ℕ => eLpNorm (fun z => (cutoff ((n : ℝ) + 1) z - 1) * wirt s f z) P
      volume) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_mul_of_eventually_zero hp
      (fun n => (contDiff_cutoff _).continuous.sub continuous_const)
      (fun n z => norm_cutoff_sub_one_le _ _) (fun z => ?_) hf
    obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [cutoff_eq_one (hR n), sub_self]
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- `‖f ∂η_R‖_p ≤ (K / R) ‖f‖_p → 0`
  have h2 : Tendsto (fun n : ℕ => eLpNorm (fun z => f z * wirt s (cutoff ((n : ℝ) + 1)) z) P
      volume) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, eLpNorm (fun z => f z * wirt s (cutoff ((n : ℝ) + 1)) z) P volume ≤
        ENNReal.ofReal (((n : ℝ) + 1)⁻¹ * K) * eLpNorm f P volume := fun n =>
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (f.continuous.aestronglyMeasurable.mul (measurable_wirt s _).aestronglyMeasurable)
        (ae_of_all _ fun z => by
          rw [Pi.mul_apply, norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hK _ (hR n) z) (norm_nonneg _)) P
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1)⁻¹ * K) * eLpNorm f P volume)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * K) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const K
      have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h0)
        (Or.inr (f.memLp P).eLpNorm_lt_top.ne) (b := eLpNorm f P volume)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb
  -- `∂u_R − ∂f = (η_R − 1) ∂f + f ∂η_R`
  have hlim := ENNReal.Tendsto.const_mul (h1.add h2) (Or.inr (ENNReal.LpAddConst_lt_top P).ne)
  rw [add_zero, mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => le_of_eq_of_le ?_ (eLpNorm_add_le' P)
  congr 1
  funext z
  rw [wirt_mul s ((contDiff_cutoff _).contDiffAt.differentiableAt (by simp)) f.differentiableAt]
  simp only [Pi.add_apply]
  ring

/-- **Cut-offs.** For a Schwartz function `f`, there are smooth compactly supported `u_n` with
`∂u_n → ∂f` and `∂̄u_n → ∂̄f` in `L^p`, `0 < p < ∞`: `u_n = η_{n+1} f`, `η_R (z) = χ (z / R)` with
`χ` a smooth bump function, `1` on the unit disc and `0` off the disc of radius `2`. These are the
cut-offs of Guerra's proofs of Corollaries 1.2 and 1.4 (2026, preprint), applied to a Schwartz
function in place of the logarithmic potential there, whose decay that proof uses instead (see
the module docstring): by the Leibniz rule `∂ (η_R f) − ∂f = (η_R − 1) ∂f + f ∂η_R`, where the
first term tends to `0` in `L^p` by dominated convergence, and the second is at most
`(sup |Dχ| / R) ‖f‖_p`. -/
theorem exists_hasCompactSupport_tendsto_dz_dzbar (f : 𝓢(ℂ, ℂ)) {p : ℝ} (hp : 0 < p) :
    ∃ u : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      Tendsto (fun n => eLpNorm (fun z => dz (u n) z - dz f z) (ENNReal.ofReal p) volume) atTop
        (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => dzbar (u n) z - dzbar f z) (ENNReal.ofReal p) volume)
        atTop (𝓝 0) := by
  refine ⟨fun n w => cutoff ((n : ℝ) + 1) w * f w, fun n => (contDiff_cutoff _).mul (f.smooth ⊤),
    fun n => (hasCompactSupport_cutoff (by positivity)).mul_right, ?_, ?_⟩
  · simp only [dz_eq_wirt]
    refine tendsto_wirt_cutoff_mul _ f hp ?_
    have h : wirt (-Complex.I) f = dzCLM f := by
      rw [← dz_eq_wirt]
      exact funext fun z => (dzCLM_apply f z).symm
    rw [h]
    exact (dzCLM f).memLp _ _
  · simp only [dzbar_eq_wirt]
    refine tendsto_wirt_cutoff_mul _ f hp ?_
    have h : wirt Complex.I f = dzbarCLM f := by
      rw [← dzbar_eq_wirt]
      exact funext fun z => (dzbarCLM_apply f z).symm
    rw [h]
    exact (dzbarCLM f).memLp _ _

/-- `𝓑 0 = 0`. -/
private lemma beurlingPow_one_zero : beurlingPow 1 (0 : ℂ → ℂ) = 0 := by
  funext z
  simp [beurlingPow, fourierMultiplier, Real.fourier_eq, Real.fourierInv_eq]

/-- **From `C_c^∞` to Schwartz functions, by cut-offs.** If `‖∂u‖_p ≤ C ‖∂̄u‖_p` for every smooth
compactly supported `u`, `1 ≤ p < ∞`, then also for every Schwartz function `f`: apply it to the
functions `η_R f` of `HarmonicAnalysis.exists_hasCompactSupport_tendsto_dz_dzbar` and let
`R → ∞`, as Guerra does for `η_R u`, `u` a potential (2026, preprint, proof of Corollary 1.4).
For `C = ∞` the inequality says only that `∂̄f = 0` implies `∂f = 0`, which holds since
`∂f = 𝓑 (∂̄f)`. -/
theorem eLpNorm_dz_le_of_forall_hasCompactSupport {p : ℝ} (hp : 1 ≤ p) {C : ℝ≥0∞}
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume)
    (f : 𝓢(ℂ, ℂ)) :
    eLpNorm (dz f) (ENNReal.ofReal p) volume ≤ C * eLpNorm (dzbar f) (ENNReal.ofReal p) volume := by
  set P := ENNReal.ofReal p
  have hP : 1 ≤ P := by simpa [P] using ENNReal.ofReal_le_ofReal hp
  have hP0 : P ≠ 0 := (zero_lt_one.trans_le hP).ne'
  rcases eq_or_ne C ⊤ with rfl | hC
  · by_cases h0 : eLpNorm (dzbar f) P volume = 0
    · -- `∂̄f = 0`, hence `∂f = 𝓑 (∂̄f) = 0`
      have hz : ⇑(dzbarCLM f) = 0 := by
        have e : dzbar (f : ℂ → ℂ) = dzbarCLM f := funext fun z => (dzbarCLM_apply f z).symm
        rw [e, eLpNorm_eq_zero_iff hP0] at h0
        exact ((dzbarCLM f).continuous.ae_eq_iff_eq volume continuous_zero).1 h0
      have hdz : dz (f : ℂ → ℂ) = 0 := by
        have h1 := beurlingPow_dzbarCLM_pow 1 f
        simp only [pow_one] at h1
        rw [hz, beurlingPow_one_zero] at h1
        funext z
        rw [← dzCLM_apply, ← h1]
      simp [hdz]
    · rw [ENNReal.top_mul h0]
      exact le_top
  · obtain ⟨u, hu, huc, hdz, hdzbar⟩ :=
      exists_hasCompactSupport_tendsto_dz_dzbar f (by linarith : (0 : ℝ) < p)
    have hlim : Tendsto (fun n => eLpNorm (fun z => dz (u n) z - dz f z) P volume +
        C * (eLpNorm (fun z => dzbar (u n) z - dzbar f z) P volume +
          eLpNorm (dzbar f) P volume)) atTop (𝓝 (C * eLpNorm (dzbar f) P volume)) := by
      simpa using hdz.add (ENNReal.Tendsto.const_mul (hdzbar.add_const _) (Or.inr hC))
    refine ge_of_tendsto' hlim fun n => ?_
    calc eLpNorm (dz f) P volume
        ≤ eLpNorm (fun z => dz (u n) z - dz f z) P volume + eLpNorm (dz (u n)) P volume := by
          have e := eLpNorm_sub_le (μ := volume) (f := dz (u n))
            (g := fun z => dz (u n) z - dz f z) hP
          rw [add_comm]
          convert e using 2
          funext z
          simp
      _ ≤ eLpNorm (fun z => dz (u n) z - dz f z) P volume +
          C * eLpNorm (dzbar (u n)) P volume := by
          gcongr
          exact h _ (hu n) (huc n)
      _ ≤ _ := by
          gcongr
          have e := eLpNorm_add_le (μ := volume) (f := fun z => dzbar (u n) z - dzbar f z)
            (g := dzbar f) hP
          convert e using 2
          funext z
          simp

/-! ### The dense class -/

/-- **The dense class.** If `‖∂u‖_p ≤ C ‖∂̄u‖_p` for every smooth compactly supported `u`,
`1 ≤ p < ∞`, then `‖𝓑 g‖_p ≤ C ‖g‖_p` for the Schwartz functions `g` whose Fourier transform is
compactly supported in `ℂ ∖ {0}`: the inequality for Schwartz functions
(`HarmonicAnalysis.eLpNorm_dz_le_of_forall_hasCompactSupport`) applied to the Cauchy transform `f`
of `g`, a Schwartz function with `∂̄f = g` and `∂f = 𝓑 g`. This is Guerra's step "apply the
inequality to the potential `η_R u` and let `R → ∞`" (2026, preprint, proof of Corollary 1.4),
with the Cauchy transform in place of the logarithmic potential of a real `h ∈ C_c^∞` there (the
gradient case), and the dense class of Hytönen–van Neerven–Veraar–Weis, Proposition 2.4.23 (ii),
in place of `C_c^∞`, so that `f` is a Schwartz function and needs no decay estimate. -/
theorem eLpNorm_beurlingPow_one_le_of_hasCompactFourierSupportOffZero {p : ℝ} (hp : 1 ≤ p)
    {C : ℝ≥0∞}
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume)
    {g : 𝓢(ℂ, ℂ)} (hg : HasCompactFourierSupportOffZero g) :
    eLpNorm (beurlingPow 1 g) (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) volume := by
  obtain ⟨f, -, -, hdzbar, hdz⟩ := exists_schwartzMap_eq_cauchyTransform hg
  have h1 : dz (f : ℂ → ℂ) = beurlingPow 1 g := by
    rw [← hdz]
    exact funext fun z => (dzCLM_apply f z).symm
  have h2 : dzbar (f : ℂ → ℂ) = g := by
    rw [← hdzbar]
    exact funext fun z => (dzbarCLM_apply f z).symm
  have e := eLpNorm_dz_le_of_forall_hasCompactSupport hp h f
  rwa [h1, h2] at e

/-! ### All Schwartz functions -/

/-- The step from the dense class to all Schwartz functions, for `C < ∞`: Guerra's "by density"
(2026, preprint, proof of Corollary 1.4), made explicit. HNVW's `g_j → g` in `L^p` have
`𝓕 g_j → 𝓕 g` in `L¹`, hence `𝓑 g_j → 𝓑 g` pointwise, and Fatou's lemma gives
`‖𝓑 g‖_p ≤ liminf ‖𝓑 g_j‖_p ≤ C ‖g‖_p`, without the boundedness of `𝓑` on `L^p`. -/
private theorem eLpNorm_beurlingPow_one_le_of_ne_top {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : C ≠ ⊤)
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume)
    (g : 𝓢(ℂ, ℂ)) :
    eLpNorm (beurlingPow 1 g) (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) volume := by
  set P := ENNReal.ofReal p
  have hP : 1 ≤ P := by simpa [P] using ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨φ, hφ, hφp, hφ1⟩ := exists_tendsto_hasCompactFourierSupportOffZero g
  have hm : Measurable fun ξ => beurlingSymbol ξ ^ 1 := measurable_beurlingSymbol.pow_const 1
  have hm1 : ∀ ξ, ‖beurlingSymbol ξ ^ 1‖ ≤ 1 := fun ξ => by
    simpa using norm_beurlingSymbol_le ξ
  -- `𝓑 φ_j → 𝓑 g` pointwise (uniformly), since `𝓕 φ_j → 𝓕 g` in `L¹`
  have hlim : ∀ x, Tendsto (fun j => beurlingPow 1 (φ j) x) atTop (𝓝 (beurlingPow 1 g x)) := by
    intro x
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφ1 (fun _ => zero_le)
      fun j => ?_
    rw [edist_eq_enorm_sub]
    exact enorm_fourierMultiplier_sub_le hm hm1 (φ j) g x
  -- Fatou's lemma
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := P) (μ := volume)
    (fun j => (continuous_fourierMultiplier _ (φ j)).aestronglyMeasurable) (beurlingPow 1 g)
    (continuous_fourierMultiplier _ g).aestronglyMeasurable (ae_of_all _ hlim)
  have hbound : ∀ j, eLpNorm (beurlingPow 1 (φ j)) P volume ≤
      C * (eLpNorm (fun x => φ j x - g x) P volume + eLpNorm g P volume) := fun j => by
    refine (eLpNorm_beurlingPow_one_le_of_hasCompactFourierSupportOffZero hp.le h (hφ j)).trans ?_
    gcongr
    have e := eLpNorm_add_le (μ := volume) (f := fun x => φ j x - g x) (g := g) hP
    convert e using 2
    funext x
    simp
  have hlim2 : Tendsto (fun j => C * (eLpNorm (fun x => φ j x - g x) P volume +
      eLpNorm g P volume)) atTop (𝓝 (C * eLpNorm g P volume)) := by
    simpa using ENNReal.Tendsto.const_mul ((hφp p hp).add_const _) (Or.inr hC)
  calc eLpNorm (beurlingPow 1 g) P volume
      ≤ atTop.liminf fun j => eLpNorm (beurlingPow 1 (φ j)) P volume := hfatou
    _ ≤ atTop.liminf fun j => C * (eLpNorm (fun x => φ j x - g x) P volume +
          eLpNorm g P volume) := liminf_le_liminf (Eventually.of_forall hbound)
    _ = C * eLpNorm g P volume := hlim2.liminf_eq

/-! ### The norm of `𝓑` -/

/-- **The norm of `𝓑` on `L^p` is at most the constant of `‖∂u‖_p ≤ C ‖∂̄u‖_p` on `C_c^∞`**,
`1 < p < ∞`: if `‖∂u‖_p ≤ C ‖∂̄u‖_p` for every smooth compactly supported `u`, then
`‖𝓑‖_p ≤ C`. Baernstein–Montgomery-Smith state it without proof (1999, §1, remark (b): their
Conjecture 3 "would show that the norm of `S` on `L^p (ℂ, ℂ)` is precisely `p* − 1`"). The proof
follows Guerra's proof of Corollary 1.4 (2026, preprint): density, a potential, cut-offs,
limit; in the gradient case, with the Cauchy transform as the potential, on the dense class of
Hytönen–van Neerven–Veraar–Weis, and with the density step made explicit by Fatou's lemma (see the
module docstring for these departures and their reasons). -/
theorem beurlingPowNorm_one_le_of_forall_hasCompactSupport {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume) :
    beurlingPowNorm 1 p ≤ C := by
  rcases eq_or_ne C ⊤ with rfl | hC
  · exact le_top
  exact iSup_le fun g => ENNReal.div_le_of_le_mul (eLpNorm_beurlingPow_one_le_of_ne_top hp hC h g)

/-- `‖𝓑 g‖_p ≤ C ‖g‖_p` for every Schwartz function `g` if `‖∂u‖_p ≤ C ‖∂̄u‖_p` for every smooth
compactly supported `u`, `1 < p < ∞`: `‖𝓑 g‖_p ≤ ‖𝓑‖_p ‖g‖_p` and
`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport`. -/
theorem eLpNorm_beurlingPow_one_le_of_forall_hasCompactSupport {p : ℝ} (hp : 1 < p)
    {C : ℝ≥0∞}
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume)
    (g : 𝓢(ℂ, ℂ)) :
    eLpNorm (beurlingPow 1 g) (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) volume :=
  (eLpNorm_fourierMultiplier_le _ p g).trans
    (mul_le_mul_left (beurlingPowNorm_one_le_of_forall_hasCompactSupport hp h) _)

/-- **The converse**: `‖∂u‖_p ≤ ‖𝓑‖_p ‖∂̄u‖_p` for every smooth compactly supported `u`, since
`u` is a Schwartz function and `𝓑 (∂̄u) = ∂u` (`HarmonicAnalysis.beurlingPow_dzbarCLM_pow`). -/
theorem eLpNorm_dz_le_beurlingPowNorm_one_mul (p : ℝ) {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) :
    eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
      beurlingPowNorm 1 p * eLpNorm (dzbar u) (ENNReal.ofReal p) volume := by
  set U : 𝓢(ℂ, ℂ) := huc.toSchwartzMap hu
  have hU : (U : ℂ → ℂ) = u := rfl
  have h1 : dz u = dzCLM U := by
    rw [← hU]
    exact funext fun z => (dzCLM_apply U z).symm
  have h2 : dzbar u = dzbarCLM U := by
    rw [← hU]
    exact funext fun z => (dzbarCLM_apply U z).symm
  have h3 := beurlingPow_dzbarCLM_pow 1 U
  simp only [pow_one] at h3
  rw [h1, h2, ← h3]
  exact eLpNorm_fourierMultiplier_le _ p (dzbarCLM U)

/-- **`‖𝓑‖_p` is the best constant of `‖∂u‖_p ≤ C ‖∂̄u‖_p` on `C_c^∞`**, `1 < p < ∞`:
`‖𝓑‖_p ≤ C` if and only if `‖∂u‖_p ≤ C ‖∂̄u‖_p` for every smooth compactly supported `u`. This is
the reduction of Baernstein–Montgomery-Smith (1999, §1, remark (b), stated without proof), by
`HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport` (Guerra's argument) and
the converse `HarmonicAnalysis.eLpNorm_dz_le_beurlingPowNorm_one_mul`. -/
theorem beurlingPowNorm_one_le_iff {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞} :
    beurlingPowNorm 1 p ≤ C ↔ ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume :=
  ⟨fun hC _ hu huc => (eLpNorm_dz_le_beurlingPowNorm_one_mul p hu huc).trans
    (mul_le_mul_left hC _), beurlingPowNorm_one_le_of_forall_hasCompactSupport hp⟩

/-- `‖𝓑‖_p` is the least `C ∈ [0, ∞]` with `‖∂u‖_p ≤ C ‖∂̄u‖_p` for all `u ∈ C_c^∞`,
`1 < p < ∞` (`HarmonicAnalysis.beurlingPowNorm_one_le_iff`). -/
theorem isLeast_beurlingPowNorm_one {p : ℝ} (hp : 1 < p) :
    IsLeast {C : ℝ≥0∞ | ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume} (beurlingPowNorm 1 p) :=
  ⟨(beurlingPowNorm_one_le_iff hp).1 le_rfl, fun _ hC => (beurlingPowNorm_one_le_iff hp).2 hC⟩

end HarmonicAnalysis
