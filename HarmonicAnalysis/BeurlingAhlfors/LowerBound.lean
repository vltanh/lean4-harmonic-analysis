/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.BeurlingAhlfors.Duality
public import HarmonicAnalysis.BeurlingAhlfors.TestFunctions
public import HarmonicAnalysis.Complex.RadialIntegral
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Dragičević's lower bound for `‖𝓑²‖_p`

With the Pochhammer symbol `(a)_n = a (a + 1) ⋯ (a + n − 1)` and `q = p / (p − 1)`, Dragičević's
constant is `κ_n (p) = (1/q)_n / (1/p)_n` (`HarmonicAnalysis.beurlingKappa`); for `n = 2`,
`κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`. Let `p* = max (p, q)` (`HarmonicAnalysis.pStar`).

## Main results

* `HarmonicAnalysis.tendsto_eLpNorm_div_testFun` (Dragičević's limit, `n = 2`): for the source's
  test functions `f_{2,α} (z) = z² |z|^{−2α} g₂ (|z|)`,
  `‖∂²f_{2,α}‖_p / ‖∂̄²f_{2,α}‖_p → κ₂ (p)` as `α → 1/p` from below.
* `HarmonicAnalysis.eLpNorm_div_le_beurlingPowNorm_two`: `‖∂²f_{2,α}‖_p / ‖∂̄²f_{2,α}‖_p ≤ ‖𝓑²‖_p`
  for `0 < α < 1/p`, since `f_{2,α} ∈ W^{2,p}` and `𝓑² (∂̄²f) = ∂²f`.
* `HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two` (Dragičević's theorem, `n = 2`):
  `κ₂ (p) ≤ ‖𝓑²‖_p` for `1 < p < ∞`.
* `HarmonicAnalysis.beurlingKappa_two_pStar_le_beurlingPowNorm_two`: `κ₂ (p*) ≤ ‖𝓑²‖_p` for
  `1 < p < ∞`, by `‖𝓑²‖_p = ‖𝓑²‖_q` for `p < 2` (`HarmonicAnalysis.beurlingPowNorm_conjExponent`),
  the reduction to `p ≥ 2` of Carbonaro–Dragičević–Kovač §1.3.1 (for `R^k`, `𝓑 = R²`). The
  lecture notes' Corollary 4.8 states the weaker asymptotic form `‖T^n‖_p ≳ n^{1−2/p*}(p* − 1)`.
* Corollaries: `p* − 1 < ‖𝓑²‖_p` for `p ≠ 2`
  (`HarmonicAnalysis.pStar_sub_one_lt_beurlingPowNorm_two`), since
  `κ₂ (p*) − (p* − 1) = (p* − 1)(p* − 2) / (p* + 1) > 0`; and `21/5 = κ₂ (4) ≤ ‖𝓑²‖₄`
  (`HarmonicAnalysis.twentyOne_div_five_le_beurlingPowNorm_two_four`).

Dragičević proves `‖T^n‖_p ≥ κ_n (p)` for every `n` and states it for `p > 2`, where it is the
informative bound; the same argument gives `κ₂ (p) ≤ ‖𝓑²‖_p` for every `p > 1`. Only `n = 2` is
proved here; general `n` is a planned extension.

The proof is the source's (lecture notes, Proposition 4.2), with its test functions
(`HarmonicAnalysis.BeurlingAhlfors.testFun`): explicit integrals over the unit disc, of order
`(1 − αp)⁻¹`, and integrals outside it that stay bounded. The norm `‖𝓑²‖_p` is a supremum over
Schwartz functions, and `f_{2,α}` is not one; the source's `𝓑² (∂̄²f) = ∂²f` for `f ∈ W^{2,p}`
(§4.1, after Exercise 4.1: "this ensures that `T^n (∂̄^n f) = ∂^n f`"; for `n = 1` this is
Exercise 2.19, whose hint is to approximate by smooth functions) enters through
the density step `HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto`, applied to Schwartz
approximations of `f_{2,α}` in `W^{2,p}`
(`HarmonicAnalysis.BeurlingAhlfors.exists_schwartz_tendsto_testFun`).

## References

* O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471, Theorem 1.1.
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), Proposition 4.2 (Theorem 1.1 of the
  previous reference, with its proof), Exercises 2.19 and 4.1.
* A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex Riesz
  transform*, Math. Ann. 386 (2023), 1081–1125,
  [arXiv:2109.08369](https://arxiv.org/abs/2109.08369), §1.3.1 and §2.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HarmonicAnalysis

open BeurlingAhlfors

/-- Dragičević's constant `κ_n (p) = (1/q)_n / (1/p)_n`, `1/q = 1 − 1/p`, with the Pochhammer
symbol `(a)_n = a (a + 1) ⋯ (a + n − 1)`. -/
def beurlingKappa (n : ℕ) (p : ℝ) : ℝ :=
  (ascPochhammer ℝ n).eval (1 - p⁻¹) / (ascPochhammer ℝ n).eval p⁻¹

/-- `p* = max (p, p / (p − 1))`. -/
def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

/-- `κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`. -/
theorem beurlingKappa_two {p : ℝ} (hp : 0 < p) :
    beurlingKappa 2 p = (p - 1) * (2 * p - 1) / (p + 1) := by
  simp only [beurlingKappa, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one,
    one_mul]
  field_simp
  ring

/-- `κ₂ (4) = 21/5`. -/
theorem beurlingKappa_two_four : beurlingKappa 2 4 = 21 / 5 := by
  simp only [beurlingKappa, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one,
    one_mul]
  norm_num

theorem pStar_of_two_le {p : ℝ} (hp : 2 ≤ p) : pStar p = p :=
  max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)

theorem pStar_of_lt_two {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : pStar p = p / (p - 1) :=
  max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)

theorem two_lt_pStar {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) : 2 < pStar p := by
  rcases lt_or_gt_of_ne hp2 with h | h
  · rw [pStar_of_lt_two hp h, lt_div_iff₀ (by linarith)]
    linarith
  · rw [pStar_of_two_le h.le]
    exact h

/-- Dragičević's limit (lecture notes, Proposition 4.2), `n = 2`:
`‖∂²f_{2,α}‖_p / ‖∂̄²f_{2,α}‖_p → κ₂ (p)` as `α → 1/p` from below, for `1 < p < ∞`. -/
theorem tendsto_eLpNorm_div_testFun {p : ℝ} (hp : 1 < p) :
    Tendsto (fun α : ℝ =>
        eLpNorm (dz (dz (testFun 2 α))) (ENNReal.ofReal p) volume /
          eLpNorm (dzbar (dzbar (testFun 2 α))) (ENNReal.ofReal p) volume)
      (𝓝[<] p⁻¹) (𝓝 (ENNReal.ofReal (beurlingKappa 2 p))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpi : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hB : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  have hIoo : ∀ α ∈ Set.Ioo 0 p⁻¹, 0 < α ∧ α * p < 1 ∧ α ∈ Set.Icc (0 : ℝ) 1 := fun α hα =>
    ⟨hα.1, by
      calc α * p < p⁻¹ * p := mul_lt_mul_of_pos_right hα.2 hp0
        _ = 1 := inv_mul_cancel₀ hp0.ne', hα.1.le, (hα.2.trans hpi).le⟩
  -- the integrals over `Δᶜ`, bounded uniformly in `α`
  obtain ⟨C, hC⟩ := exists_bound_testFun_compl_ball hp0
  obtain ⟨iOut, hiOut⟩ : ∃ g : ℝ → ℝ, ∀ α, g α =
      (∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dz (dz (testFun 2 α)) z‖ₑ ^ p).toReal :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jOut, hjOut⟩ : ∃ g : ℝ → ℝ, ∀ α, g α =
      (∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dzbar (dzbar (testFun 2 α)) z‖ₑ ^ p).toReal :=
    ⟨_, fun _ => rfl⟩
  -- the source's equation: the ratio of the `p`-th powers of the norms, with numerator and
  -- denominator multiplied by `1 − αp`
  have heq : ∀ α ∈ Set.Ioo 0 p⁻¹,
      eLpNorm (dz (dz (testFun 2 α))) (ENNReal.ofReal p) volume /
          eLpNorm (dzbar (dzbar (testFun 2 α))) (ENNReal.ofReal p) volume =
        ENNReal.ofReal (((Real.pi * ((2 - α) * (1 - α)) ^ p + (1 - α * p) * iOut α) /
          (Real.pi * (α * (α + 1)) ^ p + (1 - α * p) * jOut α)) ^ (1 / p)) := by
    intro α hα
    obtain ⟨hα0, hαp, hα1⟩ := hIoo α hα
    obtain ⟨hI, hJ⟩ := hC α hα1
    have hε : 0 < 1 - α * p := by linarith
    have hα1' : α < 1 := hα.2.trans hpi
    have ha : 0 < Real.pi / (1 - α * p) * ((2 - α) * (1 - α)) ^ p :=
      mul_pos (div_pos Real.pi_pos hε) (Real.rpow_pos_of_pos (by nlinarith) _)
    have hb : 0 < Real.pi / (1 - α * p) * (α * (α + 1)) ^ p :=
      mul_pos (div_pos Real.pi_pos hε) (Real.rpow_pos_of_pos (by positivity) _)
    have hp' : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top
        (measurable_dz _).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp' ENNReal.ofReal_ne_top
        (measurable_dzbar _).aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le, ← lintegral_add_compl (μ := volume) _ hB,
      ← lintegral_add_compl (μ := volume) _ hB, lintegral_dz_dz_testFun_ball hp hα0 hαp,
      lintegral_dzbar_dzbar_testFun_ball hp hα0 hαp,
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI),
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJ),
      ← ENNReal.ofReal_add ha.le ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_add hb.le ENNReal.toReal_nonneg,
      ← ENNReal.div_rpow_of_nonneg _ _ (one_div_nonneg.2 hp0.le),
      ← ENNReal.ofReal_div_of_pos (add_pos_of_pos_of_nonneg hb ENNReal.toReal_nonneg),
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (add_nonneg ha.le ENNReal.toReal_nonneg)
        (add_nonneg hb.le ENNReal.toReal_nonneg)) (one_div_nonneg.2 hp0.le)]
    congr 2
    rw [hiOut, hjOut]
    field_simp
  -- as `α → 1/p`, `1 − αp → 0`, and the integrals over `Δᶜ` disappear
  have hev : ∀ᶠ α in 𝓝[<] p⁻¹, α ∈ Set.Ioo 0 p⁻¹ := Ioo_mem_nhdsLT (inv_pos.2 hp0)
  have hε : Tendsto (fun α : ℝ => 1 - α * p) (𝓝[<] p⁻¹) (𝓝 0) := by
    have h : Tendsto (fun α : ℝ => 1 - α * p) (𝓝 p⁻¹) (𝓝 (1 - p⁻¹ * p)) :=
      (continuous_const.sub (continuous_id.mul continuous_const)).tendsto p⁻¹
    rw [inv_mul_cancel₀ hp0.ne', sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hvanish : ∀ g : ℝ → ℝ,
      (∀ α ∈ Set.Ioo 0 p⁻¹, 0 ≤ g α ∧ g α ≤ (ENNReal.ofReal C).toReal) →
        Tendsto (fun α => (1 - α * p) * g α) (𝓝[<] p⁻¹) (𝓝 0) := by
    intro g hg
    have h0 := hε.mul_const (ENNReal.ofReal C).toReal
    rw [zero_mul] at h0
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [hev] with α hα
      exact mul_nonneg (by linarith [(hIoo α hα).2.1]) (hg α hα).1
    · filter_upwards [hev] with α hα
      exact mul_le_mul_of_nonneg_left (hg α hα).2 (by linarith [(hIoo α hα).2.1])
  have hi := hvanish iOut fun α hα => ⟨(hiOut α).symm ▸ ENNReal.toReal_nonneg,
    (hiOut α).symm ▸ ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC α (hIoo α hα).2.2).1⟩
  have hj := hvanish jOut fun α hα => ⟨(hjOut α).symm ▸ ENNReal.toReal_nonneg,
    (hjOut α).symm ▸ ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC α (hIoo α hα).2.2).2⟩
  have hcont : ∀ g : ℝ → ℝ, Continuous g →
      Tendsto (fun α => Real.pi * g α ^ p) (𝓝[<] p⁻¹) (𝓝 (Real.pi * g p⁻¹ ^ p)) := fun g hg =>
    ((continuous_const.mul (hg.rpow_const fun _ => Or.inr hp0.le)).tendsto p⁻¹).mono_left
      nhdsWithin_le_nhds
  have hnum : Tendsto (fun α => Real.pi * ((2 - α) * (1 - α)) ^ p + (1 - α * p) * iOut α)
      (𝓝[<] p⁻¹) (𝓝 (Real.pi * ((2 - p⁻¹) * (1 - p⁻¹)) ^ p + 0)) :=
    (hcont (fun α => (2 - α) * (1 - α)) (by fun_prop)).add hi
  have hden : Tendsto (fun α => Real.pi * (α * (α + 1)) ^ p + (1 - α * p) * jOut α)
      (𝓝[<] p⁻¹) (𝓝 (Real.pi * (p⁻¹ * (p⁻¹ + 1)) ^ p + 0)) :=
    (hcont (fun α => α * (α + 1)) (by fun_prop)).add hj
  have ha : 0 < (2 - p⁻¹) * (1 - p⁻¹) := mul_pos (by linarith) (by linarith)
  have hb : 0 < p⁻¹ * (p⁻¹ + 1) := by positivity
  have hlim := (hnum.div hden (by
    rw [add_zero]
    exact (mul_pos Real.pi_pos (Real.rpow_pos_of_pos hb p)).ne')).rpow_const
    (Or.inr (one_div_nonneg.2 hp0.le))
  -- the limit is `κ₂ (p)`
  have hval : ((Real.pi * ((2 - p⁻¹) * (1 - p⁻¹)) ^ p + 0) /
      (Real.pi * (p⁻¹ * (p⁻¹ + 1)) ^ p + 0)) ^ (1 / p) = beurlingKappa 2 p := by
    rw [add_zero, add_zero, mul_div_mul_left _ _ Real.pi_ne_zero, ← Real.div_rpow ha.le hb.le,
      ← Real.rpow_mul (div_pos ha hb).le, mul_one_div_cancel hp0.ne', Real.rpow_one]
    simp only [beurlingKappa, ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one,
      one_mul]
    push_cast
    ring
  rw [hval] at hlim
  refine (ENNReal.tendsto_ofReal hlim).congr' ?_
  filter_upwards [hev] with α hα
  exact (heq α hα).symm

/-- `‖∂²f_{2,α}‖_p / ‖∂̄²f_{2,α}‖_p ≤ ‖𝓑²‖_p` for `1 < p < ∞` and `0 < α < 1/p`: Schwartz
approximations of `f_{2,α} ∈ W^{2,p}` and `𝓑² ∂̄² = ∂²` on Schwartz functions. -/
theorem eLpNorm_div_le_beurlingPowNorm_two {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    eLpNorm (dz (dz (testFun 2 α))) (ENNReal.ofReal p) volume /
        eLpNorm (dzbar (dzbar (testFun 2 α))) (ENNReal.ofReal p) volume ≤
      beurlingPowNorm 2 p := by
  obtain ⟨φ, hu, hv⟩ := exists_schwartz_tendsto_testFun hp.le hα0 hα
  exact div_le_beurlingPowNorm_of_tendsto 2 hp.le (measurable_dzbar _).aestronglyMeasurable
    (measurable_dz _).aestronglyMeasurable hu hv

/-- Dragičević's lower bound (Theorem 1.1 of the 2011 article; Proposition 4.2 of the lecture
notes), the case `n = 2`: `κ₂ (p) ≤ ‖𝓑²‖_{L^p}` for `1 < p < ∞`. The source states it for
`p > 2`. -/
theorem beurlingKappa_two_le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 p) ≤ beurlingPowNorm 2 p := by
  refine le_of_tendsto (tendsto_eLpNorm_div_testFun hp) ?_
  filter_upwards [Ioo_mem_nhdsLT (inv_pos.mpr (zero_lt_one.trans hp))] with α hα
  refine eLpNorm_div_le_beurlingPowNorm_two hp hα.1 ?_
  have hp0 : 0 < p := zero_lt_one.trans hp
  calc α * p < p⁻¹ * p := mul_lt_mul_of_pos_right hα.2 hp0
    _ = 1 := inv_mul_cancel₀ hp0.ne'

/-- `κ₂ (p*) ≤ ‖𝓑²‖_{L^p}` for `1 < p < ∞`: for `p < 2`, `‖𝓑²‖_p = ‖𝓑²‖_q` and `p* = q`. -/
theorem beurlingKappa_two_pStar_le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 (pStar p)) ≤ beurlingPowNorm 2 p := by
  rcases le_or_gt 2 p with h2 | h2
  · rw [pStar_of_two_le h2]
    exact beurlingKappa_two_le_beurlingPowNorm_two hp
  · rw [pStar_of_lt_two hp h2, beurlingPowNorm_conjExponent 2 hp]
    exact beurlingKappa_two_le_beurlingPowNorm_two (by rw [lt_div_iff₀ (by linarith)]; linarith)

/-- `(p* − 1)(2p* − 1) / (p* + 1) ≤ ‖𝓑²‖_{L^p}` for `1 < p < ∞`. -/
theorem le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal ((pStar p - 1) * (2 * pStar p - 1) / (pStar p + 1)) ≤ beurlingPowNorm 2 p := by
  have h : 0 < pStar p := lt_of_lt_of_le (by linarith) (le_max_left p _)
  rw [← beurlingKappa_two h]
  exact beurlingKappa_two_pStar_le_beurlingPowNorm_two hp

/-- `p* − 1 < κ₂ (p*)` for `1 < p < ∞`, `p ≠ 2`. -/
theorem pStar_sub_one_lt_beurlingKappa_two {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    pStar p - 1 < beurlingKappa 2 (pStar p) := by
  have h := two_lt_pStar hp hp2
  rw [beurlingKappa_two (by linarith), lt_div_iff₀ (by linarith)]
  nlinarith

/-- `p* − 1 < ‖𝓑²‖_{L^p}` for `1 < p < ∞`, `p ≠ 2`. -/
theorem pStar_sub_one_lt_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    ENNReal.ofReal (pStar p - 1) < beurlingPowNorm 2 p := by
  have h := pStar_sub_one_lt_beurlingKappa_two hp hp2
  refine lt_of_lt_of_le ?_ (beurlingKappa_two_pStar_le_beurlingPowNorm_two hp)
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [two_lt_pStar hp hp2])).mpr h

/-- `21/5 ≤ ‖𝓑²‖_{L⁴}`. -/
theorem twentyOne_div_five_le_beurlingPowNorm_two_four :
    ENNReal.ofReal (21 / 5) ≤ beurlingPowNorm 2 4 := by
  rw [← beurlingKappa_two_four]
  exact beurlingKappa_two_le_beurlingPowNorm_two (by norm_num)

end HarmonicAnalysis
