/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Basic.Real.Sign
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Lemmas shared by the two routes to the Littlewood–Paley inequalities

The lemmas of this file are used both by the route of Hytönen–van Neerven–Veraar–Weis (HNVW) to the
Littlewood–Paley inequalities (here in `VectorValued.Dyadic.Average`,
`VectorValued.LittlewoodPaley.Line` and `Circle`) and by the modules on which Paley's inequality in
the Schatten classes and the noncommutative Khintchine inequality rest (here in
`VectorValued.HilbertTransform.Fourier`, `VectorValued.Burkholder.HilbertTransform`,
`VectorValued.McConnell`, `VectorValued.LittlewoodPaley.Signs` and `CircleSigns`: the route of
Burkholder and McConnell). They are here so that the latter do not import the dyadic shifts of
HNVW, the bound of the truncated Hilbert transforms by them, and the Littlewood–Paley inequalities
of HNVW on the line and on the circle.

* the change of variables `y = a x` in the `L^p` norm (`eLpNorm_comp_mul`), `|± 1/2| = 1/2` in
  `[0, ∞]` (`enorm_half`), and the irrational dilation of HNVW I, pp. 465–466, for a finite set of
  frequencies (`exists_irrational_dilation`);
* the characters `e_a (x) = e^{2πi a x}` of the line (`expChar`), the inverse Fourier transform
  `𝓕⁻ G (x) = ∫ e_v (x) G (v) dv` (`fourierInv_eq_expChar`), its linearity, its behaviour under
  modulations and reflections (`fourierInv_smul_expChar`, `fourierInv_sign_sub`,
  `fourierInv_comp_neg`), the convolution `K * 𝓕⁻ H`, `K, H ∈ L¹`, as a Fourier multiplier
  (`integral_smul_fourierInv_sub`; HNVW I, Lemma 2.4.8), and the inverse Fourier transforms of
  Schwartz functions in `L^r` (`memLp_fourierInv`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Dilations and constants -/

/-- The change of variables `y = a x` in the `L^p` norm. -/
theorem eLpNorm_comp_mul {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (hp : p ≠ ⊤)
    {g : ℝ → E} (hg : AEStronglyMeasurable g volume) {a : ℝ} (ha : 0 < a) :
    eLpNorm (fun x => g (a * x)) p volume =
      ENNReal.ofReal a⁻¹ ^ (1 / p).toReal * eLpNorm g p volume := by
  have hmap := Real.map_volume_mul_left ha.ne'
  rw [abs_of_pos (inv_pos.2 ha)] at hmap
  have h := eLpNorm_map_measure (p := p) (μ := volume) (f := fun x : ℝ => a * x) (g := g)
    (by rw [hmap]; exact hg.smul_measure _) (measurable_const_mul a).aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_top hp _ _ hg, smul_eq_mul] at h
  exact h.symm

/-- `|± 1/2| = 1/2`, in `[0, ∞]`. -/
theorem enorm_half {𝕜 : Type*} [RCLike 𝕜] {c : 𝕜} (hc : c = 1 / 2 ∨ c = -1 / 2) : ‖c‖ₑ = 2⁻¹ := by
  have h : ‖(1 / 2 : 𝕜)‖ₑ = 2⁻¹ := by
    rw [one_div, enorm_inv two_ne_zero, ← ofReal_norm, RCLike.norm_ofNat, ENNReal.ofReal_ofNat]
  rcases hc with rfl | rfl
  · exact h
  · rw [neg_div, enorm_neg, h]

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

/-! ### Characters and the inverse Fourier transform on the line -/

/-- The character `e_a (x) = e^{2πi a x}` of the line. -/
noncomputable def expChar (a x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (a * x) : ℝ) : ℂ) * Complex.I)

/-- The characters `e_a` have modulus `1`. -/
theorem norm_expChar (a x : ℝ) : ‖expChar a x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The characters `e_a` are continuous. -/
theorem continuous_expChar (a : ℝ) : Continuous (expChar a) := by
  unfold expChar
  fun_prop

private theorem expChar_add_left (a b x : ℝ) : expChar (a + b) x = expChar a x * expChar b x := by
  rw [expChar, expChar, expChar, ← Complex.exp_add]
  push_cast
  ring_nf

private theorem expChar_comm (a x : ℝ) : expChar a x = expChar x a := by
  rw [expChar, expChar, mul_comm a]

/-- The inverse Fourier transform `𝓕⁻ G (x) = ∫ e_v (x) G (v) dv`. -/
theorem fourierInv_eq_expChar (G : ℝ → X) (x : ℝ) :
    𝓕⁻ G x = ∫ v, expChar v x • G v := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp [expChar, mul_comm]

/-- HNVW I, (5.35), p. 404, for the modulations: `(G (· + a))ˇ = e_{−a} Ǧ`. -/
theorem fourierInv_smul_expChar (a : ℝ) (G : ℝ → X) (x : ℝ) :
    𝓕⁻ (fun ξ => G (ξ + a)) x = expChar (-a) x • 𝓕⁻ G x := by
  rw [fourierInv_eq_expChar, fourierInv_eq_expChar, ← integral_smul,
    ← integral_add_right_eq_self (fun v => expChar (-a) x • expChar v x • G v) a]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [smul_smul, ← expChar_add_left]
  rw [neg_add_eq_sub, add_sub_cancel_right]

/-- The integrand `e_v (x) G (v)` of `𝓕⁻ G (x)` is integrable. -/
theorem integrable_expChar_smul {G : ℝ → X} (hG : Integrable G) (x : ℝ) :
    Integrable fun v => expChar v x • G v :=
  hG.bdd_smul 1 (by simpa only [expChar_comm] using
    (continuous_expChar x).aestronglyMeasurable) (ae_of_all _ fun v => (norm_expChar v x).le)

/-- `𝓕⁻` is linear. -/
theorem fourierInv_const_smul (c : ℂ) (G : ℝ → X) (x : ℝ) :
    𝓕⁻ (fun ξ => c • G ξ) x = c • 𝓕⁻ G x := by
  rw [fourierInv_eq_expChar, fourierInv_eq_expChar, ← integral_smul]
  exact integral_congr_ae (ae_of_all _ fun ξ => smul_comm _ _ _)

/-- `𝓕⁻` is linear: sums with real coefficients. -/
theorem fourierInv_sum_smul {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (c : Fin K → ℝ) (x : ℝ) :
    𝓕⁻ (fun ξ => ∑ k, c k • G k ξ) x = ∑ k, c k • 𝓕⁻ (G k) x := by
  simp only [fourierInv_eq_expChar]
  simp_rw [← integral_smul, Finset.smul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ => integral_congr_ae (ae_of_all _ fun v => smul_comm _ _ _)
  · intro k _
    exact integrable_expChar_smul ((hG k).smul (c k)) x

/-- `∫ K (s) e_v (x − s) ds = e_v (x) 𝓕 K (v)`. -/
private theorem integral_mul_expChar_sub (K : ℝ → ℂ) (x v : ℝ) :
    ∫ s, K s * expChar v (x - s) = expChar v x * 𝓕 K v := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [smul_eq_mul, expChar]
  rw [← mul_assoc (Complex.exp _), ← Complex.exp_add, mul_comm]
  push_cast
  ring_nf

/-- The convolution `K * 𝓕⁻ H`, with `K, H ∈ L¹`, as a Fourier multiplier: HNVW I, Lemma 2.4.8
(p. 109), in this setting. -/
theorem integral_smul_fourierInv_sub {K : ℝ → ℂ} (hK : Integrable K) {H : ℝ → X}
    (hH : Integrable H) (x : ℝ) :
    ∫ s, K s • 𝓕⁻ H (x - s) = 𝓕⁻ (fun ξ => 𝓕 K ξ • H ξ) x := by
  by_cases hX : CompleteSpace X
  swap
  · simp [Real.fourierInv_eq', integral, hX]
  have hint : Integrable (Function.uncurry fun s v : ℝ => (K s * expChar v (x - s)) • H v)
      (volume.prod volume) := by
    have h := (hK.smul_prod hH).bdd_smul 1 (φ := fun p : ℝ × ℝ => expChar p.2 (x - p.1))
      (by unfold expChar; fun_prop : Continuous fun p : ℝ × ℝ =>
        expChar p.2 (x - p.1)).aestronglyMeasurable
      (ae_of_all _ fun p => (norm_expChar _ _).le)
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [Pi.smul_apply', Function.uncurry, smul_smul]
    rw [mul_comm]
  have h1 : ∫ s, K s • 𝓕⁻ H (x - s) = ∫ s, ∫ v, (K s * expChar v (x - s)) • H v := by
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only
    rw [fourierInv_eq_expChar, ← integral_smul]
    simp only [smul_smul]
  rw [h1, integral_integral_swap hint, fourierInv_eq_expChar]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [integral_smul_const, integral_mul_expChar_sub, mul_smul]

/-- The modulations of the functions in `L^p` are in `L^p`. -/
theorem memLp_expChar_smul {p : ℝ≥0∞} {f : ℝ → X} (hf : MemLp f p volume) (a : ℝ) :
    MemLp (fun x => expChar a x • f x) p volume :=
  hf.of_le ((continuous_expChar a).aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by rw [norm_smul, norm_expChar, one_mul])

/-- HNVW I, (5.35), p. 404, with a factor `s`: `T_{s sgn (· − a)} f = s e_a T_{sgn} (e_{−a} f)`,
where `G (· + a)` is the Fourier transform of `e_{−a} f`. -/
theorem fourierInv_sign_sub (s a : ℝ) (G : ℝ → X) :
    (𝓕⁻ fun ξ => ((s * Real.sign (ξ - a) : ℝ) : ℂ) • G ξ) =
      fun x => ((s : ℂ) * expChar a x) • 𝓕⁻ (fun ξ => (Real.sign ξ : ℂ) • G (ξ + a)) x := by
  funext x
  have h := fourierInv_smul_expChar (-a) (fun ξ => (Real.sign ξ : ℂ) • G (ξ + a)) x
  simp only [neg_neg, ← sub_eq_add_neg, sub_add_cancel] at h
  rw [mul_smul, ← h, ← fourierInv_const_smul]
  simp only [Complex.ofReal_mul, mul_smul]

/-- Reflections of the line. -/
theorem fourierInv_comp_neg (F : ℝ → X) (x : ℝ) : 𝓕⁻ (fun ξ => F (-ξ)) x = 𝓕⁻ F (-x) :=
  Real.fourierInv_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) F x

/-- The inverse Fourier transforms of Schwartz functions are in `L^r (ℝ; X)`. -/
theorem memLp_fourierInv (G : 𝓢(ℝ, X)) (r : ℝ≥0∞) : MemLp (𝓕⁻ (G : ℝ → X)) r volume := by
  rw [← SchwartzMap.fourierInv_coe]
  exact (𝓕⁻ G : 𝓢(ℝ, X)).memLp r volume

end HarmonicAnalysis
