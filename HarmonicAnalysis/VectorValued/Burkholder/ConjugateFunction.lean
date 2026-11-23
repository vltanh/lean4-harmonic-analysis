/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Burkholder.Conjugate
import BanachProbability.UMD.Hilbert
import HarmonicAnalysis.FourierMultiplier.Density

/-!
# The conjugate function on UMD spaces

D. L. Burkholder, *A geometric condition that implies the existence of certain singular integrals of
Banach-space-valued functions* (1983), Lemma 3 and (33) (pp. 282–283). Let `X` be a real Banach
space, `1 < p < ∞`, `β` a `UMD_p` constant of `X`, and `f ∈ L^p (𝕋; X)`, `𝕋 = ℝ / 2πℤ`, with the
measure `dθ / 2π` (in the source `dθ`, which does not affect the constants). The
functions (30) and (31) are `u (r e^{iθ})` (`discPoissonInt r f θ`) and `v (r e^{iθ})`
(`discConjPoissonInt r f θ`), written with `f (θ − t)` (the kernels are periodic), and the truncated
conjugate function is `f̃_ε` (`truncatedConj ε f`).

* `eLpNorm_discConjPoissonInt_le` (Lemma 3): `‖v (r e^{iθ})‖_p ≤ 2 β² ‖u (r e^{iθ})‖_p`. With
  `z = r e^{it}`, the kernels are `1 + 2 Re (z / (1 − z))` and `2 Im (z / (1 − z))`, and
  `z / (1 − z)` is the uniform limit on `|z| = r` of `Σ_{k=1}^N z^k`. So `u − u (0)` and `v` are the
  uniform limits on `|z| = r` of the functions of the form (18) and (19) whose coefficients `a_k`,
  `b_k` are the Fourier coefficients of `f` (`norm_harmPoly_coeff_sub_le`,
  `norm_conjHarmPoly_coeff_sub_le`). Lemma 2 gives `‖v‖_p ≤ β² ‖u − u (0)‖_p`
  (`eLpNorm_discConjPoissonInt_le_sub`), and `‖u (0)‖ ≤ ‖u‖_p`, because `u (0)` is the mean of `u`.
* `norm_truncatedConj_sub_le`, `integral_truncationError_lt`: for `r = 1 − ε`,
  `|f̃_ε (θ) − v (r e^{iθ})| ≤ (2π)⁻¹ ∫_{−π}^π |f (θ − t)| K_r (t) dt` and `(2π)⁻¹ ∫ K_r < 1`.
* `eLpNorm_truncatedConj_le` (33): `‖f̃_ε‖_p ≤ (2 β² + 1) ‖f‖_p`, from these and Young's inequality
  for convolution (`eLpNorm_circConv_le`), which also gives `‖u (r e^{iθ})‖_p ≤ ‖f‖_p`.

The source asserts that there is a nonnegative function `K_r` with the two properties; here `K_r` is
the modulus of the difference of the two kernels (`truncationError`), and its integral is computed.
In the source the hypothesis is that `X` is ζ-convex and the constants `c_p (B)` change from line to
line; here they are explicit in `β`. The definition of a `UMD_p` constant allows `β = ∞`, a case
without counterpart in the source: Lemma 3 says then that `v = 0` if `u = 0`
(`discConjPoissonInt_eq_zero`).
-/

@[expose] public section

open MeasureTheory BanachProbability AddCircle Filter Topology
open scoped ENNReal Real

namespace HarmonicAnalysis

attribute [local instance] fact_zero_lt_two_pi

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The kernel `(1 − r²) / (1 − 2r cos t + r²)` of (30). -/
noncomputable def discPoisson (r t : ℝ) : ℝ :=
  (1 - r ^ 2) / (1 - 2 * r * Real.cos t + r ^ 2)

/-- The kernel `2r sin t / (1 − 2r cos t + r²)` of (31). -/
noncomputable def discConjPoisson (r t : ℝ) : ℝ :=
  2 * r * Real.sin t / (1 - 2 * r * Real.cos t + r ^ 2)

/-- (30), after the substitution `t ↦ θ − t`:
`u (r e^{iθ}) = (2π)⁻¹ ∫_{−π}^π (1 − r²) / (1 − 2r cos t + r²) f (θ − t) dt`. -/
noncomputable def discPoissonInt (r : ℝ) (f : AddCircle (2 * π) → X) (θ : AddCircle (2 * π)) : X :=
  (2 * π)⁻¹ • ∫ t in -π..π, discPoisson r t • f (θ - t)

/-- (31), after the substitution `t ↦ θ − t`:
`v (r e^{iθ}) = (2π)⁻¹ ∫_{−π}^π 2r sin t / (1 − 2r cos t + r²) f (θ − t) dt`. -/
noncomputable def discConjPoissonInt (r : ℝ) (f : AddCircle (2 * π) → X) (θ : AddCircle (2 * π)) :
    X :=
  (2 * π)⁻¹ • ∫ t in -π..π, discConjPoisson r t • f (θ - t)

/-- `f̃_ε (θ) = (2π)⁻¹ ∫_{ε < |t| < π} f (θ − t) cot (t / 2) dt` (p. 283). -/
noncomputable def truncatedConj (ε : ℝ) (f : AddCircle (2 * π) → X) (θ : AddCircle (2 * π)) : X :=
  (2 * π)⁻¹ • ∫ t in {t : ℝ | ε < |t| ∧ |t| < π}, Real.cot (t / 2) • f (θ - t)

/-! ### The kernels -/

/-- `z / (1 − z)` at `z = r e^{iθ}`. -/
private noncomputable def discKer (r : ℝ) (θ : AddCircle (2 * π)) : ℂ :=
  r * fourier 1 θ / (1 - r * fourier 1 θ)

/-- `|r e^{iθ}| = r`. -/
private theorem norm_mul_fourier {r : ℝ} (hr0 : 0 ≤ r) (θ : AddCircle (2 * π)) :
    ‖(r : ℂ) * fourier 1 θ‖ = r := by
  rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr0]

/-- `1 − r ≤ |1 − r e^{iθ}|`. -/
private theorem le_norm_one_sub {r : ℝ} (hr0 : 0 ≤ r) (θ : AddCircle (2 * π)) :
    1 - r ≤ ‖1 - (r : ℂ) * fourier 1 θ‖ := by
  have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * fourier 1 θ)
  rwa [norm_one, norm_mul_fourier hr0] at h

/-- `1 − r e^{iθ} ≠ 0` for `r < 1`. -/
private theorem one_sub_mul_fourier_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (θ : AddCircle (2 * π)) : 1 - (r : ℂ) * fourier 1 θ ≠ 0 :=
  norm_pos_iff.1 (lt_of_lt_of_le (by linarith) (le_norm_one_sub hr0 θ))

/-- The function `z / (1 − z)` is continuous on the circle `|z| = r`. -/
private theorem continuous_discKer {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (discKer r) := by
  have h : Continuous fun θ : AddCircle (2 * π) => (r : ℂ) * fourier 1 θ :=
    continuous_const.mul (map_continuous (fourier 1))
  exact h.div (continuous_const.sub h) (one_sub_mul_fourier_ne_zero hr0 hr1)

/-- `e^{it} = cos t + i sin t` on the circle. -/
private theorem fourier_one_coe (t : ℝ) :
    fourier 1 (t : AddCircle (2 * π)) = (Real.cos t : ℂ) + Real.sin t * Complex.I := by
  rw [fourier_coe_apply, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
  congr 1
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- `0 < 1 − 2r cos t + r²` for `r < 1`. -/
private theorem denom_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 < 1 - 2 * r * Real.cos t + r ^ 2 := by
  nlinarith [Real.cos_le_one t, mul_nonneg hr0 (sub_nonneg.2 (Real.cos_le_one t)),
    mul_pos (sub_pos.2 hr1) (sub_pos.2 hr1)]

/-- `z / (1 − z) = (r cos t − r² + i r sin t) / (1 − 2r cos t + r²)` at `z = r e^{it}`. -/
private theorem discKer_coe {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    discKer r (t : AddCircle (2 * π)) =
      ((r * Real.cos t - r ^ 2) / (1 - 2 * r * Real.cos t + r ^ 2) : ℝ) +
        (r * Real.sin t / (1 - 2 * r * Real.cos t + r ^ 2) : ℝ) * Complex.I := by
  have h1 := one_sub_mul_fourier_ne_zero hr0 hr1 (t : AddCircle (2 * π))
  have hD : ((1 - 2 * r * Real.cos t + r ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (denom_pos hr0 hr1 t).ne'
  rw [fourier_one_coe] at h1
  rw [discKer, fourier_one_coe, div_eq_iff h1, Complex.ofReal_div, Complex.ofReal_div,
    div_mul_eq_mul_div, ← add_div, div_mul_eq_mul_div, eq_div_iff hD]
  have hcs : (Real.sin t : ℂ) ^ 2 = 1 - (Real.cos t : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sin_sq]
    push_cast
    ring
  push_cast at hcs ⊢
  linear_combination (r : ℂ) ^ 2 * Complex.sin t ^ 2 * Complex.I_sq - (r : ℂ) ^ 2 * hcs

/-- `(1 − r²) / (1 − 2r cos t + r²) = 1 + 2 Re (z / (1 − z))`, `z = r e^{it}`. -/
private theorem discPoisson_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    discPoisson r t = 1 + 2 * (discKer r (t : AddCircle (2 * π))).re := by
  have hD := (denom_pos hr0 hr1 t).ne'
  rw [discKer_coe hr0 hr1, discPoisson, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
    Complex.I_re, mul_zero, add_zero, ← mul_div_assoc, div_eq_iff hD, add_mul, div_mul_cancel₀ _ hD]
  ring

/-- `2r sin t / (1 − 2r cos t + r²) = 2 Im (z / (1 − z))`, `z = r e^{it}`. -/
private theorem discConjPoisson_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    discConjPoisson r t = 2 * (discKer r (t : AddCircle (2 * π))).im := by
  rw [discKer_coe hr0 hr1, discConjPoisson, Complex.add_im, Complex.ofReal_im,
    Complex.im_ofReal_mul, Complex.I_im, mul_one, zero_add]
  ring

/-- `Σ_{k=1}^N z^k = (z − z^{N+1}) / (1 − z)` differs from `z / (1 − z)` by at most
`r^{N+1} / (1 − r)` on the circle `|z| = r`. -/
private theorem norm_sum_pow_sub_discKer_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ)
    (θ : AddCircle (2 * π)) :
    ‖∑ k ∈ Finset.Icc 1 N, ((r : ℂ) * fourier 1 θ) ^ k - discKer r θ‖ ≤ r ^ (N + 1) / (1 - r) := by
  have h1 := one_sub_mul_fourier_ne_zero hr0 hr1 θ
  set z : ℂ := (r : ℂ) * fourier 1 θ with hz
  have hsum : ∑ k ∈ Finset.Icc 1 N, z ^ k - discKer r θ = -(z ^ (N + 1) / (1 - z)) := by
    rw [discKer, ← hz, sub_eq_iff_eq_add, ← sub_eq_neg_add, ← sub_div, eq_div_iff h1]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
      ring
  rw [hsum, norm_neg, norm_div, norm_pow, norm_mul_fourier hr0]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (le_norm_one_sub hr0 θ)

/-! ### Convolutions on the circle -/

/-- `(2π)⁻¹ ∫_{−π}^π k (t) f (θ − t) dt`. -/
private noncomputable def circConv (k : ℝ → ℝ) (f : AddCircle (2 * π) → X)
    (θ : AddCircle (2 * π)) : X :=
  (2 * π)⁻¹ • ∫ t in Set.Ioc (-π) π, k t • f (θ - t)

/-- The projection of `(−π, π]` onto the circle preserves the measure. -/
private theorem measurePreserving_coe :
    MeasurePreserving (fun t : ℝ => (t : AddCircle (2 * π)))
      (volume.restrict (Set.Ioc (-π) π)) volume := by
  have h := AddCircle.measurePreserving_mk (2 * π) (-π)
  rwa [show -π + 2 * π = π by ring] at h

/-- `t ↦ θ − t`, from `(−π, π]` to the circle, preserves the measure. -/
private theorem measurePreserving_sub_coe (θ : AddCircle (2 * π)) :
    MeasurePreserving (fun t : ℝ => θ - (t : AddCircle (2 * π)))
      (volume.restrict (Set.Ioc (-π) π)) volume :=
  (volume.measurePreserving_sub_left θ).comp measurePreserving_coe

/-- Null sets for `haarAddCircle` and for the measure of mass `2π` are the same. -/
private theorem volume_absolutelyContinuous_haar :
    (volume : Measure (AddCircle (2 * π))) ≪ haarAddCircle := by
  rw [volume_eq_smul_haarAddCircle]
  exact Measure.smul_absolutelyContinuous

omit [NormedSpace ℝ X] in
/-- `f (θ − t)` is integrable in `t ∈ (−π, π]`. -/
private theorem integrable_sub_coe {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle)
    (θ : AddCircle (2 * π)) :
    Integrable (fun t : ℝ => f (θ - t)) (volume.restrict (Set.Ioc (-π) π)) := by
  have h : Integrable f volume := by
    rw [volume_eq_smul_haarAddCircle]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (measurePreserving_sub_coe θ).integrable_comp_of_integrable h

/-- `k (t) f (θ − t)` is integrable in `t ∈ (−π, π]` for a bounded kernel `k`. -/
private theorem integrable_smul_sub_coe {f : AddCircle (2 * π) → X}
    (hf : Integrable f haarAddCircle) (θ : AddCircle (2 * π)) {k : ℝ → ℝ} (hk : Measurable k)
    {C : ℝ} (hC : ∀ t ∈ Set.Ioc (-π) π, |k t| ≤ C) :
    Integrable (fun t : ℝ => k t • f (θ - t)) (volume.restrict (Set.Ioc (-π) π)) :=
  (integrable_sub_coe hf θ).bdd_smul C hk.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hC))

/-- `circConv k f θ` depends only on the class of `f`, for every `θ`. -/
private theorem circConv_congr (k : ℝ → ℝ) {f g : AddCircle (2 * π) → X}
    (hfg : f =ᵐ[haarAddCircle] g) : circConv k f = circConv k g := by
  funext θ
  have h : ∀ᵐ t ∂volume.restrict (Set.Ioc (-π) π), f (θ - (t : ℝ)) = g (θ - t) :=
    (measurePreserving_sub_coe θ).quasiMeasurePreserving.ae
      (volume_absolutelyContinuous_haar.ae_le hfg)
  have h' : (fun t : ℝ => k t • f (θ - t)) =ᵐ[volume.restrict (Set.Ioc (-π) π)]
      fun t : ℝ => k t • g (θ - t) := h.mono fun t ht => by simp only [ht]
  rw [circConv, circConv, integral_congr_ae h']

/-- `circConv k f` is strongly measurable. -/
private theorem stronglyMeasurable_circConv {k : ℝ → ℝ} (hk : Measurable k)
    {f : AddCircle (2 * π) → X} (hf : AEStronglyMeasurable f haarAddCircle) :
    StronglyMeasurable (circConv k f) := by
  rw [circConv_congr k hf.ae_eq_mk]
  have hF : StronglyMeasurable fun q : AddCircle (2 * π) × ℝ => hf.mk f (q.1 - q.2) :=
    hf.stronglyMeasurable_mk.comp_measurable
      (measurable_fst.sub (AddCircle.measurable_mk'.comp measurable_snd))
  exact (((hk.comp measurable_snd).stronglyMeasurable.smul hF).integral_prod_right).const_smul _

/-- **Young's inequality** on the circle: `‖(2π)⁻¹ ∫ k (t) f (· − t) dt‖_p ≤
(2π)⁻¹ ∫ |k| · ‖f‖_p`. -/
private theorem eLpNorm_circConv_le {p : ℝ} (hp : 1 ≤ p) {k : ℝ → ℝ} (hk : Measurable k)
    {f : AddCircle (2 * π) → X} (hf : AEStronglyMeasurable f haarAddCircle) :
    eLpNorm (circConv k f) (ENNReal.ofReal p) haarAddCircle ≤
      (∫⁻ t in Set.Ioc (-π) π, ‖(2 * π)⁻¹ * k t‖ₑ) *
        eLpNorm f (ENNReal.ofReal p) haarAddCircle := by
  have hg : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  rw [eLpNorm_congr_ae hf.ae_eq_mk, circConv_congr k hf.ae_eq_mk]
  set g := hf.mk f
  have hF : StronglyMeasurable
      (Function.uncurry fun (θ : AddCircle (2 * π)) (t : ℝ) => g (θ - t)) :=
    hg.comp_measurable (measurable_fst.sub (AddCircle.measurable_mk'.comp measurable_snd))
  have h : circConv k g = fun θ : AddCircle (2 * π) =>
      ∫ t in Set.Ioc (-π) π, ((2 * π)⁻¹ * k t) • g (θ - t) := funext fun θ => by
    rw [circConv, ← integral_smul]
    simp_rw [smul_smul]
  rw [h]
  refine eLpNorm_integral_smul_le hp (hk.const_mul _) hF (ae_of_all _ fun t => ?_)
  exact (eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
    (measurePreserving_sub_right haarAddCircle (t : AddCircle (2 * π)))).le

/-- For a kernel `k` that comes from a function `K` on the circle, `circConv k f θ` is the integral
of `K (θ − s) f (s)` over the circle. -/
private theorem circConv_eq_integral {k : ℝ → ℝ} {K : AddCircle (2 * π) → ℝ}
    (hkK : ∀ t : ℝ, k t = K t) (f : AddCircle (2 * π) → X) (θ : AddCircle (2 * π)) :
    circConv k f θ = ∫ s, K (θ - s) • f s ∂haarAddCircle := by
  have h := AddCircle.integral_preimage (2 * π) (-π) fun s => K s • f (θ - s)
  rw [show -π + 2 * π = π by ring] at h
  rw [circConv, ← integral_sub_left_eq_self (fun s => K (θ - s) • f s) haarAddCircle θ,
    integral_haarAddCircle]
  simp only [hkK, sub_sub_cancel, h]

/-- `circConv` for the kernel (30). -/
private theorem discPoissonInt_eq (r : ℝ) (f : AddCircle (2 * π) → X) :
    discPoissonInt r f = circConv (discPoisson r) f := by
  funext θ
  rw [discPoissonInt, circConv, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- `circConv` for the kernel (31). -/
private theorem discConjPoissonInt_eq (r : ℝ) (f : AddCircle (2 * π) → X) :
    discConjPoissonInt r f = circConv (discConjPoisson r) f := by
  funext θ
  rw [discConjPoissonInt, circConv, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- The kernel of `f̃_ε`. -/
private noncomputable def truncCot (ε : ℝ) : ℝ → ℝ :=
  Set.indicator {t : ℝ | ε < |t|} fun t => Real.cot (t / 2)

/-- `circConv` for the kernel of `f̃_ε`. -/
private theorem truncatedConj_eq (ε : ℝ) (f : AddCircle (2 * π) → X) :
    truncatedConj ε f = circConv (truncCot ε) f := by
  funext θ
  have hs : MeasurableSet {t : ℝ | ε < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hk : ∀ t : ℝ, truncCot ε t • f (θ - t) =
      Set.indicator {t : ℝ | ε < |t|} (fun t : ℝ => Real.cot (t / 2) • f (θ - t)) t := fun t => by
    by_cases ht : t ∈ {t : ℝ | ε < |t|}
    · rw [truncCot, Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    · rw [truncCot, Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_smul]
  rw [truncatedConj, circConv, integral_congr_ae (ae_of_all _ hk), setIntegral_indicator hs]
  congr 1
  refine setIntegral_congr_set ?_
  have hset : {t : ℝ | ε < |t| ∧ |t| < π} = Set.Ioo (-π) π ∩ {t : ℝ | ε < |t|} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioo, abs_lt]
    tauto
  rw [hset]
  exact Ioo_ae_eq_Ioc.inter (ae_eq_refl _)

/-! ### The Poisson integrals as uniform limits of harmonic polynomials -/

/-- `u (r e^{iθ}) = ∫ P (θ − s) f (s)`, an integral over the circle. -/
private theorem discPoissonInt_apply {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (f : AddCircle (2 * π) → X) (θ : AddCircle (2 * π)) :
    discPoissonInt r f θ = ∫ s, (1 + 2 * (discKer r (θ - s)).re) • f s ∂haarAddCircle := by
  rw [discPoissonInt_eq, circConv_eq_integral (K := fun s => 1 + 2 * (discKer r s).re)
    (discPoisson_eq hr0 hr1)]

/-- `v (r e^{iθ}) = ∫ Q (θ − s) f (s)`, an integral over the circle. -/
private theorem discConjPoissonInt_apply {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (f : AddCircle (2 * π) → X) (θ : AddCircle (2 * π)) :
    discConjPoissonInt r f θ = ∫ s, (2 * (discKer r (θ - s)).im) • f s ∂haarAddCircle := by
  rw [discConjPoissonInt_eq, circConv_eq_integral (K := fun s => 2 * (discKer r s).im)
    (discConjPoisson_eq hr0 hr1)]

/-- The product of a continuous kernel and an integrable function is integrable. -/
private theorem integrable_continuous_smul {K : AddCircle (2 * π) → ℝ} (hK : Continuous K)
    {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) :
    Integrable (fun s => K s • f s) haarAddCircle := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  exact hf.bdd_smul C hK.aestronglyMeasurable (ae_of_all _ fun s => hC s (Set.mem_univ s))

/-- The convolution of a continuous kernel and an integrable function is continuous. -/
private theorem continuous_integral_smul {K : AddCircle (2 * π) → ℝ} (hK : Continuous K)
    {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) :
    Continuous fun θ => ∫ s, K (θ - s) • f s ∂haarAddCircle := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  refine continuous_of_dominated (bound := fun s => C * ‖f s‖) (fun θ => ?_)
    (fun θ => ae_of_all _ fun s => ?_) (hf.norm.const_mul C) (ae_of_all _ fun s => ?_)
  · exact (integrable_continuous_smul (hK.comp (continuous_const.sub continuous_id))
      hf).aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC _ (Set.mem_univ _)) (norm_nonneg _)
  · exact (hK.comp (continuous_id.sub continuous_const)).smul continuous_const

/-- `u` is continuous on the circle `|z| = r`. -/
private theorem continuous_discPoissonInt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) :
    Continuous (discPoissonInt r f) := by
  rw [funext (discPoissonInt_apply hr0 hr1 f)]
  exact continuous_integral_smul (K := fun s => 1 + 2 * (discKer r s).re) (continuous_const.add
    (continuous_const.mul (Complex.continuous_re.comp (continuous_discKer hr0 hr1)))) hf

/-- `v` is continuous on the circle `|z| = r`. -/
private theorem continuous_discConjPoissonInt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) :
    Continuous (discConjPoissonInt r f) := by
  rw [funext (discConjPoissonInt_apply hr0 hr1 f)]
  exact continuous_integral_smul (K := fun s => 2 * (discKer r s).im)
    (continuous_const.mul (Complex.continuous_im.comp (continuous_discKer hr0 hr1))) hf

/-- The Fourier coefficient `a_k = 2 ∫ cos (ks) f (s)`. -/
private noncomputable def cosCoeff (f : AddCircle (2 * π) → X) (k : ℕ) : X :=
  ∫ s, (2 * (fourier (k : ℤ) s : ℂ).re) • f s ∂haarAddCircle

/-- The Fourier coefficient `b_k = 2 ∫ sin (ks) f (s)`. -/
private noncomputable def sinCoeff (f : AddCircle (2 * π) → X) (k : ℕ) : X :=
  ∫ s, (2 * (fourier (k : ℤ) s : ℂ).im) • f s ∂haarAddCircle

/-- `(r e^{i(θ − s)})^k = (r e^{iθ})^k e^{−iks}`. -/
private theorem mul_fourier_sub_pow (r : ℝ) (k : ℕ) (θ s : AddCircle (2 * π)) :
    ((r : ℂ) * fourier 1 (θ - s)) ^ k =
      ((r : ℂ) * fourier 1 θ) ^ k * (starRingEnd ℂ) (fourier (k : ℤ) s) := by
  have h1 : fourier 1 (θ - s) = fourier 1 θ * (starRingEnd ℂ) (fourier 1 s) := by
    rw [← fourier_neg, fourier_one, fourier_apply, fourier_apply, one_zsmul, neg_one_zsmul,
      sub_eq_add_neg, toCircle_add, Circle.coe_mul]
  rw [h1, fourier_natCast, map_pow]
  ring

/-- `cos (kt)`, `sin (kt)` are continuous. -/
private theorem continuous_fourier_re_im (k : ℤ) :
    Continuous (fun s : AddCircle (2 * π) => 2 * (fourier k s : ℂ).re) ∧
      Continuous fun s : AddCircle (2 * π) => 2 * (fourier k s : ℂ).im :=
  ⟨continuous_const.mul (Complex.continuous_re.comp (map_continuous (fourier k))),
    continuous_const.mul (Complex.continuous_im.comp (map_continuous (fourier k)))⟩

/-- The partial sum `Σ_{k=1}^N z^k` is continuous on the circle `|z| = r`. -/
private theorem continuous_sum_pow (r : ℝ) (N : ℕ) :
    Continuous fun θ : AddCircle (2 * π) => ∑ k ∈ Finset.Icc 1 N, ((r : ℂ) * fourier 1 θ) ^ k :=
  continuous_finsetSum _ fun k _ => (continuous_const.mul (map_continuous (fourier 1))).pow k

/-- The function (18) whose coefficients are the Fourier coefficients of `f` is the convolution of
`f` and `2 Re Σ_{k=1}^N z^k = 2 Σ_{k=1}^N r^k cos kt`. -/
private theorem harmPoly_coeff_eq (r : ℝ) (N : ℕ) {f : AddCircle (2 * π) → X}
    (hf : Integrable f haarAddCircle) (θ : AddCircle (2 * π)) :
    harmPoly N (cosCoeff f) (sinCoeff f) (r * fourier 1 θ) =
      ∫ s, (2 * (∑ k ∈ Finset.Icc 1 N, ((r : ℂ) * fourier 1 (θ - s)) ^ k).re) • f s
        ∂haarAddCircle := by
  have hc := fun k : ℕ => integrable_continuous_smul (continuous_fourier_re_im k).1 hf
  have hs := fun k : ℕ => integrable_continuous_smul (continuous_fourier_re_im k).2 hf
  have hterm : ∀ (k : ℕ) (s : AddCircle (2 * π)),
      (2 * (((r : ℂ) * fourier 1 (θ - s)) ^ k).re) • f s =
        (((r : ℂ) * fourier 1 θ) ^ k).re • (2 * (fourier (k : ℤ) s : ℂ).re) • f s +
          (((r : ℂ) * fourier 1 θ) ^ k).im • (2 * (fourier (k : ℤ) s : ℂ).im) • f s := by
    intro k s
    rw [mul_fourier_sub_pow, smul_smul, smul_smul, ← add_smul, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    congr 1
    ring
  simp only [Complex.re_sum, Finset.mul_sum, Finset.sum_smul]
  rw [harmPoly, integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_congr_ae (ae_of_all _ (hterm k)), cosCoeff, sinCoeff, ← integral_smul,
      ← integral_smul]
    exact (integral_add ((hc k).smul _) ((hs k).smul _)).symm
  · rw [funext (hterm k)]
    exact ((hc k).smul _).add ((hs k).smul _)

/-- The function (19) whose coefficients are the Fourier coefficients of `f` is the convolution of
`f` and `2 Im Σ_{k=1}^N z^k = 2 Σ_{k=1}^N r^k sin kt`. -/
private theorem conjHarmPoly_coeff_eq (r : ℝ) (N : ℕ) {f : AddCircle (2 * π) → X}
    (hf : Integrable f haarAddCircle) (θ : AddCircle (2 * π)) :
    conjHarmPoly N (cosCoeff f) (sinCoeff f) (r * fourier 1 θ) =
      ∫ s, (2 * (∑ k ∈ Finset.Icc 1 N, ((r : ℂ) * fourier 1 (θ - s)) ^ k).im) • f s
        ∂haarAddCircle := by
  have hc := fun k : ℕ => integrable_continuous_smul (continuous_fourier_re_im k).1 hf
  have hs := fun k : ℕ => integrable_continuous_smul (continuous_fourier_re_im k).2 hf
  have hterm : ∀ (k : ℕ) (s : AddCircle (2 * π)),
      (2 * (((r : ℂ) * fourier 1 (θ - s)) ^ k).im) • f s =
        (((r : ℂ) * fourier 1 θ) ^ k).im • (2 * (fourier (k : ℤ) s : ℂ).re) • f s -
          (((r : ℂ) * fourier 1 θ) ^ k).re • (2 * (fourier (k : ℤ) s : ℂ).im) • f s := by
    intro k s
    rw [mul_fourier_sub_pow, smul_smul, smul_smul, ← sub_smul, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    congr 1
    ring
  simp only [Complex.im_sum, Finset.mul_sum, Finset.sum_smul]
  rw [conjHarmPoly, integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_congr_ae (ae_of_all _ (hterm k)), cosCoeff, sinCoeff, ← integral_smul,
      ← integral_smul]
    exact (integral_sub ((hc k).smul _) ((hs k).smul _)).symm
  · rw [funext (hterm k)]
    exact ((hc k).smul _).sub ((hs k).smul _)

/-- A kernel bounded by `c`: `|∫ K (s) f (s)| ≤ c ∫ |f|`. -/
private theorem norm_integral_smul_le {K : AddCircle (2 * π) → ℝ} {c : ℝ} (hc : ∀ s, |K s| ≤ c)
    {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) :
    ‖∫ s, K s • f s ∂haarAddCircle‖ ≤ c * ∫ s, ‖f s‖ ∂haarAddCircle := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.norm.const_mul c) (ae_of_all _ fun s => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hc s) (norm_nonneg _)

/-- The bound for the uniform approximation. -/
private noncomputable def approxErr (r : ℝ) (f : AddCircle (2 * π) → X) (N : ℕ) : ℝ :=
  2 * (r ^ (N + 1) / (1 - r)) * ∫ s, ‖f s‖ ∂haarAddCircle

/-- `u − u (0)` is the uniform limit on the circle `|z| = r` of functions of the form (18). -/
private theorem norm_harmPoly_coeff_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) (N : ℕ)
    (θ : AddCircle (2 * π)) :
    ‖harmPoly N (cosCoeff f) (sinCoeff f) (r * fourier 1 θ) -
      (discPoissonInt r f θ - ∫ s, f s ∂haarAddCircle)‖ ≤ approxErr r f N := by
  have hsub : Continuous fun s : AddCircle (2 * π) => θ - s := continuous_const.sub continuous_id
  have hG := integrable_continuous_smul (K := fun s => 2 * (discKer r (θ - s)).re)
    (continuous_const.mul (Complex.continuous_re.comp
      ((continuous_discKer hr0 hr1).comp hsub))) hf
  have hS := integrable_continuous_smul
    (K := fun s => 2 * (∑ k ∈ Finset.Icc 1 N, ((r : ℂ) * fourier 1 (θ - s)) ^ k).re)
    (continuous_const.mul (Complex.continuous_re.comp
      ((continuous_sum_pow r N).comp hsub))) hf
  simp only [harmPoly_coeff_eq r N hf, discPoissonInt_apply hr0 hr1, add_smul, one_smul]
  rw [integral_add hf hG, add_sub_cancel_left, ← integral_sub hS hG]
  simp only [← sub_smul, ← mul_sub, ← Complex.sub_re]
  refine norm_integral_smul_le (fun s => ?_) hf
  rw [abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
    (norm_sum_pow_sub_discKer_le hr0 hr1 N _)) zero_le_two

/-- `v` is the uniform limit on the circle `|z| = r` of functions of the form (19). -/
private theorem norm_conjHarmPoly_coeff_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) (N : ℕ)
    (θ : AddCircle (2 * π)) :
    ‖conjHarmPoly N (cosCoeff f) (sinCoeff f) (r * fourier 1 θ) - discConjPoissonInt r f θ‖ ≤
      approxErr r f N := by
  have hsub : Continuous fun s : AddCircle (2 * π) => θ - s := continuous_const.sub continuous_id
  have hG := integrable_continuous_smul (K := fun s => 2 * (discKer r (θ - s)).im)
    (continuous_const.mul (Complex.continuous_im.comp
      ((continuous_discKer hr0 hr1).comp hsub))) hf
  have hS := integrable_continuous_smul
    (K := fun s => 2 * (∑ k ∈ Finset.Icc 1 N, ((r : ℂ) * fourier 1 (θ - s)) ^ k).im)
    (continuous_const.mul (Complex.continuous_im.comp
      ((continuous_sum_pow r N).comp hsub))) hf
  simp only [conjHarmPoly_coeff_eq r N hf, discConjPoissonInt_apply hr0 hr1]
  rw [← integral_sub hS hG]
  simp only [← sub_smul, ← mul_sub, ← Complex.sub_im]
  refine norm_integral_smul_le (fun s => ?_) hf
  rw [abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans
    (norm_sum_pow_sub_discKer_le hr0 hr1 N _)) zero_le_two

omit [NormedSpace ℝ X] in
/-- The bound for the approximation tends to `0`. -/
private theorem tendsto_approxErr {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (f : AddCircle (2 * π) → X) : Tendsto (approxErr r f) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
  have h2 := ((h.div_const (1 - r)).const_mul 2).mul_const (∫ s, ‖f s‖ ∂haarAddCircle)
  rw [zero_div, mul_zero, zero_mul] at h2
  exact h2

/-! ### Lemma 3 -/

/-- `∫ (r e^{iθ})^k dθ = 0` for `k ≥ 1`. -/
private theorem integral_mul_fourier_pow (r : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∫ θ : AddCircle (2 * π), ((r : ℂ) * fourier 1 θ) ^ k ∂haarAddCircle = 0 := by
  have h2 : ∀ θ : AddCircle (2 * π), ((r : ℂ) * fourier 1 θ) ^ k =
      (r : ℂ) ^ k * fourier (k : ℤ) θ := fun θ => by
    rw [mul_pow, fourier_natCast]
  have h := congrFun (fourierCoeff_fourier (T := 2 * π) (k : ℤ)) 0
  rw [Pi.single_eq_of_ne (by omega), fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  simp only [h2, integral_const_mul, h, mul_zero]

/-- The functions (18) have mean `u (0) = 0` on the circle `|z| = r`. -/
private theorem integral_harmPoly [CompleteSpace X] (r : ℝ) (N : ℕ) (a b : ℕ → X) :
    ∫ θ : AddCircle (2 * π), harmPoly N a b (r * fourier 1 θ) ∂haarAddCircle = 0 := by
  have hz : ∀ k : ℕ, Continuous fun θ : AddCircle (2 * π) => ((r : ℂ) * fourier 1 θ) ^ k :=
    fun k => (continuous_const.mul (map_continuous (fourier 1))).pow k
  have hre : ∀ k, Integrable (fun θ : AddCircle (2 * π) =>
      (((r : ℂ) * fourier 1 θ) ^ k).re • a k) haarAddCircle := fun k =>
    integrable_haar_of_continuous ((Complex.continuous_re.comp (hz k)).smul continuous_const)
  have him : ∀ k, Integrable (fun θ : AddCircle (2 * π) =>
      (((r : ℂ) * fourier 1 θ) ^ k).im • b k) haarAddCircle := fun k =>
    integrable_haar_of_continuous ((Complex.continuous_im.comp (hz k)).smul continuous_const)
  have hre0 : ∀ k : ℕ, 1 ≤ k →
      ∫ θ : AddCircle (2 * π), (((r : ℂ) * fourier 1 θ) ^ k).re ∂haarAddCircle = 0 :=
    fun k hk => by
      have h := Complex.reCLM.integral_comp_comm (integrable_haar_of_continuous (hz k))
      rw [integral_mul_fourier_pow r hk, map_zero] at h
      exact h
  have him0 : ∀ k : ℕ, 1 ≤ k →
      ∫ θ : AddCircle (2 * π), (((r : ℂ) * fourier 1 θ) ^ k).im ∂haarAddCircle = 0 :=
    fun k hk => by
      have h := Complex.imCLM.integral_comp_comm (integrable_haar_of_continuous (hz k))
      rw [integral_mul_fourier_pow r hk, map_zero] at h
      exact h
  simp only [harmPoly]
  rw [integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_eq_zero fun k hk => ?_
    have hk1 := (Finset.mem_Icc.1 hk).1
    rw [integral_add (hre k) (him k), integral_smul_const, integral_smul_const, hre0 k hk1,
      him0 k hk1, zero_smul, zero_smul, add_zero]
  · exact (hre k).add (him k)

/-- `u (0)` is the mean of `u` on the circle `|z| = r`. -/
private theorem integral_discPoissonInt [CompleteSpace X] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) :
    ∫ θ, discPoissonInt r f θ ∂haarAddCircle = ∫ s, f s ∂haarAddCircle := by
  have hu := integrable_haar_of_continuous (continuous_discPoissonInt hr0 hr1 hf)
  have hw : Integrable (fun θ => discPoissonInt r f θ - ∫ s, f s ∂haarAddCircle) haarAddCircle :=
    hu.sub (integrable_const _)
  have hN : ∀ N, ‖∫ θ, (discPoissonInt r f θ - ∫ s, f s ∂haarAddCircle) ∂haarAddCircle‖ ≤
      approxErr r f N := fun N => by
    have h := norm_integral_le_of_norm_le_const (μ := haarAddCircle)
      (ae_of_all _ (norm_harmPoly_coeff_sub_le hr0 hr1 hf N))
    have hc : Continuous fun θ : AddCircle (2 * π) =>
        harmPoly N (cosCoeff f) (sinCoeff f) (r * fourier 1 θ) :=
      (continuous_harmPoly N _ _).comp (continuous_const.mul (map_continuous (fourier 1)))
    rw [integral_sub (integrable_haar_of_continuous hc) hw, integral_harmPoly, zero_sub,
      norm_neg] at h
    simpa using h
  have h0 := norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_approxErr hr0 hr1 f) hN)
  rw [integral_sub hu (integrable_const _), integral_const, probReal_univ, one_smul] at h0
  exact sub_eq_zero.1 h0

/-- `|u (0)| ≤ ‖u (r e^{iθ})‖_p`. -/
private theorem enorm_integral_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle) :
    ‖∫ s, f s ∂haarAddCircle‖ₑ ≤
      eLpNorm (discPoissonInt r f) (ENNReal.ofReal p) haarAddCircle := by
  rw [← integral_discPoissonInt hr0 hr1 hf]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm
    (integrable_haar_of_continuous (continuous_discPoissonInt hr0 hr1 hf)).aestronglyMeasurable]
  exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.one_le_ofReal.2 hp.le)

/-- Lemma 2 and the uniform convergence: `‖v (r e^{iθ})‖_p ≤ β² ‖u (r e^{iθ}) − u (0)‖_p`. -/
private theorem eLpNorm_discConjPoissonInt_le_sub [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) (hβt : β ≠ ⊤) {f : AddCircle (2 * π) → X}
    (hf : Integrable f haarAddCircle) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    eLpNorm (discConjPoissonInt r f) (ENNReal.ofReal p) haarAddCircle ≤
      β ^ 2 * eLpNorm (fun θ => discPoissonInt r f θ - ∫ s, f s ∂haarAddCircle)
        (ENNReal.ofReal p) haarAddCircle := by
  have hq : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  set q := ENNReal.ofReal p
  set w : AddCircle (2 * π) → X := fun θ => discPoissonInt r f θ - ∫ s, f s ∂haarAddCircle
  set v := discConjPoissonInt r f
  have hw := integrable_haar_of_continuous ((continuous_discPoissonInt hr0 hr1 hf).sub
    (continuous_const (y := ∫ s, f s ∂haarAddCircle)))
  have hv := integrable_haar_of_continuous (continuous_discConjPoissonInt hr0 hr1 hf)
  let uN : ℕ → AddCircle (2 * π) → X := fun N θ =>
    harmPoly N (cosCoeff f) (sinCoeff f) (r * fourier 1 θ)
  let vN : ℕ → AddCircle (2 * π) → X := fun N θ =>
    conjHarmPoly N (cosCoeff f) (sinCoeff f) (r * fourier 1 θ)
  have hc : Continuous fun θ : AddCircle (2 * π) => (r : ℂ) * fourier 1 θ :=
    continuous_const.mul (map_continuous (fourier 1))
  have huN := fun N => integrable_haar_of_continuous
    ((continuous_harmPoly N (cosCoeff f) (sinCoeff f)).comp hc)
  have hvN := fun N => integrable_haar_of_continuous
    ((continuous_conjHarmPoly N (cosCoeff f) (sinCoeff f)).comp hc)
  let E : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (approxErr r f N)
  have hbd : ∀ (g : AddCircle (2 * π) → X) (C : ℝ), AEStronglyMeasurable g haarAddCircle →
      (∀ θ, ‖g θ‖ ≤ C) → eLpNorm g q haarAddCircle ≤ ENNReal.ofReal C := fun g C hg hC => by
    simpa using eLpNorm_le_of_ae_bound (p := q) hg (ae_of_all _ hC)
  have h1 : ∀ N, eLpNorm (uN N) q haarAddCircle ≤ eLpNorm w q haarAddCircle + E N := fun N => by
    have h := eLpNorm_add_le (f := w) (g := uN N - w) (μ := haarAddCircle) hq
    rw [add_sub_cancel] at h
    exact h.trans (add_le_add_right (hbd _ _ ((huN N).sub hw).aestronglyMeasurable
      (norm_harmPoly_coeff_sub_le hr0 hr1 hf N)) _)
  have h2 : ∀ N, eLpNorm v q haarAddCircle ≤ eLpNorm (vN N) q haarAddCircle + E N := fun N => by
    have h := eLpNorm_add_le (f := vN N) (g := v - vN N) (μ := haarAddCircle) hq
    rw [add_sub_cancel] at h
    refine h.trans (add_le_add_right (hbd _ _ (hv.sub (hvN N)).aestronglyMeasurable fun θ => ?_) _)
    rw [Pi.sub_apply, norm_sub_rev]
    exact norm_conjHarmPoly_coeff_sub_le hr0 hr1 hf N θ
  have h3 : ∀ N, eLpNorm v q haarAddCircle ≤ β ^ 2 * (eLpNorm w q haarAddCircle + E N) + E N :=
    fun N => (h2 N).trans (add_le_add_left ((eLpNorm_conjHarmPoly_le hp hβ N _ _ r).trans
      (mul_le_mul_right (h1 N) _)) _)
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_approxErr hr0 hr1 f)
  have hlim := (ENNReal.Tendsto.const_mul (a := β ^ 2)
    ((tendsto_const_nhds (x := eLpNorm w q haarAddCircle)).add hE)
    (Or.inr (ENNReal.pow_ne_top hβt))).add hE
  rw [add_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim h3

/-- (32) for a finite constant: `‖u (r e^{iθ}) − u (0)‖_p ≤ 2 ‖u (r e^{iθ})‖_p`. -/
private theorem eLpNorm_discConjPoissonInt_le_of_ne_top [CompleteSpace X] {p : ℝ} (hp : 1 < p)
    {β : ℝ≥0∞} (hβ : IsUMDBound X p β) (hβt : β ≠ ⊤) {f : AddCircle (2 * π) → X}
    (hf : Integrable f haarAddCircle) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    eLpNorm (discConjPoissonInt r f) (ENNReal.ofReal p) haarAddCircle ≤
      2 * β ^ 2 * eLpNorm (discPoissonInt r f) (ENNReal.ofReal p) haarAddCircle := by
  have hq : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  refine (eLpNorm_discConjPoissonInt_le_sub hp hβ hβt hf hr0 hr1).trans ?_
  have h := eLpNorm_sub_le (f := discPoissonInt r f) (g := fun _ => ∫ s, f s ∂haarAddCircle)
    (μ := haarAddCircle) hq
  rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero _), measure_univ,
    ENNReal.one_rpow, mul_one] at h
  calc β ^ 2 * eLpNorm (fun θ => discPoissonInt r f θ - ∫ s, f s ∂haarAddCircle)
        (ENNReal.ofReal p) haarAddCircle
      ≤ β ^ 2 * (eLpNorm (discPoissonInt r f) (ENNReal.ofReal p) haarAddCircle +
          eLpNorm (discPoissonInt r f) (ENNReal.ofReal p) haarAddCircle) :=
        mul_le_mul_right (h.trans (add_le_add_right (enorm_integral_le hp hr0 hr1 hf) _)) _
    _ = _ := by ring

/-- A continuous linear form and the integral against a continuous kernel. -/
private theorem integral_smul_comp [CompleteSpace X] {K : AddCircle (2 * π) → ℝ}
    (hK : Continuous K) {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle)
    (ℓ : StrongDual ℝ X) :
    ∫ s, K s • ℓ (f s) ∂haarAddCircle = ℓ (∫ s, K s • f s ∂haarAddCircle) := by
  rw [← ℓ.integral_comp_comm (integrable_continuous_smul hK hf)]
  simp only [map_smul]

/-- The case of (32) that is void in the source: for `β = ∞`, the inequality says that `v = 0` on
the circle `|z| = r` if `u = 0` there. For a continuous linear form `ℓ`, `ℓ (u)` and `ℓ (v)` are the
functions (30), (31) of the real-valued `ℓ (f)`, and (32) holds for them with a finite constant. -/
private theorem discConjPoissonInt_eq_zero [CompleteSpace X] {f : AddCircle (2 * π) → X}
    (hf : Integrable f haarAddCircle) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : discPoissonInt r f =ᵐ[haarAddCircle] 0) (θ : AddCircle (2 * π)) :
    discConjPoissonInt r f θ = 0 := by
  have hu0 : discPoissonInt r f = 0 :=
    ((continuous_discPoissonInt hr0 hr1 hf).ae_eq_iff_eq haarAddCircle continuous_zero).1 hu
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ => ?_
  have hℓf : Integrable (fun s => ℓ (f s)) haarAddCircle := ℓ.integrable_comp hf
  have hsub : ∀ θ : AddCircle (2 * π), Continuous fun s => discKer r (θ - s) := fun θ =>
    (continuous_discKer hr0 hr1).comp (continuous_const.sub continuous_id)
  -- `ℓ (u)` is the function (30) of `ℓ (f)`
  have hℓu : ∀ θ, discPoissonInt r (fun s => ℓ (f s)) θ = ℓ (discPoissonInt r f θ) := fun θ => by
    rw [discPoissonInt_apply hr0 hr1, discPoissonInt_apply hr0 hr1]
    exact integral_smul_comp (continuous_const.add
      (continuous_const.mul (Complex.continuous_re.comp (hsub θ)))) hf ℓ
  -- `ℓ (v)` is the function (31) of `ℓ (f)`
  have hℓv : ∀ θ, discConjPoissonInt r (fun s => ℓ (f s)) θ = ℓ (discConjPoissonInt r f θ) :=
    fun θ => by
      rw [discConjPoissonInt_apply hr0 hr1, discConjPoissonInt_apply hr0 hr1]
      exact integral_smul_comp
        (continuous_const.mul (Complex.continuous_im.comp (hsub θ))) hf ℓ
  have hfin : umdConst ℝ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (umdConst_le_of_innerProductSpace one_lt_two)
  have h := eLpNorm_discConjPoissonInt_le_of_ne_top one_lt_two (isUMDBound_umdConst one_lt_two)
    hfin hℓf hr0 hr1
  have hz : discPoissonInt r (fun s => ℓ (f s)) = fun _ => 0 := funext fun θ => by
    rw [hℓu, hu0, Pi.zero_apply, map_zero]
  have hvc := continuous_discConjPoissonInt hr0 hr1 hℓf
  rw [hz, eLpNorm_fun_zero, mul_zero, nonpos_iff_eq_zero, eLpNorm_eq_zero_iff (by simp)] at h
  rw [← hℓv, (hvc.ae_eq_iff_eq haarAddCircle continuous_zero).1 h, Pi.zero_apply]

/-- **Lemma 3** of Burkholder (1983), (32): `‖v (r e^{iθ})‖_p ≤ 2 β² ‖u (r e^{iθ})‖_p` for
`f ∈ L^p`, `0 ≤ r < 1`. Lemma 2 gives `‖v‖_p ≤ β² ‖u − u (0)‖_p`, because `u − u (0)` and `v` are
the uniform limits on the circle `|z| = r` of functions of the form (18) and (19), and
`‖u − u (0)‖_p ≤ 2 ‖u‖_p`, because `u (0)` is the mean of `u` on this circle (the source: "hence for
`u` and `v`"). In (32) the `p`-th powers are compared, with a constant `c_p (B)`: here
`(2 β²)^p`. -/
theorem eLpNorm_discConjPoissonInt_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {f : AddCircle (2 * π) → X}
    (hf : MemLp f (ENNReal.ofReal p) haarAddCircle) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    eLpNorm (discConjPoissonInt r f) (ENNReal.ofReal p) haarAddCircle ≤
      2 * β ^ 2 * eLpNorm (discPoissonInt r f) (ENNReal.ofReal p) haarAddCircle := by
  have hfi : Integrable f haarAddCircle := hf.integrable (ENNReal.one_le_ofReal.2 hp.le)
  rcases eq_or_ne β ⊤ with rfl | hβt
  · have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp.trans' one_pos
    rcases eq_or_ne (eLpNorm (discPoissonInt r f) (ENNReal.ofReal p) haarAddCircle) 0 with h | h
    · rw [eLpNorm_eq_zero_iff hp0] at h
      rw [funext (discConjPoissonInt_eq_zero hfi hr0 hr1 h), eLpNorm_fun_zero]
      exact zero_le
    · rw [ENNReal.top_pow two_ne_zero, ENNReal.mul_top two_ne_zero, ENNReal.top_mul h]
      exact le_top
  · exact eLpNorm_discConjPoissonInt_le_of_ne_top hp hβ hβt hfi hr0 hr1

/-! ### The kernel `K_r` -/

/-- A choice of the kernel `K_r` of p. 283, `r = 1 − ε`: the modulus of the difference of the
kernels of `f̃_ε` and of `v (r e^{iθ})`. (The source says only that there is a nonnegative function
`K_r` with the properties `norm_truncatedConj_sub_le`, `integrable_truncationError` and
`integral_truncationError_lt`.) -/
noncomputable def truncationError (ε t : ℝ) : ℝ :=
  |Set.indicator {t : ℝ | ε < |t|} (fun t => Real.cot (t / 2)) t - discConjPoisson (1 - ε) t|

/-- The kernel (30) is continuous. -/
private theorem continuous_discPoisson {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (discPoisson r) :=
  continuous_const.div (by fun_prop) fun t => (denom_pos hr0 hr1 t).ne'

/-- The kernel (31) is continuous. -/
private theorem continuous_discConjPoisson {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (discConjPoisson r) :=
  Continuous.div (by fun_prop) (by fun_prop) fun t => (denom_pos hr0 hr1 t).ne'

/-- The kernel of `f̃_ε` is measurable. -/
private theorem measurable_truncCot (ε : ℝ) : Measurable (truncCot ε) := by
  have h : (fun t : ℝ => Real.cot (t / 2)) = fun t => Real.cos (t / 2) / Real.sin (t / 2) :=
    funext fun t => Real.cot_eq_cos_div_sin _
  rw [truncCot, h]
  exact Measurable.indicator (by fun_prop)
    (measurableSet_lt measurable_const continuous_abs.measurable)

/-- `f̃_ε` is strongly measurable. -/
theorem stronglyMeasurable_truncatedConj {f : AddCircle (2 * π) → X}
    (hf : AEStronglyMeasurable f haarAddCircle) (ε : ℝ) :
    StronglyMeasurable (truncatedConj ε f) := by
  rw [truncatedConj_eq]
  exact stronglyMeasurable_circConv (measurable_truncCot ε) hf

/-- The kernel of `f̃_ε` is bounded by `π / ε` on `(−π, π)`. -/
private theorem abs_truncCot_le {ε : ℝ} (hε0 : 0 < ε) {t : ℝ} (ht : |t| ≤ π) :
    |truncCot ε t| ≤ π / ε := by
  have hπ := Real.pi_pos
  by_cases h : t ∈ {t : ℝ | ε < |t|}
  · rw [truncCot, Set.indicator_of_mem h, Real.cot_eq_cos_div_sin, abs_div]
    have hs : |t| / π ≤ |Real.sin (t / 2)| := by
      have h2 := Real.mul_abs_le_abs_sin (x := t / 2)
        (by rw [abs_div, abs_two]; linarith)
      rw [abs_div, abs_two] at h2
      calc |t| / π = 2 / π * (|t| / 2) := by field_simp
        _ ≤ _ := h2
    have hε : ε / π ≤ |Real.sin (t / 2)| := (div_le_div_of_nonneg_right (le_of_lt h) hπ.le).trans hs
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hε)]
    calc |Real.cos (t / 2)| ≤ 1 := Real.abs_cos_le_one _
      _ = π / ε * (ε / π) := by field_simp
      _ ≤ π / ε * |Real.sin (t / 2)| := by gcongr
  · rw [truncCot, Set.indicator_of_notMem h, abs_zero]
    positivity

/-- A continuous kernel is bounded on `(−π, π]`. -/
private theorem exists_bound_of_continuous {k : ℝ → ℝ} (hk : Continuous k) :
    ∃ C, ∀ t ∈ Set.Ioc (-π) π, |k t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn hk.continuousOn
  exact ⟨C, fun t ht => hC t ⟨ht.1.le, ht.2⟩⟩

/-- `K_r` is the modulus of the difference of the two kernels. -/
private theorem truncationError_eq (ε : ℝ) :
    truncationError ε = fun t => |truncCot ε t - discConjPoisson (1 - ε) t| := rfl

/-- `K_r` is measurable. -/
private theorem measurable_truncationError {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Measurable (truncationError ε) := by
  rw [truncationError_eq]
  exact continuous_abs.measurable.comp ((measurable_truncCot ε).sub
    (continuous_discConjPoisson (by linarith) (by linarith)).measurable)

/-- `K_r` is bounded on `(−π, π]`. -/
private theorem exists_bound_truncationError {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C, ∀ t ∈ Set.Ioc (-π) π, |truncationError ε t| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_of_continuous
    (continuous_discConjPoisson (r := 1 - ε) (by linarith) (by linarith))
  refine ⟨π / ε + C, fun t ht => ?_⟩
  rw [truncationError_eq, abs_abs]
  exact (abs_sub _ _).trans (add_le_add (abs_truncCot_le hε0 (abs_le.2 ⟨ht.1.le, ht.2⟩)) (hC t ht))

/-- `K_r` is integrable on `(−π, π]`. -/
theorem integrable_truncationError {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    IntegrableOn (truncationError ε) (Set.Ioc (-π) π) volume := by
  obtain ⟨C, hC⟩ := exists_bound_truncationError hε0 hε1
  exact IntegrableOn.of_bound measure_Ioc_lt_top
    (measurable_truncationError hε0 hε1).aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hC))

/-- `K_r` is even. -/
private theorem truncationError_neg (ε t : ℝ) : truncationError ε (-t) = truncationError ε t := by
  have h1 : truncCot ε (-t) = -truncCot ε t := by
    by_cases h : t ∈ {t : ℝ | ε < |t|}
    · have h' : -t ∈ {t : ℝ | ε < |t|} := by simpa using h
      rw [truncCot, Set.indicator_of_mem h, Set.indicator_of_mem h', Real.cot_eq_cos_div_sin,
        Real.cot_eq_cos_div_sin, neg_div, Real.cos_neg, Real.sin_neg, div_neg]
    · have h' : -t ∉ {t : ℝ | ε < |t|} := by simpa using h
      rw [truncCot, Set.indicator_of_notMem h, Set.indicator_of_notMem h', neg_zero]
  have h2 : discConjPoisson (1 - ε) (-t) = -discConjPoisson (1 - ε) t := by
    rw [discConjPoisson, discConjPoisson, Real.sin_neg, Real.cos_neg, mul_neg, neg_div]
  simp only [truncationError_eq, h1, h2]
  rw [neg_sub_neg, abs_sub_comm]

/-- `1 − 2r cos t + r² = ε² + 4r sin² (t / 2)`, `r = 1 − ε`. -/
private theorem denom_eq (ε t : ℝ) : 1 - 2 * (1 - ε) * Real.cos t + (1 - ε) ^ 2 =
    ε ^ 2 + 4 * (1 - ε) * Real.sin (t / 2) ^ 2 := by
  have h : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (t / 2)
    rw [mul_div_cancel₀ _ two_ne_zero] at h1
    rw [h1, Real.cos_sq']
    ring
  rw [h]
  ring

/-- `K_r (t) = 2r sin t / (1 − 2r cos t + r²)` for `0 ≤ t ≤ ε`. -/
private theorem truncationError_of_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ ε) : truncationError ε t = discConjPoisson (1 - ε) t := by
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.two_le_pi])
  have hn : t ∉ {t : ℝ | ε < |t|} := by
    rw [Set.mem_ofPred_eq, abs_of_nonneg ht0, not_lt]
    exact ht
  rw [truncationError, Set.indicator_of_notMem hn, zero_sub, abs_neg, abs_of_nonneg]
  exact div_nonneg (mul_nonneg (by linarith) hs)
    (denom_pos (by linarith : (0 : ℝ) ≤ 1 - ε) (by linarith) t).le

/-- `K_r (t) = cot (t / 2) − 2r sin t / (1 − 2r cos t + r²) =
cot (t / 2) ε² / (1 − 2r cos t + r²)` for `ε < t ≤ π`. -/
private theorem truncationError_of_lt {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {t : ℝ} (ht : ε < t)
    (htπ : t ≤ π) :
    truncationError ε t = Real.cot (t / 2) - discConjPoisson (1 - ε) t := by
  have hs : 0 < Real.sin (t / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : 0 ≤ Real.cos (t / 2) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hm : t ∈ {t : ℝ | ε < |t|} := by
    rw [Set.mem_ofPred_eq, abs_of_pos (by linarith)]
    exact ht
  have hD := denom_pos (by linarith : (0 : ℝ) ≤ 1 - ε) (by linarith) t
  rw [truncationError, Set.indicator_of_mem hm, abs_of_nonneg]
  have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    rw [← Real.sin_two_mul, mul_div_cancel₀ _ two_ne_zero]
  have h : Real.cot (t / 2) - discConjPoisson (1 - ε) t =
      Real.cos (t / 2) * ε ^ 2 /
        (Real.sin (t / 2) * (1 - 2 * (1 - ε) * Real.cos t + (1 - ε) ^ 2)) := by
    rw [Real.cot_eq_cos_div_sin, discConjPoisson, div_sub_div _ _ hs.ne' hD.ne', hsin]
    congr 1
    rw [denom_eq]
    ring
  rw [h]
  positivity

/-- `log (1 − 2r cos t + r²)` is a primitive of `2r sin t / (1 − 2r cos t + r²)`. -/
private theorem hasDerivAt_log_denom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    HasDerivAt (fun t => Real.log (1 - 2 * r * Real.cos t + r ^ 2)) (discConjPoisson r t) t := by
  have h : HasDerivAt (fun t => 1 - 2 * r * Real.cos t + r ^ 2) (2 * r * Real.sin t) t := by
    have h1 := (((Real.hasDerivAt_cos t).const_mul (2 * r)).const_sub 1).add_const (r ^ 2)
    rwa [mul_neg, neg_neg] at h1
  exact h.log (denom_pos hr0 hr1 t).ne'

/-- `2 log sin (t / 2)` is a primitive of `cot (t / 2)`. -/
private theorem hasDerivAt_log_sin {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    HasDerivAt (fun t => 2 * Real.log (Real.sin (t / 2))) (Real.cot (t / 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (t / 2)) (Real.cos (t / 2) * (1 / 2)) t :=
    ((hasDerivAt_id t).div_const 2).sin
  have h2 := (h1.log ht).const_mul 2
  rw [Real.cot_eq_cos_div_sin]
  convert h2 using 1
  ring

/-- `∫_0^ε K_r = log D (ε) − 2 log ε`, `D (t) = 1 − 2r cos t + r²`. -/
private theorem integral_truncationError_zero {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∫ t in 0..ε, truncationError ε t =
      Real.log (ε ^ 2 + 4 * (1 - ε) * Real.sin (ε / 2) ^ 2) - 2 * Real.log ε := by
  have hr0 : (0 : ℝ) ≤ 1 - ε := by linarith
  have hr1 : 1 - ε < 1 := by linarith
  have h1 : ∫ t in 0..ε, truncationError ε t = ∫ t in 0..ε, discConjPoisson (1 - ε) t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hε0.le] at ht
    exact truncationError_of_le hε0 hε1 ht.1 ht.2
  rw [h1, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_log_denom hr0 hr1 t)
    ((continuous_discConjPoisson hr0 hr1).intervalIntegrable _ _), denom_eq, denom_eq, zero_div,
    Real.sin_zero, zero_pow two_ne_zero, mul_zero, add_zero, Real.log_pow, Nat.cast_two]

/-- `∫_ε^π K_r = log D (ε) − 2 log sin (ε / 2) − 2 log (1 + r)`, `D (t) = 1 − 2r cos t + r²`. -/
private theorem integral_truncationError_pi {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∫ t in ε..π, truncationError ε t =
      Real.log (ε ^ 2 + 4 * (1 - ε) * Real.sin (ε / 2) ^ 2) - 2 * Real.log (Real.sin (ε / 2)) -
        2 * Real.log (2 - ε) := by
  have hr0 : (0 : ℝ) ≤ 1 - ε := by linarith
  have hr1 : 1 - ε < 1 := by linarith
  have hεπ : ε ≤ π := by linarith [Real.two_le_pi]
  have hs : ∀ t ∈ Set.uIcc ε π, Real.sin (t / 2) ≠ 0 := fun t ht => by
    rw [Set.uIcc_of_le hεπ] at ht
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
      (by linarith [ht.2, Real.pi_pos])).ne'
  have h1 : ∫ t in ε..π, truncationError ε t =
      ∫ t in ε..π, (Real.cot (t / 2) - discConjPoisson (1 - ε) t) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [Set.uIoc_of_le hεπ] at ht
    exact truncationError_of_lt hε0 hε1 ht.1 ht.2
  have hcont : ContinuousOn (fun t => Real.cot (t / 2) - discConjPoisson (1 - ε) t)
      (Set.uIcc ε π) := by
    have h : (fun t : ℝ => Real.cot (t / 2)) = fun t => Real.cos (t / 2) / Real.sin (t / 2) :=
      funext fun t => Real.cot_eq_cos_div_sin _
    refine ContinuousOn.sub ?_ (continuous_discConjPoisson hr0 hr1).continuousOn
    rw [h]
    exact ContinuousOn.div (by fun_prop) (by fun_prop) hs
  rw [h1, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hasDerivAt_log_sin (hs t ht)).sub (hasDerivAt_log_denom hr0 hr1 t))
    hcont.intervalIntegrable]
  simp only [Pi.sub_apply, denom_eq, Real.sin_pi_div_two, Real.log_one]
  have h2 : ε ^ 2 + 4 * (1 - ε) * 1 ^ 2 = (2 - ε) ^ 2 := by ring
  rw [h2, Real.log_pow, Nat.cast_two]
  ring

/-- `log π < π / 2`. -/
private theorem log_pi_lt : Real.log π < π / 2 := by
  have h1 : Real.log π = Real.log 2 + Real.log (π / 2) := by
    rw [← Real.log_mul two_ne_zero (by positivity), mul_div_cancel₀ _ two_ne_zero]
  have h2 := Real.log_le_sub_one_of_pos (show 0 < π / 2 by positivity)
  linarith [Real.log_lt_sub_one_of_pos two_pos (by norm_num)]

/-- `D (ε) = ε² + 4r sin² (ε / 2) ≤ π ε sin (ε / 2) (1 + r)`, from
`ε / π ≤ sin (ε / 2) ≤ ε / 2`. -/
private theorem log_denom_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Real.log (ε ^ 2 + 4 * (1 - ε) * Real.sin (ε / 2) ^ 2) ≤
      Real.log π + Real.log ε + Real.log (Real.sin (ε / 2)) + Real.log (2 - ε) := by
  have hπ := Real.pi_pos
  have h2 := Real.two_le_pi
  have hs1 : 2 / π * (ε / 2) ≤ Real.sin (ε / 2) := Real.mul_le_sin (by linarith) (by linarith)
  have hs2 : Real.sin (ε / 2) ≤ ε / 2 := Real.sin_le (by linarith)
  have hs0 : 0 < Real.sin (ε / 2) := lt_of_lt_of_le (by positivity) hs1
  set s := Real.sin (ε / 2)
  have hs3 : ε ≤ π * s := by
    have h := mul_le_mul_of_nonneg_left hs1 hπ.le
    calc ε = π * (2 / π * (ε / 2)) := by field_simp
      _ ≤ _ := h
  have hr : 0 < 2 - ε := by linarith
  rw [← Real.log_mul hπ.ne' hε0.ne', ← Real.log_mul (by positivity) hs0.ne',
    ← Real.log_mul (by positivity) hr.ne']
  have hr0 : 0 ≤ 1 - ε := by linarith
  refine Real.log_le_log (add_pos_of_pos_of_nonneg (pow_pos hε0 2)
    (mul_nonneg (mul_nonneg zero_le_four hr0) (sq_nonneg s))) ?_
  have h3 : ε ^ 2 ≤ π * ε * s := by nlinarith
  have h4 : 4 * (1 - ε) * s ^ 2 ≤ (1 - ε) * (π * ε * s) := by
    have h5 : 4 * s ^ 2 ≤ π * ε * s := by
      nlinarith [mul_nonneg hs0.le (sub_nonneg.2 hs2),
        mul_nonneg (mul_pos hε0 hs0).le (sub_nonneg.2 h2)]
    linarith [mul_le_mul_of_nonneg_left h5 hr0]
  nlinarith

/-- `(2π)⁻¹ ∫_{−π}^π K_r (t) dt < 1`. The source leaves the proof to the reader. Here: with
`D (t) = 1 − 2r cos t + r² = ε² + 4r sin² (t / 2)`, the even function `K_r` is `2r sin t / D (t)` on
`(0, ε)`, with the primitive `log D (t)`, and `cot (t / 2) − 2r sin t / D (t)`, which is
`cot (t / 2) ε² / D (t)`, on `(ε, π)`, with the primitive `2 log sin (t / 2) − log D (t)`. Hence
`∫_0^π K_r = 2 log (D (ε) / (ε s (1 + r)))`, `s = sin (ε / 2)`, and this is at most `2 log π < π`,
because `ε / π ≤ s ≤ ε / 2`. -/
theorem integral_truncationError_lt {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (2 * π)⁻¹ * ∫ t in -π..π, truncationError ε t < 1 := by
  have hπ := Real.pi_pos
  have hεπ : ε ≤ π := by linarith [Real.two_le_pi]
  have hint : ∀ a b, -π ≤ a → a ≤ b → b ≤ π →
      IntervalIntegrable (truncationError ε) volume a b := fun a b ha hab hb =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      ((integrable_truncationError hε0 hε1).mono_set (Set.Ioc_subset_Ioc ha hb))
  -- `K_r` is even
  have heven : ∫ t in -π..0, truncationError ε t = ∫ t in 0..π, truncationError ε t := by
    have h := intervalIntegral.integral_comp_neg (a := -π) (b := 0) (truncationError ε)
    simp only [truncationError_neg, neg_neg, neg_zero] at h
    exact h
  have h1 : ∫ t in -π..π, truncationError ε t = 2 * ∫ t in 0..π, truncationError ε t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint (-π) 0 le_rfl (by linarith) hπ.le) (hint 0 π (by linarith) hπ.le le_rfl), heven,
      two_mul]
  have h2 : ∫ t in 0..π, truncationError ε t ≤ 2 * Real.log π := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint 0 ε (by linarith) hε0.le hεπ) (hint ε π (by linarith) hεπ le_rfl),
      integral_truncationError_zero hε0 hε1, integral_truncationError_pi hε0 hε1]
    linarith [log_denom_le hε0 hε1]
  rw [h1, inv_mul_lt_iff₀ (by positivity)]
  linarith [log_pi_lt]

/-- `|f̃_ε (θ) − v (r e^{iθ})| ≤ (2π)⁻¹ ∫_{−π}^π |f (θ − t)| K_r (t) dt`, `r = 1 − ε`: the kernels
of `f̃_ε` and of `v (r e^{iθ})` are bounded. -/
theorem norm_truncatedConj_sub_le {f : AddCircle (2 * π) → X} (hf : Integrable f haarAddCircle)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (θ : AddCircle (2 * π)) :
    ‖truncatedConj ε f θ - discConjPoissonInt (1 - ε) f θ‖ ≤
      (2 * π)⁻¹ * ∫ t in -π..π, ‖f (θ - t)‖ * truncationError ε t := by
  have hπ := Real.pi_pos
  have hc := continuous_discConjPoisson (r := 1 - ε) (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hc
  have h1 := integrable_smul_sub_coe hf θ (measurable_truncCot ε) fun t ht =>
    abs_truncCot_le hε0 (abs_le.2 ⟨ht.1.le, ht.2⟩)
  have h2 := integrable_smul_sub_coe hf θ hc.measurable hC
  rw [truncatedConj_eq, discConjPoissonInt_eq, circConv, circConv, ← smul_sub,
    ← integral_sub h1 h2, norm_smul, Real.norm_of_nonneg (by positivity),
    intervalIntegral.integral_of_le (by linarith)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans_eq ?_)
    (by positivity)
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [← sub_smul, norm_smul, truncationError_eq, Real.norm_eq_abs, mul_comm]

/-! ### The inequality (33) -/

/-- `∫ |(2π)⁻¹ k| = (2π)⁻¹ ∫_{−π}^π k` for a nonnegative integrable kernel. -/
private theorem lintegral_enorm_kernel {k : ℝ → ℝ} (hk0 : ∀ t, 0 ≤ k t)
    (hk : IntegrableOn k (Set.Ioc (-π) π) volume) :
    ∫⁻ t in Set.Ioc (-π) π, ‖(2 * π)⁻¹ * k t‖ₑ =
      ENNReal.ofReal ((2 * π)⁻¹ * ∫ t in -π..π, k t) := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal (hk.const_mul _)
      (ae_of_all _ fun t => mul_nonneg (by positivity) (hk0 t))]
  refine lintegral_congr fun t => ?_
  rw [Real.enorm_of_nonneg (mul_nonneg (by positivity) (hk0 t))]

/-- The Poisson kernel has mean `1`. -/
private theorem integral_discPoisson {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (2 * π)⁻¹ * ∫ t in -π..π, discPoisson r t = 1 := by
  have h := integral_discPoissonInt hr0 hr1 (integrable_const (1 : ℝ))
  simpa [discPoissonInt] using h

/-- `‖u (r e^{iθ})‖_p ≤ ‖f‖_p`, by Young's inequality. -/
private theorem eLpNorm_discPoissonInt_le {p : ℝ} (hp : 1 ≤ p) {f : AddCircle (2 * π) → X}
    (hf : AEStronglyMeasurable f haarAddCircle) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    eLpNorm (discPoissonInt r f) (ENNReal.ofReal p) haarAddCircle ≤
      eLpNorm f (ENNReal.ofReal p) haarAddCircle := by
  have hc := continuous_discPoisson hr0 hr1
  have hk0 : ∀ t, 0 ≤ discPoisson r t := fun t =>
    div_nonneg (by nlinarith) (denom_pos hr0 hr1 t).le
  have h := eLpNorm_circConv_le hp hc.measurable hf
  rwa [lintegral_enorm_kernel hk0 (hc.integrableOn_Ioc), integral_discPoisson hr0 hr1,
    ENNReal.ofReal_one, one_mul, ← discPoissonInt_eq] at h

/-- `‖f̃_ε − v (r e^{iθ})‖_p ≤ ‖f‖_p`, `r = 1 − ε`, by Young's inequality. -/
private theorem eLpNorm_truncatedConj_sub_le {p : ℝ} (hp : 1 ≤ p) {f : AddCircle (2 * π) → X}
    (hf : Integrable f haarAddCircle) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    eLpNorm (truncatedConj ε f - discConjPoissonInt (1 - ε) f) (ENNReal.ofReal p)
        haarAddCircle ≤ eLpNorm f (ENNReal.ofReal p) haarAddCircle := by
  have hm : AEStronglyMeasurable (truncatedConj ε f - discConjPoissonInt (1 - ε) f)
      haarAddCircle := by
    rw [truncatedConj_eq, discConjPoissonInt_eq]
    exact ((stronglyMeasurable_circConv (measurable_truncCot ε) hf.aestronglyMeasurable).sub
      (stronglyMeasurable_circConv (continuous_discConjPoisson (by linarith)
        (by linarith)).measurable hf.aestronglyMeasurable)).aestronglyMeasurable
  have hle : ∀ θ, ‖(truncatedConj ε f - discConjPoissonInt (1 - ε) f) θ‖ ≤
      circConv (truncationError ε) (fun s => ‖f s‖) θ := fun θ => by
    refine (norm_truncatedConj_sub_le hf hε0 hε1 θ).trans_eq ?_
    rw [circConv, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    simp only [smul_eq_mul, mul_comm]
  have h := eLpNorm_circConv_le hp (measurable_truncationError hε0 hε1)
    hf.aestronglyMeasurable.norm
  have hk0 : ∀ t, 0 ≤ truncationError ε t := fun t => abs_nonneg _
  rw [lintegral_enorm_kernel hk0 (integrable_truncationError hε0 hε1),
    eLpNorm_norm _ hf.aestronglyMeasurable] at h
  refine (eLpNorm_mono_real hm hle).trans (h.trans (mul_le_of_le_one_left' ?_))
  exact ENNReal.ofReal_le_one.2 (integral_truncationError_lt hε0 hε1).le

/-- The bound `2 β² + 1` for the Hilbert transform in terms of a `UMD_p` constant `β`, the constant
of (33) and (34). -/
noncomputable def hilbertBound (β : ℝ≥0∞) : ℝ≥0∞ := 2 * β ^ 2 + 1

/-- Burkholder (1983), (33): `‖f̃_ε‖_p ≤ (2 β² + 1) ‖f‖_p` for `f ∈ L^p`, `0 < ε < 1`. With
`r = 1 − ε`, Young's inequality gives `‖f̃_ε − v (r e^{iθ})‖_p ≤ ‖f‖_p` and
`‖u (r e^{iθ})‖_p ≤ ‖f‖_p`, and (32) gives `‖v (r e^{iθ})‖_p ≤ 2 β² ‖u (r e^{iθ})‖_p`. -/
theorem eLpNorm_truncatedConj_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {f : AddCircle (2 * π) → X}
    (hf : MemLp f (ENNReal.ofReal p) haarAddCircle) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    eLpNorm (truncatedConj ε f) (ENNReal.ofReal p) haarAddCircle ≤
      hilbertBound β * eLpNorm f (ENNReal.ofReal p) haarAddCircle := by
  have hq : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hr0 : 0 ≤ 1 - ε := by linarith
  have hr1 : 1 - ε < 1 := by linarith
  have hadd := eLpNorm_add_le (f := truncatedConj ε f - discConjPoissonInt (1 - ε) f)
    (g := discConjPoissonInt (1 - ε) f) (μ := haarAddCircle) hq
  rw [sub_add_cancel] at hadd
  calc eLpNorm (truncatedConj ε f) (ENNReal.ofReal p) haarAddCircle
      ≤ eLpNorm f (ENNReal.ofReal p) haarAddCircle +
          2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) haarAddCircle :=
        hadd.trans (add_le_add
          (eLpNorm_truncatedConj_sub_le hp.le (hf.integrable hq) hε0 hε1)
          ((eLpNorm_discConjPoissonInt_le hp hβ hf hr0 hr1).trans
            (mul_le_mul_right (eLpNorm_discPoissonInt_le hp.le hf.aestronglyMeasurable hr0 hr1) _)))
    _ = hilbertBound β * eLpNorm f (ENNReal.ofReal p) haarAddCircle := by
        rw [hilbertBound]
        ring

end HarmonicAnalysis
