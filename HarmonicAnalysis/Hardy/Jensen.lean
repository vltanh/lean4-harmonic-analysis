/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Hardy.GeometricMean

/-!
# Jensen's inequality for analytic functions on the circle

An integrable function `f` on the circle whose Fourier coefficients of negative order vanish and
whose mean value `f̂ (0)` is not zero satisfies `∫ log |f| ≥ log |f̂ (0)|`; in particular, `log |f|`
is integrable (H. Helson and D. Lowdenslager, *Prediction theory and Fourier series in several
variables*, Acta Math. 99 (1958), 165–202, Theorem 2 and its Corollary, for the circle; the
exponents `−(m, n)`, `(m, n) ∈ S`, of the source are the positive integers here).

The proof is that of the source (pp. 174–176). If `f` is square-summable
(`log_norm_fourierCoeff_zero_le_of_memLp_two`), the inequality follows from one half of Szegő's
theorem, `inf ∫ |1 + Q|² w ≤ exp (∫ log w)`, (23), for `w = |f|²`, since `(1 + Q) f` has the
constant coefficient `f̂ (0)`; and (23) follows from Lemma 2, which is
`exists_integral_exp_circPoly_le` for `1 × 1` matrices: a real trigonometric polynomial with
vanishing integral is `2 Re P` with `P = Σ_{k > 0} c_k e_k`, and `e^P = 1 + Q`,
`|e^P|² = e^{2 Re P}`. In general (`log_norm_fourierCoeff_zero_le_integral_log_norm`), `f` is the
limit in `L¹` of its Fejér means.

For a bounded analytic function `Q` with values in the square matrices, `det Q` is bounded and
analytic with constant coefficient `det Q̂ (0)`, hence `∫ log |det Q| ≥ log |det Q̂ (0)|` (cf. (70),
loc. cit.).
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexOrder Topology

namespace HarmonicAnalysis

/-! ### Bounded analytic functions -/

/-- The bounded analytic scalar functions. -/
private def IsBoundedAnalytic (u : UnitAddCircle → ℂ) : Prop :=
  Integrable u haarAddCircle ∧ (∀ k : ℤ, k < 0 → fourierCoeff u k = 0) ∧
    ∃ C : ℝ, ∀ᵐ t ∂haarAddCircle, ‖u t‖ ≤ C

/-- An analytic scalar function as a function of `H¹` with values in the `1 × 1` matrices. -/
private theorem IsBoundedAnalytic.isHardyOne {u : UnitAddCircle → ℂ} (hu : IsBoundedAnalytic u) :
    IsHardyOne fun t => Matrix.of fun _ _ : Unit => u t :=
  ⟨fun _ _ => hu.1, fun k hk => Matrix.ext fun _ _ => hu.2.1 k hk⟩

/-- The product of bounded analytic scalar functions is bounded and analytic, and its constant
coefficient is the product of those of the factors. -/
private theorem IsBoundedAnalytic.mul {u v : UnitAddCircle → ℂ} (hu : IsBoundedAnalytic u)
    (hv : IsBoundedAnalytic v) : IsBoundedAnalytic (fun t => u t * v t) ∧
      fourierCoeff (fun t => u t * v t) 0 = fourierCoeff u 0 * fourierCoeff v 0 := by
  obtain ⟨C, hC⟩ := hu.2.2
  obtain ⟨C', hC'⟩ := hv.2.2
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu.isHardyOne.bounded_mul (hC.mono fun t ht _ _ => ht) hv.isHardyOne
  have e (t : UnitAddCircle) : ((Matrix.of fun _ _ : Unit => u t) *
      Matrix.of fun _ _ : Unit => v t) () () = u t * v t := by
    simp [Matrix.mul_apply]
  have e2 (k : ℤ) : matFourierCoeff (fun t => (Matrix.of fun _ _ : Unit => u t) *
      Matrix.of fun _ _ : Unit => v t) k () () = fourierCoeff (fun t => u t * v t) k := by
    simp only [matFourierCoeff, Matrix.of_apply, e]
  refine ⟨⟨by simpa only [e] using h1 () (), fun k hk => ?_, C * C', ?_⟩, ?_⟩
  · rw [← e2, h2 k hk, Matrix.zero_apply]
  · filter_upwards [hC, hC'] with t ht ht'
    rw [norm_mul]
    exact mul_le_mul ht ht' (norm_nonneg _) ((norm_nonneg _).trans ht)
  · rw [← e2, h3, Matrix.mul_apply, Fintype.sum_unique]
    rfl

/-- Finite products of bounded analytic scalar functions. -/
private theorem IsBoundedAnalytic.prod {ι : Type*} (s : Finset ι) {u : ι → UnitAddCircle → ℂ}
    (hu : ∀ i, IsBoundedAnalytic (u i)) : IsBoundedAnalytic (fun t => ∏ i ∈ s, u i t) ∧
      fourierCoeff (fun t => ∏ i ∈ s, u i t) 0 = ∏ i ∈ s, fourierCoeff (u i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, fourierCoeff_const, ite_true, and_true]
    refine ⟨integrable_const _, fun k hk => ?_, 1, ae_of_all _ fun t => norm_one.le⟩
    rw [fourierCoeff_const, ite_eq_right hk.ne]
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    obtain ⟨h1, h2⟩ := (hu a).mul ih.1
    exact ⟨h1, by rw [h2, ih.2]⟩

open scoped Nat in
/-- The Fourier coefficients of `e^u` for a bounded function `u`: the exponential series converges
uniformly. -/
private theorem hasSum_fourierCoeff_exp {u : UnitAddCircle → ℂ} {C : ℝ}
    (hu : AEStronglyMeasurable u haarAddCircle) (hC : ∀ᵐ t ∂haarAddCircle, ‖u t‖ ≤ C) (k : ℤ) :
    HasSum (fun j : ℕ => (j ! : ℂ)⁻¹ * fourierCoeff (fun t => u t ^ j) k)
      (fourierCoeff (fun t => Complex.exp (u t)) k) := by
  have h := hasSum_integral_of_dominated_convergence (μ := haarAddCircle)
    (F := fun (j : ℕ) t => fourier (-k) t • ((j ! : ℂ)⁻¹ * u t ^ j))
    (f := fun t => fourier (-k) t • Complex.exp (u t)) (fun j _ => C ^ j / j !)
    (fun j => (fourier (-k)).continuous.aestronglyMeasurable.smul ((hu.pow j).const_mul _))
    (fun j => ?_) (ae_of_all _ fun _ => Real.summable_pow_div_factorial C) (integrable_const _)
    (ae_of_all _ fun t => ?_)
  · simp only [← fourierCoeff.const_mul]
    exact h
  · filter_upwards [hC] with t ht
    rw [norm_smul, norm_fourier_apply_eq_one, one_mul, norm_mul, norm_inv, norm_pow,
      Complex.norm_natCast, ← div_eq_inv_mul]
    gcongr
  · have h := NormedSpace.expSeries_div_hasSum_exp (u t)
    simp only [div_eq_inv_mul, ← Complex.exp_eq_exp_ℂ] at h
    exact h.const_smul _

/-- "On account of the third property of half-planes, it is clear that `e^P = 1 + Q`"
(Helson–Lowdenslager (1958), p. 174): if `u` is a bounded analytic function, then so is `e^u`, and
its constant coefficient is `e^{û (0)}`; it is `1` if `û (0) = 0`. -/
private theorem IsBoundedAnalytic.exp {u : UnitAddCircle → ℂ} (hu : IsBoundedAnalytic u) :
    IsBoundedAnalytic (fun t => Complex.exp (u t)) ∧
      fourierCoeff (fun t => Complex.exp (u t)) 0 = Complex.exp (fourierCoeff u 0) := by
  have hpow (j : ℕ) : IsBoundedAnalytic (fun t => u t ^ j) ∧
      fourierCoeff (fun t => u t ^ j) 0 = fourierCoeff u 0 ^ j := by
    simpa only [Finset.prod_const, Finset.card_range] using
      IsBoundedAnalytic.prod (Finset.range j) (u := fun _ => u) fun _ => hu
  obtain ⟨hint, -, C, hC⟩ := hu
  have hsum := hasSum_fourierCoeff_exp hint.aestronglyMeasurable hC
  have hexp : ∀ᵐ t ∂haarAddCircle, ‖Complex.exp (u t)‖ ≤ Real.exp C := by
    filter_upwards [hC] with t ht
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ht)
  refine ⟨⟨(integrable_const (Real.exp C)).mono' (Complex.continuous_exp.comp_aestronglyMeasurable
    hint.aestronglyMeasurable) hexp, fun k hk => ?_, _, hexp⟩, ?_⟩
  · have h := hsum k
    simp only [(hpow _).1.2.1 k hk, mul_zero] at h
    exact h.unique hasSum_zero
  · have h := NormedSpace.expSeries_div_hasSum_exp (fourierCoeff u 0)
    simp only [div_eq_inv_mul, ← Complex.exp_eq_exp_ℂ, ← (hpow _).2] at h
    exact (hsum 0).unique h

/-! ### The limit `ε → 0` -/

/-- `x ↦ log (x + ε)` is Lipschitz on `[0, ∞)` with constant `1 / ε`. -/
private theorem abs_log_add_sub_log_add_le {ε x y : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.log (x + ε) - Real.log (y + ε)| ≤ ε⁻¹ * |x - y| := by
  have key {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
      Real.log (a + ε) - Real.log (b + ε) ≤ ε⁻¹ * |a - b| := by
    have hb' : 0 < b + ε := by positivity
    rw [← Real.log_div (by positivity) hb'.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    have e : (a + ε) / (b + ε) - 1 = (b + ε)⁻¹ * (a - b) := by
      field_simp
      ring
    rw [e]
    refine (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)).trans ?_
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hε (by linarith)) (abs_nonneg _)
  rw [abs_le]
  constructor
  · have := key hy hx
    rw [abs_sub_comm] at this
    linarith
  · exact key hx hy

/-- `log (g + ε)` is integrable if `g ≥ 0` is integrable. -/
private theorem integrable_log_add {g : UnitAddCircle → ℝ} (hg : Integrable g haarAddCircle)
    (h0 : ∀ t, 0 ≤ g t) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t => Real.log (g t + ε)) haarAddCircle := by
  have h1 : Integrable (fun t => Real.log (g t + ε) - Real.log ε) haarAddCircle := by
    refine (hg.const_mul ε⁻¹).mono' ?_ (ae_of_all _ fun t => ?_)
    · exact ((Real.measurable_log.comp_aemeasurable
        (hg.aemeasurable.add_const ε)).sub_const _).aestronglyMeasurable
    · simpa [abs_of_nonneg (h0 t)] using abs_log_add_sub_log_add_le hε (h0 t) le_rfl
  exact (h1.add (integrable_const (Real.log ε))).congr (ae_of_all _ fun t => sub_add_cancel _ _)

/-- The pointwise part of the monotone limit theorem below: if `u_k → w` and `G − log u_k ≤ s`,
then `w > 0` and `G − log w ≤ s`. -/
private theorem pos_and_sub_log_le {u : ℕ → ℝ} {w G s : ℝ} (hu0 : ∀ k, 0 < u k)
    (hlim : Tendsto u atTop (𝓝 w)) (hs : ∀ k, G - Real.log (u k) ≤ s) :
    0 < w ∧ G - Real.log w ≤ s := by
  have h1 : Real.exp (G - s) ≤ w := ge_of_tendsto' hlim fun k => by
    rw [← Real.le_log_iff_exp_le (hu0 k)]
    linarith [hs k]
  have h2 : 0 < w := (Real.exp_pos _).trans_le h1
  rw [← Real.le_log_iff_exp_le h2] at h1
  exact ⟨h2, by linarith⟩

/-- "As `ε` tends to zero we obtain by the monotone limit theorem" (Helson–Lowdenslager (1958), p.
172): if the positive functions `u_k` decrease to `w`, the functions `log u_k` are integrable, and
their integrals are at least `L`, then `w > 0` almost everywhere, `log w` is integrable, and
`∫ log w ≥ L`. -/
theorem pos_and_integrable_log {w : UnitAddCircle → ℝ} {u : ℕ → UnitAddCircle → ℝ} {L : ℝ}
    (hu0 : ∀ᵐ t ∂haarAddCircle, ∀ k, 0 < u k t)
    (hanti : ∀ᵐ t ∂haarAddCircle, Antitone fun k => u k t)
    (hlim : ∀ᵐ t ∂haarAddCircle, Tendsto (fun k => u k t) atTop (𝓝 (w t)))
    (hu : ∀ k, Integrable (fun t => Real.log (u k t)) haarAddCircle)
    (hL : ∀ k, L ≤ ∫ t, Real.log (u k t) ∂haarAddCircle) :
    (∀ᵐ t ∂haarAddCircle, 0 < w t) ∧ Integrable (fun t => Real.log (w t)) haarAddCircle ∧
      L ≤ ∫ t, Real.log (w t) ∂haarAddCircle := by
  let f (k : ℕ) (t : UnitAddCircle) : ℝ≥0∞ := ENNReal.ofReal (Real.log (u 0 t) - Real.log (u k t))
  have hf (k : ℕ) : AEMeasurable (f k) haarAddCircle :=
    ((hu 0).sub (hu k)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hlog : ∀ᵐ t ∂haarAddCircle, Antitone fun k => Real.log (u k t) := by
    filter_upwards [hu0, hanti] with t h0 ht i j hij
    exact Real.log_le_log (h0 j) (ht hij)
  have hfin : ∫⁻ t, ⨆ k, f k t ∂haarAddCircle ≠ ∞ := by
    rw [lintegral_iSup' hf (hlog.mono fun t ht i j hij =>
      ENNReal.ofReal_le_ofReal (sub_le_sub_left (ht hij) _))]
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun k => ?_)
      (b := ENNReal.ofReal (∫ t, Real.log (u 0 t) ∂haarAddCircle - L))
    refine (ofReal_integral_eq_lintegral_ofReal ((hu 0).sub (hu k))
      (hlog.mono fun t ht => sub_nonneg.2 (ht (Nat.zero_le k)))).symm.trans_le
        (ENNReal.ofReal_le_ofReal ?_)
    exact (integral_sub (hu 0) (hu k)).trans_le (sub_le_sub_left (hL k) _)
  have key : ∀ᵐ t ∂haarAddCircle,
      0 < w t ∧ Real.log (u 0 t) - Real.log (w t) ≤ (⨆ k, f k t).toReal := by
    filter_upwards [hu0, hlim, ae_lt_top' (AEMeasurable.iSup hf) hfin] with t h0 hl ht
    exact pos_and_sub_log_le h0 hl fun k =>
      (ENNReal.ofReal_le_iff_le_toReal ht.ne).1 (le_iSup (fun k => f k t) k)
  have hlim' : ∀ᵐ t ∂haarAddCircle, Tendsto (fun k => Real.log (u k t)) atTop
      (𝓝 (Real.log (w t))) := by
    filter_upwards [hlim, key] with t hl hk
    exact (Real.continuousAt_log hk.1.ne').tendsto.comp hl
  -- `0 ≤ log u_0 − log w ≤ sup (log u_0 − log u_k)`
  have hD : Integrable (fun t => Real.log (u 0 t) - Real.log (w t)) haarAddCircle := by
    refine (integrable_toReal_of_lintegral_ne_top (AEMeasurable.iSup hf) hfin).mono'
      ((hu 0).aestronglyMeasurable.sub (aestronglyMeasurable_of_tendsto_ae atTop
        (fun k => (hu k).aestronglyMeasurable) hlim')) ?_
    filter_upwards [hlog, hlim', key] with t ht hl hk
    rw [Real.norm_of_nonneg (sub_nonneg.2 (le_of_tendsto' hl fun k => ht (Nat.zero_le k)))]
    exact hk.2
  have hw : Integrable (fun t => Real.log (w t)) haarAddCircle :=
    ((hu 0).sub hD).congr (ae_of_all _ fun t => sub_sub_cancel _ _)
  exact ⟨key.mono fun t ht => ht.1, hw,
    ge_of_tendsto' (integral_tendsto_of_tendsto_of_antitone hu hw hlog hlim') hL⟩

/-- The limit `ε → 0` for an integrable function `g ≥ 0`: if `∫ log (g + ε) ≥ L` for all `ε > 0`,
then `g > 0` almost everywhere, `log g` is integrable, and `∫ log g ≥ L`. -/
private theorem pos_and_integrable_log_of_add {g : UnitAddCircle → ℝ} {L : ℝ}
    (hg : Integrable g haarAddCircle) (h0 : ∀ t, 0 ≤ g t)
    (hL : ∀ ε, 0 < ε → L ≤ ∫ t, Real.log (g t + ε) ∂haarAddCircle) :
    (∀ᵐ t ∂haarAddCircle, 0 < g t) ∧ Integrable (fun t => Real.log (g t)) haarAddCircle ∧
      L ≤ ∫ t, Real.log (g t) ∂haarAddCircle := by
  have hε (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
  refine pos_and_integrable_log (u := fun k t => g t + 1 / ((k : ℝ) + 1))
    (ae_of_all _ fun t k => add_pos_of_nonneg_of_pos (h0 t) (hε k))
    (ae_of_all _ fun t i j hij => add_le_add_right (Nat.one_div_le_one_div hij) _)
    (ae_of_all _ fun t => ?_) (fun k => integrable_log_add hg h0 (hε k)) fun k => hL _ (hε k)
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (g t)

/-! ### Square-summable functions -/

/-- Helson–Lowdenslager (1958), Lemma 2 (the inequality `inf ∫ e^ψ w ≤ exp (∫ log w)`), if `log w`
is summable: `exists_integral_exp_circPoly_le` for `1 × 1` matrices. -/
private theorem exists_integral_exp_mul_le {w : UnitAddCircle → ℝ} (hw : Integrable w haarAddCircle)
    (hpos : ∀ t, 0 < w t) (hlog : Integrable (fun t => Real.log (w t)) haarAddCircle) {δ : ℝ}
    (hδ : 0 < δ) : ∃ c : ℤ →₀ Matrix Unit Unit ℂ, (∀ t, (circPoly c t).IsHermitian) ∧
      (c 0).trace = 0 ∧ ∫ t, Real.exp (circPoly c t).trace.re * w t ∂haarAddCircle ≤
        Real.exp (∫ t, Real.log (w t) ∂haarAddCircle) + δ := by
  have hdet (t : UnitAddCircle) : (Matrix.diagonal fun _ : Unit => (w t : ℂ)).det.re = w t := by
    rw [Matrix.det_diagonal, Finset.univ_unique, Finset.prod_singleton, Complex.ofReal_re]
  obtain ⟨c, hc, h0, hle⟩ := exists_integral_exp_circPoly_le
    (W := fun t => Matrix.diagonal fun _ : Unit => (w t : ℂ))
    (fun _ _ => hw.ofReal) (ae_of_all _ fun t =>
      Matrix.PosDef.diagonal fun _ => Complex.zero_lt_real.2 (hpos t))
    (by simpa only [hdet] using hlog) hδ
  refine ⟨c, hc, h0, ?_⟩
  simp only [hdet, Fintype.card_unique, Nat.cast_one, div_one] at hle
  refine (integral_congr_ae (ae_of_all _ fun t => ?_)).trans_le hle
  have h1 : NormedSpace.exp (circPoly c t) default default =
      ((Real.exp (circPoly c t).trace.re : ℝ) : ℂ) :=
    (Matrix.det_unique _).symm.trans (det_matrix_exp (hc t))
  have h2 : (NormedSpace.exp (circPoly c t) * Matrix.diagonal fun _ : Unit => (w t : ℂ)).trace =
      ((Real.exp (circPoly c t).trace.re : ℝ) : ℂ) * (w t : ℂ) := by
    rw [Matrix.trace, Finset.univ_unique, Finset.sum_singleton, Matrix.diag_apply,
      Matrix.mul_diagonal, h1]
  simp only [h2, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `P̄ = Σ_k c̄_k e_{−k}` if `P = Σ_k c_k e_k`. -/
private theorem circPoly_neg (p : ℤ →₀ Matrix Unit Unit ℂ) (t : UnitAddCircle) :
    circPoly (Finsupp.equivMapDomain (Equiv.neg ℤ)
      (p.mapRange Matrix.conjTranspose Matrix.conjTranspose_zero)) t = (circPoly p t)ᴴ := by
  rw [circPoly, Finsupp.sum_equivMapDomain, Finsupp.sum_mapRange_index fun _ => smul_zero _,
    circPoly, Finsupp.sum, Finsupp.sum, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_smul, Equiv.neg_apply, fourier_neg]
  rfl

/-- "The most general trigonometric polynomial `ψ` satisfying (14) can be written, on account of the
second property of half-planes, in the form (21)": `ψ = P + P̄`, where `P = Σ_{k > 0} c_k e_k`
(Helson–Lowdenslager (1958), p. 174); (14) is `∫ ψ = 0`. -/
private theorem exists_eq_add_conjTranspose {c : ℤ →₀ Matrix Unit Unit ℂ}
    (hc : ∀ t, (circPoly c t).IsHermitian) (h0 : (c 0).trace = 0) :
    ∃ p : ℤ →₀ Matrix Unit Unit ℂ, (∀ k ∈ p.support, 0 < k) ∧
      ∀ t, circPoly c t = circPoly p t + (circPoly p t)ᴴ := by
  classical
  have hneg (k : ℤ) : c (-k) = (c k)ᴴ := by
    ext i j
    rw [← matFourierCoeff_circPoly c, ← matFourierCoeff_circPoly c, Matrix.conjTranspose_apply,
      matFourierCoeff, matFourierCoeff, Matrix.of_apply, Matrix.of_apply, fourierCoeff,
      fourierCoeff, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    dsimp only
    rw [smul_eq_mul, smul_eq_mul, map_mul, ← fourier_neg]
    exact congrArg _ ((hc t).apply i j).symm
  refine ⟨c.filter (0 < ·), fun k hk => (Finset.mem_filter.1 hk).2, fun t => ?_⟩
  rw [← circPoly_neg, ← circPoly_add]
  congr 1
  ext1 k
  rw [Finsupp.add_apply, Finsupp.equivMapDomain_apply, Finsupp.mapRange_apply, Finsupp.filter_apply,
    Finsupp.filter_apply, Equiv.neg_symm, Equiv.neg_apply]
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [ite_eq_right hk.not_gt, ite_eq_left (neg_pos.2 hk), zero_add, ← hneg, neg_neg]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_right (by simp), zero_add, Matrix.conjTranspose_zero]
    ext i j
    simpa [Matrix.trace] using h0
  · rw [ite_eq_left hk, ite_eq_right (by omega), Matrix.conjTranspose_zero, add_zero]

/-- Helson–Lowdenslager (1958), (22), (23), if `log w` is summable: `inf ∫ |q|² w ≤ exp (∫ log w)`,
where `q = 1 + Q` ranges over the bounded analytic functions (in the source, the continuous ones)
with constant coefficient `1`: for `q = e^P` we have `|q|² = e^ψ` with `ψ = 2 Re P`. -/
private theorem exists_integral_norm_sq_mul_le {w : UnitAddCircle → ℝ}
    (hw : Integrable w haarAddCircle) (hpos : ∀ t, 0 < w t)
    (hlog : Integrable (fun t => Real.log (w t)) haarAddCircle) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : UnitAddCircle → ℂ, IsBoundedAnalytic q ∧ fourierCoeff q 0 = 1 ∧
      ∫ t, ‖q t‖ ^ 2 * w t ∂haarAddCircle ≤ Real.exp (∫ t, Real.log (w t) ∂haarAddCircle) + δ := by
  obtain ⟨c, hc, h0, hle⟩ := exists_integral_exp_mul_le hw hpos hlog hδ
  obtain ⟨p, hp, hcp⟩ := exists_eq_add_conjTranspose hc h0
  have hp2 := isHardyTwo_circPoly fun k hk => (hp k hk).le
  obtain ⟨C, hC⟩ := exists_bound_of_continuous (continuous_circPoly_matrix p)
  have hP : IsBoundedAnalytic fun t => circPoly p t () () :=
    ⟨hp2.isHardyOne.1 () (), fun k hk => congrFun (congrFun (hp2.2 k hk) ()) (), C,
      ae_of_all _ fun t => hC t () ()⟩
  have hP0 : fourierCoeff (fun t => circPoly p t () ()) 0 = 0 := by
    have h1 := congrFun (congrFun (matFourierCoeff_circPoly p 0) ()) ()
    rwa [Finsupp.notMem_support_iff.1 fun h => lt_irrefl _ (hp 0 h)] at h1
  refine ⟨_, hP.exp.1, by rw [hP.exp.2, hP0, Complex.exp_zero], le_of_eq_of_le ?_ hle⟩
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have h2 : (circPoly c t).trace.re = 2 * (circPoly p t () ()).re := by
    simp [hcp, Matrix.trace, two_mul]
  simp only [h2, Complex.norm_exp, ← Real.exp_nat_mul, Nat.cast_ofNat]

/-- `|q|² w` is summable if `q` is bounded and `w` is summable. -/
private theorem IsBoundedAnalytic.integrable_norm_sq_mul {q : UnitAddCircle → ℂ}
    (hq : IsBoundedAnalytic q) {w : UnitAddCircle → ℝ} (hw : Integrable w haarAddCircle) :
    Integrable (fun t => ‖q t‖ ^ 2 * w t) haarAddCircle := by
  obtain ⟨C, hC⟩ := hq.2.2
  refine hw.bdd_mul (c := C ^ 2) (hq.1.aestronglyMeasurable.norm.pow 2) ?_
  filter_upwards [hC] with t ht
  rw [norm_pow, norm_norm]
  gcongr

/-- "If we set in the Fourier series (26) for `f` we obtain in the product `(1 + P) f` a constant
term `b`, since `P` has no constant term" (Helson–Lowdenslager (1958), p. 175), and therefore
`|b|² ≤ ∫ |(1 + P) f|²`, by Parseval's equality in the source, by `norm_fourierCoeff_zero_sq_le`
here. (`q` is `1 + P`, and `b = f̂ (0)`.) -/
private theorem norm_sq_fourierCoeff_zero_le {f q : UnitAddCircle → ℂ}
    (hf : MemLp f 2 haarAddCircle) (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0)
    (hq : IsBoundedAnalytic q) (hq0 : fourierCoeff q 0 = 1) :
    ‖fourierCoeff f 0‖ ^ 2 ≤ ∫ t, ‖q t‖ ^ 2 * ‖f t‖ ^ 2 ∂haarAddCircle := by
  obtain ⟨C, hC⟩ := hq.2.2
  have hqf : MemLp (fun t => q t * f t) 2 haarAddCircle := by
    refine hf.of_le_mul (c := C) (hq.1.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
    filter_upwards [hC] with t ht
    rw [norm_mul]
    gcongr
  have h1 := (hq.isHardyOne.bounded_mul (hC.mono fun t ht _ _ => ht)
    (f := fun t => Matrix.of fun _ _ : Unit => f t)
    ⟨fun _ _ => hf.integrable one_le_two, fun k hk => Matrix.ext fun _ _ => hneg k hk⟩).2
  have h2 : fourierCoeff (fun t => q t * f t) 0 = fourierCoeff f 0 := by
    have h3 := congrFun (congrFun h1 ()) ()
    simp only [Matrix.mul_apply, matFourierCoeff, Matrix.of_apply, Finset.univ_unique,
      Finset.sum_singleton, hq0, one_mul] at h3
    exact h3
  have h3 := norm_fourierCoeff_zero_sq_le hqf
  simpa only [h2, norm_mul, mul_pow] using h3

/-- `|f̂ (0)|² ≤ exp (∫ log (|f|² + ε))` for a square-summable analytic function `f`, by (23) for
the weight `|f|² + ε`, whose logarithm is summable. -/
private theorem norm_sq_fourierCoeff_zero_le_exp {f : UnitAddCircle → ℂ}
    (hf : MemLp f 2 haarAddCircle) (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0) {ε : ℝ}
    (hε : 0 < ε) : ‖fourierCoeff f 0‖ ^ 2 ≤
      Real.exp (∫ t, Real.log (‖f t‖ ^ 2 + ε) ∂haarAddCircle) := by
  have hf2 : Integrable (fun t => ‖f t‖ ^ 2) haarAddCircle := hf.integrable_norm_pow two_ne_zero
  have hw : Integrable (fun t => ‖f t‖ ^ 2 + ε) haarAddCircle := hf2.add (integrable_const ε)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨q, hq, hq0, hle⟩ := exists_integral_norm_sq_mul_le hw (fun t => by positivity)
    (integrable_log_add hf2 (fun t => sq_nonneg _) hε) hδ
  refine ((norm_sq_fourierCoeff_zero_le hf hneg hq hq0).trans ?_).trans hle
  refine integral_mono (hq.integrable_norm_sq_mul hf2) (hq.integrable_norm_sq_mul hw) fun t => ?_
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hε.le) (sq_nonneg _)

/-- Helson–Lowdenslager (1958), Theorem 2 and its Corollary, on the circle, for a square-summable
function `f`.

Departure from the source: (28) is Theorem 1 for the weight `|f|²`, whose logarithm is not known to
be summable. The limiting process with which the source treats such weights in Lemmas 1 and 2 (pp.
172–173) is carried out here for the inequality `|f̂ (0)|² ≤ exp (∫ log (|f|² + ε))`. Of Theorem 1
only (23) is used. -/
theorem log_norm_fourierCoeff_zero_le_of_memLp_two {f : UnitAddCircle → ℂ}
    (hf : MemLp f 2 haarAddCircle) (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0)
    (h0 : fourierCoeff f 0 ≠ 0) :
    (∀ᵐ t ∂haarAddCircle, f t ≠ 0) ∧ Integrable (fun t => Real.log ‖f t‖) haarAddCircle ∧
      Real.log ‖fourierCoeff f 0‖ ≤ ∫ t, Real.log ‖f t‖ ∂haarAddCircle := by
  have hb := norm_pos_iff.2 h0
  have hL (ε : ℝ) (hε : 0 < ε) : 2 * Real.log ‖fourierCoeff f 0‖ ≤
      ∫ t, Real.log (‖f t‖ ^ 2 + ε) ∂haarAddCircle := by
    have h := norm_sq_fourierCoeff_zero_le_exp hf hneg hε
    rw [← Real.log_le_iff_le_exp (pow_pos hb 2), Real.log_pow, Nat.cast_ofNat] at h
    exact h
  obtain ⟨h1, h2, h3⟩ := pos_and_integrable_log_of_add
    (hf.integrable_norm_pow two_ne_zero) (fun t => sq_nonneg _) hL
  simp only [Real.log_pow, Nat.cast_ofNat] at h2 h3
  rw [integral_const_mul] at h3
  exact ⟨h1.mono fun t ht => norm_ne_zero_iff.1 (pow_ne_zero_iff two_ne_zero |>.1 ht.ne'), by
    simpa using h2.const_mul 2⁻¹, le_of_mul_le_mul_left h3 two_pos⟩

/-! ### Integrable functions -/

/-- Passage to the limit in `L¹` with `ε` fixed: `∫ log (|f_K| + ε) → ∫ log (|f| + ε)`. -/
private theorem tendsto_integral_log_norm_add {F : ℕ → UnitAddCircle → ℂ} {f : UnitAddCircle → ℂ}
    (hF : ∀ K, Integrable (F K) haarAddCircle) (hf : Integrable f haarAddCircle)
    (h : Tendsto (fun K => ∫ t, ‖F K t - f t‖ ∂haarAddCircle) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun K => ∫ t, Real.log (‖F K t‖ + ε) ∂haarAddCircle) atTop
      (𝓝 (∫ t, Real.log (‖f t‖ + ε) ∂haarAddCircle)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using h.const_mul ε⁻¹) (fun _ => norm_nonneg _) fun K => ?_
  dsimp only
  rw [← integral_sub (integrable_log_add (hF K).norm (fun _ => norm_nonneg _) hε)
    (integrable_log_add hf.norm (fun _ => norm_nonneg _) hε), ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((hF K).sub hf).norm.const_mul _) (ae_of_all _ fun t => ?_)
  refine (abs_log_add_sub_log_add_le hε (norm_nonneg _) (norm_nonneg _)).trans ?_
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (inv_nonneg.2 hε.le)

/-- The Fejér means of an integrable analytic function `f`: analytic polynomials with the constant
coefficient `f̂ (0)`, which converge to `f` in `L¹`. -/
private theorem exists_tendsto_fejer {f : UnitAddCircle → ℂ} (hf : Integrable f haarAddCircle)
    (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0) :
    ∃ p : ℕ → UnitAddCircle → ℂ, (∀ K, Continuous (p K)) ∧
      (∀ K, ∀ k : ℤ, k < 0 → fourierCoeff (p K) k = 0) ∧
      (∀ K, fourierCoeff (p K) 0 = fourierCoeff f 0) ∧
      Tendsto (fun K => ∫ t, ‖p K t - f t‖ ∂haarAddCircle) atTop (𝓝 0) := by
  let F : UnitAddCircle → Matrix Unit Unit ℂ := fun t => Matrix.of fun _ _ => f t
  have hFneg (k : ℤ) (hk : k < 0) : matFourierCoeff F k = 0 := Matrix.ext fun _ _ => hneg k hk
  have hF (i j : Unit) : Integrable (fun t => F t i j) haarAddCircle := hf
  refine ⟨fun K t => circPoly (fejerCoeff F (K + 1)) t () (), fun K =>
    (continuous_circPoly_matrix _).matrix_elem () (), fun K k hk => ?_, fun K => ?_,
    (tendsto_integral_norm_fejerCoeff_sub hF () ()).comp (tendsto_add_atTop_nat 1)⟩
  · exact congrFun (congrFun ((isHardyTwo_circPoly
      (nonneg_of_mem_support_fejerCoeff hFneg (K + 1))).2 k hk) ()) ()
  · have h := matFourierCoeff_circPoly (fejerCoeff F (K + 1)) 0
    rw [fejerCoeff_zero F K.succ_pos] at h
    exact congrFun (congrFun h ()) ()

/-- Helson–Lowdenslager (1958), pp. 175–176: `∫ log (|f| + ε) ≥ log |f̂ (0)|`, the limit of the
inequalities `∫ log (|f_K| + ε) ≥ ∫ log |f_K| ≥ log |f̂ (0)|` for the Fejér means `f_K` of `f`. -/
private theorem log_norm_fourierCoeff_zero_le_integral_log_norm_add {f : UnitAddCircle → ℂ}
    (hf : Integrable f haarAddCircle) (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0)
    (h0 : fourierCoeff f 0 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    Real.log ‖fourierCoeff f 0‖ ≤ ∫ t, Real.log (‖f t‖ + ε) ∂haarAddCircle := by
  obtain ⟨p, hp, hpneg, hp0, hlim⟩ := exists_tendsto_fejer hf hneg
  have hint (K : ℕ) := integrable_haar_of_continuous (hp K)
  refine ge_of_tendsto' (tendsto_integral_log_norm_add hint hf hlim hε) fun K => ?_
  obtain ⟨hne, hlog, hle⟩ := log_norm_fourierCoeff_zero_le_of_memLp_two
    ((hp K).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hpneg K)
    (by rwa [hp0])
  rw [hp0] at hle
  refine hle.trans (integral_mono_ae hlog
    (integrable_log_add (hint K).norm (fun _ => norm_nonneg _) hε) ?_)
  filter_upwards [hne] with t ht
  exact Real.log_le_log (norm_pos_iff.2 ht) (le_add_of_nonneg_right hε.le)

/-- Helson–Lowdenslager (1958), Theorem 2 and its Corollary, on the circle: an integrable function
`f` whose Fourier coefficients of negative order vanish, with `f̂ (0) ≠ 0`, satisfies
`∫ log |f| ≥ log |f̂ (0)|`, and `log |f|` is integrable; `f ≠ 0` almost everywhere. -/
theorem log_norm_fourierCoeff_zero_le_integral_log_norm {f : UnitAddCircle → ℂ}
    (hf : Integrable f haarAddCircle) (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0)
    (h0 : fourierCoeff f 0 ≠ 0) :
    (∀ᵐ t ∂haarAddCircle, f t ≠ 0) ∧ Integrable (fun t => Real.log ‖f t‖) haarAddCircle ∧
      Real.log ‖fourierCoeff f 0‖ ≤ ∫ t, Real.log ‖f t‖ ∂haarAddCircle := by
  simpa only [norm_pos_iff] using pos_and_integrable_log_of_add hf.norm (fun _ => norm_nonneg _)
    fun _ => log_norm_fourierCoeff_zero_le_integral_log_norm_add hf hneg h0

/-! ### Determinants -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of a bounded analytic matrix-valued function `Q` is analytic, with constant
coefficient `det Q̂ (0)`. -/
theorem fourierCoeff_det_of_bounded {Q : UnitAddCircle → Matrix n n ℂ} {C : ℝ} (hQ : IsHardyOne Q)
    (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖Q t i j‖ ≤ C) :
    Integrable (fun t => (Q t).det) haarAddCircle ∧
      (∀ k : ℤ, k < 0 → fourierCoeff (fun t => (Q t).det) k = 0) ∧
      fourierCoeff (fun t => (Q t).det) 0 = (matFourierCoeff Q 0).det := by
  have hu (i j : n) : IsBoundedAnalytic fun t => Q t i j :=
    ⟨hQ.1 i j, fun k hk => congrFun (congrFun (hQ.2 k hk) i) j, C, hC.mono fun t ht => ht i j⟩
  have hprod (σ : Equiv.Perm n) :=
    IsBoundedAnalytic.prod Finset.univ (u := fun i t => Q t (σ i) i) fun i => hu (σ i) i
  have e : (fun t => (Q t).det) = ∑ σ : Equiv.Perm n, fun t =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, Q t (σ i) i := by
    ext t
    rw [Matrix.det_apply', Finset.sum_apply]
  have hint (σ : Equiv.Perm n) : Integrable (fun t =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, Q t (σ i) i) haarAddCircle :=
    (hprod σ).1.1.const_mul _
  have hcoeff (k : ℤ) : fourierCoeff (fun t => (Q t).det) k = ∑ σ : Equiv.Perm n,
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * fourierCoeff (fun t => ∏ i, Q t (σ i) i) k := by
    rw [e, fourierCoeff.sum _ _ fun σ _ => hint σ, Finset.sum_apply]
    exact Finset.sum_congr rfl fun σ _ => fourierCoeff.const_mul _ _ _
  refine ⟨?_, fun k hk => ?_, ?_⟩
  · rw [e]
    exact integrable_finsetSum' _ fun σ _ => hint σ
  · rw [hcoeff]
    exact Finset.sum_eq_zero fun σ _ => by rw [(hprod σ).1.2.1 k hk, mul_zero]
  · rw [hcoeff, Matrix.det_apply']
    exact Finset.sum_congr rfl fun σ _ => by rw [(hprod σ).2]; rfl

/-- As in Helson–Lowdenslager (1958), (70), where `Q` is the function `B` of (69): a bounded
analytic function `Q` with values in the square matrices and `det Q̂ (0) ≠ 0` satisfies
`∫ log |det Q| ≥ log |det Q̂ (0)|`. -/
theorem log_norm_det_le_integral_log_norm_det {Q : UnitAddCircle → Matrix n n ℂ} {C : ℝ}
    (hQ : IsHardyOne Q) (hC : ∀ᵐ t ∂haarAddCircle, ∀ i j, ‖Q t i j‖ ≤ C)
    (h0 : (matFourierCoeff Q 0).det ≠ 0) :
    (∀ᵐ t ∂haarAddCircle, (Q t).det ≠ 0) ∧
      Integrable (fun t => Real.log ‖(Q t).det‖) haarAddCircle ∧
      Real.log ‖(matFourierCoeff Q 0).det‖ ≤ ∫ t, Real.log ‖(Q t).det‖ ∂haarAddCircle := by
  obtain ⟨h1, h2, h3⟩ := fourierCoeff_det_of_bounded hQ hC
  rw [← h3] at h0 ⊢
  exact log_norm_fourierCoeff_zero_le_integral_log_norm h1 h2 h0

end HarmonicAnalysis
