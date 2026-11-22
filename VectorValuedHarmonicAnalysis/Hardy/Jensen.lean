module

public import VectorValuedHarmonicAnalysis.Hardy.Approximation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-!
# Jensen's inequality for analytic functions on the circle

An integrable function `f` on the circle whose Fourier coefficients of negative order vanish and
whose mean value `f̂ (0)` is not zero satisfies `∫ log |f| ≥ log |f̂ (0)|`; in particular, `log |f|`
is integrable (H. Helson and D. Lowdenslager, *Prediction theory and Fourier series in several
variables*, Acta Math. 99 (1958), 165–202, Theorem 2 and its Corollary, for the circle). For
analytic polynomials this is Jensen's formula (the source deduces the square-summable case from its
Theorem 1, and names Jensen's formula as the alternative on p. 192); in general `f` is the limit in
`L¹` of its Fejér means.

For a bounded analytic function `Q` with values in the square matrices, `det Q` is bounded and
analytic with constant coefficient `det Q̂ (0)`, hence `∫ log |det Q| ≥ log |det Q̂ (0)|` (cf. (70),
loc. cit.).
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexConjugate Topology

namespace VectorValuedHarmonicAnalysis

/-! ### Analytic polynomials -/

/-- The polynomial `Σ_{k ≥ 0} c_k X^k`. -/
private noncomputable def analyticPoly (c : ℤ →₀ ℂ) : Polynomial ℂ :=
  ∑ k ∈ c.support, Polynomial.monomial k.toNat (c k)

/-- The characters of order `≥ 0` are the powers of `e_1`. -/
private theorem fourier_natCast (k : ℕ) (t : UnitAddCircle) :
    fourier (k : ℤ) t = fourier 1 t ^ k := by
  simp [fourier_apply, toCircle_nsmul]

/-- An analytic polynomial `Σ_{k ≥ 0} c_k e_k` is the composition of `Σ_{k ≥ 0} c_k X^k` with
`e_1`. -/
private theorem eval_analyticPoly {c : ℤ →₀ ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k) (t : UnitAddCircle) :
    (analyticPoly c).eval (fourier 1 t) = trigPoly c t := by
  rw [analyticPoly, Polynomial.eval_finsetSum, trigPoly, Finsupp.sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Polynomial.eval_monomial, ← fourier_natCast, Int.toNat_of_nonneg (hc k hk), smul_eq_mul,
    mul_comm]

/-- The constant coefficient of the polynomial of an analytic polynomial. -/
private theorem coeff_zero_analyticPoly {c : ℤ →₀ ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k) :
    (analyticPoly c).coeff 0 = c 0 := by
  rw [analyticPoly, Polynomial.finsetSum_coeff]
  refine (Finset.sum_eq_single 0 (fun k hk hk0 => ?_) fun h0 => ?_).trans ?_
  · rw [Polynomial.coeff_monomial, ite_eq_right]
    have := hc k hk
    omega
  · rw [Finsupp.notMem_support_iff.1 h0, Polynomial.monomial_zero_right, Polynomial.coeff_zero]
  · rw [Int.toNat_zero, Polynomial.coeff_monomial_same]

/-- Jensen's inequality for polynomials, from Jensen's formula for the Mahler measure,
`M (p) = |a_n| Π max (1, |α_i|)`, where the `α_i` are the roots.

Departure from the source: Helson and Lowdenslager (1958), p. 175, prove the inequality for
square-summable functions, in particular for polynomials, with their Theorem 1; on p. 192 they
mention Jensen's formula as the alternative on the circle. -/
private theorem log_norm_coeff_zero_le_logMahlerMeasure {p : Polynomial ℂ} (h0 : p.coeff 0 ≠ 0) :
    Real.log ‖p.coeff 0‖ ≤ p.logMahlerMeasure := by
  rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
  refine Real.log_le_log (norm_pos_iff.2 h0) ?_
  rw [(IsAlgClosed.splits p).coeff_zero_eq_leadingCoeff_mul_prod_roots,
    Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, norm_mul, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : ‖p.roots.prod‖ = (p.roots.map fun a => ‖a‖).prod :=
    (Multiset.prod_hom p.roots (normHom (α := ℂ))).symm
  rw [h1]
  exact Multiset.prod_map_le_prod_map₀ _ _ (fun a _ => norm_nonneg a) fun a _ => le_max_right _ _

/-- The points of the circle are null sets. -/
private theorem haarAddCircle_singleton (t : UnitAddCircle) : haarAddCircle {t} = 0 := by
  have h1 := volume_closedBall 1 (x := t) 0
  rw [Metric.closedBall_zero, volume_eq_smul_haarAddCircle] at h1
  simpa using h1

/-- The character `e_1` is injective. -/
private theorem injective_fourier_one :
    Function.Injective fun t : UnitAddCircle => fourier 1 t := fun t s hts => by
  simp only [fourier_one] at hts
  exact injective_toCircle one_ne_zero (Circle.coe_injective hts)

/-- Integrals over the circle as integrals over `[0, 2π]`. -/
private theorem integrable_and_integral_eq {g : ℂ → ℝ} (hg : Measurable g)
    (hint : CircleIntegrable g 0 1) :
    Integrable (fun t : UnitAddCircle => g (fourier 1 t)) haarAddCircle ∧
      ∫ t : UnitAddCircle, g (fourier 1 t) ∂haarAddCircle = Real.circleAverage g 0 1 := by
  have hvol : (haarAddCircle : Measure UnitAddCircle) = volume := by
    rw [volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  have e (x : ℝ) : fourier 1 (x : UnitAddCircle) = circleMap 0 1 (2 * Real.pi * x) := by
    rw [fourier_coe_apply, circleMap_zero, Complex.ofReal_one, one_mul, div_one]
    push_cast
    ring_nf
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hmeas : Measurable fun t : UnitAddCircle => g (fourier 1 t) :=
    hg.comp (fourier 1).continuous.measurable
  rw [hvol]
  constructor
  · rw [← (UnitAddCircle.measurePreserving_mk 0).integrable_comp hmeas.aestronglyMeasurable]
    have h1 : IntervalIntegrable (fun x : ℝ => g (circleMap 0 1 (2 * Real.pi * x))) volume
        (0 / (2 * Real.pi)) (2 * Real.pi / (2 * Real.pi)) :=
      IntervalIntegrable.comp_mul_left hint
    rw [zero_div, div_self hpi, intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h1
    simpa only [zero_add, IntegrableOn, Function.comp_def, e] using h1
  · rw [← UnitAddCircle.intervalIntegral_preimage 0, zero_add, Real.circleAverage_def]
    simp only [e]
    rw [intervalIntegral.integral_comp_mul_left (fun x => g (circleMap 0 1 x)) hpi, mul_zero,
      mul_one]

/-- Jensen's inequality for an analytic polynomial `f = Σ_{k ≥ 0} c_k e_k` with `c_0 ≠ 0`: `f ≠ 0`
almost everywhere, `log |f|` is integrable, and `∫ log |f| ≥ log |c_0|`. -/
theorem log_norm_apply_zero_le_integral_log_norm_trigPoly {c : ℤ →₀ ℂ}
    (hc : ∀ k ∈ c.support, 0 ≤ k) (h0 : c 0 ≠ 0) :
    (∀ᵐ t ∂haarAddCircle, trigPoly c t ≠ 0) ∧
      Integrable (fun t => Real.log ‖trigPoly c t‖) haarAddCircle ∧
      Real.log ‖c 0‖ ≤ ∫ t, Real.log ‖trigPoly c t‖ ∂haarAddCircle := by
  have hp0 : (analyticPoly c).coeff 0 ≠ 0 := by rwa [coeff_zero_analyticPoly hc]
  have hp : analyticPoly c ≠ 0 := fun h => hp0 (by rw [h, Polynomial.coeff_zero])
  obtain ⟨h1, h2⟩ := integrable_and_integral_eq
    (g := fun z => Real.log ‖(analyticPoly c).eval z‖)
    (Real.measurable_log.comp (analyticPoly c).continuous.norm.measurable)
    (analyticPoly c).intervalIntegrable_mahlerMeasure
  simp only [eval_analyticPoly hc] at h1 h2
  refine ⟨?_, h1, ?_⟩
  · have hfin : {t : UnitAddCircle | trigPoly c t = 0}.Finite := by
      refine Set.Finite.subset (Set.Finite.preimage injective_fourier_one.injOn
        (analyticPoly c).roots.toFinset.finite_toSet) fun t ht => ?_
      rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp,
        Polynomial.IsRoot.def, eval_analyticPoly hc]
      exact ht
    have hnull : NullSingletonClass (haarAddCircle : Measure UnitAddCircle) :=
      ⟨haarAddCircle_singleton⟩
    exact compl_mem_ae_iff.2 (hfin.measure_zero haarAddCircle)
  · rw [h2, ← coeff_zero_analyticPoly hc]
    exact log_norm_coeff_zero_le_logMahlerMeasure hp0

/-! ### Integrable analytic functions -/

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

/-- `log (|f| + ε)` is integrable if `f` is integrable. -/
private theorem integrable_log_norm_add {f : UnitAddCircle → ℂ} (hf : Integrable f haarAddCircle)
    {ε : ℝ} (hε : 0 < ε) : Integrable (fun t => Real.log (‖f t‖ + ε)) haarAddCircle := by
  have h1 : Integrable (fun t => Real.log (‖f t‖ + ε) - Real.log ε) haarAddCircle := by
    refine (hf.norm.const_mul ε⁻¹).mono' ?_ (ae_of_all _ fun t => ?_)
    · exact ((Real.measurable_log.comp_aemeasurable
        (hf.norm.aemeasurable.add_const ε)).sub_const _).aestronglyMeasurable
    · simpa using abs_log_add_sub_log_add_le hε (norm_nonneg (f t)) le_rfl
  exact (h1.add (integrable_const (Real.log ε))).congr (ae_of_all _ fun t => sub_add_cancel _ _)

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
  rw [← integral_sub (integrable_log_norm_add (hF K) hε) (integrable_log_norm_add hf hε),
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((hF K).sub hf).norm.const_mul _) (ae_of_all _ fun t => ?_)
  refine (abs_log_add_sub_log_add_le hε (norm_nonneg _) (norm_nonneg _)).trans ?_
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (inv_nonneg.2 hε.le)

/-- The scalar Fejér means, as trigonometric polynomials. -/
private theorem exists_tendsto_trigPoly {f : UnitAddCircle → ℂ} (hf : Integrable f haarAddCircle)
    (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0) :
    ∃ c : ℕ → ℤ →₀ ℂ, (∀ K, ∀ k ∈ (c K).support, 0 ≤ k) ∧ (∀ K, c K 0 = fourierCoeff f 0) ∧
      Tendsto (fun K => ∫ t, ‖trigPoly (c K) t - f t‖ ∂haarAddCircle) atTop (𝓝 0) := by
  let F : UnitAddCircle → Matrix Unit Unit ℂ := fun t => Matrix.of fun _ _ => f t
  have hF (i j : Unit) : Integrable (fun t => F t i j) haarAddCircle := hf
  have hFneg (k : ℤ) (hk : k < 0) : matFourierCoeff F k = 0 := by
    ext i j
    exact hneg k hk
  let T : Matrix Unit Unit ℂ →ₗ[ℂ] ℂ := Matrix.entryLinearMap ℂ ℂ () ()
  refine ⟨fun K => (fejerCoeff F (K + 1)).mapRange T (map_zero T), fun K k hk => ?_,
    fun K => ?_, ?_⟩
  · exact nonneg_of_mem_support_fejerCoeff hFneg (K + 1) k (Finsupp.support_mapRange hk)
  · dsimp only
    rw [Finsupp.mapRange_apply, fejerCoeff_zero F K.succ_pos]
    rfl
  · refine ((tendsto_integral_norm_fejerCoeff_sub hF () ()).comp
      (tendsto_add_atTop_nat 1)).congr fun K => integral_congr_ae (ae_of_all _ fun t => ?_)
    dsimp only [Function.comp_apply]
    rw [trigPoly_mapRange]
    rfl

/-- Helson–Lowdenslager (1958), pp. 175–176: `∫ log (|f| + ε) ≥ log |f̂ (0)|`, the limit of the
inequalities `∫ log (|f_K| + ε) ≥ ∫ log |f_K| ≥ log |f̂ (0)|` for the Fejér means `f_K` of `f`. -/
private theorem log_norm_fourierCoeff_zero_le_integral_log_norm_add {f : UnitAddCircle → ℂ}
    (hf : Integrable f haarAddCircle) (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0)
    (h0 : fourierCoeff f 0 ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    Real.log ‖fourierCoeff f 0‖ ≤ ∫ t, Real.log (‖f t‖ + ε) ∂haarAddCircle := by
  obtain ⟨c, hc, hc0, hlim⟩ := exists_tendsto_trigPoly hf hneg
  have hint (K : ℕ) := integrable_haar_of_continuous (continuous_trigPoly (c K))
  refine ge_of_tendsto' (tendsto_integral_log_norm_add hint hf hlim hε) fun K => ?_
  obtain ⟨hne, hlog, hle⟩ := log_norm_apply_zero_le_integral_log_norm_trigPoly (hc K)
    (by rwa [hc0])
  rw [hc0] at hle
  refine hle.trans (integral_mono_ae hlog (integrable_log_norm_add (hint K) hε) ?_)
  filter_upwards [hne] with t ht
  exact Real.log_le_log (norm_pos_iff.2 ht) (by linarith)

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
172): if the positive functions `u_k` decrease to `w`, `log u_k ≤ G` with `G` integrable, and the
integrals of `log u_k` are at least `L`, then `w > 0` almost everywhere, `log w` is integrable, and
`∫ log w ≥ L`. -/
theorem pos_and_integrable_log {w G : UnitAddCircle → ℝ} {u : ℕ → UnitAddCircle → ℝ} {L : ℝ}
    (hu0 : ∀ᵐ t ∂haarAddCircle, ∀ k, 0 < u k t)
    (hanti : ∀ᵐ t ∂haarAddCircle, Antitone fun k => u k t)
    (hlim : ∀ᵐ t ∂haarAddCircle, Tendsto (fun k => u k t) atTop (𝓝 (w t)))
    (hG : Integrable G haarAddCircle)
    (hu : ∀ k, Integrable (fun t => Real.log (u k t)) haarAddCircle)
    (huG : ∀ᵐ t ∂haarAddCircle, ∀ k, Real.log (u k t) ≤ G t)
    (hL : ∀ k, L ≤ ∫ t, Real.log (u k t) ∂haarAddCircle) :
    (∀ᵐ t ∂haarAddCircle, 0 < w t) ∧ Integrable (fun t => Real.log (w t)) haarAddCircle ∧
      L ≤ ∫ t, Real.log (w t) ∂haarAddCircle := by
  let f (k : ℕ) (t : UnitAddCircle) : ℝ≥0∞ := ENNReal.ofReal (G t - Real.log (u k t))
  have hf (k : ℕ) : AEMeasurable (f k) haarAddCircle :=
    (hG.sub (hu k)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmono : ∀ᵐ t ∂haarAddCircle, Monotone fun k => f k t := by
    filter_upwards [hu0, hanti] with t h0 ht i j hij
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (Real.log_le_log (h0 j) (ht hij)) _)
  have hle : ∫⁻ t, ⨆ k, f k t ∂haarAddCircle ≤ ENNReal.ofReal (∫ t, G t ∂haarAddCircle - L) := by
    rw [lintegral_iSup' hf hmono]
    refine iSup_le fun k => ?_
    refine (ofReal_integral_eq_lintegral_ofReal (hG.sub (hu k))
      (huG.mono fun t ht => sub_nonneg.2 (ht k))).symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
    exact (integral_sub hG (hu k)).trans_le (sub_le_sub_left (hL k) _)
  have hfin := ae_lt_top' (AEMeasurable.iSup hf) (hle.trans_lt ENNReal.ofReal_lt_top).ne
  have key : ∀ᵐ t ∂haarAddCircle, 0 < w t ∧ G t - Real.log (w t) ≤ (⨆ k, f k t).toReal := by
    filter_upwards [hu0, hlim, hfin] with t h0 hl hf
    refine pos_and_sub_log_le h0 hl fun k => ?_
    exact (ENNReal.ofReal_le_iff_le_toReal hf.ne).1 (le_iSup (fun k => f k t) k)
  -- `G − log w ≥ 0` is integrable, with integral at most `∫ G − L`
  have hlog : ∀ᵐ t ∂haarAddCircle, Tendsto (fun k => Real.log (u k t)) atTop
      (𝓝 (Real.log (w t))) := by
    filter_upwards [hlim, key] with t hl hk
    exact (Real.continuousAt_log hk.1.ne').tendsto.comp hl
  have hmeas : AEStronglyMeasurable (fun t => G t - Real.log (w t)) haarAddCircle :=
    hG.aestronglyMeasurable.sub
      (aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hu k).aestronglyMeasurable) hlog)
  have hnn : 0 ≤ᵐ[haarAddCircle] fun t => G t - Real.log (w t) := by
    filter_upwards [hlog, huG] with t hl hG
    exact sub_nonneg.2 (le_of_tendsto' hl hG)
  have hlint := (lintegral_mono_ae (f := fun t => ENNReal.ofReal (G t - Real.log (w t)))
    (hfin.mp (key.mono fun t ht hf => (ENNReal.ofReal_le_iff_le_toReal hf.ne).2 ht.2))).trans hle
  have hD : Integrable (fun t => G t - Real.log (w t)) haarAddCircle :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).2 (hlint.trans_lt ENNReal.ofReal_lt_top)⟩
  have hDint : ∫ t, (G t - Real.log (w t)) ∂haarAddCircle ≤ ∫ t, G t ∂haarAddCircle - L := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    refine ENNReal.toReal_le_of_le_ofReal (sub_nonneg.2 ((hL 0).trans ?_)) hlint
    exact integral_mono_ae (hu 0) hG (huG.mono fun t ht => ht 0)
  have e : (fun t => Real.log (w t)) = fun t => G t - (G t - Real.log (w t)) := by simp
  rw [e, integral_sub hG hD]
  exact ⟨key.mono fun t ht => ht.1, hG.sub hD, by linarith⟩

/-- Helson–Lowdenslager (1958), Theorem 2 and its Corollary, on the circle: an integrable function
`f` whose Fourier coefficients of negative order vanish, with `f̂ (0) ≠ 0`, satisfies
`∫ log |f| ≥ log |f̂ (0)|`, and `log |f|` is integrable; `f ≠ 0` almost everywhere. -/
theorem log_norm_fourierCoeff_zero_le_integral_log_norm {f : UnitAddCircle → ℂ}
    (hf : Integrable f haarAddCircle) (hneg : ∀ k : ℤ, k < 0 → fourierCoeff f k = 0)
    (h0 : fourierCoeff f 0 ≠ 0) :
    (∀ᵐ t ∂haarAddCircle, f t ≠ 0) ∧ Integrable (fun t => Real.log ‖f t‖) haarAddCircle ∧
      Real.log ‖fourierCoeff f 0‖ ≤ ∫ t, Real.log ‖f t‖ ∂haarAddCircle := by
  -- the last step of the proof of Theorem 2 of the source, `ε → 0`, by monotone convergence
  have hε (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
  have hlim (t : UnitAddCircle) : Tendsto (fun k : ℕ => ‖f t‖ + 1 / ((k : ℝ) + 1)) atTop
      (𝓝 ‖f t‖) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add ‖f t‖
  have h := pos_and_integrable_log (u := fun k t => ‖f t‖ + 1 / ((k : ℝ) + 1))
    (ae_of_all _ fun t k => add_pos_of_nonneg_of_pos (norm_nonneg _) (hε k))
    (ae_of_all _ fun t i j hij => add_le_add_right (Nat.one_div_le_one_div hij) _)
    (ae_of_all _ hlim) (integrable_log_norm_add hf one_pos)
    (fun k => integrable_log_norm_add hf (hε k)) (ae_of_all _ fun t k => ?_)
    fun k => log_norm_fourierCoeff_zero_le_integral_log_norm_add hf hneg h0 (hε k)
  · simpa only [norm_pos_iff] using h
  · refine Real.log_le_log (add_pos_of_nonneg_of_pos (norm_nonneg _) (hε k)) ?_
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 (by simp)
    linarith

/-! ### Determinants -/

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

end VectorValuedHarmonicAnalysis
