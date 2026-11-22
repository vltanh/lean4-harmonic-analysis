module

public import VectorValuedHarmonicAnalysis.Dyadic.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Averages of dyadic shifts are convolutions

Averaging the dyadic shift with kernel `k` over the translates of the dyadic system turns its part
of generation `j` into the convolution with `φ_{2^{−j}}`, where `φ (x) = ∫ k (x + u) h (u) du`
(`haarCorrelation k`) and `φ_t (x) = t⁻¹ φ (t⁻¹ x)` (`intervalIntegral_dyadicShift_translate`; HNVW
I, Lemma 5.1.9, p. 381). With the bounds for the dyadic shifts this gives, on a UMD space `X` (HNVW
I, Proposition 5.1.10, p. 383, for finitely many generations):

* `‖Σ_j ε_j φ_{2^{−j}} * f‖_{L^p (ℝ × Ω)} ≤ 2 β ‖f‖_p`, for `k = h` (`eLpNormRad_dilateConv_le`);
* `‖Σ_j φ_{t 2^{−j}} * f‖_p ≤ 2 β² ‖f‖_p`, for `k = haarSplit` and every `t > 0`
  (`eLpNorm_sum_dilateConv_le`).

Source: Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I* (2016), pp. 379–384.
The book averages over the random dyadic systems `𝒟^ω`, `ω ∈ {0, 1}^ℤ`; for the generations `j ≥ 0`
only, `𝒟^ω` is the translate of the standard system by a point of `[0, 1)`, uniformly distributed.
-/

@[expose] public section

open MeasureTheory BanachProbability
open scoped ENNReal

namespace VectorValuedHarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- HNVW I, (5.14): `φ (x) = ∫ k (x + u) h (u) du`. -/
noncomputable def haarCorrelation (k : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, k (x + u) * haar u

/-- The convolution `φ_t * f`, `φ_t (x) = t⁻¹ φ (t⁻¹ x)`. -/
noncomputable def dilateConv (φ : ℝ → ℝ) (t : ℝ) (f : ℝ → X) (x : ℝ) : X :=
  ∫ y, (t⁻¹ * φ (t⁻¹ * (x - y))) • f y

/-- The part of generation `j` of the dyadic shift of the translate `f (· + u)` at `x − u`, as a
function of the relative position `w = {2^j (x − u)}` of `x − u` in its dyadic interval. -/
private noncomputable def shiftAt (k : ℝ → ℝ) (j : ℕ) (f : ℝ → X) (x w : ℝ) : X :=
  (2 ^ j * k w) • ∫ y, haar (2 ^ j * (y - x) + w) • f y

omit [CompleteSpace X] in
/-- Substitute `y − u` for `y`. -/
private theorem dyadicShift_translate (k : ℝ → ℝ) (j : ℕ) (f : ℝ → X) (u x : ℝ) :
    dyadicShift k j (fun y => f (y + u)) (x - u) =
      shiftAt k j f x (Int.fract (2 ^ j * (x - u))) := by
  rw [dyadicShift, shiftAt]
  congr 1
  rw [← integral_add_right_eq_self
    (fun y => haar (2 ^ j * (y - x) + Int.fract (2 ^ j * (x - u))) • f y) u]
  congr 1
  funext y
  rw [Int.fract]
  congr 2
  ring

omit [CompleteSpace X] in
/-- The integrand is supported in `[x − 1, x + 1]`. -/
private theorem norm_haar_smul_le (j : ℕ) (f : ℝ → X) {x w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (y : ℝ) : ‖haar (2 ^ j * (y - x) + w) • f y‖ ≤
      (Set.Icc (x - 1) (x + 1)).indicator (fun y => ‖f y‖) y := by
  have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  by_cases h : 2 ^ j * (y - x) + w ∈ Set.Ico (0 : ℝ) 1
  · have hy : y ∈ Set.Icc (x - 1) (x + 1) := by
      constructor
      · by_contra hlt
        nlinarith [h.1]
      · by_contra hlt
        nlinarith [h.2]
    rw [Set.indicator_of_mem hy, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_haar_le_one _)
  · rw [haar_of_notMem h, zero_smul, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem integrable_indicator_norm {f : ℝ → X} (hf : LocallyIntegrable f) (x : ℝ) :
    Integrable ((Set.Icc (x - 1) (x + 1)).indicator fun y => ‖f y‖) :=
  IntegrableOn.integrable_indicator (hf.integrableOn_isCompact isCompact_Icc).norm measurableSet_Icc

omit [CompleteSpace X] in
private theorem norm_shiftAt_le {k : ℝ → ℝ} {C : ℝ} (hk : ∀ x, |k x| ≤ C) (j : ℕ) {f : ℝ → X}
    (hf : LocallyIntegrable f) (x : ℝ) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ‖shiftAt k j f x w‖ ≤ 2 ^ j * C * ∫ y in Set.Icc (x - 1) (x + 1), ‖f y‖ := by
  rw [shiftAt, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have h := norm_integral_le_of_norm_le (integrable_indicator_norm hf x)
    (ae_of_all _ (norm_haar_smul_le j f (x := x) hw0 hw1))
  rw [integral_indicator measurableSet_Icc] at h
  have hC : 0 ≤ C := (abs_nonneg _).trans (hk 0)
  gcongr
  exact hk w

omit [CompleteSpace X] in
/-- Joint measurability in the point and in the position of the dyadic system (HNVW I, Lemma 5.1.8),
by the measurability of parametric integrals. -/
private theorem stronglyMeasurable_shiftAt {k : ℝ → ℝ} (hk : Measurable k) (j : ℕ) {f : ℝ → X}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable fun z : ℝ × ℝ => shiftAt k j f z.1 z.2 := by
  have h1 : Measurable fun z : ℝ × ℝ => 2 ^ j * k z.2 := (hk.comp measurable_snd).const_mul _
  have h2 : Measurable fun q : (ℝ × ℝ) × ℝ => haar (2 ^ j * (q.2 - q.1.1) + q.1.2) :=
    measurable_haar.comp (by fun_prop)
  refine h1.stronglyMeasurable.smul (StronglyMeasurable.integral_prod_right'
    (f := fun q : (ℝ × ℝ) × ℝ => haar (2 ^ j * (q.2 - q.1.1) + q.1.2) • f q.2) ?_)
  exact h2.stronglyMeasurable.smul (hf.comp_measurable measurable_snd)

omit [CompleteSpace X] in
/-- `{2^j (x − u)}` is uniformly distributed on `[0, 1)` for `u` uniformly distributed on `[0, 1)`,
by periodicity (HNVW I, proof of Lemma 5.1.9, where `Σ_m ∫_0^1 … du` becomes an integral over the
line). -/
private theorem intervalIntegral_comp_fract (j : ℕ) (x : ℝ) {G : ℝ → X}
    (hG : IntervalIntegrable G volume 0 1) :
    ∫ u in (0 : ℝ)..1, G (Int.fract (2 ^ j * (x - u))) = ∫ w in (0 : ℝ)..1, G w := by
  set P : ℝ → X := fun v => G (Int.fract v) with hP
  have hper : Function.Periodic P 1 := fun v => by simp only [hP, Int.fract_add_one]
  have hPG : ∀ v ∈ Set.Ioo (0 : ℝ) 1, P v = G v := fun v hv => by
    simp only [hP, Int.fract_eq_self.2 ⟨hv.1.le, hv.2⟩]
  have hPi : IntervalIntegrable P volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at hG ⊢
    exact hG.congr_fun (fun v hv => (hPG v hv).symm) measurableSet_Ioo
  have hPint : ∫ v in (0 : ℝ)..1, P v = ∫ v in (0 : ℝ)..1, G v := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo hPG
  have h2 : (2 : ℝ) ^ j ≠ 0 := by positivity
  have h := intervalIntegral.integral_comp_sub_mul (a := 0) (b := 1) P h2 (2 ^ j * x)
  have hz := hper.intervalIntegral_add_zsmul_eq (2 ^ j) (2 ^ j * x - 2 ^ j * 1)
    (hper.intervalIntegrable₀ one_ne_zero hPi)
  have he : 2 ^ j * x - 2 ^ j * 1 + (2 ^ j : ℤ) • (1 : ℝ) = 2 ^ j * x - 2 ^ j * 0 := by
    simp
  rw [he, hper.intervalIntegral_add_eq _ 0, zero_add, hPint] at hz
  rw [hz] at h
  simp only [mul_sub]
  rw [h, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ h2, one_smul]

/-- The admissible kernels: bounded, measurable and supported in `[0, 1)`. -/
private theorem kernel_props {k : ℝ → ℝ} (hk : k = haar ∨ k = haarSplit) :
    Measurable k ∧ (∀ x, |k x| ≤ 2) ∧ ∀ x ∉ Set.Ico (0 : ℝ) 1, k x = 0 := by
  rcases hk with rfl | rfl
  · exact ⟨measurable_haar, fun x => (abs_haar_le_one x).trans one_le_two,
      fun x hx => haar_of_notMem hx⟩
  · refine ⟨measurable_haarSplit, fun x => ?_, fun x hx => ?_⟩
    · refine (abs_sub _ _).trans ?_
      linarith [abs_haar_le_one (2 * x), abs_haar_le_one (2 * x - 1)]
    · rw [haarSplit, haar_of_notMem, haar_of_notMem, sub_zero]
      · rintro ⟨h1, h2⟩
        exact hx ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact hx ⟨by linarith, by linarith⟩

/-- The substitution `u = w − z` in `φ (z) = ∫ k (z + u) h (u) du`. -/
private theorem haarCorrelation_eq {k : ℝ → ℝ} (hk0 : ∀ x ∉ Set.Ico (0 : ℝ) 1, k x = 0) (z : ℝ) :
    haarCorrelation k z = ∫ w in (0 : ℝ)..1, k w * haar (w - z) := by
  have h : haarCorrelation k z = ∫ w, k w * haar (w - z) := by
    rw [haarCorrelation, ← integral_add_right_eq_self (fun w => k w * haar (w - z)) z]
    simp only [add_comm z, add_sub_cancel_right]
  rw [h, intervalIntegral.integral_of_le zero_le_one, ← integral_Ico_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => by
    rw [hk0 w hw, zero_mul]).symm

omit [CompleteSpace X] in
/-- The integrability for Fubini's theorem in the proof of Lemma 5.1.9. -/
private theorem integrable_shift_prod {k : ℝ → ℝ} (hkm : Measurable k) (hkb : ∀ x, |k x| ≤ 2)
    (j : ℕ) {f : ℝ → X} (hf : LocallyIntegrable f) (hfm : StronglyMeasurable f) (x : ℝ) :
    Integrable (Function.uncurry fun w y : ℝ => (2 ^ j * k w) • haar (2 ^ j * (y - x) + w) • f y)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le zero_le_one]
    infer_instance
  refine (((integrable_indicator_norm hf x).comp_snd
    (volume.restrict (Set.uIoc (0 : ℝ) 1))).const_mul (2 ^ j * 2)).mono' ?_ ?_
  · have h1 : Measurable fun z : ℝ × ℝ => 2 ^ j * k z.1 := (hkm.comp measurable_fst).const_mul _
    have h2 : Measurable fun z : ℝ × ℝ => haar (2 ^ j * (z.2 - x) + z.1) :=
      measurable_haar.comp (by fun_prop)
    exact (h1.stronglyMeasurable.smul (h2.stronglyMeasurable.smul
      (hfm.comp_measurable measurable_snd))).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_uIoc)]
      with z hz
    rw [Set.uIoc_of_le zero_le_one] at hz
    rw [Function.uncurry, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    · exact hkb _
    · exact norm_haar_smul_le j f hz.1.le hz.2 z.2

/-- Fubini's theorem and the substitution `u = t⁻¹ y − v` (HNVW I, proof of Lemma 5.1.9). -/
private theorem intervalIntegral_shiftAt {k : ℝ → ℝ} (hk : k = haar ∨ k = haarSplit) (j : ℕ)
    {f : ℝ → X} (hf : LocallyIntegrable f) (hfm : StronglyMeasurable f) (x : ℝ) :
    ∫ w in (0 : ℝ)..1, shiftAt k j f x w =
      dilateConv (haarCorrelation k) (((2 : ℝ) ^ j)⁻¹) f x := by
  obtain ⟨hkm, hkb, hk0⟩ := kernel_props hk
  simp only [shiftAt, ← integral_smul]
  rw [intervalIntegral_integral_swap (integrable_shift_prod hkm hkb j hf hfm x), dilateConv]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_smul, inv_inv]
  rw [intervalIntegral.integral_smul_const, haarCorrelation_eq hk0,
    ← intervalIntegral.integral_const_mul]
  congr 2
  funext w
  rw [mul_assoc]
  congr 3
  ring

omit [CompleteSpace X] in
private theorem intervalIntegrable_shiftAt {k : ℝ → ℝ} (hkm : Measurable k) (hkb : ∀ x, |k x| ≤ 2)
    (j : ℕ) {f : ℝ → X} (hf : LocallyIntegrable f) (hfm : StronglyMeasurable f) (x : ℝ) :
    IntervalIntegrable (shiftAt k j f x) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine IntegrableOn.of_bound (by simp) ((stronglyMeasurable_shiftAt hkm j hfm).comp_measurable
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun w hw =>
      norm_shiftAt_le hkb j hf x hw.1.le hw.2))

/-- HNVW I, Lemma 5.1.9: averaging over the translates of the dyadic system gives a convolution. -/
theorem intervalIntegral_dyadicShift_translate {k : ℝ → ℝ} (hk : k = haar ∨ k = haarSplit) (j : ℕ)
    {f : ℝ → X} (hf : LocallyIntegrable f) (x : ℝ) :
    ∫ u in (0 : ℝ)..1, dyadicShift k j (fun y => f (y + u)) (x - u) =
      dilateConv (haarCorrelation k) (((2 : ℝ) ^ j)⁻¹) f x := by
  obtain ⟨hkm, hkb, -⟩ := kernel_props hk
  -- replace `f` by a strongly measurable function
  set g : ℝ → X := hf.aestronglyMeasurable.mk f with hg
  have hgm : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgl : LocallyIntegrable g := (locallyIntegrable_congr hfg).1 hf
  have h1 : ∀ w, shiftAt k j f x w = shiftAt k j g x w := fun w => by
    rw [shiftAt, shiftAt]
    congr 1
    exact integral_congr_ae (hfg.mono fun y hy => by simp only [hy])
  have h2 : dilateConv (haarCorrelation k) (((2 : ℝ) ^ j)⁻¹) f x =
      dilateConv (haarCorrelation k) (((2 : ℝ) ^ j)⁻¹) g x :=
    integral_congr_ae (hfg.mono fun y hy => by simp only [hy])
  simp only [dyadicShift_translate, h1]
  rw [h2, intervalIntegral_comp_fract j x (intervalIntegrable_shiftAt hkm hkb j hgl hgm x),
    intervalIntegral_shiftAt hk j hgl hgm x]

omit [CompleteSpace X] in
/-- Joint measurability of the translated shifts (HNVW I, Lemma 5.1.8). -/
private theorem stronglyMeasurable_translate {k : ℝ → ℝ} (hkm : Measurable k) (j : ℕ) {f : ℝ → X}
    (hfm : StronglyMeasurable f) : StronglyMeasurable
      (Function.uncurry fun u x : ℝ => dyadicShift k j (fun y => f (y + u)) (x - u)) := by
  have h : Measurable fun z : ℝ × ℝ => (z.2, Int.fract ((2 : ℝ) ^ j * (z.2 - z.1))) :=
    measurable_snd.prodMk (measurable_snd.sub measurable_fst |>.const_mul _).fract
  simp only [dyadicShift_translate]
  exact (stronglyMeasurable_shiftAt hkm j hfm).comp_measurable h

omit [CompleteSpace X] in
/-- The translated shifts are integrable in the translation. -/
private theorem integrable_translate {k : ℝ → ℝ} (hk : k = haar ∨ k = haarSplit) (j : ℕ) {f : ℝ → X}
    (hf : LocallyIntegrable f) (hfm : StronglyMeasurable f) (x : ℝ) :
    Integrable (fun u => dyadicShift k j (fun y => f (y + u)) (x - u))
      (volume.restrict (Set.Ioc 0 1)) := by
  obtain ⟨hkm, hkb, -⟩ := kernel_props hk
  refine IntegrableOn.of_bound (C := 2 ^ j * 2 * ∫ y in Set.Icc (x - 1) (x + 1), ‖f y‖) (by simp)
    ((stronglyMeasurable_translate hkm j hfm).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [dyadicShift_translate]
  exact norm_shiftAt_le hkb j hf x (Int.fract_nonneg _) (Int.fract_lt_one _).le

omit [CompleteSpace X] in
/-- Translation invariance of the norms. -/
private theorem eLpNormRad_sub {p : ℝ} (hp : 0 < p) {n : ℕ} {g : Fin n → ℝ → X}
    (hg : ∀ j, StronglyMeasurable (g j)) (u : ℝ) :
    eLpNormRad (fun j x => g j (x - u)) p volume ≤ eLpNormRad g p volume := by
  have h := eLpNormRad_le_of_forall (C := 1) (μ := volume) (ν := volume) hp
    (f := fun j x => g j (x - u)) (g := g)
    (fun j => ((hg j).comp_measurable (measurable_id.sub_const u)).aestronglyMeasurable)
    (fun j => (hg j).aestronglyMeasurable) fun ε => ?_
  · rwa [one_mul] at h
  · rw [one_mul]
    exact (eLpNorm_comp_measurePreserving
      (g := fun x => ∑ j, SignCube.coin (ε j) • g j x)
      (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hg j).aestronglyMeasurable.const_smul _)
      (measurePreserving_sub_right volume u)).le

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem memLp_translate {p : ℝ≥0∞} {f : ℝ → X} (hf : MemLp f p volume) (u : ℝ) :
    MemLp (fun y => f (y + u)) p volume ∧
      eLpNorm (fun y => f (y + u)) p volume = eLpNorm f p volume :=
  ⟨hf.comp_measurePreserving (measurePreserving_add_right volume u),
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (measurePreserving_add_right volume u)⟩

/-- HNVW I, Proposition 5.1.10, second inequality, for the generations `0 ≤ j < n`. -/
theorem eLpNormRad_dilateConv_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) (hfm : StronglyMeasurable f) (n : ℕ) :
    eLpNormRad (fun j : Fin n => dilateConv (haarCorrelation haar) (((2 : ℝ) ^ (j : ℕ))⁻¹) f) p
        volume ≤
      2 * β * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using hp.le
  have hfl : LocallyIntegrable f := hf.locallyIntegrable hp1
  -- the average of the translated shifts
  have h : (fun j : Fin n => dilateConv (haarCorrelation haar) (((2 : ℝ) ^ (j : ℕ))⁻¹) f) =
      fun (j : Fin n) x => ∫ u in Set.Ioc (0 : ℝ) 1,
        dyadicShift haar j (fun y => f (y + u)) (x - u) := by
    funext j x
    rw [← intervalIntegral_dyadicShift_translate (Or.inl rfl) j hfl x,
      intervalIntegral.integral_of_le zero_le_one]
  rw [h]
  refine (eLpNormRad_integral_le hp.le
    (F := fun (j : Fin n) u x => dyadicShift haar j (fun y => f (y + u)) (x - u))
    (fun j => stronglyMeasurable_translate measurable_haar j hfm)
    (fun j => ae_of_all _ fun x => integrable_translate (Or.inl rfl) j hfl hfm x)).trans ?_
  calc ∫⁻ u in Set.Ioc (0 : ℝ) 1,
        eLpNormRad (fun (j : Fin n) x => dyadicShift haar j (fun y => f (y + u)) (x - u)) p volume
      ≤ ∫⁻ _u in Set.Ioc (0 : ℝ) 1, 2 * β * eLpNorm f (ENNReal.ofReal p) volume := by
        refine lintegral_mono fun u => ?_
        obtain ⟨hfu, hfu'⟩ := memLp_translate hf u
        refine (eLpNormRad_sub (by linarith) (g := fun j : Fin n =>
          dyadicShift haar j fun y => f (y + u)) (fun j => stronglyMeasurable_dyadicShift
            measurable_haar j _) u).trans ?_
        rw [← hfu']
        exact eLpNormRad_dyadicShift_le hp hβ (Or.inl rfl) hfu n
    _ = 2 * β * eLpNorm f (ENNReal.ofReal p) volume := by simp

omit [CompleteSpace X] in
/-- The Rademacher sum with one term. -/
private theorem eLpNormRad_one {p : ℝ} (hp : 0 < p) {g : ℝ → X}
    (hg : AEStronglyMeasurable g volume) :
    eLpNormRad (fun _ : Fin 1 => g) p volume = eLpNorm g (ENNReal.ofReal p) volume := by
  refine ENNReal.rpow_left_injective hp.ne' ?_
  have h : ∀ ε : Fin 1 → Bool, eLpNorm (fun x => ∑ k, SignCube.coin (ε k) • g x)
      (ENNReal.ofReal p) volume = eLpNorm g (ENNReal.ofReal p) volume := fun ε => by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rcases SignCube.coin_eq_one_or_eq_neg_one (ε default) with h | h
    · simp only [h, one_smul]
    · simp only [h, neg_smul, one_smul]
      exact eLpNorm_neg g _ _
  simp only
  rw [eLpNormRad_rpow hp fun _ => hg]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, nsmul_eq_mul, ← mul_assoc, Fintype.card_fin, pow_one, Nat.cast_ofNat]
  rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

omit [CompleteSpace X] in
/-- Minkowski's integral inequality for an average over `[0, 1]`. -/
private theorem eLpNorm_integral_Ioc_le {p : ℝ} (hp : 1 ≤ p) {G : ℝ → ℝ → X}
    (hGm : StronglyMeasurable (Function.uncurry G))
    (hGi : ∀ x, Integrable (fun u => G u x) (volume.restrict (Set.Ioc 0 1))) {C : ℝ≥0∞}
    (hC : ∀ u, eLpNorm (G u) (ENNReal.ofReal p) volume ≤ C) :
    eLpNorm (fun x => ∫ u in Set.Ioc (0 : ℝ) 1, G u x) (ENNReal.ofReal p) volume ≤ C := by
  have hp0 : 0 < p := by linarith
  have hI : AEStronglyMeasurable (fun x => ∫ u in Set.Ioc (0 : ℝ) 1, G u x) volume :=
    hGm.integral_prod_left.aestronglyMeasurable
  have hGu : ∀ u, AEStronglyMeasurable (G u) volume := fun u =>
    (hGm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [← eLpNormRad_one hp0 hI]
  refine (eLpNormRad_integral_le hp (F := fun (_ : Fin 1) u x => G u x)
    (fun _ => hGm) (fun _ => ae_of_all _ hGi)).trans ?_
  calc ∫⁻ u in Set.Ioc (0 : ℝ) 1, eLpNormRad (fun _ : Fin 1 => G u) p volume
      ≤ ∫⁻ _u in Set.Ioc (0 : ℝ) 1, C :=
        lintegral_mono fun u => (eLpNormRad_one hp0 (hGu u)).trans_le (hC u)
    _ = C := by simp

/-- HNVW I, Proposition 5.1.10, first inequality, for the dilation `t = 1`. -/
private theorem eLpNorm_sum_dilateConv_one_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hfm : StronglyMeasurable f) (n : ℕ) :
    eLpNorm (fun x => ∑ j ∈ Finset.range n,
        dilateConv (haarCorrelation haarSplit) (((2 : ℝ) ^ j)⁻¹) f x) (ENNReal.ofReal p) volume ≤
      2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using hp.le
  have hfl : LocallyIntegrable f := hf.locallyIntegrable hp1
  have hi : ∀ x, ∀ j ∈ Finset.range n,
      Integrable (fun u => dyadicShift haarSplit j (fun y => f (y + u)) (x - u))
        (volume.restrict (Set.Ioc 0 1)) :=
    fun x j _ => integrable_translate (Or.inr rfl) j hfl hfm x
  -- the average of the translated shifts
  have h : (fun x => ∑ j ∈ Finset.range n,
      dilateConv (haarCorrelation haarSplit) (((2 : ℝ) ^ j)⁻¹) f x) =
      fun x => ∫ u in Set.Ioc (0 : ℝ) 1,
        ∑ j ∈ Finset.range n, dyadicShift haarSplit j (fun y => f (y + u)) (x - u) := by
    funext x
    rw [integral_finsetSum _ (hi x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← intervalIntegral_dyadicShift_translate (Or.inr rfl) j hfl x,
      intervalIntegral.integral_of_le zero_le_one]
  rw [h]
  refine eLpNorm_integral_Ioc_le hp.le (G := fun u x =>
      ∑ j ∈ Finset.range n, dyadicShift haarSplit j (fun y => f (y + u)) (x - u))
    (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      stronglyMeasurable_translate measurable_haarSplit j hfm)
    (fun x => integrable_finsetSum _ (hi x)) fun u => ?_
  obtain ⟨hfu, hfu'⟩ := memLp_translate hf u
  rw [← hfu']
  refine le_of_eq_of_le ?_ (eLpNorm_sum_dyadicShift_le hp hβ hfu n)
  exact eLpNorm_comp_measurePreserving
    (g := fun x => ∑ j ∈ Finset.range n, dyadicShift haarSplit j (fun y => f (y + u)) x)
    (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (stronglyMeasurable_dyadicShift
      measurable_haarSplit j _).aestronglyMeasurable)
    (measurePreserving_sub_right volume u)

omit [CompleteSpace X] in
/-- Convolutions with dilates are dilates of convolutions. -/
private theorem dilateConv_mul (φ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (s : ℝ) (f : ℝ → X) (x : ℝ) :
    dilateConv φ (t * s) f x = dilateConv φ s (fun y => f (t * y)) (t⁻¹ * x) := by
  have h := Measure.integral_comp_mul_left
    (fun z => (s⁻¹ * φ (s⁻¹ * (t⁻¹ * x - t⁻¹ * z))) • f z) t
  simp only [inv_mul_cancel_left₀ ht.ne'] at h
  rw [dilateConv, dilateConv, h, abs_of_pos (inv_pos.2 ht), ← integral_smul]
  congr 1
  funext y
  rw [smul_smul, mul_inv, mul_assoc, mul_assoc, mul_sub, mul_sub, mul_sub]
  congr 4
  ring

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem eLpNorm_comp_mul {p : ℝ≥0∞} (hp : p ≠ ⊤) {g : ℝ → X}
    (hg : AEStronglyMeasurable g volume) {a : ℝ} (ha : 0 < a) :
    eLpNorm (fun x => g (a * x)) p volume =
      ENNReal.ofReal a⁻¹ ^ (1 / p).toReal * eLpNorm g p volume := by
  have hmap := Real.map_volume_mul_left ha.ne'
  rw [abs_of_pos (inv_pos.2 ha)] at hmap
  have h := eLpNorm_map_measure (p := p) (μ := volume) (f := fun x : ℝ => a * x) (g := g)
    (by rw [hmap]; exact hg.smul_measure _) (measurable_const_mul a).aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_top hp _ _ hg, smul_eq_mul] at h
  exact h.symm

omit [CompleteSpace X] in
private theorem stronglyMeasurable_dilateConv {k : ℝ → ℝ} (hk : k = haar ∨ k = haarSplit) (s : ℝ)
    {f : ℝ → X} (hfm : StronglyMeasurable f) :
    StronglyMeasurable (dilateConv (haarCorrelation k) s f) := by
  have hφ : StronglyMeasurable (haarCorrelation k) :=
    StronglyMeasurable.integral_prod_right (f := fun x u => k (x + u) * haar u)
      ((((kernel_props hk).1.comp (measurable_fst.add measurable_snd)).mul
        (measurable_haar.comp measurable_snd)).stronglyMeasurable)
  refine StronglyMeasurable.integral_prod_right
    (f := fun x y => (s⁻¹ * haarCorrelation k (s⁻¹ * (x - y))) • f y) ?_
  have h1 : Measurable fun z : ℝ × ℝ => s⁻¹ * haarCorrelation k (s⁻¹ * (z.1 - z.2)) :=
    (hφ.measurable.comp (by fun_prop)).const_mul _
  exact h1.stronglyMeasurable.smul (hfm.comp_measurable measurable_snd)

/-- HNVW I, Proposition 5.1.10, first inequality, before the integration over the dilations. -/
theorem eLpNorm_sum_dilateConv_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) (hfm : StronglyMeasurable f) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    eLpNorm (fun x => ∑ j ∈ Finset.range n,
        dilateConv (haarCorrelation haarSplit) (t * ((2 : ℝ) ^ j)⁻¹) f x) (ENNReal.ofReal p)
        volume ≤
      2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume := by
  set a : ℝ := (1 / ENNReal.ofReal p).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  -- the dilate `f (t ·)`
  have hgm : StronglyMeasurable fun y => f (t * y) :=
    hfm.comp_measurable (measurable_const_mul t)
  have hg : eLpNorm (fun y => f (t * y)) (ENNReal.ofReal p) volume =
      ENNReal.ofReal t⁻¹ ^ a * eLpNorm f (ENNReal.ofReal p) volume :=
    eLpNorm_comp_mul ENNReal.ofReal_ne_top hf.aestronglyMeasurable ht
  have hgp : MemLp (fun y => f (t * y)) (ENNReal.ofReal p) volume := by
    rw [memLp_iff, hg]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ha ENNReal.ofReal_ne_top)
      hf.eLpNorm_lt_top
  have hL := eLpNorm_comp_mul (p := ENNReal.ofReal p) (a := t⁻¹) ENNReal.ofReal_ne_top
    (g := fun x => ∑ j ∈ Finset.range n,
      dilateConv (haarCorrelation haarSplit) (((2 : ℝ) ^ j)⁻¹) (fun y => f (t * y)) x)
    (Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      (stronglyMeasurable_dilateConv (Or.inr rfl) _ hgm).aestronglyMeasurable) (inv_pos.2 ht)
  simp only [dilateConv_mul (haarCorrelation haarSplit) ht]
  rw [hL, inv_inv]
  have hmul : ENNReal.ofReal t ^ a * ENNReal.ofReal t⁻¹ ^ a = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.ofReal_mul ht.le, mul_inv_cancel₀ ht.ne',
      ENNReal.ofReal_one, ENNReal.one_rpow]
  calc ENNReal.ofReal t ^ a * eLpNorm (fun x => ∑ j ∈ Finset.range n,
        dilateConv (haarCorrelation haarSplit) (((2 : ℝ) ^ j)⁻¹) (fun y => f (t * y)) x)
          (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal t ^ a * (2 * β ^ 2 *
          (ENNReal.ofReal t⁻¹ ^ a * eLpNorm f (ENNReal.ofReal p) volume)) := by
        rw [← hg]
        gcongr
        exact eLpNorm_sum_dilateConv_one_le hp hβ hgp hgm n
    _ = ENNReal.ofReal t ^ a * ENNReal.ofReal t⁻¹ ^ a *
          (2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume) := by ring
    _ = 2 * β ^ 2 * eLpNorm f (ENNReal.ofReal p) volume := by rw [hmul, one_mul]

end VectorValuedHarmonicAnalysis
