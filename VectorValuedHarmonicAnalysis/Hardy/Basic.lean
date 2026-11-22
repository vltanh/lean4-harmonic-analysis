module

public import VectorValuedHarmonicAnalysis.LittlewoodPaley.Circle
public import BanachProbability.Schatten.Block
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Matrix-valued Hardy functions on the circle

For `f : 𝕋 → M_{m×n} (ℂ)`, `matFourierCoeff f k` is the matrix of the `k`-th Fourier coefficients of
the entries. `f` is in the Hardy class `H²` when its entries are in `L² (𝕋)` and its Fourier
coefficients of negative order vanish (`IsHardyTwo f`; in finite dimension this is the closure in
`L²` of the analytic polynomials, F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and
Paley inequalities*, Ark. Mat. 29 (1991), p. 244).

* `matFourierCoeff_mul`: for `g, h ∈ H²`, `(g h)^ (k) = Σ_{0 ≤ q ≤ k} ĝ (q) ĥ (k − q)`.
* `ae_eq_const_of_fourierCoeff_eq_zero`: an integrable function whose Fourier coefficients of order
  `≠ 0` vanish is constant almost everywhere.
-/

@[expose] public section

open MeasureTheory AddCircle BanachProbability
open scoped ENNReal Matrix ComplexConjugate

namespace VectorValuedHarmonicAnalysis

variable {l m n : Type*}

/-- The `k`-th Fourier coefficient of a matrix-valued function, entry by entry. -/
noncomputable def matFourierCoeff (f : UnitAddCircle → Matrix m n ℂ) (k : ℤ) : Matrix m n ℂ :=
  Matrix.of fun i j => fourierCoeff (fun t => f t i j) k

/-- The matrix-valued Hardy class `H²`: entries in `L²`, vanishing Fourier coefficients of negative
order. -/
def IsHardyTwo (f : UnitAddCircle → Matrix m n ℂ) : Prop :=
  (∀ i j, MemLp (fun t => f t i j) 2 haarAddCircle) ∧ ∀ k : ℤ, k < 0 → matFourierCoeff f k = 0

/-- An integrable function with vanishing Fourier coefficients has zero integral against every
continuous function. -/
private theorem integral_continuousMap_mul_eq_zero {g : UnitAddCircle → ℂ}
    (hg : Integrable g haarAddCircle) (h : ∀ k : ℤ, fourierCoeff g k = 0)
    (φ : C(UnitAddCircle, ℂ)) : ∫ t, φ t * g t ∂haarAddCircle = 0 := by
  have hint (ψ : C(UnitAddCircle, ℂ)) : Integrable (fun t => ψ t * g t) haarAddCircle :=
    hg.bdd_mul (c := ‖ψ‖) ψ.continuous.aestronglyMeasurable (ae_of_all _ ψ.norm_coe_le_norm)
  let L : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ∫ t, ψ t * g t ∂haarAddCircle
      map_add' := fun ψ₁ ψ₂ => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint ψ₁) (hint ψ₂)
      map_smul' := fun c ψ => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  let L' : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
    L.mkContinuous (∫ t, ‖g t‖ ∂haarAddCircle) fun ψ => by
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [mul_comm, ← integral_const_mul]
      refine integral_mono (hint ψ).norm (hg.norm.const_mul _) fun t => ?_
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right (ψ.norm_coe_le_norm t) (norm_nonneg _)
  have hle : (Submodule.span ℂ (Set.range (fourier (T := 1)))).topologicalClosure ≤
      LinearMap.ker (L' : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ L'.isClosed_ker
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have := h (-k)
    simp only [fourierCoeff, neg_neg, smul_eq_mul] at this
    exact this
  rw [span_fourier_closure_eq_top] at hle
  exact hle (Submodule.mem_top (x := φ))

/-- An integrable function with vanishing Fourier coefficients vanishes almost everywhere. -/
private theorem ae_eq_zero_of_fourierCoeff_eq_zero {g : UnitAddCircle → ℂ}
    (hg : Integrable g haarAddCircle) (h : ∀ k : ℤ, fourierCoeff g k = 0) :
    g =ᵐ[haarAddCircle] 0 := by
  refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hg fun F hF => ?_
  have hlim := HasOuterApproxClosed.tendsto_apprSeq hF
  rw [tendsto_pi_nhds] at hlim
  have key : Filter.Tendsto (fun N : ℕ => ∫ t, ((hF.apprSeq N t : ℝ) : ℂ) * g t ∂haarAddCircle)
      Filter.atTop (nhds (∫ t, F.indicator g t ∂haarAddCircle)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ‖g t‖) (fun N => ?_) hg.norm
      (fun N => ae_of_all _ fun t => ?_) (ae_of_all _ fun t => ?_)
    · refine Continuous.aestronglyMeasurable ?_ |>.mul hg.aestronglyMeasurable
      exact Complex.continuous_ofReal.comp
        (NNReal.continuous_coe.comp (hF.apprSeq N).continuous)
    · have : (hF.apprSeq N t : ℝ) ≤ 1 := HasOuterApproxClosed.apprSeq_apply_le_one hF N t
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) this
    · have h1 : Filter.Tendsto (fun N => ((hF.apprSeq N t : ℝ) : ℂ)) Filter.atTop
          (nhds (((F.indicator (fun _ => (1 : NNReal)) t : NNReal) : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp
          ((NNReal.continuous_coe.tendsto _).comp (hlim t))
      have h2 := h1.mul_const (g t)
      convert h2 using 2
      by_cases ht : t ∈ F <;> simp [ht]
  rw [← integral_indicator hF.measurableSet]
  refine tendsto_nhds_unique key ?_
  have : ∀ N, ∫ t, ((hF.apprSeq N t : ℝ) : ℂ) * g t ∂haarAddCircle = 0 := fun N =>
    integral_continuousMap_mul_eq_zero hg h
      ⟨fun t => ((hF.apprSeq N t : ℝ) : ℂ), Complex.continuous_ofReal.comp
        (NNReal.continuous_coe.comp (hF.apprSeq N).continuous)⟩
  simp only [this]
  exact tendsto_const_nhds

theorem ae_eq_const_of_fourierCoeff_eq_zero {g : UnitAddCircle → ℂ}
    (hg : Integrable g haarAddCircle) (h : ∀ k : ℤ, k ≠ 0 → fourierCoeff g k = 0) :
    g =ᵐ[haarAddCircle] fun _ => fourierCoeff g 0 := by
  have hc (z : ℂ) (k : ℤ) :
      fourierCoeff (fun _ : UnitAddCircle => z) k = z * (Pi.single 0 1 : ℤ → ℂ) k := by
    have h1 := congrFun (fourierCoeff_fourier (T := 1) 0) k
    have h2 := fourierCoeff.const_mul (T := 1) (fourier 0) z k
    simpa [h1] using h2
  have h0 := ae_eq_zero_of_fourierCoeff_eq_zero
    (g := g + fun _ => -fourierCoeff g 0) (hg.add (integrable_const _)) fun k => by
      rw [fourierCoeff.add hg (integrable_const _), Pi.add_apply, hc]
      by_cases hk : k = 0
      · simp [hk]
      · simp [hk, h k hk]
  filter_upwards [h0] with t ht
  simpa [← sub_eq_add_neg, sub_eq_zero] using ht

/-- The entries of a trigonometric polynomial are trigonometric polynomials. -/
private theorem trigPoly_apply (c : ℤ →₀ Matrix m n ℂ) (t : UnitAddCircle) (i : m) (j : n) :
    trigPoly c t i j = ∑ k ∈ c.support, fourier k t * c k i j := by
  simp [trigPoly, Finsupp.sum, Matrix.sum_apply]

private theorem integrable_const_mul_fourier (z : ℂ) (k : ℤ) :
    Integrable (fun t : UnitAddCircle => fourier k t * z) haarAddCircle :=
  ((fourier k).continuous.mul continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem matFourierCoeff_trigPoly (c : ℤ →₀ Matrix m n ℂ) (k : ℤ) :
    matFourierCoeff (trigPoly c) k = c k := by
  ext i j
  have h : (fun t => trigPoly c t i j) =
      ∑ q ∈ c.support, fun t : UnitAddCircle => c q i j * fourier q t := by
    ext t
    simp [trigPoly_apply, mul_comm]
  have hint (q : ℤ) : Integrable (fun t : UnitAddCircle => c q i j * fourier q t)
      haarAddCircle := by
    simpa [mul_comm] using integrable_const_mul_fourier (c q i j) q
  rw [matFourierCoeff, Matrix.of_apply, h, fourierCoeff.sum _ _ fun q _ => hint q,
    Finset.sum_apply]
  simp only [fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [Finsupp.notMem_support_iff.1 hk, Matrix.zero_apply]

theorem isHardyTwo_trigPoly {c : ℤ →₀ Matrix m n ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k) :
    IsHardyTwo (trigPoly c) := by
  refine ⟨fun i j => ?_, fun k hk => ?_⟩
  · have : (fun t => trigPoly c t i j) =
        fun t : UnitAddCircle => ∑ q ∈ c.support, fourier q t * c q i j := by
      ext t
      exact trigPoly_apply c t i j
    rw [this]
    exact (continuous_finsetSum _ fun q _ =>
      (fourier q).continuous.mul continuous_const).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · rw [matFourierCoeff_trigPoly]
    by_contra hne
    exact absurd (hc k (Finsupp.mem_support_iff.2 hne)) (not_le.2 hk)

/-- The Fourier coefficients of a product of two `L²` functions: `(u v)^ (k) = Σ_q û (k − q) v̂ (q)`
(Parseval's identity). -/
private theorem hasSum_fourierCoeff_mul {u v : UnitAddCircle → ℂ} (hu : MemLp u 2 haarAddCircle)
    (hv : MemLp v 2 haarAddCircle) (k : ℤ) :
    HasSum (fun q : ℤ => fourierCoeff u (k - q) * fourierCoeff v q)
      (fourierCoeff (fun t => u t * v t) k) := by
  have hw : MemLp (fun t => conj (u t) * fourier k t) 2 haarAddCircle := by
    have h1 : MemLp (fun t => conj (u t)) 2 haarAddCircle := hu.star
    refine h1.of_le (h1.aestronglyMeasurable.mul (fourier k).continuous.aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have key := fourierBasis.hasSum_inner_mul_inner hw.toLp hv.toLp
  have e1 (q : ℤ) : inner ℂ hw.toLp (fourierBasis q) = fourierCoeff u (k - q) := by
    rw [coe_fourierBasis, L2.inner_def, fourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [hw.coeFn_toLp, coeFn_fourierLp (T := 1) 2 q] with t h1 h2
    rw [h1, h2, RCLike.inner_apply', neg_sub, sub_eq_add_neg, fourier_add, fourier_neg]
    simp only [map_mul, Complex.conj_conj, smul_eq_mul]
    ring
  have e2 (q : ℤ) : inner ℂ (fourierBasis q) hv.toLp = fourierCoeff v q := by
    rw [← fourierBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_congr_ae hv.coeFn_toLp]
  have e3 : inner ℂ hw.toLp hv.toLp = fourierCoeff (fun t => u t * v t) k := by
    rw [L2.inner_def, fourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [hw.coeFn_toLp, hv.coeFn_toLp] with t h1 h2
    rw [h1, h2, RCLike.inner_apply', fourier_neg]
    simp only [map_mul, Complex.conj_conj, smul_eq_mul]
    ring
  simpa only [e1, e2, e3] using key

/-- The Fourier coefficients of a matrix product are the sums of those of the products of the
entries. -/
private theorem matFourierCoeff_mul_apply [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {h : UnitAddCircle → Matrix m n ℂ} (hg : ∀ i j, MemLp (fun t => g t i j) 2 haarAddCircle)
    (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle) (k : ℤ) (i : l) (j : n) :
    matFourierCoeff (fun t => g t * h t) k i j =
      ∑ o, fourierCoeff (fun t => g t i o * h t o j) k := by
  have e : (fun t => (g t * h t) i j) = ∑ o, fun t => g t i o * h t o j := by
    ext t
    simp [Matrix.mul_apply]
  rw [matFourierCoeff, Matrix.of_apply, e, fourierCoeff.sum, Finset.sum_apply]
  exact fun o _ => (hg i o).integrable_mul (hh o j)

/-- The Fourier coefficients of a product of `H²` functions. -/
theorem matFourierCoeff_mul [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {h : UnitAddCircle → Matrix m n ℂ} (hg : IsHardyTwo g) (hh : IsHardyTwo h) (k : ℕ) :
    matFourierCoeff (fun t => g t * h t) k =
      ∑ q ∈ Finset.range (k + 1), matFourierCoeff g q * matFourierCoeff h ((k : ℤ) - q) := by
  ext i j
  rw [matFourierCoeff_mul_apply hg.1 hh.1, Matrix.sum_apply]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hg0 (q : ℤ) (hq : q < 0) : fourierCoeff (fun t => g t i o) q = 0 :=
    congrFun (congrFun (hg.2 q hq) i) o
  have hh0 (q : ℤ) (hq : q < 0) : fourierCoeff (fun t => h t o j) q = 0 :=
    congrFun (congrFun (hh.2 q hq) o) j
  have key := hasSum_fourierCoeff_mul (hh.1 o j) (hg.1 i o) (k : ℤ)
  have hfin : ∀ q ∉ (Finset.range (k + 1)).map Nat.castEmbedding,
      fourierCoeff (fun t => h t o j) ((k : ℤ) - q) * fourierCoeff (fun t => g t i o) q = 0 := by
    intro q hq
    rcases lt_or_ge q 0 with hq0 | hq0
    · rw [hg0 q hq0, mul_zero]
    · rw [hh0 _ ?_, zero_mul]
      by_contra hlt
      refine hq (Finset.mem_map.2 ⟨q.toNat, ?_, ?_⟩)
      · rw [Finset.mem_range]
        omega
      · simp [hq0]
  have := key.unique (hasSum_sum_of_ne_finset_zero hfin)
  simp only [mul_comm (fourierCoeff (fun t => h t o j) _)] at this
  simp only [mul_comm (h _ o j)] at this
  rw [this, Finset.sum_map]
  rfl

/-- The partial sums of the Fourier series of an `L²` function converge to it in `L²`. -/
private theorem tendsto_eLpNorm_partialSum {u : UnitAddCircle → ℂ} (hu : MemLp u 2 haarAddCircle) :
    Filter.Tendsto (fun N : ℕ => eLpNorm (fun t =>
      ∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t * fourierCoeff u k - u t) 2 haarAddCircle)
      Filter.atTop (nhds 0) := by
  have h1 := (hasSum_fourier_series_L2 hu.toLp).comp Finset.tendsto_Icc_neg
  have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hu).1 h1
  refine h2.congr fun N => eLpNorm_congr_ae ?_
  have h3 : ∀ᵐ t ∂haarAddCircle, ∀ k : ℤ, fourierLp (T := 1) 2 k t = fourier k t :=
    ae_all_iff.2 fun k => coeFn_fourierLp 2 k
  have h4 := Lp.coeFn_fun_finsetSum (μ := haarAddCircle) (Finset.Icc (-N : ℤ) N)
    fun k => fourierCoeff hu.toLp k • fourierLp (T := 1) 2 k
  have h5 : ∀ᵐ t ∂haarAddCircle, ∀ k : ℤ, (fourierCoeff hu.toLp k • fourierLp (T := 1) 2 k :
      Lp ℂ 2 (haarAddCircle (T := 1))) t = fourierCoeff hu.toLp k • fourierLp (T := 1) 2 k t :=
    ae_all_iff.2 fun k => Lp.coeFn_smul _ _
  filter_upwards [h3, h4, h5] with t h3 h4 h5
  simp only [Function.comp_apply, Pi.sub_apply, h4, h5, h3, smul_eq_mul]
  simp only [fourierCoeff_congr_ae hu.coeFn_toLp, mul_comm]

section Norm

variable [Fintype m] [Fintype n] [DecidableEq n]

/-- The Schatten norm of a finite sum. -/
private theorem complexSchattenNorm_sum_le {q : ℝ≥0∞} (hq : 1 ≤ q) {ι : Type*} (s : Finset ι)
    (A : ι → Matrix m n ℂ) :
    complexSchattenNorm q (∑ i ∈ s, A i) ≤ ∑ i ∈ s, complexSchattenNorm q (A i) :=
  Finset.le_sum_of_subadditive _
    ((complexSchattenNorm_eq_zero_iff (zero_lt_one.trans_le hq).ne').2 rfl).le
    (complexSchattenNorm_add_le hq) _ _

/-- In finite dimension the Schatten norm is at most a multiple of the `ℓ¹` norm of the entries. -/
private theorem exists_complexSchattenNorm_le_sum {q : ℝ≥0∞} (hq : 1 ≤ q) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ A : Matrix m n ℂ, complexSchattenNorm q A ≤ C * ∑ p : m × n, ‖A p.1 p.2‖ := by
  classical
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  refine ⟨∑ p : m × n, complexSchattenNorm q (Matrix.single p.1 p.2 (1 : ℂ)),
    Finset.sum_nonneg fun p _ => complexSchattenNorm_nonneg q _, fun A => ?_⟩
  have hA : A = ∑ p : m × n, A p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A, ← Fintype.sum_prod_type'
      (f := fun i j => Matrix.single i j (A i j))]
    simp
  calc complexSchattenNorm q A
      = complexSchattenNorm q (∑ p : m × n, A p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ)) := by
        rw [← hA]
    _ ≤ ∑ p : m × n, complexSchattenNorm q (A p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ)) :=
        complexSchattenNorm_sum_le hq _ _
    _ = ∑ p : m × n, complexSchattenNorm q (Matrix.single p.1 p.2 (1 : ℂ)) * ‖A p.1 p.2‖ := by
        simp only [complexSchattenNorm_smul hq0, mul_comm]
    _ ≤ ∑ p : m × n, complexSchattenNorm q (Matrix.single p.1 p.2 (1 : ℂ)) *
          ∑ p : m × n, ‖A p.1 p.2‖ :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun p : m × n => ‖A p.1 p.2‖)
            (fun _ _ => norm_nonneg _) hp) (complexSchattenNorm_nonneg q _)
    _ = _ := by rw [Finset.sum_mul]

/-- The reverse triangle inequality for the Schatten norm. -/
private theorem abs_complexSchattenNorm_sub_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n ℂ) :
    |complexSchattenNorm q A - complexSchattenNorm q B| ≤ complexSchattenNorm q (A - B) := by
  have hneg : complexSchattenNorm q (B - A) = complexSchattenNorm q (A - B) := by
    rw [← neg_sub A B, ← neg_one_smul ℂ, complexSchattenNorm_smul (zero_lt_one.trans_le hq).ne']
    simp
  have h1 := complexSchattenNorm_add_le hq (A - B) B
  have h2 := complexSchattenNorm_add_le hq (B - A) A
  rw [sub_add_cancel] at h1 h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- A matrix-valued function with a.e. strongly measurable entries is a.e. strongly measurable. -/
private theorem aestronglyMeasurable_of_entries [Finite m] [Finite n]
    {h : UnitAddCircle → Matrix m n ℂ}
    (hh : ∀ i j, AEStronglyMeasurable (fun t => h t i j) haarAddCircle) :
    AEStronglyMeasurable h haarAddCircle := by
  classical
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  have hA : h = fun t => ∑ i, ∑ j, h t i j • Matrix.single i j (1 : ℂ) := by
    ext1 t
    conv_lhs => rw [Matrix.matrix_eq_sum_single (h t)]
    simp
  rw [hA]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hh i j).smul_const _

/-- The Schatten norm of a matrix-valued function with entries in `L²` is in `L²`. -/
private theorem memLp_complexSchattenNorm {q : ℝ≥0∞} (hq : 1 ≤ q)
    {h : UnitAddCircle → Matrix m n ℂ} (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle) :
    MemLp (fun t => complexSchattenNorm q (h t)) 2 haarAddCircle := by
  obtain ⟨C, hC, hle⟩ := exists_complexSchattenNorm_le_sum (m := m) (n := n) hq
  have hsum : MemLp (fun t => C * ∑ p : m × n, ‖h t p.1 p.2‖) 2 haarAddCircle := by
    refine MemLp.const_mul ?_ C
    exact memLp_finsetSum _ fun p _ => (hh p.1 p.2).norm
  have hmeas : AEStronglyMeasurable (fun t => complexSchattenNorm q (h t)) haarAddCircle :=
    (continuous_complexSchattenNorm hq).comp_aestronglyMeasurable
      (aestronglyMeasurable_of_entries fun i j => (hh i j).aestronglyMeasurable)
  refine hsum.of_le hmeas (ae_of_all _ fun t => ?_)
  rw [Real.norm_of_nonneg (complexSchattenNorm_nonneg q _)]
  exact (hle (h t)).trans (Real.le_norm_self _)

/-- If the entries of `f_N` converge to those of `h` in `L²`, so do the Schatten norms. -/
private theorem tendsto_eLpNorm_complexSchattenNorm {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : ℕ → UnitAddCircle → Matrix m n ℂ} {h : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ N i j, MemLp (fun t => f N t i j) 2 haarAddCircle)
    (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle)
    (hlim : ∀ i j, Filter.Tendsto (fun N => eLpNorm (fun t => f N t i j - h t i j) 2 haarAddCircle)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => eLpNorm ((fun t => complexSchattenNorm q (f N t)) -
      fun t => complexSchattenNorm q (h t)) 2 haarAddCircle) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hle⟩ := exists_complexSchattenNorm_le_sum (m := m) (n := n) hq
  have hbound (N : ℕ) : eLpNorm ((fun t => complexSchattenNorm q (f N t)) -
      fun t => complexSchattenNorm q (h t)) 2 haarAddCircle ≤
      ENNReal.ofReal C * ∑ p : m × n,
        eLpNorm (fun t => f N t p.1 p.2 - h t p.1 p.2) 2 haarAddCircle := by
    have h1 : eLpNorm ((fun t => complexSchattenNorm q (f N t)) -
        fun t => complexSchattenNorm q (h t)) 2 haarAddCircle ≤ ENNReal.ofReal C *
          eLpNorm (∑ p : m × n, fun t => ‖f N t p.1 p.2 - h t p.1 p.2‖) 2 haarAddCircle := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((memLp_complexSchattenNorm hq (hf N)).sub
        (memLp_complexSchattenNorm hq hh)).aestronglyMeasurable (ae_of_all _ fun t => ?_) 2
      rw [Pi.sub_apply, Real.norm_eq_abs, Finset.sum_apply]
      refine (abs_complexSchattenNorm_sub_le hq _ _).trans ((hle _).trans ?_)
      simp only [Matrix.sub_apply]
      exact mul_le_mul_of_nonneg_left (Real.le_norm_self _) hC
    refine h1.trans (mul_le_mul_right ((eLpNorm_sum_le one_le_two).trans ?_) _)
    refine Finset.sum_le_sum fun p _ => ?_
    exact (eLpNorm_norm (fun t => f N t p.1 p.2 - h t p.1 p.2)
      ((hf N p.1 p.2).sub (hh p.1 p.2)).aestronglyMeasurable).le
  have hzero : Filter.Tendsto (fun N => ENNReal.ofReal C * ∑ p : m × n,
      eLpNorm (fun t => f N t p.1 p.2 - h t p.1 p.2) 2 haarAddCircle) Filter.atTop (nhds 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
      (tendsto_finsetSum Finset.univ fun (p : m × n) _ => hlim p.1 p.2)
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun _ => zero_le) hbound

/-- Convergence in `L²` implies the convergence of the integrals of the squares. -/
private theorem tendsto_integral_sq {a : ℕ → UnitAddCircle → ℝ} {b : UnitAddCircle → ℝ}
    (ha : ∀ N, MemLp (a N) 2 haarAddCircle) (hb : MemLp b 2 haarAddCircle)
    (hlim : Filter.Tendsto (fun N => eLpNorm (a N - b) 2 haarAddCircle) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => ∫ t, a N t ^ 2 ∂haarAddCircle) Filter.atTop
      (nhds (∫ t, b t ^ 2 ∂haarAddCircle)) := by
  have hnorm {u : UnitAddCircle → ℝ} (hu : MemLp u 2 haarAddCircle) :
      ‖hu.toLp‖ ^ 2 = ∫ t, u t ^ 2 ∂haarAddCircle := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp] with t ht
    rw [ht, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' a ha b hb).2 hlim
  simpa only [hnorm] using (h1.norm).pow 2

end Norm

/-- The partial sums `Σ_{|k| ≤ N} ĥ (k) e_k` converge to `h` in `L² (𝕋; S_q)`: the norms converge.
-/
theorem tendsto_integral_norm_sq_partialSum [Fintype m] [Fintype n] [DecidableEq n] {q : ℝ≥0∞}
    (hq : 1 ≤ q) {h : UnitAddCircle → Matrix m n ℂ}
    (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle) :
    Filter.Tendsto (fun N : ℕ => ∫ t : UnitAddCircle, complexSchattenNorm q
        (∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t • matFourierCoeff h k) ^ 2 ∂haarAddCircle)
      Filter.atTop
      (nhds (∫ t : UnitAddCircle, complexSchattenNorm q (h t) ^ 2 ∂haarAddCircle)) := by
  have happ (N : ℕ) (t : UnitAddCircle) (i : m) (j : n) :
      (∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t • matFourierCoeff h k) i j =
        ∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t * fourierCoeff (fun t => h t i j) k := by
    simp [Matrix.sum_apply, matFourierCoeff]
  have hmem (N : ℕ) (i : m) (j : n) : MemLp (fun t : UnitAddCircle =>
      (∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t • matFourierCoeff h k) i j) 2 haarAddCircle := by
    simp only [happ]
    exact (continuous_finsetSum _ fun q _ =>
      (fourier q).continuous.mul continuous_const).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  refine tendsto_integral_sq (fun N => memLp_complexSchattenNorm hq (hmem N))
    (memLp_complexSchattenNorm hq hh)
    (tendsto_eLpNorm_complexSchattenNorm hq hmem hh fun i j => ?_)
  simp only [happ]
  exact tendsto_eLpNorm_partialSum (hh i j)

end VectorValuedHarmonicAnalysis
