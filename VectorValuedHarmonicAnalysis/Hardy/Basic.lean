module

public import VectorValuedHarmonicAnalysis.LittlewoodPaley.Circle
public import BanachProbability.Schatten.Block
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Matrix-valued Hardy functions on the circle

For `f : 𝕋 → M_{m×n} (ℂ)`, `matFourierCoeff f k` is the matrix of the `k`-th Fourier coefficients of
the entries. `f` is in the Hardy class `H²` (`IsHardyTwo f`) when its entries are in `L² (𝕋)` and
its Fourier coefficients of negative order vanish. (F. Lust-Piquard and G. Pisier, *Non commutative
Khintchine and Paley inequalities*, Ark. Mat. 29 (1991), p. 244, define `H²` as the closure in `L²`
of the analytic polynomials; the equivalence of the two definitions is not used here.)

* `matFourierCoeff_mul`: for `g, h ∈ H²` and `k ≥ 0`, `(g h)^ (k) = Σ_{0 ≤ q ≤ k} ĝ (q) ĥ (k − q)`;
  `matFourierCoeff_mul_of_neg`: for `k < 0`, `(g h)^ (k) = 0`.
* `ae_eq_const_of_fourierCoeff_eq_zero`: an integrable function whose Fourier coefficients of order
  `≠ 0` vanish is constant almost everywhere.
* `tendsto_integral_norm_sq_partialSum`: `∫ ‖S_N h‖_{S_q}² → ∫ ‖h‖_{S_q}²` for the partial sums
  `S_N h` of the Fourier series of `h`.

A matrix-valued function with entries in `L^r (𝕋)` is in `L^r (𝕋; S_q)` (`memLp_ofMatrix`,
`memLp_complexSchattenNorm`), where `S_q` is `ComplexSchattenSpace q m n`, the matrices with the
Schatten norm.
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

/-! ### Constants and continuous functions -/

/-- The Fourier coefficients of a constant function. -/
theorem fourierCoeff_const (z : ℂ) (k : ℤ) :
    fourierCoeff (fun _ : UnitAddCircle => z) k = if k = 0 then z else 0 := by
  have h1 := congrFun (fourierCoeff_fourier (T := 1) 0) k
  have h2 := fourierCoeff.const_mul (T := 1) (fourier 0) z k
  simpa [h1, Pi.single_apply] using h2

/-- Functions that agree almost everywhere have the same Fourier coefficients. -/
theorem matFourierCoeff_congr_ae {f g : UnitAddCircle → Matrix m n ℂ}
    (h : ∀ᵐ t ∂haarAddCircle, f t = g t) (k : ℤ) : matFourierCoeff f k = matFourierCoeff g k := by
  ext i j
  refine congrFun (fourierCoeff_congr_ae ?_) k
  filter_upwards [h] with t ht
  rw [ht]

/-- The entries of a continuous matrix-valued function are in `L²`. -/
theorem memLp_entry_of_continuous {f : UnitAddCircle → Matrix m n ℂ} (hf : Continuous f) (i : m)
    (j : n) : MemLp (fun t => f t i j) 2 haarAddCircle :=
  (hf.matrix_elem i j).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### Functions with vanishing Fourier coefficients -/

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

/-- An integrable function whose Fourier coefficients of order `≠ 0` vanish is constant almost
everywhere. -/
theorem ae_eq_const_of_fourierCoeff_eq_zero {g : UnitAddCircle → ℂ}
    (hg : Integrable g haarAddCircle) (h : ∀ k : ℤ, k ≠ 0 → fourierCoeff g k = 0) :
    g =ᵐ[haarAddCircle] fun _ => fourierCoeff g 0 := by
  have h0 := ae_eq_zero_of_fourierCoeff_eq_zero
    (g := g + fun _ => -fourierCoeff g 0) (hg.add (integrable_const _)) fun k => by
      rw [fourierCoeff.add hg (integrable_const _), Pi.add_apply, fourierCoeff_const]
      by_cases hk : k = 0
      · simp [hk]
      · simp [hk, h k hk]
  filter_upwards [h0] with t ht
  simpa [← sub_eq_add_neg, sub_eq_zero] using ht

/-! ### Trigonometric polynomials -/

/-- A trigonometric polynomial with matrix coefficients is continuous. (`continuous_trigPoly` is the
same for coefficients in a normed space.) -/
theorem continuous_trigPoly_matrix (c : ℤ →₀ Matrix m n ℂ) : Continuous (trigPoly c) :=
  continuous_finsetSum _ fun k _ => (fourier k).continuous.smul continuous_const

/-- The entries of a trigonometric polynomial are trigonometric polynomials. -/
private theorem trigPoly_apply (c : ℤ →₀ Matrix m n ℂ) (t : UnitAddCircle) (i : m) (j : n) :
    trigPoly c t i j = ∑ k ∈ c.support, c k i j * fourier k t := by
  simp [trigPoly, Finsupp.sum, Matrix.sum_apply, mul_comm]

/-- The Fourier coefficients of a trigonometric polynomial are its coefficients. -/
theorem matFourierCoeff_trigPoly (c : ℤ →₀ Matrix m n ℂ) (k : ℤ) :
    matFourierCoeff (trigPoly c) k = c k := by
  ext i j
  have h : (fun t => trigPoly c t i j) =
      ∑ q ∈ c.support, fun t : UnitAddCircle => c q i j * fourier q t := by
    ext t
    simp [trigPoly_apply]
  have hint (q : ℤ) : Integrable (fun t : UnitAddCircle => c q i j * fourier q t)
      haarAddCircle :=
    (continuous_const.mul (fourier q).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [matFourierCoeff, Matrix.of_apply, h, fourierCoeff.sum _ _ fun q _ => hint q,
    Finset.sum_apply]
  simp only [fourierCoeff.const_mul, fourierCoeff_fourier, Pi.single_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [Finsupp.notMem_support_iff.1 hk, Matrix.zero_apply]

/-- The analytic polynomials are in `H²`. -/
theorem isHardyTwo_trigPoly {c : ℤ →₀ Matrix m n ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k) :
    IsHardyTwo (trigPoly c) := by
  refine ⟨memLp_entry_of_continuous (continuous_trigPoly_matrix c), fun k hk => ?_⟩
  rw [matFourierCoeff_trigPoly]
  by_contra hne
  exact absurd (hc k (Finsupp.mem_support_iff.2 hne)) (not_le.2 hk)

/-! ### Products -/

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
    rw [norm_mul, norm_fourier_apply_eq_one, mul_one]
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

/-- `(g h)^ (k) = Σ_q ĝ (q) ĥ (k − q)` for matrix-valued functions with entries in `L²`. -/
private theorem hasSum_matFourierCoeff_mul [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {h : UnitAddCircle → Matrix m n ℂ} (hg : ∀ i j, MemLp (fun t => g t i j) 2 haarAddCircle)
    (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle) (k : ℤ) :
    HasSum (fun q : ℤ => matFourierCoeff g q * matFourierCoeff h (k - q))
      (matFourierCoeff (fun t => g t * h t) k) := by
  have key (i : l) (j : n) :
      HasSum (fun q : ℤ => (matFourierCoeff g q * matFourierCoeff h (k - q)) i j)
        (matFourierCoeff (fun t => g t * h t) k i j) := by
    have e : (fun t => (g t * h t) i j) = ∑ o, fun t => h t o j * g t i o := by
      ext t
      simp [Matrix.mul_apply, mul_comm]
    have hint (o : m) : Integrable (fun t => h t o j * g t i o) haarAddCircle :=
      (hh o j).integrable_mul (hg i o)
    rw [matFourierCoeff, Matrix.of_apply, e, fourierCoeff.sum _ _ fun o _ => hint o,
      Finset.sum_apply]
    simp only [Matrix.mul_apply, mul_comm (matFourierCoeff g _ i _)]
    exact hasSum_sum fun o _ => hasSum_fourierCoeff_mul (hh o j) (hg i o) k
  exact Pi.hasSum.2 fun i => Pi.hasSum.2 fun j => key i j

/-- The Fourier coefficients of order `k ≥ 0` of a product of `H²` functions. -/
theorem matFourierCoeff_mul [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {h : UnitAddCircle → Matrix m n ℂ} (hg : IsHardyTwo g) (hh : IsHardyTwo h) (k : ℕ) :
    matFourierCoeff (fun t => g t * h t) k =
      ∑ q ∈ Finset.range (k + 1), matFourierCoeff g q * matFourierCoeff h ((k : ℤ) - q) := by
  have hfin : ∀ q ∉ (Finset.range (k + 1)).map Nat.castEmbedding,
      matFourierCoeff g q * matFourierCoeff h ((k : ℤ) - q) = 0 := by
    intro q hq
    rcases lt_or_ge q 0 with hq0 | hq0
    · rw [hg.2 q hq0, Matrix.zero_mul]
    · rw [hh.2 _ ?_, Matrix.mul_zero]
      by_contra hlt
      refine hq (Finset.mem_map.2 ⟨q.toNat, ?_, ?_⟩)
      · rw [Finset.mem_range]
        omega
      · simp [hq0]
  rw [(hasSum_matFourierCoeff_mul hg.1 hh.1 k).unique (hasSum_sum_of_ne_finset_zero hfin),
    Finset.sum_map]
  rfl

/-- The Fourier coefficients of negative order of a product of `H²` functions vanish. -/
theorem matFourierCoeff_mul_of_neg [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {h : UnitAddCircle → Matrix m n ℂ} (hg : IsHardyTwo g) (hh : IsHardyTwo h) {k : ℤ}
    (hk : k < 0) : matFourierCoeff (fun t => g t * h t) k = 0 := by
  have hzero (q : ℤ) : matFourierCoeff g q * matFourierCoeff h (k - q) = 0 := by
    rcases lt_or_ge q 0 with hq | hq
    · rw [hg.2 q hq, Matrix.zero_mul]
    · rw [hh.2 _ (by omega), Matrix.mul_zero]
  have key := hasSum_matFourierCoeff_mul hg.1 hh.1 k
  simp only [hzero] at key
  exact key.unique hasSum_zero

/-! ### Functions with values in the Schatten spaces -/

section Schatten

variable {q : ℝ≥0∞}

/-- `ofMatrix` commutes with the multiplication by real scalars. -/
theorem ofMatrix_real_smul (r : ℝ) (A : Matrix m n ℂ) :
    (ComplexSchattenSpace.ofMatrix (r • A) : ComplexSchattenSpace q m n) =
      r • ComplexSchattenSpace.ofMatrix A := by
  rw [← Complex.coe_smul, map_smul, Complex.coe_smul]

/-- `ofMatrix` of a real linear combination. -/
theorem ofMatrix_sum_smul {ι : Type*} (s : Finset ι) (r : ι → ℝ) (B : ι → Matrix m n ℂ) :
    (ComplexSchattenSpace.ofMatrix (∑ k ∈ s, r k • B k) : ComplexSchattenSpace q m n) =
      ∑ k ∈ s, r k • ComplexSchattenSpace.ofMatrix (B k) := by
  simp only [map_sum, ofMatrix_real_smul]

variable [Fintype m] [Fintype n] [DecidableEq n]

/-- A matrix is the sum of the matrix units multiplied by its entries. -/
theorem ofMatrix_eq_sum [DecidableEq m] (A : Matrix m n ℂ) :
    (ComplexSchattenSpace.ofMatrix A : ComplexSchattenSpace q m n) =
      ∑ i, ∑ j, A i j • ComplexSchattenSpace.ofMatrix (Matrix.single i j (1 : ℂ)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- A matrix-valued function with entries in `L^r` is in `L^r (𝕋; S_q)`. -/
theorem memLp_ofMatrix [Fact (1 ≤ q)] {r : ℝ≥0∞} {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, MemLp (fun t => f t i j) r haarAddCircle) :
    MemLp (fun t => (ComplexSchattenSpace.ofMatrix (f t) : ComplexSchattenSpace q m n)) r
      haarAddCircle := by
  classical
  rw [funext fun t => ofMatrix_eq_sum (q := q) (f t)]
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
  exact (ContinuousLinearMap.toSpanSingleton ℂ (ComplexSchattenSpace.ofMatrix
    (Matrix.single i j (1 : ℂ)) : ComplexSchattenSpace q m n)).comp_memLp' (hf i j)

/-- The Schatten norm of a matrix-valued function with entries in `L^r` is in `L^r`. -/
theorem memLp_complexSchattenNorm (hq : 1 ≤ q) {r : ℝ≥0∞} {f : UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ i j, MemLp (fun t => f t i j) r haarAddCircle) :
    MemLp (fun t => complexSchattenNorm q (f t)) r haarAddCircle :=
  have : Fact (1 ≤ q) := ⟨hq⟩
  (memLp_ofMatrix (q := q) hf).norm

/-- If the entries of `f_N` converge to `0` in `L²`, then `f_N → 0` in `L² (𝕋; S_q)`. -/
private theorem tendsto_eLpNorm_ofMatrix [Fact (1 ≤ q)] {f : ℕ → UnitAddCircle → Matrix m n ℂ}
    (hf : ∀ N i j, MemLp (fun t => f N t i j) 2 haarAddCircle)
    (hlim : ∀ i j, Filter.Tendsto (fun N => eLpNorm (fun t => f N t i j) 2 haarAddCircle)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => eLpNorm (fun t =>
      (ComplexSchattenSpace.ofMatrix (f N t) : ComplexSchattenSpace q m n)) 2 haarAddCircle)
      Filter.atTop (nhds 0) := by
  classical
  let E (p : m × n) : ComplexSchattenSpace q m n :=
    ComplexSchattenSpace.ofMatrix (Matrix.single p.1 p.2 (1 : ℂ))
  have hsum : Filter.Tendsto (fun N => ∑ p : m × n, ENNReal.ofReal ‖E p‖ *
      eLpNorm (fun t => f N t p.1 p.2) 2 haarAddCircle) Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ fun (p : m × n) _ =>
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖E p‖) (hlim p.1 p.2)
        (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun N => ?_
  have e : (fun t => (ComplexSchattenSpace.ofMatrix (f N t) : ComplexSchattenSpace q m n)) =
      ∑ p : m × n, fun t => f N t p.1 p.2 • E p := by
    ext1 t
    rw [ofMatrix_eq_sum, Finset.sum_apply, Fintype.sum_prod_type]
  rw [e]
  refine (eLpNorm_sum_le one_le_two).trans (Finset.sum_le_sum fun p _ => ?_)
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hf N p.1 p.2).aestronglyMeasurable.smul_const _)
    (ae_of_all _ fun t => ?_) 2
  rw [norm_smul, mul_comm]

/-- Convergence in `L²` implies the convergence of the integrals of the squares of the norms. -/
private theorem tendsto_integral_norm_sq {X : Type*} [NormedAddCommGroup X]
    {a : ℕ → UnitAddCircle → X} {b : UnitAddCircle → X} (ha : ∀ N, MemLp (a N) 2 haarAddCircle)
    (hb : MemLp b 2 haarAddCircle)
    (hlim : Filter.Tendsto (fun N => eLpNorm (a N - b) 2 haarAddCircle) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => ∫ t, ‖a N t‖ ^ 2 ∂haarAddCircle) Filter.atTop
      (nhds (∫ t, ‖b t‖ ^ 2 ∂haarAddCircle)) := by
  have hnorm {u : UnitAddCircle → X} (hu : MemLp u 2 haarAddCircle) :
      ‖hu.toLp‖ ^ 2 = ∫ t, ‖u t‖ ^ 2 ∂haarAddCircle := by
    have h0 : 0 ≤ ∫ t, ‖u t‖ ^ 2 ∂haarAddCircle := integral_nonneg fun t => by positivity
    rw [Lp.norm_toLp, hu.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofNat, ← one_div, ← Real.sqrt_eq_rpow]
    simp only [Real.rpow_ofNat]
    exact Real.sq_sqrt h0
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' a ha b hb).2 hlim
  simpa only [hnorm] using (h1.norm).pow 2

end Schatten

/-! ### The partial sums of the Fourier series -/

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

/-- The partial sums `S_N h = Σ_{|k| ≤ N} ĥ (k) e_k` of the Fourier series of a matrix-valued
function `h` with entries in `L²` satisfy `∫ ‖S_N h‖_{S_q}² → ∫ ‖h‖_{S_q}²`. -/
theorem tendsto_integral_norm_sq_partialSum [Fintype m] [Fintype n] [DecidableEq n] {q : ℝ≥0∞}
    (hq : 1 ≤ q) {h : UnitAddCircle → Matrix m n ℂ}
    (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle) :
    Filter.Tendsto (fun N : ℕ => ∫ t : UnitAddCircle, complexSchattenNorm q
        (∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t • matFourierCoeff h k) ^ 2 ∂haarAddCircle)
      Filter.atTop
      (nhds (∫ t : UnitAddCircle, complexSchattenNorm q (h t) ^ 2 ∂haarAddCircle)) := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  let s (N : ℕ) (t : UnitAddCircle) : Matrix m n ℂ :=
    ∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t • matFourierCoeff h k
  have hs (N : ℕ) (i : m) (j : n) : MemLp (fun t => s N t i j) 2 haarAddCircle :=
    memLp_entry_of_continuous (continuous_finsetSum _ fun k _ =>
      (fourier k).continuous.smul continuous_const) i j
  have hlim (i : m) (j : n) : Filter.Tendsto (fun N => eLpNorm (fun t => (s N t - h t) i j) 2
      haarAddCircle) Filter.atTop (nhds 0) := by
    refine (tendsto_eLpNorm_partialSum (hh i j)).congr fun N => ?_
    congr 1
    ext t
    simp [s, Matrix.sum_apply, matFourierCoeff]
  exact tendsto_integral_norm_sq (fun N => memLp_ofMatrix (q := q) (hs N)) (memLp_ofMatrix hh)
    (tendsto_eLpNorm_ofMatrix (q := q) (fun N i j => (hs N i j).sub (hh i j)) hlim)

end VectorValuedHarmonicAnalysis
