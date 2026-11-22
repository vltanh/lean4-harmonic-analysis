module

public import VectorValuedHarmonicAnalysis.LittlewoodPaley.Circle
public import BanachProbability.Schatten.Block

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
open scoped ENNReal Matrix

namespace VectorValuedHarmonicAnalysis

variable {l m n : Type*}

/-- The `k`-th Fourier coefficient of a matrix-valued function, entry by entry. -/
noncomputable def matFourierCoeff (f : UnitAddCircle → Matrix m n ℂ) (k : ℤ) : Matrix m n ℂ :=
  Matrix.of fun i j => fourierCoeff (fun t => f t i j) k

/-- The matrix-valued Hardy class `H²`: entries in `L²`, vanishing Fourier coefficients of negative
order. -/
def IsHardyTwo (f : UnitAddCircle → Matrix m n ℂ) : Prop :=
  (∀ i j, MemLp (fun t => f t i j) 2 haarAddCircle) ∧ ∀ k : ℤ, k < 0 → matFourierCoeff f k = 0

theorem ae_eq_const_of_fourierCoeff_eq_zero {g : UnitAddCircle → ℂ}
    (hg : Integrable g haarAddCircle) (h : ∀ k : ℤ, k ≠ 0 → fourierCoeff g k = 0) :
    g =ᵐ[haarAddCircle] fun _ => fourierCoeff g 0 := by
  sorry

theorem matFourierCoeff_trigPoly (c : ℤ →₀ Matrix m n ℂ) (k : ℤ) :
    matFourierCoeff (trigPoly c) k = c k := by
  sorry

theorem isHardyTwo_trigPoly {c : ℤ →₀ Matrix m n ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k) :
    IsHardyTwo (trigPoly c) := by
  sorry

/-- The Fourier coefficients of a product of `H²` functions. -/
theorem matFourierCoeff_mul [Fintype m] {g : UnitAddCircle → Matrix l m ℂ}
    {h : UnitAddCircle → Matrix m n ℂ} (hg : IsHardyTwo g) (hh : IsHardyTwo h) (k : ℕ) :
    matFourierCoeff (fun t => g t * h t) k =
      ∑ q ∈ Finset.range (k + 1), matFourierCoeff g q * matFourierCoeff h ((k : ℤ) - q) := by
  sorry

/-- The partial sums `Σ_{|k| ≤ N} ĥ (k) e_k` converge to `h` in `L² (𝕋; S_q)`: the norms converge.
-/
theorem tendsto_integral_norm_sq_partialSum [Fintype m] [Fintype n] [DecidableEq n] {q : ℝ≥0∞}
    (hq : 1 ≤ q) {h : UnitAddCircle → Matrix m n ℂ}
    (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle) :
    Filter.Tendsto (fun N : ℕ => ∫ t : UnitAddCircle, complexSchattenNorm q
        (∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t • matFourierCoeff h k) ^ 2 ∂haarAddCircle)
      Filter.atTop
      (nhds (∫ t : UnitAddCircle, complexSchattenNorm q (h t) ^ 2 ∂haarAddCircle)) := by
  sorry

end VectorValuedHarmonicAnalysis
