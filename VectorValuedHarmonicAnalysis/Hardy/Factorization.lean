module

public import VectorValuedHarmonicAnalysis.Hardy.Basic

/-!
# Szegő and Riesz factorization of matrix-valued functions

* `exists_szego_factorization`: if `a : 𝕋 → M_n (ℂ)` is continuous with positive definite values,
  then `a = Ψ h` almost everywhere, with `Ψ` unitary-valued, `h ∈ H²` and `h⁻¹ ∈ H²` (Szegő
  factorization; here `h` is bounded).
* `exists_riesz_factorization`: an analytic matrix polynomial `f` is a product `f = g h` almost
  everywhere of `g, h ∈ H²`, with `‖g (t)‖_{S_{2p}}² ≤ ‖f (t)‖_{S_p}` and
  `‖h (t)‖_{S_{2p}}² ≤ ‖f (t)‖_{S_p} + δ` for almost every `t` and every `p ≥ 1`.

For `p = 1` the second statement is, up to `δ`, D. Sarason's theorem (1967) that `f ∈ H¹ (C_1)` is a
product `g h` with `‖f‖_{H¹ (C_1)} = ‖g‖_{H² (C_2)} ‖h‖_{H² (C_2)}`; the matrix case goes back to
Helson and Lowdenslager (F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley
inequalities*, Ark. Mat. 29 (1991), pp. 243, 249, 252). The proof is that of T. N. Bekjan and Q. Xu,
*Riesz and Szegő type factorizations for noncommutative Hardy spaces*, J. Operator Theory 62 (2009),
215–231 (arXiv:0705.1947), Theorems 3.1 and 3.4, for the algebra `M = L^∞ (𝕋; M_n)`,
`A = H^∞ (𝕋; M_n)`, `D = M_n`, which is Arveson's argument: project `a` onto the closure of `a A_0`
in `L²`; the difference `y` satisfies `yᴴ y ∈ D`; `Ψ` is the unitary part of `y` and `h = Ψᴴ a`. For
`f` one takes `a = (fᴴ f + δ²)^{1/4}` and `g = f a⁻² · a Ψ`.
-/

@[expose] public section

open MeasureTheory AddCircle BanachProbability
open scoped ENNReal Matrix ComplexOrder

namespace VectorValuedHarmonicAnalysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Szegő factorization** (Bekjan–Xu (2009), Theorem 3.1, matrix case): a continuous positive
definite `a : 𝕋 → M_n (ℂ)` is `Ψ h` with `Ψ` unitary-valued and `h, h⁻¹ ∈ H²`. -/
theorem exists_szego_factorization {a : UnitAddCircle → Matrix n n ℂ} (ha : Continuous a)
    (hpos : ∀ t, (a t).PosDef) :
    ∃ Ψ h : UnitAddCircle → Matrix n n ℂ, (∀ i j, StronglyMeasurable fun t => Ψ t i j) ∧
      (∀ t, Ψ t ∈ Matrix.unitaryGroup n ℂ) ∧ IsHardyTwo h ∧ IsHardyTwo (fun t => (h t)⁻¹) ∧
      ∀ᵐ t ∂haarAddCircle, a t = Ψ t * h t := by
  sorry

/-- **Riesz factorization of matrix polynomials** (Sarason; Bekjan–Xu (2009), Theorem 3.4). -/
theorem exists_riesz_factorization {c : ℤ →₀ Matrix n n ℂ} (hc : ∀ k ∈ c.support, 0 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ g h : UnitAddCircle → Matrix n n ℂ, IsHardyTwo g ∧ IsHardyTwo h ∧
      (∀ᵐ t ∂haarAddCircle, trigPoly c t = g t * h t) ∧
      (∀ᵐ t ∂haarAddCircle, ∀ p : ℝ, 1 ≤ p →
        complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ≤
          complexSchattenNorm (ENNReal.ofReal p) (trigPoly c t)) ∧
      (∀ᵐ t ∂haarAddCircle, ∀ p : ℝ, 1 ≤ p →
        complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ≤
          complexSchattenNorm (ENNReal.ofReal p) (trigPoly c t) + δ) := by
  sorry

end VectorValuedHarmonicAnalysis
