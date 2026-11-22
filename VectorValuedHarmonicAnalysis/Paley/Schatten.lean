module

public import VectorValuedHarmonicAnalysis.Hardy.Factorization

/-!
# Paley's inequality in the Schatten classes

**Theorem** (`paley_schatten`; F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley
inequalities*, Ark. Mat. 29 (1991), Theorem III.1 (i) for the Paley projection, pp. 252–253; for
`p = 1`, Theorem II.1). There is an absolute constant `M` such that for `1 ≤ p ≤ 2`, in every size
`n`, every analytic polynomial
`f = Σ_{k ≥ 0} c_k e_k` with coefficients `c_k ∈ M_n (ℂ)` and every `K`,

`‖(c_{2^k})_{k < K}‖_{C_p (ℓ²_R) + C_p (ℓ²_L)} ≤ M ∫_𝕋 ‖f (t)‖_{S_p} dt`,

that is, `c_{2^k} = b_k + a_k` with
`‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} + ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} ≤ M ∫ ‖f‖_{S_p}`.

The proof is Lust-Piquard and Pisier's: `f = g h` with `g, h ∈ H² (C_{2p})`; `f̂ (2^k) = A_k + B_k`
by splitting `Σ ĝ (q) ĥ (2^k − q)` at `q = 2^{k−1}`; `A_k = ∫ g H_{2^k} e^{−i 2^k t}`, Jensen's
inequality in `C_p (ℓ²_L)` and Hölder's inequality; then (III.1)–(III.3): the square function is
dominated by the Rademacher sums (I.7), and these by the Littlewood–Paley inequality for `C_{2p}`, a
UMD space whose constant is bounded for `2p ∈ [2, 4]`. The constant is therefore independent of `p`
(G. Pisier, *Non-commutative vector valued `L_p`-spaces and completely `p`-summing maps*, Astérisque
247 (1998), p. 106). In place of Bourgain's multiplier theorem, which the source uses for general
multipliers, the Littlewood–Paley inequality of `LittlewoodPaley.Circle` and the randomised
boundedness of single frequencies suffice for the sequence `2^k`.
-/

@[expose] public section

open MeasureTheory AddCircle BanachProbability BanachProbability.SignCube
open scoped ENNReal Matrix

namespace VectorValuedHarmonicAnalysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The blocks `H_{2^k} (t) = Σ_{2^k/2 ≤ p ≤ 2^k} ĥ (p) e_p (t)` (Lust-Piquard–Pisier, p. 249). -/
noncomputable def paleyBlockClosed (h : UnitAddCircle → Matrix n n ℂ) (k : ℕ) (t : UnitAddCircle) :
    Matrix n n ℂ :=
  ∑ p ∈ (Finset.Icc 0 (2 ^ k)).filter (fun p : ℕ => 2 ^ k ≤ 2 * p),
    fourier (p : ℤ) t • matFourierCoeff h p

/-- The blocks `G_{2^k} (t) = Σ_{2^k/2 < p ≤ 2^k} ĝ (p) e_p (t)` (Lust-Piquard–Pisier, p. 249). -/
noncomputable def paleyBlockOpen (g : UnitAddCircle → Matrix n n ℂ) (k : ℕ) (t : UnitAddCircle) :
    Matrix n n ℂ :=
  ∑ p ∈ (Finset.Icc 0 (2 ^ k)).filter (fun p : ℕ => 2 ^ k < 2 * p),
    fourier (p : ℤ) t • matFourierCoeff g p

/-- Lust-Piquard–Pisier, p. 249: `(g h)^ (2^k) = A_k + B_k`, `A_k = ∫ g H_{2^k} e_{−2^k}`,
`B_k = ∫ G_{2^k} h e_{−2^k}`. -/
theorem matFourierCoeff_mul_two_pow {g h : UnitAddCircle → Matrix n n ℂ} (hg : IsHardyTwo g)
    (hh : IsHardyTwo h) (k : ℕ) :
    matFourierCoeff (fun t => g t * h t) (2 ^ k) =
      matFourierCoeff (fun t => g t * paleyBlockClosed h k t) (2 ^ k) +
        matFourierCoeff (fun t => paleyBlockOpen g k t * h t) (2 ^ k) := by
  sorry

/-- Lust-Piquard–Pisier, (III.3) and (0.1), for the closed blocks: an absolute constant bounds
`E ∫ ‖Σ ε_k H_{2^k}‖_{S_{2p}}²` by `∫ ‖h‖_{S_{2p}}²`, for `1 ≤ p ≤ 2` and all sizes. -/
theorem exists_avg_integral_paleyBlockClosed_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n]
    [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ (h : UnitAddCircle → Matrix n n ℂ), IsHardyTwo h →
    ∀ K : ℕ, (avg fun ε : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
        (∑ k, coin (ε k) • paleyBlockClosed h k t) ^ 2 ∂haarAddCircle) ≤
      C * ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ∂haarAddCircle := by
  sorry

/-- The same for the half-open blocks. -/
theorem exists_avg_integral_paleyBlockOpen_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n]
    [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ (g : UnitAddCircle → Matrix n n ℂ), IsHardyTwo g →
    ∀ K : ℕ, (avg fun ε : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
        (∑ k, coin (ε k) • paleyBlockOpen g k t) ^ 2 ∂haarAddCircle) ≤
      C * ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle := by
  sorry

/-- **Paley's inequality in the Schatten classes** (Lust-Piquard–Pisier (1991), Theorem III.1 (i)
for the Paley projection, uniformly in `1 ≤ p ≤ 2`). -/
theorem paley_schatten : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ), 1 ≤ p →
    p ≤ 2 → ∀ (c : ℤ →₀ Matrix n n ℂ), (∀ k ∈ c.support, 0 ≤ k) → ∀ K : ℕ,
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k : Fin K, c (2 ^ (k : ℕ)) = a k + b k) ∧
      complexSchattenNorm (ENNReal.ofReal p) (blockRow a) +
        complexSchattenNorm (ENNReal.ofReal p) (blockCol b) ≤
      M * ∫ t, complexSchattenNorm (ENNReal.ofReal p) (trigPoly c t) ∂haarAddCircle := by
  sorry

end VectorValuedHarmonicAnalysis
