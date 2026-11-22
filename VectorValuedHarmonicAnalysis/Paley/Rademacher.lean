module

public import VectorValuedHarmonicAnalysis.Paley.Schatten

/-!
# The Khintchine inequality in the Schatten classes, `1 ≤ p ≤ 2`

**Theorem** (`rademacher_schatten_le`; F. Lust-Piquard and G. Pisier, *Non commutative Khintchine
and Paley inequalities*, Ark. Mat. 29 (1991), Corollary III.4, p. 254, and Theorem 0.1, with signs;
G. Pisier, Astérisque 247 (1998), (8.4.4), p. 105). There is an absolute constant `M` such that for
`1 ≤ p ≤ 2`, in every size, all `A_1, …, A_K ∈ M_n (ℂ)` are `A_k = a_k + b_k` with

`‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M E ‖Σ ε_k A_k‖_{S_p}`.

Corollary III.4 has the `L²` norm on the right-hand side; the `L¹` norm is what Theorem III.1 (i)
gives.

Proof (p. 243): apply Paley's inequality to `Σ ε_k e^{i 2^k t} A_k`; the left-hand side does not
depend on the signs, and the average over the signs of the right-hand side is at most
`2 E ‖Σ ε_k A_k‖` by the contraction principle.
-/

@[expose] public section

open MeasureTheory AddCircle BanachProbability BanachProbability.SignCube
open scoped ENNReal Matrix

namespace VectorValuedHarmonicAnalysis

/-- **The Khintchine inequality in the Schatten classes**, `1 ≤ p ≤ 2` (Lust-Piquard–Pisier (1991),
Corollary III.4), with a constant independent of `p` and of the size. -/
theorem rademacher_schatten_le : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ),
    1 ≤ p → p ≤ 2 → ∀ (K : ℕ) (A : Fin K → Matrix n n ℂ),
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k, A k = a k + b k) ∧
      complexSchattenNorm (ENNReal.ofReal p) (blockRow a) +
        complexSchattenNorm (ENNReal.ofReal p) (blockCol b) ≤
      M * avg fun ε : Fin K → Bool =>
        complexSchattenNorm (ENNReal.ofReal p) (∑ k, coin (ε k) • A k) := by
  sorry

end VectorValuedHarmonicAnalysis
