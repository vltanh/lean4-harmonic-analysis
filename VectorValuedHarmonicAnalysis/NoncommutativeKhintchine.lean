module

public import VectorValuedHarmonicAnalysis.Paley.Rademacher
public import BanachProbability.KConvexity.Schatten
public import BanachProbability.NoncommutativeKhintchine.Lower

/-!
# The noncommutative Khintchine inequality

**Theorem** (`ncKhintchine`; F. Lust-Piquard, C. R. Acad. Sci. Paris 303 (1986); F. Lust-Piquard and
G. Pisier, *Non commutative Khintchine and Paley inequalities*, Ark. Mat. 29 (1991); the order `√q`
of the constant: G. Pisier,
*Non-commutative vector valued `L_p`-spaces and completely `p`-summing maps*, Astérisque 247 (1998),
Theorem 8.4.1 and (8.4.5), pp. 105–106). There is an absolute constant `C` such that for all
`2 ≤ q < ∞`, all sizes and all real matrices `x_1, …, x_K ∈ M_n (ℝ)`,

`max (‖(Σ x_kᵀ x_k)^{1/2}‖_{S_q}, ‖(Σ x_k x_kᵀ)^{1/2}‖_{S_q}) ≤ ‖Σ ε_k x_k‖_{L_q (Ω; S_q)}
  ≤ C √q max (‖(Σ x_kᵀ x_k)^{1/2}‖_{S_q}, ‖(Σ x_k x_kᵀ)^{1/2}‖_{S_q})`.

For normal `x_k` the two square functions agree (`ncKhintchine_of_normal`).

The lower bound is the convexity inequality (I.7) (`BanachProbability.ncKhintchine_lower_col`). The
upper bound follows Lust-Piquard–Pisier, pp. 254–255, and Pisier, p. 106: by duality,
`‖Σ ε_k x_k‖_{L_q (S_q)} = E tr (φ Σ ε_k x_k) = Σ tr (x_k φ_k)`,
`φ_k = E (ε_k φ)`, for some `φ` in the unit ball of `L_{q'} (S_{q'})`; Corollary III.4 for
`1 < q' ≤ 2` splits `φ_k = a_k + b_k` with control by `‖Σ ε_k φ_k‖_{L_1 (S_{q'})}`, the norm of the
Rademacher projection of `φ`, which is of order `√q`.

A shorter proof of the upper bound, by exchangeable pairs, with the constant `√(2 (q − 1))`, is
`BanachProbability.ncKhintchine_upper`.
-/

@[expose] public section

open BanachProbability BanachProbability.SignCube
open scoped ENNReal Matrix

namespace VectorValuedHarmonicAnalysis

/-- **The noncommutative Khintchine inequality** (Lust-Piquard 1986; Lust-Piquard–Pisier 1991;
Pisier 1998, (8.4.3) and (8.4.5)), real matrices, `2 ≤ q < ∞`, with constants `1` and `C √q`. -/
theorem ncKhintchine : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (q : ℝ), 2 ≤ q →
    ∀ (K : ℕ) (x : Fin K → Matrix n n ℝ),
    √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ))) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) ∧
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) ≤
      C * √q * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ))) := by
  sorry

/-- The noncommutative Khintchine inequality for normal matrices. -/
theorem ncKhintchine_of_normal : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (q : ℝ),
    2 ≤ q → ∀ (K : ℕ) (x : Fin K → Matrix n n ℝ), (∀ k, x k * (x k)ᵀ = (x k)ᵀ * x k) →
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ)) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) ∧
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) ≤
      C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ)) := by
  sorry

end VectorValuedHarmonicAnalysis
