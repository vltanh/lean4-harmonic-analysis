/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Paley.Rademacher
import BanachProbability.KConvexity.Schatten
import BanachProbability.Schatten.CubeDuality

/-!
# The noncommutative Khintchine inequality

**Theorem** (`ncKhintchine`; F. Lust-Piquard, C. R. Acad. Sci. Paris 303 (1986); F. Lust-Piquard and
G. Pisier, *Non commutative Khintchine and Paley inequalities*, Ark. Mat. 29 (1991); for the growth
of the constant, G. Pisier, *Non-commutative vector valued `L_p`-spaces and completely `p`-summing
maps*, Astérisque 247 (1998), Theorem 8.4.1, (8.4.3) and (8.4.5), pp. 105–106). There is an absolute
constant `C` such that for all `2 ≤ q < ∞`, all sizes and all real matrices `x_1, …, x_K ∈ M_n (ℝ)`,

`max (‖(Σ x_kᵀ x_k)^{1/2}‖_{S_q}, ‖(Σ x_k x_kᵀ)^{1/2}‖_{S_q}) ≤ ‖Σ ε_k x_k‖_{L_q (Ω; S_q)}
  ≤ C √q max (‖(Σ x_kᵀ x_k)^{1/2}‖_{S_q}, ‖(Σ x_k x_kᵀ)^{1/2}‖_{S_q})`.

In the statements the square functions are written without square roots of matrices:
`‖(Σ x_kᵀ x_k)^{1/2}‖_{S_q} = ‖Σ x_kᵀ x_k‖_{S_{q/2}}^{1/2}`, and similarly for `Σ x_k x_kᵀ`. For
normal `x_k` the two square functions agree (`ncKhintchine_of_normal`).

The sources consider complex operators on Hilbert spaces; here the `x_k` are real matrices. In the
proof they are viewed as complex matrices, and the square functions are
`‖blockCol x‖_{S_q}` and `‖blockRow x‖_{S_q}` (`BanachProbability.Schatten.Block`), the norms of
`C_q (ℓ²_R)` and `C_q (ℓ²_L)`.

## The lower bound

It is the convexity inequality (I.7) of Lust-Piquard–Pisier, p. 247, which follows from (I.5) and
the triangle inequality in `C_F`, here `C_F = S_{q/2}`: `‖blockCol x‖_{S_q}² ≤ E ‖Σ ε_k x_k‖_{S_q}²`
(`BanachProbability.complexSchattenNorm_blockCol_sq_le_avg`), and its row form; then `L² ≤ L^q`.
(`BanachProbability.ncKhintchine_lower_col` and `ncKhintchine_lower_row` are the same bounds.)

## The upper bound

It is the duality argument of Lust-Piquard–Pisier, Remark III.5, pp. 254–255, and Pisier, p. 106.
Let `q'` be the conjugate exponent, `1 < q' ≤ 2`.

1. For some real `φ` in the unit ball of `L_{q'} (Ω; S_{q'})`, with `φ_k = E (ε_k φ)`,
   `‖Σ ε_k x_k‖_{L_q (S_q)} = E tr (φᵀ Σ ε_k x_k) = Σ tr (x_k φ_kᵀ)`
   (`BanachProbability.exists_avg_trace_transpose_mul_eq_lpNorm`).
2. Corollary III.4, p. 254, for `S_{q'}` (`rademacher_schatten_le`): `φ_k = a_k + b_k` with complex
   `a_k`, `b_k` and `‖blockRow a‖_{S_{q'}} + ‖blockCol b‖_{S_{q'}} ≤ M E ‖Σ ε_k φ_k‖_{S_{q'}}`.
3. `Σ ε_k φ_k = P_1 φ` is the Rademacher projection of `φ`, and, by K-convexity,
   `E ‖P_1 φ‖_{S_{q'}} ≤ ‖P_1 φ‖_{L_{q'} (S_{q'})} ≤ √(π/2) √(q + 1)`
   (`BanachProbability.lpNorm_rademacherProj_schattenNorm_conj_le`).
4. `Σ tr (x_k φ_kᵀ) = Σ tr (x_k a_kᴴ) + Σ tr (x_k b_kᴴ) ≤
   ‖blockRow x‖_{S_q} ‖blockRow a‖_{S_{q'}} + ‖blockCol x‖_{S_q} ‖blockCol b‖_{S_{q'}} ≤
   max (‖blockCol x‖_{S_q}, ‖blockRow x‖_{S_q}) (‖blockRow a‖_{S_{q'}} + ‖blockCol b‖_{S_{q'}})`.
   This is the duality of `C_{q'} (ℓ²_R) + C_{q'} (ℓ²_L)`, p. 248, (I.12), by the dualities of
   `C_q (ℓ²_R)` and `C_{q'} (ℓ²_R)`, and of `C_q (ℓ²_L)` and `C_{q'} (ℓ²_L)`, p. 246. The maximum of
   the two norms, as in Pisier's (8.4.3), stands for the norm of `C_q (ℓ²_S)`, to which it is
   equivalent by (I.10) and (I.11).

A shorter proof of the upper bound, by exchangeable pairs, with the constant `√(2 (q − 1))`, is
`BanachProbability.ncKhintchine_upper`.
-/

@[expose] public section

open BanachProbability BanachProbability.SignCube
open scoped Matrix

namespace HarmonicAnalysis

section RealMatrices

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

private theorem sqrt_max (a b : ℝ) : √(max a b) = max √a √b :=
  Real.sqrt_monotone.map_max

/-! ### The square functions as norms of block columns and block rows -/

/-- `‖blockCol x‖_{S_q} = ‖Σ x_kᵀ x_k‖_{S_{q/2}}^{1/2}` for real matrices. -/
private theorem complexSchattenNorm_blockCol_map_ofReal {q : ℝ} (hq : 0 < q)
    (x : Fin K → Matrix n n ℝ) :
    complexSchattenNorm (ENNReal.ofReal q) (blockCol fun k => (x k).map Complex.ofReal) =
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k)) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
  change complexSchattenNorm _ ((blockCol x).map Complex.ofReal) = _
  rw [complexSchattenNorm_map_ofReal hq0, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat,
    show ∑ k, (x k)ᵀ * x k = (blockCol x)ᵀ * blockCol x from
      (conjTranspose_blockCol_mul_blockCol x x).symm,
    schattenNorm_transpose_mul_self hq0, Real.sqrt_sq (schattenNorm_nonneg _ _)]

/-- `‖blockRow x‖_{S_q} = ‖Σ x_k x_kᵀ‖_{S_{q/2}}^{1/2}` for real matrices. -/
private theorem complexSchattenNorm_blockRow_map_ofReal {q : ℝ} (hq : 0 < q)
    (x : Fin K → Matrix n n ℝ) :
    complexSchattenNorm (ENNReal.ofReal q) (blockRow fun k => (x k).map Complex.ofReal) =
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ)) := by
  have h := complexSchattenNorm_blockCol_map_ofReal hq fun k => (x k)ᵀ
  simp only [Matrix.transpose_transpose] at h
  rw [← h, ← complexSchattenNorm_blockRow_conjTranspose]
  congr 2
  funext k
  ext i j
  simp

/-- `‖Σ ε_k x_k‖_{S_p}` is the same when the real matrices `x_k` are viewed as complex ones. -/
private theorem complexSchattenNorm_sum_coin_smul_map_ofReal {p : ℝ} (hp : 0 < p)
    (x : Fin K → Matrix n n ℝ) (ε : Fin K → Bool) :
    complexSchattenNorm (ENNReal.ofReal p) (∑ k, coin (ε k) • (x k).map Complex.ofReal) =
      schattenNorm (ENNReal.ofReal p) (∑ k, coin (ε k) • x k) := by
  rw [← complexSchattenNorm_map_ofReal (ENNReal.ofReal_pos.2 hp).ne']
  congr 1
  ext i j
  simp [Matrix.sum_apply]

/-! ### The lower bound -/

/-- `c² ≤ E ‖Σ ε_k x_k‖_{S_q}²` implies `c ≤ ‖Σ ε_k x_k‖_{L_q (S_q)}`, by `L² ≤ L^q`. -/
private theorem le_lpNorm_of_sq_le_avg {q : ℝ} (hq : 2 ≤ q) (x : Fin K → Matrix n n ℝ) {c : ℝ}
    (hc : c ^ 2 ≤ avg fun ε : Fin K → Bool =>
      complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • (x k).map Complex.ofReal) ^ 2) :
    c ≤ SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
      (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) := by
  simp only [complexSchattenNorm_sum_coin_smul_map_ofReal (zero_lt_two.trans_le hq)] at hc
  refine (Real.le_sqrt_of_sq_le hc).trans ?_
  refine Eq.trans_le ?_ (lpNorm_mono_exponent (schattenNorm_nonneg _) two_pos hq _)
  simp only [SignCube.lpNorm, Real.sqrt_eq_rpow, Real.rpow_two]

/-- The lower bound for the column square function: Lust-Piquard–Pisier, (I.7), p. 247, and
`L² ≤ L^q`. -/
private theorem lower_col {q : ℝ} (hq : 2 ≤ q) (x : Fin K → Matrix n n ℝ) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k)) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) := by
  rw [← complexSchattenNorm_blockCol_map_ofReal (zero_lt_two.trans_le hq)]
  exact le_lpNorm_of_sq_le_avg hq x (complexSchattenNorm_blockCol_sq_le_avg hq _)

/-- The lower bound for the row square function: Lust-Piquard–Pisier, (I.7), p. 247, for the
adjoints, and `L² ≤ L^q`. -/
private theorem lower_row {q : ℝ} (hq : 2 ≤ q) (x : Fin K → Matrix n n ℝ) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ)) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) := by
  rw [← complexSchattenNorm_blockRow_map_ofReal (zero_lt_two.trans_le hq)]
  exact le_lpNorm_of_sq_le_avg hq x (complexSchattenNorm_blockRow_sq_le_avg hq _)

/-! ### The upper bound, by duality -/

omit [DecidableEq n] in
/-- `E tr (φᵀ Σ ε_k x_k) = Σ tr (x_k φ_kᵀ)`, `φ_k = E (ε_k φ)`. -/
private theorem avg_trace_transpose_mul_eq (x : Fin K → Matrix n n ℝ)
    (φ : (Fin K → Bool) → Matrix n n ℝ) :
    (avg fun ε => ((φ ε)ᵀ * ∑ k, coin (ε k) • x k).trace) =
      ∑ k, (x k * (rademacherCoeff φ k)ᵀ).trace := by
  have e (k : Fin K) :
      rademacherCoeff (fun ε => (φ ε)ᵀ) k = (rademacherCoeff φ k)ᵀ := by
    simp only [rademacherCoeff, Matrix.transpose_smul, Matrix.transpose_sum]
  simp only [← e, Matrix.trace_mul_comm (φ _)ᵀ]
  exact avg_trace_sum_coin_smul_mul x fun ε => (φ ε)ᵀ

/-- The bound in the duality of `C_q (ℓ²_R) ∩ C_q (ℓ²_L)` and `C_{q'} (ℓ²_R) + C_{q'} (ℓ²_L)`
(Lust-Piquard–Pisier, (I.12), p. 248, with the maximum of the two norms): if `φ_k = a_k + b_k`, then
`Σ tr (x_k φ_kᵀ) ≤ max (‖blockCol x‖_q, ‖blockRow x‖_q) (‖blockRow a‖_{q'} + ‖blockCol b‖_{q'})`.
-/
private theorem sum_trace_mul_transpose_le {q q' : ℝ} (hqq' : q.HolderConjugate q')
    (x y : Fin K → Matrix n n ℝ) {a b : Fin K → Matrix n n ℂ}
    (hab : ∀ k, (y k).map Complex.ofReal = a k + b k) :
    ∑ k, (x k * (y k)ᵀ).trace ≤
      √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ))) *
      (complexSchattenNorm (ENNReal.ofReal q') (blockRow a) +
        complexSchattenNorm (ENNReal.ofReal q') (blockCol b)) := by
  -- `φ_kᵀ = φ_kᴴ = a_kᴴ + b_kᴴ`
  have e : ((∑ k, (x k * (y k)ᵀ).trace : ℝ) : ℂ) =
      ∑ k, ((x k).map Complex.ofReal * (a k)ᴴ).trace +
        ∑ k, ((x k).map Complex.ofReal * (b k)ᴴ).trace := by
    rw [← Finset.sum_add_distrib, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.trace_add, ← Matrix.mul_add, ← Matrix.conjTranspose_add, ← hab k]
    simp [Matrix.trace, Matrix.mul_apply]
  -- the rows for `a`, the columns for `b` (p. 246)
  have ha := norm_sum_trace_mul_conjTranspose_le_blockRow hqq'
    (fun k => (x k).map Complex.ofReal) a
  have hb := norm_sum_trace_mul_conjTranspose_le_blockCol hqq'
    (fun k => (x k).map Complex.ofReal) b
  rw [complexSchattenNorm_blockRow_map_ofReal hqq'.pos] at ha
  rw [complexSchattenNorm_blockCol_map_ofReal hqq'.pos] at hb
  calc ∑ k, (x k * (y k)ᵀ).trace ≤ ‖((∑ k, (x k * (y k)ᵀ).trace : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real]
        exact Real.le_norm_self _
    _ ≤ _ + _ := e ▸ norm_add_le _ _
    _ ≤ _ := add_le_add ha hb
    _ ≤ _ := by
        rw [sqrt_max, mul_add]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (complexSchattenNorm_nonneg _ _))
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (complexSchattenNorm_nonneg _ _))

/-- `E ‖Σ ε_k φ_k‖_{S_{q'}} ≤ ‖P_1 φ‖_{L_{q'} (S_{q'})} ≤ √(π/2) √(q + 1)`, `φ_k = E (ε_k φ)`, for
`φ` in the unit ball of `L_{q'} (S_{q'})`. -/
private theorem avg_sum_coin_smul_rademacherCoeff_le {q q' : ℝ} (hq : 2 ≤ q)
    (hqq' : q.HolderConjugate q') {φ : (Fin K → Bool) → Matrix n n ℝ}
    (hφ : SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' φ ≤ 1) :
    (avg fun ε : Fin K → Bool => complexSchattenNorm (ENNReal.ofReal q')
      (∑ k, coin (ε k) • (rademacherCoeff φ k).map Complex.ofReal)) ≤
      √(Real.pi / 2) * √(q + 1) := by
  simp only [complexSchattenNorm_sum_coin_smul_map_ofReal hqq'.symm.pos]
  refine (avg_le_rpow_avg_rpow (fun ε => schattenNorm_nonneg _ _) hqq'.symm.lt.le).trans ?_
  refine (lpNorm_rademacherProj_schattenNorm_conj_le hq hqq' φ).trans ?_
  exact mul_le_of_le_one_right (by positivity) hφ

end RealMatrices

/-- The upper bound, by duality (Lust-Piquard–Pisier, pp. 246–248 and 254–255; Pisier, p. 106). -/
private theorem exists_upper : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n] [DecidableEq n]
    (q : ℝ), 2 ≤ q → ∀ (K : ℕ) (x : Fin K → Matrix n n ℝ),
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) ≤
      C * √q * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ))) := by
  obtain ⟨M, hM, hrad⟩ := rademacher_schatten_le
  refine ⟨M * (√(Real.pi / 2) * √(3 / 2)), by positivity, ?_⟩
  intro n _ _ q hq K x
  have hqq' : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent (by linarith)
  set q' := q / (q - 1) with hq'
  have hq'2 : q' ≤ 2 := by
    rw [hq', div_le_iff₀ (by linarith)]
    linarith
  -- a norming `φ`
  obtain ⟨φ, hφ, hφe⟩ := exists_avg_trace_transpose_mul_eq_lpNorm hqq'
    fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k
  -- Corollary III.4 for `φ_k = E (ε_k φ)`
  obtain ⟨a, b, hab, hle⟩ := hrad n q' hqq'.symm.lt.le hq'2 K fun k =>
    (rademacherCoeff φ k).map Complex.ofReal
  -- the Rademacher projection of `φ`
  have h1 := hle.trans
    (mul_le_mul_of_nonneg_left (avg_sum_coin_smul_rademacherCoeff_le hq hqq' hφ) hM.le)
  have h2 : √(q + 1) ≤ √(3 / 2) * √q := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  -- the duality of the square functions
  rw [← hφe, avg_trace_transpose_mul_eq]
  refine (sum_trace_mul_transpose_le hqq' x _ hab).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right (h1.trans ?_) (Real.sqrt_nonneg _)
  calc M * (√(Real.pi / 2) * √(q + 1)) ≤ M * (√(Real.pi / 2) * (√(3 / 2) * √q)) := by gcongr
    _ = _ := by ring

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
  obtain ⟨C, hC, h⟩ := exists_upper
  refine ⟨C, hC, fun n _ _ q hq K x => ⟨?_, h n q hq K x⟩⟩
  rw [sqrt_max]
  exact max_le (lower_col hq x) (lower_row hq x)

/-- The noncommutative Khintchine inequality for normal matrices. -/
theorem ncKhintchine_of_normal : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (q : ℝ),
    2 ≤ q → ∀ (K : ℕ) (x : Fin K → Matrix n n ℝ), (∀ k, x k * (x k)ᵀ = (x k)ᵀ * x k) →
    √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ)) ≤
      SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) ∧
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) ≤
      C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ)) := by
  obtain ⟨C, hC, h⟩ := ncKhintchine
  refine ⟨C, hC, ?_⟩
  intro n _ _ q hq K x hx
  -- the two square functions agree
  have h1 := h n q hq K x
  simp only [← hx, max_self] at h1
  exact h1

end HarmonicAnalysis
