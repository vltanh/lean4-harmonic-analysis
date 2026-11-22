module

public import VectorValuedHarmonicAnalysis.Paley.Rademacher
public import BanachProbability.KConvexity.Schatten
public import BanachProbability.NoncommutativeKhintchine.Lower
import BanachProbability.Schatten.CubeDuality
import BanachProbability.Schatten.Dilation

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

The lower bound is the convexity inequality (I.7), p. 247 (and its row form), followed by
`L² ≤ L^q` (`BanachProbability.ncKhintchine_lower_col`, `BanachProbability.ncKhintchine_lower_row`).
The upper bound follows Lust-Piquard–Pisier, pp. 254–255, and Pisier, p. 106: by duality,
`‖Σ ε_k x_k‖_{L_q (S_q)} = E tr (φ Σ ε_k x_k) = Σ tr (x_k φ_k)`, `φ_k = E (ε_k φ)`, for some `φ` in
the unit ball of `L_{q'} (S_{q'})`; Corollary III.4 for `1 < q' ≤ 2` splits `φ_k = a_k + b_k` with
control by `‖Σ ε_k φ_k‖_{L_1 (S_{q'})}`, the norm of the Rademacher projection of `φ`, which is at
most a constant times `√q`.

Departure from the sources, which treat all matrices at once: the duality is used for symmetric
`x_k`, with a symmetric-valued `φ`, and general real matrices are reduced to symmetric ones by the
Hermitian dilations `[[0, x_k], [x_kᵀ, 0]]`.

A shorter proof of the upper bound, by exchangeable pairs, with the constant `√(2 (q − 1))`, is
`BanachProbability.ncKhintchine_upper`.
-/

@[expose] public section

open BanachProbability BanachProbability.SignCube
open scoped ENNReal Matrix

namespace VectorValuedHarmonicAnalysis

/-! ### The upper bound for symmetric matrices, by duality -/

section Symmetric

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

private theorem sqrt_max (a b : ℝ) : √(max a b) = max √a √b :=
  Real.sqrt_monotone.map_max

omit [DecidableEq n] in
/-- `E tr (φ Σ ε_k x_k) = Σ tr (x_k φ_k)`, `φ_k = E (ε_k φ)`. -/
private theorem avg_trace_mul_eq (x : Fin K → Matrix n n ℝ)
    (φ : (Fin K → Bool) → Matrix n n ℝ) :
    (avg fun ε => ((∑ k, coin (ε k) • x k) * φ ε).trace) =
      ∑ k, (x k * (((2 : ℝ) ^ K)⁻¹ • ∑ η : Fin K → Bool, coin (η k) • φ η)).trace := by
  simp only [Finset.sum_mul, Matrix.trace_sum, avg_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum, Matrix.trace_sum, smul_eq_mul, avg,
    div_eq_inv_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

/-- `‖blockCol x‖_{S_q} = ‖Σ x_kᵀ x_k‖_{S_{q/2}}^{1/2}` for real matrices. -/
private theorem complexSchattenNorm_blockCol_map_ofReal {q : ℝ} (hq : 0 < q)
    (x : Fin K → Matrix n n ℝ) :
    complexSchattenNorm (ENNReal.ofReal q) (blockCol fun k => (x k).map Complex.ofReal) =
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k)) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
  have hq2 : ENNReal.ofReal (q / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have h := complexSchattenNorm_blockCol_sq hq0 fun k => (x k).map Complex.ofReal
  have e : ∑ k, ((x k).map Complex.ofReal)ᴴ * (x k).map Complex.ofReal =
      (∑ k, (x k)ᵀ * x k).map Complex.ofReal := by
    ext i j
    simp [Matrix.sum_apply, Matrix.mul_apply]
  rw [e, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos two_pos,
    complexSchattenNorm_map_ofReal hq2] at h
  rw [← h, Real.sqrt_sq (complexSchattenNorm_nonneg _ _)]

/-- `‖blockRow x‖_{S_q} = ‖Σ x_k x_kᵀ‖_{S_{q/2}}^{1/2}` for real matrices. -/
private theorem complexSchattenNorm_blockRow_map_ofReal {q : ℝ} (hq : 0 < q)
    (x : Fin K → Matrix n n ℝ) :
    complexSchattenNorm (ENNReal.ofReal q) (blockRow fun k => (x k).map Complex.ofReal) =
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ)) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
  have hq2 : ENNReal.ofReal (q / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have h := complexSchattenNorm_blockRow_sq hq0 fun k => (x k).map Complex.ofReal
  have e : ∑ k, (x k).map Complex.ofReal * ((x k).map Complex.ofReal)ᴴ =
      (∑ k, x k * (x k)ᵀ).map Complex.ofReal := by
    ext i j
    simp [Matrix.sum_apply, Matrix.mul_apply]
  rw [e, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos two_pos,
    complexSchattenNorm_map_ofReal hq2] at h
  rw [← h, Real.sqrt_sq (complexSchattenNorm_nonneg _ _)]

/-- The duality between `C_{q'} (ℓ²_R) + C_{q'} (ℓ²_L)` and `C_q (ℓ²_R) ∩ C_q (ℓ²_L)`: if
`φ_k = a_k + b_k`, then
`|Σ tr (x_k φ_k)| ≤ max (‖blockCol x‖_q, ‖blockRow x‖_q) (‖blockRow a‖_{q'} + ‖blockCol b‖_{q'})`.
-/
private theorem sum_trace_mul_le {q q' : ℝ} (hqq' : q.HolderConjugate q')
    (x y : Fin K → Matrix n n ℝ) {a b : Fin K → Matrix n n ℂ}
    (hab : ∀ k, (y k).map Complex.ofReal = a k + b k) :
    ∑ k, (x k * y k).trace ≤
      √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ))) *
      (complexSchattenNorm (ENNReal.ofReal q') (blockRow a) +
        complexSchattenNorm (ENNReal.ofReal q') (blockCol b)) := by
  have e : ((∑ k, (x k * y k).trace : ℝ) : ℂ) =
      ∑ k, (a k * (x k).map Complex.ofReal).trace +
        ∑ k, ((x k).map Complex.ofReal * b k).trace := by
    rw [← Finset.sum_add_distrib, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_comm (a k), ← Matrix.trace_add, ← Matrix.mul_add, ← hab k]
    simp [Matrix.trace, Matrix.mul_apply]
  have h1 := norm_sum_trace_mul_le hqq'.symm a fun k => (x k).map Complex.ofReal
  have h2 := norm_sum_trace_mul_le hqq' (fun k => (x k).map Complex.ofReal) b
  rw [complexSchattenNorm_blockCol_map_ofReal hqq'.pos] at h1
  rw [complexSchattenNorm_blockRow_map_ofReal hqq'.pos] at h2
  have ha := complexSchattenNorm_nonneg (ENNReal.ofReal q') (blockRow a)
  have hb := complexSchattenNorm_nonneg (ENNReal.ofReal q') (blockCol b)
  calc ∑ k, (x k * y k).trace ≤ ‖((∑ k, (x k * y k).trace : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real]
        exact Real.le_norm_self _
    _ ≤ _ + _ := e ▸ norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ ≤ _ := by
        rw [sqrt_max, mul_add, mul_comm (complexSchattenNorm _ (blockRow a))]
        exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hb)

/-- `‖Σ ε_k φ_k‖_{L_1 (S_{q'})} ≤ √(π/2) √(q + 1)` for the Rademacher projection `Σ ε_k φ_k` of a
symmetric `φ` in the unit ball of `L_{q'} (S_{q'})`. -/
private theorem avg_rademacherProj_le {q q' : ℝ} (hq : 2 ≤ q) (hqq' : q.HolderConjugate q')
    {φ : (Fin K → Bool) → Matrix n n ℝ} (hφ : ∀ ε, (φ ε).IsHermitian)
    (hφ1 : SignCube.lpNorm (schattenNorm (ENNReal.ofReal q')) q' φ ≤ 1) :
    (avg fun ε : Fin K → Bool => complexSchattenNorm (ENNReal.ofReal q') (∑ k, coin (ε k) •
      (((2 : ℝ) ^ K)⁻¹ • ∑ η : Fin K → Bool, coin (η k) • φ η).map Complex.ofReal)) ≤
      √(Real.pi / 2) * √(q + 1) := by
  have hq'0 : ENNReal.ofReal q' ≠ 0 := (ENNReal.ofReal_pos.2 hqq'.symm.pos).ne'
  have e (ε : Fin K → Bool) (y : Fin K → Matrix n n ℝ) :
      ∑ k, coin (ε k) • (y k).map Complex.ofReal =
        (∑ k, coin (ε k) • y k).map Complex.ofReal := by
    ext i j
    simp [Matrix.sum_apply]
  simp only [e, complexSchattenNorm_map_ofReal hq'0]
  refine (avg_le_rpow_avg_rpow (fun ε => schattenNorm_nonneg _ _) hqq'.symm.lt.le).trans ?_
  refine (lpNorm_rademacherProj_schattenNorm_conj_le hq hqq' φ hφ).trans ?_
  exact mul_le_of_le_one_right (by positivity) hφ1

end Symmetric

/-- The upper bound for symmetric matrices, by the duality argument of Lust-Piquard–Pisier,
pp. 254–255, and Pisier, p. 106 (there for all matrices). -/
private theorem exists_symmetric_upper : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n]
    (q : ℝ), 2 ≤ q → ∀ (K : ℕ) (x : Fin K → Matrix n n ℝ), (∀ k, (x k).IsHermitian) →
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) ≤
      M * √q * √(max (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, (x k)ᵀ * x k))
        (schattenNorm (ENNReal.ofReal (q / 2)) (∑ k, x k * (x k)ᵀ))) := by
  obtain ⟨M, hM, hrad⟩ := rademacher_schatten_le
  refine ⟨M * (√(Real.pi / 2) * √(3 / 2)), by positivity, ?_⟩
  intro n _ _ q hq K x hx
  have hqq' : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent (by linarith)
  set q' := q / (q - 1) with hq'
  have hq'2 : q' ≤ 2 := by
    rw [hq', div_le_iff₀ (by linarith)]
    linarith
  -- duality: a norming `φ`
  have hY (ε : Fin K → Bool) : (∑ k, coin (ε k) • x k).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, (hx k).eq, star_trivial]
  obtain ⟨φ, hφ, hφ1, hφe⟩ := exists_avg_trace_mul_eq_lpNorm hqq'
    (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) hY
  -- Corollary III.4 for `φ_k = E (ε_k φ)`
  obtain ⟨a, b, hab, hle⟩ := hrad n q' hqq'.symm.lt.le hq'2 K fun k =>
    (((2 : ℝ) ^ K)⁻¹ • ∑ η : Fin K → Bool, coin (η k) • φ η).map Complex.ofReal
  have h1 := hle.trans (mul_le_mul_of_nonneg_left (avg_rademacherProj_le hq hqq' hφ hφ1) hM.le)
  have h2 : √(q + 1) ≤ √(3 / 2) * √q := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [← hφe, avg_trace_mul_eq]
  refine (sum_trace_mul_le hqq' x _ hab).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right (h1.trans ?_) (Real.sqrt_nonneg _)
  calc M * (√(Real.pi / 2) * √(q + 1)) ≤ M * (√(Real.pi / 2) * (√(3 / 2) * √q)) := by gcongr
    _ = _ := by ring

/-! ### The general case, by dilation -/

section Dilation

variable {n : Type*} [Fintype n] [DecidableEq n] {K : ℕ}

/-- `‖Σ ε_k D (x_k)‖_{L_q (S_q)} = 2^{1/q} ‖Σ ε_k x_k‖_{L_q (S_q)}`. -/
private theorem lpNorm_dilation {q : ℝ} (hq : 0 < q) (x : Fin K → Matrix n n ℝ) :
    SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • dilation (x k)) =
      (2 : ℝ) ^ (1 / q) * SignCube.lpNorm (schattenNorm (ENNReal.ofReal q)) q
        (fun ε : Fin K → Bool => ∑ k, coin (ε k) • x k) := by
  have hD (ε : Fin K → Bool) :
      ∑ k, coin (ε k) • dilation (x k) = dilation (∑ k, coin (ε k) • x k) := by
    change _ = dilationLinearMap (∑ k, coin (ε k) • x k)
    rw [map_sum]
    simp only [map_smul]
    rfl
  unfold SignCube.lpNorm
  simp only [hD, schattenNorm_dilation_rpow hq]
  rw [avg_const_mul, Real.mul_rpow (by norm_num)
    (avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _)]

/-- The square function of the dilations: `‖diag (B, C)‖_{S_{q/2}}^{1/2} ≤ 2^{1/q}
max (‖B‖_{S_{q/2}}, ‖C‖_{S_{q/2}})^{1/2}`. -/
private theorem sqrt_schattenNorm_fromBlocks_le {q : ℝ} (hq : 0 < q) (B C : Matrix n n ℝ) :
    √(schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C)) ≤
      (2 : ℝ) ^ (1 / q) * √(max (schattenNorm (ENNReal.ofReal (q / 2)) B)
        (schattenNorm (ENNReal.ofReal (q / 2)) C)) := by
  have hq2 : 0 < q / 2 := by linarith
  set m := max (schattenNorm (ENNReal.ofReal (q / 2)) B) (schattenNorm (ENNReal.ofReal (q / 2)) C)
  set D := schattenNorm (ENNReal.ofReal (q / 2)) (Matrix.fromBlocks B 0 0 C)
  have hm0 : 0 ≤ m := (schattenNorm_nonneg _ _).trans (le_max_left _ _)
  have hD0 : 0 ≤ D := schattenNorm_nonneg _ _
  have hle : D ^ (q / 2) ≤ 2 * m ^ (q / 2) := by
    rw [schattenNorm_fromBlocks_rpow hq2 B C]
    have h1 := Real.rpow_le_rpow (schattenNorm_nonneg _ _) (le_max_left
      (schattenNorm (ENNReal.ofReal (q / 2)) B) (schattenNorm (ENNReal.ofReal (q / 2)) C)) hq2.le
    have h2 := Real.rpow_le_rpow (schattenNorm_nonneg _ _) (le_max_right
      (schattenNorm (ENNReal.ofReal (q / 2)) B) (schattenNorm (ENNReal.ofReal (q / 2)) C)) hq2.le
    linarith
  have e (t : ℝ) (ht : 0 ≤ t) : (t ^ (q / 2)) ^ (1 / q) = √t := by
    rw [← Real.rpow_mul ht, Real.sqrt_eq_rpow]
    congr 1
    field_simp
  calc √D = (D ^ (q / 2)) ^ (1 / q) := (e D hD0).symm
    _ ≤ (2 * m ^ (q / 2)) ^ (1 / q) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hD0 _) hle (by positivity)
    _ = (2 : ℝ) ^ (1 / q) * √m := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hm0 _), e m hm0]

end Dilation

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
  obtain ⟨M, hM, hsym⟩ := exists_symmetric_upper
  refine ⟨M, hM, ?_⟩
  intro n _ _ q hq K x
  refine ⟨?_, ?_⟩
  · rw [sqrt_max]
    exact max_le (ncKhintchine_lower_col hq x) (ncKhintchine_lower_row hq x)
  · have hq0 : 0 < q := by linarith
    have h := hsym (n ⊕ n) q hq K (fun k => dilation (x k)) fun k => dilation_isHermitian (x k)
    have hT (k : Fin K) : (dilation (x k))ᵀ = dilation (x k) :=
      (Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans (dilation_isHermitian (x k))
    simp only [hT, max_self, sum_dilation_mul_self] at h
    rw [lpNorm_dilation hq0] at h
    have h2 := sqrt_schattenNorm_fromBlocks_le hq0 (∑ k, x k * (x k)ᵀ) (∑ k, (x k)ᵀ * x k)
    rw [max_comm] at h2
    -- the factors `2^{1/q}` cancel
    refine le_of_mul_le_mul_left (h.trans ?_) (show (0 : ℝ) < 2 ^ (1 / q) by positivity)
    refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq ?_
    ring

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

end VectorValuedHarmonicAnalysis
