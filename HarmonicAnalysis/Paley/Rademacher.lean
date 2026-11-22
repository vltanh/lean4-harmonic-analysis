/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Paley.Schatten
import BanachProbability.RandomSums.Contraction

/-!
# The lower Khintchine inequality in the Schatten classes, `1 ≤ p ≤ 2`

**Theorem** (`rademacher_schatten_le`; F. Lust-Piquard and G. Pisier, *Non commutative Khintchine
and Paley inequalities*, Ark. Mat. 29 (1991), Corollary III.4, p. 254, left-hand inequality, with
signs, `1 < p < 2`; for `p = 1`, Theorem 0.1, p. 242, the right-hand inequality of (0.5); G. Pisier,
*Non-commutative vector valued `L_p`-spaces and completely `p`-summing maps*, Astérisque 247 (1998),
(8.4.4), left-hand inequality, p. 105). There is an absolute constant `M` such that for
`1 ≤ p ≤ 2`, in every size, all `A_1, …, A_K ∈ M_n (ℂ)` are `A_k = a_k + b_k` with

`‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M E ‖Σ ε_k A_k‖_{S_p}`.

The square functions are written as norms of block rows and block columns
(`BanachProbability.Schatten.Block`):
`‖blockRow a‖_{S_p} = ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} = ‖Σ a_k a_kᴴ‖_{S_{p/2}}^{1/2}` and
`‖blockCol b‖_{S_p} = ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} = ‖Σ b_kᴴ b_k‖_{S_{p/2}}^{1/2}`.

This is the hard half of the Khintchine inequality. The easy half, the bound of the Rademacher sums
by the square functions, (I.14), p. 248, is not proved here.

Corollary III.4 is stated with the functions `e^{i 2^k t}` in place of the signs `ε_k`, and with the
`L²` norm on the right-hand side; (8.4.4) has the `L_p` norm. The `L¹` norm, which is at most these,
is what Theorem III.1 (i) gives.

Proof (p. 243, "an elementary averaging over all choices of signs"): apply Paley's inequality to
`Σ ε_k e_{2^k} A_k`; the left-hand side does not depend on the signs, so the right-hand side may be
averaged over the signs; by the contraction principle its average is at most `2 M E ‖Σ ε_k A_k‖`.
-/

@[expose] public section

open MeasureTheory AddCircle BanachProbability BanachProbability.SignCube
open scoped ENNReal Matrix

namespace HarmonicAnalysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The coefficients of the lacunary polynomial `f_ε = Σ_k ε_k e_{2^k} A_k`. -/
private noncomputable def lacunaryCoeff {K : ℕ} (A : Fin K → Matrix n n ℂ) (ε : Fin K → Bool) :
    ℤ →₀ Matrix n n ℂ :=
  ∑ k : Fin K, Finsupp.single ((2 : ℤ) ^ (k : ℕ)) (coin (ε k) • A k)

omit [Fintype n] [DecidableEq n] in
private theorem lacunaryCoeff_two_pow {K : ℕ} (A : Fin K → Matrix n n ℂ) (ε : Fin K → Bool)
    (k : Fin K) : lacunaryCoeff A ε (2 ^ (k : ℕ)) = coin (ε k) • A k := by
  have hinj (j : Fin K) : (2 : ℤ) ^ (j : ℕ) = 2 ^ (k : ℕ) ↔ j = k := by
    rw [pow_right_inj₀ (by norm_num) (by norm_num), Fin.ext_iff]
  simp [lacunaryCoeff, Finsupp.finsetSum_apply, Finsupp.single_apply, hinj]

omit [Fintype n] [DecidableEq n] in
private theorem nonneg_of_mem_support_lacunaryCoeff {K : ℕ} (A : Fin K → Matrix n n ℂ)
    (ε : Fin K → Bool) : ∀ q ∈ (lacunaryCoeff A ε).support, 0 ≤ q := by
  intro q hq
  by_contra hneg
  refine Finsupp.mem_support_iff.1 hq ?_
  rw [lacunaryCoeff, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun k _ => Finsupp.single_eq_of_ne ?_
  have : (0 : ℤ) ≤ 2 ^ (k : ℕ) := by positivity
  omega

omit [Fintype n] [DecidableEq n] in
private theorem circPoly_lacunaryCoeff {K : ℕ} (A : Fin K → Matrix n n ℂ) (ε : Fin K → Bool)
    (t : UnitAddCircle) : circPoly (lacunaryCoeff A ε) t =
      ∑ k, coin (ε k) • fourier ((2 : ℤ) ^ (k : ℕ)) t • A k := by
  rw [circPoly, lacunaryCoeff, ← Finsupp.sum_finsetSum_index (fun _ => smul_zero _)
    fun _ _ _ => smul_add _ _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (Finsupp.sum_single_index ?_).trans (smul_comm _ _ _)
  exact smul_zero _

/-- The contraction principle: multiplying the `A_k` by the unimodular numbers `e_{2^k} (t)`. -/
private theorem avg_lacunary_le {q : ℝ≥0∞} (hq : 1 ≤ q) {K : ℕ} (A : Fin K → Matrix n n ℂ)
    (t : UnitAddCircle) :
    (avg fun ε : Fin K → Bool => complexSchattenNorm q (circPoly (lacunaryCoeff A ε) t)) ≤
      2 * avg fun ε : Fin K → Bool => complexSchattenNorm q (∑ k, coin (ε k) • A k) := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  have h := lpNorm_sum_coin_smul_le_two_mul (E := ComplexSchattenSpace q n n) le_rfl
    (c := fun k : Fin K => fourier ((2 : ℤ) ^ (k : ℕ)) t)
    (fun k => (norm_fourier_apply_eq_one _ _).le) fun k => ComplexSchattenSpace.ofMatrix (A k)
  have e (ε : Fin K → Bool) (B : Fin K → Matrix n n ℂ) :
      ‖∑ k, coin (ε k) • (ComplexSchattenSpace.ofMatrix (B k) : ComplexSchattenSpace q n n)‖ =
        complexSchattenNorm q (∑ k, coin (ε k) • B k) := by
    rw [← ComplexSchattenSpace.norm_ofMatrix, ofMatrix_sum_smul]
  simp only [SignCube.lpNorm, Real.rpow_one, div_one, ← map_smul, e] at h
  simpa only [circPoly_lacunaryCoeff] using h

/-- **The lower Khintchine inequality in the Schatten classes**, `1 ≤ p ≤ 2` (Lust-Piquard–Pisier
(1991), Corollary III.4, left-hand inequality, with signs; Pisier (1998), (8.4.4), left-hand
inequality), with a constant independent of `p` and of the size. -/
theorem rademacher_schatten_le : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ),
    1 ≤ p → p ≤ 2 → ∀ (K : ℕ) (A : Fin K → Matrix n n ℂ),
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k, A k = a k + b k) ∧
      complexSchattenNorm (ENNReal.ofReal p) (blockRow a) +
        complexSchattenNorm (ENNReal.ofReal p) (blockCol b) ≤
      M * avg fun ε : Fin K → Bool =>
        complexSchattenNorm (ENNReal.ofReal p) (∑ k, coin (ε k) • A k) := by
  obtain ⟨M, hM, hpaley⟩ := paley_schatten
  refine ⟨M * 2, by positivity, ?_⟩
  intro n _ _ p hp1 hp2 K A
  have h1p : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1
  have hp0 : ENNReal.ofReal p ≠ 0 := (zero_lt_one.trans_le h1p).ne'
  have hint (ε : Fin K → Bool) : Integrable (fun t =>
      complexSchattenNorm (ENNReal.ofReal p) (circPoly (lacunaryCoeff A ε) t)) haarAddCircle :=
    integrable_haar_of_continuous
      ((continuous_complexSchattenNorm h1p).comp (continuous_circPoly_matrix _))
  -- a choice of signs for which the integral is at most its average
  obtain ⟨ε, -, hε⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin K → Bool)))
    Finset.univ_nonempty
    (f := fun ε => ∫ t, complexSchattenNorm (ENNReal.ofReal p) (circPoly (lacunaryCoeff A ε) t)
      ∂haarAddCircle)
    (g := fun _ => avg fun η : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal p)
      (circPoly (lacunaryCoeff A η) t) ∂haarAddCircle) (by simp [avg, mul_div_cancel₀])
  -- the average over the signs, by the contraction principle
  have havg : (avg fun η : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal p)
      (circPoly (lacunaryCoeff A η) t) ∂haarAddCircle) ≤
      2 * avg fun η : Fin K → Bool =>
        complexSchattenNorm (ENNReal.ofReal p) (∑ k, coin (η k) • A k) := by
    rw [avg, ← integral_finsetSum _ fun ε _ => hint ε, ← integral_div]
    refine (integral_mono ?_ (integrable_const _) fun t => avg_lacunary_le h1p A t).trans ?_
    · exact (integrable_finsetSum _ fun ε _ => hint ε).div_const _
    · simp
  -- Paley's inequality for `f_ε`
  obtain ⟨a, b, hab, hle⟩ := hpaley n p hp1 hp2 (lacunaryCoeff A ε)
    (nonneg_of_mem_support_lacunaryCoeff A ε) K
  have hunit (k : Fin K) : ‖(coin (ε k) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_coin]
  refine ⟨fun k => (coin (ε k) : ℂ) • a k, fun k => (coin (ε k) : ℂ) • b k, fun k => ?_, ?_⟩
  · rw [← smul_add, ← hab k, lacunaryCoeff_two_pow, Complex.coe_smul, smul_smul, coin_mul_self,
      one_smul]
  · rw [complexSchattenNorm_blockRow_smul hp0 a hunit,
      complexSchattenNorm_blockCol_smul hp0 b hunit, mul_assoc]
    exact hle.trans (mul_le_mul_of_nonneg_left (hε.trans havg) hM.le)

end HarmonicAnalysis
