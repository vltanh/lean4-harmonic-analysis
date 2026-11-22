/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Hardy.RieszFactorization
import HarmonicAnalysis.VectorValued.LittlewoodPaley.CircleSigns
import BanachProbability.Noncommutative.ComplexSchattenUMD

/-!
# Paley's inequality in the Schatten classes

**Theorem** (`paley_schatten_of_isHardyOne`; F. Lust-Piquard and G. Pisier, *Non commutative
Khintchine and Paley inequalities*, Ark. Mat. 29 (1991), Theorem III.1 (i), p. 252, for the Paley
projection and `C_E = C_p`; for `p = 1`, Theorem II.1 a) (i), p. 248, without its constant). There
is an absolute constant `M` such that for `1 ≤ p ≤ 2`, in every size `n`, every function `f` of `H¹`
with values in `M_n (ℂ)` and every `K`,

`‖(f̂ (2^k))_{k < K}‖_{C_p (ℓ²_R) + C_p (ℓ²_L)} ≤ M ∫_𝕋 ‖f (t)‖_{S_p} dt`,

that is, `f̂ (2^k) = a_k + b_k` with
`‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M ∫ ‖f‖_{S_p}`; in particular for
analytic polynomials `f = Σ_{k ≥ 0} c_k e_k` with coefficients `c_k ∈ M_n (ℂ)` (`paley_schatten`).

The square functions are written as norms of block rows and block columns
(`BanachProbability.Schatten.Block`; (I.2), p. 245):
`‖blockRow a‖_{S_p} = ‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} = ‖Σ a_k a_kᴴ‖_{S_{p/2}}^{1/2}` and
`‖blockCol b‖_{S_p} = ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} = ‖Σ b_kᴴ b_k‖_{S_{p/2}}^{1/2}`.

## The proof

The proof is that of Theorem III.1 (pp. 249–250 and 252–253). By Sarason's theorem (1967), `f = g h`
with `g, h ∈ H²` and `‖f‖_{L¹ (C_p)} = ‖g‖_{L² (C_{2p})} ‖h‖_{L² (C_{2p})}`
(`exists_mul_eq_integral_complexSchattenNorm_eq`; (α), (β), p. 252). Splitting
`f̂ (2^k) = Σ ĝ (q) ĥ (2^k − q)` at `q = 2^{k−1}` gives `f̂ (2^k) = A_k + B_k` with
`A_k = ∫ g H_{2^k} e_{−2^k}` and `B_k = ∫ G_{2^k} h e_{−2^k}`. By Jensen's inequality in
`C_p (ℓ²_L)`, Hölder's inequality and the Cauchy–Schwarz inequality, the square function of the
`A_k` is at most the norm of `g` in `L² (𝕋; C_{2p})` times that of the square function of the
`H_{2^k} (t)`, for which (III.1) is proved: by (I.7), it is dominated by the Rademacher sums of the
`H_{2^k} (t)`, (III.2); and these are, for every choice of the signs `ε_k`, bounded by the norm of
`h` in `L² (𝕋; C_{2p})`, (III.3), because `C_{2p}` is a UMD space and
`Σ_k ε_k H_{2^k} = Σ_p a_p ĥ (p) e_p` with `a_p = Σ_{p ≤ 2^k ≤ 2p} ε_k`, a bounded multiplier by
McConnell's theorem (`exists_eLpNorm_blockSign_le`). Similarly for the `B_k`.

`M` does not depend on `p`, because the UMD constants of `C_{2p}`, `2 ≤ 2p ≤ 4`, are bounded.
(G. Pisier, *Non-commutative vector valued `L_p`-spaces and completely `p`-summing maps*, Astérisque
247 (1998), p. 106, attributes to Lust-Piquard and Pisier that the constant `A'` of the Khintchine
inequality (8.4.4) can be taken independent of `p`.)

Departures from the source:

* Only `E = ℓ^p` with `1 ≤ p ≤ 2`.
* The source treats general multipliers `H¹ → ℓ²`; here only the sequence `2^k` occurs. (For (III.3)
  it cites a version of the Marcinkiewicz multiplier theorem by Bourgain ([B2, Theorem 4] there),
  "see also [MC, Theorem 1.3]"; the second reference is the one followed here.)
* The source recalls (p. 251) that `C_{2p}` is UMD, with Cotlar's trick, interpolation and duality
  as a known argument. The fact is proved in BanachProbability by Randrianantoanina's theorem on
  noncommutative martingale transforms (`BanachProbability.umdConst_two_complexSchattenSpace_le`;
  J. Funct. Anal. 194 (2002)).
* The case `p = 1` is covered by the proof of Theorem III.1. The proof of Theorem II.1, with
  Parseval's identity in place of (III.2) and (III.3), is not followed, and its constant `1 + √2` is
  not obtained.
-/

@[expose] public section

open MeasureTheory AddCircle BanachProbability BanachProbability.SignCube
open scoped ENNReal Matrix

namespace HarmonicAnalysis

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

/-! ### Polynomials with prescribed coefficients -/

section Poly

variable {V : Type*} [AddCommMonoid V]

/-- The family `(v_p)_{p ∈ S}`, extended by zero. -/
private noncomputable def coeffOn (S : Finset ℕ) (v : ℤ → V) : ℤ →₀ V :=
  Finsupp.onFinset (S.map Nat.castEmbedding)
    (fun p => if p ∈ S.map Nat.castEmbedding then v p else 0) fun p hp => by
      by_contra h
      exact hp (ite_eq_right h)

private theorem coeffOn_apply (S : Finset ℕ) (v : ℤ → V) (p : ℕ) :
    coeffOn S v p = if p ∈ S then v p else 0 := by
  simp [coeffOn]

private theorem nonneg_of_mem_support_coeffOn {S : Finset ℕ} {v : ℤ → V} :
    ∀ k ∈ (coeffOn S v).support, 0 ≤ k := by
  intro k hk
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 (Finsupp.support_onFinset_subset hk)
  exact Int.natCast_nonneg p

private theorem circPoly_coeffOn [Module ℂ V] (S : Finset ℕ) (v : ℤ → V) (t : UnitAddCircle) :
    circPoly (coeffOn S v) t = ∑ p ∈ S, fourier (p : ℤ) t • v p := by
  rw [circPoly, coeffOn, Finsupp.onFinset_sum _ fun _ => smul_zero _, Finset.sum_map]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp [hp]

end Poly

omit [DecidableEq n] in
/-- Lust-Piquard–Pisier, p. 249: `(g h)^ (2^k) = A_k + B_k`, `A_k = ∫ g H_{2^k} e_{−2^k}`,
`B_k = ∫ G_{2^k} h e_{−2^k}`. -/
theorem matFourierCoeff_mul_two_pow {g h : UnitAddCircle → Matrix n n ℂ} (hg : IsHardyTwo g)
    (hh : IsHardyTwo h) (k : ℕ) :
    matFourierCoeff (fun t => g t * h t) (2 ^ k) =
      matFourierCoeff (fun t => g t * paleyBlockClosed h k t) (2 ^ k) +
        matFourierCoeff (fun t => paleyBlockOpen g k t * h t) (2 ^ k) := by
  have hH : paleyBlockClosed h k = circPoly (coeffOn _ (matFourierCoeff h)) :=
    funext fun t => (circPoly_coeffOn _ _ t).symm
  have hG : paleyBlockOpen g k = circPoly (coeffOn _ (matFourierCoeff g)) :=
    funext fun t => (circPoly_coeffOn _ _ t).symm
  have hk : (2 ^ k : ℤ) = ((2 ^ k : ℕ) : ℤ) := by push_cast; rfl
  rw [hH, hG, hk, matFourierCoeff_mul hg hh,
    matFourierCoeff_mul hg (isHardyTwo_circPoly nonneg_of_mem_support_coeffOn),
    matFourierCoeff_mul (isHardyTwo_circPoly nonneg_of_mem_support_coeffOn) hh,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq : q ≤ 2 ^ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  rw [← Nat.cast_sub hq, matFourierCoeff_circPoly, matFourierCoeff_circPoly, coeffOn_apply,
    coeffOn_apply]
  simp only [Finset.mem_filter, Finset.mem_Icc]
  -- the terms with `2 q ≤ 2^k` make up `A_k`, the others `B_k`
  by_cases h2 : 2 * q ≤ 2 ^ k
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), Matrix.zero_mul, add_zero]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), Matrix.mul_zero, zero_add]

/-! ### The multipliers of (III.3) -/

section Blocks

/-- The frequencies of `H_{2^k}`. -/
private def closedFreq (k : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (2 ^ k)).filter fun p => 2 ^ k ≤ 2 * p

/-- The frequencies of `G_{2^k}`. -/
private def openFreq (k : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (2 ^ k)).filter fun p => 2 ^ k < 2 * p

private theorem mem_closedFreq {p k : ℕ} :
    p ∈ closedFreq k ↔ p ≠ 0 ∧ k ∈ Finset.Icc (Nat.clog 2 p) (Nat.log 2 p + 1) := by
  rw [closedFreq, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc,
    Nat.clog_le_iff_le_pow one_lt_two]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    have hp : p ≠ 0 := by
      rintro rfl
      simp at h2
    refine ⟨hp, h1, ?_⟩
    have h3 : 2 ^ k ≤ 2 ^ (Nat.log 2 p + 1) := by
      have := Nat.lt_pow_succ_log_self one_lt_two p
      rw [pow_succ] at this ⊢
      cases k with
      | zero => simp [Nat.one_le_iff_ne_zero]
      | succ j =>
        have h4 : 2 ^ j ≤ p := by
          rw [pow_succ] at h2
          omega
        have := (Nat.le_log_iff_pow_le one_lt_two hp).2 h4
        rw [pow_succ]
        exact Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right two_pos this)
    exact (Nat.pow_le_pow_iff_right one_lt_two).1 h3
  · rintro ⟨hp, h1, h2⟩
    refine ⟨⟨Nat.zero_le _, h1⟩, ?_⟩
    calc 2 ^ k ≤ 2 ^ (Nat.log 2 p + 1) := Nat.pow_le_pow_right two_pos h2
      _ = 2 * 2 ^ Nat.log 2 p := by rw [pow_succ, mul_comm]
      _ ≤ 2 * p := Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hp)

private theorem mem_openFreq {p k : ℕ} : p ∈ openFreq k ↔ p ≠ 0 ∧ Nat.clog 2 p = k := by
  rw [openFreq, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    have hp : p ≠ 0 := by
      rintro rfl
      simp at h2
    refine ⟨hp, le_antisymm ((Nat.clog_le_iff_le_pow one_lt_two).2 h1) ?_⟩
    cases k with
    | zero => exact Nat.zero_le _
    | succ j =>
      refine (Nat.lt_clog_iff_pow_lt one_lt_two).2 ?_
      rw [pow_succ] at h2
      omega
  · rintro ⟨hp, rfl⟩
    refine ⟨⟨Nat.zero_le _, Nat.le_pow_clog one_lt_two p⟩, ?_⟩
    rcases Nat.lt_or_ge 1 p with h | h
    · obtain ⟨j, hj⟩ : ∃ j, Nat.clog 2 p = j + 1 :=
        Nat.exists_eq_succ_of_ne_zero (Nat.clog_pos one_lt_two h).ne'
      have h1 : 2 ^ j < p := (Nat.lt_clog_iff_pow_lt one_lt_two).1 (by omega)
      rw [hj, pow_succ]
      omega
    · have : p = 1 := by omega
      subst this
      simp

private theorem natCast_mem_map {p : ℕ} {S : Finset ℕ} :
    (p : ℤ) ∈ S.map Nat.castEmbedding ↔ p ∈ S :=
  Finset.mem_map' (f := Nat.castEmbedding)

/-- The signs `ε_ℓ`, `ℓ < K`, extended by `0`. -/
private def signExt {K : ℕ} (ε : Fin K → Bool) (ℓ : ℕ) : ℝ :=
  if h : ℓ < K then coin (ε ⟨ℓ, h⟩) else 0

private theorem signExt_mem {K : ℕ} (ε : Fin K → Bool) (ℓ : ℕ) :
    signExt ε ℓ = 1 ∨ signExt ε ℓ = 0 ∨ signExt ε ℓ = -1 := by
  rw [signExt]
  split_ifs with h
  · cases ε ⟨ℓ, h⟩ <;> simp
  · simp

private theorem signExt_coe {K : ℕ} (ε : Fin K → Bool) (k : Fin K) :
    signExt ε k = coin (ε k) := by
  simp [signExt]

private theorem sum_signExt {K : ℕ} (ε : Fin K → Bool) (s : Finset ℕ) :
    ∑ ℓ ∈ s, signExt ε ℓ = ∑ k : Fin K, if (k : ℕ) ∈ s then coin (ε k) else 0 := by
  have h1 : (∑ k : Fin K, if (k : ℕ) ∈ s then coin (ε k) else 0) =
      ∑ ℓ ∈ Finset.range K, if ℓ ∈ s then signExt ε ℓ else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun ℓ => if ℓ ∈ s then signExt ε ℓ else 0) K]
    simp only [signExt_coe]
  rw [h1, Finset.sum_ite_mem]
  refine (Finset.sum_subset Finset.inter_subset_right fun ℓ hℓ hℓ' => ?_).symm
  rw [signExt, dite_eq_right]
  intro h
  exact hℓ' (Finset.mem_inter.2 ⟨Finset.mem_range.2 h, hℓ⟩)

/-- `a_p = Σ_{p ≤ 2^ℓ ≤ 2p} ε_ℓ` (Lust-Piquard–Pisier, p. 253), in terms of the blocks `H_{2^ℓ}`. -/
private theorem closedBlockSign_signExt {K : ℕ} (ε : Fin K → Bool) (n : ℤ) :
    closedBlockSign (signExt ε) n =
      ∑ k : Fin K, if n ∈ (closedFreq k).map Nat.castEmbedding then coin (ε k) else 0 := by
  rcases le_or_gt n 0 with hn | hn
  · rw [closedBlockSign, ite_eq_right hn.not_gt]
    refine (Finset.sum_eq_zero fun k _ => ite_eq_right fun h => ?_).symm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 h
    exact (mem_closedFreq.1 hp).1 (by simpa using hn)
  · lift n to ℕ using hn.le
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hn
    rw [closedBlockSign, ite_eq_left hn, sum_signExt]
    refine Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
    rw [natCast_mem_map, mem_closedFreq, Int.toNat_natCast]
    exact (and_iff_right hn0).symm

/-- The same for the blocks `G_{2^ℓ}`. -/
private theorem rightBlockSign_signExt {K : ℕ} (ε : Fin K → Bool) (n : ℤ) :
    rightBlockSign (signExt ε) n =
      ∑ k : Fin K, if n ∈ (openFreq k).map Nat.castEmbedding then coin (ε k) else 0 := by
  rcases le_or_gt n 0 with hn | hn
  · rw [rightBlockSign, ite_eq_right hn.not_gt]
    refine (Finset.sum_eq_zero fun k _ => ite_eq_right fun h => ?_).symm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 h
    exact (mem_openFreq.1 hp).1 (by simpa using hn)
  · lift n to ℕ using hn.le
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hn
    rw [rightBlockSign, ite_eq_left hn, ← Finset.sum_singleton (signExt ε), sum_signExt]
    refine Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
    rw [natCast_mem_map, mem_openFreq, Finset.mem_singleton, Int.toNat_natCast, eq_comm]
    exact (and_iff_right hn0).symm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- `Σ ε_k H_{2^k} = Σ_p a_p ĥ (p) e_p` (Lust-Piquard–Pisier, p. 253), for blocks of frequencies. -/
private theorem sum_coin_smul_block (S : ℕ → Finset ℕ) {K : ℕ} (ε : Fin K → Bool) {a : ℤ → ℝ}
    (ha : ∀ n : ℤ, a n =
      ∑ k : Fin K, if n ∈ (S k).map Nat.castEmbedding then coin (ε k) else 0)
    (c : ℤ →₀ X) (t : UnitAddCircle) :
    ∑ k, coin (ε k) • ∑ p ∈ S k, fourier (p : ℤ) t • c p =
      circPoly (mulCoeff (fun n => (a n : ℂ)) c) t := by
  classical
  have h (k : Fin K) : ∑ p ∈ S k, fourier (p : ℤ) t • c p = ∑ n ∈ c.support,
      if n ∈ (S k).map Nat.castEmbedding then fourier n t • c n else 0 := by
    rw [Finset.sum_ite_mem]
    refine (Finset.sum_map (S k) Nat.castEmbedding fun n : ℤ => fourier n t • c n).symm.trans
      (Finset.sum_subset Finset.inter_subset_right fun n hn hn' => ?_).symm
    have h0 : c n = 0 := by
      by_contra h0
      exact hn' (Finset.mem_inter.2 ⟨Finsupp.mem_support_iff.2 h0, hn⟩)
    rw [h0, smul_zero]
  rw [circPoly_mulCoeff, Finsupp.sum]
  simp only [h, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ha, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [Complex.coe_smul, smul_comm]
  · simp

end Blocks

/-! ### Square norms of continuous functions -/

section Sq

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]

/-- The square of the `L²` norm of a continuous function. -/
private theorem eLpNorm_two_sq_eq {u : UnitAddCircle → X} (hu : Continuous u) :
    eLpNorm u (ENNReal.ofReal 2) haarAddCircle ^ (2 : ℝ) =
      ENNReal.ofReal (∫ t, ‖u t‖ ^ 2 ∂haarAddCircle) := by
  have hint : Integrable (fun t => ‖u t‖ ^ 2) haarAddCircle :=
    integrable_haar_of_continuous (hu.norm.pow 2)
  rw [eLpNorm_ofReal_rpow_eq_lintegral two_pos hu.aestronglyMeasurable,
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => sq_nonneg _)]
  refine lintegral_congr fun t => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]

/-- From norms to integrals of squares. -/
private theorem integral_sq_le_of_eLpNorm_le {u : UnitAddCircle → X} (hu : Continuous u)
    {v : UnitAddCircle → Y} (hv : Continuous v) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : eLpNorm u (ENNReal.ofReal 2) haarAddCircle ≤
      C * eLpNorm v (ENNReal.ofReal 2) haarAddCircle) :
    ∫ t, ‖u t‖ ^ 2 ∂haarAddCircle ≤ C.toReal ^ 2 * ∫ t, ‖v t‖ ^ 2 ∂haarAddCircle := by
  have h0 : 0 ≤ ∫ t, ‖v t‖ ^ 2 ∂haarAddCircle := integral_nonneg fun t => by positivity
  have h1 := ENNReal.rpow_le_rpow h (z := 2) (by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), eLpNorm_two_sq_eq hv, eLpNorm_two_sq_eq hu,
    ← ENNReal.ofReal_toReal hC, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)] at h1
  simpa using (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1

end Sq

/-! ### The blocks of functions in `H²` -/

section Hardy

variable {q : ℝ≥0∞}

variable [Fact (1 ≤ q)]

/-- The coefficients of the analytic polynomial `Σ_{0 ≤ p ≤ N} ĥ (p) e_p`. -/
private noncomputable def partialCoeff (q : ℝ≥0∞) (h : UnitAddCircle → Matrix n n ℂ) (N : ℕ) :
    ℤ →₀ ComplexSchattenSpace q n n :=
  coeffOn (Finset.range (N + 1)) fun p => ComplexSchattenSpace.ofMatrix (matFourierCoeff h p)

omit [Fact (1 ≤ q)] in
/-- For `h ∈ H²` this polynomial is the partial sum of the Fourier series of `h`. -/
private theorem norm_circPoly_partialCoeff {h : UnitAddCircle → Matrix n n ℂ} (hh : IsHardyTwo h)
    (N : ℕ) (t : UnitAddCircle) : ‖circPoly (partialCoeff q h N) t‖ = complexSchattenNorm q
      (∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t • matFourierCoeff h k) := by
  have h1 : (Finset.range (N + 1)).map Nat.castEmbedding ⊆ Finset.Icc (-N : ℤ) N := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hp
    rw [Finset.mem_range] at hr
    simp only [Nat.castEmbedding_apply, Finset.mem_Icc]
    omega
  rw [partialCoeff, circPoly_coeffOn, ← Finset.sum_subset h1, Finset.sum_map,
    ← ComplexSchattenSpace.norm_ofMatrix, map_sum]
  · simp only [map_smul]
    rfl
  · intro p hp hp'
    rw [hh.2 p, smul_zero]
    by_contra hp0
    rw [Finset.mem_Icc] at hp
    refine hp' (Finset.mem_map.2 ⟨p.toNat, Finset.mem_range.2 (by omega), ?_⟩)
    simp only [Nat.castEmbedding_apply]
    omega

/-- The blocks of this polynomial are those of `h`, if `N` is large. -/
private theorem norm_sum_block_partialCoeff {S : ℕ → Finset ℕ} (hS : ∀ k, ∀ p ∈ S k, p ≤ 2 ^ k)
    {K N : ℕ} (hN : 2 ^ K ≤ N) (h : UnitAddCircle → Matrix n n ℂ) (ε : Fin K → Bool)
    (t : UnitAddCircle) :
    ‖∑ k, coin (ε k) • ∑ p ∈ S k, fourier (p : ℤ) t • partialCoeff q h N p‖ =
      complexSchattenNorm q
        (∑ k, coin (ε k) • ∑ p ∈ S k, fourier (p : ℤ) t • matFourierCoeff h p) := by
  have hcoeff (k : Fin K) (p : ℕ) (hp : p ∈ S k) :
      partialCoeff q h N p = ComplexSchattenSpace.ofMatrix (matFourierCoeff h p) := by
    have h1 : 2 ^ (k : ℕ) ≤ 2 ^ K := Nat.pow_le_pow_right two_pos k.2.le
    rw [partialCoeff, coeffOn_apply, ite_eq_left]
    exact Finset.mem_range.2 (Nat.lt_succ_of_le ((hS k p hp).trans (h1.trans hN)))
  rw [← ComplexSchattenSpace.norm_ofMatrix, ofMatrix_sum_smul]
  simp only [map_sum, map_smul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun p hp => by rw [hcoeff k p hp]

/-- From polynomials to `H²`, by the convergence of the partial sums of the Fourier series of `h`.
-/
private theorem integral_block_le {S : ℕ → Finset ℕ} (hS : ∀ k, ∀ p ∈ S k, p ≤ 2 ^ k)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {K : ℕ} (ε : Fin K → Bool)
    (hle : ∀ c : ℤ →₀ ComplexSchattenSpace q n n,
      eLpNorm (fun t : UnitAddCircle => ∑ k, coin (ε k) • ∑ p ∈ S k, fourier (p : ℤ) t • c p)
          (ENNReal.ofReal 2) haarAddCircle ≤
        C * eLpNorm (circPoly c) (ENNReal.ofReal 2) haarAddCircle)
    {h : UnitAddCircle → Matrix n n ℂ} (hh : IsHardyTwo h) :
    ∫ t : UnitAddCircle, complexSchattenNorm q
        (∑ k, coin (ε k) • ∑ p ∈ S k, fourier (p : ℤ) t • matFourierCoeff h p) ^ 2
          ∂haarAddCircle ≤
      C.toReal ^ 2 * ∫ t, complexSchattenNorm q (h t) ^ 2 ∂haarAddCircle := by
  refine ge_of_tendsto ((tendsto_integral_norm_sq_partialSum (Fact.out (p := 1 ≤ q)) hh.1).const_mul
    (C.toReal ^ 2)) ?_
  filter_upwards [Filter.eventually_ge_atTop (2 ^ K)] with N hN
  have hcont : Continuous fun t : UnitAddCircle =>
      ∑ k, coin (ε k) • ∑ p ∈ S k, fourier (p : ℤ) t • partialCoeff q h N p :=
    continuous_finsetSum _ fun k _ =>
      (continuous_finsetSum _ fun p _ => (fourier _).continuous.smul continuous_const).const_smul _
  have key := integral_sq_le_of_eLpNorm_le hcont (continuous_circPoly (partialCoeff q h N)) hC
    (hle (partialCoeff q h N))
  simpa only [norm_sum_block_partialCoeff hS hN, norm_circPoly_partialCoeff hh] using key

end Hardy

/-- The `UMD_2` constants of the spaces `S_{2p}`, `1 ≤ p ≤ 2`, of all sizes are bounded. Departure
from the source (p. 251: Cotlar's identity, interpolation and duality show that `C_{2p}` is an
HT-space, hence UMD): the bound is that of `BanachProbability.umdConst_two_complexSchattenSpace_le`,
from the weak type `(1, 1)` inequality for noncommutative martingale transforms. -/
private theorem exists_isUMDBound : ∃ β : ℝ≥0∞, β ≠ ⊤ ∧ ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (p : ℝ),
    1 ≤ p → p ≤ 2 → q = ENNReal.ofReal (2 * p) → ∀ (n : Type) [Fintype n] [DecidableEq n],
      IsUMDBound (ComplexSchattenSpace q n n) 2 β := by
  obtain ⟨C, hC, hle⟩ := umdConst_two_complexSchattenSpace_le
  refine ⟨ENNReal.ofReal (C * 3), ENNReal.ofReal_ne_top, ?_⟩
  intro q _ p hp1 hp2 hq n _ _
  have hq1 : 1 < q := by
    rw [hq, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  refine (isUMDBound_umdConst one_lt_two).mono ((hle q hq1 (hq ▸ ENNReal.ofReal_ne_top) n).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC.le)))
  rw [hq, ENNReal.toReal_ofReal (by linarith), sub_le_iff_le_add, BanachProbability.pStar]
  refine max_le (by linarith) ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Lust-Piquard–Pisier, (III.3)**, p. 253, for the blocks `H_{2^k}` of `h ∈ H²`: for every choice
of the signs `ε_k`, `∫ ‖Σ ε_k H_{2^k}‖_{S_{2p}}² ≤ C ∫ ‖h‖_{S_{2p}}²` with an absolute constant `C`,
for `1 ≤ p ≤ 2` and all sizes. The multiplier is `a_p = Σ_{p ≤ 2^ℓ ≤ 2p} ε_ℓ`, bounded on
`L² (𝕋; C_{2p})` by McConnell's theorem (`exists_eLpNorm_blockSign_le`). -/
theorem exists_integral_paleyBlockClosed_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n]
    [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ (h : UnitAddCircle → Matrix n n ℂ), IsHardyTwo h →
    ∀ (K : ℕ) (ε : Fin K → Bool), ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
        (∑ k, coin (ε k) • paleyBlockClosed h k t) ^ 2 ∂haarAddCircle ≤
      C * ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ∂haarAddCircle := by
  obtain ⟨β, hβ, hUMD⟩ := exists_isUMDBound
  obtain ⟨C, hC, hle⟩ := exists_eLpNorm_blockSign_le
  refine ⟨(C β).toReal ^ 2 + 1, by positivity, ?_⟩
  intro n _ _ p hp1 hp2 h hh K ε
  have hfact : Fact (1 ≤ ENNReal.ofReal (2 * p)) := ⟨ENNReal.one_le_ofReal.2 (by linarith)⟩
  have hint : 0 ≤ ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ∂haarAddCircle :=
    integral_nonneg fun t => by positivity
  refine (integral_block_le (q := ENNReal.ofReal (2 * p)) (S := closedFreq)
    (fun k r hr => (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).2) (hC β hβ) ε
    (fun c => ?_) hh).trans (mul_le_mul_of_nonneg_right (by linarith) hint)
  rw [funext (sum_coin_smul_block closedFreq ε (closedBlockSign_signExt ε) c)]
  exact hle _ 2 one_lt_two β (hUMD _ p hp1 hp2 rfl n) _ (signExt_mem ε) _ (Or.inr (Or.inr rfl)) c

/-- **Lust-Piquard–Pisier, (III.3)**, p. 253, for the blocks `G_{2^k}` of `g ∈ H²`: for every choice
of the signs `ε_k`, `∫ ‖Σ ε_k G_{2^k}‖_{S_{2p}}² ≤ C ∫ ‖g‖_{S_{2p}}²` with an absolute constant `C`,
for `1 ≤ p ≤ 2` and all sizes. ("Similarly for the `G'_k s`", p. 252.) -/
theorem exists_integral_paleyBlockOpen_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n]
    [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ (g : UnitAddCircle → Matrix n n ℂ), IsHardyTwo g →
    ∀ (K : ℕ) (ε : Fin K → Bool), ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
        (∑ k, coin (ε k) • paleyBlockOpen g k t) ^ 2 ∂haarAddCircle ≤
      C * ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle := by
  obtain ⟨β, hβ, hUMD⟩ := exists_isUMDBound
  obtain ⟨C, hC, hle⟩ := exists_eLpNorm_blockSign_le
  refine ⟨(C β).toReal ^ 2 + 1, by positivity, ?_⟩
  intro n _ _ p hp1 hp2 g hg K ε
  have hfact : Fact (1 ≤ ENNReal.ofReal (2 * p)) := ⟨ENNReal.one_le_ofReal.2 (by linarith)⟩
  have hint : 0 ≤ ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle :=
    integral_nonneg fun t => by positivity
  refine (integral_block_le (q := ENNReal.ofReal (2 * p)) (S := openFreq)
    (fun k r hr => (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).2) (hC β hβ) ε
    (fun c => ?_) hg).trans (mul_le_mul_of_nonneg_right (by linarith) hint)
  rw [funext (sum_coin_smul_block openFreq ε (rightBlockSign_signExt ε) c)]
  exact hle _ 2 one_lt_two β (hUMD _ p hp1 hp2 rfl n) _ (signExt_mem ε) _ (Or.inr (Or.inl rfl)) c

/-! ### Jensen's and Hölder's inequalities -/

section Jensen

variable {l m o : Type*} [Fintype l] [Fintype m] [Fintype o] [DecidableEq o] {q : ℝ≥0∞}

/-- Jensen's inequality for the integral of a matrix-valued function. -/
private theorem complexSchattenNorm_integral_le (hq : 1 ≤ q) {F : UnitAddCircle → Matrix m o ℂ}
    (hF : ∀ i j, Integrable (fun t => F t i j) haarAddCircle) :
    complexSchattenNorm q (Matrix.of fun i j => ∫ t, F t i j ∂haarAddCircle) ≤
      ∫ t, complexSchattenNorm q (F t) ∂haarAddCircle := by
  classical
  have : Fact (1 ≤ q) := ⟨hq⟩
  have hint : ∫ t, (ComplexSchattenSpace.ofMatrix (F t) : ComplexSchattenSpace q m o)
      ∂haarAddCircle = ComplexSchattenSpace.ofMatrix
        (Matrix.of fun i j => ∫ t, F t i j ∂haarAddCircle) := by
    rw [funext fun t => ofMatrix_eq_sum (q := q) (F t), ofMatrix_eq_sum,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF i j).smul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hF i j).smul_const _]
    exact Finset.sum_congr rfl fun j _ => integral_smul_const _ _
  have key := norm_integral_le_integral_norm (μ := haarAddCircle)
    fun t => (ComplexSchattenSpace.ofMatrix (F t) : ComplexSchattenSpace q m o)
  rw [hint] at key
  exact key

/-- Jensen's, Hölder's and the Cauchy–Schwarz inequality:
`‖∫ P Q‖_{S_p} ≤ (∫ ‖P‖_{S_{2p}}²)^{1/2} (∫ ‖Q‖_{S_{2p}}²)^{1/2}`. -/
private theorem complexSchattenNorm_integral_mul_le [DecidableEq m] {p : ℝ} (hp : 1 ≤ p)
    {P : UnitAddCircle → Matrix l m ℂ} {Q : UnitAddCircle → Matrix m o ℂ}
    (hP : ∀ i j, MemLp (fun t => P t i j) 2 haarAddCircle)
    (hQ : ∀ i j, MemLp (fun t => Q t i j) 2 haarAddCircle) :
    complexSchattenNorm (ENNReal.ofReal p)
        (Matrix.of fun i j => ∫ t, (P t * Q t) i j ∂haarAddCircle) ≤
      √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (P t) ^ 2 ∂haarAddCircle) *
        √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (Q t) ^ 2 ∂haarAddCircle) := by
  have h1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have h2 : 1 ≤ ENNReal.ofReal (2 * p) := ENNReal.one_le_ofReal.2 (by linarith)
  have hPQ (i : l) (j : o) : Integrable (fun t => (P t * Q t) i j) haarAddCircle := by
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun k _ => (hP i k).integrable_mul (hQ k j)
  have hP' := memLp_complexSchattenNorm h2 hP
  have hQ' := memLp_complexSchattenNorm h2 hQ
  have hint : Integrable (fun t => complexSchattenNorm (ENNReal.ofReal p) (P t * Q t))
      haarAddCircle :=
    memLp_one_iff_integrable.1 (memLp_complexSchattenNorm h1 fun i j =>
      memLp_one_iff_integrable.2 (hPQ i j))
  calc _ ≤ ∫ t, complexSchattenNorm (ENNReal.ofReal p) (P t * Q t) ∂haarAddCircle :=
        complexSchattenNorm_integral_le h1 hPQ
    _ ≤ ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (P t) *
          complexSchattenNorm (ENNReal.ofReal (2 * p)) (Q t) ∂haarAddCircle :=
        integral_mono hint (hP'.integrable_mul hQ') fun t =>
          complexSchattenNorm_mul_le (by linarith) (by linarith) (by field_simp; norm_num) _ _
    _ ≤ _ := by
        have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := haarAddCircle) (p := 2) (q := 2)
          (Real.HolderConjugate.two_two)
          (f := fun t => complexSchattenNorm (ENNReal.ofReal (2 * p)) (P t))
          (g := fun t => complexSchattenNorm (ENNReal.ofReal (2 * p)) (Q t))
          (ae_of_all _ fun t => complexSchattenNorm_nonneg _ _)
          (ae_of_all _ fun t => complexSchattenNorm_nonneg _ _) (by simpa using hP')
          (by simpa using hQ')
        simpa only [Real.sqrt_eq_rpow, Real.rpow_ofNat] using this

end Jensen

/-! ### The square functions of the two parts -/

section SquareFunction

omit [Fintype n] [DecidableEq n] in
private theorem continuous_paleyBlockClosed (h : UnitAddCircle → Matrix n n ℂ) (k : ℕ) :
    Continuous (paleyBlockClosed h k) :=
  continuous_finsetSum _ fun _ _ => (fourier _).continuous.smul continuous_const

omit [Fintype n] [DecidableEq n] in
private theorem continuous_paleyBlockOpen (g : UnitAddCircle → Matrix n n ℂ) (k : ℕ) :
    Continuous (paleyBlockOpen g k) :=
  continuous_finsetSum _ fun _ _ => (fourier _).continuous.smul continuous_const

/-- (III.2), integrated. -/
private theorem integral_sq_le_avg {q : ℝ} (hq : 1 ≤ q) {K : ℕ}
    {U : Fin K → UnitAddCircle → Matrix n n ℂ} (hU : ∀ k, Continuous (U k)) {N : UnitAddCircle → ℝ}
    (hN : Continuous N) (hle : ∀ t, N t ^ 2 ≤ avg fun ε : Fin K → Bool =>
      complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • U k t) ^ 2) :
    ∫ t, N t ^ 2 ∂haarAddCircle ≤ avg fun ε : Fin K → Bool =>
      ∫ t, complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • U k t) ^ 2 ∂haarAddCircle := by
  have hsum (ε : Fin K → Bool) : Continuous fun t => ∑ k, coin (ε k) • U k t :=
    continuous_finsetSum _ fun k _ => (hU k).const_smul (coin (ε k))
  have hcont (ε : Fin K → Bool) : Continuous fun t =>
      complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • U k t) :=
    (continuous_complexSchattenNorm (ENNReal.one_le_ofReal.2 hq)).comp (hsum ε)
  have hint (ε : Fin K → Bool) : Integrable (fun t =>
      complexSchattenNorm (ENNReal.ofReal q) (∑ k, coin (ε k) • U k t) ^ 2) haarAddCircle :=
    integrable_haar_of_continuous ((hcont ε).pow 2)
  rw [avg, ← integral_finsetSum _ fun ε _ => hint ε, ← integral_div]
  refine integral_mono (integrable_haar_of_continuous (hN.pow 2)) ?_ fun t => ?_
  · exact (integrable_finsetSum _ fun ε _ => hint ε).div_const _
  · exact hle t

/-- (III.2), integrated, row form. -/
private theorem integral_blockRow_sq_le {q : ℝ} (hq : 2 ≤ q) {K : ℕ}
    {U : Fin K → UnitAddCircle → Matrix n n ℂ} (hU : ∀ k, Continuous (U k)) :
    ∫ t, complexSchattenNorm (ENNReal.ofReal q) (blockRow fun k => U k t) ^ 2 ∂haarAddCircle ≤
      avg fun ε : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal q)
        (∑ k, coin (ε k) • U k t) ^ 2 ∂haarAddCircle := by
  have hrow : Continuous fun t => blockRow fun k => U k t :=
    continuous_matrix fun i p => (hU p.1).matrix_elem i p.2
  have hq1 : 1 ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 (by linarith)
  have hN := (continuous_complexSchattenNorm hq1).comp hrow
  exact integral_sq_le_avg (by linarith) hU hN fun t =>
    complexSchattenNorm_blockRow_sq_le_avg hq fun k => U k t

/-- (III.2), integrated, column form. -/
private theorem integral_blockCol_sq_le {q : ℝ} (hq : 2 ≤ q) {K : ℕ}
    {U : Fin K → UnitAddCircle → Matrix n n ℂ} (hU : ∀ k, Continuous (U k)) :
    ∫ t, complexSchattenNorm (ENNReal.ofReal q) (blockCol fun k => U k t) ^ 2 ∂haarAddCircle ≤
      avg fun ε : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal q)
        (∑ k, coin (ε k) • U k t) ^ 2 ∂haarAddCircle := by
  have hcol : Continuous fun t => blockCol fun k => U k t :=
    continuous_matrix fun p j => (hU p.1).matrix_elem p.2 j
  have hq1 : 1 ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 (by linarith)
  have hN := (continuous_complexSchattenNorm hq1).comp hcol
  exact integral_sq_le_avg (by linarith) hU hN fun t =>
    complexSchattenNorm_blockCol_sq_le_avg hq fun k => U k t

/-- The first part of the proof of (γ), p. 250, with the norms of Theorem III.1, for the
coefficients `∫ g U_k e_{−m_k}`: by Jensen's, Hölder's and the Cauchy–Schwarz inequality, the row
square function is at most `(∫ ‖g‖_{S_{2p}}²)^{1/2} (∫ ‖Σ U_k U_kᴴ‖_{S_p})^{1/2}`. -/
private theorem complexSchattenNorm_blockRow_matFourierCoeff_le {p : ℝ} (hp : 1 ≤ p)
    {g : UnitAddCircle → Matrix n n ℂ} (hg : ∀ i j, MemLp (fun t => g t i j) 2 haarAddCircle)
    {K : ℕ} {U : Fin K → UnitAddCircle → Matrix n n ℂ} (hU : ∀ k, Continuous (U k))
    (m : Fin K → ℤ) :
    complexSchattenNorm (ENNReal.ofReal p)
        (blockRow fun k => matFourierCoeff (fun t => g t * U k t) (m k)) ≤
      √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle) *
        √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (blockRow fun k => U k t) ^ 2
          ∂haarAddCircle) := by
  have hq0 : ENNReal.ofReal (2 * p) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    linarith
  let Q (t : UnitAddCircle) : Matrix n (Fin K × n) ℂ :=
    blockRow fun k => fourier (-m k) t • U k t
  have hQ : Continuous Q := continuous_matrix fun i r =>
    ((fourier (-m r.1)).continuous.smul (hU r.1)).matrix_elem i r.2
  have e : (blockRow fun k => matFourierCoeff (fun t => g t * U k t) (m k)) =
      Matrix.of fun i j => ∫ t, (g t * Q t) i j ∂haarAddCircle := by
    ext i ⟨k, j⟩
    simp only [Q, mul_blockRow, Matrix.mul_smul]
    rfl
  have hQn (t : UnitAddCircle) : complexSchattenNorm (ENNReal.ofReal (2 * p)) (Q t) =
      complexSchattenNorm (ENNReal.ofReal (2 * p)) (blockRow fun k => U k t) :=
    complexSchattenNorm_blockRow_smul hq0 _ fun k => norm_fourier_apply_eq_one _ _
  rw [e]
  refine (complexSchattenNorm_integral_mul_le hp hg (memLp_entry_of_continuous hQ)).trans_eq ?_
  simp only [hQn]

/-- The first part of the proof of (δ), p. 250, with the norms of Theorem III.1, for the
coefficients `∫ U_k h e_{−m_k}`: by Jensen's, Hölder's and the Cauchy–Schwarz inequality, the column
square function is at most `(∫ ‖Σ U_kᴴ U_k‖_{S_p})^{1/2} (∫ ‖h‖_{S_{2p}}²)^{1/2}`. -/
private theorem complexSchattenNorm_blockCol_matFourierCoeff_le {p : ℝ} (hp : 1 ≤ p)
    {h : UnitAddCircle → Matrix n n ℂ} (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle)
    {K : ℕ} {U : Fin K → UnitAddCircle → Matrix n n ℂ} (hU : ∀ k, Continuous (U k))
    (m : Fin K → ℤ) :
    complexSchattenNorm (ENNReal.ofReal p)
        (blockCol fun k => matFourierCoeff (fun t => U k t * h t) (m k)) ≤
      √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (blockCol fun k => U k t) ^ 2
          ∂haarAddCircle) *
        √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ∂haarAddCircle) := by
  have hq0 : ENNReal.ofReal (2 * p) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    linarith
  let P (t : UnitAddCircle) : Matrix (Fin K × n) n ℂ :=
    blockCol fun k => fourier (-m k) t • U k t
  have hP : Continuous P := continuous_matrix fun r j =>
    ((fourier (-m r.1)).continuous.smul (hU r.1)).matrix_elem r.2 j
  have e : (blockCol fun k => matFourierCoeff (fun t => U k t * h t) (m k)) =
      Matrix.of fun i j => ∫ t, (P t * h t) i j ∂haarAddCircle := by
    ext ⟨k, i⟩ j
    simp only [P, blockCol_mul, Matrix.smul_mul]
    rfl
  have hPn (t : UnitAddCircle) : complexSchattenNorm (ENNReal.ofReal (2 * p)) (P t) =
      complexSchattenNorm (ENNReal.ofReal (2 * p)) (blockCol fun k => U k t) :=
    complexSchattenNorm_blockCol_smul hq0 _ fun k => norm_fourier_apply_eq_one _ _
  rw [e]
  refine (complexSchattenNorm_integral_mul_le hp (memLp_entry_of_continuous hP) hh).trans_eq ?_
  simp only [hPn]

private theorem avg_le_of_forall {K : ℕ} {f : (Fin K → Bool) → ℝ} {C : ℝ} (h : ∀ ε, f ε ≤ C) :
    avg f ≤ C :=
  (avg_mono h).trans_eq (avg_const C)

/-- Lust-Piquard–Pisier, (III.1), p. 252, for the Paley projection and `C_E = C_p`:
`∫ ‖Σ H_{2^k} H_{2^k}ᴴ‖_{S_p} ≤ C ∫ ‖h‖_{S_{2p}}²`, by (III.2) and (III.3). -/
private theorem exists_integral_blockRow_paleyBlockClosed_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type)
    [Fintype n] [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ (h : UnitAddCircle → Matrix n n ℂ),
    IsHardyTwo h → ∀ K : ℕ, ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
        (blockRow fun k : Fin K => paleyBlockClosed h k t) ^ 2 ∂haarAddCircle ≤
      C * ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ∂haarAddCircle := by
  obtain ⟨C, hC, hle⟩ := exists_integral_paleyBlockClosed_le
  exact ⟨C, hC, fun n _ _ p hp1 hp2 h hh K => (integral_blockRow_sq_le (by linarith) fun k =>
    continuous_paleyBlockClosed h k).trans (avg_le_of_forall (hle n p hp1 hp2 h hh K))⟩

/-- Lust-Piquard–Pisier, (III.1), p. 252, "similarly for the `G'_k s`":
`∫ ‖Σ G_{2^k}ᴴ G_{2^k}‖_{S_p} ≤ C ∫ ‖g‖_{S_{2p}}²`. -/
private theorem exists_integral_blockCol_paleyBlockOpen_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type)
    [Fintype n] [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ (g : UnitAddCircle → Matrix n n ℂ),
    IsHardyTwo g → ∀ K : ℕ, ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
        (blockCol fun k : Fin K => paleyBlockOpen g k t) ^ 2 ∂haarAddCircle ≤
      C * ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle := by
  obtain ⟨C, hC, hle⟩ := exists_integral_paleyBlockOpen_le
  exact ⟨C, hC, fun n _ _ p hp1 hp2 g hg K => (integral_blockCol_sq_le (by linarith) fun k =>
    continuous_paleyBlockOpen g k).trans (avg_le_of_forall (hle n p hp1 hp2 g hg K))⟩

end SquareFunction

/-! ### Paley's inequality -/

/-- Lust-Piquard–Pisier, (α) and (β), p. 252, for `C_E = C_p`: `f ∈ H¹` is a product `f = g h` of
functions of `H²` such that `‖f‖_{H¹ (C_p)} = ‖g‖_{H² (C_{2p})} ‖h‖_{H² (C_{2p})}`. These are the
factors of Sarason's theorem (`exists_mul_eq_of_isHardyOne`). (The source cites "[S, Theorem 4 and
proof p. 204]" — Sarason's article ends on p. 203 — and (I.1). Here the equality comes from the two
identities of Theorem 4, for every `0 < p < ∞`.) -/
theorem exists_mul_eq_integral_complexSchattenNorm_eq {p : ℝ} (hp : 0 < p)
    {f : UnitAddCircle → Matrix n n ℂ} (hf : IsHardyOne f) :
    ∃ g h : UnitAddCircle → Matrix n n ℂ, IsHardyTwo g ∧ IsHardyTwo h ∧
      (∀ᵐ t ∂haarAddCircle, f t = g t * h t) ∧
      ∫ t, complexSchattenNorm (ENNReal.ofReal p) (f t) ∂haarAddCircle =
        √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle) *
          √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ∂haarAddCircle) := by
  obtain ⟨g, h, hg, hh, hgh⟩ := exists_mul_eq_of_isHardyOne hf
  have key := hgh.mono fun t ht => complexSchattenNorm_sq_of_factorization hp ht.2.1 ht.2.2
  refine ⟨g, h, hg, hh, hgh.mono fun t ht => ht.1, ?_⟩
  rw [integral_congr_ae (key.mono fun t ht => ht.1), integral_congr_ae (key.mono fun t ht => ht.2),
    Real.mul_self_sqrt (integral_nonneg fun t => complexSchattenNorm_nonneg _ _)]

/-- **Paley's inequality in the Schatten classes** (Lust-Piquard–Pisier (1991), Theorem III.1 (i)
for the Paley projection and `C_p`), for functions of `H¹`, with a constant independent of
`1 ≤ p ≤ 2` and of the size. -/
theorem paley_schatten_of_isHardyOne : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n]
    (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ f : UnitAddCircle → Matrix n n ℂ, IsHardyOne f → ∀ K : ℕ,
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k : Fin K, matFourierCoeff f (2 ^ (k : ℕ)) = a k + b k) ∧
      complexSchattenNorm (ENNReal.ofReal p) (blockRow a) +
        complexSchattenNorm (ENNReal.ofReal p) (blockCol b) ≤
      M * ∫ t, complexSchattenNorm (ENNReal.ofReal p) (f t) ∂haarAddCircle := by
  obtain ⟨C₁, hC₁, hclosed⟩ := exists_integral_blockRow_paleyBlockClosed_le
  obtain ⟨C₂, hC₂, hopen⟩ := exists_integral_blockCol_paleyBlockOpen_le
  refine ⟨√C₁ + √C₂, by positivity, ?_⟩
  intro n _ _ p hp1 hp2 f hf K
  -- `f = g h`, (α) and (β)
  obtain ⟨g, h, hg, hh, hfac, hβ⟩ := exists_mul_eq_integral_complexSchattenNorm_eq
    (one_pos.trans_le hp1) hf
  refine ⟨fun k => matFourierCoeff (fun t => g t * paleyBlockClosed h k t) (2 ^ (k : ℕ)),
    fun k => matFourierCoeff (fun t => paleyBlockOpen g k t * h t) (2 ^ (k : ℕ)), fun k => ?_, ?_⟩
  · -- `f̂ (2^k) = A_k + B_k`
    rw [← matFourierCoeff_mul_two_pow hg hh, ← matFourierCoeff_congr_ae hfac]
  rw [add_mul, hβ]
  refine add_le_add ?_ ?_
  · -- the `A_k`: (γ) for the norms of Theorem III.1
    have hA := complexSchattenNorm_blockRow_matFourierCoeff_le hp1 hg.1
      (fun k : Fin K => continuous_paleyBlockClosed h k) fun k => 2 ^ (k : ℕ)
    refine hA.trans ((mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hclosed n p hp1 hp2 h hh K)) (Real.sqrt_nonneg _)).trans_eq ?_)
    rw [Real.sqrt_mul hC₁.le, mul_left_comm]
  · -- the `B_k`: (δ) for the norms of Theorem III.1
    have hB := complexSchattenNorm_blockCol_matFourierCoeff_le hp1 hh.1
      (fun k : Fin K => continuous_paleyBlockOpen g k) fun k => 2 ^ (k : ℕ)
    refine hB.trans ((mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (hopen n p hp1 hp2 g hg K)) (Real.sqrt_nonneg _)).trans_eq ?_)
    rw [Real.sqrt_mul hC₂.le, mul_assoc]

/-- Paley's inequality in the Schatten classes (`paley_schatten_of_isHardyOne`) for analytic
polynomials. -/
theorem paley_schatten : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ), 1 ≤ p →
    p ≤ 2 → ∀ (c : ℤ →₀ Matrix n n ℂ), (∀ k ∈ c.support, 0 ≤ k) → ∀ K : ℕ,
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k : Fin K, c (2 ^ (k : ℕ)) = a k + b k) ∧
      complexSchattenNorm (ENNReal.ofReal p) (blockRow a) +
        complexSchattenNorm (ENNReal.ofReal p) (blockCol b) ≤
      M * ∫ t, complexSchattenNorm (ENNReal.ofReal p) (circPoly c t) ∂haarAddCircle := by
  obtain ⟨M, hM, h⟩ := paley_schatten_of_isHardyOne
  refine ⟨M, hM, fun n _ _ p hp1 hp2 c hc K => ?_⟩
  simpa only [matFourierCoeff_circPoly] using
    h n p hp1 hp2 _ (isHardyTwo_circPoly hc).isHardyOne K

end HarmonicAnalysis
