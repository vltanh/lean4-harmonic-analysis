module

public import VectorValuedHarmonicAnalysis.Hardy.RieszFactorization
import BanachProbability.Noncommutative.ComplexSchattenUMD

/-!
# Paley's inequality in the Schatten classes

**Theorem** (`paley_schatten`; F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley
inequalities*, Ark. Mat. 29 (1991), Theorem III.1 (i), p. 252, for the Paley projection and
`C_E = C_p`; for `p = 1`, Theorem II.1 a) (i), p. 248, without its constant). There is an absolute
constant `M` such that for `1 ≤ p ≤ 2`, in every size `n`, every analytic polynomial
`f = Σ_{k ≥ 0} c_k e_k` with coefficients `c_k ∈ M_n (ℂ)` and every `K`,

`‖(c_{2^k})_{k < K}‖_{C_p (ℓ²_R) + C_p (ℓ²_L)} ≤ M ∫_𝕋 ‖f (t)‖_{S_p} dt`,

that is, `c_{2^k} = a_k + b_k` with
`‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M ∫ ‖f‖_{S_p}`.

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
`H_{2^k} (t)`. By (I.7), the latter is dominated by the Rademacher sums of the `H_{2^k} (t)`,
(III.2); and these are bounded by the norm of `h` in `L² (𝕋; C_{2p})`, (III.3), because `C_{2p}` is
a UMD space. Similarly for the `B_k`.

`M` does not depend on `p`, because the UMD constants of `C_{2p}`, `2 ≤ 2p ≤ 4`, are bounded.
(G. Pisier, *Non-commutative vector valued `L_p`-spaces and completely `p`-summing maps*, Astérisque
247 (1998), p. 106, attributes to Lust-Piquard and Pisier that the constant `A'` of the Khintchine
inequality (8.4.4) can be taken independent of `p`.)

Departures from the source:

* (III.3) is proved only on average over the signs, which is all that (III.2) uses
  (`exists_avg_integral_paleyBlockClosed_le`, `exists_avg_integral_paleyBlockOpen_le`). The source
  proves it for every choice of the signs, by Bourgain's multiplier theorem ([B2, Theorem 4] there).
  Here it follows from the Littlewood–Paley inequality (Hytönen–van Neerven–Veraar–Weis, *Analysis
  in Banach spaces I* (2016), Theorem 5.7.10; `eLpNormRad_dyadicBlock_succ_le`) and the randomised
  boundedness of single frequencies (`eLpNormRad_singleFrequency_le`): the blocks `[2^{k−1}, 2^k]`
  and `(2^{k−1}, 2^k]` of the source differ from the dyadic blocks `[2^{k−1}, 2^k)` by one and two
  frequencies. The source treats general multipliers `H¹ → ℓ²`; here only the sequence `2^k` occurs.
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

private theorem trigPoly_coeffOn [Module ℂ V] (S : Finset ℕ) (v : ℤ → V) (t : UnitAddCircle) :
    trigPoly (coeffOn S v) t = ∑ p ∈ S, fourier (p : ℤ) t • v p := by
  rw [trigPoly, coeffOn, Finsupp.onFinset_sum _ fun _ => smul_zero _, Finset.sum_map]
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
  have hH : paleyBlockClosed h k = trigPoly (coeffOn _ (matFourierCoeff h)) :=
    funext fun t => (trigPoly_coeffOn _ _ t).symm
  have hG : paleyBlockOpen g k = trigPoly (coeffOn _ (matFourierCoeff g)) :=
    funext fun t => (trigPoly_coeffOn _ _ t).symm
  have hk : (2 ^ k : ℤ) = ((2 ^ k : ℕ) : ℤ) := by push_cast; rfl
  rw [hH, hG, hk, matFourierCoeff_mul hg hh,
    matFourierCoeff_mul hg (isHardyTwo_trigPoly nonneg_of_mem_support_coeffOn),
    matFourierCoeff_mul (isHardyTwo_trigPoly nonneg_of_mem_support_coeffOn) hh,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq : q ≤ 2 ^ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  rw [← Nat.cast_sub hq, matFourierCoeff_trigPoly, matFourierCoeff_trigPoly, coeffOn_apply,
    coeffOn_apply]
  simp only [Finset.mem_filter, Finset.mem_Icc]
  -- the terms with `2 q ≤ 2^k` make up `A_k`, the others `B_k`
  by_cases h2 : 2 * q ≤ 2 ^ k
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), Matrix.zero_mul, add_zero]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), Matrix.mul_zero, zero_add]

/-! ### Littlewood–Paley for the blocks -/

section Blocks

/-- The frequencies of `H_{2^k}`. -/
private def closedFreq (k : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (2 ^ k)).filter fun p => 2 ^ k ≤ 2 * p

/-- The frequencies of `G_{2^k}`. -/
private def openFreq (k : ℕ) : Finset ℕ :=
  (Finset.Icc 0 (2 ^ k)).filter fun p => 2 ^ k < 2 * p

/-- The frequencies of `H_{2^{j+1}}` are those of the dyadic block `[2^j, 2^{j+1})` and `2^{j+1}`.
-/
private theorem closedFreq_succ (j : ℕ) :
    closedFreq (j + 1) = insert (2 ^ (j + 1)) (Finset.Ico (2 ^ j) (2 ^ (j + 1))) := by
  ext p
  simp only [closedFreq, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico,
    pow_succ]
  have : 0 < 2 ^ j := by positivity
  omega

private theorem closedFreq_zero : closedFreq 0 = {1} := by
  decide

/-- The frequencies of `G_{2^{j+1}}` and `2^j` are those of `H_{2^{j+1}}`. -/
private theorem insert_openFreq_succ (j : ℕ) :
    insert (2 ^ j) (openFreq (j + 1)) = closedFreq (j + 1) := by
  ext p
  simp only [closedFreq, openFreq, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, pow_succ]
  have : 0 < 2 ^ j := by positivity
  omega

private theorem openFreq_zero : openFreq 0 = {1} := by
  decide

/-- The dyadic block `[2^j, 2^{j+1})`, as a set of natural numbers. -/
private theorem mem_dyadicBlock_succ (q : ℤ) (j : ℕ) : q ∈ dyadicBlock ((j : ℕ) + 1) ↔
    q ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).map Nat.castEmbedding := by
  have h1 : ((j : ℤ) + 1).natAbs = j + 1 := by omega
  rw [dyadicBlock, ite_eq_right (by omega), ite_eq_left (by omega), h1, Set.mem_Ico, Finset.mem_map]
  simp only [add_tsub_cancel_right, Finset.mem_Ico, Nat.castEmbedding_apply]
  constructor
  · rintro ⟨h2, h3⟩
    have hq : 0 ≤ q := le_trans (by positivity) h2
    lift q to ℕ using hq
    exact ⟨q, ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩, rfl⟩
  · rintro ⟨p, ⟨h2, h3⟩, rfl⟩
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- The block `Δ̃_{j+1} f`, as a sum over the natural numbers of `[2^j, 2^{j+1})`. -/
private theorem trigBlock_dyadicBlock_succ {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (c : ℤ →₀ V) (j : ℕ) (t : UnitAddCircle) :
    trigBlock (dyadicBlock ((j : ℕ) + 1)) c t =
      ∑ p ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) : Finset ℕ), fourier (p : ℤ) t • c p := by
  classical
  rw [trigBlock, trigPoly, Finsupp.sum_of_support_subset
    (s := (Finset.Ico (2 ^ j) (2 ^ (j + 1))).map Nat.castEmbedding) _ _ _ fun _ _ => smul_zero _,
    Finset.sum_map]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finsupp.filter_apply_pos]
    · rfl
    · exact (mem_dyadicBlock_succ _ _).2 (Finset.mem_map_of_mem _ hp)
  · intro q hq
    rw [Finsupp.support_filter, Finset.mem_filter] at hq
    exact (mem_dyadicBlock_succ q j).1 hq.2

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The term `ĥ (2^j) e_{2^j}`. -/
private noncomputable def freqTerm (c : ℤ →₀ X) (j : ℕ) (t : UnitAddCircle) : X :=
  fourier ((2 ^ j : ℕ) : ℤ) t • c ((2 ^ j : ℕ) : ℤ)

/-- The family `(0, u_0, u_1, …)`. -/
private def prev (u : ℕ → UnitAddCircle → X) (k : ℕ) (t : UnitAddCircle) : X :=
  if k = 0 then 0 else u (k - 1) t

omit [NormedSpace ℂ X] in
private theorem aestronglyMeasurable_prev {u : ℕ → UnitAddCircle → X}
    (hu : ∀ k, AEStronglyMeasurable (u k) haarAddCircle) (k : ℕ) :
    AEStronglyMeasurable (prev u k) haarAddCircle := by
  by_cases hk : k = 0
  · subst hk
    exact aestronglyMeasurable_const
  · have : prev u k = u (k - 1) := funext fun t => ite_eq_right hk
    rw [this]
    exact hu _

/-- A Rademacher sum does not increase when the terms are shifted by one. -/
private theorem eLpNormRad_prev_le {p : ℝ} (hp : 1 ≤ p) {u : ℕ → UnitAddCircle → X}
    (hu : ∀ k, AEStronglyMeasurable (u k) haarAddCircle) (K : ℕ) :
    eLpNormRad (fun k : Fin K => prev u k) p haarAddCircle ≤
      eLpNormRad (fun k : Fin K => u k) p haarAddCircle := by
  cases K with
  | zero =>
    have : (fun k : Fin 0 => prev u k) = fun k : Fin 0 => u k := funext fun k => k.elim0
    rw [this]
  | succ K =>
    have hσ : Function.Injective fun k : Fin (K + 1) => k - 1 := fun a b h => by simpa using h
    have h1 := eLpNormRad_comp_le hp hσ (f := fun k : Fin (K + 1) => u k) fun k => hu k
    have h2 := eLpNormRad_indicator_le hp {0}ᶜ
      (f := fun k : Fin (K + 1) => u (k - 1 : Fin (K + 1))) fun k => hu _
    refine le_trans (le_of_eq ?_) (h2.trans h1)
    congr 1
    funext k
    by_cases hk : k = 0
    · subst hk
      funext t
      simp [prev]
    · rw [Set.indicator_of_mem (by simpa using hk)]
      funext t
      have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
      simp [prev, this, Fin.coe_sub_one, hk]

/-- `H_{2^k} = Δ̃_k f + c_{2^k} e_{2^k}`, without the first term for `k = 0`. -/
private theorem sum_closedFreq (c : ℤ →₀ X) (k : ℕ) (t : UnitAddCircle) :
    ∑ p ∈ closedFreq k, fourier (p : ℤ) t • c p =
      prev (fun j => trigBlock (dyadicBlock ((j : ℕ) + 1)) c) k t + freqTerm c k t := by
  cases k with
  | zero => simp [closedFreq_zero, prev, freqTerm]
  | succ j =>
    rw [closedFreq_succ, Finset.sum_insert (by simp), add_comm]
    simp [prev, freqTerm, trigBlock_dyadicBlock_succ]

/-- `G_{2^k} = Δ̃_k f + c_{2^k} e_{2^k} − c_{2^{k−1}} e_{2^{k−1}}`, without the first and the last
term for `k = 0`. -/
private theorem sum_openFreq (c : ℤ →₀ X) (k : ℕ) (t : UnitAddCircle) :
    ∑ p ∈ openFreq k, fourier (p : ℤ) t • c p =
      prev (fun j => trigBlock (dyadicBlock ((j : ℕ) + 1)) c) k t + freqTerm c k t +
        (-1 : ℂ) • prev (freqTerm c) k t := by
  rw [← sum_closedFreq]
  cases k with
  | zero => simp [closedFreq_zero, openFreq_zero, prev]
  | succ j =>
    rw [← insert_openFreq_succ, Finset.sum_insert (by simp [openFreq, pow_succ, mul_comm])]
    simp [prev, freqTerm]

private theorem aestronglyMeasurable_trigBlock (s : Set ℤ) (c : ℤ →₀ X) :
    AEStronglyMeasurable (trigBlock s c) haarAddCircle :=
  (continuous_trigPoly _).aestronglyMeasurable

private theorem aestronglyMeasurable_freqTerm (c : ℤ →₀ X) (j : ℕ) :
    AEStronglyMeasurable (freqTerm c j) haarAddCircle :=
  ((fourier _).continuous.smul continuous_const).aestronglyMeasurable

/-- The single frequencies `2^k`, one in each dyadic block. -/
private theorem eLpNormRad_freqTerm_le [CompleteSpace X] {p : ℝ} (hp : 1 ≤ p) (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun k : Fin K => freqTerm c k) p haarAddCircle ≤
      4 * eLpNormRad (fun k : Fin K => trigBlock (dyadicBlock ((k : ℕ) + 1)) c) p
        haarAddCircle := by
  classical
  have h := eLpNormRad_singleFrequency_le hp
    (fun k : Fin K => c.filter (· ∈ dyadicBlock ((k : ℕ) + 1))) fun k => ((2 ^ (k : ℕ) : ℕ) : ℤ)
  have h1 (k : Fin K) : c.filter (· ∈ dyadicBlock ((k : ℕ) + 1)) ((2 ^ (k : ℕ) : ℕ) : ℤ) =
      c ((2 ^ (k : ℕ) : ℕ) : ℤ) := by
    refine Finsupp.filter_apply_pos _ _ ((mem_dyadicBlock_succ _ _).2 ?_)
    exact Finset.mem_map_of_mem _ (Finset.mem_Ico.2 ⟨le_rfl, by simp [pow_succ]⟩)
  simp only [h1] at h
  refine h.trans_eq ?_
  congr 2

variable [CompleteSpace X]

/-- (III.3) on average over the signs, for the blocks `H_{2^k}` of a polynomial with values in a UMD
space, in the norm of `L^p`, `1 < p < ∞`. Departure from the source, which obtains (III.3) for every
choice of the signs from Bourgain's multiplier theorem: here `H_{2^k}` is a dyadic block and one
frequency, and the Littlewood–Paley inequality is applied to the dyadic blocks. -/
private theorem eLpNormRad_closed_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun (k : Fin K) (t : UnitAddCircle) =>
        ∑ q ∈ closedFreq k, fourier (q : ℤ) t • c q) p haarAddCircle ≤
      5 * (littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle) := by
  have hF := fun j : ℕ => aestronglyMeasurable_trigBlock (dyadicBlock ((j : ℕ) + 1)) c
  have h0 := eLpNormRad_dyadicBlock_succ_le hp hβ c K
  have h1 := eLpNormRad_prev_le hp.le hF K
  have h2 := eLpNormRad_freqTerm_le hp.le c K
  simp only [sum_closedFreq]
  refine (eLpNormRad_add_le hp.le (fun k => aestronglyMeasurable_prev hF k)
    fun k => aestronglyMeasurable_freqTerm c k).trans ?_
  calc _ ≤ littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle +
        4 * (littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle) :=
        add_le_add (h1.trans h0) (h2.trans (by gcongr))
    _ = _ := by ring

/-- The same for the blocks `G_{2^k}`, which are a dyadic block, plus one frequency, minus another.
-/
private theorem eLpNormRad_open_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun (k : Fin K) (t : UnitAddCircle) =>
        ∑ q ∈ openFreq k, fourier (q : ℤ) t • c q) p haarAddCircle ≤
      13 * (littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle) := by
  have hF := fun j : ℕ => aestronglyMeasurable_trigBlock (dyadicBlock ((j : ℕ) + 1)) c
  have hL := aestronglyMeasurable_freqTerm c
  have h0 := eLpNormRad_dyadicBlock_succ_le hp hβ c K
  have h1 := eLpNormRad_prev_le hp.le hF K
  have h2 := eLpNormRad_freqTerm_le hp.le c K
  have h3 := eLpNormRad_prev_le hp.le hL K
  have h4 := eLpNormRad_smul_le (μ := haarAddCircle) hp.le
    (c := fun (_ : Fin K) (_ : UnitAddCircle) => (-1 : ℂ)) (fun _ _ => by simp)
    (fun _ => aestronglyMeasurable_const) fun k => aestronglyMeasurable_prev hL k
  simp only [sum_openFreq]
  refine (eLpNormRad_add_le hp.le
    (fun k => (aestronglyMeasurable_prev hF k).add (hL k))
    fun k => (aestronglyMeasurable_prev hL k).const_smul _).trans ?_
  refine (add_le_add_left (eLpNormRad_add_le hp.le (fun k => aestronglyMeasurable_prev hF k)
    fun k => hL k) _).trans ?_
  calc _ ≤ littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle +
        4 * (littlewoodPaleyBound β * eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle) +
        2 * (4 * (littlewoodPaleyBound β *
          eLpNorm (trigPoly c) (ENNReal.ofReal p) haarAddCircle)) :=
        add_le_add (add_le_add (h1.trans h0) (h2.trans (by gcongr)))
          (h4.trans (by
            gcongr
            exact h3.trans (h2.trans (by gcongr))))
    _ = _ := by ring

end Blocks

/-! ### Square norms of Rademacher sums of continuous functions -/

section Sq

/-- The square of the `L²` norm of a continuous function. -/
private theorem eLpNorm_two_sq_eq {X : Type*} [NormedAddCommGroup X] {u : UnitAddCircle → X}
    (hu : Continuous u) :
    eLpNorm u (ENNReal.ofReal 2) haarAddCircle ^ (2 : ℝ) =
      ENNReal.ofReal (∫ t, ‖u t‖ ^ 2 ∂haarAddCircle) := by
  have hmem : MemLp u (ENNReal.ofReal 2) haarAddCircle :=
    hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : 0 ≤ ∫ t, ‖u t‖ ^ 2 ∂haarAddCircle := integral_nonneg fun t => by positivity
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by simp) (by simp), ENNReal.toReal_ofReal (by simp)]
  simp only [Real.rpow_ofNat]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by simp), ← Real.rpow_mul h0]
  norm_num

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The square of the norm of a Rademacher sum of continuous functions. -/
private theorem eLpNormRad_two_sq_eq {K : ℕ} {u : Fin K → UnitAddCircle → X}
    (hu : ∀ k, Continuous (u k)) :
    eLpNormRad u 2 haarAddCircle ^ (2 : ℝ) = ENNReal.ofReal (avg fun ε : Fin K → Bool =>
      ∫ t, ‖∑ k, coin (ε k) • u k t‖ ^ 2 ∂haarAddCircle) := by
  rw [eLpNormRad_rpow two_pos fun k => (hu k).aestronglyMeasurable, avg, div_eq_inv_mul,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun ε _ => integral_nonneg fun t => by positivity]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun ε _ => ?_
    exact eLpNorm_two_sq_eq (continuous_finsetSum _ fun k _ => (hu k).const_smul _)

/-- From norms of Rademacher sums to averages of integrals. -/
private theorem avg_integral_le_of_eLpNormRad_le {K : ℕ} {u : Fin K → UnitAddCircle → X}
    (hu : ∀ k, Continuous (u k)) {v : UnitAddCircle → X} (hv : Continuous v) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (h : eLpNormRad u 2 haarAddCircle ≤
      C * eLpNorm v (ENNReal.ofReal 2) haarAddCircle) :
    (avg fun ε : Fin K → Bool => ∫ t, ‖∑ k, coin (ε k) • u k t‖ ^ 2 ∂haarAddCircle) ≤
      C.toReal ^ 2 * ∫ t, ‖v t‖ ^ 2 ∂haarAddCircle := by
  have h0 : 0 ≤ ∫ t, ‖v t‖ ^ 2 ∂haarAddCircle := integral_nonneg fun t => by positivity
  have h1 := ENNReal.rpow_le_rpow h (z := 2) (by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), eLpNorm_two_sq_eq hv, eLpNormRad_two_sq_eq hu,
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
private theorem norm_trigPoly_partialCoeff {h : UnitAddCircle → Matrix n n ℂ} (hh : IsHardyTwo h)
    (N : ℕ) (t : UnitAddCircle) : ‖trigPoly (partialCoeff q h N) t‖ = complexSchattenNorm q
      (∑ k ∈ Finset.Icc (-N : ℤ) N, fourier k t • matFourierCoeff h k) := by
  have h1 : (Finset.range (N + 1)).map Nat.castEmbedding ⊆ Finset.Icc (-N : ℤ) N := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hp
    rw [Finset.mem_range] at hr
    simp only [Nat.castEmbedding_apply, Finset.mem_Icc]
    omega
  rw [partialCoeff, trigPoly_coeffOn, ← Finset.sum_subset h1, Finset.sum_map,
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
private theorem avg_integral_block_le {S : ℕ → Finset ℕ} (hS : ∀ k, ∀ p ∈ S k, p ≤ 2 ^ k)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {K : ℕ}
    (hle : ∀ c : ℤ →₀ ComplexSchattenSpace q n n,
      eLpNormRad (fun (k : Fin K) (t : UnitAddCircle) =>
          ∑ p ∈ S k, fourier (p : ℤ) t • c p) 2 haarAddCircle ≤
        C * eLpNorm (trigPoly c) (ENNReal.ofReal 2) haarAddCircle)
    {h : UnitAddCircle → Matrix n n ℂ} (hh : IsHardyTwo h) :
    (avg fun ε : Fin K → Bool => ∫ t : UnitAddCircle, complexSchattenNorm q
        (∑ k, coin (ε k) • ∑ p ∈ S k, fourier (p : ℤ) t • matFourierCoeff h p) ^ 2
          ∂haarAddCircle) ≤
      C.toReal ^ 2 * ∫ t, complexSchattenNorm q (h t) ^ 2 ∂haarAddCircle := by
  refine ge_of_tendsto ((tendsto_integral_norm_sq_partialSum (Fact.out (p := 1 ≤ q)) hh.1).const_mul
    (C.toReal ^ 2)) ?_
  filter_upwards [Filter.eventually_ge_atTop (2 ^ K)] with N hN
  have key := avg_integral_le_of_eLpNormRad_le
    (u := fun (k : Fin K) (t : UnitAddCircle) =>
      ∑ p ∈ S k, fourier (p : ℤ) t • partialCoeff q h N p)
    (fun k => continuous_finsetSum _ fun p _ => (fourier _).continuous.smul continuous_const)
    (continuous_trigPoly _) hC (hle (partialCoeff q h N))
  simpa only [norm_sum_block_partialCoeff hS hN, norm_trigPoly_partialCoeff hh] using key

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
  rw [hq, ENNReal.toReal_ofReal (by linarith), sub_le_iff_le_add, pStar]
  refine max_le (by linarith) ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

private theorem littlewoodPaleyBound_ne_top {β : ℝ≥0∞} (hβ : β ≠ ⊤) :
    littlewoodPaleyBound β ≠ ⊤ := by
  unfold littlewoodPaleyBound hilbertBound
  finiteness

/-- Lust-Piquard–Pisier, (III.3), p. 253, on average over the signs, for the blocks `H_{2^k}` of
`h ∈ H²`: `E ∫ ‖Σ ε_k H_{2^k}‖_{S_{2p}}² ≤ C ∫ ‖h‖_{S_{2p}}²` with an absolute constant `C`, for
`1 ≤ p ≤ 2` and all sizes. Departure from the source: there (III.3) is proved for every choice of
the signs, by Bourgain's multiplier theorem; the average, which is all that (III.2) uses, is bounded
here by the Littlewood–Paley inequality and the randomised boundedness of single frequencies. -/
theorem exists_avg_integral_paleyBlockClosed_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n]
    [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ (h : UnitAddCircle → Matrix n n ℂ), IsHardyTwo h →
    ∀ K : ℕ, (avg fun ε : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
        (∑ k, coin (ε k) • paleyBlockClosed h k t) ^ 2 ∂haarAddCircle) ≤
      C * ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ∂haarAddCircle := by
  obtain ⟨β, hβ, hUMD⟩ := exists_isUMDBound
  have hC : 5 * littlewoodPaleyBound β ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (littlewoodPaleyBound_ne_top hβ)
  refine ⟨(5 * littlewoodPaleyBound β).toReal ^ 2 + 1, by positivity, ?_⟩
  intro n _ _ p hp1 hp2 h hh K
  have hfact : Fact (1 ≤ ENNReal.ofReal (2 * p)) :=
    ⟨ENNReal.one_le_ofReal.2 (by linarith)⟩
  have hint : 0 ≤ ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (h t) ^ 2 ∂haarAddCircle :=
    integral_nonneg fun t => by positivity
  refine (avg_integral_block_le (q := ENNReal.ofReal (2 * p)) (S := closedFreq)
    (fun k r hr => (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).2) hC (fun c => ?_) hh).trans ?_
  · rw [mul_assoc]
    exact eLpNormRad_closed_le one_lt_two (hUMD _ p hp1 hp2 rfl n) c K
  · exact mul_le_mul_of_nonneg_right (by linarith) hint

/-- Lust-Piquard–Pisier, (III.3), p. 253, on average over the signs, for the blocks `G_{2^k}` of
`g ∈ H²`: `E ∫ ‖Σ ε_k G_{2^k}‖_{S_{2p}}² ≤ C ∫ ‖g‖_{S_{2p}}²` with an absolute constant `C`, for
`1 ≤ p ≤ 2` and all sizes. The departure from the source is that of
`exists_avg_integral_paleyBlockClosed_le`. -/
theorem exists_avg_integral_paleyBlockOpen_le : ∃ C : ℝ, 0 < C ∧ ∀ (n : Type) [Fintype n]
    [DecidableEq n] (p : ℝ), 1 ≤ p → p ≤ 2 → ∀ (g : UnitAddCircle → Matrix n n ℂ), IsHardyTwo g →
    ∀ K : ℕ, (avg fun ε : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
        (∑ k, coin (ε k) • paleyBlockOpen g k t) ^ 2 ∂haarAddCircle) ≤
      C * ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle := by
  obtain ⟨β, hβ, hUMD⟩ := exists_isUMDBound
  have hC : 13 * littlewoodPaleyBound β ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (littlewoodPaleyBound_ne_top hβ)
  refine ⟨(13 * littlewoodPaleyBound β).toReal ^ 2 + 1, by positivity, ?_⟩
  intro n _ _ p hp1 hp2 g hg K
  have hfact : Fact (1 ≤ ENNReal.ofReal (2 * p)) :=
    ⟨ENNReal.one_le_ofReal.2 (by linarith)⟩
  have hint : 0 ≤ ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle :=
    integral_nonneg fun t => by positivity
  refine (avg_integral_block_le (q := ENNReal.ofReal (2 * p)) (S := openFreq)
    (fun k r hr => (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).2) hC (fun c => ?_) hg).trans ?_
  · rw [mul_assoc]
    exact eLpNormRad_open_le one_lt_two (hUMD _ p hp1 hp2 rfl n) c K
  · exact mul_le_mul_of_nonneg_right (by linarith) hint

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
coefficients `∫ g U_k e_{−m_k}`: by Jensen's, Hölder's and the Cauchy–Schwarz inequality and
(III.2), the row square function is at most
`(∫ ‖g‖_{S_{2p}}²)^{1/2} (E ∫ ‖Σ ε_k U_k‖_{S_{2p}}²)^{1/2}`. -/
private theorem complexSchattenNorm_blockRow_matFourierCoeff_le {p : ℝ} (hp : 1 ≤ p)
    {g : UnitAddCircle → Matrix n n ℂ} (hg : ∀ i j, MemLp (fun t => g t i j) 2 haarAddCircle)
    {K : ℕ} {U : Fin K → UnitAddCircle → Matrix n n ℂ} (hU : ∀ k, Continuous (U k))
    (m : Fin K → ℤ) :
    complexSchattenNorm (ENNReal.ofReal p)
        (blockRow fun k => matFourierCoeff (fun t => g t * U k t) (m k)) ≤
      √(∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p)) (g t) ^ 2 ∂haarAddCircle) *
        √(avg fun ε : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
          (∑ k, coin (ε k) • U k t) ^ 2 ∂haarAddCircle) := by
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
  refine (complexSchattenNorm_integral_mul_le hp hg (memLp_entry_of_continuous hQ)).trans ?_
  simp only [hQn]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (integral_blockRow_sq_le (by linarith) hU))
    (Real.sqrt_nonneg _)

/-- The first part of the proof of (δ), p. 250, with the norms of Theorem III.1, for the
coefficients `∫ U_k h e_{−m_k}`: by Jensen's, Hölder's and the Cauchy–Schwarz inequality and
(III.2), the column square function is at most
`(E ∫ ‖Σ ε_k U_k‖_{S_{2p}}²)^{1/2} (∫ ‖h‖_{S_{2p}}²)^{1/2}`. -/
private theorem complexSchattenNorm_blockCol_matFourierCoeff_le {p : ℝ} (hp : 1 ≤ p)
    {h : UnitAddCircle → Matrix n n ℂ} (hh : ∀ i j, MemLp (fun t => h t i j) 2 haarAddCircle)
    {K : ℕ} {U : Fin K → UnitAddCircle → Matrix n n ℂ} (hU : ∀ k, Continuous (U k))
    (m : Fin K → ℤ) :
    complexSchattenNorm (ENNReal.ofReal p)
        (blockCol fun k => matFourierCoeff (fun t => U k t * h t) (m k)) ≤
      √(avg fun ε : Fin K → Bool => ∫ t, complexSchattenNorm (ENNReal.ofReal (2 * p))
          (∑ k, coin (ε k) • U k t) ^ 2 ∂haarAddCircle) *
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
  refine (complexSchattenNorm_integral_mul_le hp (memLp_entry_of_continuous hP) hh).trans ?_
  simp only [hPn]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (integral_blockCol_sq_le (by linarith) hU))
    (Real.sqrt_nonneg _)

end SquareFunction

/-! ### Paley's inequality -/

/-- Lust-Piquard–Pisier, (α) and (β), p. 252, for `C_E = C_p`: `f ∈ H¹` is a product `f = g h` of
functions of `H²` such that `‖f‖_{H¹ (C_p)} = ‖g‖_{H² (C_{2p})} ‖h‖_{H² (C_{2p})}`. These are the
factors of Sarason's theorem (`exists_mul_eq_of_isHardyOne`). -/
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
for the Paley projection and `C_p`), with a constant independent of `1 ≤ p ≤ 2` and of the size. -/
theorem paley_schatten : ∃ M : ℝ, 0 < M ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (p : ℝ), 1 ≤ p →
    p ≤ 2 → ∀ (c : ℤ →₀ Matrix n n ℂ), (∀ k ∈ c.support, 0 ≤ k) → ∀ K : ℕ,
    ∃ a b : Fin K → Matrix n n ℂ, (∀ k : Fin K, c (2 ^ (k : ℕ)) = a k + b k) ∧
      complexSchattenNorm (ENNReal.ofReal p) (blockRow a) +
        complexSchattenNorm (ENNReal.ofReal p) (blockCol b) ≤
      M * ∫ t, complexSchattenNorm (ENNReal.ofReal p) (trigPoly c t) ∂haarAddCircle := by
  obtain ⟨C₁, hC₁, hclosed⟩ := exists_avg_integral_paleyBlockClosed_le
  obtain ⟨C₂, hC₂, hopen⟩ := exists_avg_integral_paleyBlockOpen_le
  refine ⟨√C₁ + √C₂, by positivity, ?_⟩
  intro n _ _ p hp1 hp2 c hc K
  -- `f = g h`, (α) and (β)
  obtain ⟨g, h, hg, hh, hfac, hβ⟩ := exists_mul_eq_integral_complexSchattenNorm_eq
    (one_pos.trans_le hp1) (isHardyTwo_trigPoly hc).isHardyOne
  refine ⟨fun k => matFourierCoeff (fun t => g t * paleyBlockClosed h k t) (2 ^ (k : ℕ)),
    fun k => matFourierCoeff (fun t => paleyBlockOpen g k t * h t) (2 ^ (k : ℕ)), fun k => ?_, ?_⟩
  · -- `f̂ (2^k) = A_k + B_k`
    rw [← matFourierCoeff_mul_two_pow hg hh, ← matFourierCoeff_congr_ae hfac,
      matFourierCoeff_trigPoly]
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

end VectorValuedHarmonicAnalysis
