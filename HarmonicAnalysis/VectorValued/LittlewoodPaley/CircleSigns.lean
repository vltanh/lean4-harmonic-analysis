/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.LittlewoodPaley.Signs
public import HarmonicAnalysis.VectorValued.LittlewoodPaley.Circle

/-!
# Dyadic multipliers on the circle for every choice of the signs

McConnell's Littlewood–Paley theorem on the line (`Signs.lean`), transferred to the circle: for a
complex UMD space, `1 < p < ∞`, all `ε_ℓ ∈ {−1, 0, 1}` and all trigonometric polynomials
`f = Σ_n c_n e_n`, the `L^p` norm of `Σ_n a_n c_n e_n` is at most `C_β ‖f‖_p`, uniformly in the
signs, for

* `a_n = ε_ℓ` if `2^ℓ ≤ n < 2^{ℓ+1}`, `0` if `n ≤ 0` (blocks closed on the left);
* `a_n = ε_ℓ` if `2^{ℓ−1} < n ≤ 2^ℓ`, `0` if `n ≤ 0` (blocks closed on the right);
* `a_n = Σ_{n ≤ 2^ℓ ≤ 2n} ε_ℓ` (closed blocks), so that `a_n = ε_ℓ` for `2^{ℓ−1} < n < 2^ℓ` and
  `a_n = ε_ℓ + ε_{ℓ+1}` for `n = 2^ℓ`.

The last multiplier is that of F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley
inequalities*, Ark. Mat. 29 (1991), p. 253, for `k_ℓ = 2^ℓ`; their sums `ℓ ≤ L` are finite, whence
the coefficients `ε_ℓ = 0` here. They deduce its boundedness from Bourgain's version of the
Marcinkiewicz multiplier theorem and refer also to T. R. McConnell, *On Fourier multiplier
transformations of Banach-valued functions*, Trans. Amer. Math. Soc. 285 (1984), 739–757, Theorem
1.3, which is used here. It gives the first two multipliers, `L_ε` and `R_ε`, by transference; the
third one, which takes the value `ε_ℓ + ε_{ℓ+1}` at `2^ℓ`, is
`R_ε + ½ L_{ε (· + 1)} − ½ L_{θ ε (· + 1)} R_{−θ}`, where `θ_ℓ = (−1)^ℓ`. If the first two
multipliers have norms at most `K`, for all the signs, then the third one has norm at most
`K + ½ K + ½ K²`.

The transference is that of Hytönen–van Neerven–Veraar–Weis (HNVW), *Analysis in Banach spaces I*
(2016), pp. 458–460 and 465–466 (`HarmonicAnalysis.VectorValued.Transference`), with their
irrational dilations `ρ > 1` near `1` for the blocks closed on the left. For the blocks closed on
the right the dilations are `ρ < 1`, which is added here.
-/

@[expose] public section

open MeasureTheory AddCircle Filter BanachProbability
open scoped ENNReal FourierTransform SchwartzMap Topology

namespace HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The coefficients `a_n c_n` of `T_a f`, for a multiplier `a : ℤ → ℂ` and `f = Σ c_n e_n`. -/
noncomputable def mulCoeff (a : ℤ → ℂ) (c : ℤ →₀ X) : ℤ →₀ X :=
  Finsupp.onFinset c.support (fun n => a n • c n) fun n hn => by
    rw [Finsupp.mem_support_iff]
    rintro h
    exact hn (by rw [h, smul_zero])

/-- `a_n = ε_ℓ` for `2^ℓ ≤ n < 2^{ℓ+1}`, `ℓ ≥ 0`, and `a_n = 0` for `n ≤ 0`. -/
noncomputable def leftBlockSign (ε : ℕ → ℝ) (n : ℤ) : ℝ :=
  if 0 < n then ε (Nat.log 2 n.toNat) else 0

/-- `a_n = ε_ℓ` for `2^{ℓ−1} < n ≤ 2^ℓ`, `ℓ ≥ 0`, and `a_n = 0` for `n ≤ 0`. -/
noncomputable def rightBlockSign (ε : ℕ → ℝ) (n : ℤ) : ℝ :=
  if 0 < n then ε (Nat.clog 2 n.toNat) else 0

/-- `a_n = Σ_{n ≤ 2^ℓ ≤ 2n} ε_ℓ` for `n ≥ 1`, and `a_n = 0` for `n ≤ 0` (Lust-Piquard–Pisier (1991),
p. 253, for `k_ℓ = 2^ℓ`): the sum has the terms `ℓ = ⌈log₂ n⌉` and, if `n` is a power of `2`,
`ℓ = log₂ n + 1`. -/
noncomputable def closedBlockSign (ε : ℕ → ℝ) (n : ℤ) : ℝ :=
  if 0 < n then ∑ ℓ ∈ Finset.Icc (Nat.clog 2 n.toNat) (Nat.log 2 n.toNat + 1), ε ℓ else 0

/-! ### The multipliers `T_a` -/

/-- The coefficients of `T_a f`. -/
theorem mulCoeff_apply (a : ℤ → ℂ) (c : ℤ →₀ X) (n : ℤ) : mulCoeff a c n = a n • c n :=
  rfl

/-- `T_a f = Σ_n a_n c_n e_n`. -/
theorem circPoly_mulCoeff (a : ℤ → ℂ) (c : ℤ →₀ X) (t : UnitAddCircle) :
    circPoly (mulCoeff a c) t = c.sum fun n x => fourier n t • a n • x :=
  Finsupp.onFinset_sum _ fun _ => smul_zero _

/-- `T_a f` depends only on the values of `a` at the frequencies of `f`. -/
private theorem mulCoeff_congr {a b : ℤ → ℂ} {c : ℤ →₀ X} (h : ∀ n ∈ c.support, a n = b n) :
    mulCoeff a c = mulCoeff b c := by
  ext n
  rw [mulCoeff_apply, mulCoeff_apply]
  by_cases hn : n ∈ c.support
  · rw [h n hn]
  · rw [Finsupp.notMem_support_iff.1 hn, smul_zero, smul_zero]

/-! ### The symbols on the line

`dyadicSign η (ρ ·)`, for an irrational `ρ > 0` and `η_j = 0` for `j < −1`: it is bounded and
measurable, and continuous at the integers. -/

/-- `dyadicSign η = 0` on `(−∞, 1/2)`, if `η_j = 0` for `j < −1`. -/
private theorem dyadicSign_eq_zero {η : ℤ → ℝ} (hη : ∀ j < -1, η j = 0) {ξ : ℝ}
    (hξ : ξ < 1 / 2) : dyadicSign η ξ = 0 := by
  rw [dyadicSign]
  split_ifs with h0
  · refine hη _ ((Int.lt_zpow_iff_log_lt one_lt_two h0).1 ?_)
    rw [Nat.cast_ofNat, zpow_neg_one]
    linarith
  · rfl

/-- The numbers `ρ k`, `k` a nonzero integer, are not powers of `2`. -/
private theorem mul_intCast_ne_zpow {ρ : ℝ} (hρ : Irrational ρ) {k : ℤ} (hk : k ≠ 0) (j : ℤ) :
    (2 : ℝ) ^ j ≠ ρ * k := by
  intro h
  refine (hρ.mul_intCast hk).ne_rat (2 ^ j) ?_
  rw [← h]
  push_cast
  rfl

/-- `dyadicSign η (ρ ·)` is continuous at the integers. -/
private theorem continuousAt_dyadicSign {η : ℤ → ℝ} (hη : ∀ j < -1, η j = 0) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ : Irrational ρ) (k : ℤ) :
    ContinuousAt (fun ξ => dyadicSign η (ρ * ξ)) k := by
  have hloc : ∀ᶠ ξ in 𝓝 (ρ * k), dyadicSign η ξ = dyadicSign η (ρ * k) := by
    rcases le_or_gt k 0 with hk | hk
    · -- the symbol vanishes on `(−∞, 1/2)`
      have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      have h1 : ρ * k < 1 / 2 := by nlinarith
      filter_upwards [Iio_mem_nhds h1] with ξ hξ
      rw [dyadicSign_eq_zero hη hξ, dyadicSign_eq_zero hη h1]
    · -- the symbol is constant near `ρ k`, which is not a power of `2`
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      set j := Int.log 2 (ρ * k)
      have h1 : (2 : ℝ) ^ j ≤ ρ * k := by
        simpa using Int.zpow_log_le_self (b := 2) one_lt_two (mul_pos hρ0 hk')
      have h2 : ρ * k < 2 ^ (j + 1) := by
        simpa using Int.lt_zpow_succ_log_self (b := 2) one_lt_two (ρ * k)
      have h3 := lt_of_le_of_ne h1 (mul_intCast_ne_zpow hρ hk.ne' j)
      filter_upwards [Ioo_mem_nhds h3 h2] with ξ hξ
      rw [dyadicSign_eq η hξ.1.le hξ.2, dyadicSign_eq η h1 h2]
  have hcont : ContinuousAt (fun ξ : ℝ => ρ * ξ) k := by fun_prop
  exact continuousAt_const.congr (EventuallyEq.symm (hcont.eventually hloc))

/-! ### Transference -/

/-- The multipliers `dyadicSign η`, `η_j ∈ {−1, 0, 1}`, are bounded on `L^p (ℝ; X)` with norms at
most `K`. -/
private def DyadicSignBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] (p : ℝ)
    (K : ℝ≥0∞) : Prop :=
  ∀ η : ℤ → ℝ, (∀ j, η j = 1 ∨ η j = 0 ∨ η j = -1) →
    ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => ((dyadicSign η ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        K * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume

section

variable [CompleteSpace X] {p : ℝ} {K : ℝ≥0∞}

/-- **Transference** (HNVW I, Proposition 5.7.1 and (5.61)): the multiplier `dyadicSign η (ρ n)` on
the circle, for an irrational `ρ > 0`, has the bound of the multiplier `dyadicSign η` on the
line. -/
private theorem eLpNorm_mulCoeff_dyadicSign_le (hp : 1 < p) (hK : DyadicSignBound X p K)
    {η : ℤ → ℝ} (hη : ∀ j, η j = 1 ∨ η j = 0 ∨ η j = -1) (hη0 : ∀ j < -1, η j = 0) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ : Irrational ρ) (c : ℤ →₀ X) :
    eLpNorm (circPoly (mulCoeff (fun n => ((dyadicSign η (ρ * n) : ℝ) : ℂ)) c))
        (ENNReal.ofReal p) haarAddCircle ≤
      K * eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  set m : ℝ → X →L[ℂ] X := fun ξ => ((dyadicSign η ξ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ X
    with hm
  have hm_apply : ∀ ξ x, m ξ x = ((dyadicSign η ξ : ℝ) : ℂ) • x := fun ξ x => rfl
  have hbound : ∀ ξ, ‖m (ρ * ξ)‖ ≤ 1 := fun ξ =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [hm_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_dyadicSign_le hη _) (norm_nonneg x)
  have hmeas : ∀ x, AEStronglyMeasurable (fun ξ => m (ρ * ξ) x) volume := fun x => by
    simp only [hm_apply]
    exact (Complex.measurable_ofReal.comp ((measurable_dyadicSign η).comp
      (measurable_const_mul ρ))).aestronglyMeasurable.smul_const x
  have hcont : ∀ (k : ℤ) (x : X), ContinuousAt (fun ξ => m (ρ * ξ) x) k := fun k x => by
    simp only [hm_apply]
    exact (Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_dyadicSign hη0 hρ0 hρ k)).smul continuousAt_const
  have h := eLpNorm_circPoly_multiplier_le hp hbound hmeas hcont
    (eLpNorm_fourierInv_multiplier_dilate_le (m := m) (by linarith) (fun G => by
      simp only [hm_apply]
      exact hK η hη G G.integrable (memLp_fourierInv G _)) hρ0) c
  rw [funext (circPoly_mulCoeff _ c)]
  simpa only [hm_apply] using h

/-! ### The blocks closed on one side

As in HNVW I, pp. 465–466: an irrational `ρ` near `1` moves the frequencies `n > 0` of `f` into the
blocks `[2^j, 2^{j+1})` of the line, to the right for the blocks closed on the left (`ρ > 1`, as in
the book), to the left for those closed on the right (`ρ < 1`). -/

/-- `η_j = ε_{j + s}`, for `j ≥ −s`, and `η_j = 0` for `j < −s`. -/
private def shiftSign (ε : ℕ → ℝ) (s j : ℤ) : ℝ :=
  if 0 ≤ j + s then ε (j + s).toNat else 0

private theorem shiftSign_mem {ε : ℕ → ℝ} (hε : ∀ ℓ, ε ℓ = 1 ∨ ε ℓ = 0 ∨ ε ℓ = -1) (s j : ℤ) :
    shiftSign ε s j = 1 ∨ shiftSign ε s j = 0 ∨ shiftSign ε s j = -1 := by
  rw [shiftSign]
  split_ifs
  · exact hε _
  · exact Or.inr (Or.inl rfl)

private theorem shiftSign_eq_zero (ε : ℕ → ℝ) {s : ℤ} (hs : s ≤ 1) {j : ℤ} (hj : j < -1) :
    shiftSign ε s j = 0 :=
  ite_eq_right (by omega)

/-- The blocks closed on the left: `⌊ρ n⌋ = n`, if `ρ > 1` is near `1`. -/
private theorem dyadicSign_left {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ) (hρN : ρ * N < N + 1) {n : ℤ}
    (hn : n ≤ N) (ε : ℕ → ℝ) : dyadicSign (shiftSign ε 0) (ρ * n) = leftBlockSign ε n := by
  rcases le_or_gt n 0 with hn0 | hn0
  · have h1 : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    rw [dyadicSign, leftBlockSign, ite_eq_right (by nlinarith), ite_eq_right (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hn0
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hn
    rw [Int.cast_natCast]
    have h1 : (k : ℝ) ≤ ρ * k := by nlinarith
    have h2 : ρ * k < k + 1 := by nlinarith
    have h3 : ⌊ρ * k⌋₊ = k := (Nat.floor_eq_iff (by linarith)).2 ⟨h1, h2⟩
    rw [dyadicSign, leftBlockSign, ite_eq_left (by linarith), ite_eq_left hn0,
      Int.log_of_one_le_right 2 (hk1.trans h1), h3, shiftSign, ite_eq_left (by omega)]
    simp

/-- The blocks closed on the right: `n − 1 < ρ n < n`, if `ρ < 1` is near `1`, so that
`2^{ℓ−1} ≤ ρ n < 2^ℓ` if `2^{ℓ−1} < n ≤ 2^ℓ` (for `n = 1`, `ℓ = 0`, this is `1/2 ≤ ρ < 1`). -/
private theorem dyadicSign_right {N : ℕ} {ρ : ℝ} (hρ2 : 1 / 2 ≤ ρ) (hρ : ρ < 1)
    (hρN : N - 1 < ρ * N) {n : ℤ} (hn : n ≤ N) (ε : ℕ → ℝ) :
    dyadicSign (shiftSign ε 1) (ρ * n) = rightBlockSign ε n := by
  rcases le_or_gt n 0 with hn0 | hn0
  · have h1 : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    rw [dyadicSign, rightBlockSign, ite_eq_right (by nlinarith), ite_eq_right (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    have hk0 : 0 < k := by exact_mod_cast hn0
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hn
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    rw [Int.cast_natCast, rightBlockSign, ite_eq_left hn0, Int.toNat_natCast,
      dyadicSign_eq (j := (Nat.clog 2 k : ℤ) - 1), shiftSign, ite_eq_left (by omega)]
    · simp
    · rcases Nat.lt_or_ge 1 k with hk | hk
      · -- `2^{ℓ−1} < n`
        have h1 := Nat.pow_pred_clog_lt_self one_lt_two hk
        have h2 : 0 < Nat.clog 2 k := Nat.clog_pos one_lt_two hk
        have h3 : ((Nat.clog 2 k : ℤ) - 1) = ((Nat.clog 2 k).pred : ℕ) := by
          rw [Nat.pred_eq_sub_one]
          omega
        have h4 : (2 : ℝ) ^ (Nat.clog 2 k).pred + 1 ≤ k := by exact_mod_cast h1
        rw [h3, zpow_natCast]
        nlinarith
      · obtain rfl : k = 1 := by omega
        norm_num
        linarith
    · have h1 : (k : ℝ) ≤ 2 ^ Nat.clog 2 k := by exact_mod_cast Nat.le_pow_clog one_lt_two k
      rw [sub_add_cancel, zpow_natCast]
      nlinarith

/-- A bound `N` of the frequencies of `f`. -/
private theorem exists_le_natCast (s : Finset ℤ) : ∃ N : ℕ, 2 ≤ N ∧ ∀ n ∈ s, n ≤ N := by
  refine ⟨s.sup Int.natAbs + 2, by omega, fun n hn => ?_⟩
  have h := Finset.le_sup (f := Int.natAbs) hn
  omega

/-- The multipliers with the coefficients `ε_ℓ` on the blocks closed on the left. -/
private theorem eLpNorm_leftBlockSign_le (hp : 1 < p) (hK : DyadicSignBound X p K) {ε : ℕ → ℝ}
    (hε : ∀ ℓ, ε ℓ = 1 ∨ ε ℓ = 0 ∨ ε ℓ = -1) (c : ℤ →₀ X) :
    eLpNorm (circPoly (mulCoeff (fun n => (leftBlockSign ε n : ℂ)) c)) (ENNReal.ofReal p)
      haarAddCircle ≤ K * eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  obtain ⟨N, ρ, hρi, hρ1, hρN, hN⟩ := exists_irrational_dilation c.support
  rw [← mulCoeff_congr fun n hn =>
    congrArg Complex.ofReal (dyadicSign_left hρ1 hρN ((le_abs_self n).trans (hN n hn)) ε)]
  exact eLpNorm_mulCoeff_dyadicSign_le hp hK (shiftSign_mem hε 0)
    (fun j hj => shiftSign_eq_zero ε (by norm_num) hj) (by linarith) hρi c

/-- The multipliers with the coefficients `ε_ℓ` on the blocks closed on the right. -/
private theorem eLpNorm_rightBlockSign_le (hp : 1 < p) (hK : DyadicSignBound X p K) {ε : ℕ → ℝ}
    (hε : ∀ ℓ, ε ℓ = 1 ∨ ε ℓ = 0 ∨ ε ℓ = -1) (c : ℤ →₀ X) :
    eLpNorm (circPoly (mulCoeff (fun n => (rightBlockSign ε n : ℂ)) c)) (ENNReal.ofReal p)
      haarAddCircle ≤ K * eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  obtain ⟨N, hN2, hN⟩ := exists_le_natCast c.support
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨ρ, hρi, hρN, hρ1⟩ := exists_irrational_btwn (sub_lt_self (1 : ℝ)
    (one_div_pos.2 hN0))
  have hρN' : N - 1 < ρ * N := by
    calc (N : ℝ) - 1 = (1 - 1 / N) * N := by field_simp
      _ < ρ * N := by gcongr
  have hρ2 : 1 / 2 ≤ ρ := by
    have h1 : 1 / (N : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le two_pos hN2'
    linarith
  rw [← mulCoeff_congr fun n hn =>
    congrArg Complex.ofReal (dyadicSign_right hρ2 hρ1 hρN' (hN n hn) ε)]
  exact eLpNorm_mulCoeff_dyadicSign_le hp hK (shiftSign_mem hε 1)
    (fun j hj => shiftSign_eq_zero ε le_rfl hj) (by linarith) hρi c

/-! ### The closed blocks -/

/-- The signs `θ_ℓ = (−1)^ℓ`. -/
private def altSign (ℓ : ℕ) : ℝ :=
  (-1) ^ ℓ

private theorem neg_altSign_mem (ℓ : ℕ) :
    -altSign ℓ = 1 ∨ -altSign ℓ = 0 ∨ -altSign ℓ = -1 := by
  rcases neg_one_pow_eq_or ℝ ℓ with h | h <;> simp [altSign, h]

private theorem altSign_mul_mem (ℓ : ℕ) {a : ℝ} (ha : a = 1 ∨ a = 0 ∨ a = -1) :
    altSign ℓ * a = 1 ∨ altSign ℓ * a = 0 ∨ altSign ℓ * a = -1 := by
  rcases neg_one_pow_eq_or ℝ ℓ with h | h <;> rcases ha with rfl | rfl | rfl <;> simp [altSign, h]

/-- `⌈log₂ k⌉ = ⌊log₂ k⌋` or `⌈log₂ k⌉ = ⌊log₂ k⌋ + 1`. -/
private theorem clog_eq_log_or (k : ℕ) :
    Nat.clog 2 k = Nat.log 2 k ∨ Nat.clog 2 k = Nat.log 2 k + 1 := by
  have h1 := Nat.log_le_clog 2 k
  have h2 : Nat.clog 2 k ≤ Nat.log 2 k + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two k).le
  omega

/-- The multiplier of the closed blocks is `R_ε + ½ L_{ε (· + 1)} − ½ L_{θ ε (· + 1)} R_{−θ}`. With
`ℓ = ⌊log₂ n⌋` and `ℓ' = ⌈log₂ n⌉` the sum of the last two terms at `n > 0` is
`½ ε_{ℓ+1} (1 + θ_ℓ θ_{ℓ'})`, that is, `ε_{ℓ+1}` if `n = 2^ℓ` and `0` otherwise. -/
private theorem closedBlockSign_eq (ε : ℕ → ℝ) (n : ℤ) : closedBlockSign ε n =
    rightBlockSign ε n + (1 / 2 * leftBlockSign (fun ℓ => ε (ℓ + 1)) n + -1 / 2 *
      (leftBlockSign (fun ℓ => altSign ℓ * ε (ℓ + 1)) n *
        rightBlockSign (fun ℓ => -altSign ℓ) n)) := by
  rcases le_or_gt n 0 with hn | hn
  · simp [closedBlockSign, rightBlockSign, leftBlockSign, ite_eq_right (not_lt.2 hn)]
  · have h1 (j : ℕ) : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
    simp only [closedBlockSign, rightBlockSign, leftBlockSign, ite_eq_left hn, altSign]
    rcases clog_eq_log_or n.toNat with h | h
    · rw [h, Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
      linear_combination (-1 / 2 * ε (Nat.log 2 n.toNat + 1)) * h1 (Nat.log 2 n.toNat)
    · rw [h, Finset.Icc_self, Finset.sum_singleton, pow_succ]
      linear_combination (1 / 2 * ε (Nat.log 2 n.toNat + 1)) * h1 (Nat.log 2 n.toNat)

/-- The multipliers of the closed blocks. -/
private theorem eLpNorm_closedBlockSign_le (hp : 1 < p) (hK : DyadicSignBound X p K) {ε : ℕ → ℝ}
    (hε : ∀ ℓ, ε ℓ = 1 ∨ ε ℓ = 0 ∨ ε ℓ = -1) (c : ℤ →₀ X) :
    eLpNorm (circPoly (mulCoeff (fun n => (closedBlockSign ε n : ℂ)) c)) (ENNReal.ofReal p)
        haarAddCircle ≤ (K + (2⁻¹ * K + 2⁻¹ * K ^ 2)) *
      eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  set u := mulCoeff (fun n => (rightBlockSign ε n : ℂ)) c
  set v := mulCoeff (fun n => (leftBlockSign (fun ℓ => ε (ℓ + 1)) n : ℂ)) c
  set z := mulCoeff (fun n => (rightBlockSign (fun ℓ => -altSign ℓ) n : ℂ)) c
  set w := mulCoeff (fun n => (leftBlockSign (fun ℓ => altSign ℓ * ε (ℓ + 1)) n : ℂ)) z
  have hu := eLpNorm_rightBlockSign_le hp hK hε c
  have hv := eLpNorm_leftBlockSign_le hp hK (fun ℓ => hε (ℓ + 1)) c
  have hz := eLpNorm_rightBlockSign_le hp hK neg_altSign_mem c
  have hw := eLpNorm_leftBlockSign_le hp hK (fun ℓ => altSign_mul_mem ℓ (hε (ℓ + 1))) z
  have h1 : mulCoeff (fun n => (closedBlockSign ε n : ℂ)) c =
      u + ((1 / 2 : ℂ) • v + (-1 / 2 : ℂ) • w) := by
    ext n
    simp only [u, v, z, w, closedBlockSign_eq, mulCoeff_apply, Finsupp.add_apply,
      Finsupp.smul_apply, smul_smul, ← add_smul]
    push_cast
    ring_nf
  have h2 : circPoly (mulCoeff (fun n => (closedBlockSign ε n : ℂ)) c) =
      circPoly u + ((1 / 2 : ℂ) • circPoly v + (-1 / 2 : ℂ) • circPoly w) := by
    funext t
    rw [h1, circPoly_add, circPoly_add, circPoly_smul, circPoly_smul]
    rfl
  rw [h2]
  refine (eLpNorm_add_le hp1).trans ((add_le_add_right (eLpNorm_add_le hp1) _).trans ?_)
  rw [eLpNorm_const_smul, eLpNorm_const_smul, enorm_half (Or.inl rfl), enorm_half (Or.inr rfl)]
  set F := eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle
  calc _ ≤ K * F + (2⁻¹ * (K * F) + 2⁻¹ * (K * (K * F))) := by
        gcongr
        exact hw.trans (by gcongr)
    _ = _ := by ring

end

/-- The multipliers with the coefficients `ε_ℓ ∈ {−1, 0, 1}` on the dyadic blocks closed on the
left, on those closed on the right, and on the closed dyadic blocks are bounded on the trigonometric
polynomials in `L^p (𝕋; X)`, uniformly in the coefficients, if `X` is a UMD space. The constant is
`C β = K + ½ K + ½ K²`, where `K = C₀ β⁸ ħ²` is the constant of
`exists_eLpNorm_fourierInv_dyadicSign_le'`. -/
theorem exists_eLpNorm_blockSign_le : ∃ C : ℝ≥0∞ → ℝ≥0∞, (∀ β, β ≠ ⊤ → C β ≠ ⊤) ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p →
    ∀ β : ℝ≥0∞, IsUMDBound X p β → ∀ ε : ℕ → ℝ, (∀ ℓ, ε ℓ = 1 ∨ ε ℓ = 0 ∨ ε ℓ = -1) →
    ∀ (a : ℤ → ℝ), a = leftBlockSign ε ∨ a = rightBlockSign ε ∨ a = closedBlockSign ε →
    ∀ c : ℤ →₀ X, eLpNorm (circPoly (mulCoeff (fun n => (a n : ℂ)) c)) (ENNReal.ofReal p)
        haarAddCircle ≤ C β * eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_fourierInv_dyadicSign_le'
  set K : ℝ≥0∞ → ℝ≥0∞ := fun β => C₀ * β ^ 8 * dyadicHilbertBound β ^ 2
  refine ⟨fun β => K β + (2⁻¹ * K β + 2⁻¹ * K β ^ 2), fun β hβ => ?_, ?_⟩
  · have h1 : K β ≠ ⊤ := by
      simp only [K, dyadicHilbertBound]
      finiteness
    have h2 : (2⁻¹ : ℝ≥0∞) ≠ ⊤ := by simp
    finiteness
  · intro X _ _ _ p hp β hβ ε hε a ha c
    have hK : DyadicSignBound X p (K β) := fun η hη G hG hG' => hC₀ X p hp β hβ η hη G hG hG'
    rcases ha with rfl | rfl | rfl
    · exact (eLpNorm_leftBlockSign_le hp hK hε c).trans (by gcongr; exact le_self_add)
    · exact (eLpNorm_rightBlockSign_le hp hK hε c).trans (by gcongr; exact le_self_add)
    · exact eLpNorm_closedBlockSign_le hp hK hε c

end HarmonicAnalysis
