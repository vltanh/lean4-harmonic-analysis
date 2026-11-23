/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Burkholder.HilbertTransform
public import HarmonicAnalysis.VectorValued.McConnell.Multiplier
public import Mathlib.Data.Int.Log
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Littlewood–Paley inequalities for every choice of the signs

**Theorem** (`exists_eLpNorm_fourierInv_dyadicSign_le`; T. R. McConnell, *On Fourier multiplier
transformations of Banach-valued functions*, Trans. Amer. Math. Soc. 285 (1984), 739–757, Theorem
1.3 and (1.13), p. 742, for `n = 1`, the direction from UMD spaces to the inequalities). Let `X` be
a complex UMD space with a `UMD_p` constant `β`, `1 < p < ∞`. For all signs `ε_j`, `ε'_j`, `j ∈ ℤ`,
the multiplier `m = Σ_j ε_j 1_{[2^j, 2^{j+1})} + Σ_j ε'_j 1_{(−2^{j+1}, −2^j]}` satisfies (1.13):
`c⁻¹ ‖f‖_p ≤ ‖T_m f‖_p ≤ c ‖f‖_p`, with `c = C β⁸ ħ²`, where `C` is an absolute constant and `ħ` is
the bound of the Hilbert transform (`hilbertBound β = 2 β² + 1`, by Burkholder's theorem, which the
source recalls on p. 741). Here `f = 𝓕⁻ G ∈ L^p` with `G ∈ L¹` (the
source has Schwartz functions in (3.18)). The converse, which the source deduces from a result of
Bourgain (p. 756), is not treated.

## The proof

The proof is McConnell's, pp. 754–756. The Hilbert transform reduces to `f` with spectrum in
`(0, ∞)`. Four multipliers `m_1, …, m_4`, smooth on `ℝ ∖ {0}` and with `m_1 + ⋯ + m_4 = 1` there,
are sums of bumps `φ (2^{2j} |·|)`, `φ (2^{2j+1} |·|)`, `ψ (2^{2j} |·|)`, `ψ (2^{2j+1} |·|)`,
supported in `2^k ≤ |ξ| ≤ 2^{k+1}` and `3/4 · 2^k ≤ |ξ| ≤ 3/2 · 2^k`, where `φ = 1` near `3/2`; they
satisfy the hypothesis of Theorem 1.1 on `ℝ ∖ {0}` (they are not continuous at `0`), and so do
`M (ω, ·) = Σ_j ξ_j (ω) ρ (2^{2j} |·|)` for independent signs `ξ_j`, where `ρ` is supported in
`[5/8, 17/8]` and equal to `1` on `[3/4, 2]`, which contains the supports of `φ` and `ψ` (for `m_2`,
`m_4` the bumps are `ρ (2^{2j+1} |·|)`). As `M² = 1` on the support of `m_1`, Theorem 1.1 compares
`‖T_{m_1} T_m f‖_p` with `(E ‖T_M T_{m_1} T_m f‖_p^p)^{1/p}`; on the positive half of the support of
one bump `m` is almost everywhere a sign times `sign (· − α_j)`, so that the Hilbert transform and
two applications of Burkholder's inequality (2.1) to the Rademacher sums lead back to
`(E ‖T_M T_{m_1} f‖_p^p)^{1/p}`, and Theorem 1.1 is used twice more.

Corrections to the source:

* (3.19) is printed as an equality, and it is a two-sided inequality, by Theorem 1.1;
* `φ (3/2) = 1` (p. 754) is not enough for `ψ` to be smooth;
* in the last display of p. 756, `‖T_{m_1} T_m f‖` stands for `‖T_{m_1} T_m f‖_p^p`;
* by p. 741 the dyadic intervals are all the `[k 2^{−l}, (k + 1) 2^{−l}]`, for which the series
  `T_(ε) f` of p. 742 makes no sense; Theorem 1.3 means the intervals `± [2^j, 2^{j+1})` (p. 755).

Details that differ from the source:

* One function `ρ`, equal to `1` on `[3/4, 2]`, serves `φ` and `ψ`; the source has `ρ = 1` on
  `[1, 2]`, with support in `[1/2, 4]`, for `m_1`, and the same proof for the others (with the
  dilates `ρ (2 ·)`, `ρ (4/3 ·)`, `ρ (8/3 ·)`).
* Theorem 1.1 is applied to finite parts of the sums `m_i` and `M (ω, ·)`, which have compact
  support in `ℝ ∖ {0}`, with constants that do not depend on the number of the terms; the limit is
  taken in (3.17), by dominated convergence and Fatou's lemma.
* The inequality (2.1) is stated for real coefficients, and it is applied on pp. 755–756 to the
  complex coefficients `ε_j e^{iα_j x}` and `e^{−iα_j x}` (here with `2π`). It is used for the real
  and the imaginary parts, whence a factor `2` (`eLpNormRad_smul_le_umd`).
-/

@[expose] public section

open MeasureTheory Filter BanachProbability
open scoped ENNReal FourierTransform Topology

namespace HarmonicAnalysis

/-- `Σ_j ε_j 1_{[2^j, 2^{j+1})}`, a function on `ℝ` that vanishes on `(−∞, 0]`. -/
noncomputable def dyadicSign (ε : ℤ → ℝ) (ξ : ℝ) : ℝ :=
  if 0 < ξ then ε (Int.log 2 ξ) else 0

/-- `dyadicSign ε = ε_j` on `[2^j, 2^{j+1})`. -/
theorem dyadicSign_eq (ε : ℤ → ℝ) {j : ℤ} {ξ : ℝ} (h1 : 2 ^ j ≤ ξ) (h2 : ξ < 2 ^ (j + 1)) :
    dyadicSign ε ξ = ε j := by
  have h0 : 0 < ξ := (zpow_pos two_pos j).trans_le h1
  have h3 : j ≤ Int.log 2 ξ :=
    (Int.zpow_le_iff_le_log one_lt_two h0).1 (by rwa [Nat.cast_ofNat])
  have h4 : Int.log 2 ξ < j + 1 :=
    (Int.lt_zpow_iff_log_lt one_lt_two h0).1 (by rwa [Nat.cast_ofNat])
  rw [dyadicSign, ite_eq_left h0, le_antisymm (Int.lt_add_one_iff.1 h4) h3]

/-- `dyadicSign ε` is bounded by `1`, if `ε_j ∈ {−1, 0, 1}`. -/
theorem abs_dyadicSign_le {ε : ℤ → ℝ} (hε : ∀ j, ε j = 1 ∨ ε j = 0 ∨ ε j = -1) (ξ : ℝ) :
    |dyadicSign ε ξ| ≤ 1 := by
  rw [dyadicSign]
  split_ifs
  · rcases hε (Int.log 2 ξ) with h | h | h <;> simp [h]
  · simp

/-- `dyadicSign ε` is measurable, as `Int.log 2 ξ = ⌊log₂ ξ⌋` for `ξ > 0`. -/
theorem measurable_dyadicSign (ε : ℤ → ℝ) : Measurable (dyadicSign ε) := by
  have h1 : dyadicSign ε = fun ξ => if 0 < ξ then ε ⌊Real.logb 2 ξ⌋ else 0 := by
    funext ξ
    rw [dyadicSign]
    refine ite_congr rfl (fun hξ => ?_) fun _ => rfl
    have h2 := Real.floor_logb_natCast (b := 2) hξ.le
    rw [Nat.cast_ofNat] at h2
    rw [h2]
  rw [h1]
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  exact (measurable_from_top (f := ε)).comp
    (Int.measurable_floor.comp (Real.measurable_log.div_const _))

/-! ### The bumps -/

/-- What Theorem 1.1 needs of the bumps `φ (|·|)`, `ψ (|·|)` and `ρ (|·|)`: they are of class `C²`,
vanish outside `{5/8 ≤ |ξ| ≤ 17/8}`, and `|ξ|^k |g^{(k)} (ξ)| ≤ c` for `k ≤ 2`. As `17/8 < 4 · 5/8`,
the supports of the dilates of `g` by different powers of `4` are disjoint. -/
private structure IsBump (g : ℝ → ℂ) (c : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 g
  supp : ∀ ξ, g ξ ≠ 0 → 5 / 8 ≤ |ξ| ∧ |ξ| ≤ 17 / 8
  bound : ∀ k ≤ 2, ∀ ξ, |ξ| ^ k * ‖iteratedDeriv k g ξ‖ ≤ c

/-- The derivatives of a function that vanishes outside `{5/8 ≤ |ξ| ≤ 17/8}` vanish there. -/
private theorem supp_iteratedDeriv {g : ℝ → ℂ}
    (hg : ∀ ξ, g ξ ≠ 0 → 5 / 8 ≤ |ξ| ∧ |ξ| ≤ 17 / 8) (k : ℕ) {ξ : ℝ}
    (hξ : iteratedDeriv k g ξ ≠ 0) : 5 / 8 ≤ |ξ| ∧ |ξ| ≤ 17 / 8 := by
  have hcl : IsClosed {ξ : ℝ | 5 / 8 ≤ |ξ| ∧ |ξ| ≤ 17 / 8} :=
    (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have h1 : ξ ∈ Function.support (iteratedFDeriv ℝ k g) := fun h => hξ <| by
    rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, h, norm_zero]
  exact closure_minimal (fun η hη => hg η hη) hcl (support_iteratedFDeriv_subset k h1)

/-- A bump on `[5/8, 17/8]`, extended to an even function, satisfies (3.1), which is (1.10), with
some constant. -/
private theorem exists_isBump {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hs : ∀ ξ, h ξ ≠ 0 → 5 / 8 ≤ ξ ∧ ξ ≤ 17 / 8) :
    ∃ c, IsBump (fun ξ => ((h |ξ| : ℝ) : ℂ)) c := by
  have hneg : ∀ ξ ≤ 0, h ξ = 0 := fun ξ hξ => by
    by_contra h0
    linarith [(hs ξ h0).1]
  have hsum : (fun ξ => ((h |ξ| : ℝ) : ℂ)) = fun ξ => ((h ξ + h (-ξ) : ℝ) : ℂ) := by
    funext ξ
    rcases le_total 0 ξ with h0 | h0
    · rw [abs_of_nonneg h0, hneg (-ξ) (by linarith), add_zero]
    · rw [abs_of_nonpos h0, hneg ξ h0, zero_add]
  have hC : ContDiff ℝ 2 fun ξ => ((h |ξ| : ℝ) : ℂ) := by
    rw [hsum]
    exact Complex.ofRealCLM.contDiff.comp (hh.add (hh.comp contDiff_neg))
  have hsupp : ∀ ξ, ((h |ξ| : ℝ) : ℂ) ≠ 0 → 5 / 8 ≤ |ξ| ∧ |ξ| ≤ 17 / 8 := fun ξ hξ =>
    hs _ (by simpa using hξ)
  obtain ⟨c, hc⟩ := exists_isMihlin hC (HasCompactSupport.intro
    (isCompact_Icc (a := (-(17 / 8) : ℝ)) (b := 17 / 8)) fun ξ hξ => by
      by_contra h0
      exact hξ (abs_le.1 (hsupp ξ h0).2))
  refine ⟨c, hC, hsupp, fun k hk ξ => ?_⟩
  by_cases h0 : iteratedDeriv k (fun ξ => ((h |ξ| : ℝ) : ℂ)) ξ = 0
  · simpa [h0] using (abs_nonneg (h 1)).trans (by simpa using hc.2 0 (by norm_num) 1 one_ne_zero)
  · refine hc.2 k hk ξ fun h1 => ?_
    have h2 := (supp_iteratedDeriv hsupp k h0).1
    rw [h1, abs_zero] at h2
    norm_num at h2

private theorem IsBump.mono {g : ℝ → ℂ} {c c' : ℝ} (hg : IsBump g c) (hc : c ≤ c') : IsBump g c' :=
  ⟨hg.contDiff, hg.supp, fun k hk ξ => (hg.bound k hk ξ).trans hc⟩

/-- `φ`, smooth, supported in `[1, 2]`, with `φ = 1` on `[5/4, 7/4]`. (The source has `φ (3/2) = 1`,
which is not enough for `ψ` to be smooth.) -/
private noncomputable def lpPhi : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- A cutoff, `1` on `[3/4, 3/2]` and supported in `[5/8, 13/8]`, for the definition of `ψ`. -/
private noncomputable def lpChi : ContDiffBump (9 / 8 : ℝ) :=
  ⟨3 / 8, 1 / 2, by norm_num, by norm_num⟩

/-- `ρ`, smooth, supported in `[5/8, 17/8]`, with `ρ = 1` on `[3/4, 2]`, for `φ` and `ψ`. (The
function `ρ` of the source, for `m_1`, has support in `[1/2, 4]` and `ρ = 1` on `[1, 2]`.) -/
private noncomputable def lpRho : ContDiffBump (11 / 8 : ℝ) :=
  ⟨5 / 8, 3 / 4, by norm_num, by norm_num⟩

/-- `ψ`: `ψ (λ) = 1 − φ (λ)` for `1 ≤ λ ≤ 3/2`, `ψ (λ) = 1 − φ (2λ)` for `3/4 ≤ λ ≤ 1`, and `0`
elsewhere. The cutoff makes the smoothness obvious: `1 − φ (λ) − φ (2λ)` vanishes for
`5/8 ≤ λ ≤ 3/4` and for `3/2 ≤ λ ≤ 13/8`. -/
private noncomputable def lpPsi (x : ℝ) : ℝ := (1 - lpPhi x - lpPhi (2 * x)) * lpChi x

private theorem lpPhi_one {x : ℝ} (h1 : 5 / 4 ≤ x) (h2 : x ≤ 7 / 4) : lpPhi x = 1 := by
  refine lpPhi.one_of_mem_closedBall ?_
  rw [Real.closedBall_eq_Icc]
  exact ⟨by norm_num [lpPhi]; linarith, by norm_num [lpPhi]; linarith⟩

private theorem lpPhi_ne_zero {x : ℝ} (h : lpPhi x ≠ 0) : 1 < x ∧ x < 2 := by
  have h1 : x ∈ Function.support lpPhi := h
  rw [lpPhi.support_eq, Real.ball_eq_Ioo] at h1
  norm_num [lpPhi] at h1
  exact h1

private theorem lpPhi_zero {x : ℝ} (h : x ≤ 1 ∨ 2 ≤ x) : lpPhi x = 0 := by
  by_contra h0
  have h1 := lpPhi_ne_zero h0
  rcases h with h | h <;> linarith

private theorem lpRho_one {x : ℝ} (h1 : 3 / 4 ≤ x) (h2 : x ≤ 2) : lpRho x = 1 := by
  refine lpRho.one_of_mem_closedBall ?_
  rw [Real.closedBall_eq_Icc]
  exact ⟨by norm_num [lpRho]; linarith, by norm_num [lpRho]; linarith⟩

private theorem lpRho_ne_zero {x : ℝ} (h : lpRho x ≠ 0) : 5 / 8 ≤ x ∧ x ≤ 17 / 8 := by
  have h1 : x ∈ Function.support lpRho := h
  rw [lpRho.support_eq, Real.ball_eq_Ioo] at h1
  norm_num [lpRho] at h1
  exact ⟨h1.1.le, h1.2.le⟩

private theorem lpChi_one {x : ℝ} (h1 : 3 / 4 ≤ x) (h2 : x ≤ 3 / 2) : lpChi x = 1 := by
  refine lpChi.one_of_mem_closedBall ?_
  rw [Real.closedBall_eq_Icc]
  exact ⟨by norm_num [lpChi]; linarith, by norm_num [lpChi]; linarith⟩

private theorem lpPsi_ne_zero {x : ℝ} (h : lpPsi x ≠ 0) : 3 / 4 ≤ x ∧ x ≤ 3 / 2 := by
  have h1 : x ∈ Function.support lpChi := right_ne_zero_of_mul h
  rw [lpChi.support_eq, Real.ball_eq_Ioo] at h1
  norm_num [lpChi] at h1
  constructor
  · by_contra h2
    refine h ?_
    rw [lpPsi, lpPhi_zero (x := x) (Or.inl (by linarith)),
      lpPhi_one (x := 2 * x) (by linarith) (by linarith)]
    ring
  · by_contra h2
    refine h ?_
    rw [lpPsi, lpPhi_zero (x := 2 * x) (Or.inr (by linarith)),
      lpPhi_one (x := x) (by linarith) (by linarith)]
    ring

/-- `φ (λ) + ψ (λ) + ψ (λ/2) = 1` for `1 ≤ λ < 2`. -/
private theorem lpPhi_add_lpPsi {x : ℝ} (h1 : 1 ≤ x) (h2 : x < 2) :
    lpPhi x + lpPsi x + lpPsi (x / 2) = 1 := by
  rcases le_total x (3 / 2) with h3 | h3
  · have h4 : lpPsi (x / 2) = 0 := by
      rcases h3.lt_or_eq with h5 | h5
      · by_contra h0
        linarith [(lpPsi_ne_zero h0).1]
      · rw [h5, lpPsi, lpPhi_one (x := 2 * (3 / 2 / 2)) (by norm_num) (by norm_num),
          lpPhi_zero (x := 3 / 2 / 2) (by norm_num)]
        ring
    rw [h4, lpPsi, lpChi_one (by linarith) h3, lpPhi_zero (x := 2 * x) (Or.inr (by linarith))]
    ring
  · have h4 : lpPsi x = 0 := by
      rcases h3.lt_or_eq with h5 | h5
      · by_contra h0
        linarith [(lpPsi_ne_zero h0).2]
      · rw [← h5, lpPsi, lpPhi_one (x := 3 / 2) (by norm_num) (by norm_num),
          lpPhi_zero (x := 2 * (3 / 2)) (by norm_num)]
        ring
    rw [h4, lpPsi, lpChi_one (x := x / 2) (by linarith) (by linarith),
      lpPhi_zero (x := x / 2) (Or.inl (by linarith)), mul_div_cancel₀ x two_ne_zero]
    ring

private theorem contDiff_lpPsi : ContDiff ℝ 2 lpPsi :=
  ((contDiff_const.sub lpPhi.contDiff).sub
    (lpPhi.contDiff.comp (contDiff_const.mul contDiff_id))).mul lpChi.contDiff

/-- The even bumps `φ (|·|)`, `ψ (|·|)`, `ρ (|·|)` of the source. -/
private noncomputable def evenBump (h : ℝ → ℝ) (ξ : ℝ) : ℂ := ((h |ξ| : ℝ) : ℂ)

/-- The three bumps satisfy (3.1), which is (1.10), with one constant. -/
private theorem exists_isBump_all : ∃ c, IsBump (evenBump lpPhi) c ∧ IsBump (evenBump lpPsi) c ∧
    IsBump (evenBump lpRho) c := by
  obtain ⟨c1, h1⟩ := exists_isBump (h := lpPhi) lpPhi.contDiff fun ξ hξ => by
    have := lpPhi_ne_zero hξ
    constructor <;> linarith
  obtain ⟨c2, h2⟩ := exists_isBump (h := lpPsi) contDiff_lpPsi fun ξ hξ => by
    have := lpPsi_ne_zero hξ
    constructor <;> linarith
  obtain ⟨c3, h3⟩ := exists_isBump (h := lpRho) lpRho.contDiff fun ξ hξ => lpRho_ne_zero hξ
  exact ⟨max c1 (max c2 c3), h1.mono (le_max_left _ _),
    h2.mono ((le_max_left _ _).trans (le_max_right _ _)),
    h3.mono ((le_max_right _ _).trans (le_max_right _ _))⟩

/-! ### Sums of dilated bumps -/

/-- The dilation factor `2^{−k}`, `k = a + 2i`. -/
private noncomputable def dil (a : ℤ) (i : ℕ) : ℝ := (2 : ℝ) ^ (-(a + 2 * (i : ℤ)))

private theorem dil_pos (a : ℤ) (i : ℕ) : 0 < dil a i := by
  unfold dil
  positivity

/-- For `i < j` the dilation factors differ at least by the factor `4`. -/
private theorem four_mul_dil_le (a : ℤ) {i j : ℕ} (hij : i < j) : 4 * dil a j ≤ dil a i := by
  have h : (4 : ℝ) = 2 ^ (2 : ℤ) := by norm_num
  rw [dil, dil, h, ← zpow_add₀ two_ne_zero]
  exact zpow_le_zpow_right₀ one_le_two (by omega)

/-- At most one of the points `2^{−a−2i} ξ` lies in `{5/8 ≤ |ξ| ≤ 17/8}`. -/
private theorem dil_unique {a : ℤ} {i j : ℕ} {ξ : ℝ}
    (hi : 5 / 8 ≤ |dil a i * ξ| ∧ |dil a i * ξ| ≤ 17 / 8)
    (hj : 5 / 8 ≤ |dil a j * ξ| ∧ |dil a j * ξ| ≤ 17 / 8) : i = j := by
  have key : ∀ {i j : ℕ}, i < j → 4 * |dil a j * ξ| ≤ |dil a i * ξ| := fun {i j} hij => by
    rw [abs_mul, abs_mul, abs_of_pos (dil_pos a j), abs_of_pos (dil_pos a i), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (four_mul_dil_le a hij) (abs_nonneg ξ)
  rcases lt_trichotomy i j with h | h | h
  · linarith [key h]
  · exact h
  · linarith [key h]

/-- `Σ_i u_i g (2^{−a−2i} ξ)`, a finite part of one of the sums `m_1, …, m_4` and
`M (ω, ·)`. -/
private noncomputable def bumpSum (g : ℝ → ℂ) (a : ℤ) {K : ℕ} (u : Fin K → ℂ) (ξ : ℝ) : ℂ :=
  ∑ i, u i * g (dil a i * ξ)

/-- A sum with at most one term `≠ 0` is bounded by the bound of its terms. -/
private theorem norm_sum_le_of_unique {ι : Type*} [Fintype ι] {x : ι → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hx : ∀ i, ‖x i‖ ≤ c) (hu : ∀ i j, x i ≠ 0 → x j ≠ 0 → i = j) : ‖∑ i, x i‖ ≤ c := by
  by_cases h : ∃ i, x i ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i (fun j _ hj => by
      by_contra h0
      exact hj (hu j i h0 hi)) fun h => absurd (Finset.mem_univ i) h]
    exact hx i
  · push Not at h
    simpa [h] using hc

private theorem IsBump.nonneg {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) : 0 ≤ c :=
  le_trans (by positivity) (hg.bound 0 (by norm_num) 0)

private theorem contDiff_bump_dil {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) (i : ℕ) (u : ℂ) :
    ContDiff ℝ 2 fun ξ => u * g (dil a i * ξ) :=
  contDiff_const.mul (hg.contDiff.comp (contDiff_const.mul contDiff_id))

private theorem contDiff_bumpSum {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) {K : ℕ}
    (u : Fin K → ℂ) : ContDiff ℝ 2 (bumpSum g a u) :=
  ContDiff.sum fun i _ => contDiff_bump_dil hg a i.1 (u i)

private theorem iteratedDeriv_bumpSum {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) {K : ℕ}
    (u : Fin K → ℂ) {k : ℕ} (hk : k ≤ 2) (ξ : ℝ) :
    iteratedDeriv k (bumpSum g a u) ξ =
      ∑ i, u i * (dil a i ^ k • iteratedDeriv k g (dil a i * ξ)) := by
  have hk' : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  have h1 := iteratedDeriv_fun_sum (x := ξ) (n := k) (I := (Finset.univ : Finset (Fin K)))
    (f := fun i ξ => u i * g (dil a i * ξ))
    fun i _ => ((contDiff_bump_dil hg a i (u i)).of_le hk').contDiffAt
  refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_smul (hg.contDiff.of_le hk')]

/-- The sums of the dilated bumps satisfy (3.1), which is (1.10), with a constant that depends
neither on the coefficients, of modulus at most `1`, nor on the number of the terms (p. 755). -/
private theorem isMihlin_bumpSum {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) {K : ℕ}
    {u : Fin K → ℂ} (hu : ∀ i, ‖u i‖ ≤ 1) : IsMihlin (bumpSum g a u) c := by
  refine ⟨(contDiff_bumpSum hg a u).contDiffOn, fun k hk ξ _ => ?_⟩
  have h : ((|ξ| ^ k : ℝ) : ℂ) * iteratedDeriv k (bumpSum g a u) ξ =
      ∑ i, u i * (((|dil a i * ξ| ^ k : ℝ) : ℂ) * iteratedDeriv k g (dil a i * ξ)) := by
    rw [iteratedDeriv_bumpSum hg a u hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_of_pos (dil_pos a i), mul_pow, Complex.real_smul]
    push_cast
    ring
  rw [← abs_of_nonneg (pow_nonneg (abs_nonneg ξ) k), ← Real.norm_eq_abs, ← Complex.norm_real,
    ← norm_mul, h]
  refine norm_sum_le_of_unique hg.nonneg (fun i => ?_) fun i j hi hj => Fin.ext ?_
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (abs_nonneg _) k)]
    exact (mul_le_of_le_one_left (by positivity) (hu i)).trans (hg.bound k hk _)
  · exact dil_unique
      (supp_iteratedDeriv hg.supp k (right_ne_zero_of_mul (right_ne_zero_of_mul hi)))
      (supp_iteratedDeriv hg.supp k (right_ne_zero_of_mul (right_ne_zero_of_mul hj)))

/-- The sums of the dilated bumps are bounded. -/
private theorem norm_bumpSum_le {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) {K : ℕ}
    {u : Fin K → ℂ} (hu : ∀ i, ‖u i‖ ≤ 1) (ξ : ℝ) : ‖bumpSum g a u ξ‖ ≤ c := by
  refine norm_sum_le_of_unique hg.nonneg (fun i => ?_) fun i j hi hj => Fin.ext ?_
  · have h := hg.bound 0 (by norm_num) (dil a i * ξ)
    rw [pow_zero, one_mul, iteratedDeriv_zero] at h
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hu i)).trans h
  · exact dil_unique (hg.supp _ (right_ne_zero_of_mul hi)) (hg.supp _ (right_ne_zero_of_mul hj))

/-- The finite sums vanish near `0` and near infinity. -/
private theorem bumpSum_ne_zero {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) {a : ℤ} {K : ℕ}
    {u : Fin K → ℂ} {ξ : ℝ} (h : bumpSum g a u ξ ≠ 0) :
    5 / 8 ≤ dil a 0 * |ξ| ∧ dil a K * |ξ| ≤ 17 / 8 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := hg.supp _ (right_ne_zero_of_mul hi)
  rw [abs_mul, abs_of_pos (dil_pos a i)] at h1
  have hmono : ∀ {i j : ℕ}, i ≤ j → dil a j ≤ dil a i := fun {i j} hij =>
    zpow_le_zpow_right₀ one_le_two (by omega)
  exact ⟨h1.1.trans (mul_le_mul_of_nonneg_right (hmono (Nat.zero_le _)) (abs_nonneg ξ)),
    (mul_le_mul_of_nonneg_right (hmono i.2.le) (abs_nonneg ξ)).trans h1.2⟩

private theorem hasCompactSupport_bumpSum {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) {K : ℕ}
    (u : Fin K → ℂ) : HasCompactSupport (bumpSum g a u) := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := -(17 / 8 / dil a K)) (b := 17 / 8 / dil a K)) fun ξ hξ => ?_
  by_contra h
  have h1 := (bumpSum_ne_zero hg h).2
  rw [← le_div_iff₀' (dil_pos a K)] at h1
  exact hξ (abs_le.1 h1)

private theorem zero_notMem_tsupport_bumpSum {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) {K : ℕ}
    (u : Fin K → ℂ) : (0 : ℝ) ∉ tsupport (bumpSum g a u) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  have h : ∀ᶠ ξ : ℝ in 𝓝 0, dil a 0 * |ξ| < 5 / 8 := by
    refine ContinuousAt.eventually_lt (by fun_prop) continuousAt_const ?_
    norm_num
  filter_upwards [h] with ξ hξ
  by_contra h0
  linarith [(bumpSum_ne_zero hg h0).1]

/-! ### Fourier multipliers -/

section Multipliers

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

private theorem integrable_bdd_smul {m : ℝ → ℂ} {c : ℝ} (hm : AEStronglyMeasurable m volume)
    (hc : ∀ ξ, ‖m ξ‖ ≤ c) {G : ℝ → X} (hG : Integrable G) : Integrable fun ξ => m ξ • G ξ :=
  hG.bdd_smul c hm (ae_of_all _ hc)

/-- `𝓕⁻` is linear. -/
private theorem fourierInv_add' {G H : ℝ → X} (hG : Integrable G) (hH : Integrable H) (x : ℝ) :
    𝓕⁻ (fun ξ => G ξ + H ξ) x = 𝓕⁻ G x + 𝓕⁻ H x := by
  simp only [fourierInv_eq_expChar, smul_add]
  exact integral_add (integrable_expChar_smul hG x) (integrable_expChar_smul hH x)

/-! ### Burkholder's inequality and the modulated Hilbert transforms -/

variable [CompleteSpace X]

/-- The two inequalities on p. 756: with the norm `(E ‖·‖_p^p)^{1/p}` of the Rademacher sums,
`‖Σ_j ε_j ξ_j e^{2πiα_j·} H_0 * (e^{−2πiα_j·} g_j)‖ ≤ 4 β² ħ ‖Σ_j ξ_j g_j‖`. Burkholder's inequality
(2.1) is applied at each point `x` to the Rademacher sums, whose terms are martingale differences,
with the coefficients `ε_j e^{2πiα_j x}` and `e^{−2πiα_j x}` of modulus `1`; each time it costs the
factor `2 β`, as the coefficients are complex. Between these two steps `H_0` is applied to the sum,
for each choice of the signs, with (3.20). Here `s_j = ε_j`, and the formula
`H_α * g (x) = e^{2πiαx} H_0 * (e^{−2πiα·} g) (x)` of p. 755 is `fourierInv_sign_sub`. -/
private theorem eLpNormRad_fourierInv_sign_sub_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {K : ℕ} {G : Fin K → ℝ → X} (hG : ∀ k, Integrable (G k))
    (hf : ∀ k, MemLp (𝓕⁻ (G k)) (ENNReal.ofReal p) volume) {s : Fin K → ℝ} (hs : ∀ k, |s k| ≤ 1)
    (α : Fin K → ℝ) :
    eLpNormRad (fun k => 𝓕⁻ fun ξ => ((s k * Real.sign (ξ - α k) : ℝ) : ℂ) • G k ξ) p volume ≤
      4 * β ^ 2 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
  set G' : Fin K → ℝ → X := fun k ξ => G k (ξ + α k)
  have hG' : ∀ k, Integrable (G' k) := fun k => (hG k).comp_add_right (α k)
  have hinv : ∀ k, 𝓕⁻ (G' k) = fun x => expChar (-α k) x • 𝓕⁻ (G k) x := fun k =>
    funext fun x => fourierInv_smul_expChar (α k) (G k) x
  have hcont := fun k => continuous_fourierInv_of_integrable (integrable_sign_smul (hG' k))
  simp only [fourierInv_sign_sub]
  -- (2.1) with the coefficients `ε_j e^{2πiα_j x}`
  have h1 := eLpNormRad_smul_le_umd hp.le hβ (μ := volume)
    (c := fun k x => (s k : ℂ) * expChar (α k) x)
    (f := fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ)
    (fun k x => by
      rw [norm_mul, norm_expChar, mul_one, Complex.norm_real]
      exact hs k)
    (fun k => ((continuous_const.mul (continuous_expChar _))).aestronglyMeasurable)
    fun k => (hcont k).aestronglyMeasurable
  -- (3.20)
  have h2 : eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ) p volume ≤
      hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G' k)) p volume :=
    eLpNormRad_fourierInv_sign_le hp (fun _ => eLpNorm_fourierInv_sign_le hp hβ) hG' fun k => by
      rw [hinv]
      exact memLp_expChar_smul (hf k) _
  -- (2.1) with the coefficients `e^{−2πiα_j x}`
  have h3 : eLpNormRad (fun k => 𝓕⁻ (G' k)) p volume ≤
      2 * β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by
    simp only [hinv]
    exact eLpNormRad_smul_le_umd hp.le hβ (c := fun k => expChar (-α k))
      (fun k x => (norm_expChar _ _).le) (fun k => (continuous_expChar _).aestronglyMeasurable)
      fun k => (hf k).aestronglyMeasurable
  calc _ ≤ 2 * β * eLpNormRad (fun k => 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G' k ξ) p volume := h1
    _ ≤ 2 * β * (hilbertBound β * (2 * β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume)) := by
        gcongr
        exact h2.trans (by gcongr)
    _ = 4 * β ^ 2 * hilbertBound β * eLpNormRad (fun k => 𝓕⁻ (G k)) p volume := by ring

/-! ### The estimate (3.18) -/

/-- Theorem 1.1 for the sums of the dilated bumps. -/
private theorem eLpNorm_bumpSum_smul_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : IsUMDBound X p β)
    {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) {K : ℕ} {u : Fin K → ℂ} (hu : ∀ i, ‖u i‖ ≤ 1)
    {G : ℝ → X} (hG : Integrable G) :
    eLpNorm (𝓕⁻ fun ξ => bumpSum g a u ξ • G ξ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * (1088 * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume :=
  eLpNorm_fourierInv_mihlin_le_of_hasCompactSupport hp hβ (isMihlin_bumpSum hg a hu)
    (hasCompactSupport_bumpSum hg a u) (zero_notMem_tsupport_bumpSum hg a u) hG

/-- The signs `ξ_j (ω)` as coefficients. -/
private noncomputable def coinC {K : ℕ} (σ : Fin K → Bool) (i : Fin K) : ℂ :=
  ((SignCube.coin (σ i) : ℝ) : ℂ)

private theorem norm_coinC_le {K : ℕ} (σ : Fin K → Bool) (i : Fin K) : ‖coinC σ i‖ ≤ 1 := by
  rcases SignCube.coin_eq_one_or_eq_neg_one (σ i) with h | h <;> simp [coinC, h]

private theorem coinC_mul_self {K : ℕ} (σ : Fin K → Bool) (i : Fin K) :
    coinC σ i * coinC σ i = 1 := by
  rcases SignCube.coin_eq_one_or_eq_neg_one (σ i) with h | h <;> simp [coinC, h]

omit [CompleteSpace X] in
private theorem integrable_bump_smul {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (D : ℝ) {G : ℝ → X}
    (hG : Integrable G) : Integrable fun ξ => g (D * ξ) • G ξ := by
  refine integrable_bdd_smul (c := c)
    (hg.contDiff.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (fun ξ => ?_) hG
  simpa using hg.bound 0 (by norm_num) (D * ξ)

omit [CompleteSpace X] in
/-- `T_M T_{m_i} f = Σ_j ξ_j Φ_j * f`. -/
private theorem sum_coin_fourierInv_bump {g : ℝ → ℂ} {c : ℝ} (hg : IsBump g c) (a : ℤ) {K : ℕ}
    (σ : Fin K → Bool) {G : ℝ → X} (hG : Integrable G) :
    (fun x => ∑ i : Fin K, SignCube.coin (σ i) • 𝓕⁻ (fun ξ => g (dil a i * ξ) • G ξ) x) =
      𝓕⁻ fun ξ => bumpSum g a (coinC σ) ξ • G ξ := by
  rw [← funext (fourierInv_sum_smul (fun i : Fin K => integrable_bump_smul hg (dil a i) hG) _)]
  congr 1
  funext ξ
  rw [bumpSum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coinC, mul_smul, Complex.coe_smul]

/-- `ρ (2^{−k} ξ) = 1` on the support of the bump with the index `k`, and the other bumps `ρ` vanish
there: `M (ω, ·) g (2^{−k} ·) = ξ_k (ω) g (2^{−k} ·)`. -/
private theorem bumpSum_rho_mul {c : ℝ} (hρ : IsBump (evenBump lpRho) c) {g : ℝ → ℂ}
    (hgs : ∀ ξ, g ξ ≠ 0 → 3 / 4 ≤ |ξ| ∧ |ξ| < 2) (a : ℤ) {K : ℕ} (u v : Fin K → ℂ) (ξ : ℝ) :
    bumpSum (evenBump lpRho) a u ξ * bumpSum g a v ξ = bumpSum g a (fun i => u i * v i) ξ := by
  rw [bumpSum, bumpSum, bumpSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h0 : g (dil a i * ξ) = 0
  · simp [h0]
  have h1 := hgs _ h0
  have h2 : evenBump lpRho (dil a i * ξ) = 1 := by
    rw [evenBump, lpRho_one h1.1 h1.2.le, Complex.ofReal_one]
  rw [Finset.sum_eq_single i (fun j _ hj => ?_) fun h => absurd (Finset.mem_univ i) h, h2]
  · ring
  · by_contra h3
    exact hj (Fin.ext (dil_unique (hρ.supp _ (right_ne_zero_of_mul h3))
      (hρ.supp _ (by rw [h2]; exact one_ne_zero))))

/-- (3.19), with the constants of Theorem 1.1 (the source has an equality):
`‖T_{m_i} h‖_p ≤ C (E ‖T_M T_{m_i} h‖_p^p)^{1/p}`, since `T_{m_i} h = T_M T_M T_{m_i} h`. -/
private theorem eLpNorm_bumpSum_le_eLpNormRad {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {c : ℝ} (hρ : IsBump (evenBump lpRho) c) {g : ℝ → ℂ} (hg : IsBump g c)
    (hgs : ∀ ξ, g ξ ≠ 0 → 3 / 4 ≤ |ξ| ∧ |ξ| < 2) (a : ℤ) (K : ℕ) {H : ℝ → X} (hH : Integrable H) :
    eLpNorm (𝓕⁻ fun ξ => bumpSum g a (fun _ : Fin K => 1) ξ • H ξ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal c * (1088 * β ^ 2) *
        eLpNormRad (fun i : Fin K => 𝓕⁻ fun ξ => g (dil a i * ξ) • H ξ) p volume := by
  refine le_mul_eLpNormRad_of_forall_le (by linarith) (fun i => (continuous_fourierInv_of_integrable
    (integrable_bump_smul hg _ hH)).aestronglyMeasurable) fun σ => ?_
  rw [sum_coin_fourierInv_bump hg a σ hH]
  have h1 : (fun ξ => bumpSum g a (fun _ : Fin K => 1) ξ • H ξ) =
      fun ξ => bumpSum (evenBump lpRho) a (coinC σ) ξ • bumpSum g a (coinC σ) ξ • H ξ := by
    funext ξ
    rw [smul_smul, bumpSum_rho_mul hρ hgs]
    simp only [coinC_mul_self]
  rw [h1]
  exact eLpNorm_bumpSum_smul_le hp hβ hρ a (norm_coinC_le σ)
    (integrable_bdd_smul (contDiff_bumpSum hg a _).continuous.aestronglyMeasurable
      (norm_bumpSum_le hg a (norm_coinC_le σ)) hH)

/-- The end of the proof of (3.18): `(E ‖T_M T_{m_i} f‖_p^p)^{1/p} ≤ C ‖f‖_p` by Theorem 1.1,
twice. -/
private theorem eLpNormRad_bump_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {c : ℝ} (hρ : IsBump (evenBump lpRho) c) {g : ℝ → ℂ} (hg : IsBump g c)
    (hgs : ∀ ξ, g ξ ≠ 0 → 3 / 4 ≤ |ξ| ∧ |ξ| < 2) (a : ℤ) (K : ℕ) {G : ℝ → X} (hG : Integrable G) :
    eLpNormRad (fun i : Fin K => 𝓕⁻ fun ξ => g (dil a i * ξ) • G ξ) p volume ≤
      (ENNReal.ofReal c * (1088 * β ^ 2)) ^ 2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  refine eLpNormRad_le_of_forall_le (by linarith) (fun i => (continuous_fourierInv_of_integrable
    (integrable_bump_smul hg _ hG)).aestronglyMeasurable) fun σ => ?_
  rw [sum_coin_fourierInv_bump hg a σ hG]
  have h1 : (fun ξ => bumpSum g a (coinC σ) ξ • G ξ) =
      fun ξ => bumpSum (evenBump lpRho) a (coinC σ) ξ •
        bumpSum g a (fun _ : Fin K => 1) ξ • G ξ := by
    funext ξ
    rw [smul_smul, bumpSum_rho_mul hρ hgs]
    simp only [mul_one]
  have hu : ∀ _ : Fin K, ‖(1 : ℂ)‖ ≤ 1 := fun _ => norm_one.le
  rw [h1, pow_two, mul_assoc]
  refine (eLpNorm_bumpSum_smul_le hp hβ hρ a (norm_coinC_le σ)
    (integrable_bdd_smul (contDiff_bumpSum hg a _).continuous.aestronglyMeasurable
      (norm_bumpSum_le hg a hu) hG)).trans ?_
  gcongr
  exact eLpNorm_bumpSum_smul_le hp hβ hg a hu hG

omit [NormedSpace ℂ X] [CompleteSpace X] in
/-- The functions that are estimated are in `L^p`. -/
private theorem memLp_of_eLpNorm_le {P β C : ℝ≥0∞} {f u : ℝ → X}
    (hf : MemLp f P volume) (hfin : β ≠ ⊤ ∨ eLpNorm f P volume = 0) (hC : β ≠ ⊤ → C ≠ ⊤)
    (h : eLpNorm u P volume ≤ C * eLpNorm f P volume) : MemLp u P volume := by
  refine h.trans_lt ?_
  rcases hfin with h1 | h1
  · exact ENNReal.mul_lt_top (hC h1).lt_top hf.eLpNorm_lt_top
  · rw [h1, mul_zero]
    exact ENNReal.zero_lt_top

private theorem bumpConst_ne_top (c : ℝ) {β : ℝ≥0∞} (hβ : β ≠ ⊤) :
    ENNReal.ofReal c * (1088 * β ^ 2) ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top hβ))

/-- On `3/4 · 2^k ≤ ξ < 2 · 2^k`, the function `m` is `ε_{k−1}` for `ξ < 2^k` and `ε_k` for
`ξ ≥ 2^k`: there are a sign `s` and a number `α` such that `m = s sign (· − α)` there, except at
`2^k` (p. 755). -/
private theorem exists_dyadicSign_eq {ε : ℤ → ℝ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) (k : ℤ) :
    ∃ s α : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ξ, 3 / 4 * (2 : ℝ) ^ k ≤ ξ → ξ < 2 * 2 ^ k → ξ ≠ 2 ^ k →
      dyadicSign ε ξ = s * Real.sign (ξ - α) := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  -- the values of `m`
  have hlt : ∀ ξ, 3 / 4 * (2 : ℝ) ^ k ≤ ξ → ξ < 2 ^ k → dyadicSign ε ξ = ε (k - 1) := fun ξ h1 h2 =>
    dyadicSign_eq ε (by rw [zpow_sub_one₀ two_ne_zero]; linarith) (by rwa [sub_add_cancel])
  have hge : ∀ ξ, (2 : ℝ) ^ k ≤ ξ → ξ < 2 * 2 ^ k → dyadicSign ε ξ = ε k := fun ξ h1 h2 =>
    dyadicSign_eq ε h1 (by rwa [zpow_add_one₀ two_ne_zero, mul_comm])
  by_cases hε' : ε (k - 1) = ε k
  · refine ⟨ε k, 0, hε k, fun ξ h1 h2 _ => ?_⟩
    rw [sub_zero, Real.sign_of_pos (by linarith), mul_one]
    rcases lt_or_ge ξ (2 ^ k) with h | h
    · rw [hlt ξ h1 h, hε']
    · rw [hge ξ h h2]
  · refine ⟨ε k, 2 ^ k, hε k, fun ξ h1 h2 h3 => ?_⟩
    rcases lt_or_gt_of_ne h3 with h | h
    · rw [hlt ξ h1 h, Real.sign_of_neg (by linarith)]
      rcases hε k with h4 | h4 <;> rcases hε (k - 1) with h5 | h5 <;> simp_all
    · rw [hge ξ h.le h2, Real.sign_of_pos (by linarith), mul_one]

omit [CompleteSpace X] in
/-- `Φ_j * T_m f = s H_α * Φ_j * f` on the Fourier side, with a sign `s = ε_j` and `α = α_j`, for
`f` with spectrum in `(0, ∞)` (p. 755). -/
private theorem exists_bump_dyadicSign_ae_eq {g : ℝ → ℂ}
    (hgs : ∀ ξ, g ξ ≠ 0 → 3 / 4 ≤ |ξ| ∧ |ξ| < 2) (a : ℤ) (i : ℕ) {ε : ℤ → ℝ}
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) {G : ℝ → X} (hG0 : ∀ ξ ≤ 0, G ξ = 0) :
    ∃ s α : ℝ, (s = 1 ∨ s = -1) ∧
      (fun ξ => g (dil a i * ξ) • ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) =ᵐ[volume]
        fun ξ => ((s * Real.sign (ξ - α) : ℝ) : ℂ) • g (dil a i * ξ) • G ξ := by
  obtain ⟨s, α, hs, h⟩ := exists_dyadicSign_eq hε (a + 2 * (i : ℤ))
  refine ⟨s, α, hs, ?_⟩
  filter_upwards [Measure.ae_ne volume ((2 : ℝ) ^ (a + 2 * (i : ℤ)))] with ξ hξ
  rcases le_or_gt ξ 0 with h0 | h0
  · simp [hG0 ξ h0]
  by_cases h1 : g (dil a i * ξ) = 0
  · simp [h1]
  have h2 := hgs _ h1
  have hk : (0 : ℝ) < 2 ^ (a + 2 * (i : ℤ)) := by positivity
  rw [abs_of_pos (mul_pos (dil_pos a i) h0), dil, zpow_neg, inv_mul_eq_div, le_div_iff₀ hk,
    div_lt_iff₀ hk] at h2
  rw [h ξ h2.1 h2.2 hξ, smul_comm]

omit [CompleteSpace X] in
private theorem integrable_dyadicSign_smul {ε : ℤ → ℝ} (hε : ∀ j, ε j = 1 ∨ ε j = -1) {G : ℝ → X}
    (hG : Integrable G) : Integrable fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ :=
  integrable_bdd_smul
    (Complex.measurable_ofReal.comp (measurable_dyadicSign ε)).aestronglyMeasurable (c := 1)
    (fun ξ => by
      rw [Function.comp_apply, Complex.norm_real]
      exact abs_dyadicSign_le (fun j => (hε j).imp_right Or.inr) ξ) hG

/-- **(3.18)**: `‖T_{m_i} T_m f‖_p ≤ c ‖f‖_p` for `f` with spectrum in `(0, ∞)`, for one of the four
families (a finite part of it), `g` being `φ (|·|)` or `ψ (|·|)`. -/
private theorem eLpNorm_bumpSum_dyadicSign_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {c : ℝ} (hρ : IsBump (evenBump lpRho) c) {g : ℝ → ℂ} (hg : IsBump g c)
    (hgs : ∀ ξ, g ξ ≠ 0 → 3 / 4 ≤ |ξ| ∧ |ξ| < 2) (a : ℤ) (K : ℕ) {ε : ℤ → ℝ}
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) {G : ℝ → X} (hG : Integrable G) (hG0 : ∀ ξ ≤ 0, G ξ = 0)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume)
    (hfin : β ≠ ⊤ ∨ eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume = 0) :
    eLpNorm (𝓕⁻ fun ξ => bumpSum g a (fun _ : Fin K => 1) ξ • ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ)
        (ENNReal.ofReal p) volume ≤
      4 * (ENNReal.ofReal c * (1088 * β ^ 2)) ^ 3 * β ^ 2 * hilbertBound β *
        eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set B := ENNReal.ofReal c * (1088 * β ^ 2) with hB
  have hgG : ∀ i : Fin K, Integrable fun ξ => g (dil a i * ξ) • G ξ := fun i =>
    integrable_bump_smul hg (dil a i) hG
  have hmem : ∀ i : Fin K, MemLp (𝓕⁻ fun ξ => g (dil a i * ξ) • G ξ) (ENNReal.ofReal p) volume := by
    intro i
    refine memLp_of_eLpNorm_le hf hfin (bumpConst_ne_top c) ?_
    have h := eLpNorm_bumpSum_smul_le hp hβ hg (a + 2 * (i : ℤ)) (u := fun _ : Fin 1 => 1)
      (fun _ => norm_one.le) hG
    simpa [bumpSum, dil] using h
  -- `Φ_j * T_m f = ε_j H_{α_j} * Φ_j * f`
  choose s α hs hae using fun i : Fin K => exists_bump_dyadicSign_ae_eq hgs a i hε hG0
  have h1 := eLpNorm_bumpSum_le_eLpNormRad hp hβ hρ hg hgs a K (integrable_dyadicSign_smul hε hG)
  have h2 : (fun i : Fin K => 𝓕⁻ fun ξ => g (dil a i * ξ) • ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) =
      fun i : Fin K => 𝓕⁻ fun ξ => ((s i * Real.sign (ξ - α i) : ℝ) : ℂ) • g (dil a i * ξ) • G ξ :=
    funext fun i => funext (Real.fourierInv_congr_ae (hae i))
  have hs1 : ∀ i, |s i| ≤ 1 := fun i => by rcases hs i with h | h <;> simp [h]
  rw [h2] at h1
  -- (2.1), (3.20), (2.1), and Theorem 1.1 twice
  calc _ ≤ B * eLpNormRad (fun i : Fin K => 𝓕⁻ fun ξ =>
        ((s i * Real.sign (ξ - α i) : ℝ) : ℂ) • g (dil a i * ξ) • G ξ) p volume := h1
    _ ≤ B * (4 * β ^ 2 * hilbertBound β *
        eLpNormRad (fun i : Fin K => 𝓕⁻ fun ξ => g (dil a i * ξ) • G ξ) p volume) := by
        gcongr
        exact eLpNormRad_fourierInv_sign_sub_le hp hβ hgG hmem hs1 α
    _ ≤ B * (4 * β ^ 2 * hilbertBound β *
        (B ^ 2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume)) := by
        gcongr
        exact eLpNormRad_bump_le hp hβ hρ hg hgs a K hG
    _ = 4 * B ^ 3 * β ^ 2 * hilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by ring

/-! ### The sum of the four families -/

/-- The sum of finite parts of the four families `m_1, …, m_4`, with the indices `k` from `−2N` to
`2N − 1`. -/
private noncomputable def fourSum (N : ℕ) (ξ : ℝ) : ℂ :=
  bumpSum (evenBump lpPhi) (-(2 * (N : ℤ))) (fun _ : Fin (2 * N) => 1) ξ +
    bumpSum (evenBump lpPhi) (-(2 * (N : ℤ)) + 1) (fun _ : Fin (2 * N) => 1) ξ +
    (bumpSum (evenBump lpPsi) (-(2 * (N : ℤ))) (fun _ : Fin (2 * N) => 1) ξ +
    bumpSum (evenBump lpPsi) (-(2 * (N : ℤ)) + 1) (fun _ : Fin (2 * N) => 1) ξ)

/-- The sums over the even and over the odd indices. -/
private theorem sum_even_add_sum_odd (F : ℤ → ℂ) (a : ℤ) (K : ℕ) :
    ∑ i : Fin K, F (a + 2 * ((i : ℕ) : ℤ)) + ∑ i : Fin K, F (a + 1 + 2 * ((i : ℕ) : ℤ)) =
      ∑ j ∈ Finset.range (2 * K), F (a + (j : ℤ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => F (a + 2 * (i : ℤ))),
    Fin.sum_univ_eq_sum_range (fun i => F (a + 1 + 2 * (i : ℤ)))]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_one, Finset.sum_range_succ,
      Finset.sum_range_succ, ← ih]
    push_cast
    rw [show a + 1 + 2 * (K : ℤ) = a + (2 * K + 1) by ring]
    ring

/-- `φ + ψ` vanishes outside `[1/2, 2]`. -/
private theorem lpPhi_add_lpPsi_eq_zero {x : ℝ} (h : x ≤ 1 / 2 ∨ 2 ≤ x) :
    lpPhi x + lpPsi x = 0 := by
  have h1 : lpPsi x = 0 := by
    by_contra h0
    have h1 := lpPsi_ne_zero h0
    rcases h with h | h <;> linarith
  rw [h1, lpPhi_zero (h.imp (fun h => by linarith) id), add_zero]

private theorem fourSum_eq_sum (N : ℕ) (ξ : ℝ) :
    fourSum N ξ = ((∑ j ∈ Finset.range (2 * (2 * N)),
      (lpPhi ((2 : ℝ) ^ (-(-(2 * (N : ℤ)) + (j : ℤ))) * |ξ|) +
        lpPsi ((2 : ℝ) ^ (-(-(2 * (N : ℤ)) + (j : ℤ))) * |ξ|)) : ℝ) : ℂ) := by
  have h := sum_even_add_sum_odd (fun k => ((lpPhi ((2 : ℝ) ^ (-k) * |ξ|) +
    lpPsi ((2 : ℝ) ^ (-k) * |ξ|) : ℝ) : ℂ)) (-(2 * (N : ℤ))) (2 * N)
  rw [Complex.ofReal_sum, ← h]
  have habs : ∀ (a : ℤ) (i : ℕ), |dil a i * ξ| = dil a i * |ξ| := fun a i => by
    rw [abs_mul, abs_of_pos (dil_pos a i)]
  simp only [fourSum, bumpSum, evenBump, one_mul, habs]
  simp only [dil, Complex.ofReal_add, Finset.sum_add_distrib]
  ring

/-- `m_1 + m_2 + m_3 + m_4 = 1` (p. 755): with `λ = 2^{−k} |ξ| ∈ [1, 2)` the only terms that do not
vanish at `ξ` are `φ (λ)`, `ψ (λ)` and `ψ (λ/2)`. -/
private theorem fourSum_eq_one {ξ : ℝ} (hξ : ξ ≠ 0) {N : ℕ}
    (h1 : -(2 * (N : ℤ)) ≤ Int.log 2 |ξ|) (h2 : Int.log 2 |ξ| + 1 < 2 * (N : ℤ)) :
    fourSum N ξ = 1 := by
  have hpos : 0 < |ξ| := abs_pos.2 hξ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Int.log 2 |ξ| = -(2 * (N : ℤ)) + (n : ℤ) :=
    ⟨(Int.log 2 |ξ| + 2 * N).toNat, by omega⟩
  -- `λ = 2^{−k} |ξ|`
  set x : ℝ := (2 : ℝ) ^ (-(-(2 * (N : ℤ)) + (n : ℤ))) * |ξ| with hx
  have hk : (0 : ℝ) < 2 ^ (-(2 * (N : ℤ)) + (n : ℤ)) := by positivity
  have hx1 : 1 ≤ x := by
    have h := Int.zpow_log_le_self (b := 2) one_lt_two hpos
    rw [hn] at h
    rw [hx, zpow_neg, inv_mul_eq_div, one_le_div hk]
    exact_mod_cast h
  have hx2 : x < 2 := by
    have h := Int.lt_zpow_succ_log_self (b := 2) one_lt_two |ξ|
    rw [hn] at h
    push_cast at h
    rwa [hx, zpow_neg, inv_mul_eq_div, div_lt_iff₀ hk, mul_comm, ← zpow_add_one₀ two_ne_zero]
  have hj : ∀ j : ℕ, (2 : ℝ) ^ (-(-(2 * (N : ℤ)) + (j : ℤ))) * |ξ| =
      (2 : ℝ) ^ ((n : ℤ) - (j : ℤ)) * x := fun j => by
    rw [hx, ← mul_assoc, ← zpow_add₀ two_ne_zero]
    congr 2
    ring
  rw [fourSum_eq_sum, Complex.ofReal_eq_one]
  simp only [hj]
  rw [Finset.sum_eq_add n (n + 1) (Nat.ne_add_one n) (fun j _ hj => ?_)
    (fun h => absurd (Finset.mem_range.2 (by omega)) h)
    (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
  · have e : (2 : ℝ) ^ ((n : ℤ) - ((n + 1 : ℕ) : ℤ)) * x = x / 2 := by
      rw [show (n : ℤ) - ((n + 1 : ℕ) : ℤ) = -1 by omega, zpow_neg_one, inv_mul_eq_div]
    rw [e, sub_self, zpow_zero, one_mul, lpPhi_zero (x := x / 2) (Or.inl (by linarith)), zero_add]
    exact lpPhi_add_lpPsi hx1 hx2
  · refine lpPhi_add_lpPsi_eq_zero ?_
    rcases lt_or_gt_of_ne hj.1 with h | h
    · right
      have h3 : (2 : ℝ) ^ (1 : ℤ) ≤ 2 ^ ((n : ℤ) - (j : ℤ)) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      rw [zpow_one] at h3
      nlinarith
    · left
      have h3 : (2 : ℝ) ^ ((n : ℤ) - (j : ℤ)) ≤ 2 ^ (-2 : ℤ) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      norm_num at h3
      nlinarith

private theorem tendsto_fourSum {ξ : ℝ} (hξ : ξ ≠ 0) :
    Tendsto (fun N => fourSum N ξ) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ((Int.log 2 |ξ|).natAbs + 1)] with N hN
  exact (fourSum_eq_one hξ (by omega) (by omega)).symm

private theorem norm_fourSum_le {c : ℝ} (hφ : IsBump (evenBump lpPhi) c)
    (hψ : IsBump (evenBump lpPsi) c) (N : ℕ) (ξ : ℝ) : ‖fourSum N ξ‖ ≤ 4 * c := by
  have hu : ∀ _ : Fin (2 * N), ‖(1 : ℂ)‖ ≤ 1 := fun _ => norm_one.le
  have h1 := norm_bumpSum_le hφ (-(2 * (N : ℤ))) hu ξ
  have h2 := norm_bumpSum_le hφ (-(2 * (N : ℤ)) + 1) hu ξ
  have h3 := norm_bumpSum_le hψ (-(2 * (N : ℤ))) hu ξ
  have h4 := norm_bumpSum_le hψ (-(2 * (N : ℤ)) + 1) hu ξ
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_)
  linarith

private theorem continuous_fourSum {c : ℝ} (hφ : IsBump (evenBump lpPhi) c)
    (hψ : IsBump (evenBump lpPsi) c) (N : ℕ) : Continuous (fourSum N) :=
  ((contDiff_bumpSum hφ _ _).continuous.add (contDiff_bumpSum hφ _ _).continuous).add
    ((contDiff_bumpSum hψ _ _).continuous.add (contDiff_bumpSum hψ _ _).continuous)

/-! ### Functions with spectrum in `(0, ∞)` -/

omit [CompleteSpace X] in
/-- `Σ_i T_{m_i} = id` (p. 755), in the limit of the finite sums. -/
private theorem tendsto_fourierInv_fourSum {c : ℝ} (hφ : IsBump (evenBump lpPhi) c)
    (hψ : IsBump (evenBump lpPsi) c) {H : ℝ → X} (hH : Integrable H) (x : ℝ) :
    Tendsto (fun N => 𝓕⁻ (fun ξ => fourSum N ξ • H ξ) x) atTop (𝓝 (𝓕⁻ H x)) := by
  simpa using tendsto_fourierInv_of_dominated hH (a := fourSum) (b := fun _ => 1) (C := 4 * c)
    (Eventually.of_forall fun N => (continuous_fourSum hφ hψ N).aestronglyMeasurable)
    (Eventually.of_forall fun N => ae_of_all _ (norm_fourSum_le hφ hψ N))
    ((Measure.ae_ne volume 0).mono fun ξ hξ => tendsto_fourSum hξ) x

omit [CompleteSpace X] in
/-- (3.17), p. 755, for the finite sums: `‖Σ_i T_{m_i} h‖_p ≤ Σ_i ‖T_{m_i} h‖_p`. -/
private theorem eLpNorm_fourSum_le {p : ℝ} (hp : 1 ≤ p) {c : ℝ} (hφ : IsBump (evenBump lpPhi) c)
    (hψ : IsBump (evenBump lpPsi) c) {H : ℝ → X} (hH : Integrable H) (N : ℕ) {D : ℝ≥0∞}
    (h : ∀ g, g = evenBump lpPhi ∨ g = evenBump lpPsi → ∀ a K,
      eLpNorm (𝓕⁻ fun ξ => bumpSum g a (fun _ : Fin K => 1) ξ • H ξ) (ENNReal.ofReal p) volume ≤
        D) :
    eLpNorm (𝓕⁻ fun ξ => fourSum N ξ • H ξ) (ENNReal.ofReal p) volume ≤ 4 * D := by
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hi : ∀ g, g = evenBump lpPhi ∨ g = evenBump lpPsi → ∀ a K,
      Integrable fun ξ => bumpSum g a (fun _ : Fin K => 1) ξ • H ξ := by
    intro g hg a K
    have hg' : IsBump g c := by rcases hg with rfl | rfl <;> assumption
    exact integrable_bdd_smul (contDiff_bumpSum hg' _ _).continuous.aestronglyMeasurable
      (norm_bumpSum_le hg' a fun _ => norm_one.le) hH
  have hadd : ∀ {G₁ G₂ : ℝ → X}, Integrable G₁ → Integrable G₂ → ∀ {D₁ D₂ : ℝ≥0∞},
      eLpNorm (𝓕⁻ G₁) (ENNReal.ofReal p) volume ≤ D₁ →
      eLpNorm (𝓕⁻ G₂) (ENNReal.ofReal p) volume ≤ D₂ →
      eLpNorm (𝓕⁻ fun ξ => G₁ ξ + G₂ ξ) (ENNReal.ofReal p) volume ≤ D₁ + D₂ := by
    intro G₁ G₂ h₁ h₂ D₁ D₂ hD₁ hD₂
    have h12 : (𝓕⁻ fun ξ => G₁ ξ + G₂ ξ) = 𝓕⁻ G₁ + 𝓕⁻ G₂ := funext fun x => fourierInv_add' h₁ h₂ x
    rw [h12]
    exact (eLpNorm_add_le hp1).trans (add_le_add hD₁ hD₂)
  have hφ' := h _ (Or.inl rfl)
  have hψ' := h _ (Or.inr rfl)
  have iφ := hi _ (Or.inl rfl)
  have iψ := hi _ (Or.inr rfl)
  simp only [fourSum, add_smul]
  refine (hadd ((iφ _ _).add (iφ _ _)) ((iψ _ _).add (iψ _ _)) (hadd (iφ _ _) (iφ _ _) (hφ' _ _)
    (hφ' _ _)) (hadd (iψ _ _) (iψ _ _) (hψ' _ _) (hψ' _ _))).trans_eq ?_
  ring

/-- The right-hand inequality of (1.13) for the functions with spectrum in `(0, ∞)`: (3.17) with
`T_m f`, and (3.18). -/
private theorem eLpNorm_fourierInv_dyadicSign_pos_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {c : ℝ} (hφ : IsBump (evenBump lpPhi) c)
    (hψ : IsBump (evenBump lpPsi) c) (hρ : IsBump (evenBump lpRho) c) {ε : ℤ → ℝ}
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) {G : ℝ → X} (hG : Integrable G) (hG0 : ∀ ξ ≤ 0, G ξ = 0)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume)
    (hfin : β ≠ ⊤ ∨ eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume = 0) :
    eLpNorm (𝓕⁻ fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      16 * (ENNReal.ofReal c * (1088 * β ^ 2)) ^ 3 * β ^ 2 * hilbertBound β *
        eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hH := integrable_dyadicSign_smul hε hG
  have hsφ : ∀ ξ, evenBump lpPhi ξ ≠ 0 → 3 / 4 ≤ |ξ| ∧ |ξ| < 2 := fun ξ hξ => by
    have h := lpPhi_ne_zero (x := |ξ|) (by simpa [evenBump] using hξ)
    constructor <;> linarith
  have hsψ : ∀ ξ, evenBump lpPsi ξ ≠ 0 → 3 / 4 ≤ |ξ| ∧ |ξ| < 2 := fun ξ hξ => by
    have h := lpPsi_ne_zero (x := |ξ|) (by simpa [evenBump] using hξ)
    constructor <;> linarith
  have hN : ∀ N, eLpNorm (𝓕⁻ fun ξ => fourSum N ξ • ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ)
      (ENNReal.ofReal p) volume ≤
      4 * (4 * (ENNReal.ofReal c * (1088 * β ^ 2)) ^ 3 * β ^ 2 * hilbertBound β *
        eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) := fun N =>
    eLpNorm_fourSum_le hp.le hφ hψ hH N fun g hg a K => by
      rcases hg with rfl | rfl
      · exact eLpNorm_bumpSum_dyadicSign_le hp hβ hρ hφ hsφ a K hε hG hG0 hf hfin
      · exact eLpNorm_bumpSum_dyadicSign_le hp hβ hρ hψ hsψ a K hε hG hG0 hf hfin
  -- Fatou's lemma
  refine (Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hN)
    (fun N => (continuous_fourierInv_of_integrable (integrable_bdd_smul
      (continuous_fourSum hφ hψ N).aestronglyMeasurable (norm_fourSum_le hφ hψ N)
        hH)).aestronglyMeasurable)
    (continuous_fourierInv_of_integrable hH).aestronglyMeasurable
    (ae_of_all _ fun x => tendsto_fourierInv_fourSum hφ hψ hH x)).trans_eq ?_
  ring

/-! ### Reduction to the positive half-line -/

omit [CompleteSpace X] in
/-- `1_{(0,∞)} = (1 + sign) / 2` almost everywhere. -/
private theorem fourierInv_indicator_Ioi {G : ℝ → X} (hG : Integrable G) :
    𝓕⁻ ((Set.Ioi (0 : ℝ)).indicator G) =
      (1 / 2 : ℂ) • (𝓕⁻ G + 𝓕⁻ fun ξ => (Real.sign ξ : ℂ) • G ξ) := by
  funext x
  rw [Pi.smul_apply, Pi.add_apply, ← fourierInv_add' hG (integrable_sign_smul hG),
    ← fourierInv_const_smul]
  refine Real.fourierInv_congr_ae ?_ x
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ξ hξ
  rcases lt_or_gt_of_ne hξ with h | h
  · rw [Set.indicator_of_notMem (fun h' : ξ ∈ Set.Ioi 0 => h.not_gt h'), Real.sign_of_neg h]
    simp
  · rw [Set.indicator_of_mem (Set.mem_Ioi.2 h), Real.sign_of_pos h, Complex.ofReal_one, one_smul,
      ← two_smul ℂ, smul_smul, one_div_mul_cancel two_ne_zero, one_smul]

omit [NormedSpace ℂ X] [CompleteSpace X] in
/-- Averages of two functions. -/
private theorem half_mul_eLpNorm_add_le {p : ℝ} (hp : 1 ≤ p) {u v : ℝ → X} {D : ℝ≥0∞}
    (hu : eLpNorm u (ENNReal.ofReal p) volume ≤ D) (hv : eLpNorm v (ENNReal.ofReal p) volume ≤ D) :
    2⁻¹ * eLpNorm (u + v) (ENNReal.ofReal p) volume ≤ D := by
  calc _ ≤ (2⁻¹ : ℝ≥0∞) * (D + D) := by
        gcongr
        exact (eLpNorm_add_le (ENNReal.one_le_ofReal.2 hp)).trans (add_le_add hu hv)
    _ = D := by rw [mul_add, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

private theorem one_le_hilbertBound (β : ℝ≥0∞) : 1 ≤ hilbertBound β :=
  le_add_self

/-- The reduction to functions with spectrum in `(0, ∞)` by the Hilbert transform (p. 754):
`‖f_+‖_p ≤ ħ ‖f‖_p`. -/
private theorem eLpNorm_fourierInv_Ioi_le {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ ((Set.Ioi (0 : ℝ)).indicator G)) (ENNReal.ofReal p) volume ≤
      hilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  rw [fourierInv_indicator_Ioi hG, eLpNorm_const_smul, enorm_half (Or.inl rfl)]
  exact half_mul_eLpNorm_add_le hp.le (le_mul_of_one_le_left' (one_le_hilbertBound β))
    (eLpNorm_fourierInv_sign_le hp hβ hG hf)

/-- The right-hand inequality of (1.13) for `m = Σ_j ε_j 1_{[2^j, 2^{j+1})}`, if `β < ∞` or
`f = 0`. -/
private theorem eLpNorm_fourierInv_dyadicSign_le_aux {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) {c : ℝ} (hφ : IsBump (evenBump lpPhi) c)
    (hψ : IsBump (evenBump lpPsi) c) (hρ : IsBump (evenBump lpRho) c) {ε : ℤ → ℝ}
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume)
    (hfin : β ≠ ⊤ ∨ eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume = 0) :
    eLpNorm (𝓕⁻ fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      16 * (ENNReal.ofReal c * (1088 * β ^ 2)) ^ 3 * β ^ 2 * hilbertBound β ^ 2 *
        eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  set G₁ := (Set.Ioi (0 : ℝ)).indicator G with hG₁
  have h1 := eLpNorm_fourierInv_Ioi_le hp hβ hG hf
  have h2 : (fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) =
      fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G₁ ξ := by
    funext ξ
    by_cases h0 : 0 < ξ
    · rw [hG₁, Set.indicator_of_mem (Set.mem_Ioi.2 h0)]
    · rw [dyadicSign, ite_eq_right h0]
      simp
  have hħ : β ≠ ⊤ → hilbertBound β ≠ ⊤ := fun h => ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top h), ENNReal.one_ne_top⟩
  have h3 := eLpNorm_fourierInv_dyadicSign_pos_le hp hβ hφ hψ hρ hε
    (hG.indicator measurableSet_Ioi) (fun ξ hξ => Set.indicator_of_notMem (by simpa using hξ) G)
    (memLp_of_eLpNorm_le hf hfin hħ h1) (hfin.imp_right fun h0 => by
      rw [h0, mul_zero] at h1
      exact le_antisymm h1 zero_le)
  rw [h2]
  refine h3.trans ?_
  calc _ ≤ 16 * (ENNReal.ofReal c * (1088 * β ^ 2)) ^ 3 * β ^ 2 * hilbertBound β *
        (hilbertBound β * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume) := by gcongr
    _ = _ := by ring

/-! ### The two half-lines -/

/-- The multiplier `m`, with the two half-lines. -/
private noncomputable def fullSign (ε ε' : ℤ → ℝ) (ξ : ℝ) : ℝ :=
  dyadicSign ε ξ + dyadicSign ε' (-ξ)

/-- `m² = 1`. -/
private theorem fullSign_mul_self {ε ε' : ℤ → ℝ} (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hε' : ∀ j, ε' j = 1 ∨ ε' j = -1) {ξ : ℝ} (hξ : ξ ≠ 0) :
    fullSign ε ε' ξ * fullSign ε ε' ξ = 1 := by
  rcases lt_or_gt_of_ne hξ with h | h
  · rw [fullSign, dyadicSign, dyadicSign, ite_eq_right h.not_gt, ite_eq_left (neg_pos.2 h)]
    rcases hε' (Int.log 2 (-ξ)) with h | h <;> simp [h]
  · rw [fullSign, dyadicSign, dyadicSign, ite_eq_left h, ite_eq_right (by linarith)]
    rcases hε (Int.log 2 ξ) with h | h <;> simp [h]

omit [CompleteSpace X] in
private theorem integrable_fullSign_smul {ε ε' : ℤ → ℝ} (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hε' : ∀ j, ε' j = 1 ∨ ε' j = -1) {G : ℝ → X} (hG : Integrable G) :
    Integrable fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ := by
  have h := (integrable_dyadicSign_smul hε' hG.comp_neg).comp_neg
  simp only [neg_neg] at h
  simp only [fullSign, Complex.ofReal_add, add_smul]
  exact (integrable_dyadicSign_smul hε hG).add h

omit [CompleteSpace X] in
/-- The right-hand inequality of (1.13). -/
private theorem eLpNorm_fourierInv_fullSign_le {p : ℝ} (hp : 1 < p) {D : ℝ≥0∞} {ε ε' : ℤ → ℝ}
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (hε' : ∀ j, ε' j = 1 ∨ ε' j = -1)
    (h : ∀ ε : ℤ → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) → ∀ G : ℝ → X, Integrable G →
      MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        D * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume)
    {G : ℝ → X} (hG : Integrable G) (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      2 * D * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  have hi := integrable_dyadicSign_smul hε' hG.comp_neg
  have hi' := hi.comp_neg
  simp only [neg_neg] at hi'
  have h1 : (𝓕⁻ fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ) =
      (𝓕⁻ fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) +
        𝓕⁻ fun ξ => ((dyadicSign ε' (-ξ) : ℝ) : ℂ) • G ξ := by
    funext x
    rw [Pi.add_apply, ← fourierInv_add' (integrable_dyadicSign_smul hε hG) hi']
    simp only [fullSign, Complex.ofReal_add, add_smul]
  have h2 : eLpNorm (𝓕⁻ fun ξ => ((dyadicSign ε' (-ξ) : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
      D * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
    have e1 := eLpNorm_fourierInv_comp_neg hi (ENNReal.ofReal p)
    have e2 := eLpNorm_fourierInv_comp_neg hG (ENNReal.ofReal p)
    simp only [neg_neg] at e1
    rw [e1, ← e2]
    exact h ε' hε' _ hG.comp_neg (e2.trans_lt hf.eLpNorm_lt_top)
  rw [h1, two_mul, add_mul]
  exact (eLpNorm_add_le (ENNReal.one_le_ofReal.2 hp.le)).trans (add_le_add (h ε hε G hG hf) h2)

omit [CompleteSpace X] in
/-- The left-hand inequality of (1.13), from the right-hand one for `T_m f`, as `m² = 1` (p. 755,
where `m² = 1` on `ℝ₊`, after the reduction; here for the two half-lines together). -/
private theorem eLpNorm_le_eLpNorm_fourierInv_fullSign {p : ℝ} {D : ℝ≥0∞} {ε ε' : ℤ → ℝ}
    (hε : ∀ j, ε j = 1 ∨ ε j = -1) (hε' : ∀ j, ε' j = 1 ∨ ε' j = -1)
    (h : ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        D * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume)
    {G : ℝ → X} (hG : Integrable G) (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ≤
      D * eLpNorm (𝓕⁻ fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume := by
  by_cases hm : MemLp (𝓕⁻ fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume
  · have h1 := h _ (integrable_fullSign_smul hε hε' hG) hm
    have h2 : (𝓕⁻ fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ) =
        𝓕⁻ G := by
      refine funext (Real.fourierInv_congr_ae ?_)
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ξ hξ
      rw [smul_smul, ← Complex.ofReal_mul, fullSign_mul_self hε hε' hξ, Complex.ofReal_one,
        one_smul]
    rwa [h2] at h1
  · -- if `T_m f` is not in `L^p`, then `D ≠ 0`
    have htop : eLpNorm (𝓕⁻ fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume =
        ⊤ := by simpa [memLp_iff] using hm
    have hD : D ≠ 0 := by
      rintro rfl
      have h1 := h G hG hf
      rw [htop, zero_mul] at h1
      exact absurd h1 (by simp)
    rw [htop, ENNReal.mul_top hD]
    exact le_top

end Multipliers

/-! ### The theorem -/

/-- The right-hand inequality of (1.13) for `m = Σ_j ε_j 1_{[2^j, 2^{j+1})}`. For `β = ∞` the
right-hand side is `∞`, unless `f = 0`. -/
private theorem exists_eLpNorm_fourierInv_dyadicSign_le_aux : ∃ C : NNReal, ∀ (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p → ∀ β : ℝ≥0∞,
    IsUMDBound X p β → ∀ ε : ℤ → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) →
    ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * hilbertBound β ^ 2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  obtain ⟨c, hφ, hψ, hρ⟩ := exists_isBump_all
  refine ⟨16 * (c.toNNReal * 1088) ^ 3 + 1, fun X _ _ _ p hp β hβ ε hε G hG hf => ?_⟩
  have hħ : hilbertBound β ^ 2 ≠ 0 :=
    pow_ne_zero 2 (zero_lt_one.trans_le (one_le_hilbertBound β)).ne'
  by_cases hfin : β ≠ ⊤ ∨ eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume = 0
  · refine (eLpNorm_fourierInv_dyadicSign_le_aux hp hβ hφ hψ hρ hε hG hf hfin).trans ?_
    have h : 16 * (ENNReal.ofReal c * (1088 * β ^ 2)) ^ 3 * β ^ 2 =
        16 * (ENNReal.ofReal c * 1088) ^ 3 * β ^ 8 := by ring
    rw [h]
    gcongr
    push_cast
    exact le_self_add
  · push Not at hfin
    rw [hfin.1, ENNReal.top_pow (by norm_num), ENNReal.mul_top (by simp), ENNReal.top_mul
      (hfin.1 ▸ hħ), ENNReal.top_mul hfin.2]
    exact le_top

/-- **Littlewood–Paley inequalities on UMD spaces**, McConnell (1984), Theorem 1.3 (`n = 1`, UMD
implies (1.13)), for every choice of the signs `ε_j`, `ε'_j`: both inequalities of (1.13) for the
functions `f = 𝓕⁻ G ∈ L^p` with `G ∈ L¹`. -/
theorem exists_eLpNorm_fourierInv_dyadicSign_le : ∃ C : NNReal, ∀ (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p → ∀ β : ℝ≥0∞, IsUMDBound X p β →
    ∀ ε ε' : ℤ → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) → (∀ j, ε' j = 1 ∨ ε' j = -1) →
    ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => ((dyadicSign ε ξ + dyadicSign ε' (-ξ) : ℝ) : ℂ) • G ξ)
          (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * hilbertBound β ^ 2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ∧
      eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * hilbertBound β ^ 2 *
          eLpNorm (𝓕⁻ fun ξ => ((dyadicSign ε ξ + dyadicSign ε' (-ξ) : ℝ) : ℂ) • G ξ)
            (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierInv_dyadicSign_le_aux
  refine ⟨2 * C, fun X _ _ _ p hp β hβ ε ε' hε hε' G hG hf => ?_⟩
  have hD : ((2 * C : NNReal) : ℝ≥0∞) * β ^ 8 * hilbertBound β ^ 2 =
      2 * (C * β ^ 8 * hilbertBound β ^ 2) := by
    push_cast
    ring
  rw [hD]
  have h : ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => ((fullSign ε ε' ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        2 * (C * β ^ 8 * hilbertBound β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume :=
    fun G hG hf => eLpNorm_fourierInv_fullSign_le hp hε hε' (hC X p hp β hβ) hG hf
  exact ⟨h G hG hf, eLpNorm_le_eLpNorm_fourierInv_fullSign hε hε' h hG hf⟩

/-- The right-hand inequality on the positive half-line, for coefficients `−1`, `0` and `1` (not in
the source): they are averages of two sequences of signs. -/
theorem exists_eLpNorm_fourierInv_dyadicSign_le' : ∃ C : NNReal, ∀ (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p → ∀ β : ℝ≥0∞,
    IsUMDBound X p β → ∀ ε : ℤ → ℝ, (∀ j, ε j = 1 ∨ ε j = 0 ∨ ε j = -1) →
    ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * hilbertBound β ^ 2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierInv_dyadicSign_le_aux
  refine ⟨C, fun X _ _ _ p hp β hβ ε hε G hG hf => ?_⟩
  -- `ε` is the average of two sequences of signs
  set ε₁ : ℤ → ℝ := fun j => if ε j = 0 then 1 else ε j with hε₁
  set ε₂ : ℤ → ℝ := fun j => if ε j = 0 then -1 else ε j with hε₂
  have h₁ : ∀ j, ε₁ j = 1 ∨ ε₁ j = -1 := fun j => by
    rcases hε j with h | h | h <;> simp [hε₁, h]
  have h₂ : ∀ j, ε₂ j = 1 ∨ ε₂ j = -1 := fun j => by
    rcases hε j with h | h | h <;> simp [hε₂, h]
  have h12 : ∀ j, ε j = 2⁻¹ * (ε₁ j + ε₂ j) := fun j => by
    rcases hε j with h | h | h <;> norm_num [hε₁, hε₂, h]
  have hd : ∀ ξ, dyadicSign ε ξ = 2⁻¹ * (dyadicSign ε₁ ξ + dyadicSign ε₂ ξ) := fun ξ => by
    simp only [dyadicSign]
    split_ifs
    · exact h12 _
    · ring
  have heq : (𝓕⁻ fun ξ => ((dyadicSign ε ξ : ℝ) : ℂ) • G ξ) =
      (1 / 2 : ℂ) • ((𝓕⁻ fun ξ => ((dyadicSign ε₁ ξ : ℝ) : ℂ) • G ξ) +
        𝓕⁻ fun ξ => ((dyadicSign ε₂ ξ : ℝ) : ℂ) • G ξ) := by
    funext x
    rw [Pi.smul_apply, Pi.add_apply, ← fourierInv_add' (integrable_dyadicSign_smul h₁ hG)
      (integrable_dyadicSign_smul h₂ hG), ← fourierInv_const_smul]
    simp only [hd, one_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_inv,
      Complex.ofReal_ofNat, ← add_smul, ← mul_smul]
  rw [heq, eLpNorm_const_smul, enorm_half (Or.inl rfl)]
  exact half_mul_eLpNorm_add_le hp.le (hC X p hp β hβ ε₁ h₁ G hG hf) (hC X p hp β hβ ε₂ h₂ G hG hf)

end HarmonicAnalysis
