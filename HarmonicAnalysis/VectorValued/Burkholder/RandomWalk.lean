/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.VectorValued.Burkholder.HarmonicPolynomial
public import BanachProbability.UMD.Decoupling
public import BanachProbability.Martingale.Burkholder.Inequality
public import BanachProbability.SignCube.Bridge

/-!
# A random walk stopped at the exit from the unit disc

D. L. Burkholder, *A geometric condition that implies the existence of certain singular integrals of
Banach-space-valued functions* (1983), pp. 278–282, the first part of the proof of Lemma 2. For
Rademacher functions `r_1, r_2, …` and `0 < δ < 1/2` let `d_k = δ r_{2k−1}`, `e_k = δ r_{2k}`,
`Z_n = X_n + i Y_n = Σ_{k=1}^n (d_k + i e_k)` (`walk`), `τ = inf {n : |Z_n| ≥ 1}` (`exitTime` is
`τ ∧ n`), and `w_k = ∏_{j=0}^{k−1} χ (Z_j)`, the characteristic function of `{τ ≥ k}`.

* `lpNorm_sqrt_exitTime_le`: (20), `δ ‖(τ ∧ n)^{1/2}‖_p ≤ 2 c_p`. The martingale `f = X_{τ ∧ n}`
  with the differences `w_k d_k` is bounded by `2` and has the square function `δ (τ ∧ n)^{1/2}`.
* `norm_walk_exitTime_le`: (22), `|Z_{τ ∧ n}| ≤ 1 + 2δ`.
* `exists_lpNorm_harmPoly_sub_le`: (27), `‖u (Z_{τ ∧ n}) − U‖_p ≤ C_p γ δ` for a harmonic polynomial
  `u` with coefficients in a Banach space and `U = Σ_{k=1}^n w_k [u_x (Z_{k−1}) d_k + u_y (Z_{k−1})
  e_k]` (`walkMartingale`). By the Taylor estimates the norm of `u (Z_{τ ∧ n}) − U − W`, where
  `W = Σ_{k=1}^n w_k u_{xy} (Z_{k−1}) d_k e_k`, is at most `γ δ³ (τ ∧ n)`, (24), which is estimated
  by (20) with the exponent `2p`, (25); `W` is a combination, (26), of real martingales, estimated
  by the square function inequality and (20).
* `lpNorm_walkMartingale_conj_le`: (29), `‖V‖_p ≤ β² ‖U‖_p` for the sum `V` that belongs to the
  conjugate `v` of `u`, if the space has the `UMD_p` constant `β`. Both norms are compared, by Lemma
  1, with those of the decoupled sums, and these are equal because `v_x = −u_y`, `v_y = u_x`.
* `exists_lpNorm_conjHarmPoly_walk_le`: `‖v (Z_{τ ∧ n})‖_p ≤ β² ‖u (Z_{τ ∧ n})‖_p +
  (β² + 1) C_p γ δ`, from (27), (28), (29).

Differences from the source. The signs are the coordinates of the cube `{−1, 1}^{2n}`, `n` fixed,
and only the stopped times `τ ∧ n` are considered; the limit `n → ∞`, (21) and (23), comes later. In
the source `c_p`, `c_p (B)` change from line to line; here the constant of the square function
inequality, (9) in the source, is `c_p = p* − 1`, `p* = max (p, p / (p − 1))`, and that of (27) is
`2 c_p² + 4 c_{2p}²`. Lemma 1 with the constant `β` is `BanachProbability.decoupling_dyadic`, proved
as in the source: the transforms of a Paley–Walsh martingale by fixed signs, averaged over the
signs. For (29) the source says that the transformations `(−r_1, r_2, −r_3, r_4, …)` and
`(r_2, r_1, r_4, r_3, …)` of the signs have the same distribution; here the average over the signs
is invariant under their composition `(r_2, −r_1, r_4, −r_3, …)` (`swapSigns`). The hypothesis of
the source is (8): the inequality for constant signs, and martingales with any start; `IsUMDBound`
has predictable signs and martingales started at `0`, with the same constant
(`BanachProbability.isUMDBound_iff_isDeterministicUMDBound`).

Correction to the source: on p. 280 the `k`-th term of the martingale difference sequence of `W^j`
is said to be bounded by `k² δ²`; the bound is `N² δ² w_k`, as it is used on p. 281.
-/

@[expose] public section

open MeasureTheory BanachProbability SignCube
open scoped ENNReal

namespace HarmonicAnalysis

/-- The walk `Z_n = Σ_{k=1}^n (d_k + i e_k)`, `d_k = δ r_{2k−1}`, `e_k = δ r_{2k}` (p. 278), for a
sequence of signs `r_1, r_2, …` (here `coin (ω 0), coin (ω 1), …`). -/
noncomputable def walk (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n,
    ((δ * coin (ω (2 * k)) : ℝ) + (δ * coin (ω (2 * k + 1)) : ℝ) * Complex.I)

open scoped Classical in
/-- The stopped time `τ ∧ n`, `τ = inf {n : |Z_n| ≥ 1}` (p. 278), `inf ∅ = ∞`. -/
noncomputable def exitTime (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) : ℕ :=
  Nat.find (p := fun m => m = n ∨ 1 ≤ ‖walk δ ω m‖) ⟨n, Or.inl rfl⟩

/-- The sequence of signs that begins with `ε` (and continues with `−1`). -/
def extendSigns {N : ℕ} (ε : Fin N → Bool) (j : ℕ) : Bool :=
  if h : j < N then ε ⟨j, h⟩ else false

/-! ### The walk and the stopped time -/

/-- `Z_0 = 0`. -/
private theorem walk_zero (δ : ℝ) (ω : ℕ → Bool) : walk δ ω 0 = 0 := by
  simp [walk]

/-- `Z_{n+1} = Z_n + d_{n+1} + i e_{n+1}`. -/
private theorem walk_succ (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    walk δ ω (n + 1) = walk δ ω n +
      ((δ * coin (ω (2 * n)) : ℝ) + (δ * coin (ω (2 * n + 1)) : ℝ) * Complex.I) :=
  Finset.sum_range_succ _ _

/-- `Z_k` is a function of the first `2k` signs. -/
private theorem walk_congr (δ : ℝ) {ω ω' : ℕ → Bool} {k : ℕ} (h : ∀ j < 2 * k, ω j = ω' j) :
    walk δ ω k = walk δ ω' k := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [h (2 * j) (by omega), h (2 * j + 1) (by omega)]

/-- `τ ∧ n ≤ n`. -/
private theorem exitTime_le (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) : exitTime δ ω n ≤ n :=
  Nat.find_min' _ (Or.inl rfl)

/-- `|Z_k| < 1` for `k < τ ∧ n`. -/
private theorem norm_walk_lt_one {δ : ℝ} {ω : ℕ → Bool} {n k : ℕ} (h : k < exitTime δ ω n) :
    ‖walk δ ω k‖ < 1 :=
  not_le.1 fun h1 => Nat.find_min _ h (Or.inr h1)

/-- For `k < n`: `k < τ ∧ n` if and only if `|Z_0|, …, |Z_k| < 1`. -/
private theorem lt_exitTime_iff {δ : ℝ} {ω : ℕ → Bool} {n k : ℕ} (hk : k < n) :
    k < exitTime δ ω n ↔ ∀ j ≤ k, ‖walk δ ω j‖ < 1 := by
  refine ⟨fun h j hj => norm_walk_lt_one (hj.trans_lt h), fun h => ?_⟩
  by_contra hle
  rcases Nat.find_spec (p := fun m => m = n ∨ 1 ≤ ‖walk δ ω m‖) ⟨n, Or.inl rfl⟩ with h1 | h1
  · exact absurd (h1 ▸ not_lt.1 hle) (not_le.2 hk)
  · exact absurd (h _ (not_lt.1 hle)) (not_lt.2 h1)

open scoped Classical in
/-- The factor `w_{k+1} = ∏_{j=0}^k χ (Z_j)` (p. 278), the characteristic function of
`{τ ≥ k + 1}`. -/
private noncomputable def weight (δ : ℝ) (ω : ℕ → Bool) (k : ℕ) : ℝ :=
  if ∀ j ≤ k, ‖walk δ ω j‖ < 1 then 1 else 0

/-- `w_{k+1}` is a function of the first `2k` signs. -/
private theorem weight_congr (δ : ℝ) {ω ω' : ℕ → Bool} {k : ℕ} (h : ∀ j < 2 * k, ω j = ω' j) :
    weight δ ω k = weight δ ω' k := by
  have hw : ∀ j ≤ k, walk δ ω j = walk δ ω' j := fun j hj =>
    walk_congr δ fun i hi => h i (by omega)
  have hiff : (∀ j ≤ k, ‖walk δ ω j‖ < 1) ↔ ∀ j ≤ k, ‖walk δ ω' j‖ < 1 :=
    forall₂_congr fun j hj => by rw [hw j hj]
  simp only [weight, hiff]

/-- For `k < n`, `w_{k+1}` is the characteristic function of `{k < τ ∧ n}`. -/
private theorem weight_eq {δ : ℝ} {ω : ℕ → Bool} {n k : ℕ} (hk : k < n) :
    weight δ ω k = if k < exitTime δ ω n then 1 else 0 := by
  simp only [weight, lt_exitTime_iff hk]

/-- `w_k² = w_k` (p. 279). -/
private theorem weight_sq (δ : ℝ) (ω : ℕ → Bool) (k : ℕ) : weight δ ω k ^ 2 = weight δ ω k := by
  unfold weight
  split_ifs <;> norm_num

/-- `Σ_{k ≤ τ ∧ n} F_k = Σ_{k=1}^n w_k F_k`. -/
private theorem sum_range_exitTime {E : Type*} [AddCommGroup E] [Module ℝ E] (δ : ℝ)
    (ω : ℕ → Bool) (n : ℕ) (F : ℕ → E) :
    ∑ k ∈ Finset.range (exitTime δ ω n), F k = ∑ k ∈ Finset.range n, weight δ ω k • F k := by
  have hsub : Finset.range (exitTime δ ω n) ⊆ Finset.range n :=
    Finset.range_subset_range.2 (exitTime_le δ ω n)
  rw [← Finset.sum_subset hsub (f := fun k => weight δ ω k • F k) fun k hk hk' => ?_]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [weight_eq (Finset.mem_range.1 (hsub hk)), ite_eq_left (Finset.mem_range.1 hk), one_smul]
  · rw [weight_eq (Finset.mem_range.1 hk), ite_eq_right fun h => hk' (Finset.mem_range.2 h),
      zero_smul]

/-- `τ ∧ n = Σ_{k=1}^n w_k` (p. 280). -/
private theorem exitTime_eq_sum (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    (exitTime δ ω n : ℝ) = ∑ k ∈ Finset.range n, weight δ ω k := by
  simpa using sum_range_exitTime δ ω n fun _ => (1 : ℝ)

/-! ### Predictable families for pairs of signs -/

section Pairs

variable {E : Type*}

/-- The sequence of signs that extends `ε` has the values of `ε` at the places `i < N`. -/
private theorem extendSigns_val {N : ℕ} (ε : Fin N → Bool) (i : Fin N) :
    extendSigns ε i = ε i := by
  simp [extendSigns]

/-- The family `A_0, B_0, A_1, B_1, …, A_{n−1}, B_{n−1}` of functions on the cube `{−1, 1}^{2n}`. -/
private def pairFamily (n : ℕ) (A B : ℕ → (ℕ → Bool) → E) (i : Fin (2 * n))
    (ε : Fin (2 * n) → Bool) : E :=
  if i.val % 2 = 0 then A (i / 2) (extendSigns ε) else B (i / 2) (extendSigns ε)

/-- The family is predictable if `A_k` is a function of the first `2k` signs and `B_k` of the first
`2k + 1` signs. -/
private theorem isPredictable_pairFamily (n : ℕ) {A B : ℕ → (ℕ → Bool) → E}
    (hA : ∀ k ω ω', (∀ j < 2 * k, ω j = ω' j) → A k ω = A k ω')
    (hB : ∀ k ω ω', (∀ j < 2 * k + 1, ω j = ω' j) → B k ω = B k ω') :
    IsPredictable (pairFamily n A B) := by
  intro i ε ε' h
  have hext : ∀ j < i.val, extendSigns ε j = extendSigns ε' j := fun j hj => by
    have hj' : j < 2 * n := hj.trans i.isLt
    simpa only [extendSigns, dite_eq_left hj'] using h ⟨j, hj'⟩ hj
  unfold pairFamily
  split_ifs with h2
  · exact hA _ _ _ fun j hj => hext j (by omega)
  · exact hB _ _ _ fun j hj => hext j (by omega)

/-- Sums over the family, two terms at a time. -/
private theorem sum_pairFamily {M : Type*} [AddCommMonoid M] (n : ℕ) (A B : ℕ → (ℕ → Bool) → E)
    (ε : Fin (2 * n) → Bool) (g : ℕ → E → M) :
    ∑ i : Fin (2 * n), g i (pairFamily n A B i ε) = ∑ k ∈ Finset.range n,
      (g (2 * k) (A k (extendSigns ε)) + g (2 * k + 1) (B k (extendSigns ε))) := by
  have hpair : ∀ (m : ℕ) (f : ℕ → M),
      ∑ i ∈ Finset.range (2 * m), f i = ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
    intro m f
    induction m with
    | zero => simp
    | succ m ih =>
      rw [mul_add, mul_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        add_assoc]
  refine (Fin.sum_univ_eq_sum_range (fun i => g i (if i % 2 = 0 then A (i / 2) (extendSigns ε)
    else B (i / 2) (extendSigns ε))) (2 * n)).trans ?_
  rw [hpair]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : ¬(2 * k + 1) % 2 = 0 := by omega
  rw [ite_eq_left h1, ite_eq_right h2, show 2 * k / 2 = k by omega,
    show (2 * k + 1) / 2 = k by omega]

/-- The Paley–Walsh sum of the family, with the signs `ε'` as factors and the family at `ε`. -/
private theorem sum_coin_smul_pairFamily [AddCommGroup E] [Module ℝ E] (n : ℕ)
    (A B : ℕ → (ℕ → Bool) → E) (ε ε' : Fin (2 * n) → Bool) :
    ∑ i : Fin (2 * n), coin (ε' i) • pairFamily n A B i ε = ∑ k ∈ Finset.range n,
      (coin (extendSigns ε' (2 * k)) • A k (extendSigns ε) +
        coin (extendSigns ε' (2 * k + 1)) • B k (extendSigns ε)) := by
  simpa only [extendSigns_val] using
    sum_pairFamily n A B ε fun i x => coin (extendSigns ε' i) • x

end Pairs

/-! ### `L^p` norms on the cube and the square function inequality -/

section Norms

variable {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The `L^p` norm is monotone. -/
private theorem lpNorm_mono {p : ℝ} (hp : 0 < p) {f : (Fin N → Bool) → E} {g : (Fin N → Bool) → F}
    (h : ∀ ε, ‖f ε‖ ≤ ‖g ε‖) :
    SignCube.lpNorm (fun x => ‖x‖) p f ≤ SignCube.lpNorm (fun x => ‖x‖) p g :=
  Real.rpow_le_rpow (avg_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) p)
    (avg_mono fun ε => Real.rpow_le_rpow (norm_nonneg _) (h ε) hp.le) (by positivity)

/-- A function bounded by `c` has `L^p` norm at most `c`. -/
private theorem lpNorm_le_of_norm_le {p : ℝ} (hp : 0 < p) {f : (Fin N → Bool) → E} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ ε, ‖f ε‖ ≤ c) : SignCube.lpNorm (fun x => ‖x‖) p f ≤ c := by
  have hc' : ‖c‖ = c := Real.norm_of_nonneg hc
  refine (lpNorm_mono hp (g := fun _ => c) fun ε => (h ε).trans_eq hc'.symm).trans_eq ?_
  exact (lpNorm_const (nrm := fun x : ℝ => ‖x‖) (norm_nonneg c) hp).trans hc'

/-- The `L^p` norm of a multiple `φ v` of a vector `v`, with a real function `φ`. -/
private theorem lpNorm_smul_const [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p) (φ : (Fin N → Bool) → ℝ)
    (v : E) : SignCube.lpNorm (fun x => ‖x‖) p (fun ε => φ ε • v) =
      SignCube.lpNorm (fun x => ‖x‖) p φ * ‖v‖ := by
  unfold SignCube.lpNorm
  simp only [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg v), mul_comm _ (‖v‖ ^ p),
    avg_const_mul]
  rw [Real.mul_rpow (by positivity) (avg_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) p),
    ← Real.rpow_mul (norm_nonneg v), mul_one_div_cancel hp.ne', Real.rpow_one, mul_comm]

/-- `‖g‖_p = ‖g^{1/2}‖_{2p}²` for `g ≥ 0`. -/
private theorem lpNorm_eq_sq_lpNorm_sqrt {p : ℝ} (hp : 0 < p) {g : (Fin N → Bool) → ℝ}
    (hg : ∀ ε, 0 ≤ g ε) : SignCube.lpNorm (fun x => ‖x‖) p g =
      SignCube.lpNorm (fun x => ‖x‖) (2 * p) (fun ε => √(g ε)) ^ 2 := by
  have h1 : ∀ ε, ‖√(g ε)‖ ^ (2 * p) = ‖g ε‖ ^ p := fun ε => by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (hg ε),
      Real.rpow_mul (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt (hg ε)]
  have h0 : 0 ≤ avg fun ε => ‖g ε‖ ^ p := avg_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) p
  unfold SignCube.lpNorm
  simp only [h1]
  rw [← Real.rpow_two, ← Real.rpow_mul h0]
  congr 1
  field_simp

/-- The triangle inequality. -/
private theorem lpNorm_add_le' [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) (f g : (Fin N → Bool) → E) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε => f ε + g ε) ≤
      SignCube.lpNorm (fun x => ‖x‖) p f + SignCube.lpNorm (fun x => ‖x‖) p g :=
  SignCube.lpNorm_add_le (normSeminorm ℝ E) hp f g

/-- `‖f‖_p ≤ ‖g‖_p + c` if `‖f − g‖_p ≤ c`. -/
private theorem lpNorm_le_add_of_sub_le [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p)
    (f g : (Fin N → Bool) → E) {c : ℝ}
    (h : SignCube.lpNorm (fun x => ‖x‖) p (fun ε => f ε - g ε) ≤ c) :
    SignCube.lpNorm (fun x => ‖x‖) p f ≤ SignCube.lpNorm (fun x => ‖x‖) p g + c := by
  have h1 := lpNorm_add_le' hp g fun ε => f ε - g ε
  simp only [add_sub_cancel] at h1
  linarith

/-- `‖g‖_p ≤ ‖f‖_p + c` if `‖f − g‖_p ≤ c`. -/
private theorem lpNorm_le_add_of_sub_le' [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p)
    (f g : (Fin N → Bool) → E) {c : ℝ}
    (h : SignCube.lpNorm (fun x => ‖x‖) p (fun ε => f ε - g ε) ≤ c) :
    SignCube.lpNorm (fun x => ‖x‖) p g ≤ SignCube.lpNorm (fun x => ‖x‖) p f + c :=
  lpNorm_le_add_of_sub_le hp g f <| (lpNorm_mono (one_pos.trans_le hp) fun ε =>
    (norm_sub_rev (g ε) (f ε)).le).trans h

/-- The triangle inequality for finite sums. -/
private theorem lpNorm_sum_le [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (f : ι → (Fin N → Bool) → E) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε => ∑ i ∈ s, f i ε) ≤
      ∑ i ∈ s, SignCube.lpNorm (fun x => ‖x‖) p (f i) := by
  have h := Finset.le_sum_of_subadditive (lpSeminorm (N := N) (normSeminorm ℝ E) p hp)
    (map_zero _).le (map_add_le_add _) s f
  have he : (fun ε => ∑ i ∈ s, f i ε) = ∑ i ∈ s, f i := by
    funext ε
    rw [Finset.sum_apply]
  rw [he]
  exact h

/-- The constant `c_p = p* − 1` of the square function inequality is nonnegative. -/
private theorem sqConst_nonneg {p : ℝ} (hp : 1 < p) : 0 ≤ max p (p / (p - 1)) - 1 := by
  linarith [le_max_left p (p / (p - 1))]

/-- The square function inequality, (9) in the source, for a real Paley–Walsh martingale on the
cube, with the constant `c_p = p* − 1`. -/
private theorem squareFunction_cube {p : ℝ} (hp : 1 < p) {ξ : Fin N → (Fin N → Bool) → ℝ}
    (hξ : IsPredictable ξ) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε => √(∑ i, ξ i ε ^ 2)) ≤ (max p (p / (p - 1)) - 1) *
        SignCube.lpNorm (fun x => ‖x‖) p (fun ε => ∑ i, coin (ε i) • ξ i ε) ∧
      SignCube.lpNorm (fun x => ‖x‖) p (fun ε => ∑ i, coin (ε i) • ξ i ε) ≤
        (max p (p / (p - 1)) - 1) *
          SignCube.lpNorm (fun x => ‖x‖) p (fun ε => √(∑ i, ξ i ε ^ 2)) := by
  have hp0 : 0 < p := one_pos.trans hp
  have hc := sqConst_nonneg hp
  have h0 : ∀ f : (Fin N → Bool) → ℝ, 0 ≤ SignCube.lpNorm (fun x => ‖x‖) p f := fun f =>
    lpNorm_nonneg (fun x => norm_nonneg x) p f
  have hsum : (fun ε => ∑ i, coin (ε i) • ξ i ε) = paleyWalsh ξ N :=
    funext fun ε => (paleyWalsh_of_le ξ le_rfl ε).symm
  have hsq : ∀ ε, ∑ k ∈ Finset.range N, ‖paleyWalsh ξ (k + 1) ε - paleyWalsh ξ k ε‖ ^ 2 =
      ∑ i, ξ i ε ^ 2 := fun ε => by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ‖paleyWalsh ξ (k + 1) ε - paleyWalsh ξ k ε‖ ^ 2)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [norm_paleyWalsh_succ_sub, Real.norm_eq_abs, sq_abs]
  have h := Burkholder.squareFunction_of_martingale hp (martingale_paleyWalsh ξ hξ)
    (fun ε => paleyWalsh_zero ξ ε) N
  simp only [hsq, eLpNorm_uniformOn _ hp0, ← ENNReal.ofReal_mul hc] at h
  rw [hsum]
  exact ⟨(ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (h0 _))).1 h.1,
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (h0 _))).1 h.2⟩

end Norms

/-! ### (20) and (22) -/

/-- The martingale `f_n = Σ_{k=1}^n w_k d_k` is the real part of `Z_{τ ∧ n}` (p. 279). -/
private theorem re_walk_exitTime (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    (walk δ ω (exitTime δ ω n)).re =
      ∑ k ∈ Finset.range n, weight δ ω k • (δ * coin (ω (2 * k))) := by
  rw [← sum_range_exitTime, walk, Complex.re_sum]
  simp

/-- `|f_n| = |X_{τ ∧ n}| ≤ 1 + δ ≤ 2` (p. 279). -/
private theorem abs_re_walk_exitTime_le {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (ω : ℕ → Bool)
    (n : ℕ) : |(walk δ ω (exitTime δ ω n)).re| ≤ 2 := by
  rcases h : exitTime δ ω n with _ | k
  · simp [walk_zero]
  · have h1 : ‖walk δ ω k‖ < 1 := norm_walk_lt_one (n := n) (by omega)
    have h2 : |δ * coin (ω (2 * k))| = δ := by
      rw [abs_mul, abs_coin, mul_one, abs_of_pos hδ0]
    have h3 : (walk δ ω (k + 1)).re = (walk δ ω k).re + δ * coin (ω (2 * k)) := by
      rw [walk_succ]
      simp
    rw [h3]
    linarith [abs_add_le (walk δ ω k).re (δ * coin (ω (2 * k))),
      Complex.abs_re_le_norm (walk δ ω k)]

/-- (20), `δ ‖τ^{1/2}‖_p = ‖S (f)‖_p ≤ c_p ‖f‖_p ≤ 2 c_p`, with the constant `c_p = p* − 1` of the
square function inequality, for `τ ∧ n` in place of `τ`, uniformly in `n`. -/
theorem lpNorm_sqrt_exitTime_le {p : ℝ} (hp : 1 < p) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (n : ℕ) :
    δ * SignCube.lpNorm (fun x => ‖x‖) p
        (fun ε : Fin (2 * n) → Bool => √(exitTime δ (extendSigns ε) n)) ≤
      2 * (max p (p / (p - 1)) - 1) := by
  have hp0 : 0 < p := one_pos.trans hp
  -- the martingale differences `w_k d_k`, at the places of the signs of the `d_k`
  set A : ℕ → (ℕ → Bool) → ℝ := fun k ω => weight δ ω k * δ with hA
  have hpred : IsPredictable (pairFamily n A fun _ _ => 0) := isPredictable_pairFamily n
    (fun k ω ω' h => by simp only [hA, weight_congr δ h]) fun _ _ _ _ => rfl
  -- `S (f) = δ (τ ∧ n)^{1/2}`
  have hS : ∀ ε, √(∑ i, pairFamily n A (fun _ _ => 0) i ε ^ 2) =
      √(exitTime δ (extendSigns ε) n) • δ := fun ε => by
    have hsum : ∑ i, pairFamily n A (fun _ _ => 0) i ε ^ 2 =
        exitTime δ (extendSigns ε) n * δ ^ 2 := by
      rw [sum_pairFamily n A _ ε fun _ x => x ^ 2, exitTime_eq_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hA, mul_pow, weight_sq]
      ring
    rw [hsum, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hδ0.le, smul_eq_mul]
  have hf : ∀ ε, ∑ i, coin (ε i) • pairFamily n A (fun _ _ => 0) i ε =
      (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n)).re := fun ε => by
    rw [sum_coin_smul_pairFamily, re_walk_exitTime]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hA, smul_eq_mul]
    ring
  have h := (squareFunction_cube hp hpred).1
  simp only [hS, hf] at h
  rw [lpNorm_smul_const hp0, Real.norm_of_nonneg hδ0.le, mul_comm] at h
  -- `‖f‖_p ≤ ‖f‖_∞ ≤ 2`
  refine h.trans ((mul_le_mul_of_nonneg_left ?_ (sqConst_nonneg hp)).trans_eq (mul_comm _ _))
  exact lpNorm_le_of_norm_le hp0 zero_le_two fun ε => abs_re_walk_exitTime_le hδ0 hδ _ n

/-- (22), `|Z_{τ ∧ n}| ≤ 1 + 2δ < 2`: either `τ ∧ n = 0`, or `|Z_{τ ∧ n − 1}| < 1` and the last step
has length at most `2δ`. -/
theorem norm_walk_exitTime_le {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (ω : ℕ → Bool) (n : ℕ) :
    ‖walk δ ω (exitTime δ ω n)‖ ≤ 1 + 2 * δ := by
  rcases h : exitTime δ ω n with _ | k
  · rw [walk_zero, norm_zero]
    linarith
  · have h1 : ‖walk δ ω k‖ < 1 := norm_walk_lt_one (n := n) (by omega)
    have h2 : ∀ b : Bool, ‖((δ * coin b : ℝ) : ℂ)‖ = δ := fun b => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_coin, mul_one, abs_of_pos hδ0]
    rw [walk_succ]
    refine (norm_add_le _ _).trans (add_le_add h1.le ((norm_add_le _ _).trans_eq ?_))
    rw [norm_mul, Complex.norm_I, mul_one, h2, h2, two_mul]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `U = Σ_{k=1}^n w_k [u_x (Z_{k−1}) d_k + u_y (Z_{k−1}) e_k]` (p. 280); the factor `w_k`, the
characteristic function of `{τ ≥ k}`, is written as the restriction of the sum to `k ≤ τ ∧ n`. -/
noncomputable def walkMartingale (N : ℕ) (a b : ℕ → X) (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) : X :=
  ∑ k ∈ Finset.range (exitTime δ ω n),
    ((δ * coin (ω (2 * k))) • harmDx N a b (walk δ ω k) +
      (δ * coin (ω (2 * k + 1))) • harmDy N a b (walk δ ω k))

/-! ### (24)–(27) -/

/-- `W = Σ_{k=1}^n w_k u_{xy} (Z_{k−1}) d_k e_k` (p. 280). -/
private noncomputable def walkCorrection (N : ℕ) (a b : ℕ → X) (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) : X :=
  ∑ k ∈ Finset.range (exitTime δ ω n),
    (δ * coin (ω (2 * k)) * (δ * coin (ω (2 * k + 1)))) • harmDxy N a b (walk δ ω k)

/-- `|u (Z_{τ ∧ n}) − U − W| ≤ γ δ³ (τ ∧ n)` (p. 280): the sum over `k ≤ τ ∧ n` of the Taylor
estimates for `Z_k = Z_{k−1} + d_k + i e_k`, `|Z_{k−1}| < 1`. -/
private theorem norm_harmPoly_walk_sub_le (N : ℕ) (a b : ℕ → X) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < 1 / 2) (ω : ℕ → Bool) (n : ℕ) :
    ‖harmPoly N a b (walk δ ω (exitTime δ ω n)) - walkMartingale N a b δ ω n -
        walkCorrection N a b δ ω n‖ ≤ harmConst N a b * δ ^ 3 * exitTime δ ω n := by
  have hzero : harmPoly N a b (walk δ ω 0) = 0 := by
    rw [walk_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [zero_pow (Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hk).1)]
    simp
  have hstep : ∀ b : Bool, |δ * coin b| = δ := fun b => by
    rw [abs_mul, abs_coin, mul_one, abs_of_pos hδ0]
  -- `u (Z_{τ ∧ n}) = Σ_{k ≤ τ ∧ n} (u (Z_k) − u (Z_{k−1}))`
  rw [← sub_zero (harmPoly N a b _), ← hzero,
    ← Finset.sum_range_sub fun k => harmPoly N a b (walk δ ω k), walkMartingale, walkCorrection,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (norm_sum_le_of_le _ fun k hk => ?_).trans_eq (b := ∑ k ∈ Finset.range (exitTime δ ω n),
    harmConst N a b * δ ^ 3) (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm])
  have h := norm_harmPoly_sub_le N a b (norm_walk_lt_one (Finset.mem_range.1 hk)).le hδ.le
    (hstep (ω (2 * k))) (hstep (ω (2 * k + 1)))
  rw [walk_succ, ← sub_sub]
  exact h

/-- (25): `δ² ‖τ ∧ n‖_p ≤ 4 c_{2p}²`, which is (20) with `2p` in place of `p`. -/
private theorem lpNorm_exitTime_le {p : ℝ} (hp : 1 < p) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (n : ℕ) :
    δ ^ 2 * SignCube.lpNorm (fun x => ‖x‖) p
        (fun ε : Fin (2 * n) → Bool => (exitTime δ (extendSigns ε) n : ℝ)) ≤
      4 * (max (2 * p) (2 * p / (2 * p - 1)) - 1) ^ 2 := by
  have h := lpNorm_sqrt_exitTime_le (p := 2 * p) (by linarith) hδ0 hδ n
  rw [lpNorm_eq_sq_lpNorm_sqrt (one_pos.trans hp) fun ε => Nat.cast_nonneg _, ← mul_pow]
  refine (pow_le_pow_left₀ (mul_nonneg hδ0.le ?_) h 2).trans_eq (by ring)
  exact lpNorm_nonneg (fun x => norm_nonneg x) _ _

/-- The square function of `W^j` (p. 281): if `|G| ≤ M` in the disc, then
`Σ_{k=1}^n (w_k G (Z_{k−1}) d_k δ)² ≤ (τ ∧ n) (δ² M)²`. -/
private theorem sum_sq_correction_le {δ : ℝ} (ω : ℕ → Bool) (n : ℕ) {G : ℂ → ℝ} {M : ℝ}
    (hG : ∀ z, ‖z‖ < 1 → |G z| ≤ M) :
    ∑ k ∈ Finset.range n, (weight δ ω k * (δ * coin (ω (2 * k)) * δ * G (walk δ ω k))) ^ 2 ≤
      exitTime δ ω n * (δ ^ 2 * M) ^ 2 := by
  have hterm : ∀ k, (weight δ ω k * (δ * coin (ω (2 * k)) * δ * G (walk δ ω k))) ^ 2 =
      weight δ ω k • (δ ^ 2 * G (walk δ ω k)) ^ 2 := fun k => by
    simp only [mul_pow, weight_sq, smul_eq_mul, sq (coin _), coin_mul_self]
    ring
  simp only [hterm]
  rw [← sum_range_exitTime]
  refine (Finset.sum_le_card_nsmul _ _ ((δ ^ 2 * M) ^ 2) fun k hk => ?_).trans_eq ?_
  · rw [← sq_abs, abs_mul, abs_of_nonneg (sq_nonneg δ)]
    have := hG _ (norm_walk_lt_one (Finset.mem_range.1 hk))
    gcongr
  · rw [Finset.card_range, nsmul_eq_mul]

/-- The estimate of `W^j` (p. 280–281), for a real function `G` (in the source `u^j_{xy}`) that is
bounded by `M` (in the source by `N²`) in the disc: `‖Σ_{k=1}^n w_k G (Z_{k−1}) d_k e_k‖_p ≤
c_p M δ² ‖(τ ∧ n)^{1/2}‖_p ≤ 2 c_p² M δ`. The summands are martingale differences: `e_k` is
independent of the other factors. -/
private theorem lpNorm_real_correction_le {p : ℝ} (hp : 1 < p) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < 1 / 2) (n : ℕ) {G : ℂ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hG : ∀ z, ‖z‖ < 1 → |G z| ≤ M) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
      ∑ k ∈ Finset.range (exitTime δ (extendSigns ε) n), δ * coin (extendSigns ε (2 * k)) *
        (δ * coin (extendSigns ε (2 * k + 1))) * G (walk δ (extendSigns ε) k)) ≤
      2 * (max p (p / (p - 1)) - 1) ^ 2 * M * δ := by
  have hp0 : 0 < p := one_pos.trans hp
  have hc := sqConst_nonneg hp
  set B : ℕ → (ℕ → Bool) → ℝ := fun k ω =>
    weight δ ω k * (δ * coin (ω (2 * k)) * δ * G (walk δ ω k)) with hB
  have hpred : IsPredictable (pairFamily n (fun _ _ => 0) B) := by
    refine isPredictable_pairFamily n (fun _ _ _ _ => rfl) fun k ω ω' h => ?_
    have hlt : ∀ j < 2 * k, ω j = ω' j := fun j hj => h j (by omega)
    simp only [hB, weight_congr δ hlt, walk_congr δ hlt, h (2 * k) (by omega)]
  have hf : ∀ ε, ∑ i, coin (ε i) • pairFamily n (fun _ _ => 0) B i ε =
      ∑ k ∈ Finset.range (exitTime δ (extendSigns ε) n), δ * coin (extendSigns ε (2 * k)) *
        (δ * coin (extendSigns ε (2 * k + 1))) * G (walk δ (extendSigns ε) k) := fun ε => by
    rw [sum_coin_smul_pairFamily, sum_range_exitTime]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB, smul_eq_mul]
    ring
  have hS : ∀ ε, ‖√(∑ i, pairFamily n (fun _ _ => 0) B i ε ^ 2)‖ ≤
      ‖√(exitTime δ (extendSigns ε) n) • (δ ^ 2 * M)‖ := fun ε => by
    have hsum : ∑ i, pairFamily n (fun _ _ => 0) B i ε ^ 2 ≤
        exitTime δ (extendSigns ε) n * (δ ^ 2 * M) ^ 2 := by
      rw [sum_pairFamily n _ B ε fun _ x => x ^ 2]
      refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) (sum_sq_correction_le _ n hG)
      rw [zero_pow two_ne_zero, zero_add]
    have hM' : 0 ≤ δ ^ 2 * M := by positivity
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), smul_eq_mul, Real.norm_of_nonneg (by positivity)]
    refine (Real.sqrt_le_sqrt hsum).trans_eq ?_
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM']
  have h := (squareFunction_cube hp hpred).2
  simp only [hf] at h
  have h20 := lpNorm_sqrt_exitTime_le hp hδ0 hδ n
  refine h.trans ((mul_le_mul_of_nonneg_left (lpNorm_mono hp0 hS) hc).trans ?_)
  rw [lpNorm_smul_const hp0, Real.norm_of_nonneg (by positivity)]
  calc _ = (max p (p / (p - 1)) - 1) * (δ * M) * (δ * SignCube.lpNorm (fun x => ‖x‖) p
        fun ε : Fin (2 * n) → Bool => √(exitTime δ (extendSigns ε) n)) := by ring
    _ ≤ (max p (p / (p - 1)) - 1) * (δ * M) * (2 * (max p (p / (p - 1)) - 1)) := by gcongr
    _ = _ := by ring

/-- `|u^j_{xy} (z)| ≤ N²` for `|z| < 1` (p. 280), where `u^j` is the real or the imaginary part of
`z^j`, `1 ≤ j ≤ N`. -/
private theorem norm_second_deriv_le {N j : ℕ} (hj : j ∈ Finset.Icc 1 N) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Complex.I * (j * (j - 1)) * z ^ (j - 2)‖ ≤ N ^ 2 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have h3 : ‖(j : ℂ) - 1‖ ≤ N := by
    rw [← Nat.cast_pred h1, Complex.norm_natCast]
    exact Nat.cast_le.2 ((Nat.sub_le j 1).trans h2)
  have h4 : ‖(j : ℂ)‖ ≤ N := by
    rw [Complex.norm_natCast]
    exact Nat.cast_le.2 h2
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_mul, sq]
  exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg z) hz.le)).trans
    (mul_le_mul h4 h3 (norm_nonneg _) (Nat.cast_nonneg _))

/-- (26): `W = Σ_{j=1}^N (W^{2j−1} a_j + W^{2j} b_j)`, where `W^{2j−1}` and `W^{2j}` are the
analogues of `W` for the functions `Re z^j` and `Im z^j`. -/
private theorem walkCorrection_eq (N : ℕ) (a b : ℕ → X) (δ : ℝ) (ω : ℕ → Bool) (n : ℕ) :
    walkCorrection N a b δ ω n = ∑ j ∈ Finset.Icc 1 N,
      ((∑ k ∈ Finset.range (exitTime δ ω n), δ * coin (ω (2 * k)) * (δ * coin (ω (2 * k + 1))) *
          (Complex.I * (j * (j - 1)) * walk δ ω k ^ (j - 2)).re) • a j +
        (∑ k ∈ Finset.range (exitTime δ ω n), δ * coin (ω (2 * k)) * (δ * coin (ω (2 * k + 1))) *
          (Complex.I * (j * (j - 1)) * walk δ ω k ^ (j - 2)).im) • b j) := by
  simp only [walkCorrection, harmDxy, Finset.smul_sum, smul_add, smul_smul, Finset.sum_smul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_comm

/-- (26) and the estimate of `W` (p. 281): `‖W‖_p ≤ 2 c_p² γ δ`. -/
private theorem lpNorm_walkCorrection_le {p : ℝ} (hp : 1 < p) (N : ℕ) (a b : ℕ → X) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (n : ℕ) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
      walkCorrection N a b δ (extendSigns ε) n) ≤
      2 * (max p (p / (p - 1)) - 1) ^ 2 * harmConst N a b * δ := by
  have hp0 : 0 < p := one_pos.trans hp
  have hN0 : (0 : ℝ) ≤ N ^ 2 := by positivity
  simp only [walkCorrection_eq]
  refine (lpNorm_sum_le hp.le _ _).trans ((Finset.sum_le_sum (g := fun j =>
    2 * (max p (p / (p - 1)) - 1) ^ 2 * N ^ 2 * δ * (‖a j‖ + ‖b j‖)) fun j hj => ?_).trans ?_)
  · refine (lpNorm_add_le' hp.le _ _).trans ?_
    rw [lpNorm_smul_const hp0, lpNorm_smul_const hp0, mul_add]
    gcongr
    · exact lpNorm_real_correction_le hp hδ0 hδ n
        (G := fun z => (Complex.I * (j * (j - 1)) * z ^ (j - 2)).re) hN0 fun z hz =>
          (Complex.abs_re_le_norm _).trans (norm_second_deriv_le hj hz)
    · exact lpNorm_real_correction_le hp hδ0 hδ n
        (G := fun z => (Complex.I * (j * (j - 1)) * z ^ (j - 2)).im) hN0 fun z hz =>
          (Complex.abs_im_le_norm _).trans (norm_second_deriv_le hj hz)
  · -- `N² ≤ N³ 2^N`
    have hN : (N : ℝ) ^ 2 ≤ N ^ 3 * 2 ^ N := by
      rcases N with _ | N
      · simp
      · have h1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by simp
        exact (pow_le_pow_right₀ h1 (by norm_num)).trans
          (le_mul_of_one_le_right (by positivity) (one_le_pow₀ one_le_two))
    have hs : 0 ≤ ∑ j ∈ Finset.Icc 1 N, (‖a j‖ + ‖b j‖) :=
      Finset.sum_nonneg fun j _ => by positivity
    rw [← Finset.mul_sum, harmConst]
    calc _ = 2 * (max p (p / (p - 1)) - 1) ^ 2 * (N ^ 2 * ∑ j ∈ Finset.Icc 1 N,
          (‖a j‖ + ‖b j‖)) * δ := by ring
      _ ≤ _ := by gcongr

/-- (27), with the constant `2 c_p² + 4 c_{2p}²`. -/
private theorem lpNorm_harmPoly_sub_le {p : ℝ} (hp : 1 < p) (N : ℕ) (a b : ℕ → X) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (n : ℕ) :
    SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
      harmPoly N a b (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n)) -
        walkMartingale N a b δ (extendSigns ε) n) ≤
      (2 * (max p (p / (p - 1)) - 1) ^ 2 + 4 * (max (2 * p) (2 * p / (2 * p - 1)) - 1) ^ 2) *
        harmConst N a b * δ := by
  have hp0 : 0 < p := one_pos.trans hp
  have hγ : 0 ≤ harmConst N a b := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
  -- (24)
  have h24 := lpNorm_add_le' hp.le (fun ε : Fin (2 * n) → Bool =>
    harmPoly N a b (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n)) -
      walkMartingale N a b δ (extendSigns ε) n - walkCorrection N a b δ (extendSigns ε) n)
    fun ε => walkCorrection N a b δ (extendSigns ε) n
  simp only [sub_add_cancel] at h24
  have hmono : SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
      harmPoly N a b (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n)) -
        walkMartingale N a b δ (extendSigns ε) n - walkCorrection N a b δ (extendSigns ε) n) ≤
      SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
        (exitTime δ (extendSigns ε) n : ℝ) • (harmConst N a b * δ ^ 3)) := by
    refine lpNorm_mono hp0 fun ε => (norm_harmPoly_walk_sub_le N a b hδ0 hδ _ n).trans ?_
    rw [smul_eq_mul, mul_comm]
    exact le_abs_self _
  rw [lpNorm_smul_const hp0, Real.norm_of_nonneg (by positivity)] at hmono
  have h25 := mul_le_mul_of_nonneg_left (lpNorm_exitTime_le hp hδ0 hδ n)
    (mul_nonneg hγ hδ0.le)
  have hW := lpNorm_walkCorrection_le hp N a b hδ0 hδ n
  refine h24.trans ((add_le_add hmono hW).trans ?_)
  linarith

/-- (27): `‖u (Z_{τ ∧ n}) − U‖_p ≤ C_p γ δ`, with a constant `C_p` that depends only on `p`. -/
theorem exists_lpNorm_harmPoly_sub_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (N : ℕ) (a b : ℕ → X) (δ : ℝ),
      0 < δ → δ < 1 / 2 → ∀ n : ℕ,
        SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
          harmPoly N a b (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n)) -
            walkMartingale N a b δ (extendSigns ε) n) ≤ C * harmConst N a b * δ :=
  ⟨2 * (max p (p / (p - 1)) - 1) ^ 2 + 4 * (max (2 * p) (2 * p / (2 * p - 1)) - 1) ^ 2,
    by positivity, fun _ _ _ N a b _ hδ0 hδ n => lpNorm_harmPoly_sub_le hp N a b hδ0 hδ n⟩

/-! ### (29) -/

/-- The bijection `(r_1, r_2, r_3, r_4, …) ↦ (r_2, −r_1, r_4, −r_3, …)` of the cube, with which the
two transformations of p. 281–282 are compared. -/
private def swapSigns (n : ℕ) : (Fin (2 * n) → Bool) ≃ (Fin (2 * n) → Bool) where
  toFun ε i := if h : i.val % 2 = 0 then ε ⟨i + 1, by omega⟩ else !ε ⟨i - 1, by omega⟩
  invFun ε i := if h : i.val % 2 = 0 then !ε ⟨i + 1, by omega⟩ else ε ⟨i - 1, by omega⟩
  left_inv ε := by
    funext i
    by_cases h : i.val % 2 = 0
    · simp [h, show (i.val + 1) % 2 = 1 by omega]
    · simp [h, show (i.val - 1) % 2 = 0 by omega, show i.val - 1 + 1 = i.val by omega]
  right_inv ε := by
    funext i
    by_cases h : i.val % 2 = 0
    · simp [h, show (i.val + 1) % 2 = 1 by omega]
    · simp [h, show (i.val - 1) % 2 = 0 by omega, show i.val - 1 + 1 = i.val by omega]

/-- The signs at the places `2k` after the bijection. -/
private theorem extendSigns_swapSigns_even {n k : ℕ} (hk : k < n) (ε : Fin (2 * n) → Bool) :
    extendSigns (swapSigns n ε) (2 * k) = extendSigns ε (2 * k + 1) := by
  simp [extendSigns, swapSigns, show 2 * k < 2 * n by omega, show 2 * k + 1 < 2 * n by omega]

/-- The signs at the places `2k + 1` after the bijection. -/
private theorem extendSigns_swapSigns_odd {n k : ℕ} (hk : k < n) (ε : Fin (2 * n) → Bool) :
    extendSigns (swapSigns n ε) (2 * k + 1) = !extendSigns ε (2 * k) := by
  simp [extendSigns, swapSigns, show 2 * k < 2 * n by omega, show 2 * k + 1 < 2 * n by omega,
    show (2 * k + 1) % 2 = 1 by omega]

/-- The predictable family of `U`: `δ w_k u_x (Z_{k−1})` at the place of `r_{2k−1}` and
`δ w_k u_y (Z_{k−1})` at the place of `r_{2k}`. -/
private noncomputable def martingaleFamily (N : ℕ) (a b : ℕ → X) (δ : ℝ) (n : ℕ) :
    Fin (2 * n) → (Fin (2 * n) → Bool) → X :=
  pairFamily n (fun k ω => (δ * weight δ ω k) • harmDx N a b (walk δ ω k))
    fun k ω => (δ * weight δ ω k) • harmDy N a b (walk δ ω k)

/-- The family of `U` is predictable. -/
private theorem isPredictable_martingaleFamily (N : ℕ) (a b : ℕ → X) (δ : ℝ) (n : ℕ) :
    IsPredictable (martingaleFamily N a b δ n) := by
  refine isPredictable_pairFamily n (fun k ω ω' h => ?_) fun k ω ω' h => ?_
  · rw [weight_congr δ h, walk_congr δ h]
  · have hlt : ∀ j < 2 * k, ω j = ω' j := fun j hj => h j (by omega)
    rw [weight_congr δ hlt, walk_congr δ hlt]

/-- `U` is a Paley–Walsh martingale, a sum `Σ_{k=1}^{2n} v_k r_k` as in Lemma 1 (p. 281). -/
private theorem walkMartingale_eq_paleyWalsh (N : ℕ) (a b : ℕ → X) (δ : ℝ) (n : ℕ)
    (ε : Fin (2 * n) → Bool) : walkMartingale N a b δ (extendSigns ε) n =
      paleyWalsh (martingaleFamily N a b δ n) (2 * n) ε := by
  rw [paleyWalsh_of_le _ le_rfl, martingaleFamily, sum_coin_smul_pairFamily, walkMartingale,
    sum_range_exitTime]
  refine Finset.sum_congr rfl fun k _ => ?_
  module

/-- The sums under the inner integrals of p. 281: as `v_x = −u_y` and `v_y = u_x`, the sum for `V`
is the sum for `U` at the signs `(r_2, −r_1, r_4, −r_3, …)`. -/
private theorem paleyWalsh_conj (N : ℕ) (a b : ℕ → X) (δ : ℝ) (n : ℕ) (ε ε' : Fin (2 * n) → Bool) :
    paleyWalsh (fun i _ => martingaleFamily N (-b) a δ n i ε) (2 * n) ε' =
      paleyWalsh (fun i _ => martingaleFamily N a b δ n i ε) (2 * n) (swapSigns n ε') := by
  rw [paleyWalsh_of_le _ le_rfl, paleyWalsh_of_le _ le_rfl]
  simp only [martingaleFamily, sum_coin_smul_pairFamily]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [extendSigns_swapSigns_even (Finset.mem_range.1 hk),
    extendSigns_swapSigns_odd (Finset.mem_range.1 hk), coin_not, harmDx_conj, harmDy_conj]
  module

/-- The two double integrals of p. 281 are equal. -/
private theorem decoupledLpNorm_conj (p : ℝ) (N : ℕ) (a b : ℕ → X) (δ : ℝ) (n : ℕ) :
    decoupledLpNorm p (martingaleFamily N (-b) a δ n) (2 * n) =
      decoupledLpNorm p (martingaleFamily N a b δ n) (2 * n) := by
  unfold decoupledLpNorm
  congr 2
  funext ε
  simp only [paleyWalsh_conj]
  exact avg_comp_equiv (swapSigns n) fun ε' =>
    ‖paleyWalsh (fun i _ => martingaleFamily N a b δ n i ε) (2 * n) ε'‖ ^ p

/-- (29): `‖V‖_p ≤ β² ‖U‖_p`, by two uses of Lemma 1; `V`, the sum `U` for the conjugate `v`, is the
one for the coefficients `−b_k` and `a_k`. -/
theorem lpNorm_walkMartingale_conj_le [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : IsUMDBound X p β) (N : ℕ) (a b : ℕ → X) (δ : ℝ) (n : ℕ) :
    ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
        walkMartingale N (-b) a δ (extendSigns ε) n)) ≤
      β ^ 2 * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
        walkMartingale N a b δ (extendSigns ε) n)) := by
  have hβ' : dyadicUMDConst X p ≤ β := dyadicUMDConst_le_of_isDyadicUMDBound
    (umdd_isDyadicUMDBound_of_isUMDBound (one_pos.trans hp) hβ)
  have hV := (decoupling_dyadic hp _ (isPredictable_martingaleFamily N (-b) a δ n) (2 * n)).2
  have hU := (decoupling_dyadic hp _ (isPredictable_martingaleFamily N a b δ n) (2 * n)).1
  rw [decoupledLpNorm_conj] at hV
  simp only [walkMartingale_eq_paleyWalsh]
  refine hV.trans ((mul_le_mul_right hU _).trans ?_)
  rw [← mul_assoc, ← sq]
  gcongr

/-- `‖v (Z_{τ ∧ n})‖_p ≤ β² ‖u (Z_{τ ∧ n})‖_p + (β² + 1) C_p γ δ` (p. 282), by (27)–(29). -/
theorem exists_lpNorm_conjHarmPoly_walk_le {p : ℝ} (hp : 1 < p) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (β : ℝ≥0∞),
      IsUMDBound X p β → ∀ (N : ℕ) (a b : ℕ → X) (δ : ℝ), 0 < δ → δ < 1 / 2 → ∀ n : ℕ,
        ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
          conjHarmPoly N a b (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n)))) ≤
        β ^ 2 * ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
          harmPoly N a b (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n)))) +
        (β ^ 2 + 1) * ENNReal.ofReal (C * harmConst N a b * δ) := by
  obtain ⟨C, hC, h27⟩ := exists_lpNorm_harmPoly_sub_le hp
  refine ⟨C, hC, fun X _ _ _ β hβ N a b δ hδ0 hδ n => ?_⟩
  simp only [conjHarmPoly_eq]
  -- (28) is (27) for the coefficients `−b_k` and `a_k`
  have h28 := h27 X N (-b) a δ hδ0 hδ n
  rw [harmConst_conj] at h28
  have hv := (lpNorm_le_add_of_sub_le hp.le _ _ h28).trans_eq (add_comm _ _)
  have hu := lpNorm_le_add_of_sub_le' hp.le _ _ (h27 X N a b δ hδ0 hδ n)
  have h29 := lpNorm_walkMartingale_conj_le hp hβ N a b δ n
  calc _ ≤ _ := (ENNReal.ofReal_le_ofReal hv).trans ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (C * harmConst N a b * δ) + β ^ 2 *
        (ENNReal.ofReal (SignCube.lpNorm (fun x => ‖x‖) p (fun ε : Fin (2 * n) → Bool =>
          harmPoly N a b (walk δ (extendSigns ε) (exitTime δ (extendSigns ε) n)))) +
          ENNReal.ofReal (C * harmConst N a b * δ)) := by
        refine add_le_add_right (h29.trans ?_) _
        gcongr
        exact (ENNReal.ofReal_le_ofReal hu).trans ENNReal.ofReal_add_le
    _ = _ := by ring

end HarmonicAnalysis
