/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Trigonometric polynomials and Fourier multipliers on the torus

On the torus `𝕋^ι = (ℝ / ℤ)^ι`, with Mathlib's measure (of total mass one) and the monomials
`e_n = UnitAddTorus.mFourier n`, `n ∈ ℤ^ι`:

* `HarmonicAnalysis.trigPoly c = Σ_n c_n e_n`, for finitely supported coefficients `c`;
* `HarmonicAnalysis.torusMultiplier m c = Σ_n m (n) c_n e_n`, the Fourier multiplier with symbol
  `m : ℤ^ι → ℂ` applied to `trigPoly c`;
* `HarmonicAnalysis.torusMultiplierNorm m p`, the norm of this multiplier on the mean-zero
  subspace `L^p_0 (𝕋^ι)`, computed on the dense subspace of mean-zero trigonometric polynomials
  (`c₀ = 0`): `⨆ ‖T_m (trigPoly c)‖_p / ‖trigPoly c‖_p` in `ℝ≥0∞`.

## Main results

* `HarmonicAnalysis.eLpNorm_tsum_le_torusMultiplierNorm` (the `ℓ¹` extension):
  `‖Σ_n m (n) c_n e_n‖_p ≤ ‖T_m‖_{L^p_0} ‖Σ_n c_n e_n‖_p` for every summable `c` with `c₀ = 0`,
  the series converging uniformly when `m c` is summable (otherwise the left side is `0`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HarmonicAnalysis

open UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-- The trigonometric polynomial `x ↦ Σ_n c_n e^{2πi ⟨n, x⟩}` on the torus `𝕋^ι`. -/
def trigPoly (c : (ι → ℤ) →₀ ℂ) (x : UnitAddTorus ι) : ℂ :=
  c.sum fun n a => a * mFourier n x

/-- The Fourier multiplier with symbol `m : ℤ^ι → ℂ` applied to the trigonometric polynomial with
coefficients `c`: `x ↦ Σ_n m (n) c_n e^{2πi ⟨n, x⟩}`. -/
def torusMultiplier (m : (ι → ℤ) → ℂ) (c : (ι → ℤ) →₀ ℂ) (x : UnitAddTorus ι) : ℂ :=
  c.sum fun n a => m n * a * mFourier n x

/-- `‖T_m‖_{L^p_0 (𝕋^ι) → L^p_0 (𝕋^ι)}`: the supremum over the (dense) mean-zero trigonometric
polynomials (`c₀ = 0`). -/
def torusMultiplierNorm (m : (ι → ℤ) → ℂ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ (c : (ι → ℤ) →₀ ℂ) (_ : c 0 = 0),
    eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume /
      eLpNorm (trigPoly c) (ENNReal.ofReal p) volume

/-- The series `Σ_n d_n e_n` converges absolutely in `C(𝕋^ι, ℂ)` for summable `d`. -/
private lemma summable_smul_mFourier {d : (ι → ℤ) → ℂ} (hd : Summable d) :
    Summable fun n => d n • mFourier n :=
  .of_norm <| by simpa [norm_smul, mFourier_norm] using hd.norm

private lemma norm_mFourier_apply (n : ι → ℤ) (x : UnitAddTorus ι) : ‖mFourier n x‖ = 1 := by
  simp [mFourier, fourier_apply, norm_prod, Circle.norm_coe]

/-- The uniform sum of `Σ_n d_n e_n` is the pointwise sum. -/
private lemma tsum_smul_mFourier_apply {d : (ι → ℤ) → ℂ} (hd : Summable d) (x : UnitAddTorus ι) :
    (∑' n, d n • mFourier n) x = ∑' n, d n * mFourier n x := by
  rw [← ContinuousMap.tsum_apply (summable_smul_mFourier hd)]
  rfl

/-- On the torus, of total mass one, the `L^q` norm is at most the sup norm. -/
private lemma eLpNorm_le_norm (w : C(UnitAddTorus ι, ℂ)) (q : ℝ≥0∞) :
    eLpNorm w q volume ≤ ENNReal.ofReal ‖w‖ := by
  refine (eLpNorm_le_of_ae_bound w.continuous.aestronglyMeasurable
    (ae_of_all _ w.norm_coe_le_norm)).trans_eq ?_
  rw [volume_pi, Measure.pi_univ]
  simp [AddCircle.measure_univ]

/-- The coefficients determine the sum: if `Σ_n d_n e_n` converges in `C(𝕋^ι, ℂ)` to a function
vanishing almost everywhere, then `d = 0`. -/
private lemma eq_zero_of_hasSum_mFourier {d : (ι → ℤ) → ℂ} {g : C(UnitAddTorus ι, ℂ)}
    (hg : HasSum (fun n => d n • mFourier n) g) (h0 : ⇑g =ᵐ[volume] 0) : d = 0 := by
  have hg0 : g = 0 := by
    ext x
    exact congrFun ((g.continuous.ae_eq_iff_eq volume continuous_zero).1 h0) x
  subst hg0
  funext k
  -- `⟨e_k, ·⟩` in `L²`, for the measure used by `orthonormal_mFourier`
  let L : C(UnitAddTorus ι, ℂ) →L[ℂ] ℂ := (innerSL ℂ (mFourierLp 2 k)).comp
    (ContinuousMap.toLp 2 (Measure.pi fun _ : ι => AddCircle.haarAddCircle) ℂ)
  have hL : ∀ n, L (d n • mFourier n) = if n = k then d k else 0 := by
    intro n
    rw [map_smul, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    change d n • inner ℂ (mFourierLp 2 k) (mFourierLp 2 n) = _
    rw [orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι)) k n]
    by_cases h : n = k
    · subst h; simp
    · simp [h, Ne.symm h]
  have := hg.mapL L
  simp only [hL, map_zero] at this
  exact (hasSum_ite_eq k (d k)).unique this

private lemma trigPoly_eq_sum (c : (ι → ℤ) →₀ ℂ) :
    trigPoly c = ⇑(∑ n ∈ c.support, c n • mFourier n) := by
  funext x
  simp [trigPoly, Finsupp.sum, ContinuousMap.sum_apply]

/-- The bound defining `torusMultiplierNorm`, for one mean-zero trigonometric polynomial. -/
private lemma eLpNorm_torusMultiplier_le (m : (ι → ℤ) → ℂ) {p : ℝ} (hp : 0 < p)
    (c : (ι → ℤ) →₀ ℂ) (hc0 : c 0 = 0) :
    eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume ≤
      torusMultiplierNorm m p * eLpNorm (trigPoly c) (ENNReal.ofReal p) volume := by
  by_cases hy : eLpNorm (trigPoly c) (ENNReal.ofReal p) volume = 0
  · have hae := (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.2 hp).ne').1 hy
    rw [trigPoly_eq_sum] at hae
    have hc := eq_zero_of_hasSum_mFourier (hasSum_sum_of_ne_finset_zero
      (f := fun n => c n • mFourier n) fun n hn => by simp [Finsupp.notMem_support_iff.1 hn]) hae
    obtain rfl : c = 0 := Finsupp.ext (congrFun hc)
    have : torusMultiplier m (0 : (ι → ℤ) →₀ ℂ) = 0 := funext fun x => by simp [torusMultiplier]
    simp [this]
  have hy' : eLpNorm (trigPoly c) (ENNReal.ofReal p) volume ≠ ⊤ := by
    rw [trigPoly_eq_sum]
    exact (eLpNorm_le_norm _ _).trans_lt ENNReal.ofReal_lt_top |>.ne
  calc eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume
      = eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume /
          eLpNorm (trigPoly c) (ENNReal.ofReal p) volume *
          eLpNorm (trigPoly c) (ENNReal.ofReal p) volume := (ENNReal.div_mul_cancel hy hy').symm
    _ ≤ _ := by
      gcongr
      exact le_iSup₂ (f := fun (c : (ι → ℤ) →₀ ℂ) (_ : c 0 = 0) =>
        eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume /
          eLpNorm (trigPoly c) (ENNReal.ofReal p) volume) c hc0

/-- The `ℓ¹` extension: for `1 ≤ p` and summable coefficients `c` with `c₀ = 0`,
`‖Σ_n m (n) c_n e_n‖_p ≤ ‖T_m‖_{L^p_0} ‖Σ_n c_n e_n‖_p`. -/
theorem eLpNorm_tsum_le_torusMultiplierNorm (m : (ι → ℤ) → ℂ) {p : ℝ} (hp : 1 ≤ p)
    {c : (ι → ℤ) → ℂ} (hc : Summable c) (hc0 : c 0 = 0) :
    eLpNorm (fun x => ∑' n, m n * c n * mFourier n x) (ENNReal.ofReal p) volume ≤
      torusMultiplierNorm m p *
        eLpNorm (fun x => ∑' n, c n * mFourier n x) (ENNReal.ofReal p) volume := by
  classical
  have hq : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  by_cases ha : Summable fun n => m n * c n
  swap
  · -- `‖m n c n e_n x‖ = ‖m n c n‖`: the series diverges at every point
    have : (fun x => ∑' n, m n * c n * mFourier n x) = 0 := by
      funext x
      refine tsum_eq_zero_of_not_summable fun h => ha (summable_norm_iff.1 ?_)
      simpa [norm_mFourier_apply] using summable_norm_iff.2 h
    simp [this]
  have hF : (fun x => ∑' n, m n * c n * mFourier n x) = ⇑(∑' n, (m n * c n) • mFourier n) :=
    funext fun x => (tsum_smul_mFourier_apply ha x).symm
  have hG : (fun x => ∑' n, c n * mFourier n x) = ⇑(∑' n, c n • mFourier n) :=
    funext fun x => (tsum_smul_mFourier_apply hc x).symm
  rw [hF, hG]
  set gA := ∑' n, (m n * c n) • mFourier n
  set gC := ∑' n, c n • mFourier n
  set M := torusMultiplierNorm m p
  set q := ENNReal.ofReal p
  by_cases hG0 : eLpNorm gC q volume = 0
  · have hae : ⇑gC =ᵐ[volume] 0 := (eLpNorm_eq_zero_iff (by positivity)).1 hG0
    have hc' := eq_zero_of_hasSum_mFourier (summable_smul_mFourier hc).hasSum hae
    have : gA = 0 := by simp [gA, hc']
    simp [this]
  -- the bound for the truncations `c_s = c 𝟙_s`, up to the uniform errors
  have key : ∀ s : Finset (ι → ℤ), eLpNorm gA q volume ≤
      ENNReal.ofReal ‖(∑ n ∈ s, (m n * c n) • mFourier n) - gA‖ +
        M * (eLpNorm gC q volume + ENNReal.ofReal ‖(∑ n ∈ s, c n • mFourier n) - gC‖) := by
    intro s
    let cs : (ι → ℤ) →₀ ℂ := Finsupp.onFinset s (fun n => if n ∈ s then c n else 0)
      fun n hn => by by_contra h; simp [h] at hn
    have hP : trigPoly cs = ⇑(∑ n ∈ s, c n • mFourier n) := by
      funext x
      rw [trigPoly, Finsupp.onFinset_sum _ fun n => zero_mul _, ContinuousMap.sum_apply]
      exact Finset.sum_congr rfl fun n hn => by simp [hn]
    have hT : torusMultiplier m cs = ⇑(∑ n ∈ s, (m n * c n) • mFourier n) := by
      funext x
      rw [torusMultiplier, Finsupp.onFinset_sum _ fun n => by simp, ContinuousMap.sum_apply]
      exact Finset.sum_congr rfl fun n hn => by simp [hn]
    have h3 := eLpNorm_torusMultiplier_le m (by linarith) cs (by simp [cs, hc0])
    rw [hP, hT] at h3
    calc eLpNorm gA q volume
        = eLpNorm (⇑(gA - ∑ n ∈ s, (m n * c n) • mFourier n) +
            ⇑(∑ n ∈ s, (m n * c n) • mFourier n)) q volume := by simp
      _ ≤ eLpNorm ⇑(gA - ∑ n ∈ s, (m n * c n) • mFourier n) q volume +
            eLpNorm ⇑(∑ n ∈ s, (m n * c n) • mFourier n) q volume := eLpNorm_add_le hq
      _ ≤ ENNReal.ofReal ‖(∑ n ∈ s, (m n * c n) • mFourier n) - gA‖ +
            M * eLpNorm ⇑(∑ n ∈ s, c n • mFourier n) q volume := by
          gcongr
          rw [norm_sub_rev]
          exact eLpNorm_le_norm _ _
      _ ≤ _ := by
          gcongr
          calc eLpNorm ⇑(∑ n ∈ s, c n • mFourier n) q volume
              = eLpNorm (⇑gC + ⇑((∑ n ∈ s, c n • mFourier n) - gC)) q volume := by simp
            _ ≤ _ := eLpNorm_add_le hq
            _ ≤ _ := by gcongr; exact eLpNorm_le_norm _ _
  -- the truncations converge uniformly
  have h1 := ENNReal.tendsto_ofReal
    (tendsto_iff_norm_sub_tendsto_zero.1 (summable_smul_mFourier ha).hasSum)
  have h2 := ENNReal.tendsto_ofReal
    (tendsto_iff_norm_sub_tendsto_zero.1 (summable_smul_mFourier hc).hasSum)
  rw [ENNReal.ofReal_zero] at h1 h2
  have hlim := h1.add (ENNReal.Tendsto.const_mul
    ((tendsto_const_nhds (x := eLpNorm gC q volume)).add h2) (a := M)
    (Or.inl (by simpa using hG0)))
  simpa using ge_of_tendsto' hlim key

end HarmonicAnalysis
