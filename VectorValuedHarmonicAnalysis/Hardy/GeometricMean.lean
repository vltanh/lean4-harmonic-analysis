module

public import VectorValuedHarmonicAnalysis.Hardy.FunctionalCalculus
import Mathlib.Analysis.Convex.Integral

/-!
# The geometric mean of a positive matrix-valued function

For a function `W` on the circle with integrable entries, positive definite almost everywhere, such
that `log det W` is integrable,

`exp ((1/n) ∫ log det W) = inf_Ψ ∫ (1/n) tr (e^Ψ W)`,

where `Ψ` ranges over the Hermitian trigonometric polynomials with `∫ tr Ψ = 0` (H. Helson and D.
Lowdenslager, *Prediction theory and Fourier series in several variables*, Acta Math. 99 (1958),
165–202, Lemma 5; Lemma 4 is the same equality for all Hermitian functions `Ψ` with summable trace).
In the source `W` is positive semidefinite and the left side is zero if `∫ log det W = −∞`; this
case is treated in `posDef_of_szegoInf_pos` (Szego.lean). The trace of the source is normalized,
`tr 1 = 1`, so that `tr log W = (1/n) log det W`.

* `exp_integral_log_det_le`: the inequality of the arithmetic and geometric means, (58).
* `exp_integral_log_det_le_integral_exp`: (59).
* `exists_integral_exp_trigPoly_le`: Lemma 5.

The proof of Lemma 5 is that of Lemma 2, the scalar case, carried through for functions of the
matrices `W (t)`: the positive and negative parts of `log W` are truncated, which gives bounded
functions `Ψ` with `∫ tr Ψ = 0` and `∫ (1/n) tr (e^Ψ W)` close to `exp ((1/n) ∫ log det W)`, and
these are replaced by their Fejér means.
-/

@[expose] public section

open MeasureTheory AddCircle Filter
open scoped ENNReal Matrix ComplexOrder Topology

namespace VectorValuedHarmonicAnalysis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The inequality of the arithmetic and geometric means -/

/-- "The trace of a Hermitian matrix is the average of its proper values; and the determinant is the
product of the same numbers" (Helson–Lowdenslager (1958), p. 189). -/
private theorem log_det_re_eq_sum {W : Matrix n n ℂ} (hW : W.PosDef) :
    Real.log W.det.re = ∑ i, Real.log (hW.isHermitian.eigenvalues i) := by
  have h : W.det = ((∏ i, hW.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    rw [hW.isHermitian.det_eq_prod_eigenvalues, Complex.ofReal_prod]
    rfl
  rw [h, Complex.ofReal_re, Real.log_prod fun i _ => (hW.eigenvalues_pos i).ne']

/-- The inequality of the arithmetic and geometric means for the eigenvalues of a positive definite
matrix of order `n`: `(1/n) log det W ≤ log ((1/n) tr W)`. -/
theorem log_det_div_card_le_log_trace {W : Matrix n n ℂ} (hW : W.PosDef) :
    Real.log W.det.re / Fintype.card n ≤ Real.log (W.trace.re / Fintype.card n) := by
  cases isEmpty_or_nonempty n
  · simp
  have hn : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Finset.univ)
    (w := fun _ => (Fintype.card n : ℝ)⁻¹) (p := hW.isHermitian.eigenvalues)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn])
    (fun i _ => hW.eigenvalues_pos i)
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← log_det_re_eq_sum hW,
    ← trace_re_eq_sum_eigenvalues hW.isHermitian, smul_eq_mul, smul_eq_mul] at h
  rwa [div_eq_inv_mul, div_eq_inv_mul]

/-- The inequality of the arithmetic and geometric means: `|det M|^{2/n} ≤ (1/n) tr (Mᴴ M)` for a
matrix `M` of order `n`. -/
theorem norm_det_rpow_le_trace [Nonempty n] (M : Matrix n n ℂ) :
    ‖M.det‖ ^ (2 / Fintype.card n : ℝ) ≤ (Mᴴ * M).trace.re / Fintype.card n := by
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  by_cases h0 : M.det = 0
  · rw [h0, norm_zero, Real.zero_rpow (by positivity), trace_conjTranspose_mul_self_re]
    positivity
  have hpos : (Mᴴ * M).PosDef :=
    (Matrix.posSemidef_conjTranspose_mul_self M).posDef_iff_det_ne_zero.2 <| by
      rw [Matrix.det_mul, Matrix.det_conjTranspose]
      exact mul_ne_zero (star_ne_zero.2 h0) h0
  have h1 := log_det_div_card_le_log_trace hpos
  rw [det_conjTranspose_mul_self_re, Real.log_pow] at h1
  rw [Real.rpow_def_of_pos (norm_pos_iff.2 h0),
    ← Real.le_log_iff_exp_le (div_pos (Complex.pos_iff.1 hpos.trace_pos).1 hn)]
  refine le_trans (le_of_eq ?_) h1
  push_cast
  ring

/-- `exp ((1/n) log det W) ≤ (1/n) tr W`. -/
private theorem exp_log_det_div_card_le [Nonempty n] {W : Matrix n n ℂ} (hW : W.PosDef) :
    Real.exp (Real.log W.det.re / Fintype.card n) ≤ W.trace.re / Fintype.card n := by
  have hpos : 0 < W.trace.re / Fintype.card n :=
    div_pos (Complex.pos_iff.1 hW.trace_pos).1 (Nat.cast_pos.2 Fintype.card_pos)
  exact (Real.exp_le_exp.2 (log_det_div_card_le_log_trace hW)).trans_eq (Real.exp_log hpos)

/-- Helson–Lowdenslager (1958), (58), without its middle term `∫ (det W)^{1/n}`:
`exp ((1/n) ∫ log det W) ≤ ∫ (1/n) tr W`. -/
theorem exp_integral_log_det_le [Nonempty n] {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef)
    (hlog : Integrable (fun t => Real.log (W t).det.re) haarAddCircle) :
    Real.exp ((∫ t, Real.log (W t).det.re ∂haarAddCircle) / Fintype.card n) ≤
      (∫ t, (W t).trace.re ∂haarAddCircle) / Fintype.card n := by
  have hle : ∀ᵐ t ∂haarAddCircle, Real.exp (Real.log (W t).det.re / Fintype.card n) ≤
      (W t).trace.re / Fintype.card n := hW.mono fun t ht => exp_log_det_div_card_le ht
  have htr := (integrable_trace_re hint).div_const (Fintype.card n : ℝ)
  have hφ := hlog.div_const (Fintype.card n : ℝ)
  have hexp : Integrable (Real.exp ∘ fun t => Real.log (W t).det.re / Fintype.card n)
      haarAddCircle := by
    refine htr.mono (Real.continuous_exp.comp_aestronglyMeasurable hφ.aestronglyMeasurable) ?_
    filter_upwards [hle] with t ht
    rw [Function.comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact ht.trans (le_abs_self _)
  rw [← integral_div, ← integral_div]
  exact (convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hφ hexp).trans (integral_mono_ae hexp htr hle)

/-! ### The conjugate `W' = e^{Ψ/2} W e^{Ψ/2}` -/

/-- `W'` is positive definite. -/
private theorem posDef_exp_half_conj {A W : Matrix n n ℂ} (hA : A.IsHermitian) (hW : W.PosDef) :
    (NormedSpace.exp ((2⁻¹ : ℝ) • A) * W * NormedSpace.exp ((2⁻¹ : ℝ) • A)).PosDef := by
  have h := hW.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit
    (Matrix.isUnit_exp ((2⁻¹ : ℝ) • A)))
  rwa [(isHermitian_exp_half hA).eq] at h

/-- `tr W' = tr (e^Ψ W)`. -/
private theorem trace_exp_half_conj (A W : Matrix n n ℂ) :
    (NormedSpace.exp ((2⁻¹ : ℝ) • A) * W * NormedSpace.exp ((2⁻¹ : ℝ) • A)).trace =
      (NormedSpace.exp A * W).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, exp_half_mul_self]

/-- `log det W' = tr Ψ + log det W`. -/
private theorem log_det_exp_half_conj {A W : Matrix n n ℂ} (hA : A.IsHermitian) (hW : W.PosDef) :
    Real.log (NormedSpace.exp ((2⁻¹ : ℝ) • A) * W *
      NormedSpace.exp ((2⁻¹ : ℝ) • A)).det.re = A.trace.re + Real.log W.det.re := by
  have h : 0 < W.det.re := (Complex.pos_iff.1 hW.det_pos).1
  rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, exp_half_mul_self, Matrix.det_mul,
    det_matrix_exp hA, Complex.re_ofReal_mul, Real.log_mul (Real.exp_pos _).ne' h.ne', Real.log_exp]

/-- Helson–Lowdenslager (1958), (59): `exp ((1/n) ∫ log det W) ≤ ∫ (1/n) tr (e^Ψ W)` for a Hermitian
trigonometric polynomial `Ψ` with `∫ tr Ψ = 0`. -/
theorem exp_integral_log_det_le_integral_exp [Nonempty n] {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef)
    (hlog : Integrable (fun t => Real.log (W t).det.re) haarAddCircle) {c : ℤ →₀ Matrix n n ℂ}
    (hc : ∀ t, (trigPoly c t).IsHermitian) (h0 : (c 0).trace = 0) :
    Real.exp ((∫ t, Real.log (W t).det.re ∂haarAddCircle) / Fintype.card n) ≤
      (∫ t, (NormedSpace.exp (trigPoly c t) * W t).trace.re ∂haarAddCircle) / Fintype.card n := by
  let E (t : UnitAddCircle) : Matrix n n ℂ := NormedSpace.exp ((2⁻¹ : ℝ) • trigPoly c t)
  have hcont := continuous_trigPoly_matrix c
  have hE : Continuous E := continuous_matrix_exp.comp (hcont.const_smul (2⁻¹ : ℝ))
  have hΨ (i j : n) : Integrable (fun t => trigPoly c t i j) haarAddCircle :=
    (memLp_entry_of_continuous hcont i j).integrable one_le_two
  have htr : ∫ t, (trigPoly c t).trace.re ∂haarAddCircle = 0 := by
    rw [integral_trace_re hΨ, matFourierCoeff_trigPoly, h0, Complex.zero_re]
  have hdet : (fun t => Real.log (E t * W t * E t).det.re) =ᵐ[haarAddCircle]
      fun t => (trigPoly c t).trace.re + Real.log (W t).det.re :=
    hW.mono fun t ht => log_det_exp_half_conj (hc t) ht
  have h := exp_integral_log_det_le (W := fun t => E t * W t * E t)
    (integrable_mul_continuous (integrable_continuous_mul hE hint) hE)
    (hW.mono fun t ht => posDef_exp_half_conj (hc t) ht)
    (((integrable_trace_re hΨ).add hlog).congr hdet.symm)
  rw [integral_congr_ae hdet, integral_add (integrable_trace_re hΨ) hlog, htr, zero_add] at h
  simpa only [E, trace_exp_half_conj] using h

/-! ### The truncations of the positive and negative parts of the logarithm -/

/-- The positive part `u = log⁺ s` of `log s`, for `s > 0`, as a continuous function on the line. -/
private noncomputable def logPos (s : ℝ) : ℝ := Real.log (max s 1)

/-- The negative part `v = log⁻ s` of `log s`, for `s > 0`. -/
private noncomputable def logNeg (s : ℝ) : ℝ := logPos s - Real.log s

/-- The truncation `u_N = min (u, N)`. -/
private noncomputable def cutPos (N : ℕ) (s : ℝ) : ℝ := min (logPos s) N

/-- The truncation `v_N = min (v, N)`, for `s > 0`, as a continuous function on the line. -/
private noncomputable def cutNeg (N : ℕ) (s : ℝ) : ℝ := max (-Real.log (max s (Real.exp (-N)))) 0

private theorem continuous_logPos : Continuous logPos :=
  (continuous_id.max continuous_const).log fun _ => (one_pos.trans_le (le_max_right _ _)).ne'

private theorem continuous_cutPos (N : ℕ) : Continuous (cutPos N) :=
  continuous_logPos.min continuous_const

private theorem continuous_cutNeg (N : ℕ) : Continuous (cutNeg N) := by
  refine Continuous.max (Continuous.neg ?_) continuous_const
  exact (continuous_id.max continuous_const).log fun _ =>
    ((Real.exp_pos _).trans_le (le_max_right _ _)).ne'

private theorem logPos_nonneg (s : ℝ) : 0 ≤ logPos s := Real.log_nonneg (le_max_right _ _)

private theorem logPos_eq {s : ℝ} (hs : 0 < s) : logPos s = max (Real.log s) 0 := by
  rw [logPos]
  rcases le_total s 1 with h | h
  · rw [max_eq_right h, Real.log_one, max_eq_right (Real.log_nonpos hs.le h)]
  · rw [max_eq_left h, max_eq_left (Real.log_nonneg h)]

private theorem logNeg_eq {s : ℝ} (hs : 0 < s) : logNeg s = max (-Real.log s) 0 := by
  rw [logNeg, logPos_eq hs]
  rcases le_total (Real.log s) 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h), zero_sub]
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h), sub_self]

private theorem cutNeg_eq {s : ℝ} (hs : 0 < s) (N : ℕ) : cutNeg N s = min (logNeg s) N := by
  have hN : (0 : ℝ) ≤ N := N.cast_nonneg
  rw [cutNeg, logNeg_eq hs]
  rcases le_total s (Real.exp (-N)) with h | h
  · have h1 : Real.log s ≤ -N := (Real.log_le_iff_le_exp hs).2 h
    rw [max_eq_right h, Real.log_exp, neg_neg, max_eq_left hN,
      min_eq_right ((le_neg_of_le_neg h1).trans (le_max_left _ _))]
  · have h1 : -(N : ℝ) ≤ Real.log s := (Real.le_log_iff_exp_le hs).2 h
    rw [max_eq_left h, min_eq_left (max_le (neg_le_of_neg_le h1) hN)]

/-- `0 ≤ u_N ≤ N`. -/
private theorem cutPos_mem (N : ℕ) (s : ℝ) : 0 ≤ cutPos N s ∧ cutPos N s ≤ N :=
  ⟨le_min (logPos_nonneg s) N.cast_nonneg, min_le_right _ _⟩

/-- `0 ≤ v_N ≤ N`. -/
private theorem cutNeg_mem (N : ℕ) (s : ℝ) : 0 ≤ cutNeg N s ∧ cutNeg N s ≤ N := by
  refine ⟨le_max_right _ _, max_le ?_ N.cast_nonneg⟩
  rw [neg_le]
  exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) (le_max_right _ _))

/-- `u_N → u`. -/
private theorem tendsto_cutPos (s : ℝ) : Tendsto (fun N => cutPos N s) atTop (𝓝 (logPos s)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈logPos s⌉₊] with N hN
  exact (min_eq_left (Nat.ceil_le.1 hN)).symm

/-- `v_N → v`. -/
private theorem tendsto_cutNeg {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N => cutNeg N s) atTop (𝓝 (logNeg s)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈logNeg s⌉₊] with N hN
  rw [cutNeg_eq hs, min_eq_left (Nat.ceil_le.1 hN)]

/-- `e^{(u − a u_N) − (v − b v_N)} ≤ max (1, w)`, where `log w = u − v`. -/
private theorem exp_cut_mul_le {s : ℝ} (hs : 0 < s) (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Real.exp (b * cutNeg N s - a * cutPos N s) * s ≤ max 1 s := by
  rw [← Real.exp_log hs, ← Real.exp_add, Real.exp_log hs]
  rcases le_total (Real.log s) 0 with h | h
  · -- `u = 0`
    refine le_max_of_le_left (Real.exp_le_one_iff.2 ?_)
    have h1 : 0 ≤ a * cutPos N s := mul_nonneg ha (cutPos_mem N s).1
    have h2 : b * cutNeg N s ≤ cutNeg N s := mul_le_of_le_one_left (cutNeg_mem N s).1 hb
    have h3 : cutNeg N s ≤ -Real.log s := by
      rw [cutNeg_eq hs, logNeg_eq hs, max_eq_left (neg_nonneg.2 h)]
      exact min_le_left _ _
    linarith
  · -- `v = 0`
    refine le_max_of_le_right ?_
    have h1 : 0 ≤ a * cutPos N s := mul_nonneg ha (cutPos_mem N s).1
    have h2 : cutNeg N s = 0 := by
      rw [cutNeg_eq hs, logNeg_eq hs, max_eq_right (neg_nonpos.2 h), min_eq_left N.cast_nonneg]
    calc Real.exp (b * cutNeg N s - a * cutPos N s + Real.log s) ≤ Real.exp (Real.log s) := by
          rw [Real.exp_le_exp, h2]
          linarith
      _ = s := Real.exp_log hs

/-- `e^{(u − a_N u_N) − (v − b_N v_N)} → 1`. -/
private theorem tendsto_exp_cut_mul {s : ℝ} (hs : 0 < s) {a b : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 1)) (hb : Tendsto b atTop (𝓝 1)) :
    Tendsto (fun N => Real.exp (b N * cutNeg N s - a N * cutPos N s) * s) atTop (𝓝 1) := by
  have h : Tendsto (fun N => b N * cutNeg N s - a N * cutPos N s) atTop
      (𝓝 (1 * logNeg s - 1 * logPos s)) :=
    (hb.mul (tendsto_cutNeg hs)).sub (ha.mul (tendsto_cutPos s))
  have h1 : Real.exp (1 * logNeg s - 1 * logPos s) * s = 1 := by
    rw [logNeg, one_mul, one_mul, sub_sub_cancel_left, Real.exp_neg, Real.exp_log hs,
      inv_mul_cancel₀ hs.ne']
  rw [← h1]
  exact ((Real.continuous_exp.tendsto _).comp h).mul_const s

/-- The constants of the proof of Lemma 2: if the integrals `p_N` of `u_N` and `q_N` of `v_N` have
the same limit, the larger of the two is multiplied by a constant `≤ 1`, which tends to `1`, so that
they agree. -/
private theorem exists_scaling {p q : ℕ → ℝ} {r : ℝ} (hp : ∀ N, 0 ≤ p N ∧ p N ≤ r)
    (hq : ∀ N, 0 ≤ q N ∧ q N ≤ r) (hpr : Tendsto p atTop (𝓝 r)) (hqr : Tendsto q atTop (𝓝 r)) :
    ∃ a b : ℕ → ℝ, (∀ N, 0 ≤ a N ∧ a N ≤ 1) ∧ (∀ N, 0 ≤ b N ∧ b N ≤ 1) ∧
      (∀ N, a N * p N = b N * q N) ∧ Tendsto a atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) := by
  rcases ((hp 0).1.trans (hp 0).2).eq_or_lt with hr | hr
  · refine ⟨fun _ => 1, fun _ => 1, fun _ => ⟨zero_le_one, le_rfl⟩, fun _ => ⟨zero_le_one, le_rfl⟩,
      fun N => ?_, tendsto_const_nhds, tendsto_const_nhds⟩
    rw [le_antisymm ((hp N).2.trans hr.ge) (hp N).1, le_antisymm ((hq N).2.trans hr.ge) (hq N).1]
  · have hmin : Tendsto (fun N => min (p N) (q N)) atTop (𝓝 r) := by
      simpa only [min_self] using hpr.min hqr
    refine ⟨fun N => min (p N) (q N) / p N, fun N => min (p N) (q N) / q N, fun N => ?_,
      fun N => ?_, fun N => ?_, ?_, ?_⟩
    · exact ⟨div_nonneg (le_min (hp N).1 (hq N).1) (hp N).1,
        div_le_one_of_le₀ (min_le_left _ _) (hp N).1⟩
    · exact ⟨div_nonneg (le_min (hp N).1 (hq N).1) (hq N).1,
        div_le_one_of_le₀ (min_le_right _ _) (hq N).1⟩
    · rw [div_mul_cancel_of_imp fun h => ?_, div_mul_cancel_of_imp fun h => ?_]
      · rw [h, min_eq_right (hp N).1]
      · rw [h, min_eq_left (hq N).1]
    · have h := hmin.div hpr hr.ne'
      rwa [div_self hr.ne'] at h
    · have h := hmin.div hqr hr.ne'
      rwa [div_self hr.ne'] at h

/-! ### Integrals of the trace of a function of `W` -/

section TraceFunction

variable {W : UnitAddCircle → Matrix n n ℂ}

private theorem aestronglyMeasurable_trace_cfc
    (hm : ∀ i j, AEStronglyMeasurable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    AEStronglyMeasurable (fun t => (cfc φ (W t)).trace.re) haarAddCircle := by
  refine Complex.continuous_re.comp_aestronglyMeasurable ?_
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    aestronglyMeasurable_cfc hm (hW.mono fun t ht => ht.isHermitian) hφ i i

/-- `|tr φ (W)| ≤ tr B (W)` if `|φ| ≤ B` on `(0, ∞)`. -/
private theorem abs_trace_cfc_le {A : Matrix n n ℂ} (hA : A.PosDef) {φ B : ℝ → ℝ}
    (hle : ∀ s, 0 < s → |φ s| ≤ B s) : |(cfc φ A).trace.re| ≤ (cfc B A).trace.re := by
  rw [trace_cfc_re hA.isHermitian, trace_cfc_re hA.isHermitian]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hle _ (hA.eigenvalues_pos i))

private theorem integrable_trace_cfc
    (hm : ∀ i j, AEStronglyMeasurable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef) {φ B : ℝ → ℝ} (hφ : Continuous φ)
    (hle : ∀ s, 0 < s → |φ s| ≤ B s)
    (hB : Integrable (fun t => (cfc B (W t)).trace.re) haarAddCircle) :
    Integrable (fun t => (cfc φ (W t)).trace.re) haarAddCircle :=
  hB.mono' (aestronglyMeasurable_trace_cfc hm hW hφ) (hW.mono fun _ ht => abs_trace_cfc_le ht hle)

/-- Dominated convergence for the traces of functions of `W`. -/
private theorem tendsto_integral_trace_cfc
    (hm : ∀ i j, AEStronglyMeasurable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef) {φ : ℕ → ℝ → ℝ} {ψ B : ℝ → ℝ}
    (hφ : ∀ N, Continuous (φ N)) (hle : ∀ N s, 0 < s → |φ N s| ≤ B s)
    (hlim : ∀ s, 0 < s → Tendsto (fun N => φ N s) atTop (𝓝 (ψ s)))
    (hB : Integrable (fun t => (cfc B (W t)).trace.re) haarAddCircle) :
    Tendsto (fun N => ∫ t, (cfc (φ N) (W t)).trace.re ∂haarAddCircle) atTop
      (𝓝 (∫ t, (cfc ψ (W t)).trace.re ∂haarAddCircle)) := by
  refine tendsto_integral_of_dominated_convergence (fun t => (cfc B (W t)).trace.re)
    (fun N => aestronglyMeasurable_trace_cfc hm hW (hφ N)) hB
    (fun N => hW.mono fun t ht => abs_trace_cfc_le ht (hle N)) ?_
  filter_upwards [hW] with t ht
  simp only [trace_cfc_re ht.isHermitian]
  exact tendsto_finsetSum _ fun i _ => hlim _ (ht.eigenvalues_pos i)

/-- `1 + tr W` is summable. -/
private theorem integrable_trace_cfc_one_add
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef) :
    Integrable (fun t => (cfc (fun s : ℝ => 1 + s) (W t)).trace.re) haarAddCircle := by
  refine ((integrable_const (Fintype.card n : ℝ)).add (integrable_trace_re hint)).congr ?_
  filter_upwards [hW] with t ht
  rw [trace_cfc_re ht.isHermitian, Finset.sum_add_distrib, ← trace_re_eq_sum_eigenvalues,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rfl

/-- `tr u` is summable: `0 ≤ u ≤ W`. -/
private theorem integrable_trace_cfc_logPos
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef) :
    Integrable (fun t => (cfc logPos (W t)).trace.re) haarAddCircle := by
  refine integrable_trace_cfc (fun i j => (hint i j).aestronglyMeasurable) hW continuous_logPos
    (fun s hs => ?_) (integrable_trace_cfc_one_add hint hW)
  rw [abs_of_nonneg (logPos_nonneg s), logPos_eq hs]
  exact max_le ((Real.log_le_sub_one_of_pos hs).trans (by linarith)) (by linarith)

/-- `tr v = tr u − log det W`. -/
private theorem trace_cfc_logNeg {A : Matrix n n ℂ} (hA : A.PosDef) :
    (cfc logNeg A).trace.re = (cfc logPos A).trace.re - Real.log A.det.re := by
  rw [trace_cfc_re hA.isHermitian, trace_cfc_re hA.isHermitian, log_det_re_eq_sum hA,
    ← Finset.sum_sub_distrib]
  rfl

/-- If `0 ≤ φ ≤ ψ` on `(0, ∞)`, then `0 ≤ ∫ tr φ (W) ≤ ∫ tr ψ (W)`. -/
private theorem integral_trace_cfc_mem
    (hm : ∀ i j, AEStronglyMeasurable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef) {φ ψ : ℝ → ℝ} (hφ : Continuous φ)
    (hle : ∀ s, 0 < s → 0 ≤ φ s ∧ φ s ≤ ψ s)
    (hψ : Integrable (fun t => (cfc ψ (W t)).trace.re) haarAddCircle) :
    0 ≤ ∫ t, (cfc φ (W t)).trace.re ∂haarAddCircle ∧
      ∫ t, (cfc φ (W t)).trace.re ∂haarAddCircle ≤
        ∫ t, (cfc ψ (W t)).trace.re ∂haarAddCircle := by
  have hint : Integrable (fun t => (cfc φ (W t)).trace.re) haarAddCircle :=
    integrable_trace_cfc hm hW hφ (fun s hs => (abs_of_nonneg (hle s hs).1).trans_le (hle s hs).2)
      hψ
  refine ⟨integral_nonneg_of_ae ?_, integral_mono_ae hint hψ ?_⟩
  · filter_upwards [hW] with t ht
    rw [trace_cfc_re ht.isHermitian]
    exact Finset.sum_nonneg fun i _ => (hle _ (ht.eigenvalues_pos i)).1
  · filter_upwards [hW] with t ht
    rw [trace_cfc_re ht.isHermitian, trace_cfc_re ht.isHermitian]
    exact Finset.sum_le_sum fun i _ => (hle _ (ht.eigenvalues_pos i)).2

/-- The proof of Lemma 2, for matrices: `u_N` and `v_N` are multiplied by constants `a_N` and `b_N`
in `[0, 1]`, which tend to `1`, so that `Ψ_N = b_N v_N − a_N u_N` satisfies `∫ tr Ψ_N = 0`.

Departure from the source: there only the `v_m` are multiplied by constants, and "for each `n` there
is an `m` such that `∫ u_n ≤ ∫ v_m`". For the truncations `min (u, n)` and `min (v, m)` this fails
if `u` is bounded and `v` is not: then `∫ u_n = ∫ u = ∫ v > ∫ v_m` for large `n` and all `m`. Here
the one of `u_N` and `v_N` that has the larger integral is multiplied by a constant. -/
private theorem exists_scaled_cut (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef)
    (hlog : Integrable (fun t => Real.log (W t).det.re) haarAddCircle)
    (h0 : ∫ t, Real.log (W t).det.re ∂haarAddCircle = 0) :
    ∃ a b : ℕ → ℝ, (∀ N, 0 ≤ a N ∧ a N ≤ 1) ∧ (∀ N, 0 ≤ b N ∧ b N ≤ 1) ∧
      Tendsto a atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧ ∀ N, ∫ t,
        (cfc (fun s => b N * cutNeg N s - a N * cutPos N s) (W t)).trace.re ∂haarAddCircle = 0 := by
  have hm (i j : n) := (hint i j).aestronglyMeasurable
  have hu := integrable_trace_cfc_logPos hint hW
  have hv0 : (fun t => (cfc logNeg (W t)).trace.re) =ᵐ[haarAddCircle]
      fun t => (cfc logPos (W t)).trace.re - Real.log (W t).det.re :=
    hW.mono fun t ht => trace_cfc_logNeg ht
  have hv : Integrable (fun t => (cfc logNeg (W t)).trace.re) haarAddCircle :=
    (hu.sub hlog).congr hv0.symm
  -- `∫ tr u = ∫ tr v`
  have huv : ∫ t, (cfc logNeg (W t)).trace.re ∂haarAddCircle =
      ∫ t, (cfc logPos (W t)).trace.re ∂haarAddCircle := by
    rw [integral_congr_ae hv0, integral_sub hu hlog, h0, sub_zero]
  have hpu (N : ℕ) (s : ℝ) (_ : 0 < s) : 0 ≤ cutPos N s ∧ cutPos N s ≤ logPos s :=
    ⟨(cutPos_mem N s).1, min_le_left _ _⟩
  have hpv (N : ℕ) (s : ℝ) (hs : 0 < s) : 0 ≤ cutNeg N s ∧ cutNeg N s ≤ logNeg s :=
    ⟨(cutNeg_mem N s).1, (cutNeg_eq hs N).trans_le (min_le_left _ _)⟩
  have habs {φ ψ : ℝ → ℝ} (h : ∀ s, 0 < s → 0 ≤ φ s ∧ φ s ≤ ψ s) (s : ℝ) (hs : 0 < s) :
      |φ s| ≤ ψ s := (abs_of_nonneg (h s hs).1).trans_le (h s hs).2
  obtain ⟨a, b, ha, hb, hab, ha1, hb1⟩ := exists_scaling
    (fun N => integral_trace_cfc_mem hm hW (continuous_cutPos N) (hpu N) hu)
    (fun N => huv ▸ integral_trace_cfc_mem hm hW (continuous_cutNeg N) (hpv N) hv)
    (tendsto_integral_trace_cfc hm hW continuous_cutPos (fun N => habs (hpu N))
      (fun s _ => tendsto_cutPos s) hu)
    (huv ▸ tendsto_integral_trace_cfc hm hW continuous_cutNeg (fun N => habs (hpv N))
      (fun s hs => tendsto_cutNeg hs) hv)
  refine ⟨a, b, ha, hb, ha1, hb1, fun N => ?_⟩
  have hsum : (fun t => (cfc (fun s => b N * cutNeg N s - a N * cutPos N s) (W t)).trace.re)
      =ᵐ[haarAddCircle] fun t => b N * (cfc (cutNeg N) (W t)).trace.re -
        a N * (cfc (cutPos N) (W t)).trace.re := by
    filter_upwards [hW] with t ht
    simp only [trace_cfc_re ht.isHermitian, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [integral_congr_ae hsum, integral_sub
    ((integrable_trace_cfc hm hW (continuous_cutNeg N) (habs (hpv N)) hv).const_mul _)
    ((integrable_trace_cfc hm hW (continuous_cutPos N) (habs (hpu N)) hu).const_mul _),
    integral_const_mul, integral_const_mul, hab, sub_self]

/-- `e^{φ (A)} A = χ (A)` with `χ (s) = e^{φ (s)} s`. -/
private theorem exp_cfc_mul_self {A : Matrix n n ℂ} (hA : A.IsHermitian) {φ : ℝ → ℝ}
    (hφ : Continuous φ) :
    NormedSpace.exp (cfc φ A) * A = cfc (fun s => Real.exp (φ s) * s) A := by
  have hA' : IsSelfAdjoint A := hA.isSelfAdjoint
  have h1 : Continuous fun s => Real.exp (φ s) := Real.continuous_exp.comp hφ
  rw [cfc_mul (fun s => Real.exp (φ s)) (fun s => s) A h1.continuousOn, cfc_id' ℝ A,
    cfc_comp' Real.exp φ A Real.continuous_exp.continuousOn hφ.continuousOn,
    matrix_exp_eq_cfc (cfc_predicate φ A)]

open scoped Matrix.Norms.L2Operator in
/-- The entries of `φ (A)` are bounded by the bound of `φ`. -/
private theorem norm_cfc_apply_le {φ : ℝ → ℝ} {M : ℝ} (hM : ∀ s, |φ s| ≤ M) (A : Matrix n n ℂ)
    (i j : n) : ‖cfc φ A i j‖ ≤ M := by
  have h1 : ‖cfc φ A‖ ≤ M := norm_cfc_le ((abs_nonneg _).trans (hM 0)) fun s _ => hM s
  have h2 := Matrix.l2_opNorm_mulVec (cfc φ A) (EuclideanSpace.single j (1 : ℂ))
  rw [PiLp.norm_single, norm_one, mul_one] at h2
  refine le_trans ?_ (h2.trans h1)
  have h3 := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (cfc φ A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  simpa using h3

end TraceFunction

/-! ### Bounded functions `Ψ` -/

section Bounded

variable {W : UnitAddCircle → Matrix n n ℂ}

/-- `lim ∫ tr (e^{Ψ_N} W) = ∫ tr 1`, by dominated convergence. -/
private theorem tendsto_integral_exp_cut
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef) {a b : ℕ → ℝ} (ha : ∀ N, 0 ≤ a N ∧ a N ≤ 1)
    (hb : ∀ N, 0 ≤ b N ∧ b N ≤ 1) (ha1 : Tendsto a atTop (𝓝 1)) (hb1 : Tendsto b atTop (𝓝 1)) :
    Tendsto (fun N => ∫ t, (NormedSpace.exp
      (cfc (fun s => b N * cutNeg N s - a N * cutPos N s) (W t)) * W t).trace.re ∂haarAddCircle)
      atTop (𝓝 (Fintype.card n)) := by
  have hφ (N : ℕ) : Continuous fun s => b N * cutNeg N s - a N * cutPos N s :=
    ((continuous_cutNeg N).const_mul _).sub ((continuous_cutPos N).const_mul _)
  have h := tendsto_integral_trace_cfc (fun i j => (hint i j).aestronglyMeasurable) hW
    (φ := fun N s => Real.exp (b N * cutNeg N s - a N * cutPos N s) * s) (ψ := fun _ => 1)
    (fun N => (Real.continuous_exp.comp (hφ N)).mul continuous_id) (fun N s hs => ?_)
    (fun s hs => tendsto_exp_cut_mul hs ha1 hb1) (integrable_trace_cfc_one_add hint hW)
  · have h1 : ∫ t, (cfc (fun _ : ℝ => (1 : ℝ)) (W t)).trace.re ∂haarAddCircle =
        Fintype.card n := by
      have h2 : (fun t => (cfc (fun _ : ℝ => (1 : ℝ)) (W t)).trace.re) =ᵐ[haarAddCircle]
          fun _ => (Fintype.card n : ℝ) := by
        filter_upwards [hW] with t ht
        rw [trace_cfc_re ht.isHermitian, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [integral_congr_ae h2, integral_const, probReal_univ, one_smul]
    rw [h1] at h
    refine h.congr fun N => integral_congr_ae ?_
    filter_upwards [hW] with t ht
    rw [exp_cfc_mul_self ht.isHermitian (hφ N)]
  · rw [abs_of_nonneg (by positivity)]
    exact (exp_cut_mul_le hs N (ha N).1 (hb N).2).trans
      (max_le (le_add_of_nonneg_right hs.le) (le_add_of_nonneg_left zero_le_one))

/-- (19), for matrices: if `∫ log det W = 0`, then `inf ∫ (1/n) tr (e^Ψ W) ≤ 1`, where `Ψ` ranges
over the bounded Hermitian functions with `∫ tr Ψ = 0`. -/
private theorem exists_bounded_integral_exp_lt
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef)
    (hlog : Integrable (fun t => Real.log (W t).det.re) haarAddCircle)
    (h0 : ∫ t, Real.log (W t).det.re ∂haarAddCircle = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Ψ : UnitAddCircle → Matrix n n ℂ) (C : ℝ),
      (∀ i j, AEStronglyMeasurable (fun t => Ψ t i j) haarAddCircle) ∧
      (∀ t, (Ψ t).IsHermitian) ∧ (∀ t i j, ‖Ψ t i j‖ ≤ C) ∧
      ∫ t, (Ψ t).trace.re ∂haarAddCircle = 0 ∧
      ∫ t, (NormedSpace.exp (Ψ t) * W t).trace.re ∂haarAddCircle < Fintype.card n + δ := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := exists_scaled_cut hint hW hlog h0
  obtain ⟨N, hN⟩ := ((tendsto_integral_exp_cut hint hW ha hb ha1 hb1).eventually_lt_const
    (lt_add_of_pos_right _ hδ)).exists
  refine ⟨fun t => cfc (fun s => b N * cutNeg N s - a N * cutPos N s) (W t), N, fun i j => ?_,
    fun t => cfc_predicate _ _, fun t => norm_cfc_apply_le (fun s => ?_) _, hab N, hN⟩
  · exact aestronglyMeasurable_cfc (fun i j => (hint i j).aestronglyMeasurable)
      (hW.mono fun t ht => ht.isHermitian)
      (((continuous_cutNeg N).const_mul _).sub ((continuous_cutPos N).const_mul _)) i j
  · have h1 := mul_nonneg (hb N).1 (cutNeg_mem N s).1
    have h2 := mul_nonneg (ha N).1 (cutPos_mem N s).1
    have h3 := (mul_le_of_le_one_left (cutNeg_mem N s).1 (hb N).2).trans (cutNeg_mem N s).2
    have h4 := (mul_le_of_le_one_left (cutPos_mem N s).1 (ha N).2).trans (cutPos_mem N s).2
    exact abs_le.2 ⟨by linarith, by linarith⟩

end Bounded

/-! ### Trigonometric polynomials `Ψ` -/

/-- The matrix exponential is bounded on bounded sets. -/
private theorem exists_norm_exp_apply_le (C : ℝ) : ∃ M : ℝ, ∀ A : Matrix n n ℂ,
    (∀ i j, ‖A i j‖ ≤ C) → ∀ i j, ‖NormedSpace.exp A i j‖ ≤ M := by
  have hK : IsCompact (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 C
  have hcont : Continuous fun (A : n → n → ℂ) (i j : n) =>
      NormedSpace.exp (Matrix.of A) i j := continuous_matrix_exp
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨M, fun A hA i j => ?_⟩
  have h := hM A fun i _ j _ => mem_closedBall_zero_iff.2 (hA i j)
  exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h

omit [DecidableEq n] in
/-- The constant coefficient of a Hermitian function `Ψ` with `∫ tr Ψ = 0` has trace `0`. -/
private theorem trace_matFourierCoeff_zero {Ψ : UnitAddCircle → Matrix n n ℂ}
    (hΨ : ∀ i j, Integrable (fun t => Ψ t i j) haarAddCircle) (hH : ∀ t, (Ψ t).IsHermitian)
    (h0 : ∫ t, (Ψ t).trace.re ∂haarAddCircle = 0) : (matFourierCoeff Ψ 0).trace = 0 := by
  have h1 (t : UnitAddCircle) : (Ψ t).trace = (((Ψ t).trace.re : ℝ) : ℂ) := by
    refine (Complex.conj_eq_iff_re.1 ?_).symm
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, (hH t).eq]
  rw [← integral_trace hΨ, show (fun t => (Ψ t).trace) = _ from funext h1,
    integral_complex_ofReal, h0, Complex.ofReal_zero]

/-- "Every bounded function is boundedly the limit of Fejér means of its Fourier series; each
approximating function is a trigonometric polynomial" which is Hermitian if `Ψ` is, and satisfies
`∫ tr Ψ = 0` if `Ψ` does. -/
private theorem exists_trigPoly_integral_exp_lt {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle) {Ψ : UnitAddCircle → Matrix n n ℂ}
    {C r : ℝ} (hm : ∀ i j, AEStronglyMeasurable (fun t => Ψ t i j) haarAddCircle)
    (hH : ∀ t, (Ψ t).IsHermitian) (hC : ∀ t i j, ‖Ψ t i j‖ ≤ C)
    (h0 : ∫ t, (Ψ t).trace.re ∂haarAddCircle = 0)
    (hr : ∫ t, (NormedSpace.exp (Ψ t) * W t).trace.re ∂haarAddCircle < r) :
    ∃ c : ℤ →₀ Matrix n n ℂ, (∀ t, (trigPoly c t).IsHermitian) ∧ (c 0).trace = 0 ∧
      ∫ t, (NormedSpace.exp (trigPoly c t) * W t).trace.re ∂haarAddCircle < r := by
  have hΨ (i j : n) : Integrable (fun t => Ψ t i j) haarAddCircle :=
    (integrable_const C).mono' (hm i j) (ae_of_all _ fun t => hC t i j)
  obtain ⟨ns, -, hns, hlim⟩ := exists_seq_tendsto_fejerCoeff hΨ
  obtain ⟨M, hM⟩ := exists_norm_exp_apply_le (n := n) C
  have htend := tendsto_integral_trace_mul
    (fun N => continuous_matrix_exp.comp (continuous_trigPoly_matrix (fejerCoeff Ψ (ns N))))
    (fun N t => hM _ fun i j =>
      norm_trigPoly_fejerCoeff_le hΨ (ae_of_all _ fun t => hC t i j) (hns N) t)
    (hlim.mono fun t ht => (continuous_matrix_exp.tendsto _).comp ht) hint
  obtain ⟨N, hN⟩ := (htend.eventually_lt_const hr).exists
  refine ⟨fejerCoeff Ψ (ns N), isHermitian_trigPoly_fejerCoeff hΨ (ae_of_all _ hH) _, ?_, hN⟩
  rw [fejerCoeff_zero Ψ (hns N), trace_matFourierCoeff_zero hΨ hH h0]

/-! ### The normalization `∫ log det W = 0` -/

/-- `log det (κ W) = n log κ + log det W`. -/
private theorem log_det_smul {A : Matrix n n ℂ} (hA : A.PosDef) {κ : ℝ} (hκ : 0 < κ) :
    Real.log ((κ : ℂ) • A).det.re = Fintype.card n * Real.log κ + Real.log A.det.re := by
  have h : 0 < A.det.re := (Complex.pos_iff.1 hA.det_pos).1
  rw [Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.log_mul (pow_pos hκ _).ne' h.ne', Real.log_pow]

/-- Helson–Lowdenslager (1958), Lemma 5, if `log det W` is integrable: with (59),
`exp ((1/n) ∫ log det W)` is the infimum of `∫ (1/n) tr (e^Ψ W)` over the Hermitian trigonometric
polynomials `Ψ` with `∫ tr Ψ = 0`. -/
theorem exists_integral_exp_trigPoly_le {W : UnitAddCircle → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun t => W t i j) haarAddCircle)
    (hW : ∀ᵐ t ∂haarAddCircle, (W t).PosDef)
    (hlog : Integrable (fun t => Real.log (W t).det.re) haarAddCircle) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℤ →₀ Matrix n n ℂ, (∀ t, (trigPoly c t).IsHermitian) ∧ (c 0).trace = 0 ∧
      (∫ t, (NormedSpace.exp (trigPoly c t) * W t).trace.re ∂haarAddCircle) / Fintype.card n ≤
        Real.exp ((∫ t, Real.log (W t).det.re ∂haarAddCircle) / Fintype.card n) + ε := by
  cases isEmpty_or_nonempty n
  · exact ⟨0, fun _ => Subsingleton.elim _ _, by simp, by simpa using by positivity⟩
  have hn : 0 < (Fintype.card n : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ t, Real.log (W t).det.re ∂haarAddCircle := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Real.exp (-(m / Fintype.card n)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := hκ ▸ Real.exp_pos _
  have hκinv : Real.exp (m / Fintype.card n) = κ⁻¹ := by rw [hκ, Real.exp_neg, inv_inv]
  -- `W` is replaced by `κ W`
  have hdet : (fun t => Real.log ((κ : ℂ) • W t).det.re) =ᵐ[haarAddCircle]
      fun t => Fintype.card n * Real.log κ + Real.log (W t).det.re :=
    hW.mono fun t ht => log_det_smul ht hκ0
  have hdet0 : ∫ t, Real.log ((κ : ℂ) • W t).det.re ∂haarAddCircle = 0 := by
    rw [integral_congr_ae hdet, integral_add (integrable_const _) hlog, integral_const,
      probReal_univ, one_smul, ← hm, hκ, Real.log_exp, mul_neg, mul_div_cancel₀ _ hn.ne',
      neg_add_cancel]
  have hint' (i j : n) : Integrable (fun t => ((κ : ℂ) • W t) i j) haarAddCircle :=
    (hint i j).const_mul _
  obtain ⟨Ψ, C, hΨ, hH, hC, h0, hlt⟩ := exists_bounded_integral_exp_lt hint'
    (hW.mono fun t ht => ht.smul (Complex.zero_lt_real.2 hκ0))
    (((integrable_const _).add hlog).congr hdet.symm) hdet0
    (δ := Fintype.card n * (κ * ε)) (by positivity)
  obtain ⟨c, hc, hc0, hlt⟩ := exists_trigPoly_integral_exp_lt hint' hΨ hH hC h0 hlt
  refine ⟨c, hc, hc0, ?_⟩
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul] at hlt
  rw [integral_const_mul] at hlt
  rw [← hm, hκinv, div_le_iff₀ hn, ← mul_le_mul_iff_right₀ hκ0]
  refine hlt.le.trans_eq ?_
  field_simp

end VectorValuedHarmonicAnalysis
