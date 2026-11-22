/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Torus.Cube
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor

/-!
# Lattice Riemann sums of functions continuous off the origin

`HarmonicAnalysis.tendsto_riemannSum`: if `φ : ℂ → ℂ` is continuous at every `ξ ≠ 0` and
`|φ (ξ)| ≤ C (1 + |ξ|)^{−3}`, then the Riemann sums over the lattice `R⁻¹ ℤ²`,
`Σ_{n ∈ ℤ²} R⁻² φ (n / R)`, tend to `∫_ℂ φ` as `R → ∞`. No continuity at `0` is needed: the
cells `R⁻¹ (n + [0, 1)²)` shrink, and the step functions `ξ ↦ φ (⌊R ξ⌋ / R)` converge to `φ` off
`0` under the integrable bound `C' (1 + |ξ|)^{−3}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace HarmonicAnalysis

/-! ### The cells of the lattice `R⁻¹ ℤ²` -/

/-- The index `(⌊R Re ξ⌋, ⌊R Im ξ⌋) ∈ ℤ²` of the cell `R⁻¹ (n + [0, 1)²)` containing `ξ`. -/
private def cellIndex (R : ℕ) (ξ : ℂ) : Fin 2 → ℤ := ![⌊(R : ℝ) * ξ.re⌋, ⌊(R : ℝ) * ξ.im⌋]

private theorem measurable_cellIndex (R : ℕ) : Measurable (cellIndex R) :=
  measurable_pi_iff.mpr <| Fin.forall_fin_two.mpr
    ⟨(measurable_const.mul Complex.measurable_re).floor,
      (measurable_const.mul Complex.measurable_im).floor⟩

private theorem latticePoint_re (n : Fin 2 → ℤ) : (latticePoint n).re = n 0 := by
  simp [latticePoint]

private theorem latticePoint_im (n : Fin 2 → ℤ) : (latticePoint n).im = n 1 := by
  simp [latticePoint]

/-- `|⌊R x⌋ / R − x| ≤ R⁻¹`. -/
private theorem abs_floor_div_sub_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |⌊R * x⌋ / R - x| ≤ R⁻¹ := by
  have h : (⌊R * x⌋ : ℝ) / R - x = -(Int.fract (R * x) / R) := by
    rw [Int.fract]
    field_simp
    ring
  rw [h, abs_neg, abs_of_nonneg (div_nonneg (Int.fract_nonneg _) hR.le), div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr hR.le) (Int.fract_lt_one _).le

/-- The lower left corner `⌊R ξ⌋ / R` of the cell containing `ξ` is within `2 / R` of `ξ`. -/
private theorem norm_latticePoint_cellIndex_div_sub_le {R : ℕ} (hR : R ≠ 0) (ξ : ℂ) :
    ‖latticePoint (cellIndex R ξ) / R - ξ‖ ≤ 2 / R := by
  have hR' : (0 : ℝ) < R := by positivity
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 := abs_floor_div_sub_le hR' ξ.re
  have h2 := abs_floor_div_sub_le hR' ξ.im
  simp only [Complex.sub_re, Complex.sub_im, Complex.div_natCast_re, Complex.div_natCast_im,
    latticePoint_re, latticePoint_im, cellIndex]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (2 : ℝ) / R = (R : ℝ)⁻¹ + (R : ℝ)⁻¹ by ring]
  exact add_le_add h1 h2

/-- The cell `R⁻¹ (n + [0, 1)²)`, in the coordinates `ℂ ≃ ℝ × ℝ`. -/
private theorem cellIndex_preimage (R : ℕ) (n : Fin 2 → ℤ) :
    cellIndex R ⁻¹' {n} = Complex.measurableEquivRealProd ⁻¹'
      (((fun x : ℝ => (R : ℝ) * x) ⁻¹' Set.Ico (n 0 : ℝ) (n 0 + 1)) ×ˢ
        ((fun x : ℝ => (R : ℝ) * x) ⁻¹' Set.Ico (n 1 : ℝ) (n 1 + 1))) := by
  ext ξ
  simp [cellIndex, funext_iff, Fin.forall_fin_two, Int.floor_eq_iff]

/-- Each cell of `R⁻¹ ℤ²` has measure `R⁻²`. -/
private theorem volume_real_cellIndex_preimage {R : ℕ} (hR : R ≠ 0) (n : Fin 2 → ℤ) :
    volume.real (cellIndex R ⁻¹' {n}) = ((R : ℝ) ^ 2)⁻¹ := by
  have hR' : (0 : ℝ) < R := by positivity
  have hm : ∀ k : ℤ, MeasurableSet ((fun x : ℝ => (R : ℝ) * x) ⁻¹' Set.Ico (k : ℝ) (k + 1)) :=
    fun _ => measurableSet_Ico.preimage (measurable_id.const_mul _)
  rw [Measure.real, cellIndex_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((hm _).prod (hm _)).nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_preimage_mul_left hR'.ne', Real.volume_preimage_mul_left hR'.ne', Real.volume_Ico,
    Real.volume_Ico]
  simp [abs_of_pos hR', ENNReal.toReal_mul, sq]

private theorem rpow_neg_three {x : ℝ} (hx : 0 ≤ x) : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_ofNat]

/-! ### Riemann sums -/

/-- Lattice Riemann sums: for `φ` continuous off `0` with `|φ (ξ)| ≤ C (1 + |ξ|)^{−3}`,
`Σ_{n ∈ ℤ²} R⁻² φ (n / R) → ∫_ℂ φ` as `R → ∞`. -/
theorem tendsto_riemannSum {φ : ℂ → ℂ} (hφ : ∀ ξ ≠ 0, ContinuousAt φ ξ) {C : ℝ}
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-3 : ℝ)) :
    Tendsto (fun R : ℕ => ∑' n : Fin 2 → ℤ, ((R : ℂ) ^ 2)⁻¹ * φ (latticePoint n / R)) atTop
      (𝓝 (∫ ξ, φ ξ)) := by
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  -- The step functions `S R ξ = φ (⌊R ξ⌋ / R)`, constant on the cells of `R⁻¹ ℤ²`.
  set S : ℕ → ℂ → ℂ := fun R ξ => φ (latticePoint (cellIndex R ξ) / R) with hS
  -- The dominating function.
  set g : ℂ → ℝ := fun ξ => C * 27 * (1 + ‖ξ‖) ^ (-3 : ℝ) with hg
  have hg_int : Integrable g :=
    (integrable_one_add_norm (by simp [Complex.finrank_real_complex]; norm_num)).const_mul _
  have hS_meas : ∀ R, AEStronglyMeasurable (S R) volume := fun R =>
    ((measurable_of_countable fun n => φ (latticePoint n / R)).comp
      (measurable_cellIndex R)).aestronglyMeasurable
  have hS_bound : ∀ R : ℕ, 1 ≤ R → ∀ ξ, ‖S R ξ‖ ≤ g ξ := by
    intro R hR ξ
    set p := latticePoint (cellIndex R ξ) / R
    have hp : ‖ξ‖ ≤ ‖p‖ + 2 := by
      have h1 := norm_latticePoint_cellIndex_div_sub_le (by omega : R ≠ 0) ξ
      have h2 : (2 : ℝ) / R ≤ 2 := div_le_self zero_le_two (by exact_mod_cast hR)
      have h3 := norm_sub_norm_le ξ p
      rw [norm_sub_rev] at h3
      linarith
    have h1 : (1 + ‖ξ‖) ^ 3 ≤ 27 * (1 + ‖p‖) ^ 3 := by
      have : 1 + ‖ξ‖ ≤ 3 * (1 + ‖p‖) := by linarith [norm_nonneg p]
      calc (1 + ‖ξ‖) ^ 3 ≤ (3 * (1 + ‖p‖)) ^ 3 := by gcongr
        _ = 27 * (1 + ‖p‖) ^ 3 := by ring
    calc ‖S R ξ‖ ≤ C * (1 + ‖p‖) ^ (-3 : ℝ) := hC p
      _ ≤ g ξ := by
        simp only [hg, rpow_neg_three (by positivity : (0 : ℝ) ≤ 1 + ‖p‖),
          rpow_neg_three (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖), mul_assoc]
        gcongr
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        linarith
  have hS_int : ∀ R : ℕ, 1 ≤ R → Integrable (S R) := fun R hR =>
    hg_int.mono' (hS_meas R) (ae_of_all _ (hS_bound R hR))
  -- The integral of `S R` is the Riemann sum.
  have hsum : ∀ R : ℕ, 1 ≤ R →
      HasSum (fun n => ((R : ℂ) ^ 2)⁻¹ * φ (latticePoint n / R)) (∫ ξ, S R ξ) := by
    intro R hR
    have hR0 : R ≠ 0 := by omega
    have hm : ∀ n, MeasurableSet (cellIndex R ⁻¹' {n}) := fun n =>
      measurable_cellIndex R (measurableSet_singleton n)
    have h := hasSum_integral_iUnion (μ := volume) hm
      (fun m n hmn => (Set.disjoint_singleton.mpr hmn).preimage _) (hS_int R hR).integrableOn
    rw [← Set.preimage_iUnion, Set.iUnion_of_singleton, Set.preimage_univ,
      Measure.restrict_univ] at h
    convert h using 1
    funext n
    rw [setIntegral_congr_fun (hm n) (g := fun _ => φ (latticePoint n / R))
      (fun ξ hξ => by simp only [hS, Set.mem_singleton_iff.mp hξ]),
      setIntegral_const, volume_real_cellIndex_preimage hR0, Complex.real_smul]
    push_cast
    rfl
  -- Dominated convergence.
  have hlim : Tendsto (fun R => ∫ ξ, S R ξ) atTop (𝓝 (∫ ξ, φ ξ)) := by
    refine tendsto_integral_filter_of_dominated_convergence g (Eventually.of_forall hS_meas)
      (eventually_atTop.mpr ⟨1, fun R hR => ae_of_all _ (hS_bound R hR)⟩) hg_int ?_
    filter_upwards [Measure.ae_ne volume 0] with ξ hξ
    refine (hφ ξ hξ).tendsto.comp ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_atTop.mpr ⟨1, fun R hR => norm_latticePoint_cellIndex_div_sub_le (by omega) ξ⟩)
      (tendsto_const_div_atTop_nhds_zero_nat 2)
  exact hlim.congr' (eventually_atTop.mpr ⟨1, fun R hR => (hsum R hR).tsum_eq.symm⟩)

end HarmonicAnalysis
