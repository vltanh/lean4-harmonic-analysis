/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The torus `𝕋^ι`, periodic functions on `ℝ^ι` and the unit cube

* `UnitAddTorus.ofPi : ℝ^ι → 𝕋^ι = (ℝ / ℤ)^ι` and its measurable section
  `UnitAddTorus.toPi : 𝕋^ι → (0, 1]^ι`; `ℤ^ι`-periodic functions (`UnitAddTorus.IsPeriodic`).
* The open unit cube `(0, 1)^ι` (`UnitAddTorus.cube`): integrals over the torus, with the Haar
  measure of total mass one, are integrals over the cube (`UnitAddTorus.integral_cube_ofPi`); the
  monomials `e_n (x) = e^{2πi ⟨n, x⟩}` on `ℝ^ι` (`UnitAddTorus.mFourier_ofPi`) and their
  orthogonality on the cube (`UnitAddTorus.integral_cube_mFourier`).
* The torus `𝕋²` and `ℂ ≅ ℝ²` (`x + iy ↦ (x, y)`): the lattice point `n₀ + i n₁` of `n ∈ ℤ²`
  (`HarmonicAnalysis.latticePoint`), the projection `HarmonicAnalysis.ofComplex : ℂ → 𝕋²`, with
  `e_n (y) = e^{2πi ⟨n₀ + i n₁, y⟩}` (`HarmonicAnalysis.mFourier_ofComplex`), and integrals over
  `𝕋²` as integrals over the centred cell `(−½, ½]²` of `ℂ`
  (`HarmonicAnalysis.lintegral_torus_eq_centredCell`).

The first two items normalise the measure on `ℝ / ℤ` as `Mathlib.Analysis.Fourier.AddCircleMulti`
does, with its local instances; the last item uses Mathlib's global measure on `ℝ / ℤ`, which is
the same measure of total mass one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Complex
open scoped ComplexConjugate Real Finset ENNReal

section HaarNormalized

/-! As in `Mathlib.Analysis.Fourier.AddCircleMulti`, the measure on `ℝ / ℤ` is the Haar measure of
total mass one. -/
attribute [local instance] instMeasureSpaceUnitAddCircle instIsAddHaarMeasureUnitAddCircleVolume
  instIsProbabilityMeasureUnitAddCircleVolume

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-! ### Periodic functions on `ℝ^ι` and functions on the torus -/

/-- The projection `ℝ^ι → 𝕋^ι = (ℝ / ℤ)^ι`. -/
def ofPi (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

omit [Fintype ι] in
theorem continuous_ofPi : Continuous (ofPi : (ι → ℝ) → UnitAddTorus ι) :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_apply i)

omit [Fintype ι] in
theorem measurable_ofPi [Finite ι] : Measurable (ofPi : (ι → ℝ) → UnitAddTorus ι) :=
  continuous_ofPi.measurable

omit [Fintype ι] in
theorem ofPi_add (x y : ι → ℝ) : ofPi (x + y) = ofPi x + ofPi y := by
  funext i; simp [ofPi]

omit [Fintype ι] in
theorem ofPi_add_int (x : ι → ℝ) (k : ι → ℤ) : ofPi (x + fun i => (k i : ℝ)) = ofPi x := by
  funext i
  simp only [ofPi, Pi.add_apply, AddCircle.coe_add, add_eq_left]
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k i, by simp⟩

/-- The representative of a point of the torus in `(0, 1]^ι`. -/
def toPi (z : UnitAddTorus ι) : ι → ℝ := ((measurableEquivPiIoc (0 : ι → ℝ) z : _) : ι → ℝ)

omit [Fintype ι] in
theorem measurable_toPi : Measurable (toPi : UnitAddTorus ι → ι → ℝ) :=
  measurable_subtype_coe.comp (measurableEquivPiIoc (0 : ι → ℝ)).measurable

omit [Fintype ι] in
theorem ofPi_toPi (z : UnitAddTorus ι) : ofPi (toPi z) = z := by
  funext i
  simp [ofPi, toPi]

omit [Fintype ι] in
theorem exists_toPi_ofPi (x : ι → ℝ) : ∃ k : ι → ℤ, toPi (ofPi x) = x + fun i => (k i : ℝ) := by
  have h : ∀ i, ∃ k : ℤ, toPi (ofPi x) i = x i + k := by
    intro i
    have h1 : ((toPi (ofPi x) i - x i : ℝ) : UnitAddCircle) = 0 := by
      have := congrFun (ofPi_toPi (ofPi x)) i
      simp only [ofPi] at this
      rw [AddCircle.coe_sub, this, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
    exact ⟨k, by simp at hk; linarith⟩
  choose k hk using h
  exact ⟨k, funext fun i => by simp [hk i]⟩

/-- `g` is `ℤ^ι`-periodic. -/
def IsPeriodic {E : Type*} (g : (ι → ℝ) → E) : Prop :=
  ∀ (x : ι → ℝ) (k : ι → ℤ), g (x + fun i => (k i : ℝ)) = g x

omit [Fintype ι] in
theorem IsPeriodic.comp_toPi_ofPi {E : Type*} {g : (ι → ℝ) → E} (hg : IsPeriodic g)
    (x : ι → ℝ) : g (toPi (ofPi x)) = g x := by
  obtain ⟨k, hk⟩ := exists_toPi_ofPi x
  rw [hk, hg]

/-- The open unit cube `(0, 1)^ι`. -/
abbrev cube (ι : Type*) : Set (ι → ℝ) := univ.pi fun _ => Ioo (0 : ℝ) 1

omit [Fintype ι] in
theorem measurableSet_cube [Finite ι] : MeasurableSet (cube ι) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem volume_cube : volume (cube ι) = 1 := by
  rw [Real.volume_pi_Ioo]; simp

instance : IsFiniteMeasure (volume.restrict (cube ι)) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_cube]; exact ENNReal.one_lt_top⟩

/-- Integrals over the torus (with the Haar measure of total mass one, as in
`Mathlib.Analysis.Fourier.AddCircleMulti`) are integrals over the cube. -/
theorem integral_cube_ofPi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : UnitAddTorus ι → E) : ∫ x in cube ι, F (ofPi x) = ∫ z, F z := by
  rw [integral_preimage F 0]
  have h1 : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      univ.pi fun _ => Ioc (0 : ℝ) 1 := by
    ext x; simp
  rw [h1]
  exact setIntegral_congr_set
    (Measure.univ_pi_Ioo_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm)

/-- The integral over the cube of a periodic function is invariant under translations. -/
theorem integral_cube_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hg : IsPeriodic g) (a : ι → ℝ) :
    ∫ x in cube ι, g (x + a) = ∫ x in cube ι, g x := by
  have h1 : ∀ x, g (x + a) = (g ∘ toPi) (ofPi x + ofPi a) := fun x => by
    rw [Function.comp_apply, ← ofPi_add, hg.comp_toPi_ofPi]
  have h2 : ∀ x, g x = (g ∘ toPi) (ofPi x) := fun x => (hg.comp_toPi_ofPi x).symm
  simp_rw [h1, h2]
  rw [integral_cube_ofPi (fun z => (g ∘ toPi) (z + ofPi a)), integral_cube_ofPi,
    integral_add_right_eq_self]

/-! ### The monomials on `ℝ^ι` -/

theorem mFourier_ofPi (n : ι → ℤ) (x : ι → ℝ) :
    mFourier n (ofPi x) = Complex.exp (2 * π * I * ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, ofPi, fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem norm_mFourier_ofPi (n : ι → ℤ) (x : ι → ℝ) : ‖mFourier n (ofPi x)‖ = 1 := by
  simp [mFourier, fourier_apply, norm_prod, Circle.norm_coe]

theorem mFourier_ofPi_add (n : ι → ℤ) (x y : ι → ℝ) :
    mFourier n (ofPi (x + y)) = mFourier n (ofPi x) * mFourier n (ofPi y) := by
  simp only [mFourier_ofPi, ← Complex.exp_add, Pi.add_apply]
  congr 1
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mFourier_ofPi_neg (n : ι → ℤ) (x : ι → ℝ) :
    mFourier (-n) (ofPi x) = mFourier n (ofPi (-x)) := by
  simp only [mFourier_ofPi, Pi.neg_apply]
  congr 1
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mFourier_ofPi_add_index (m n : ι → ℤ) (x : ι → ℝ) :
    mFourier (m + n) (ofPi x) = mFourier m (ofPi x) * mFourier n (ofPi x) :=
  mFourier_add

theorem continuous_mFourier_ofPi (n : ι → ℤ) : Continuous fun x : ι → ℝ => mFourier n (ofPi x) :=
  (mFourier n).continuous.comp continuous_ofPi

theorem mFourier_ofPi_isPeriodic (n : ι → ℤ) : IsPeriodic fun x : ι → ℝ => mFourier n (ofPi x) :=
  fun x k => by simp only [ofPi_add_int]

/-- Orthogonality: `∫_{(0,1)^ι} e_m = 1` if `m = 0`, and `0` otherwise. -/
theorem integral_cube_mFourier (m : ι → ℤ) :
    ∫ x in cube ι, mFourier m (ofPi x) = if m = 0 then 1 else 0 := by
  rw [integral_cube_ofPi (fun z => mFourier m z)]
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := ι))) 0 m
  rw [ContinuousMap.inner_toLp] at h
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  rw [h]
  by_cases hm : m = 0 <;> simp [hm, eq_comm]

end UnitAddTorus

end HaarNormalized

namespace HarmonicAnalysis

open UnitAddTorus

/-- The lattice point `n₀ + i n₁ ∈ ℂ` of `n ∈ ℤ²`. -/
def latticePoint (n : Fin 2 → ℤ) : ℂ := (n 0 : ℂ) + (n 1 : ℂ) * Complex.I

/-- The projection `ℂ → 𝕋² = (ℝ / ℤ)²`, `y ↦ (Re y, Im y) mod ℤ²`. -/
def ofComplex (y : ℂ) : UnitAddTorus (Fin 2) := ofPi ![y.re, y.im]

/-- The centred cell `{y : Re y, Im y ∈ (−½, ½]}` of the lattice `ℤ² = ℤ + iℤ ⊂ ℂ`. -/
def centredCell : Set ℂ := {y | y.re ∈ Ioc (-2⁻¹ : ℝ) 2⁻¹ ∧ y.im ∈ Ioc (-2⁻¹ : ℝ) 2⁻¹}

/-- The monomial `e_n` on `ℂ`: `e_n (y) = e^{2πi ⟨n₀ + i n₁, y⟩}`. -/
theorem mFourier_ofComplex (n : Fin 2 → ℤ) (y : ℂ) :
    mFourier n (ofComplex y) =
      Complex.exp (2 * π * Complex.I * (inner ℝ (latticePoint n) y : ℝ)) := by
  rw [ofComplex, mFourier_ofPi]
  congr 1
  simp [Fin.sum_univ_two, latticePoint, Complex.inner]
  ring

/-- Integrals over `𝕋²` (with Mathlib's measure, of total mass one) are integrals over the centred
cell of `ℂ`. -/
theorem lintegral_torus_eq_centredCell (f : UnitAddTorus (Fin 2) → ℝ≥0∞) :
    ∫⁻ x, f x = ∫⁻ y in centredCell, f (ofComplex y) := by
  sorry

end HarmonicAnalysis
