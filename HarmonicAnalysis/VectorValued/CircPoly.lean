/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Defs
public import HarmonicAnalysis.VectorValued.Defs
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Vector-valued trigonometric polynomials on the circle

`circPoly c = Σ_n c_n e_n` is the trigonometric polynomial on `𝕋 = ℝ / ℤ` with coefficients `c_n` in
a complex vector space, `e_n (t) = e^{2πi n t}`. For scalar coefficients it is the trigonometric
polynomial `trigPoly` of the torus of dimension `1` (`circPoly_eq_trigPoly`).
-/

@[expose] public section

open MeasureTheory AddCircle
open scoped ENNReal

namespace HarmonicAnalysis

section Algebra

variable {V V' : Type*} [AddCommMonoid V] [Module ℂ V] [AddCommMonoid V'] [Module ℂ V']

/-- The trigonometric polynomial whose coefficients are zero. -/
theorem circPoly_zero (t : UnitAddCircle) : circPoly (0 : ℤ →₀ V) t = 0 :=
  Finsupp.sum_zero_index

/-- The trigonometric polynomial `e_k x`. -/
theorem circPoly_single (k : ℤ) (x : V) (t : UnitAddCircle) :
    circPoly (Finsupp.single k x) t = fourier k t • x :=
  Finsupp.sum_single_index (smul_zero _)

/-- The sum of two trigonometric polynomials. -/
theorem circPoly_add (c d : ℤ →₀ V) (t : UnitAddCircle) :
    circPoly (c + d) t = circPoly c t + circPoly d t :=
  Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _

/-- The image of a trigonometric polynomial under a linear map. -/
theorem circPoly_mapRange (T : V →ₗ[ℂ] V') (c : ℤ →₀ V) (t : UnitAddCircle) :
    circPoly (c.mapRange T (map_zero T)) t = T (circPoly c t) := by
  rw [circPoly, Finsupp.sum_mapRange_index fun _ => smul_zero _, circPoly, map_finsuppSum]
  simp only [map_smul]

/-- The product of a scalar and a trigonometric polynomial. -/
theorem circPoly_smul (z : ℂ) (c : ℤ →₀ V) (t : UnitAddCircle) :
    circPoly (z • c) t = z • circPoly c t :=
  circPoly_mapRange (LinearMap.lsmul ℂ V z) c t

/-- A finite sum of trigonometric polynomials. -/
theorem circPoly_sum {ι : Type*} (s : Finset ι) (c : ι → ℤ →₀ V) (t : UnitAddCircle) :
    circPoly (∑ i ∈ s, c i) t = ∑ i ∈ s, circPoly (c i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact circPoly_zero t
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, circPoly_add, ih]

/-- For scalar coefficients, `circPoly` is `trigPoly` on the torus of dimension `1`. -/
theorem circPoly_eq_trigPoly (c : ℤ →₀ ℂ) (t : UnitAddCircle) :
    circPoly c t = trigPoly (c.mapDomain fun k (_ : Unit) => k) fun _ => t := by
  have hinj : Function.Injective fun (k : ℤ) (_ : Unit) => k := fun k l h => congrFun h ()
  rw [trigPoly, Finsupp.sum_mapDomain_index_inj hinj, circPoly]
  refine Finsupp.sum_congr fun k _ => ?_
  have h : UnitAddTorus.mFourier (fun _ : Unit => k) (fun _ => t) = fourier k t := by
    simp [UnitAddTorus.mFourier]
  rw [h, smul_eq_mul, mul_comm]

end Algebra

section Normed

/-- Continuous functions on the circle are integrable. -/
theorem integrable_haar_of_continuous {E : Type*} [NormedAddCommGroup E] {u : UnitAddCircle → E}
    (hu : Continuous u) : Integrable u haarAddCircle :=
  hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Trigonometric polynomials are continuous. -/
theorem continuous_circPoly (c : ℤ →₀ X) : Continuous (circPoly c) := by
  unfold circPoly Finsupp.sum
  exact continuous_finsetSum _ fun n _ => (map_continuous (fourier n)).smul continuous_const

/-- Trigonometric polynomials are in `L^r`. -/
theorem memLp_circPoly (c : ℤ →₀ X) (r : ℝ≥0∞) : MemLp (circPoly c) r haarAddCircle :=
  (continuous_circPoly c).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The characters `e_k` have modulus `1`. -/
theorem norm_fourier_apply_eq_one (k : ℤ) (t : UnitAddCircle) : ‖fourier k t‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- The Fourier coefficients of a trigonometric polynomial. -/
theorem integral_fourier_smul_circPoly [CompleteSpace X] (c : ℤ →₀ X) (n : ℤ) :
    ∫ t, fourier (-n) t • circPoly c t ∂haarAddCircle = c n := by
  have hi : ∀ m : ℤ, Integrable (fun t : UnitAddCircle => fourier (-n) t • fourier m t • c m)
      haarAddCircle := fun m => integrable_haar_of_continuous
    ((map_continuous (fourier (-n))).smul ((map_continuous (fourier m)).smul continuous_const))
  have hterm : ∀ m : ℤ, ∫ t : UnitAddCircle, fourier (-n) t • fourier m t • c m ∂haarAddCircle =
      if n = m then c m else 0 := fun m => by
    have h := congrFun (fourierCoeff_fourier (T := 1) m) n
    rw [fourierCoeff, Pi.single_apply] at h
    simp only [smul_smul]
    simp only [smul_eq_mul] at h
    rw [integral_smul_const, h]
    split_ifs <;> simp
  simp only [circPoly, Finsupp.sum, Finset.smul_sum]
  rw [integral_finsetSum _ fun m _ => hi m, Finset.sum_congr rfl fun m _ => hterm m,
    Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

end Normed

end HarmonicAnalysis
