/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import HarmonicAnalysis.Torus.Lipschitz
public import HarmonicAnalysis.Torus.Lattice
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.PSeries

/-!
# Smooth periodic functions on `ℝ^ι`, their Fourier series and Fourier multipliers

For `ℤ^ι`-periodic functions `g : ℝ^ι → ℂ` (`UnitAddTorus.IsPeriodic`), with the Fourier
coefficients `ĝ (n) = ∫_{(0,1)^ι} e^{−2πi ⟨n, x⟩} g (x) dx` (`UnitAddTorus.cubeFourierCoeff`) and
the monomials `e_n (x) = e^{2πi ⟨n, x⟩}` (`UnitAddTorus.mFourier n (UnitAddTorus.ofPi x)`); the
norm `‖n‖` of `n ∈ ℤ^ι` is the sup norm. The arguments are the standard ones of Grafakos,
*Classical Fourier Analysis*, Chapter 3, and Katznelson, *An Introduction to Harmonic Analysis*,
Chapter I.

* A `C¹` periodic map is Lipschitz (`UnitAddTorus.IsPeriodic.exists_lipschitzWith`: its derivative
  is periodic and continuous, hence bounded, and the mean value inequality).
* The coefficients of a derivative: `(∂_v g)^ (n) = 2πi ⟨n, v⟩ ĝ (n)` for `C¹` periodic `g`
  (`UnitAddTorus.cubeFourierCoeff_fderiv_of_contDiff`), by the difference quotient argument.
* Rapid decay: for smooth periodic `g`, `(1 + ‖n‖)^k |ĝ (n)|` is bounded and summable for every
  `k` (`UnitAddTorus.exists_norm_cubeFourierCoeff_le`, `UnitAddTorus.summable_cubeFourierCoeff`),
  by integrating by parts `k` times in one coordinate.
* The Fourier series of a smooth periodic `g` converges absolutely to `g`
  (`UnitAddTorus.hasSum_cubeFourierCoeff_mul_mFourier`, from Mathlib's
  `hasSum_mFourier_series_apply_of_summable`), hence the uniqueness of the coefficients
  (`UnitAddTorus.eq_of_cubeFourierCoeff_eq`).
* Fourier multipliers `T_m g = Σ_n m (n) ĝ (n) e_n` (`UnitAddTorus.periodicMultiplier`) with
  polynomially bounded symbols `m` (`UnitAddTorus.IsPolyBounded`): `T_m g` is smooth and periodic
  (`UnitAddTorus.contDiff_periodicMultiplier`, by the Weierstrass M-test for all derivatives),
  with coefficients `m ĝ` (`UnitAddTorus.cubeFourierCoeff_periodicMultiplier`, by termwise
  integration); `T_m T_{m'} = T_{m m'}`, `T_1 = id`, `T_m ∂_v = T_{2πi ⟨·, v⟩ m}`, linearity, and
  `T_m` on trigonometric polynomials, by comparing coefficients.
* On `ℝ² ≅ ℂ`: the Wirtinger derivatives `∂ = ½ (∂_x − i ∂_y)`, `∂̄ = ½ (∂_x + i ∂_y)`
  (`UnitAddTorus.dzPi`, `UnitAddTorus.dzbarPi`), with the symbols `πi ν̄` and `πi ν`,
  `ν = n₀ + i n₁` (`HarmonicAnalysis.latticePoint`); the inverse of `∂̄` on mean-zero smooth
  periodic functions, the multiplier with symbol `(πi ν)⁻¹` off `0`
  (`UnitAddTorus.dzbarPi_periodicMultiplier_dzbarInvSymbol`, `UnitAddTorus.exists_dzbarPi_eq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Complex
open scoped ComplexConjugate Real ContDiff

/-! As in `Mathlib.Analysis.Fourier.AddCircleMulti` (whose local instances these are), the measure
on `ℝ / ℤ` is the Haar measure of total mass one. -/
attribute [local instance] instMeasureSpaceUnitAddCircle instIsAddHaarMeasureUnitAddCircleVolume
  instIsProbabilityMeasureUnitAddCircleVolume

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-! ### Periodic functions -/

omit [Fintype ι] in
/-- A continuous periodic function induces a continuous function on the torus. -/
theorem IsPeriodic.continuous_comp_toPi {E : Type*} [TopologicalSpace E] {g : (ι → ℝ) → E}
    (hc : Continuous g) (hper : IsPeriodic g) : Continuous (g ∘ toPi) := by
  sorry

omit [Fintype ι] in
/-- A continuous periodic function is bounded. -/
theorem IsPeriodic.exists_bound {E : Type*} [SeminormedAddCommGroup E] {g : (ι → ℝ) → E}
    (hc : Continuous g) (hper : IsPeriodic g) : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  sorry

omit [Fintype ι] in
/-- The derivative of a periodic map is periodic. -/
theorem isPeriodic_fderiv [Finite ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hper : IsPeriodic g) : IsPeriodic (fderiv ℝ g) := by
  sorry

omit [Fintype ι] in
/-- The directional derivatives of a periodic map are periodic. -/
theorem IsPeriodic.fderiv_apply [Finite ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hper : IsPeriodic g) (v : ι → ℝ) : IsPeriodic fun x => fderiv ℝ g x v := by
  sorry

/-- A `C¹` periodic map is Lipschitz: its derivative is continuous and periodic, hence bounded,
and the mean value inequality applies. -/
theorem IsPeriodic.exists_lipschitzWith {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (ι → ℝ) → E} (hg : ContDiff ℝ 1 g) (hper : IsPeriodic g) :
    ∃ K : NNReal, LipschitzWith K g := by
  sorry

/-! ### Coefficients -/

/-- The coefficients are bounded by the sup norm. -/
theorem norm_cubeFourierCoeff_le {g : (ι → ℝ) → ℂ} {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (n : ι → ℤ) :
    ‖cubeFourierCoeff g n‖ ≤ C := by
  sorry

/-- The coefficients over the cube of a periodic `g` are the Fourier coefficients on the torus of
the function `g ∘ toPi` that `g` induces there. -/
theorem mFourierCoeff_comp_toPi {g : (ι → ℝ) → ℂ} (hper : IsPeriodic g) (n : ι → ℤ) :
    mFourierCoeff (g ∘ toPi) n = cubeFourierCoeff g n := by
  sorry

/-- The coefficients of the derivative of a Lipschitz `ℤ^ι`-periodic `g : ℝ^ι → ℂ`:
`(∂_v g)^ (n) = 2πi ⟨n, v⟩ ĝ (n)`, with `∂_v g (x) = fderiv ℝ g x v` (the derivative almost
everywhere, by Rademacher's theorem). The difference quotient argument of
`UnitAddTorus.cubeFourierCoeff_fderiv`: integrate `t⁻¹ (g (x + t v) − g (x))` against `e_{−n}`,
move the translation onto `e_{−n}` and let `t → 0`. -/
theorem cubeFourierCoeff_fderiv_of_lipschitzWith {g : (ι → ℝ) → ℂ} {C : NNReal}
    (hg : LipschitzWith C g) (hper : IsPeriodic g) (v : ι → ℝ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => fderiv ℝ g x v) n =
      2 * π * I * (∑ i, (n i : ℂ) * (v i : ℂ)) * cubeFourierCoeff g n := by
  sorry

/-- The coefficients of the derivative of a `C¹` periodic `g : ℝ^ι → ℂ`:
`(∂_v g)^ (n) = 2πi ⟨n, v⟩ ĝ (n)`. -/
theorem cubeFourierCoeff_fderiv_of_contDiff {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (v : ι → ℝ) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => fderiv ℝ g x v) n =
      2 * π * I * (∑ i, (n i : ℂ) * (v i : ℂ)) * cubeFourierCoeff g n := by
  sorry

/-- The derivative of a `C¹` periodic function has mean zero. -/
theorem cubeFourierCoeff_fderiv_zero {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (v : ι → ℝ) : cubeFourierCoeff (fun x => fderiv ℝ g x v) 0 = 0 := by
  sorry

/-! ### Rapid decay and the Fourier series of a smooth periodic function -/

/-- Rapid decay of the coefficients of a smooth periodic `g`: `(1 + ‖n‖)^k |ĝ (n)|` is bounded,
by integrating by parts `k` times in one coordinate (the derivative formula
`UnitAddTorus.cubeFourierCoeff_fderiv_of_contDiff` along a coordinate vector). -/
theorem exists_norm_cubeFourierCoeff_le {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) (k : ℕ) :
    ∃ C : ℝ, ∀ n : ι → ℤ, (1 + ‖n‖) ^ k * ‖cubeFourierCoeff g n‖ ≤ C := by
  sorry

/-- `Σ_{n ∈ ℤ^ι} (1 + ‖n‖)^{−2 card ι}` converges, by comparison with
`Π_i Σ_{m ∈ ℤ} (1 + |m|)^{−2}`. -/
theorem summable_one_add_norm_pow_inv :
    Summable fun n : ι → ℤ => ((1 + ‖n‖) ^ (2 * Fintype.card ι))⁻¹ := by
  sorry

/-- For smooth periodic `g`, `Σ_n (1 + ‖n‖)^k |ĝ (n)|` converges for every `k`. -/
theorem summable_cubeFourierCoeff {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) (k : ℕ) :
    Summable fun n : ι → ℤ => (1 + ‖n‖) ^ k * ‖cubeFourierCoeff g n‖ := by
  sorry

/-- The Fourier series of a smooth periodic `g` converges absolutely to `g`:
`g (x) = Σ_n ĝ (n) e^{2πi ⟨n, x⟩}` (Mathlib's `hasSum_mFourier_series_apply_of_summable` for the
function `g ∘ toPi` on the torus). -/
theorem hasSum_cubeFourierCoeff_mul_mFourier {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) (x : ι → ℝ) :
    HasSum (fun n => cubeFourierCoeff g n * mFourier n (ofPi x)) (g x) := by
  sorry

/-- Uniqueness of Fourier coefficients: smooth periodic functions with the same coefficients are
equal. -/
theorem eq_of_cubeFourierCoeff_eq {g g' : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (hper : IsPeriodic g) (hg' : ContDiff ℝ ∞ g') (hper' : IsPeriodic g')
    (h : ∀ n, cubeFourierCoeff g n = cubeFourierCoeff g' n) : g = g' := by
  sorry

/-- The coefficients of an absolutely convergent trigonometric series `Σ_l c_l e_l` are `c`
(termwise integration and the orthogonality of the monomials). -/
theorem cubeFourierCoeff_tsum_mFourier {c : (ι → ℤ) → ℂ} (hc : Summable c) (n : ι → ℤ) :
    cubeFourierCoeff (fun x => ∑' l, c l * mFourier l (ofPi x)) n = c n := by
  sorry

/-! ### Polynomially bounded symbols -/

/-- The symbol `m : ℤ^ι → ℂ` is polynomially bounded: `|m (n)| ≤ C (1 + ‖n‖)^k`. -/
def IsPolyBounded (m : (ι → ℤ) → ℂ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n, ‖m n‖ ≤ C * (1 + ‖n‖) ^ k

/-- Bounded symbols are polynomially bounded. -/
theorem isPolyBounded_of_norm_le {m : (ι → ℤ) → ℂ} {C : ℝ} (h : ∀ n, ‖m n‖ ≤ C) :
    IsPolyBounded m := by
  sorry

theorem isPolyBounded_const (c : ℂ) : IsPolyBounded fun _ : ι → ℤ => c := by
  sorry

theorem IsPolyBounded.add {m m' : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) (hm' : IsPolyBounded m') :
    IsPolyBounded fun n => m n + m' n := by
  sorry

theorem IsPolyBounded.mul {m m' : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) (hm' : IsPolyBounded m') :
    IsPolyBounded fun n => m n * m' n := by
  sorry

theorem IsPolyBounded.pow {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) (k : ℕ) :
    IsPolyBounded fun n => m n ^ k := by
  sorry

/-- The symbol `n ↦ 2πi ⟨n, v⟩` of the directional derivative `∂_v` is polynomially bounded. -/
theorem isPolyBounded_derivSymbol (v : ι → ℝ) :
    IsPolyBounded fun n : ι → ℤ => 2 * π * I * ∑ i, (n i : ℂ) * (v i : ℂ) := by
  sorry

/-! ### Fourier multipliers on smooth periodic functions -/

/-- The Fourier multiplier with symbol `m : ℤ^ι → ℂ` on periodic functions:
`T_m g (x) = Σ_n m (n) ĝ (n) e^{2πi ⟨n, x⟩}` (`0` where the series does not converge; it
converges absolutely for smooth periodic `g` and polynomially bounded `m`). -/
def periodicMultiplier (m : (ι → ℤ) → ℂ) (g : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  ∑' n, m n * cubeFourierCoeff g n * mFourier n (ofPi x)

theorem isPeriodic_periodicMultiplier (m : (ι → ℤ) → ℂ) (g : (ι → ℝ) → ℂ) :
    IsPeriodic (periodicMultiplier m g) := by
  sorry

/-- `T_m g` is smooth, by the Weierstrass M-test for the series of the derivatives of every order
(`contDiff_tsum`), whose terms are `O ((1 + ‖n‖)^{k + j} |ĝ (n)|)`. -/
theorem contDiff_periodicMultiplier {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) :
    ContDiff ℝ ∞ (periodicMultiplier m g) := by
  sorry

/-- The coefficients of `T_m g` are `m ĝ`, by termwise integration. -/
theorem cubeFourierCoeff_periodicMultiplier {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) (n : ι → ℤ) :
    cubeFourierCoeff (periodicMultiplier m g) n = m n * cubeFourierCoeff g n := by
  sorry

/-- `T_m T_{m'} = T_{m m'}` on smooth periodic functions. -/
theorem periodicMultiplier_periodicMultiplier {m m' : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    (hm' : IsPolyBounded m') {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) :
    periodicMultiplier m (periodicMultiplier m' g) =
      periodicMultiplier (fun n => m n * m' n) g := by
  sorry

/-- `T_1 = id` on smooth periodic functions: the Fourier series converges to the function. -/
theorem periodicMultiplier_one {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) :
    periodicMultiplier (fun _ => 1) g = g := by
  sorry

/-- `T_m ∂_v = T_{2πi ⟨·, v⟩ m}` on smooth periodic functions. -/
theorem periodicMultiplier_fderiv {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic g) (v : ι → ℝ) :
    periodicMultiplier m (fun x => fderiv ℝ g x v) =
      periodicMultiplier (fun n => 2 * π * I * (∑ i, (n i : ℂ) * (v i : ℂ)) * m n) g := by
  sorry

theorem periodicMultiplier_add {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) {g h : (ι → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodic g) (hh : ContDiff ℝ ∞ h) (hhp : IsPeriodic h) :
    periodicMultiplier m (fun x => g x + h x) =
      fun x => periodicMultiplier m g x + periodicMultiplier m h x := by
  sorry

theorem periodicMultiplier_sub {m : (ι → ℤ) → ℂ} (hm : IsPolyBounded m) {g h : (ι → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodic g) (hh : ContDiff ℝ ∞ h) (hhp : IsPeriodic h) :
    periodicMultiplier m (fun x => g x - h x) =
      fun x => periodicMultiplier m g x - periodicMultiplier m h x := by
  sorry

theorem periodicMultiplier_const_mul (m : (ι → ℤ) → ℂ) (c : ℂ) (g : (ι → ℝ) → ℂ) :
    periodicMultiplier m (fun x => c * g x) = fun x => c * periodicMultiplier m g x := by
  sorry

/-- `T_m` on trigonometric polynomials. -/
theorem periodicMultiplier_sum_mFourier (m : (ι → ℤ) → ℂ) (S : Finset (ι → ℤ))
    (c : (ι → ℤ) → ℂ) :
    periodicMultiplier m (fun x => ∑ n ∈ S, c n * mFourier n (ofPi x)) =
      fun x => ∑ n ∈ S, m n * c n * mFourier n (ofPi x) := by
  sorry

/-! ### The Wirtinger derivatives on `ℝ² ≅ ℂ` and the inverse of `∂̄`

With `ℝ² ≅ ℂ` by `(x, y) ↦ x + iy`, and the lattice point `ν = n₀ + i n₁` of `n ∈ ℤ²`
(`HarmonicAnalysis.latticePoint`). -/

section Two

/-- The Wirtinger derivative `∂g = ½ (∂_x g − i ∂_y g)` of `g : ℝ² → ℂ`. -/
def dzPi (g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  2⁻¹ * (fderiv ℝ g x (Pi.single 0 1) - I * fderiv ℝ g x (Pi.single 1 1))

/-- The Wirtinger derivative `∂̄g = ½ (∂_x g + i ∂_y g)` of `g : ℝ² → ℂ`. -/
def dzbarPi (g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  2⁻¹ * (fderiv ℝ g x (Pi.single 0 1) + I * fderiv ℝ g x (Pi.single 1 1))

theorem contDiff_dzPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (dzPi g) := by
  sorry

theorem contDiff_dzbarPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (dzbarPi g) := by
  sorry

theorem isPeriodic_dzPi {g : (Fin 2 → ℝ) → ℂ} (hper : IsPeriodic g) : IsPeriodic (dzPi g) := by
  sorry

theorem isPeriodic_dzbarPi {g : (Fin 2 → ℝ) → ℂ} (hper : IsPeriodic g) :
    IsPeriodic (dzbarPi g) := by
  sorry

/-- The symbol of `∂̄`: `(∂̄g)^ (n) = πi (n₀ + i n₁) ĝ (n)`. -/
theorem cubeFourierCoeff_dzbarPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (n : Fin 2 → ℤ) :
    cubeFourierCoeff (dzbarPi g) n =
      π * I * HarmonicAnalysis.latticePoint n * cubeFourierCoeff g n := by
  sorry

/-- The symbol of `∂`: `(∂g)^ (n) = πi (n₀ − i n₁) ĝ (n)`. -/
theorem cubeFourierCoeff_dzPi {g : (Fin 2 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hper : IsPeriodic g) (n : Fin 2 → ℤ) :
    cubeFourierCoeff (dzPi g) n =
      π * I * conj (HarmonicAnalysis.latticePoint n) * cubeFourierCoeff g n := by
  sorry

/-- The symbol of `∂̄⁻¹` on mean-zero functions: `(πi (n₀ + i n₁))⁻¹` for `n ≠ 0`, and `0` at
`n = 0`. -/
def dzbarInvSymbol (n : Fin 2 → ℤ) : ℂ :=
  if n = 0 then 0 else (π * I * HarmonicAnalysis.latticePoint n)⁻¹

theorem isPolyBounded_dzbarInvSymbol : IsPolyBounded dzbarInvSymbol := by
  sorry

/-- `∂̄ (T h) = h` for the multiplier `T` with symbol `dzbarInvSymbol` and every smooth periodic
`h` of mean zero, by comparing coefficients. -/
theorem dzbarPi_periodicMultiplier_dzbarInvSymbol {h : (Fin 2 → ℝ) → ℂ} (hh : ContDiff ℝ ∞ h)
    (hper : IsPeriodic h) (h0 : cubeFourierCoeff h 0 = 0) :
    dzbarPi (periodicMultiplier dzbarInvSymbol h) = h := by
  sorry

/-- Every smooth periodic `h` of mean zero is `∂̄u` for a smooth periodic `u` of mean zero. -/
theorem exists_dzbarPi_eq {h : (Fin 2 → ℝ) → ℂ} (hh : ContDiff ℝ ∞ h) (hper : IsPeriodic h)
    (h0 : cubeFourierCoeff h 0 = 0) :
    ∃ u, ContDiff ℝ ∞ u ∧ IsPeriodic u ∧ cubeFourierCoeff u 0 = 0 ∧ dzbarPi u = h := by
  sorry

end Two

end UnitAddTorus
