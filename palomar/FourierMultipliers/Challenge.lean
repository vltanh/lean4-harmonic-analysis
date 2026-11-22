module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Order.LiminfLimsup
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Challenge: Fourier multipliers on `L^p`, transference, powers of the Beurling–Ahlfors transform

Scalar Fourier multipliers `T_m f = 𝓕⁻¹ (m · 𝓕 f)` on `L^p`, `1 < p < ∞`, after

* [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*,
  Springer, 2016: Proposition 5.3.7, Proposition 5.7.4, Corollary 5.7.6;
* [D] O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471: Theorem 1.1;
* [CDK] A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex
  Riesz transform*, Math. Ann. 386 (2023), 1081–1125, arXiv:2109.08369: §1.3.1.

## Conventions

* `V` is a Euclidean space (a finite-dimensional real inner product space) with its Lebesgue
  measure, and `𝓕 f (ξ) = ∫ e^{−2πi ⟨v, ξ⟩} f (v) dv` (Mathlib's Fourier transform). The plane `ℝ²`
  is `ℂ`, by `x + iy ↦ (x, y)`, and the lattice `ℤ²` is `ℤ + iℤ` (`latticePoint`).
* The torus is `𝕋^ι = (ℝ / ℤ)^ι`, with its measure of total mass one, and
  `mFourier n (x) = e^{2πi ⟨n, x⟩}`, `n ∈ ℤ^ι`.
* `p` is a real number, and `eLpNorm f (ENNReal.ofReal p) volume` is `‖f‖_p`. Norms of multipliers
  are in `[0, ∞]` (`ℝ≥0∞`), and `∞` means that the operator is unbounded.
* `multiplierNorm m p` is the supremum of `‖T_m f‖_p / ‖f‖_p` over the Schwartz functions `f`. By
  `multiplierNorm_spec`, for bounded measurable `m` and `1 ≤ p < ∞`, it is finite if and only if
  `T_m` extends from Schwartz functions to a bounded operator on `L^p (V)`, and it is then the norm
  of that (unique) extension. ([HNVW, Definitions 5.3.1 and 5.3.3] extends `T_m` from the larger
  space of the `f ∈ L^p` that are inverse Fourier transforms of integrable functions. That this
  gives the same extension is [HNVW, p. 401 and Proposition 2.4.23], not formalized here.)
* `torusMultiplierNorm m p` is the supremum of `‖T_m f‖_p / ‖f‖_p` over the trigonometric
  polynomials `f` of mean zero, by which [HNVW, pp. 457–458] define multipliers on `L^p_0 (𝕋^ι)`.
  (They are dense in `L^p_0`, so that this is the norm of the extension of `T_m` to `L^p_0`; that is
  not formalized, and the bounds below do not need it, as the supremum is at most that norm.)
* The Beurling–Ahlfors transform `𝓑` is the Fourier multiplier with symbol `ξ̄ / ξ`, and `𝓑^k` the
  one with symbol `(ξ̄ / ξ)^k`. [D] defines `𝓑` (there `T`) as the singular integral
  `−(1/π) p.v. ∫ f (ζ) (z − ζ)^{−2} dA (ζ)`, which has this symbol [CDK, (1.1)–(1.3)], a classical
  fact that is not formalized here, and `𝓑^k` as its `k`-th power; `beurlingPow_dzbar_iterate` is
  the property `𝓑^k (∂̄^k F) = ∂^k F` by which [D] uses it, for both meanings of `𝓑^k`. That `𝓑` is
  bounded on `L^p` (Calderón–Zygmund) is neither assumed nor proved: the statements about
  `‖𝓑^k‖_p` hold in `[0, ∞]`.

## Statements

* `multiplierNorm_spec`: `multiplierNorm m p` is the norm of `T_m` on `L^p (V)`.
* `multiplierNorm_conjExponent` ([HNVW, Proposition 5.3.7], scalar): `‖T_m‖_p = ‖T_m‖_{p'}`.
* `transference` ([HNVW, Proposition 5.7.4], scalar, `d = 2`): if `m` is continuous off `0` and
  `ε_j ↓ 0`, then `‖T_m‖_{L^p (ℝ²)} ≤ liminf_j ‖T_{m (ε_j ·)}‖_{L^p_0 (𝕋²)}`.
* `transference_homogeneous` ([HNVW, Corollary 5.7.6], scalar, `d = 2`, only the inequality
  `I ≤ II` of its three equal norms): `‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}` if `m` is moreover
  homogeneous of degree `0`.
* `beurlingPow_dzbar_iterate`: `𝓑^k (∂̄^k F) = ∂^k F` for Schwartz functions `F`, also with the
  `k`-fold iterate of `𝓑` for `𝓑^k`.
* `beurlingPowNorm_conjExponent` ([CDK, §1.3.1], for the even powers `R^{2k} = 𝓑^k` of the complex
  Riesz transform `R`): `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}`.
* `dragicevic_limit`, `dragicevic_lower_bound` ([D, Theorem 1.1] for `n = 2` and one cutoff `g₂`
  only; there for every `n`, and `p > 2`): `‖∂² f_{2,α}‖_p / ‖∂̄² f_{2,α}‖_p → κ₂ (p)` as `α ↑ 1/p`,
  and `‖𝓑²‖_p ≥ κ₂ (p)`. `beurlingKappa_two`: `κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`.
* `dragicevic_lower_bound_pStar`, `pStar_sub_one_lt_beurlingPowNorm_two`: for `1 < p < ∞` and
  `p* = max (p, p')`, `‖𝓑²‖_p ≥ κ₂ (p*)`, and so `‖𝓑²‖_p > p* − 1` if `p ≠ 2`. For `p < 2`, the
  first is the bound for `p'` and [CDK, §1.3.1].

The definitions are copied word for word from `HarmonicAnalysis/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in
`palomar/FourierMultipliers/Solution.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace HarmonicAnalysis

-- BEGIN SHARED DEFINITIONS

/-! ### Fourier multipliers on a Euclidean space -/

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier multiplier with symbol `m`: `T_m f = 𝓕⁻¹ (m · 𝓕 f)`, by Mathlib's integral formulas
for `𝓕` and `𝓕⁻¹`. For a bounded measurable `m` and a Schwartz function `f`, `m · 𝓕 f` is
integrable and `T_m f (x) = ∫ m (ξ) 𝓕 f (ξ) e^{2πi ⟨ξ, x⟩} dξ`. -/
def fourierMultiplier (m : V → ℂ) (f : V → ℂ) : V → ℂ :=
  𝓕⁻ (fun ξ : V => m ξ • 𝓕 f ξ)

/-- `‖T_m‖_{L^p → L^p}`: the supremum, in `[0, ∞]`, of `‖T_m f‖_p / ‖f‖_p` over the Schwartz
functions `f` (dense in `L^p` for `1 ≤ p < ∞`; `0 / 0 = 0`). -/
def multiplierNorm (m : V → ℂ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ f : 𝓢(V, ℂ), eLpNorm (fourierMultiplier m f) (ENNReal.ofReal p) volume /
    eLpNorm (f : V → ℂ) (ENNReal.ofReal p) volume

end Euclidean

/-! ### Fourier multipliers on the torus -/

section Torus

open UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-- The trigonometric polynomial `x ↦ Σ_n c_n e^{2πi ⟨n, x⟩}` on the torus `𝕋^ι = (ℝ / ℤ)^ι`, for
finitely supported coefficients `c`. -/
def trigPoly (c : (ι → ℤ) →₀ ℂ) (x : UnitAddTorus ι) : ℂ :=
  c.sum fun n a => a * mFourier n x

/-- The Fourier multiplier with symbol `m : ℤ^ι → ℂ` applied to the trigonometric polynomial with
coefficients `c`: `x ↦ Σ_n m (n) c_n e^{2πi ⟨n, x⟩}`. -/
def torusMultiplier (m : (ι → ℤ) → ℂ) (c : (ι → ℤ) →₀ ℂ) (x : UnitAddTorus ι) : ℂ :=
  c.sum fun n a => m n * a * mFourier n x

/-- `‖T_m‖_{L^p_0 (𝕋^ι) → L^p_0 (𝕋^ι)}`, `L^p_0` the subspace of mean-zero functions: the supremum,
in `[0, ∞]`, of `‖T_m f‖_p / ‖f‖_p` over the (dense) trigonometric polynomials `f` of mean zero
(`c₀ = 0`). The value `m (0)` does not matter. -/
def torusMultiplierNorm (m : (ι → ℤ) → ℂ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ (c : (ι → ℤ) →₀ ℂ) (_ : c 0 = 0),
    eLpNorm (torusMultiplier m c) (ENNReal.ofReal p) volume /
      eLpNorm (trigPoly c) (ENNReal.ofReal p) volume

/-- The lattice point `n₀ + i n₁ ∈ ℂ` of `n ∈ ℤ²`. -/
def latticePoint (n : Fin 2 → ℤ) : ℂ := (n 0 : ℂ) + (n 1 : ℂ) * Complex.I

end Torus

/-! ### The Wirtinger derivatives -/

section Wirtinger

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Wirtinger derivative `∂g (z) = ½ (∂_x g (z) − i ∂_y g (z))` of a function `g : ℂ → F`
(`0` where `g` is not real-differentiable). -/
def dz (g : ℂ → F) (z : ℂ) : F :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 - Complex.I • fderiv ℝ g z Complex.I)

/-- The Wirtinger derivative `∂̄g (z) = ½ (∂_x g (z) + i ∂_y g (z))` of a function `g : ℂ → F`
(`0` where `g` is not real-differentiable). -/
def dzbar (g : ℂ → F) (z : ℂ) : F :=
  (2⁻¹ : ℂ) • (fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I)

end Wirtinger

/-! ### The Beurling–Ahlfors transform and its powers -/

/-- The symbol `m (ξ) = ξ̄ / ξ` of the Beurling–Ahlfors transform (`m (0) = 0`). -/
def beurlingSymbol (ξ : ℂ) : ℂ := conj ξ / ξ

/-- `𝓑^k f = 𝓕⁻¹ (m^k · 𝓕 f)`, with `m (ξ) = ξ̄ / ξ`. -/
def beurlingPow (k : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fourierMultiplier (fun ξ => beurlingSymbol ξ ^ k) f

/-- `‖𝓑^k‖_{L^p (ℝ²) → L^p (ℝ²)}`: the supremum, in `[0, ∞]`, of `‖𝓑^k f‖_p / ‖f‖_p` over the
(dense) Schwartz functions `f`. -/
def beurlingPowNorm (k : ℕ) (p : ℝ) : ℝ≥0∞ :=
  multiplierNorm (fun ξ => beurlingSymbol ξ ^ k) p

/-! ### Dragičević's constants and test functions -/

/-- Dragičević's constant `κ_n (p) = (1/q)_n / (1/p)_n`, `1/q = 1 − 1/p`, with the Pochhammer
symbol `(a)_n = a (a + 1) ⋯ (a + n − 1)`. -/
def beurlingKappa (n : ℕ) (p : ℝ) : ℝ :=
  (ascPochhammer ℝ n).eval (1 - p⁻¹) / (ascPochhammer ℝ n).eval p⁻¹

/-- `p* = max (p, p / (p − 1))`. -/
def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

/-- The cutoff `g_n (x) = 1` for `x ≤ 1`, `exp (−(x − 1)^n)` for `x > 1`, which Dragičević (2011,
p. 465) gives as an example of a sufficiently smooth, rapidly decaying `g_n` equal to `1` on
`[0, 1]`. -/
def BeurlingAhlfors.testCutoff (n : ℕ) (x : ℝ) : ℝ := if x ≤ 1 then 1 else Real.exp (-(x - 1) ^ n)

/-- Dragičević's test function `f_{n,α} (z) = z^n |z|^{−2α} g_n (|z|)`, with this cutoff `g_n`. -/
def BeurlingAhlfors.testFun (n : ℕ) (α : ℝ) (z : ℂ) : ℂ :=
  z ^ n * ((‖z‖ ^ (-2 * α) * testCutoff n ‖z‖ : ℝ) : ℂ)

-- END SHARED DEFINITIONS

end HarmonicAnalysis

namespace FourierMultipliersChallenge

open HarmonicAnalysis HarmonicAnalysis.BeurlingAhlfors Filter Topology

section Euclidean

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **What `multiplierNorm` is.** Let `m` be bounded and measurable, and `1 ≤ p < ∞`. If
`multiplierNorm m p` is finite, then there is exactly one bounded operator `T` on `L^p (V)` with
`T f = T_m f` for every Schwartz function `f`. Conversely, if `T` is such an operator, then its norm
is `multiplierNorm m p` (which is therefore finite). -/
theorem multiplierNorm_spec {m : V → ℂ} (hm : Measurable m) (hb : ∃ C : ℝ, ∀ ξ, ‖m ξ‖ ≤ C) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    (multiplierNorm m p ≠ ∞ →
      ∃! T : Lp ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
          Lp ℂ (ENNReal.ofReal p) (volume : Measure V),
        ∀ f : 𝓢(V, ℂ), T (f.toLp (ENNReal.ofReal p)) =ᵐ[volume] fourierMultiplier m f) ∧
    ∀ T : Lp ℂ (ENNReal.ofReal p) (volume : Measure V) →L[ℂ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure V),
      (∀ f : 𝓢(V, ℂ), T (f.toLp (ENNReal.ofReal p)) =ᵐ[volume] fourierMultiplier m f) →
        ‖T‖ₑ = multiplierNorm m p := by
  sorry

/-- **Duality** ([HNVW, Proposition 5.3.7], for scalar symbols): `‖T_m‖_p = ‖T_m‖_{p'}`,
`p' = p / (p − 1)`, for a bounded measurable symbol `m` and `1 < p < ∞`. -/
theorem multiplierNorm_conjExponent {m : V → ℂ} (hm : Measurable m)
    (hb : ∃ C : ℝ, ∀ ξ, ‖m ξ‖ ≤ C) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p = multiplierNorm m (p / (p - 1)) := by
  sorry

end Euclidean

/-- **Transference from `𝕋²` to `ℝ²`** ([HNVW, Proposition 5.7.4], for scalar symbols and `d = 2`).
Let `m` be continuous at every `ξ ≠ 0`, `1 < p < ∞`, and `ε_j → 0` with `ε_j > 0`. Then
`‖T_m‖_{L^p (ℝ²)} ≤ liminf_j ‖T_{(m (ε_j k))_{k ≠ 0}}‖_{L^p_0 (𝕋²)}`; and if this `liminf` is
finite, then `m` is bounded, so that, by `multiplierNorm_spec`, `T_m` extends to a bounded operator
on `L^p (ℝ²)`, of norm at most the `liminf`. -/
theorem transference {m : ℂ → ℂ} (hm : ∀ ξ ≠ 0, ContinuousAt m ξ) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝[>] 0)) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤
        liminf (fun j => torusMultiplierNorm (fun k => m (ε j * latticePoint k)) p) atTop ∧
      (liminf (fun j => torusMultiplierNorm (fun k => m (ε j * latticePoint k)) p) atTop ≠ ∞ →
        ∃ C : ℝ, ∀ ξ, ‖m ξ‖ ≤ C) := by
  sorry

/-- **Transference for homogeneous symbols** ([HNVW, Corollary 5.7.6], for scalar symbols and
`d = 2`: the inequality `I ≤ II` of its three norms). Let `m` be continuous at every `ξ ≠ 0` and
homogeneous of degree `0`. Then `‖T_m‖_{L^p (ℝ²)} ≤ ‖T_{(m (k))_{k ≠ 0}}‖_{L^p_0 (𝕋²)}` for
`1 < p < ∞`. -/
theorem transference_homogeneous {m : ℂ → ℂ} (hm : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hh : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ torusMultiplierNorm (fun k => m (latticePoint k)) p := by
  sorry

/-- `𝓑^k (∂̄^k F) = ∂^k F` for every Schwartz function `F` ([D, p. 465] states it for `F = f_{k,α}`,
because `f_{k,α} ∈ W^{k,p}`); and so does the `k`-fold iterate of `𝓑 = 𝓑^1`. -/
theorem beurlingPow_dzbar_iterate (k : ℕ) (F : 𝓢(ℂ, ℂ)) :
    beurlingPow k (dzbar^[k] F) = dz^[k] F ∧ (beurlingPow 1)^[k] (dzbar^[k] F) = dz^[k] F := by
  sorry

/-- `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}`, `p' = p / (p − 1)`, for `1 < p < ∞` ([CDK, §1.3.1], for the powers
`R^{2k} = 𝓑^k` of the complex Riesz transform `R`). -/
theorem beurlingPowNorm_conjExponent (k : ℕ) {p : ℝ} (hp : 1 < p) :
    beurlingPowNorm k p = beurlingPowNorm k (p / (p - 1)) := by
  sorry

/-- `κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`. -/
theorem beurlingKappa_two {p : ℝ} (hp : 0 < p) :
    beurlingKappa 2 p = (p - 1) * (2 * p - 1) / (p + 1) := by
  sorry

/-- **Dragičević's limit** ([D, Theorem 1.1], `n = 2`; there for `p > 2`):
`‖∂² f_{2,α}‖_p / ‖∂̄² f_{2,α}‖_p → κ₂ (p)` as `α → 1/p` from below, for `1 < p < ∞`. The
derivatives are pointwise; `f_{2,α}` is smooth off `0` and the unit circle, a null set. (For
`α < 1/p` they are almost everywhere the weak derivatives; this is not formalized.) -/
theorem dragicevic_limit {p : ℝ} (hp : 1 < p) :
    Tendsto (fun α : ℝ => eLpNorm (dz^[2] (testFun 2 α)) (ENNReal.ofReal p) volume /
        eLpNorm (dzbar^[2] (testFun 2 α)) (ENNReal.ofReal p) volume)
      (𝓝[<] p⁻¹) (𝓝 (ENNReal.ofReal (beurlingKappa 2 p))) := by
  sorry

/-- **Dragičević's lower bound** ([D, Theorem 1.1], `n = 2`; there for `p > 2`):
`‖𝓑²‖_{L^p (ℝ²)} ≥ κ₂ (p)` for `1 < p < ∞`. (For `p ≤ 2`, `κ₂ (p) ≤ 1`, and the bound says little;
see `dragicevic_lower_bound_pStar`.) -/
theorem dragicevic_lower_bound {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 p) ≤ beurlingPowNorm 2 p := by
  sorry

/-- The lower bound for all `1 < p < ∞`, with `p* = max (p, p')`: `‖𝓑²‖_{L^p (ℝ²)} ≥ κ₂ (p*)`, by
`dragicevic_lower_bound` and `beurlingPowNorm_conjExponent`. -/
theorem dragicevic_lower_bound_pStar {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 (pStar p)) ≤ beurlingPowNorm 2 p := by
  sorry

/-- `‖𝓑²‖_{L^p (ℝ²)} > p* − 1` for `1 < p < ∞`, `p ≠ 2`, since `κ₂ (p*) > p* − 1` for `p* > 2`. -/
theorem pStar_sub_one_lt_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    ENNReal.ofReal (pStar p - 1) < beurlingPowNorm 2 p := by
  sorry

end FourierMultipliersChallenge
