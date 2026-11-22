module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Basic.Real.Sign
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.UniformOn

/-!
# Challenge: Littlewood–Paley theory for functions with values in UMD spaces

For functions with values in a UMD space, the Hilbert transform on the line, the right-hand
Littlewood–Paley inequalities with random signs on the line and on the circle, Mihlin multipliers,
and the Littlewood–Paley inequalities for every choice of the signs on the line; for any complex
Banach spaces, the transference of operator-valued Fourier multipliers from the line to the circle;
after

* [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I:
  Martingales and Littlewood–Paley Theory*, Springer, 2016 (in the docstrings also HNVW I): Theorem
  5.1.13, Proposition 5.2.2, Theorem 5.3.24, Corollary 5.3.25, Proposition 5.7.1, Theorem 5.7.10;
  for Hilbert spaces, Corollary 4.5.15;
* [MC] T. R. McConnell, *On Fourier multiplier transformations of Banach-valued functions*, Trans.
  Amer. Math. Soc. 285 (1984), 739–757: Theorems 1.1 and 1.3, in dimension 1.

## Conventions

* `X`, `Y` are Banach spaces, complex except in `truncatedHilbert_bounded`; `p` is a real number,
  `1 < p < ∞`, and `eLpNorm f (ENNReal.ofReal p) μ` is `‖f‖_{L^p (μ)}`, in `[0, ∞]` (`∞` if `f` is
  not almost everywhere strongly measurable).
* `IsUMDBound X p β`: `β` is a `UMD_p` constant of `X`, for real predictable signs and probability
  spaces in the universe `Type`; `X` is a UMD space if there is a finite `β`. (The best `β` is the
  `β^ℝ_{p,X}` of [HNVW, p. 285], whose definition has deterministic signs and σ-finite measure
  spaces: predictable and deterministic signs give the same constants by [HNVW, Theorem 4.2.25], and
  the dyadic martingales on `[0, 1)` suffice by [HNVW, Corollary 4.2.6]; not formalized here.)
  Every bound below is explicit in `β` (in `mihlin_multiplier` and `littlewoodPaley_signs` up to an
  absolute constant).
* On the line, `𝓕⁻ G (x) = ∫ G (ξ) e^{2πi x ξ} dξ` (Mathlib's inverse Fourier transform). The
  functions are `f = 𝓕⁻ G ∈ L^p (ℝ; X)` with `G ∈ L¹ (ℝ; X)`, that is, `f ∈ L^p ∩ Ľ¹`, the class on
  which [HNVW, p. 401] define the boundedness of Fourier multipliers, dense in `L^p` (the density is
  not formalized); a symbol `m` acts by `T_m f = 𝓕⁻ (m G)` [HNVW, Definition 5.3.1].
* The circle is `𝕋 = ℝ / ℤ` (`UnitAddCircle`) with its Haar probability measure `haarAddCircle`,
  `fourier n` is `e_n (t) = e^{2πi n t}`, and `circPoly c = Σ_n c_n e_n` is the trigonometric
  polynomial with finitely supported coefficients `c_n ∈ X`.
* `eLpNormRad f p μ` is `‖Σ_k ε_k f_k‖_{L^p (μ × P)}`, `ε_k` independent fair real signs on the sign
  cube with its uniform probability `P` (`eLpNormRad_rpow`). [HNVW] has complex Rademacher variables
  for complex `X`.

## Statements

* `truncatedHilbert_bounded` ([HNVW, Theorem 5.1.13], for the truncations): the truncated Hilbert
  transforms `H_{ε,R} f (x) = π⁻¹ ∫_{ε < |x − y| < R} f (y) / (x − y) dy`, `R = 2^n ε`, satisfy
  `‖H_{ε,R} f‖_p ≤ (4 β² + 11) ‖f‖_p` for `f ∈ L^p (ℝ; X)`, `X` real or complex.
* `hilbert_multiplier` ([HNVW, Proposition 5.2.2]): for `f = 𝓕⁻ G`, `G ∈ L¹`, and every `x`,
  `H_{ε,R} f (x) → 𝓕⁻ (−i sgn · G) (x)` as `ε ↓ 0`, `R → ∞`: the Hilbert transform `H f` is the
  Fourier multiplier with symbol `−i sgn`.
* `hilbert_bounded` ([HNVW, Theorem 5.1.13 and Proposition 5.2.2]): `‖H f‖_p ≤ (4 β² + 11) ‖f‖_p`
  for `f ∈ L^p ∩ Ľ¹`; `hilbert_bounded_innerProductSpace` (with [HNVW, Corollary 4.5.15]): for a
  Hilbert space `X`, with `β = p* − 1`, `p* = max (p, p/(p − 1))` (M. Riesz's theorem for `X = ℂ`).
* `littlewoodPaley_line` ([HNVW, Corollary 5.3.25], right-hand inequality, finite sums): for the
  dyadic intervals `I_k`, `|k| ≤ K`, and their dilates `ρ⁻¹ I_k`,
  `‖Σ_k ε_k Δ_k f‖_{L^p (ℝ × Ω; X)} ≤ C_β ‖f‖_p`, `C_β = (144 β + 1)(4 β² + 11)`. For `ρ = 2^N` and
  `K = 2N` the intervals are `±(2^j, 2^{j+1})`, `−N ≤ j < N`, as in [HNVW, Theorem 5.3.24], and
  `(−2^{−N}, 2^{−N})`, which may be dropped (omitting terms does not increase the norm).
* `transference` ([HNVW, Proposition 5.7.1], `d = 1`, symbols continuous at the integers): a bounded
  operator-valued symbol `m` that is a Fourier multiplier from `L^p (ℝ; X)` to `L^p (ℝ; Y)` gives a
  multiplier `(m (k))_k` from `L^p (𝕋; X)` to `L^p (𝕋; Y)`, whose norm is not larger.
* `littlewoodPaley_circle` ([HNVW, Theorem 5.7.10 (2)], right-hand inequality): for the dyadic
  blocks `Ĩ_k ⊂ ℤ` and trigonometric polynomials `f`,
  `‖Σ_k ε_k Δ̃_k f‖_{L^p (𝕋 × Ω; X)} ≤ C_β ‖f‖_p` with the same `C_β`.
* `mihlin_multiplier` ([MC, Theorem 1.1], `n = 1`): if `m` is of class `C²` on `ℝ ∖ {0}` with
  `|ξ|^k |m^{(k)} (ξ)| ≤ c`, `k ≤ 2`, then `‖𝓕⁻ (m G)‖_p ≤ C c β² ‖𝓕⁻ G‖_p`, `C` absolute.
* `littlewoodPaley_signs` ([MC, Theorem 1.3], `n = 1`, the implication from UMD to (1.13)): for every
  choice of the signs `ε_j`, `ε'_j`, the multiplier `m` equal to `ε_j` on `[2^j, 2^{j+1})` and to
  `ε'_j` on `(−2^{j+1}, −2^j]` satisfies `c⁻¹ ‖f‖_p ≤ ‖T_m f‖_p ≤ c ‖f‖_p`,
  `c = C β⁸ (4 β² + 11)²`, `C` absolute.
* `eLpNormRad_rpow`: the `p`-th power of `eLpNormRad` is the average over the signs (a check).

The definitions are copied word for word from `HarmonicAnalysis/VectorValued/Defs.lean` (kept in
sync by `scripts/sync_challenge_defs.py`); the theorems are proved in
`palomar/VectorValuedLittlewoodPaley/Solution.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace HarmonicAnalysis

-- BEGIN SHARED DEFINITIONS: umd

/-- `β` is a `UMD_p` constant of the Banach space `X`: for every probability space and filtration,
every `X`-valued martingale `Y` with `Y₀ = 0` and every sequence of predictable signs
`σ_k ∈ {±1}` (`σ_{k+1}` is `ℱ_k`-measurable),
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. The probability spaces range over
`Type`. -/
protected def IsUMDBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → X) (σ : ℕ → Ω → ℝ),
    Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, σ n ω = 1 ∨ σ n ω = -1) →
      (∀ k, StronglyMeasurable[ℱ k] (σ (k + 1))) →
      ∀ n, eLpNorm (fun ω => ‖∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖)
          (ENNReal.ofReal p) μ ≤
        β * eLpNorm (fun ω => ‖Y n ω‖) (ENNReal.ofReal p) μ

-- END SHARED DEFINITIONS: umd

-- BEGIN SHARED DEFINITIONS: circle

/-- The trigonometric polynomial `Σ_n c_n e_n` on `𝕋 = ℝ / ℤ`, with coefficients in a complex vector
space. -/
noncomputable def circPoly {V : Type*} [AddCommMonoid V] [Module ℂ V] (c : ℤ →₀ V)
    (t : UnitAddCircle) : V :=
  c.sum fun n x => fourier n t • x

-- END SHARED DEFINITIONS: circle

-- BEGIN SHARED DEFINITIONS: rademacher

/-- The `L^p` norm of the Rademacher sum `Σ_k ε_k f_k` over `α × {±1}^K`, where `{±1}^K` carries the
uniform probability and `true`, `false` stand for the signs `1`, `−1`. -/
noncomputable def eLpNormRad {α : Type*} [MeasurableSpace α] {K : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Fin K → α → E) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  eLpNorm (fun z : α × (Fin K → Bool) => ∑ k, (if z.2 k then (1 : ℝ) else -1) • f k z.1)
    (ENNReal.ofReal p) (μ.prod (ProbabilityTheory.uniformOn Set.univ))

-- END SHARED DEFINITIONS: rademacher

-- BEGIN SHARED DEFINITIONS: dyadic

/-- The intervals of HNVW I, Corollary 5.3.25 (p. 419): `I_0 = (−1, 1)`, and `I_k = (2^{k−1}, 2^k)`,
`I_{−k} = (−2^k, −2^{k−1})` for `k > 0`. -/
def lineBlock (k : ℤ) : Set ℝ :=
  if k = 0 then Set.Ioo (-1) 1 else if 0 < k then Set.Ioo (2 ^ (k.natAbs - 1)) (2 ^ k.natAbs)
  else Set.Ioo (-2 ^ k.natAbs) (-2 ^ (k.natAbs - 1))

/-- The dyadic blocks of `ℤ` (HNVW I, p. 464): `Ĩ_0 = {0}`, `Ĩ_k = [2^{k−1}, 2^k)`,
`Ĩ_{−k} = (−2^k, −2^{k−1}]`, `k > 0`. -/
def dyadicBlock (k : ℤ) : Set ℤ :=
  if k = 0 then {0} else if 0 < k then Set.Ico (2 ^ (k.natAbs - 1)) (2 ^ k.natAbs)
  else Set.Ioc (-2 ^ k.natAbs) (-2 ^ (k.natAbs - 1))

open scoped Classical in
/-- `Δ̃_s f = Σ_{n ∈ s} c_n e_n`, for a set `s` of frequencies. -/
noncomputable def trigBlock {V : Type*} [AddCommMonoid V] [Module ℂ V] (s : Set ℤ) (c : ℤ →₀ V) :
    UnitAddCircle → V :=
  circPoly (c.filter (· ∈ s))

-- END SHARED DEFINITIONS: dyadic

end HarmonicAnalysis

namespace VectorValuedLittlewoodPaleyChallenge

open HarmonicAnalysis AddCircle Filter
open scoped FourierTransform SchwartzMap Topology

/-- **The truncated Hilbert transforms** are bounded on `L^p (ℝ; X)`, `X` a real or complex UMD
space: `H_{ε,R} f (x) = π⁻¹ ∫_{ε < |x − y| < R} f (y) / (x − y) dy`, for `R = 2^n ε`, uniformly in
`ε` and `n` ([HNVW, Theorem 5.1.13], where the limit `H f` is bounded, with the constant
`2 β⁺ β⁻`). -/
theorem truncatedHilbert_bounded {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : HarmonicAnalysis.IsUMDBound X p β)
    {f : ℝ → X} (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    eLpNorm (fun x => Real.pi⁻¹ • ∫ y in {y | ε < |x - y| ∧ |x - y| < 2 ^ n * ε}, (x - y)⁻¹ • f y)
        (ENNReal.ofReal p) volume ≤
      (4 * β ^ 2 + 11) * eLpNorm f (ENNReal.ofReal p) volume := by
  sorry

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **The Hilbert transform as a Fourier multiplier** ([HNVW, Proposition 5.2.2]): for `f = 𝓕⁻ G`,
`G ∈ L¹ (ℝ; X)`, `X` any complex Banach space, and every `x`, `H_{ε,R} f (x)` tends to
`𝓕⁻ (−i sgn · G) (x)` as `ε ↓ 0` and `R → ∞`. -/
theorem hilbert_multiplier {G : ℝ → X} (hG : Integrable G) (x : ℝ) :
    Tendsto (fun z : ℝ × ℝ =>
        Real.pi⁻¹ • ∫ y in {y | z.1 < |x - y| ∧ |x - y| < z.2}, (x - y)⁻¹ • 𝓕⁻ G y)
      (𝓝[>] 0 ×ˢ atTop) (𝓝 (𝓕⁻ (fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) x)) := by
  sorry

variable [CompleteSpace X]

/-- **The Hilbert transform on a UMD space** ([HNVW, Theorem 5.1.13 and Proposition 5.2.2]):
`‖H f‖_p ≤ (4 β² + 11) ‖f‖_p` for `f = 𝓕⁻ G ∈ L^p (ℝ; X)`, `G ∈ L¹`, where
`H f = 𝓕⁻ (−i sgn · G)`. -/
theorem hilbert_bounded {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞} (hβ : HarmonicAnalysis.IsUMDBound X p β)
    {G : ℝ → X} (hG : Integrable G) (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) (ENNReal.ofReal p) volume ≤
      (4 * β ^ 2 + 11) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  sorry

/-- **The Littlewood–Paley inequality on the line** ([HNVW, Corollary 5.3.25], right-hand
inequality, for finite sums): for `f = 𝓕⁻ G ∈ L^p (ℝ; X)`, `G ∈ L¹`, `ρ > 0` and
`Δ_k f = 𝓕⁻ (1_{ρ⁻¹ I_k} G)`,
`‖Σ_{|k| ≤ K} ε_k Δ_k f‖_{L^p (ℝ × Ω; X)} ≤ (144 β + 1)(4 β² + 11) ‖f‖_p`. (`ρ = 1` in [HNVW];
`ρ = 2^N` and `K = 2N` give the dyadic intervals `±(2^j, 2^{j+1})`, `−N ≤ j < N`, of [HNVW, Theorem
5.3.24], and `(−2^{−N}, 2^{−N})`.) -/
theorem littlewoodPaley_line {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : HarmonicAnalysis.IsUMDBound X p β) {G : ℝ → X} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) (K : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    eLpNormRad (fun i : Fin (2 * K + 1) =>
        𝓕⁻ ({ξ | ρ * ξ ∈ lineBlock ((i : ℕ) - K)}.indicator G)) p volume ≤
      (144 * β + 1) * (4 * β ^ 2 + 11) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  sorry

/-- **The Littlewood–Paley inequality on the circle** ([HNVW, Theorem 5.7.10 (2)], right-hand
inequality): for a trigonometric polynomial `f = Σ c_n e_n` and the blocks
`Δ̃_k f = Σ_{n ∈ Ĩ_k} c_n e_n`,
`‖Σ_{|k| ≤ K} ε_k Δ̃_k f‖_{L^p (𝕋 × Ω; X)} ≤ (144 β + 1)(4 β² + 11) ‖f‖_p`. -/
theorem littlewoodPaley_circle {p : ℝ} (hp : 1 < p) {β : ℝ≥0∞}
    (hβ : HarmonicAnalysis.IsUMDBound X p β) (c : ℤ →₀ X) (K : ℕ) :
    eLpNormRad (fun i : Fin (2 * K + 1) => trigBlock (dyadicBlock ((i : ℕ) - K)) c) p
        haarAddCircle ≤
      (144 * β + 1) * (4 * β ^ 2 + 11) *
        eLpNorm (circPoly c) (ENNReal.ofReal p) haarAddCircle := by
  sorry

/-- **Transference from `ℝ` to `𝕋`** ([HNVW, Proposition 5.7.1], `d = 1`; there the integers are
Lebesgue points of `m (·) x`): let `m : ℝ → 𝓛 (X, Y)` be bounded, `m (·) x` a.e. strongly
measurable and continuous at the integers for every `x`, and
`‖𝓕⁻ (m G)‖_{L^p (ℝ; Y)} ≤ C ‖𝓕⁻ G‖_{L^p (ℝ; X)}` for Schwartz functions `G`. Then
`‖Σ m (k) a_k e_k‖_{L^p (𝕋; Y)} ≤ C ‖Σ a_k e_k‖_{L^p (𝕋; X)}`. -/
theorem transference {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] {p : ℝ}
    (hp : 1 < p) {m : ℝ → X →L[ℂ] Y} (hb : ∃ M : ℝ, ∀ ξ, ‖m ξ‖ ≤ M)
    (hm : ∀ x, AEStronglyMeasurable (fun ξ => m ξ x) volume)
    (hc : ∀ (k : ℤ) (x : X), ContinuousAt (fun ξ => m ξ x) k) {C : ℝ≥0∞}
    (hC : ∀ G : 𝓢(ℝ, X), eLpNorm (𝓕⁻ fun ξ => m ξ (G ξ)) (ENNReal.ofReal p) volume ≤
      C * eLpNorm (𝓕⁻ (G : ℝ → X)) (ENNReal.ofReal p) volume) (a : ℤ →₀ X) :
    eLpNorm (fun t : UnitAddCircle => a.sum fun k x => fourier k t • m k x) (ENNReal.ofReal p)
        haarAddCircle ≤
      C * eLpNorm (circPoly a) (ENNReal.ofReal p) haarAddCircle := by
  sorry

end

/-- **Hilbert spaces** (M. Riesz's theorem for `H = ℂ`): `hilbert_bounded` with `β = p* − 1`, the
`UMD_p` constant of a Hilbert space `H ≠ 0` ([HNVW, Corollary 4.5.15]), where
`p* = max (p, p / (p − 1))`. -/
theorem hilbert_bounded_innerProductSpace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {p : ℝ} (hp : 1 < p) {G : ℝ → H} (hG : Integrable G)
    (hf : MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume) :
    eLpNorm (𝓕⁻ fun ξ => (-Complex.I * (Real.sign ξ : ℂ)) • G ξ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (4 * (max p (p / (p - 1)) - 1) ^ 2 + 11) *
        eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  sorry

/-- **Mihlin's multiplier theorem on UMD spaces** ([MC, Theorem 1.1], `n = 1`): let `m` be of class
`C²` on `ℝ ∖ {0}` with `|ξ|^k |m^{(k)} (ξ)| ≤ c` for `k ≤ 2` and `ξ ≠ 0`. Then
`‖𝓕⁻ (m G)‖_p ≤ C c β² ‖𝓕⁻ G‖_p` for `G ∈ L¹ (ℝ; X)`, with an absolute constant `C`. ([MC]: `m` real
and `C²` on `ℝ`; the constant depends on `c`, `p` and `X`.) -/
theorem mihlin_multiplier : ∃ C : NNReal, ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (p : ℝ), 1 < p → ∀ β : ℝ≥0∞, HarmonicAnalysis.IsUMDBound X p β →
    ∀ (m : ℝ → ℂ) (c : ℝ), ContDiffOn ℝ 2 m {0}ᶜ →
    (∀ k ≤ 2, ∀ ξ ≠ 0, |ξ| ^ k * ‖iteratedDeriv k m ξ‖ ≤ c) → ∀ G : ℝ → X, Integrable G →
      eLpNorm (𝓕⁻ fun ξ => m ξ • G ξ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal c * (C * β ^ 2) * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume := by
  sorry

/-- **Littlewood–Paley inequalities for every choice of the signs** ([MC, Theorem 1.3], `n = 1`, for
UMD spaces both inequalities of (1.13)): if `m` is equal to a sign `ε_j` on `[2^j, 2^{j+1})` and to
a sign
`ε'_j` on `(−2^{j+1}, −2^j]`, for every `j ∈ ℤ`, then `c⁻¹ ‖f‖_p ≤ ‖T_m f‖_p ≤ c ‖f‖_p`,
`c = C β⁸ (4 β² + 11)²`, for `f = 𝓕⁻ G ∈ L^p (ℝ; X)`, `G ∈ L¹`, with an absolute constant `C`. -/
theorem littlewoodPaley_signs : ∃ C : NNReal, ∀ (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p → ∀ β : ℝ≥0∞,
    HarmonicAnalysis.IsUMDBound X p β → ∀ ε ε' : ℤ → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) →
    (∀ j, ε' j = 1 ∨ ε' j = -1) → ∀ m : ℝ → ℝ,
    (∀ j : ℤ, ∀ ξ ∈ Set.Ico ((2 : ℝ) ^ j) (2 ^ (j + 1)), m ξ = ε j) →
    (∀ j : ℤ, ∀ ξ ∈ Set.Ioc (-(2 : ℝ) ^ (j + 1)) (-2 ^ j), m ξ = ε' j) →
    ∀ G : ℝ → X, Integrable G → MemLp (𝓕⁻ G) (ENNReal.ofReal p) volume →
      eLpNorm (𝓕⁻ fun ξ => (m ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * (4 * β ^ 2 + 11) ^ 2 * eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ∧
      eLpNorm (𝓕⁻ G) (ENNReal.ofReal p) volume ≤
        C * β ^ 8 * (4 * β ^ 2 + 11) ^ 2 *
          eLpNorm (𝓕⁻ fun ξ => (m ξ : ℂ) • G ξ) (ENNReal.ofReal p) volume := by
  sorry

/-- The `p`-th power of `eLpNormRad` is the average over the signs (a check of the definition). -/
theorem eLpNormRad_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p) {K : ℕ} {f : Fin K → α → E}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) :
    eLpNormRad f p μ ^ p = ((2 : ℝ≥0∞) ^ K)⁻¹ * ∑ ε : Fin K → Bool,
      eLpNorm (fun x => ∑ k, (if ε k then (1 : ℝ) else -1) • f k x) (ENNReal.ofReal p) μ ^ p := by
  sorry

end VectorValuedLittlewoodPaleyChallenge
