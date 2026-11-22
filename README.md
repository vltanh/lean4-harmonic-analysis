# Harmonic analysis in Lean: Fourier multipliers, transference, the Beurling–Ahlfors transform

[![Lean Action CI](https://github.com/vltanh/lean4-harmonic-analysis/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-harmonic-analysis/actions/workflows/lean_action_ci.yml)

Lean 4 with Mathlib `v4.36.0-rc2`, on `ℂ ≅ ℝ²`, the torus `𝕋² = (ℝ/ℤ)²` and the tori `𝕋^ι`:

- **Fourier multipliers** `T_m f = 𝓕⁻¹(m · 𝓕f)` and their norms on `L^p`, computed on Schwartz
  functions, which also bound `T_m` on the `L^p`-closure of its graph (density); on the torus, on
  mean-zero trigonometric polynomials. Duality for bounded measurable `m`:
  `‖T_m‖_p = ‖T_{m̄}‖_{p'}` and `‖T_{m̄(−·)}‖_p = ‖T_m‖_p`.
- **de Leeuw's transference** from `𝕋²` to `ℝ²` for symbols homogeneous of degree `0`:
  `‖T_m‖_{L^p(ℝ²)} ≤ ‖T_m‖_{L^p_0(𝕋²)}`, through Poisson summation on `ℤ²` and lattice Riemann
  sums.
- **The Beurling–Ahlfors transform** `𝓑`, symbol `ξ̄/ξ`: `𝓑^k(∂̄^k F) = ∂^k F`,
  `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}`, transference for `𝓑^k`, and **Dragičević's lower bound** for `n = 2`,
  `‖𝓑²‖_p ≥ κ₂(p*) = (p*−1)(2p*−1)/(p*+1)`, `p* = max(p, p')`; hence `‖𝓑²‖_p > p* − 1` for
  `p ≠ 2` and `‖𝓑²‖₄ ≥ 21/5`.
- **Smooth periodic functions** on `ℝ^ι`, `ι` finite: the derivative formula
  `(∂_v g)^(n) = 2πi⟨n,v⟩ ĝ(n)`, rapid decay of the Fourier coefficients and absolute convergence
  of the Fourier series; Fourier multipliers `T_m g = Σ_n m(n) ĝ(n) e_n` with polynomially bounded
  symbols, which preserve smooth periodic functions; on `ℝ² ≅ ℂ`, the inverse of `∂̄` on mean-zero
  smooth periodic functions and `𝓑(∂̄g) = ∂g` for smooth periodic `g`.

**Status: complete.** Every statement is proved. The [audit](scripts/Audit.lean) checks that every
declaration of the library depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`): no `sorry`, no `axiom`, no `native_decide`.

## Main statements

`p' = p/(p−1)`. The `L^p` norms are `MeasureTheory.eLpNorm` with exponent `ENNReal.ofReal p`, and
the operator norms are suprema in `ℝ≥0∞`.

| Statement | Lean | Source |
| --- | --- | --- |
| `𝓕(∂̄f)(ξ) = πiξ 𝓕f(ξ)`, `𝓕(∂f)(ξ) = πiξ̄ 𝓕f(ξ)` | `fourier_dzbarCLM`, `fourier_dzCLM` | |
| `‖v‖_p / ‖u‖_p ≤ ‖T_m‖_p` if Schwartz `φ_k → u`, `T_m φ_k → v` in `L^p` | `div_le_multiplierNorm_of_tendsto` | density |
| `∫ T_m f · ḡ = ∫ f · conj(T_{m̄} g)` for Schwartz `f, g` (`m` bounded measurable) | `integral_fourierMultiplier_mul_conj` | |
| `‖h‖_p ≤ A` if `\|∫ h ḡ\| ≤ A ‖g‖_{p'}` for all Schwartz `g` (`h` continuous, `1 < p`) | `eLpNorm_le_of_forall_schwartz` | duality |
| `‖T_m‖_p = ‖T_{m̄}‖_{p'}` (`m` bounded measurable, `1 < p`) | `multiplierNorm_conj_conjExponent` | duality; [CDK, §1.3.1] for `R^k` |
| `‖T_{m̄(−·)}‖_p = ‖T_m‖_p` | `multiplierNorm_conj_comp_neg` | conjugation; [CDK, §1.3.1] for `R^k` |
| `Σ_j f(R(y+j)) = Σ_n R⁻² 𝓕f(n/R) e^{2πi⟨n,y⟩}` on `ℤ²` | `hasSum_periodize` | Poisson summation |
| `Σ_n R⁻² φ(n/R) → ∫ φ` for `φ` continuous off `0`, `\|φ\| ≤ C(1+\|ξ\|)^{−3}` | `tendsto_riemannSum` | |
| `‖T_m‖_{L^p(ℝ²)} ≤ ‖T_m‖_{L^p_0(𝕋²)}`, `m` homogeneous of degree `0`, continuous off `0` | `multiplierNorm_le_torusMultiplierNorm` | [dL] |
| `𝓑^k(∂̄^k F) = ∂^k F` for Schwartz `F` | `beurlingPow_dzbarCLM_pow` | [D-LN, Ex. 2.19] for `k = 1`; §4.1 |
| `‖v‖_p / ‖u‖_p ≤ ‖𝓑^k‖_p` if Schwartz `∂̄^k φ_j → u`, `∂^k φ_j → v` in `L^p` | `div_le_beurlingPowNorm_of_tendsto` | density; [D-LN, Ex. 2.19, §4.1] |
| `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}` | `beurlingPowNorm_conjExponent` | [CDK, §1.3.1] |
| `‖𝓑^k‖_{L^p(ℝ²)} ≤ ‖𝓑^k‖_{L^p_0(𝕋²)}` | `beurlingPowNorm_le_torusBeurlingPowNorm` | [dL] |
| `f_{2,α} ∈ W^{2,p}`: Schwartz `φ_k` with `∂̄²φ_k → ∂̄²f_{2,α}`, `∂²φ_k → ∂²f_{2,α}` (`1 ≤ p`) | `BeurlingAhlfors.exists_schwartz_tendsto_testFun` | [D-LN, Ex. 4.1] (for `p > 2`) |
| `‖∂²f_{2,α}‖_p / ‖∂̄²f_{2,α}‖_p → κ₂(p)` as `α → 1/p⁻` | `tendsto_eLpNorm_div_testFun` | [D, Thm 1.1], [D-LN, Prop. 4.2] |
| `κ₂(p) ≤ ‖𝓑²‖_p` for `1 < p` | `beurlingKappa_two_le_beurlingPowNorm_two` | [D, Thm 1.1], [D-LN, Prop. 4.2] |
| `κ₂(p*) ≤ ‖𝓑²‖_p` for `1 < p` | `beurlingKappa_two_pStar_le_beurlingPowNorm_two` | [D-LN, Prop. 4.2]; [CDK, §1.3.1] |
| `p* − 1 < ‖𝓑²‖_p` for `p ≠ 2`; `21/5 ≤ ‖𝓑²‖₄` | `pStar_sub_one_lt_beurlingPowNorm_two`, `twentyOne_div_five_le_beurlingPowNorm_two_four` | |
| `(∂_v g)^(n) = 2πi⟨n,v⟩ ĝ(n)` for Lipschitz, or `C¹`, `ℤ^ι`-periodic `g` | `UnitAddTorus.cubeFourierCoeff_fderiv_of_lipschitzWith`, `UnitAddTorus.cubeFourierCoeff_fderiv_of_contDiff` | difference quotients; [G, Ch. 3] |
| `Σ_n (1 + ‖n‖)^k \|ĝ(n)\| < ∞` for smooth periodic `g` and every `k` | `UnitAddTorus.exists_norm_cubeFourierCoeff_le`, `UnitAddTorus.summable_cubeFourierCoeff` | integration by parts; [G, Ch. 3] |
| `g(x) = Σ_n ĝ(n) e^{2πi⟨n,x⟩}` absolutely, for smooth periodic `g`; uniqueness | `UnitAddTorus.hasSum_cubeFourierCoeff_mul_mFourier`, `UnitAddTorus.eq_of_cubeFourierCoeff_eq` | [G, Ch. 3], [K, Ch. I] |
| `T_m g` is smooth and periodic, with coefficients `m ĝ` (`\|m(n)\| ≤ C(1 + ‖n‖)^k`) | `UnitAddTorus.contDiff_periodicMultiplier`, `UnitAddTorus.cubeFourierCoeff_periodicMultiplier` | Weierstrass M-test |
| `h = ∂̄u`, `u` smooth periodic of mean zero, for smooth `ℤ²`-periodic `h` of mean zero | `UnitAddTorus.exists_dzbarPi_eq` | the symbol `(πiν)⁻¹` |
| `𝓑(∂̄g) = ∂g` for smooth `ℤ²`-periodic `g` | `periodicMultiplier_beurlingSymbol_dzbarPi` | comparison of coefficients |

All names are in the namespace `HarmonicAnalysis`, except those prefixed by `UnitAddTorus`. Two of
them in Lean:

```lean
theorem HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm {m : ℂ → ℂ}
    (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ) (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ torusMultiplierNorm (fun n => m (latticePoint n)) p

theorem HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 p) ≤ beurlingPowNorm 2 p
```

Here `beurlingKappa n p = (1/q)_n / (1/p)_n`, `1/q = 1 − 1/p`, with the Pochhammer symbol
`(a)_n = a(a+1)⋯(a+n−1)`; `κ₂(p) = (p−1)(2p−1)/(p+1)`.

## Method

- **Dragičević's lower bound** follows his proof [D-LN, Prop. 4.2], with his test functions
  `f_{2,α}(z) = z² |z|^{−2α} g₂(|z|)`, `g₂ = 1` on `[0, 1]`, `g₂(x) = exp(−(x−1)²)` for `x > 1`,
  `0 < α < 1/p`: `𝓑²(∂̄²f) = ∂²f` [D-LN, §4.1], explicit integrals over the disc, of order
  `(1 − αp)⁻¹`, a
  bounded contribution outside it, and `α → 1/p`. The norms here are suprema over Schwartz
  functions, which `f_{2,α}` is not; `f_{2,α} ∈ W^{2,p}` [D-LN, Ex. 4.1] is approximated by
  Schwartz functions, and the density statements carry the bound over, as the hint of
  [D-LN, Ex. 2.19] does ("first consider smooth `h` and then approximate"). The approximation
  is the standard one: `z²(|z|² + ε)^{−α}` near `0`, the cutoff smoothed near `|z| = 1` (where
  `g₂` is only `C¹`) and truncated at infinity, and dominated convergence. The source states the
  bound for `p > 2` (and its asymptotic form with `p*` for all `p` [D-LN, Cor. 4.8]); the case
  `p < 2` comes from `‖𝓑^n‖_p = ‖𝓑^n‖_{p'}`, by `𝓑^{−n} = (𝓑^n)^*` and `𝓑^{−n} f = conj(𝓑^n(conj f))`
  [CDK, §1.3.1, for `R^k`, `𝓑 = R²`], as here (for bounded multipliers, by the standard duality
  argument: the adjoint of `T_m` is `T_{m̄}`, and Schwartz functions norm `L^p`).
- **Transference**, by the standard argument for this direction of de Leeuw's theorem [dL]: sample `𝓕f` on `R⁻¹ℤ²` with the mean removed; the
  periodisation and Poisson summation bound the torus norms (`limsup R^{2/p} ‖·‖_{L^p(𝕋²)} ≤ ‖f‖_p`);
  by homogeneity the multiplied series are lattice Riemann sums of `T_m f`, and Fatou's lemma
  concludes, through the extension of the torus bound to absolutely summable coefficients.

- **Smooth periodic functions.** The Fourier coefficients over the unit cube `(0,1)^ι` are those
  of the function induced on the torus. The derivative formula integrates the difference quotients
  against `e_{−n}`, moves the translation onto `e_{−n}` by translation invariance, and passes to
  the limit by dominated convergence; iterated along a coordinate it bounds `|n_i|^k |ĝ(n)|` by the
  supremum of `∂_i^k g`, and the comparison `(1 + ‖n‖)^{−2 card ι} ≤ Π_i (1 + |n_i|)^{−2}` gives
  the summability. Mathlib's `hasSum_mFourier_series_apply_of_summable` gives the Fourier series
  and the uniqueness of the coefficients. `T_m g` is smooth by `contDiff_tsum`, with
  `‖D^j e_n‖ ≤ (2π card ι (1 + ‖n‖))^j`; its coefficients come from termwise integration, and the
  identities (`T_m T_{m'} = T_{mm'}`, `T_m ∂_v`, `∂̄ T_{(πiν)⁻¹} h = h`, `𝓑(∂̄g) = ∂g`) from
  comparing coefficients.

## Planned extensions

- Dragičević's bound for every `n`: `‖𝓑^n‖_p ≥ κ_n(p)` (`n = 1` is Lehto's `‖𝓑‖_p ≥ p* − 1`).
- General dimension: `EuclideanSpace ℝ (Fin d)` and `UnitAddTorus (Fin d)`.
- The reverse direction of transference (`‖T_m‖_{L^p_0(𝕋²)} ≤ ‖T_m‖_{L^p(ℝ²)}`).

## Using it from another Lake project

```toml
[[require]]
name = "HarmonicAnalysis"
git = "https://github.com/vltanh/lean4-harmonic-analysis"
rev = "<commit>"
```

Then import the modules you need, for instance `public import HarmonicAnalysis.BeurlingAhlfors.LowerBound`,
or `import HarmonicAnalysis` for everything. The package requires Lean and Mathlib `v4.36.0-rc2`;
your project should use the same Mathlib version.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build
lake env lean scripts/Audit.lean   # axioms: fails on any `sorry` or non-standard axiom
```

## Layout

| Path | Content |
| --- | --- |
| [`HarmonicAnalysis/Complex/`](HarmonicAnalysis/Complex) | `Wirtinger` (`∂`, `∂̄` on functions and on `𝓢(ℂ, F)`, symbols, conjugation), `WirtingerRadial` (`∂`, `∂̄` of `z^a z̄^b K(\|z\|²)`), `RadialIntegral` (radial integrals) |
| [`HarmonicAnalysis/FourierMultiplier/`](HarmonicAnalysis/FourierMultiplier) | `Basic` (`fourierMultiplier`, `multiplierNorm`, density), `Norming` (`L^p` norms by Schwartz test functions), `Duality` |
| [`HarmonicAnalysis/Torus/`](HarmonicAnalysis/Torus) | `Cube` (periodic functions, the unit cube, `𝕋² ↔ ℂ`), `Lattice` (the lattice `ℤ + iℤ`, the tiling of `ℂ` by cells, periodic functions on `𝕋²`), `TrigPoly` (trigonometric polynomials, `torusMultiplierNorm`, the `ℓ¹` extension), `Poisson` (periodisation, Poisson summation on `ℤ²`), `Lipschitz` (Fourier coefficients over the unit cube, Parseval, derivatives of Lipschitz periodic functions), `Smooth` (smooth periodic functions: rapid decay, Fourier series, multipliers `T_m`, Wirtinger derivatives, `∂̄⁻¹`) |
| [`HarmonicAnalysis/Transference/`](HarmonicAnalysis/Transference) | `RiemannSum`, `Homogeneous` (de Leeuw) |
| [`HarmonicAnalysis/BeurlingAhlfors/`](HarmonicAnalysis/BeurlingAhlfors) | `Basic` (symbol, `𝓑^k`, `𝓑^k ∂̄^k = ∂^k`, density), `Duality`, `TestFunctions` (Dragičević's `f_{2,α}`; with `TestFunctions/Profile`, one-variable calculus, and `TestFunctions/Approx`, its Schwartz approximations), `LowerBound` (Dragičević, `n = 2`), `Transference` (`𝓑^k` on `𝕋²`), `Periodic` (`𝓑` on smooth periodic functions) |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, line lengths |

## References

- [D] O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471, Theorem 1.1. Not consulted: its statement and proof
  are taken from [D-LN] and [CDK].
- [D-LN] O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes (Seville,
  2013), [arXiv:2109.04555](https://arxiv.org/abs/2109.04555): §4.1, Proposition 4.2
  (= [D, Thm 1.1]), Corollary 4.8, Exercises 1.16, 2.19 and 4.1.
- [CDK] A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex
  Riesz transform*, Math. Ann. 386 (2023), 1081–1125,
  [arXiv:2109.08369](https://arxiv.org/abs/2109.08369): §1.3.1 (duality), §2.1.
- [dL] K. de Leeuw, *On `L_p` multipliers*, Ann. of Math. 81 (1965), 364–379. Not consulted: the
  proof is the standard argument for this direction of transference, described in
  [`Transference/Homogeneous.lean`](HarmonicAnalysis/Transference/Homogeneous.lean).

- [G] L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Graduate Texts in Mathematics 249,
  Springer, 2014: Chapter 3 (Fourier series on `𝕋^n`). Not consulted: the arguments for smooth
  periodic functions (decay of the coefficients, absolute convergence and uniqueness of the Fourier
  series) are the standard ones.
- [K] Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press,
  2004: Chapter I (Fourier series on `𝕋`). Not consulted, as for [G].

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
