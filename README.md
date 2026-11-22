# Harmonic analysis in Lean: Fourier multipliers, transference, the Beurling–Ahlfors transform

<!-- PLACEHOLDER: CI badge, once the repository has a public URL. -->

Lean 4 with Mathlib `v4.36.0-rc2`, on `ℂ ≅ ℝ²` and the torus `𝕋² = (ℝ/ℤ)²`:

- **Fourier multipliers** `T_m f = 𝓕⁻¹(m · 𝓕f)` and their norms on `L^p`, computed on Schwartz
  functions; on the torus, on mean-zero trigonometric polynomials. Duality:
  `‖T_m‖_p = ‖T_{m̄}‖_{p'}` and `‖T_{m̄(−·)}‖_p = ‖T_m‖_p`.
- **de Leeuw's transference** from `𝕋²` to `ℝ²` for symbols homogeneous of degree `0`:
  `‖T_m‖_{L^p(ℝ²)} ≤ ‖T_m‖_{L^p_0(𝕋²)}`, through Poisson summation on `ℤ²` and lattice Riemann
  sums.
- **The Beurling–Ahlfors transform** `𝓑`, symbol `ξ̄/ξ`: `𝓑^k(∂̄^k F) = ∂^k F`,
  `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}`, transference for `𝓑^k`, and **Dragičević's lower bound** for `n = 2`,
  `‖𝓑²‖_p ≥ κ₂(p*) = (p*−1)(2p*−1)/(p*+1)`, `p* = max(p, p')`; hence `‖𝓑²‖_p > p* − 1` for
  `p ≠ 2` and `‖𝓑²‖₄ ≥ 21/5`.

**Status: statements only.** Every definition has its body; most theorems are stated with
`sorry` proofs, which the [audit](scripts/Audit.lean) lists. The corollaries that follow from the
main statements by algebra are proved. No `axiom`, no `native_decide`.

## Main statements

`p' = p/(p−1)`. The `L^p` norms are `MeasureTheory.eLpNorm` with exponent `ENNReal.ofReal p`, and
the operator norms are suprema in `ℝ≥0∞`.

| Statement | Lean | Source |
| --- | --- | --- |
| `𝓕(∂̄f)(ξ) = πiξ 𝓕f(ξ)`, `𝓕(∂f)(ξ) = πiξ̄ 𝓕f(ξ)` | `fourier_dzbarCLM`, `fourier_dzCLM` | |
| `‖T_m‖_p = ‖T_{m̄}‖_{p'}` (`m` bounded measurable, `1 < p`) | `multiplierNorm_conj_conjExponent` | [CDK, §1.3.1] |
| `‖T_{m̄(−·)}‖_p = ‖T_m‖_p` | `multiplierNorm_conj_comp_neg` | [CDK, §1.3.1] |
| `Σ_j f(R(y+j)) = Σ_n R⁻² 𝓕f(n/R) e^{2πi⟨n,y⟩}` on `ℤ²` | `hasSum_periodize` | Poisson summation |
| `Σ_n R⁻² φ(n/R) → ∫ φ` for `φ` continuous off `0`, `|φ| ≤ C(1+|ξ|)^{−3}` | `tendsto_riemannSum` | |
| `‖T_m‖_{L^p(ℝ²)} ≤ ‖T_m‖_{L^p_0(𝕋²)}`, `m` homogeneous of degree `0`, continuous off `0` | `multiplierNorm_le_torusMultiplierNorm` | [dL] |
| `𝓑^k(∂̄^k F) = ∂^k F` | `beurlingPow_dzbarCLM_pow` | [D-LN, Ex. 2.19] |
| `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}` | `beurlingPowNorm_conjExponent` | [CDK, §1.3.1] |
| `‖𝓑^k‖_{L^p(ℝ²)} ≤ ‖𝓑^k‖_{L^p_0(𝕋²)}` | `beurlingPowNorm_le_torusBeurlingPowNorm` | [dL] |
| `‖∂²F_ε‖_p / ‖∂̄²F_ε‖_p → κ₂(p)` | `tendsto_eLpNorm_div_testFunction` | [D, Thm 1.1], [D-LN, Prop. 4.2] |
| `κ₂(p) ≤ ‖𝓑²‖_p` for `1 < p` | `beurlingKappa_two_le_beurlingPowNorm_two` | [D, Thm 1.1], [D-LN, Prop. 4.2] |
| `κ₂(p*) ≤ ‖𝓑²‖_p` for `1 < p` | `beurlingKappa_two_pStar_le_beurlingPowNorm_two` | with [CDK, §1.3.1] |
| `p* − 1 < ‖𝓑²‖_p` for `p ≠ 2`; `21/5 ≤ ‖𝓑²‖₄` | `pStar_sub_one_lt_beurlingPowNorm_two`, `twentyOne_div_five_le_beurlingPowNorm_two_four` | |

All names are in the namespace `HarmonicAnalysis`. Two of them in Lean:

```lean
theorem HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm {m : ℂ → ℂ} (hm : Measurable m)
    (hmb : ∃ C, ∀ ξ, ‖m ξ‖ ≤ C) (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ torusMultiplierNorm (fun n => m (latticePoint n)) p

theorem HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 p) ≤ beurlingPowNorm 2 p
```

Here `beurlingKappa n p = (1/q)_n / (1/p)_n`, `1/q = 1 − 1/p`, with the Pochhammer symbol
`(a)_n = a(a+1)⋯(a+n−1)`; `κ₂(p) = (p−1)(2p−1)/(p+1)`.

## Method

- **Dragičević's lower bound** follows his proof [D-LN, Prop. 4.2]: the test functions
  `z² |z|^{−2α}` on the disc, the identity `𝓑²(∂̄²F) = ∂²F`, explicit radial integrals over the
  disc and a bounded contribution outside it. Departure from the source: its test functions are not
  Schwartz functions, and the norms here are suprema over Schwartz functions, so the proof uses
  `F_ε(z) = z² (|z|² + ε²)^{−1/p} σ(|z|²)` with a smooth cutoff `σ` (at the critical exponent
  `α = 1/p`, with `ε → 0` in place of `α → 1/p`). The source states the bound for `p > 2`; for
  `p < 2` it uses `‖𝓑^n‖_p = ‖𝓑^n‖_{p'}`, from `𝓑^{−n} = (𝓑^n)^*` and
  `𝓑^{−n} f = conj(𝓑^n(conj f))` [CDK, §1.3.1], as here.
- **Transference** follows de Leeuw [dL]: sample `𝓕f` on `R⁻¹ℤ²` with the mean removed; the
  periodisation and Poisson summation bound the torus norms (`limsup R^{2/p} ‖·‖_{L^p(𝕋²)} ≤ ‖f‖_p`);
  by homogeneity the multiplied series are lattice Riemann sums of `T_m f`, and Fatou's lemma
  concludes, through the extension of the torus bound to absolutely summable coefficients.

## Planned extensions

- Dragičević's bound for every `n`: `‖𝓑^n‖_p ≥ κ_n(p)` (`n = 1` is Lehto's `‖𝓑‖_p ≥ p* − 1`).
- General dimension: `EuclideanSpace ℝ (Fin d)` and `UnitAddTorus (Fin d)`.
- The reverse direction of transference (`‖T_m‖_{L^p_0(𝕋²)} ≤ ‖T_m‖_{L^p(ℝ²)}`).

## Using it from another Lake project

<!-- PLACEHOLDER: the repository URL and a published commit. -->

```toml
[[require]]
name = "HarmonicAnalysis"
git = "<repository URL>"
rev = "<commit>"
```

Then import the modules you need, for instance `public import HarmonicAnalysis.BeurlingAhlfors.LowerBound`,
or `import HarmonicAnalysis` for everything. The package requires Lean and Mathlib `v4.36.0-rc2`;
your project should use the same Mathlib version.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build
lake env lean scripts/Audit.lean   # axioms; lists the `sorry`s while proofs are open
```

## Layout

| Path | Content |
| --- | --- |
| [`HarmonicAnalysis/Complex/`](HarmonicAnalysis/Complex) | `Wirtinger` (`∂`, `∂̄` on functions and on `𝓢(ℂ, F)`, symbols, conjugation), `WirtingerRadial` (`∂`, `∂̄` of `z^a z̄^b K(|z|²)`), `RadialIntegral` (radial integrals, logarithmic averages) |
| [`HarmonicAnalysis/FourierMultiplier/`](HarmonicAnalysis/FourierMultiplier) | `Basic` (`fourierMultiplier`, `multiplierNorm`), `Duality` |
| [`HarmonicAnalysis/Torus/`](HarmonicAnalysis/Torus) | `Cube` (periodic functions, the unit cube, `𝕋² ↔ ℂ`), `TrigPoly` (trigonometric polynomials, `torusMultiplierNorm`, the `ℓ¹` extension), `Poisson` (periodisation, Poisson summation on `ℤ²`) |
| [`HarmonicAnalysis/Transference/`](HarmonicAnalysis/Transference) | `RiemannSum`, `Homogeneous` (de Leeuw) |
| [`HarmonicAnalysis/BeurlingAhlfors/`](HarmonicAnalysis/BeurlingAhlfors) | `Basic` (symbol, `𝓑^k`, `𝓑^k ∂̄^k = ∂^k`), `Duality`, `TestFunctions`, `LowerBound` (Dragičević, `n = 2`), `Transference` (`𝓑^k` on `𝕋²`) |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, line lengths |

## References

- [D] O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471, Theorem 1.1. Not consulted: its statement and proof
  are taken from [D-LN] and [CDK].
- [D-LN] O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes (Seville,
  2013), [arXiv:2109.04555](https://arxiv.org/abs/2109.04555): Proposition 4.2 (= [D, Thm 1.1]),
  Exercises 1.16 and 2.19.
- [CDK] A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex
  Riesz transform*, Math. Ann. 386 (2023), 1081–1125,
  [arXiv:2109.08369](https://arxiv.org/abs/2109.08369): §1.3.1 (duality), §2.1.
- [dL] K. de Leeuw, *On `L_p` multipliers*, Ann. of Math. 81 (1965), 364–379.

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the statements or the proofs.

## License

Apache-2.0; see [LICENSE](LICENSE).
