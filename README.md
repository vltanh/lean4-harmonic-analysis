# Harmonic analysis in Lean: Fourier multipliers, transference, the Beurling–Ahlfors transform

[![Lean Action CI](https://github.com/vltanh/lean4-harmonic-analysis/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-harmonic-analysis/actions/workflows/lean_action_ci.yml)

Lean 4 with Mathlib `v4.36.0-rc2`, on `ℂ ≅ ℝ²`, the torus `𝕋² = (ℝ/ℤ)²` and the tori `𝕋^ι`:

- **Fourier multipliers** `T_m f = 𝓕⁻¹(m · 𝓕f)` and their norms on `L^p`, computed on Schwartz
  functions, which also bound `T_m` on the `L^p`-closure of its graph (density); on the torus, on
  mean-zero trigonometric polynomials. For bounded measurable `m`, the norm is that of the bounded
  extension of `T_m` to `L^p` (`1 ≤ p < ∞`), and there is duality (`1 < p < ∞`):
  `‖T_m‖_p = ‖T_m‖_{p'}`, `‖T_m‖_p = ‖T_{m̄}‖_{p'}`; also `‖T_{m̄(−·)}‖_p = ‖T_{m(−·)}‖_p = ‖T_m‖_p`.
- **Transference from `𝕋²` to `ℝ²`** [HNVW, Prop. 5.7.4, Cor. 5.7.6], `1 < p < ∞`: for `m` continuous
  off `0` and `R_j → ∞`, `‖T_m‖_{L^p(ℝ²)} ≤ liminf_j ‖T_{m(·/R_j)}‖_{L^p_0(𝕋²)}`; if `m` is moreover
  homogeneous of degree `0`, `‖T_m‖_{L^p(ℝ²)} ≤ ‖T_m‖_{L^p_0(𝕋²)}`. Through the density of the Schwartz
  functions with Fourier transform in `C_c^∞(ℝ^d∖{0})`, Poisson summation on `ℤ²` and lattice Riemann
  sums.
- **The Beurling–Ahlfors transform** `𝓑`, symbol `ξ̄/ξ`: `𝓑^k(∂̄^k F) = ∂^k F`,
  `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}`, transference for `𝓑^k`, and **Dragičević's lower bound** for `n = 2`,
  `‖𝓑²‖_p ≥ κ₂(p) = (p−1)(2p−1)/(p+1)`; with the duality of Carbonaro, Dragičević and Kovač for
  `p < 2`, `‖𝓑²‖_p ≥ κ₂(p*)`, `p* = max(p, p')`, hence `‖𝓑²‖_p > p* − 1` for `p ≠ 2`, and
  `‖𝓑²‖₄ ≥ 21/5`.
- **Smooth periodic functions** on `ℝ^ι`, `ι` finite: the derivative formula
  `(∂_v g)^(n) = 2πi⟨n,v⟩ ĝ(n)`, rapid decay of the Fourier coefficients and absolute convergence
  of the Fourier series; Fourier multipliers `T_m g = Σ_n m(n) ĝ(n) e_n` with polynomially bounded
  symbols, which preserve smooth periodic functions; on `ℝ² ≅ ℂ`, the inverse of `∂̄` on mean-zero
  smooth periodic functions and `𝓑(∂̄g) = ∂g` for smooth periodic `g`.

**Status: complete.** Every statement is proved. The [audit](scripts/Audit.lean) checks that every
declaration of the library depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`): no `sorry`, no `axiom`, no `native_decide`. (The Challenge of the
[Palomar entry](#palomar) states its theorems with `sorry`, by design; its Solution proves them.)

## Main statements

`p' = p/(p−1)`. The `L^p` norms are `MeasureTheory.eLpNorm` with exponent `ENNReal.ofReal p`, and
the operator norms are suprema in `ℝ≥0∞`.

| Statement | Lean | Source |
| --- | --- | --- |
| `𝓕(∂̄f)(ξ) = πiξ 𝓕f(ξ)`, `𝓕(∂f)(ξ) = πiξ̄ 𝓕f(ξ)` | `fourier_dzbarCLM`, `fourier_dzCLM` | |
| `‖v‖_p / ‖u‖_p ≤ ‖T_m‖_p` if Schwartz `φ_k → u`, `T_m φ_k → v` in `L^p` | `div_le_multiplierNorm_of_tendsto` | density |
| `‖T_m‖_p < ∞` iff `T_m` extends from Schwartz functions to a bounded operator on `L^p`, which is then unique, of norm `‖T_m‖_p` (`m` bounded measurable, `1 ≤ p`) | `existsUnique_extension_of_multiplierNorm_ne_top`, `enorm_eq_multiplierNorm` | density |
| `‖T_m‖_p = ‖T_m‖_{p'}` (`m` bounded measurable, `1 < p`) | `multiplierNorm_conjExponent` | [HNVW, Prop. 5.3.7] |
| `‖T_{m(−·)}‖_p = ‖T_m‖_p` | `multiplierNorm_comp_neg` | reflection; [HNVW, p. 403] |
| `∫ T_m f · ḡ = ∫ f · conj(T_{m̄} g)` for Schwartz `f, g` (`m` bounded measurable) | `integral_fourierMultiplier_mul_conj` | |
| `‖h‖_p ≤ A` if `\|∫ h ḡ\| ≤ A ‖g‖_{p'}` for all Schwartz `g` (`h` continuous, `1 < p`) | `eLpNorm_le_of_forall_schwartz` | duality |
| `‖T_m‖_p = ‖T_{m̄}‖_{p'}` (`m` bounded measurable, `1 < p`) | `multiplierNorm_conj_conjExponent` | duality; [CDK, §1.3.1] for `R^k` |
| `‖T_{m̄(−·)}‖_p = ‖T_m‖_p` | `multiplierNorm_conj_comp_neg` | conjugation; [CDK, §1.3.1] for `R^k` |
| `ϕ_t ∗ f → f` in `L^p` as `t → 0` for Schwartz `f`, `ϕ`, `∫ϕ = 1` (`1 ≤ p`) | `tendsto_eLpNorm_mollify_sub` | [HNVW, Prop. 1.2.32] |
| For Schwartz `f`, `dim V > 0`: Schwartz `f_j → f` in every `L^p`, `1 < p < ∞`, `𝓕f_j → 𝓕f` in `L¹`, with `𝓕f_j ∈ C_c^∞(V∖{0})` | `exists_tendsto_hasCompactFourierSupportOffZero` | [HNVW, Prop. 2.4.23 (ii)] |
| `∫_{𝕋^ι} T_m(Σ c_k e_k) (Σ d_ℓ e_ℓ) = Σ_k m(k) c_k d_{−k}` | `integral_torusMultiplier_mul_trigPoly` | orthogonality |
| `Σ_j f(R(y+j)) = Σ_n R⁻² 𝓕f(n/R) e^{2πi⟨n,y⟩}` on `ℤ²`, for Schwartz `f` | `hasSum_periodize` | Poisson summation |
| `R^{2/p} ‖Σ_n R⁻² 𝓕f(n/R) e_n‖_{L^p(𝕋²)} → ‖f‖_{L^p(ℝ²)}` as `R → ∞`, for Schwartz `f` (`1 ≤ p`) | `tendsto_eLpNorm_tsum_fourier_mul_mFourier` | [HNVW, Lemma 5.7.5] |
| `Σ_n R⁻² φ(n/R) → ∫ φ` for `φ` continuous off `0`, `\|φ\| ≤ C(1+\|ξ\|)^{−3}` | `tendsto_riemannSum_real` | |
| `‖T_m‖_{L^p(ℝ²)} ≤ liminf_j ‖T_{m(·/R_j)}‖_{L^p_0(𝕋²)}`, `R_j → ∞`, `m` continuous off `0` (`1 < p`) | `multiplierNorm_le_liminf_torusMultiplierNorm` | [HNVW, Prop. 5.7.4] |
| `m` is bounded if that `liminf` is finite | `exists_norm_le_of_liminf_torusMultiplierNorm_ne_top` | |
| `‖T_m‖_{L^p(ℝ²)} ≤ ‖T_m‖_{L^p_0(𝕋²)}`, `m` homogeneous of degree `0`, continuous off `0` (`1 < p`) | `multiplierNorm_le_torusMultiplierNorm` | [HNVW, Cor. 5.7.6] (`I ≤ II`) |
| `𝓑^k(∂̄^k F) = ∂^k F` for Schwartz `F`; the same for the `k`-fold iterate of `𝓑` | `beurlingPow_dzbarCLM_pow`, `beurlingPow_dzbar_iterate`, `iterate_beurlingPow_one_dzbar_iterate` | [D, p. 465]; [D-LN, §4.1, and Ex. 2.19 for `k = 1`] |
| `‖v‖_p / ‖u‖_p ≤ ‖𝓑^k‖_p` if Schwartz `∂̄^k φ_j → u`, `∂^k φ_j → v` in `L^p` | `div_le_beurlingPowNorm_of_tendsto` | density; [D, p. 465]; [D-LN, Ex. 2.19, §4.1] |
| `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}` (`1 < p`) | `beurlingPowNorm_conjExponent` | [CDK, §1.3.1] |
| `‖𝓑^k‖_{L^p(ℝ²)} ≤ ‖𝓑^k‖_{L^p_0(𝕋²)}` (`1 < p`) | `beurlingPowNorm_le_torusBeurlingPowNorm` | [HNVW, Cor. 5.7.6] (`I ≤ II`) |
| `f_{2,α}`, what is used of `f_{2,α} ∈ W^{2,p}`: Schwartz `φ_k` with `∂̄²φ_k → ∂̄²f_{2,α}`, `∂²φ_k → ∂²f_{2,α}` in `L^p` (`1 ≤ p`, `0 < α < 1/p`) | `BeurlingAhlfors.exists_schwartz_tendsto_testFun` | asserted in [D, p. 465], [D-LN, Ex. 4.1] (for `p > 2`) |
| `‖∂²f_{2,α}‖_p / ‖∂̄²f_{2,α}‖_p → κ₂(p)` as `α → 1/p⁻` | `tendsto_eLpNorm_div_testFun` | [D, Thm 1.1] (for `p > 2`) |
| `κ₂(p) ≤ ‖𝓑²‖_p` for `1 < p` | `beurlingKappa_two_le_beurlingPowNorm_two` | [D, Thm 1.1] (for `p > 2`) |
| `κ₂(p*) ≤ ‖𝓑²‖_p` for `1 < p` | `beurlingKappa_two_pStar_le_beurlingPowNorm_two` | [D, Thm 1.1] for `p > 2`; [CDK, §1.3.1] for `p < 2` |
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

## Palomar

The entry [`palomar/FourierMultipliers/`](palomar/FourierMultipliers) states the headline theorems for
the [Palomar registry](https://palomar-registry.org). It is not submitted yet.

| File | Content |
| --- | --- |
| [`Challenge.lean`](palomar/FourierMultipliers/Challenge.lean) | the statements, with `sorry` proofs, and the definitions they use, from Mathlib alone (the definitions are a copy of [`HarmonicAnalysis/Defs.lean`](HarmonicAnalysis/Defs.lean)) |
| [`Solution.lean`](palomar/FourierMultipliers/Solution.lean) | the same statements, proved from the library |
| [`comparator.json`](palomar/FourierMultipliers/comparator.json) | Comparator's configuration: the 11 theorems compared |
| [`formalization.yaml`](palomar/FourierMultipliers/formalization.yaml) | the metadata: sources, scope, every deviation from the sources |

The compared theorems are: what the norm `‖T_m‖_p` is (`multiplierNorm_spec`); `‖T_m‖_p = ‖T_m‖_{p'}`;
transference, for symbols continuous off `0` and for homogeneous ones; `𝓑^k(∂̄^k F) = ∂^k F`, also
for the `k`-fold iterate of `𝓑`;
`‖𝓑^k‖_p = ‖𝓑^k‖_{p'}`; the closed form of `κ₂(p)`; Dragičević's limit and lower bound for `n = 2`; the
bound with `p*`, and `‖𝓑²‖_p > p* − 1`.

## Method

- **Dragičević's lower bound** follows his proof [D, pp. 466–467], which [D-LN, Prop. 4.2] repeats,
  with his test functions `f_{2,α}(z) = z² |z|^{−2α} g₂(|z|)` (here `0 < α < 1/p`, and his example of a
  cutoff, `g₂ = 1` on `[0, 1]`, `g₂(x) = exp(−(x−1)²)` for `x > 1`): `𝓑²(∂̄²f) = ∂²f`, explicit
  integrals over the disc, of order `(1 − αp)⁻¹`, a bounded contribution outside it, and `α → 1/p`. The
  norms here are suprema over Schwartz functions, which `f_{2,α}` is not; that `f_{2,α} ∈ W^{2,p}`, "which ensures
  that `T^n(∂̄^n f) = ∂^n f`", is asserted without proof in [D, p. 465] (and is [D-LN, Ex. 4.1]).
  What is used of it is proved here: `f_{2,α}` is approximated by Schwartz functions, and the density
  statements carry the bound over, as the hint of [D-LN, Ex. 2.19] does ("first consider smooth `h`
  and then approximate"). The approximation is the standard one: `z²(|z|² + ε)^{−α}` near `0`, the
  cutoff smoothed near `|z| = 1` (where `g₂` is only `C¹`) and truncated at infinity, and dominated
  convergence. [D] states the bound for `p > 2` (its standing assumption, p. 464), and the argument
  works for every `p > 1`; the bound with `p*` for `p < 2` is not in [D]. It comes from
  `‖𝓑^n‖_p = ‖𝓑^n‖_{p'}`, by `𝓑^{−n} = (𝓑^n)^*` and `𝓑^{−n} f = conj(𝓑^n(conj f))` [CDK, §1.3.1, for
  `R^k`, `𝓑 = R²`], as here (for bounded multipliers, by the standard duality argument: the adjoint of
  `T_m` is `T_{m̄}`, and Schwartz functions norm `L^p`).
- **Duality** `‖T_m‖_p = ‖T_m‖_{p'}` follows [HNVW, Prop. 5.3.7], for scalar symbols:
  `∫ T_m f · g = ∫ T_{m(−·)} g · f`, Hölder's inequality, the norming of `L^p` by Schwartz functions,
  and the reflection `T_{m(−·)}(f(−·)) = (T_m f)(−·)`.
- **Transference** follows [HNVW, Prop. 5.7.4 and Cor. 5.7.6], for scalar symbols on `ℝ² ≅ ℂ` and the
  inequality from `𝕋²` to `ℝ²`: for Schwartz `f`, `g` with Fourier transforms in `C_c^∞(ℂ∖{0})`,
  `∫ T_m f g = ∫ m 𝓕f 𝓕⁻¹g` is a limit of Riemann sums over `R⁻¹ℤ²`, which by orthogonality are
  pairings of trigonometric polynomials on `𝕋²`; Hölder's inequality and [HNVW, Lemma 5.7.5] (Poisson
  summation) bound them by `‖T_{m(·/R)}‖ ‖f‖_p ‖g‖_{p'}` in the limit, and density [HNVW,
  Prop. 2.4.23 (ii)] and duality conclude. Corrections to the printed text, all in the docstrings:
  the missing hypotheses of Prop. 5.7.4 and the boundedness of `m`, the centred cell in Lemma 5.7.5,
  two interchanged exponents, and the norming of `T_m f`, for which the density of the `g` in `L^{p'}`
  alone is not enough (here their Fourier transforms converge in `L¹` as well, as Prop. 2.4.23 says).
  Part (i) of Prop. 2.4.23 (not used) is wrong for `C_c^∞(ℝ^d∖{0})`, whose functions vanish at `0`.
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
- The other inequalities of [HNVW, Cor. 5.7.6]: `‖T_m‖_{L^p_0(𝕋²)} ≤ ‖T_m‖_{L^p(𝕋²)} ≤ ‖T_m‖_{L^p(ℝ²)}`.

## Shorter proofs

Arguments shorter than the sources' that the proofs here do not use:

- [HNVW, Cor. 5.7.6], `I ≤ II`: the torus series with coefficients `R⁻² m(n) 𝓕f(n/R)`, `n ≠ 0`, at `x/R` are, up to the term `n = 0`, Riemann sums of `T_m f(x)`, and Fatou's lemma concludes, with no second test function, duality or density on `ℝ²`; the torus bound is extended to absolutely summable coefficients instead. This is Igari's proof of his Theorem 2 [I], there for `f ∈ C_c^∞(ℝ)` and the full norm on `𝕋`; here for Schwartz `f` and mean-zero polynomials (the library's proof at commit `bf215c5`, replaced since).
- [HNVW, Prop. 5.7.4]: `g` can be any Schwartz function, since `m 𝓕f 𝓕⁻¹g` is already continuous with compact support and the mean of the (then infinite, absolutely convergent) sum `Σ_n 𝓕g(n/R) e_n` plays no role; this removes the density step for `g` and the correction on norming (on paper).
- [HNVW, Prop. 2.4.23 (ii)]: `‖h‖_p ≤ ‖h‖_1^{1/p} ‖h‖_∞^{1−1/p}` gives the `L^p` limits from `‖𝓕f_j − 𝓕f‖_1 → 0` and `‖ϕ_t ∗ f‖_1 ≤ ‖ϕ‖_1 ‖f‖_1` (on paper).

## Literature

As of 22 November 2026; preprints are reported as claimed.

- **Transference.** Restriction from `ℝ` to `𝕋` is de Leeuw's (1965, Prop. 3.3). The converse used
  here, `‖m‖_{M_p(ℝ)} ≤ lim_{λ→0} ‖(m(λn))_n‖_{M_p(ℤ)}`, is Igari's (1968 lectures;
  1969, Thm 2, for `1 ≤ p ≤ 2`, by Riemann sums and Fatou's lemma), and Jodeit (1970, p. 215) states that a symbol continuous off `0` and homogeneous of
  degree `0` is a multiplier on `ℝ^N` iff its restriction to `ℤ^N` is one. Equality of the norms,
  mean-zero functions included, is Geiss–Montgomery-Smith–Saksman (2010, Lemma 2.2; smooth symbols,
  vector-valued) and [HNVW, Cor. 5.7.6] (operator-valued symbols, continuous off `0`).
- **`‖𝓑‖_p`.** `≥ p* − 1` is Lehto's (1965); Iwaniec (1982) conjectured equality. Uniform upper
  bounds: `4(p* − 1)` (Bañuelos–Wang 1995), `2(p* − 1)` (Nazarov–Volberg 2003), `1.575(p* − 1)`
  (Bañuelos–Janakiraman 2008); `1.523958(p* − 1)` is claimed in a manuscript of
  `Tencent-Hunyuan/Hyra-results` (2026), and the conjecture in the preprint arXiv:2609.28311 (v2,
  October 2026).
- **`‖𝓑^n‖_p`.** Of order `n^{1−2/p*}(p* − 1)` (Dragičević–Petermichl–Volberg 2006; the lower bound
  completed in [D]); `≥ κ_n(p)` for `p > 2` ([D], 2011); the same for all powers of the complex Riesz
  transform ([CDK], 2023). The conjecture `‖𝓑^n‖_p = κ_n(p)`, `p ≥ 2` ([D, Conj. 1.2]), is open for `n ≥ 2` as far as we found;
  arXiv:2609.28311 concerns `n = 1`.
- **Other formalizations of `𝓑`** (all Lean 4). Bounded on `L^p`, `1 < p < ∞`:
  `will1491/no-wandering-domains` (arXiv:2609.16027; the singular integral, through the Carleson
  project's Calderón–Zygmund theory) and `TauCetiProject/TauCeti` (the multiplier, through
  Mihlin–Hörmander; it also has `𝓑∂̄ = ∂` and the Fourier symbols of `∂`, `∂̄` on Schwartz functions).
  `L²` isometry: `openai/math`, `Tencent-Hunyuan/Hyra-results` (which also has certificates for parts of
  its manuscript). Lehto's bound, the bound `1.575(p* − 1)` and Iwaniec's conjecture are stated, not
  proved, in `facebookresearch/atlas-lean`.
- **Other overlaps.** Poisson summation on lattices of `ℝ^n` for Schwartz functions: at least five
  Lean projects of 2026, among them `CBirkbeck/AINTLIB`, `anthropics/fermats-last-theorem` and TauCeti
  (Mathlib: only on `ℝ`). Fourier series and `∂̄` of smooth functions on tori, and `L²` multipliers:
  TauCeti. Mathlib has Fourier multipliers with smooth symbols of temperate growth, on Schwartz
  functions and tempered distributions, and no `L^p` bounds for `p ≠ 2`. The Isabelle AFP, MathComp-Analysis and
  HOL Light have no multiplier theory that we found.
- **Transference elsewhere in Lean.** Magyar–Stein–Wainger's transference from `ℝ` to `ℤ`, for variation
  norms, is in PALOMAR-2026-11-17-000007.
- **New here, as far as we found:** `L^p` transference of Fourier multipliers from the torus to `ℝ²`; lower
  bounds for
  `‖𝓑²‖_p`; the isometric duality `‖T_m‖_p = ‖T_m‖_{p'}`; the `L^p` asymptotics of periodisations
  [HNVW, Lemma 5.7.5] and the density of the Schwartz functions with Fourier transform in
  `C_c^∞(ℝ^d∖{0})` [HNVW, Prop. 2.4.23 (ii)]; the corrections to HNVW listed under Method.

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
lake build                         # the library and the Palomar entry (whose Challenge has `sorry`s)
lake env lean scripts/Audit.lean   # axioms: fails on any `sorry` or non-standard axiom
# Comparator (needs bubblewrap): the Solution proves the Challenge's statements
lake env lake comparator --config=palomar/FourierMultipliers/comparator.json
```

## Layout

| Path | Content |
| --- | --- |
| [`HarmonicAnalysis/Defs.lean`](HarmonicAnalysis/Defs.lean) | the definitions that the headline theorems use |
| [`HarmonicAnalysis/Complex/`](HarmonicAnalysis/Complex) | `Wirtinger` (`∂`, `∂̄` on functions and on `𝓢(ℂ, F)`, symbols, conjugation), `WirtingerRadial` (`∂`, `∂̄` of `z^a z̄^b K(\|z\|²)`), `RadialIntegral` (radial integrals) |
| [`HarmonicAnalysis/FourierMultiplier/`](HarmonicAnalysis/FourierMultiplier) | `Basic` (`fourierMultiplier`, `multiplierNorm`, density), `Density` (mollifiers, the Schwartz functions with Fourier transform supported off `0`), `Norming` (`L^p` norms by Schwartz test functions), `Duality`, `Extension` (`T_m` as an operator on `L^p`) |
| [`HarmonicAnalysis/Torus/`](HarmonicAnalysis/Torus) | `Cube` (periodic functions, the unit cube, `𝕋² ↔ ℂ`), `Lattice` (the lattice `ℤ + iℤ`, the tiling of `ℂ` by cells, periodic functions on `𝕋²`), `TrigPoly` (trigonometric polynomials, `torusMultiplierNorm`, orthogonality), `Poisson` (periodisation, Poisson summation on `ℤ²`, the `L^p` norms of the periodisations), `Lipschitz` (Fourier coefficients over the unit cube, Parseval, derivatives of Lipschitz periodic functions), `Smooth` (smooth periodic functions: rapid decay, Fourier series, multipliers `T_m`, Wirtinger derivatives, `∂̄⁻¹`) |
| [`HarmonicAnalysis/Transference/`](HarmonicAnalysis/Transference) | `RiemannSum`, `ContinuousSymbol` (symbols continuous off `0`), `Homogeneous` (symbols homogeneous of degree `0`) |
| [`HarmonicAnalysis/BeurlingAhlfors/`](HarmonicAnalysis/BeurlingAhlfors) | `Basic` (symbol, `𝓑^k`, `𝓑^k ∂̄^k = ∂^k`, density), `Duality`, `TestFunctions` (Dragičević's `f_{2,α}`; with `TestFunctions/Profile`, one-variable calculus, and `TestFunctions/Approx`, its Schwartz approximations), `LowerBound` (Dragičević, `n = 2`), `Transference` (`𝓑^k` on `𝕋²`), `Periodic` (`𝓑` on smooth periodic functions) |
| [`palomar/FourierMultipliers/`](palomar/FourierMultipliers) | the Palomar entry |
| [`scripts/`](scripts) | `Audit.lean` (the axiom audit), `sync_challenge_defs.py` (the Challenge's copy of the definitions), `check_md_tables.py`, and tools for checking files and statements |
| [`.github/workflows/`](.github/workflows) | CI: build, audit, import list of the audit, the Challenge's copy of the definitions, Markdown tables, line lengths; Palomar's preflight, run by hand |

## References

- [HNVW] T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*,
  Ergebnisse der Mathematik 63, Springer, 2016: Lemma 1.2.30, Proposition 1.2.32, Lemma 2.4.8,
  Proposition 2.4.23, Definitions 5.3.1 and 5.3.3, Propositions 5.3.7, 5.7.1 and 5.7.4, Lemma 5.7.5,
  Corollary 5.7.6.
- [D] O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471: Theorem 1.1 (`p > 2`).
- [D-LN] O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes (Seville,
  2013), [arXiv:2109.04555](https://arxiv.org/abs/2109.04555): §4.1, Proposition 4.2
  (= [D, Thm 1.1]), Corollary 4.8, Exercises 1.16, 2.19 and 4.1.
- [CDK] A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex
  Riesz transform*, Math. Ann. 386 (2023), 1081–1125,
  [arXiv:2109.08369](https://arxiv.org/abs/2109.08369): §1.3.1 (duality), §2.1.
- [G] L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Graduate Texts in Mathematics 249,
  Springer, 2014: Chapter 3 (Fourier series on `𝕋^n`). Not consulted: the arguments for smooth
  periodic functions (decay of the coefficients, absolute convergence and uniqueness of the Fourier
  series) are the standard ones.
- [K] Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press,
  2004: Chapter I (Fourier series on `𝕋`). Not consulted, as for [G].

Cited in the section on the literature, and for the first of the shorter proofs, only:

- [I] S. Igari, *Functions of `L^p`-multipliers*, Tôhoku Math. J. (2) 21 (1969), 304–320.
- K. de Leeuw, *On `L_p` multipliers*, Ann. of Math. (2) 81 (1965), 364–379.
- M. Jodeit, Jr., *Restrictions and extensions of Fourier multipliers*, Studia Math. 34 (1970),
  215–226.
- S. Geiss, S. Montgomery-Smith, E. Saksman, *On singular integral and martingale transforms*, Trans.
  Amer. Math. Soc. 362 (2010), 553–575.
- O. Lehto, *Remarks on the integrability of the derivatives of quasiconformal mappings*, Ann. Acad.
  Sci. Fenn. A I 371 (1965).
- T. Iwaniec, *Extremal inequalities in Sobolev spaces and quasiconformal mappings*, Z. Anal. Anwend.
  1 (1982), no. 6, 1–16.
- R. Bañuelos, G. Wang, *Sharp inequalities for martingales with applications to the
  Beurling–Ahlfors and Riesz transforms*, Duke Math. J. 80 (1995), 575–600.
- F. Nazarov, A. Volberg, *Heating of the Ahlfors–Beurling operator, and estimates of its norm*, St.
  Petersburg Math. J. 15 (2004), 563–573.
- R. Bañuelos, P. Janakiraman, *`L^p`-bounds for the Beurling–Ahlfors transform*, Trans. Amer. Math.
  Soc. 360 (2008), 3603–3613.
- O. Dragičević, S. Petermichl, A. Volberg, *A rotation method which gives linear `L^p` estimates
  for powers of the Ahlfors–Beurling operator*, J. Math. Pures Appl. 86 (2006), 492–509.

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
