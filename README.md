# Harmonic analysis in Lean: Fourier multipliers, the Beurling–Ahlfors transform, vector-valued harmonic analysis

[![Lean Action CI](https://github.com/vltanh/lean4-harmonic-analysis/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-harmonic-analysis/actions/workflows/lean_action_ci.yml)

Lean 4 with Mathlib `v4.36.0-rc2`. For scalar functions, on `ℂ ≅ ℝ²`, the torus `𝕋² = (ℝ/ℤ)²` and the tori `𝕋^ι`:

- **Fourier multipliers** `T_m f = 𝓕⁻¹(m · 𝓕f)` and their norms on `L^p`, computed on Schwartz
  functions, which also bound `T_m` on the `L^p`-closure of its graph (density); on the torus, on
  mean-zero trigonometric polynomials. For bounded measurable `m`, the norm is that of the bounded
  extension of `T_m` to `L^p` (`1 ≤ p < ∞`), and there is duality (`1 < p < ∞`):
  `‖T_m‖_p = ‖T_m‖_{p'}`, `‖T_m‖_p = ‖T_{m̄}‖_{p'}`; also `‖T_{m̄(−·)}‖_p = ‖T_{m(−·)}‖_p = ‖T_m‖_p`.
- **Transference from `𝕋²` to `ℝ²`** [HNVW, Prop. 5.7.4, Cor. 5.7.6], `1 < p < ∞`: for `m` continuous
  off `0` and `R_j → ∞`, `‖T_m‖_{L^p(ℝ²)} ≤ liminf_j ‖T_{m(·/R_j)}‖_{L^p_0(𝕋²)}`; if `m` is moreover
  homogeneous of degree `0`, `‖T_m‖_{L^p(ℝ²)} ≤ ‖T_m‖_{L^p_0(𝕋²)}`. Through:
  - the density of the Schwartz functions with Fourier transform in `C_c^∞(ℝ^d∖{0})`
  - Poisson summation on `ℤ²`
  - lattice Riemann sums
- **The Beurling–Ahlfors transform** `𝓑`, symbol `ξ̄/ξ`:
  - `𝓑^k(∂̄^k F) = ∂^k F`
  - `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}`
  - transference for `𝓑^k`
  - the Cauchy transform `C g(z) = (1/π) ∫ g(w)/(z − w) dw` of `g ∈ C_c^∞`, which is smooth:
    - `∂̄(C g) = g` (the Cauchy–Pompeiu formula)
    - `∂(C g) = 𝓑g`
    - `C g = O(1/|z|)` and `∂(C g) = O(1/|z|²)`
  - **`‖𝓑‖_p` is the best constant of `‖∂u‖_p ≤ C ‖∂̄u‖_p` on `C_c^∞`**, `1 < p < ∞` [BMS, §1 (b)],
    by the cut-offs of Guerra [Gu]
  - **Dragičević's lower bound** `‖𝓑^n‖_p ≥ κ_n(p)` for `n = 1` and `n = 2`:
    - `‖𝓑‖_p ≥ κ₁(p) = p − 1`
    - `‖𝓑²‖_p ≥ κ₂(p) = (p−1)(2p−1)/(p+1)`; with the duality of Carbonaro, Dragičević and Kovač
      for `p < 2`, `‖𝓑²‖_p ≥ κ₂(p*)`, `p* = max(p, p')`, hence `‖𝓑²‖_p > p* − 1` for `p ≠ 2`, and
      `‖𝓑²‖₄ ≥ 21/5`
- **Smooth periodic functions** on `ℝ^ι`, `ι` finite:
  - the derivative formula `(∂_v g)^(n) = 2πi⟨n,v⟩ ĝ(n)`
  - rapid decay of the Fourier coefficients
  - absolute convergence of the Fourier series
  - Fourier multipliers `T_m g = Σ_n m(n) ĝ(n) e_n` with polynomially bounded symbols, which
    preserve smooth periodic functions
  - on `ℝ² ≅ ℂ`, the inverse of `∂̄` on mean-zero smooth periodic functions and `𝓑(∂̄g) = ∂g` for
    smooth periodic `g`

For functions with values in Banach spaces, on `ℝ` and the circle `𝕋 = ℝ/ℤ`:

- **UMD spaces**:
  - [HNVW, Sections 5.1–5.3, 5.7]:
    - dyadic shifts
    - the Hilbert transform
    - the (right-hand) Littlewood–Paley inequality on the line and on the circle, with random signs
      and sharp cut-offs
    - the transference of Fourier multipliers with operator-valued symbols from the line to the
      circle
  - Burkholder's theorem: conjugate functions on the circle and the Hilbert transform on the line
    [B83]
  - McConnell's theorems: Mihlin multipliers, and the Littlewood–Paley inequalities with sharp
    cut-offs for every choice of the signs [MC]
- **Matrix-valued Hardy functions**:
  - [HL1, HL2]:
    - Jensen's inequality
    - outer functions
    - Szegő's theorem and the factorization `W = BᴴB` for matrix-valued functions
    - analytic range functions
  - **Sarason's factorization** of `H¹`: `A = A₁A₂` with `A₂ᴴA₂ = (AᴴA)^{1/2}`, `A₁ᴴA₁ = A₂A₂ᴴ` [S]
- **Paley's inequality in the Schatten classes** `S_p`, `1 ≤ p ≤ 2`, and the **noncommutative Khintchine
  inequality**, along the route of Lust-Piquard and Pisier [LPP, Pi], with constants `1` and `C √q`.

**Status: complete.** Every statement is proved, and no theorem takes an unproved result as a hypothesis.
The [audit](scripts/Audit.lean) checks that every
declaration of the library depends only on Lean's standard axioms ([`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice),
[`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)): no `sorry`, no `axiom`, no `native_decide`. (The Challenges of the
[Palomar entries](#palomar) state their theorems with `sorry`, by design; the Solutions prove them.)
The vector-valued part uses [BanachProbability](https://github.com/vltanh/lean4-banach-probability):

- UMD constants
- Schatten norms of real and complex matrices
- type 2 of `S_q` and K-convexity
- the contraction principle
- the Kahane–Khintchine inequality

Keys in brackets refer to [docs/REFERENCES.md](docs/REFERENCES.md).

## Main statements

### Fourier multipliers, transference, the Beurling–Ahlfors transform

`p' = p/(p−1)`. The `L^p` norms are `MeasureTheory.eLpNorm` with exponent `ENNReal.ofReal p`, and
the operator norms are suprema in `ℝ≥0∞`.

| Statement | Lean | Source |
| --- | --- | --- |
| `𝓕(∂̄f)(ξ) = πiξ 𝓕f(ξ)`, `𝓕(∂f)(ξ) = πiξ̄ 𝓕f(ξ)` | [`fourier_dzbarCLM`](HarmonicAnalysis/Complex/Wirtinger.lean#L90), [`fourier_dzCLM`](HarmonicAnalysis/Complex/Wirtinger.lean#L103) | |
| `‖v‖_p / ‖u‖_p ≤ ‖T_m‖_p` if Schwartz `φ_k → u`, `T_m φ_k → v` in `L^p` | [`div_le_multiplierNorm_of_tendsto`](HarmonicAnalysis/FourierMultiplier/Basic.lean#L141) | density |
| `‖T_m‖_p < ∞` iff `T_m` extends from Schwartz functions to a bounded operator on `L^p`, which is then unique, of norm `‖T_m‖_p` (`m` bounded measurable, `1 ≤ p`) | [`existsUnique_extension_of_multiplierNorm_ne_top`](HarmonicAnalysis/FourierMultiplier/Extension.lean#L80), [`enorm_eq_multiplierNorm`](HarmonicAnalysis/FourierMultiplier/Extension.lean#L116) | density |
| `‖T_m‖_p = ‖T_m‖_{p'}` (`m` bounded measurable, `1 < p`) | [`multiplierNorm_conjExponent`](HarmonicAnalysis/FourierMultiplier/Duality.lean#L317) | [HNVW, Prop. 5.3.7] |
| `‖T_{m(−·)}‖_p = ‖T_m‖_p` | [`multiplierNorm_comp_neg`](HarmonicAnalysis/FourierMultiplier/Duality.lean#L250) | reflection; [HNVW, p. 403] |
| `∫ T_m f · ḡ = ∫ f · conj(T_{m̄} g)` for Schwartz `f, g` (`m` bounded measurable) | [`integral_fourierMultiplier_mul_conj`](HarmonicAnalysis/FourierMultiplier/Duality.lean#L131) | |
| `‖h‖_p ≤ A` if `\|∫ h ḡ\| ≤ A ‖g‖_{p'}` for all Schwartz `g` (`h` continuous, `1 < p`) | [`eLpNorm_le_of_forall_schwartz`](HarmonicAnalysis/FourierMultiplier/Norming.lean#L146) | duality |
| `‖T_m‖_p = ‖T_{m̄}‖_{p'}` (`m` bounded measurable, `1 < p`) | [`multiplierNorm_conj_conjExponent`](HarmonicAnalysis/FourierMultiplier/Duality.lean#L187) | duality; [CDK, §1.3.1] for `R^k` |
| `‖T_{m̄(−·)}‖_p = ‖T_m‖_p` | [`multiplierNorm_conj_comp_neg`](HarmonicAnalysis/FourierMultiplier/Duality.lean#L216) | conjugation; [CDK, §1.3.1] for `R^k` |
| `ϕ_t ∗ f → f` in `L^p` as `t → 0` for Schwartz `f`, `ϕ`, `∫ϕ = 1` (`1 ≤ p`) | [`tendsto_eLpNorm_mollify_sub`](HarmonicAnalysis/FourierMultiplier/Density.lean#L314) | [HNVW, Prop. 1.2.32] |
| For Schwartz `f`, `dim V > 0`: Schwartz `f_j → f` in every `L^p`, `1 < p < ∞`, `𝓕f_j → 𝓕f` in `L¹`, with `𝓕f_j ∈ C_c^∞(V∖{0})` | [`exists_tendsto_hasCompactFourierSupportOffZero`](HarmonicAnalysis/FourierMultiplier/Density.lean#L567) | [HNVW, Prop. 2.4.23 (ii)] |
| `∫_{𝕋^ι} T_m(Σ c_k e_k) (Σ d_ℓ e_ℓ) = Σ_k m(k) c_k d_{−k}` | [`integral_torusMultiplier_mul_trigPoly`](HarmonicAnalysis/Torus/TrigPoly.lean#L68) | orthogonality |
| `Σ_j f(R(y+j)) = Σ_n R⁻² 𝓕f(n/R) e^{2πi⟨n,y⟩}` on `ℤ²`, for Schwartz `f` | [`hasSum_periodize`](HarmonicAnalysis/Torus/Poisson.lean#L270) | Poisson summation |
| `R^{2/p} ‖Σ_n R⁻² 𝓕f(n/R) e_n‖_{L^p(𝕋²)} → ‖f‖_{L^p(ℝ²)}` as `R → ∞`, for Schwartz `f` (`1 ≤ p`) | [`tendsto_eLpNorm_tsum_fourier_mul_mFourier`](HarmonicAnalysis/Torus/Poisson.lean#L430) | [HNVW, Lemma 5.7.5] |
| `Σ_n R⁻² φ(n/R) → ∫ φ` for `φ` continuous off `0`, `\|φ\| ≤ C(1+\|ξ\|)^{−3}` | [`tendsto_riemannSum_real`](HarmonicAnalysis/Transference/RiemannSum.lean#L94) | |
| `‖T_m‖_{L^p(ℝ²)} ≤ liminf_j ‖T_{m(·/R_j)}‖_{L^p_0(𝕋²)}`, `R_j → ∞`, `m` continuous off `0` (`1 < p`) | [`multiplierNorm_le_liminf_torusMultiplierNorm`](HarmonicAnalysis/Transference/ContinuousSymbol.lean#L402) | [HNVW, Prop. 5.7.4] |
| `m` is bounded if that `liminf` is finite | [`exists_norm_le_of_liminf_torusMultiplierNorm_ne_top`](HarmonicAnalysis/Transference/ContinuousSymbol.lean#L430) | |
| `‖T_m‖_{L^p(ℝ²)} ≤ ‖T_m‖_{L^p_0(𝕋²)}`, `m` homogeneous of degree `0`, continuous off `0` (`1 < p`) | [`multiplierNorm_le_torusMultiplierNorm`](HarmonicAnalysis/Transference/Homogeneous.lean#L53) | [HNVW, Cor. 5.7.6] (`I ≤ II`) |
| `𝓑^k(∂̄^k F) = ∂^k F` for Schwartz `F`; the same for the `k`-fold iterate of `𝓑` | [`beurlingPow_dzbarCLM_pow`](HarmonicAnalysis/BeurlingAhlfors/Basic.lean#L91), [`beurlingPow_dzbar_iterate`](HarmonicAnalysis/BeurlingAhlfors/Basic.lean#L109), [`iterate_beurlingPow_one_dzbar_iterate`](HarmonicAnalysis/BeurlingAhlfors/Basic.lean#L116) | [D, p. 465]; [D-LN, §4.1, and Ex. 2.19 for `k = 1`] |
| `‖v‖_p / ‖u‖_p ≤ ‖𝓑^k‖_p` if Schwartz `∂̄^k φ_j → u`, `∂^k φ_j → v` in `L^p` | [`div_le_beurlingPowNorm_of_tendsto`](HarmonicAnalysis/BeurlingAhlfors/Basic.lean#L132) | density; [D, p. 465]; [D-LN, Ex. 2.19, §4.1] |
| `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}` (`1 < p`) | [`beurlingPowNorm_conjExponent`](HarmonicAnalysis/BeurlingAhlfors/Duality.lean#L39) | [CDK, §1.3.1] |
| `‖𝓑^k‖_{L^p(ℝ²)} ≤ ‖𝓑^k‖_{L^p_0(𝕋²)}` (`1 < p`) | [`beurlingPowNorm_le_torusBeurlingPowNorm`](HarmonicAnalysis/BeurlingAhlfors/Transference.lean#L50) | [HNVW, Cor. 5.7.6] (`I ≤ II`) |
| `f_{1,α}` (with the cutoff `g₂`), what is used of `f_{1,α} ∈ W^{1,p}`: Schwartz `φ_k` with `∂̄φ_k → ∂̄f_{1,α}`, `∂φ_k → ∂f_{1,α}` in `L^p` (`1 ≤ p`, `0 < α < 1/p`) | [`BeurlingAhlfors.exists_schwartz_tendsto_testFunOne`](HarmonicAnalysis/BeurlingAhlfors/TestFunctions/One.lean#L448) | asserted in [D, p. 465] (for `p > 2`); [D-LN, Ex. 2.19] |
| `‖∂f_{1,α}‖_p / ‖∂̄f_{1,α}‖_p → κ₁(p) = p − 1` as `α → 1/p⁻` | [`tendsto_eLpNorm_div_testFunOne`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L248) | [D, Thm 1.1] (for `p > 2`); on the unit disc, [BMS, §1] |
| `κ₁(p) = p − 1 ≤ ‖𝓑‖_p` for `1 < p` | [`beurlingKappa_one_le_beurlingPowNorm_one`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L279), [`sub_one_le_beurlingPowNorm_one`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L288) | [D, Thm 1.1] (for `p > 2`) |
| `f_{2,α}`, what is used of `f_{2,α} ∈ W^{2,p}`: Schwartz `φ_k` with `∂̄²φ_k → ∂̄²f_{2,α}`, `∂²φ_k → ∂²f_{2,α}` in `L^p` (`1 ≤ p`, `0 < α < 1/p`) | [`BeurlingAhlfors.exists_schwartz_tendsto_testFun`](HarmonicAnalysis/BeurlingAhlfors/TestFunctions.lean#L396) | asserted in [D, p. 465], [D-LN, Ex. 4.1] (for `p > 2`) |
| `‖∂²f_{2,α}‖_p / ‖∂̄²f_{2,α}‖_p → κ₂(p)` as `α → 1/p⁻` | [`tendsto_eLpNorm_div_testFun`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L297) | [D, Thm 1.1] (for `p > 2`) |
| `κ₂(p) ≤ ‖𝓑²‖_p` for `1 < p` | [`beurlingKappa_two_le_beurlingPowNorm_two`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L332) | [D, Thm 1.1] (for `p > 2`) |
| `κ₂(p*) ≤ ‖𝓑²‖_p` for `1 < p` | [`beurlingKappa_two_pStar_le_beurlingPowNorm_two`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L343) | [D, Thm 1.1] for `p > 2`; [CDK, §1.3.1] for `p < 2` |
| `C g(z) = (1/π) ∫ g(w)/(z − w) dw`: for `g ∈ C_c^∞`, `C g` is smooth, `∂(C g) = C(∂g)`, `∂̄(C g) = C(∂̄g)`, `C g = O(1/\|z\|)`, and `C g = O(1/\|z\|²)` if `∫ g = 0` | [`contDiff_cauchyTransform`](HarmonicAnalysis/Complex/CauchyTransform.lean#L134), [`dz_cauchyTransform`](HarmonicAnalysis/Complex/CauchyTransform.lean#L186), [`dzbar_cauchyTransform`](HarmonicAnalysis/Complex/CauchyTransform.lean#L191), [`exists_norm_cauchyTransform_le`](HarmonicAnalysis/Complex/CauchyTransform.lean#L251), [`exists_norm_cauchyTransform_le_of_integral_eq_zero`](HarmonicAnalysis/Complex/CauchyTransform.lean#L280) | differentiation of convolutions; elementary bounds |
| `C(∂̄g) = g` for `g` of class `C¹` with compact support | [`cauchyTransform_dzbar`](HarmonicAnalysis/Complex/CauchyPompeiu.lean#L210) | the Cauchy–Pompeiu formula, by polar coordinates |
| `𝓑g` is differentiable with `∂̄(𝓑g) = ∂g`, and `𝓑g → 0` at infinity, for Schwartz `g`; `∂̄u = 0` and `u → 0` at infinity imply `u = 0` | [`dzbar_beurlingPow_one`](HarmonicAnalysis/BeurlingAhlfors/Regularity.lean#L80), [`tendsto_beurlingPow_one_cocompact`](HarmonicAnalysis/BeurlingAhlfors/Regularity.lean#L119), [`eq_zero_of_dzbar_eq_zero`](HarmonicAnalysis/Complex/Liouville.lean#L62) | differentiation under the Fourier integral; Riemann–Lebesgue; Liouville |
| For `g ∈ C_c^∞`: `∂̄(C g) = g`, `∂(C g) = 𝓑g`, `∂(C g) ∈ L^p` (`1 < p`) | [`dzbar_cauchyTransform_eq`](HarmonicAnalysis/BeurlingAhlfors/CauchyTransform.lean#L66), [`dz_cauchyTransform_eq_beurlingPow_one`](HarmonicAnalysis/BeurlingAhlfors/CauchyTransform.lean#L73), [`memLp_dz_cauchyTransform`](HarmonicAnalysis/BeurlingAhlfors/CauchyTransform.lean#L102) | Liouville's theorem for `∂(C g) − 𝓑g` |
| For Schwartz `f`: `f_n = η_n f ∈ C_c^∞` with `f_n → f` in every `L^p`, `1 ≤ p`, and `𝓕f_n → 𝓕f` in `L¹` | [`exists_hasCompactSupport_tendsto`](HarmonicAnalysis/FourierMultiplier/CompactSupport.lean#L57) | cut-offs; `𝓕 f_n` is a mollification of `𝓕f` |
| For `g ∈ C_c^∞`: `u_n = η_n C g ∈ C_c^∞` with `∂u_n → 𝓑g`, `∂̄u_n → g` in `L^p` (`1 < p`); so `‖𝓑g‖_p ≤ C ‖g‖_p` if `‖∂u‖_p ≤ C ‖∂̄u‖_p` for all `u ∈ C_c^∞` | [`exists_hasCompactSupport_tendsto_cauchyTransform`](HarmonicAnalysis/BeurlingAhlfors/CompactSupport.lean#L343), [`eLpNorm_beurlingPow_one_le_of_hasCompactSupport`](HarmonicAnalysis/BeurlingAhlfors/CompactSupport.lean#L381) | the cut-offs of [Gu, proofs of Cors 1.2, 1.4], in the gradient case |
| `‖𝓑‖_p ≤ C` if `‖∂u‖_p ≤ C ‖∂̄u‖_p` for all `u ∈ C_c^∞`; conversely `‖∂u‖_p ≤ ‖𝓑‖_p ‖∂̄u‖_p`; so `‖𝓑‖_p` is the least such `C` (`1 < p`) | [`beurlingPowNorm_one_le_of_forall_hasCompactSupport`](HarmonicAnalysis/BeurlingAhlfors/CompactSupport.lean#L485), [`eLpNorm_dz_le_beurlingPowNorm_one_mul`](HarmonicAnalysis/BeurlingAhlfors/CompactSupport.lean#L510), [`beurlingPowNorm_one_le_iff`](HarmonicAnalysis/BeurlingAhlfors/CompactSupport.lean#L532), [`isLeast_beurlingPowNorm_one`](HarmonicAnalysis/BeurlingAhlfors/CompactSupport.lean#L541) | [BMS, §1 (b)] (stated without proof); the proof of [Gu, Cor. 1.4], in the gradient case |
| `p* − 1 < ‖𝓑²‖_p` for `p ≠ 2`; `21/5 ≤ ‖𝓑²‖₄` | [`pStar_sub_one_lt_beurlingPowNorm_two`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L366), [`twentyOne_div_five_le_beurlingPowNorm_two_four`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L373) | |
| `(∂_v g)^(n) = 2πi⟨n,v⟩ ĝ(n)` for Lipschitz, or `C¹`, `ℤ^ι`-periodic `g` | [`UnitAddTorus.cubeFourierCoeff_fderiv_of_lipschitzWith`](HarmonicAnalysis/Torus/Smooth.lean#L140), [`UnitAddTorus.cubeFourierCoeff_fderiv_of_contDiff`](HarmonicAnalysis/Torus/Smooth.lean#L206) | difference quotients; [G, Ch. 3] |
| `Σ_n (1 + ‖n‖)^k \|ĝ(n)\| < ∞` for smooth periodic `g` and every `k` | [`UnitAddTorus.exists_norm_cubeFourierCoeff_le`](HarmonicAnalysis/Torus/Smooth.lean#L282), [`UnitAddTorus.summable_cubeFourierCoeff`](HarmonicAnalysis/Torus/Smooth.lean#L361) | integration by parts; [G, Ch. 3] |
| `g(x) = Σ_n ĝ(n) e^{2πi⟨n,x⟩}` absolutely, for smooth periodic `g`; uniqueness | [`UnitAddTorus.hasSum_cubeFourierCoeff_mul_mFourier`](HarmonicAnalysis/Torus/Smooth.lean#L376), [`UnitAddTorus.eq_of_cubeFourierCoeff_eq`](HarmonicAnalysis/Torus/Smooth.lean#L390) | [G, Ch. 3], [K, Ch. I] |
| `T_m g` is smooth and periodic, with coefficients `m ĝ` (`\|m(n)\| ≤ C(1 + ‖n‖)^k`) | [`UnitAddTorus.contDiff_periodicMultiplier`](HarmonicAnalysis/Torus/Smooth.lean#L582), [`UnitAddTorus.cubeFourierCoeff_periodicMultiplier`](HarmonicAnalysis/Torus/Smooth.lean#L605) | Weierstrass M-test |
| `h = ∂̄u`, `u` smooth periodic of mean zero, for smooth `ℤ²`-periodic `h` of mean zero | [`UnitAddTorus.exists_dzbarPi_eq`](HarmonicAnalysis/Torus/Smooth.lean#L866) | the symbol `(πiν)⁻¹` |
| `𝓑(∂̄g) = ∂g` for smooth `ℤ²`-periodic `g` | [`periodicMultiplier_beurlingSymbol_dzbarPi`](HarmonicAnalysis/BeurlingAhlfors/Periodic.lean#L47) | comparison of coefficients |

Three of them in Lean:

```lean
theorem HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm {m : ℂ → ℂ}
    (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ) (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ torusMultiplierNorm (fun n => m (latticePoint n)) p

theorem HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (beurlingKappa 2 p) ≤ beurlingPowNorm 2 p

theorem HarmonicAnalysis.beurlingPowNorm_one_le_of_forall_hasCompactSupport {p : ℝ} (hp : 1 < p)
    {C : ℝ≥0∞}
    (h : ∀ u : ℂ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (dz u) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (dzbar u) (ENNReal.ofReal p) volume) :
    beurlingPowNorm 1 p ≤ C
```

Here `beurlingKappa n p = (1/q)_n / (1/p)_n`, `1/q = 1 − 1/p`, with the Pochhammer symbol
`(a)_n = a(a+1)⋯(a+n−1)`; `κ₁(p) = p − 1`, `κ₂(p) = (p−1)(2p−1)/(p+1)`. Dragičević's test
functions are `f_{n,α}(z) = z^n |z|^{−2α} g_n(|z|)`; `f_{1,α}` is taken here with the cutoff `g₂`
(see Method).

### Vector-valued harmonic analysis

- `X` is a complex Banach space and `β` a `UMD_p` constant of `X` for real signs
  (`BanachProbability.IsUMDBound X p β`), `1 < p < ∞`.
- `ε_k` are independent fair signs.
- `e_n (t) = e^{2πi n t}`.
- [`eLpNormRad`](HarmonicAnalysis/VectorValued/Defs.lean#L73) is the norm of a Rademacher sum `Σ_k ε_k f_k` in `L^p` of the product
  with the signs.
- `circPoly c` is the trigonometric polynomial `Σ c_n e_n` with coefficients in a vector space
  ([`circPoly_eq_trigPoly`](HarmonicAnalysis/VectorValued/CircPoly.lean#L65): the scalar [`trigPoly`](HarmonicAnalysis/Defs.lean#L77), in dimension `1`).
- `C_p = S_p` are the Schatten classes of complex matrices, of every size.
- Matrices are finite.
- `H¹`, `H²` are the classes of matrix-valued functions on `𝕋` with entries in `L¹`, `L²` and
  vanishing Fourier coefficients of negative order.
- Equalities of functions on `𝕋` hold almost everywhere.
- An analytic polynomial has frequencies `≥ 0`.
- `A ∈ H²` is outer if the closure in `L²` of the functions `A (1 + P)`, `P` an analytic polynomial
  without constant term, contains a constant; left-outer if its transpose is outer.
- `Δ W` is the determinant of `W` on its range, and "`∫ log Δ W > −∞`" means that `log Δ W` is
  integrable.

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| Dyadic averages on the line form a martingale on each unit interval | [`martingale_dyadicAvg`](HarmonicAnalysis/VectorValued/Dyadic/Martingale.lean#L190) |  | `VectorValued/Dyadic/Martingale` |
| The parts `S_j`, `0 ≤ j < n`, of the dyadic shift with the kernel `h` or (5.19): `‖Σ_j ε_j S_j f‖_p ≤ 2β ‖f‖_p` | [`eLpNormRad_dyadicShift_le`](HarmonicAnalysis/VectorValued/Dyadic/Shift.lean#L181) | [HNVW, Props 5.1.4, 5.1.5] | `VectorValued/Dyadic/Shift` |
| The parts `S_j`, `0 ≤ j < n`, of the dyadic shift: `‖Σ_j S_j f‖_p ≤ 2β² ‖f‖_p` for (5.19) | [`eLpNorm_sum_dyadicShift_le`](HarmonicAnalysis/VectorValued/Dyadic/Shift.lean#L263) | [HNVW, Prop 5.1.5] | `VectorValued/Dyadic/Shift` |
| Averaging over translates gives a convolution: `∫_0^1 S_j (f (· + u)) (· − u) du = φ_{2^{−j}} * f`, `φ (x) = ∫ k (x + u) h (u) du` for a kernel `k` | [`intervalIntegral_dyadicShift_translate`](HarmonicAnalysis/VectorValued/Dyadic/Average.lean#L302) | [HNVW, Lemma 5.1.9] | `VectorValued/Dyadic/Average` |
| Averaging over translates: hence `‖Σ_j ε_j φ_{2^{−j}} * f‖_p ≤ 2β ‖f‖_p` for `k = h` | [`eLpNormRad_dilateConv_le`](HarmonicAnalysis/VectorValued/Dyadic/Average.lean#L365) | [HNVW, Prop 5.1.10] (second inequality) | `VectorValued/Dyadic/Average` |
| Averaging over translates: hence `‖Σ_j φ_{t 2^{−j}} * f‖_p ≤ 2β² ‖f‖_p` for `k` of (5.19) and `t > 0` | [`eLpNorm_sum_dilateConv_le`](HarmonicAnalysis/VectorValued/Dyadic/Average.lean#L435) | [HNVW, Prop 5.1.10] (first inequality) | `VectorValued/Dyadic/Average` |
| Hilbert transform, by dyadic shifts: the truncations `H_{ε, 2^n ε}` are bounded on `L^p (ℝ; X)` by `4β² + 11` | [`eLpNorm_truncatedHilbert_le`](HarmonicAnalysis/VectorValued/HilbertTransform/Truncated.lean#L603) | [HNVW, Thm 5.1.13] | `VectorValued/HilbertTransform/Truncated` |
| Hilbert transform, by dyadic shifts: the symbols of the truncations are `−i sgn (ξ) m_{ε,R} (ξ)` with `\|m_{ε,R}\| ≤ 2`, `m_{ε,R} → 1` | [`truncatedHilbert_fourierInv`](HarmonicAnalysis/VectorValued/HilbertTransform/Fourier.lean#L422), [`abs_hilbertSymbol_le`](HarmonicAnalysis/VectorValued/HilbertTransform/Fourier.lean#L221), [`tendsto_hilbertSymbol`](HarmonicAnalysis/VectorValued/HilbertTransform/Fourier.lean#L249) | [HNVW, Lemma 5.2.1] | `VectorValued/HilbertTransform/Fourier` |
| Hilbert transform, by dyadic shifts: hence `‖𝓕⁻ (−i sgn · G)‖_p = ‖𝓕⁻ (sgn · G)‖_p ≤ (4β² + 11) ‖𝓕⁻ G‖_p` for `G ∈ L¹`, `𝓕⁻ G ∈ L^p` | [`tendsto_truncatedHilbert_fourierInv`](HarmonicAnalysis/VectorValued/HilbertTransform/Fourier.lean#L507), [`eLpNorm_fourierInv_neg_I_sign_le_dyadic`](HarmonicAnalysis/VectorValued/HilbertTransform/Dyadic.lean#L66), [`eLpNorm_fourierInv_sign_le_dyadic`](HarmonicAnalysis/VectorValued/HilbertTransform/Dyadic.lean#L96) | [HNVW, Thm 5.1.13, Prop 5.2.2] | `VectorValued/HilbertTransform/Fourier`, `VectorValued/HilbertTransform/Dyadic` |
| **Burkholder's theorem**: conjugate harmonic polynomials `u (r e^{iθ}) = Σ (a_k cos kθ + b_k sin kθ) r^k`, `v (r e^{iθ}) = Σ (a_k sin kθ − b_k cos kθ) r^k` satisfy `‖v (r e^{iθ})‖_p ≤ β² ‖u (r e^{iθ})‖_p` | [`eLpNorm_conjHarmPoly_le`](HarmonicAnalysis/VectorValued/Burkholder/Conjugate.lean#L583); [`lpNorm_sqrt_exitTime_le`](HarmonicAnalysis/VectorValued/Burkholder/RandomWalk.lean#L576), [`exists_lpNorm_harmPoly_sub_le`](HarmonicAnalysis/VectorValued/Burkholder/RandomWalk.lean#L818), [`lpNorm_walkMartingale_conj_le`](HarmonicAnalysis/VectorValued/Burkholder/RandomWalk.lean#L907) | [B83, Lemma 2, (20)–(29)] | [`VectorValued/Burkholder/`](HarmonicAnalysis/VectorValued/Burkholder) |
| Burkholder's theorem, on `ℝ/ℤ`, `c_0 = 0`: `‖Σ (−i sgn n) c_n e_n‖_p ≤ β² ‖Σ c_n e_n‖_p` | [`eLpNorm_conj_circPoly_le`](HarmonicAnalysis/VectorValued/Burkholder/Conjugate.lean#L668) | [B83, Lemma 2] | [`VectorValued/Burkholder/`](HarmonicAnalysis/VectorValued/Burkholder) |
| Burkholder's theorem, conjugate Poisson integrals of `f ∈ L^p`: `‖v (r e^{iθ})‖_p ≤ 2β² ‖u (r e^{iθ})‖_p` | [`eLpNorm_discConjPoissonInt_le`](HarmonicAnalysis/VectorValued/Burkholder/ConjugateFunction.lean#L702) | [B83, Lemma 3] | [`VectorValued/Burkholder/`](HarmonicAnalysis/VectorValued/Burkholder) |
| Burkholder's theorem, the truncated conjugate function: `‖f̃_ε‖_p ≤ (2β² + 1) ‖f‖_p`, `0 < ε < 1` | [`eLpNorm_truncatedConj_le`](HarmonicAnalysis/VectorValued/Burkholder/ConjugateFunction.lean#L1080); [`integral_truncationError_lt`](HarmonicAnalysis/VectorValued/Burkholder/ConjugateFunction.lean#L973) | [B83, (33)] | [`VectorValued/Burkholder/`](HarmonicAnalysis/VectorValued/Burkholder) |
| Burkholder's theorem, the truncated Hilbert transform `H_ε f (x) = π⁻¹ ∫_{\|t\| > ε} f (x − t) dt/t`: `‖H_ε f‖_p ≤ (2β² + 1) ‖f‖_p`, `f ∈ L^p (ℝ; X)`, `X` a real Banach space | [`eLpNorm_hilbertTrunc_le`](HarmonicAnalysis/VectorValued/Burkholder/HilbertTransform.lean#L569) | [B83, Lemma 4] | [`VectorValued/Burkholder/`](HarmonicAnalysis/VectorValued/Burkholder) |
| Burkholder's theorem: hence `‖𝓕⁻ (−i sgn · G)‖_p = ‖𝓕⁻ (sgn · G)‖_p ≤ (2β² + 1) ‖𝓕⁻ G‖_p` for `G ∈ L¹`, `𝓕⁻ G ∈ L^p`, `X` complex | [`tendsto_hilbertTrunc_fourierInv`](HarmonicAnalysis/VectorValued/Burkholder/HilbertTransform.lean#L668), [`eLpNorm_fourierInv_neg_I_sign_le`](HarmonicAnalysis/VectorValued/Burkholder/HilbertTransform.lean#L685), [`eLpNorm_fourierInv_sign_le`](HarmonicAnalysis/VectorValued/Burkholder/HilbertTransform.lean#L708) | [B83, Lemma 4], with [HNVW, Prop 5.2.2] | [`VectorValued/Burkholder/`](HarmonicAnalysis/VectorValued/Burkholder) |
| Littlewood–Paley on the line, for the intervals `(2^{k−1}, 2^k)`, `−(2^{k−1}, 2^k)`, `(−1, 1)`, `0 < k ≤ K`, and `f = 𝓕⁻ G`, `G ∈ L¹`: `‖Σ ε_k Δ_k f‖_p ≤ C_β ‖f‖_p`; the same for the dilates of these intervals by `ρ⁻¹ > 0`, which gives the finite sums over all dyadic intervals | [`eLpNormRad_fourierInv_indicator_le`](HarmonicAnalysis/VectorValued/LittlewoodPaley/Line.lean#L707), [`eLpNormRad_lineBlock_le`](HarmonicAnalysis/VectorValued/LittlewoodPaley/Line.lean#L955), [`eLpNormRad_lineBlock_dilate_le`](HarmonicAnalysis/VectorValued/LittlewoodPaley/Line.lean#L1028) | [HNVW, Thm 5.3.24 and Cor 5.3.25, right-hand inequalities] | `VectorValued/LittlewoodPaley/Line` |
| Transference (`X`, `Y` complex Banach spaces): let `m` be a bounded operator-valued symbol such that each `m (·) x` is strongly measurable and continuous at the integers; if `‖T_m h‖_p ≤ C ‖h‖_p` for Schwartz `h : ℝ → X`, then `‖Σ m (k) a_k e_k‖_{L^p (𝕋; Y)} ≤ C ‖Σ a_k e_k‖_{L^p (𝕋; X)}` for trigonometric polynomials | [`eLpNorm_circPoly_multiplier_le`](HarmonicAnalysis/VectorValued/Transference.lean#L1028); Lemmas 5.7.2, 5.7.3: [`tendsto_integral_dilate_multiplier`](HarmonicAnalysis/VectorValued/Transference.lean#L521), [`tendsto_eLpNorm_dilate_smul`](HarmonicAnalysis/VectorValued/Transference.lean#L283) | [HNVW, Prop 5.7.1 (`d = 1`)] | `VectorValued/Transference` |
| Littlewood–Paley on the circle, for the dyadic blocks `Ĩ_k ⊂ ℤ`, `\|k\| ≤ K`, and trigonometric polynomials: `‖Σ ε_k Δ̃_k f‖_{L^p (Ω × 𝕋; X)} ≤ C_β ‖f‖_{L^p (𝕋; X)}` | [`eLpNormRad_dyadicBlock_le`](HarmonicAnalysis/VectorValued/LittlewoodPaley/Circle.lean#L352), [`eLpNormRad_dyadicBlock_succ_le`](HarmonicAnalysis/VectorValued/LittlewoodPaley/Circle.lean#L340) | [HNVW, Thm 5.7.10 (2), right-hand inequality] | `VectorValued/LittlewoodPaley/Circle` |
| **Mihlin multipliers**: for `m` of class `C²` on `ℝ ∖ {0}` with `\|ξ\|^k \|m^{(k)} (ξ)\| ≤ c`, `k ≤ 2`, `‖𝓕⁻ (m G)‖_p ≤ C c β² ‖𝓕⁻ G‖_p` for `G ∈ L¹`, `C` absolute. Through chains with independent Cauchy increments (the Poisson semigroup) and Burkholder's inequality | [`exists_eLpNorm_fourierInv_mihlin_le`](HarmonicAnalysis/VectorValued/McConnell/Multiplier.lean#L1638); [`lintegral_chainLaw_reverse`](HarmonicAnalysis/VectorValued/McConnell/Chain.lean#L171), [`eLpNorm_sum_smul_le`](HarmonicAnalysis/VectorValued/McConnell/Chain.lean#L328), [`norm_mihlinKernel_le`](HarmonicAnalysis/VectorValued/McConnell/Kernel.lean#L398), [`map_two_chains`](HarmonicAnalysis/VectorValued/McConnell/Chain.lean#L502), [`fourierInv_mihlin_eq_integral`](HarmonicAnalysis/VectorValued/McConnell/Multiplier.lean#L425) | [MC, Thm 1.1, Lemmas 2.1, 2.2, 3.1, 3.2, (3.3)] (`n = 1`) | [`VectorValued/McConnell/`](HarmonicAnalysis/VectorValued/McConnell) |
| **Littlewood–Paley inequalities for every choice of the signs**: for signs `ε_j`, `ε'_j` and `m = Σ_j ε_j 1_{[2^j, 2^{j+1})} + Σ_j ε'_j 1_{(−2^{j+1}, −2^j]}`, `c⁻¹ ‖f‖_p ≤ ‖T_m f‖_p ≤ c ‖f‖_p`, `c = C β⁸ (2β² + 1)²`, for `f = 𝓕⁻ G ∈ L^p`, `G ∈ L¹` | [`exists_eLpNorm_fourierInv_dyadicSign_le`](HarmonicAnalysis/VectorValued/LittlewoodPaley/Signs.lean#L1078) | [MC, Thm 1.3] (`n = 1`, UMD ⇒ (1.13)) | `VectorValued/LittlewoodPaley/Signs` |
| On the circle, for `ε_ℓ ∈ {−1, 0, 1}`: the multipliers equal to `ε_ℓ` on the blocks `[2^ℓ, 2^{ℓ+1})`, or on `(2^{ℓ−1}, 2^ℓ]`, and `a_n = Σ_{n ≤ 2^ℓ ≤ 2n} ε_ℓ` (zero for `n ≤ 0`) are bounded on the trigonometric polynomials in `L^p (𝕋; X)`, uniformly in the `ε_ℓ` | [`exists_eLpNorm_blockSign_le`](HarmonicAnalysis/VectorValued/LittlewoodPaley/CircleSigns.lean#L375) | [MC, Thm 1.3], [HNVW, Prop 5.7.1]; [LPP, p. 253] | `VectorValued/LittlewoodPaley/CircleSigns` |
| Jensen's inequality: `f ∈ L¹ (𝕋)` with `f̂ (k) = 0` for `k < 0` and `f̂ (0) ≠ 0` has `∫ log \|f\| ≥ log \|f̂ (0)\|`, and `log \|f\|` is integrable | [`log_norm_fourierCoeff_zero_le_integral_log_norm`](HarmonicAnalysis/Hardy/Jensen.lean#L467) | [HL1, Thm 2] (`𝕋`) | `Hardy/Jensen` |
| For `A` with entries in `L²`, the innovation of the columns of `A`: `X` with `Xᴴ X = 1` and `Xᴴ A ∈ H²`; if `A ∈ H²`, `A = X (Xᴴ A)` | [`exists_innovation`](HarmonicAnalysis/Hardy/Outer.lean#L711) | [HL2, §9] | `Hardy/Outer` |
| If `A ∈ H²`, `Aᴴ A = Bᴴ B` with `B` outer and `B̂ (0)` surjective | [`exists_isOuter`](HarmonicAnalysis/Hardy/Outer.lean#L899) | [HL2, pp. 202–203, 207] | `Hardy/Outer` |
| The range of an outer `B` is a.e. that of `B̂ (0)` | [`IsOuter.range_eq`](HarmonicAnalysis/Hardy/Outer.lean#L850) | [HL2, Thm 9] | `Hardy/Outer` |
| For an outer `B`, the closure of `{B Q}` is the set of the functions of `H²` with range in the range of `B` | [`IsOuter.exists_tendsto_iff`](HarmonicAnalysis/Hardy/Outer.lean#L935) | [HL2, Thm 10] | `Hardy/Outer` |
| For `W` positive definite a.e., with integrable entries and integrable `log det W`: `exp ((1/n) ∫ log det W) = inf ∫ (1/n) tr (e^Ψ W)` over the Hermitian trigonometric polynomials with `∫ tr Ψ = 0` | [`exp_integral_log_det_le_integral_exp`](HarmonicAnalysis/Hardy/GeometricMean.lean#L134), [`exists_integral_exp_circPoly_le`](HarmonicAnalysis/Hardy/GeometricMean.lean#L593) | [HL1, (59), Lemma 5] | `Hardy/GeometricMean` |
| **Szegő's theorem** for a positive semidefinite `W` with integrable entries: `exp ((1/n) ∫ log det W)` is the infimum of `∫ (1/n) tr (Qᴴ W Q)`, `Q` an analytic polynomial, `det Q̂ (0) = 1` (zero unless `W` is positive definite a.e. with `log det W` integrable) | [`szegoInf_eq`](HarmonicAnalysis/Hardy/Szego.lean#L610), [`posDef_of_szegoInf_pos`](HarmonicAnalysis/Hardy/Szego.lean#L669) | [HL1, Thm 8] (absolutely continuous measures) | `Hardy/Szego` |
| For such a `W`: it is positive definite a.e. with integrable `log det W` iff `W = Bᴴ B`, `B ∈ H²`, `det B̂ (0) ≠ 0`; then `B` can be chosen outer, with `∫ log \|det B\| = log \|det B̂ (0)\|` | [`exists_isOuter_of_integrable_log_det`](HarmonicAnalysis/Hardy/Szego.lean#L788), [`integrable_log_det_of_isHardyTwo`](HarmonicAnalysis/Hardy/Szego.lean#L737) | [HL1, Thm 9] | `Hardy/Szego` |
| `A ∈ H²` square, `det Â (0) ≠ 0`, is outer iff `∫ log \|det A\| = log \|det Â (0)\|` | [`isOuter_iff_integral_log_norm_det`](HarmonicAnalysis/Hardy/RangeFunction.lean#L271) | [HL2, Thm 8] | `Hardy/RangeFunction` |
| Every analytic range function is the range of a left-outer function with isometric values | [`IsAnalyticRange.exists_isometry`](HarmonicAnalysis/Hardy/RangeFunction.lean#L399) | [HL2, Thm 12] | `Hardy/RangeFunction` |
| `W = A Aᴴ`, `A ∈ H²`, iff the range of `W` is analytic and `∫ log Δ W > −∞` (any rank) | [`exists_mul_conjTranspose_eq_iff`](HarmonicAnalysis/Hardy/RangeFunction.lean#L585), [`isFactorable_iff`](HarmonicAnalysis/Hardy/RangeFunction.lean#L652) | [HL2, Thm 13]; [S, Lemma 10.1] | `Hardy/RangeFunction` |
| **Riesz factorization**: every `A ∈ H¹` with values in the `m × n` matrices is `A₁ A₂` a.e., `A₁, A₂ ∈ H²`, `A₂ᴴ A₂ = (Aᴴ A)^{1/2}`, `A₁ᴴ A₁ = A₂ A₂ᴴ`; so `‖A₁‖²_{S_{2p}} = ‖A₂‖²_{S_{2p}} = ‖A‖_{S_p}` a.e., `0 < p < ∞` | [`exists_mul_eq_of_isHardyOne`](HarmonicAnalysis/Hardy/RieszFactorization.lean#L427), [`complexSchattenNorm_sq_of_factorization`](HarmonicAnalysis/Hardy/RieszFactorization.lean#L467) | [S, Thm 4] (finite dimension) | `Hardy/RieszFactorization` |
| Paley's inequality: for `1 ≤ p ≤ 2` and every `f ∈ H¹` with values in `M_n (ℂ)` (in particular, analytic polynomials `Σ c_k e_k`), `f̂ (2^k) = a_k + b_k`, `k < K`, with `‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M ∫ ‖f‖_{S_p}`, `M` absolute | [`paley_schatten_of_isHardyOne`](HarmonicAnalysis/Paley/Schatten.lean#L725), [`paley_schatten`](HarmonicAnalysis/Paley/Schatten.lean#L759); (III.3): [`exists_integral_paleyBlockClosed_le`](HarmonicAnalysis/Paley/Schatten.lean#L448), [`exists_integral_paleyBlockOpen_le`](HarmonicAnalysis/Paley/Schatten.lean#L469); (α), (β): [`exists_mul_eq_integral_complexSchattenNorm_eq`](HarmonicAnalysis/Paley/Schatten.lean#L709) | [LPP, Thm III.1 (i)] for the Paley projection, and [LPP, Thm II.1 a) (i)] without its constant | `Paley/Schatten` |
| The lower Khintchine inequality, `1 ≤ p ≤ 2`: `A_k = a_k + b_k` with `‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M E ‖Σ ε_k A_k‖_{S_p}`, `M` absolute | [`rademacher_schatten_le`](HarmonicAnalysis/Paley/Rademacher.lean#L102) | [LPP, Cor III.4] (named for `S_p`, `1 < p < 2`; its general form covers `1 ≤ p ≤ 2`) and [LPP, Thm 0.1] (`p = 1`), with signs; [Pi, (8.4.4)] | `Paley/Rademacher` |
| **Noncommutative Khintchine inequality**: an absolute `C` such that for all `2 ≤ q < ∞` and real matrices `x_k` of any size, with `m = max (‖(Σ x_kᵀ x_k)^{1/2}‖_{S_q}, ‖(Σ x_k x_kᵀ)^{1/2}‖_{S_q})`, `m ≤ ‖Σ ε_k x_k‖_{L_q (Ω; S_q)} ≤ C √q m`; for normal `x_k` with the one square function | [`ncKhintchine`](HarmonicAnalysis/NoncommutativeKhintchine.lean#L251), [`ncKhintchine_of_normal`](HarmonicAnalysis/NoncommutativeKhintchine.lean#L267) | Lust-Piquard (1986); [LPP]; [Pi, Thm 8.4.1 (i), (8.4.5)] | `NoncommutativeKhintchine` |

All names are in the namespace [`HarmonicAnalysis`](HarmonicAnalysis), except those prefixed by `UnitAddTorus`.

## Palomar

The headline theorems are packaged for the [Palomar registry](https://palomar-registry.org) as four
entries, not submitted yet. An entry is a directory `palomar/<Entry>/`:

- `Challenge.lean` states the theorems, with `sorry` proofs and the definitions they need, importing
  only Mathlib.
- `Solution.lean` proves the same statements from the library.
- `comparator.json` configures Comparator, which checks that the Solution proves the Challenge.
- `formalization.yaml` is the metadata (sources, scope, differences from the sources).

| Entry | Theorems | Sources | Files |
| --- | --- | --- | --- |
| [`palomar/FourierMultipliers`](palomar/FourierMultipliers) | Fourier multipliers, transference, the Beurling–Ahlfors transform (below) | [HNVW], [D], [CDK] | [`Challenge.lean`](palomar/FourierMultipliers/Challenge.lean), [`Solution.lean`](palomar/FourierMultipliers/Solution.lean), [`comparator.json`](palomar/FourierMultipliers/comparator.json), [`formalization.yaml`](palomar/FourierMultipliers/formalization.yaml) |
| [`palomar/VectorValuedLittlewoodPaley`](palomar/VectorValuedLittlewoodPaley) | for functions with values in UMD spaces (below) | [HNVW], [B83], [MC] | [`Challenge.lean`](palomar/VectorValuedLittlewoodPaley/Challenge.lean), [`Solution.lean`](palomar/VectorValuedLittlewoodPaley/Solution.lean), [`comparator.json`](palomar/VectorValuedLittlewoodPaley/comparator.json), [`formalization.yaml`](palomar/VectorValuedLittlewoodPaley/formalization.yaml) |
| [`palomar/HardyFactorization`](palomar/HardyFactorization) | matrix-valued functions on `𝕋` (below) | [HL1], [HL2], [S] | [`Challenge.lean`](palomar/HardyFactorization/Challenge.lean), [`Solution.lean`](palomar/HardyFactorization/Solution.lean), [`comparator.json`](palomar/HardyFactorization/comparator.json), [`formalization.yaml`](palomar/HardyFactorization/formalization.yaml) |
| [`palomar/PaleySchatten`](palomar/PaleySchatten) | Paley's inequality in `S_p`, `1 ≤ p ≤ 2`, for functions of `H¹`; the lower Khintchine inequality in `S_p` | [LPP], [Pi] | [`Challenge.lean`](palomar/PaleySchatten/Challenge.lean), [`Solution.lean`](palomar/PaleySchatten/Solution.lean), [`comparator.json`](palomar/PaleySchatten/comparator.json), [`formalization.yaml`](palomar/PaleySchatten/formalization.yaml) |

The theorems of FourierMultipliers:

- what the norm `‖T_m‖_p` is
- `‖T_m‖_p = ‖T_m‖_{p'}`
- transference from `𝕋²` to `ℝ²`, for symbols continuous off `0` and for homogeneous ones
- `𝓑^k(∂̄^k F) = ∂^k F`
- `‖𝓑^k‖_p = ‖𝓑^k‖_{p'}`
- Dragičević's limit and lower bound for `n = 2`, with `p*`, and `‖𝓑²‖_p > p* − 1`

The theorems of VectorValuedLittlewoodPaley, for functions with values in UMD spaces:

- conjugate functions on the circle and truncated Hilbert transforms on the line
- the Hilbert transform, as a limit of truncations and as the multiplier `−i sgn`, and its bound
- the right-hand Littlewood–Paley inequalities on the line and on the circle
- transference of operator-valued multipliers from `ℝ` to `𝕋`
- Mihlin multipliers, and the Littlewood–Paley inequalities for every choice of the signs

The theorems of HardyFactorization, matrix-valued functions on `𝕋`:

- Jensen's inequality
- outer functions
- Szegő's theorem
- `W = Bᴴ B`
- analytic range functions and the factorization of any rank
- the Riesz factorization of `H¹` with its Schatten norms

The definitions in the Challenges are copies of marked blocks of [`HarmonicAnalysis/Defs.lean`](HarmonicAnalysis/Defs.lean),
[`HarmonicAnalysis/VectorValued/Defs.lean`](HarmonicAnalysis/VectorValued/Defs.lean) and [`HarmonicAnalysis/Hardy/Defs.lean`](HarmonicAnalysis/Hardy/Defs.lean), made by
[`scripts/sync_challenge_defs.py`](scripts/sync_challenge_defs.py). Those of UMD constants and of the Schatten norms are copies of the
definitions of BanachProbability, equal to them by definition ([`isUMDBound_iff`](palomar/VectorValuedLittlewoodPaley/Solution.lean#L26), [`complexSchattenNorm_eq`](palomar/HardyFactorization/Solution.lean#L23), in the
Solutions). The two-sided noncommutative Khintchine inequality ([`ncKhintchine`](HarmonicAnalysis/NoncommutativeKhintchine.lean#L251)) is not in an entry here: the entry
NoncommutativeKhintchine of [BanachProbability](https://github.com/vltanh/lean4-banach-probability) states it with an explicit constant.

## Method

The proofs follow the sources; the module docstrings say where they depart.

### Fourier multipliers, transference, the Beurling–Ahlfors transform

- **Dragičević's lower bound** follows the proof of [D, pp. 466–467], which [D-LN, Prop. 4.2] repeats,
  with the test functions of [D] `f_{n,α}(z) = z^n |z|^{−2α} g_n(|z|)` for `n = 2` and `n = 1` (here
  `0 < α < 1/p`, and the example of a cutoff in [D], `g₂ = 1` on `[0, 1]`, `g₂(x) = exp(−(x−1)²)` for
  `x > 1`, also for `n = 1`, where the example `g₁(x) = exp(−(x−1))` is not `C¹` at `1`; the cutoff
  changes no limit): `𝓑^n(∂̄^n f) = ∂^n f`, explicit integrals over the disc, of order `(1 − αp)⁻¹`,
  a bounded contribution outside it, and `α → 1/p`, by one lemma for both `n`
  ([`tendsto_eLpNorm_div_of_lintegral_ball`](HarmonicAnalysis/BeurlingAhlfors/LowerBound.lean#L141)). On the
  unit disc, `f_{1,α}(z) = z |z|^{−2α}` are the functions `f_α` of [BMS, §1], who continue them by
  `1/z̄` outside it and compute `∫ |∂f_α|^p / ∫ |∂̄f_α|^p → (p − 1)^p`. The
  norms here are suprema over Schwartz functions, which `f_{n,α}` is not; that `f_{n,α} ∈ W^{n,p}`, "which ensures
  that `T^n(∂̄^n f) = ∂^n f`", is asserted without proof in [D, p. 465] (and is [D-LN, Ex. 4.1]; for
  `n = 1`, [D-LN, Ex. 2.19]).
  What is used of it is proved here: `f_{n,α}` is approximated by Schwartz functions, and the density
  statements carry the bound over, as the hint of [D-LN, Ex. 2.19] does ("first consider smooth `h`
  and then approximate"). The approximation is the standard one: `z^n(|z|² + ε)^{−α}` near `0`, the
  cutoff smoothed near `|z| = 1` (where `g₂` is only `C¹`) and truncated at infinity, and dominated
  convergence; for `n = 1` the profiles of `n = 2` serve as they are. For `n = 1`, `p − 1 ≤ ‖𝓑‖_p`
  is half of the classical bound `‖𝓑‖_p ≥ p* − 1`, which is Lehto's [Le] (not read here); the other
  half, `‖𝓑‖_p ≥ p' − 1`, follows by `‖𝓑‖_p = ‖𝓑‖_{p'}`, and [BMS, §1] obtain it from the
  conjugates of the `f_α`. [D] states the bound for `p > 2` (its standing assumption, p. 464), and
  the argument works for every `p > 1`; the bound for `n = 2` with `p*` for `p < 2` is not in [D].
  It comes from
  `‖𝓑^n‖_p = ‖𝓑^n‖_{p'}`, by `𝓑^{−n} = (𝓑^n)^*` and `𝓑^{−n} f = conj(𝓑^n(conj f))` [CDK, §1.3.1, for
  `R^k`, `𝓑 = R²`], as here (for bounded multipliers, by the standard duality argument: the adjoint of
  `T_m` is `T_{m̄}`, and Schwartz functions norm `L^p`).
- **`‖𝓑‖_p` as the best constant of `‖∂u‖_p ≤ C ‖∂̄u‖_p` on `C_c^∞`** is stated without proof in
  [BMS, §1, remark (b)]. The bound `‖∂u‖_p ≤ ‖𝓑‖_p ‖∂̄u‖_p` is `𝓑(∂̄u) = ∂u`. The other direction
  follows Guerra's proof of Corollary 1.4 of [Gu], with the cut-offs of the proof of Corollary 1.2:
  - the dense class `C_c^∞`, and the potential of `g ∈ C_c^∞`: its Cauchy transform `f = C g`,
    with:
    - `∂̄f = g` (the Cauchy–Pompeiu formula, by polar coordinates);
    - `∂f = 𝓑g`;
    - the decay `f = O(1/|z|)`, `∂f = O(1/|z|²)` (elementary bounds; `∫ ∂g = 0`);
  - cut-offs `η_R` (`1` on the disc of radius `R`, `0` off that of radius `2R`, `|Dη_R| ≤ K/R`):
    `∂(η_R f) − ∂f = (η_R − 1) ∂f + f ∂η_R`, the first term `→ 0` in `L^p` by dominated
    convergence and the second `O(R^{2/p − 2}) → 0` since `p > 1`; the same for `∂̄`; the
    inequality for `η_R f` and `R → ∞` give `‖𝓑g‖_p ≤ C ‖g‖_p`;
  - density: `g_n = η_n g → g` in `L^p` with `𝓕g_n → 𝓕g` in `L¹`, so `𝓑g_n → 𝓑g` uniformly, and
    Fatou's lemma.

  One departure is forced: Guerra treats Hessians (a real `h`, its logarithmic potential `u`,
  `a₊ = h`, `a₋ = conj(𝒮h)` for `D²u`), while the inequality here is on `∂u`, `∂̄u` for complex
  `u`, so the potential is the Cauchy transform of a complex `g`. Guerra states three facts about
  the potential without proof, and their gradient analogues are proved here:
  - `Δu = 2h`: here `∂̄(C g) = g`;
  - the decay: here `C g = O(1/|z|)`, `∂(C g) = O(1/|z|²)`;
  - `𝒮h = 2u_{zz}`, which applies `𝒮∂̄ = ∂` to a function that is not Schwartz: here
    `∂(C g) = 𝓑g`, by Liouville's theorem, since `∂(C g) − 𝓑g` has `∂̄ = 0` and tends to `0` at
    infinity.

  Guerra's "by density" presupposes the boundedness of `𝒮` on `L^p`, which the
  library does not prove: the density step uses the convergence of the Fourier transforms in
  `L¹` and Fatou's lemma instead. A shorter route through a Fourier-supported dense class is
  recorded in [docs/SHORTER_PROOFS.md](docs/SHORTER_PROOFS.md), item 48.
- **Duality** `‖T_m‖_p = ‖T_m‖_{p'}` follows [HNVW, Prop. 5.3.7], for scalar symbols:
  - `∫ T_m f · g = ∫ T_{m(−·)} g · f`
  - Hölder's inequality
  - the norming of `L^p` by Schwartz functions
  - the reflection `T_{m(−·)}(f(−·)) = (T_m f)(−·)`
- **Transference** follows [HNVW, Prop. 5.7.4 and Cor. 5.7.6], for scalar symbols on `ℝ² ≅ ℂ` and the
  inequality from `𝕋²` to `ℝ²`: for Schwartz `f`, `g` with Fourier transforms in `C_c^∞(ℂ∖{0})`,
  `∫ T_m f g = ∫ m 𝓕f 𝓕⁻¹g` is a limit of Riemann sums over `R⁻¹ℤ²`, which by orthogonality are
  pairings of trigonometric polynomials on `𝕋²`; Hölder's inequality and [HNVW, Lemma 5.7.5] (Poisson
  summation) bound them by `‖T_{m(·/R)}‖ ‖f‖_p ‖g‖_{p'}` in the limit, and density [HNVW,
  Prop. 2.4.23 (ii)] and duality conclude. Part (i) of Prop. 2.4.23 (not used) is wrong for
  `C_c^∞(ℝ^d∖{0})`, whose functions vanish at `0`. Corrections to the printed text, all in the
  docstrings:
  - the missing hypotheses of Prop. 5.7.4 and the boundedness of `m`
  - the centred cell in Lemma 5.7.5
  - two interchanged exponents
  - the norming of `T_m f`, for which the density of the `g` in `L^{p'}` alone is not enough (here
    their Fourier transforms converge in `L¹` as well, as Prop. 2.4.23 says)
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

### Vector-valued harmonic analysis

1. *Dyadic shifts and the Hilbert transform* [HNVW, Section 5.1]. The UMD property bounds the Haar
   projections with random signs, hence the dyadic shifts; averages over translates and dilates of the
   dyadic system are convolutions, and `∫_ε^R φ_t * f dt/t` is a truncated Hilbert transform up to two
   error terms; its Fourier symbol is computed by Cauchy's theorem (Lemma 5.2.1).
2. *The Hilbert transform by a random walk* [B83]. A random walk with steps `±δ ± iδ` stopped at the exit from
   the unit disc: `u (Z_τ)` is a martingale `Σ w_k (u_x d_k + u_y e_k)` up to an error `O (δ)` in `L^p` (Taylor's
   theorem, Laplace's equation and the square function inequality for real martingales), and the martingales of `u`
   and `v` have the same decoupled sums, because `u_x = v_y`, `u_y = −v_x`; decoupling twice gives `β²`; rotations and
   `δ → 0` give the circle. Then Poisson integrals, the truncated conjugate function, and the line by M. Riesz's
   argument [R, §18]: periodization, dilation and Fatou's lemma.
3. *Littlewood–Paley on the line and on the circle* [HNVW, Sections 5.3, 5.7].
   - Intervals from the Hilbert transform (step 1), a randomised multiplier bound for `1_I / φ̂_I`
     (Lemmas 5.3.21–5.3.23), the bounds of step 1.
   - Transference by duality (Proposition 5.7.1, the direction from `ℝ` to `𝕋`), with the book's
     dilation that moves the dyadic points off the integers.
4. *Multipliers and signs* [MC]. `T_m f (x) = −32 ∫_0^∞ ∫ y² v_{yy} (s, y) u_y (x − s, 3y) ds dy` for the Poisson
   integrals `u`, `v` of `f` and `𝓕⁻ m`; the Riemann sums in `y` are expectations over two independent chains with
   Cauchy increments, in which `v_{yy}` enters through bounded coefficients (Lemma 3.1) that Burkholder's
   inequality for martingale differences removes; Lemma 3.2 and a second use of that inequality leave `f`. For the
   signs:
   - a partition of unity into Mihlin multipliers, and random Mihlin multipliers `M` with `M² = 1`
     on the supports of these multipliers
   - Burkholder's inequality for Rademacher sums
   - the Hilbert transform (step 2) for the jumps of the sign multiplier
   - transference to the circle
5. *Outer functions* [HL2, §§9–10]. For a matrix-valued function `A` with entries in `L²`, the closed span
   `M_k` of the columns of `A e_j`, `j ≥ k`; an orthonormal basis of the innovation `M_0 ⊖ M_1` is a function
   `X` with `Xᴴ X = 1`, because the Fourier coefficients of `Xᴴ X` of order `≠ 0` vanish, and `B = Xᴴ A` is
   analytic. For `A ∈ H²` there is no remote past, `A = X B`, and the functions `B Q` are dense in `H²`.
6. *Szegő's theorem* [HL1]. Jensen's inequality from the scalar case of the infimum (Theorem 2);
   `exp ((1/n) ∫ log det W)` as an infimum over Hermitian trigonometric polynomials (Lemma 5); `e^Ψ = Q Qᴴ`
   with `Q` bounded and analytic, by step 5 and Jensen's inequality for `det Q` and `det Q⁻¹` ((68)); then Fejér
   means. Theorem 9: if `log det W` is integrable, the infimum is positive, the innovation of `W^{1/2}` has full
   rank, and `W = Bᴴ B`.
7. *Range functions and Sarason's factorization* [HL2, §§10–11; S, §10]. An analytic range function is the
   range of an analytic isometry `V` (Theorem 12); `W = V (Vᴴ W V) Vᴴ` reduces the factorization of `W` to
   full rank (Theorem 13). If `A ∈ H¹` is bounded, `Aᴴ A` satisfies the conditions of Theorem 13, hence so does
   `(Aᴴ A)^{1/2}`, which is `A₂ᴴ A₂` with `A₂` outer; `A₁ = J A₂ᴴ`, with the partial isometry `J` of the
   polar decomposition, is analytic because `A₂` is outer. The general case by a scalar outer function.
8. *Paley* [LPP, pp. 249–253]. `f = g h` with `‖f‖_{L¹ (C_p)} = ‖g‖_{L² (C_{2p})} ‖h‖_{L² (C_{2p})}`; the coefficient of
   order `2^k` is split at `2^{k−1}`; Jensen's inequality in `C_p (ℓ²_R)` and `C_p (ℓ²_L)` and Hölder's inequality
   reduce the theorem to (III.1), which follows from (I.7), (III.2), and from (III.3): for every choice of the signs
   the blocks `Σ ε_k H_{2^k}` are bounded by `h` in `L² (𝕋; C_{2p})`, by step 4 for the UMD space `C_{2p}`.
9. *Khintchine* [LPP, pp. 243, 246–248, 254–255; Pi, p. 106]. The lower bound is (I.7). For the
   upper bound:
   - averaging over signs
   - duality of rows and columns
   - the Rademacher projection on `L_{q'} (S_{q'})`, bounded by a multiple of `√q` because `S_q` has
     type 2 with constant at most `√(q + 1)` (BanachProbability, after Tomczak-Jaegermann and
     [HNVW II])

| Source | Used for | Departures and completions |
| --- | --- | --- |
| [HNVW], [HNVW II] | I, Sections 5.1–5.3, 5.7; Props 1.2.22, 1.3.1, 3.2.10, 4.2.3, Lemma 2.4.8, Cor 4.5.15; II, Thm 6.1.13 | finitely many generations, and others (below) |
| [HL1] | Theorem 2, (58), (59), Lemma 5, Lemma 6, (68), Theorem 8 for absolutely continuous measures, Theorem 9 | columns instead of rows, and others (below) |
| [HL2] | §9, Theorems 8, 9, 10, 12, 13 | columns instead of rows, and others (below) |
| [S] | §10: Theorem 4, Lemmas 10.1, 10.3, 10.4 | finite dimension, and others (below) |
| [LPP] | Theorem III.1 (i), Corollary III.4, pp. 254–255, (I.1)–(I.3) (trace form), (I.5), (I.7), the dualities of p. 246, (I.12), first half | (III.3) by [MC, Thm 1.3], and others (below) |
| [B83] | Lemmas 1–4, (2), (9), (33) (below) | UMD constants in place of ζ-convexity, and others (below) |
| [MC] | Theorem 1.1 and Theorem 1.3 (UMD ⇒ (1.13)), for `n = 1`; (2.1), Lemmas 2.1, 2.2, 3.1, 3.2 | the facts on Brownian motion, and others (below) |
| [Pi] | pp. 105–106, `√q` | the type 2 constant for all `q ≥ 2` (the source has even `q`) |
| [R] | §18, pp. 234–235: the passage from Theorem II on the circle to Theorem VII on the line, for [B83, Lemma 4] | the truncated conjugate functions, and others (below) |

[HNVW], [HNVW II], departures and completions:

- Finitely many generations.
- The bounds are uniform in the truncation and the limit is taken on the Fourier side by Fatou's
  lemma, instead of the convergence of the averaged shifts in `L^p` (Lemmas 5.1.8, 5.1.12).
- The random dyadic systems are translates of the standard one.
- The randomised UMD property is used directly on unit intervals instead of Theorem 4.2.13; for the
  left half of Prop 5.1.5, the martingale of the shifts.
- Real signs, so the contraction principle costs a factor.
- Lemma 5.3.21 only for scalar weights equal up to dilation, with the `L¹` norm of the derivative,
  bounded by `π²` where Lemma 5.3.23 has `2π`.
- In Cor 5.3.25 the signs `±` are split first, by reflection, and its dilates give the finite sums
  of Thm 5.3.24.
- Continuity at the integers instead of Lebesgue points in Prop 5.7.1.
- Minkowski's inequality by a weighted Jensen inequality.

[HL1], departures and completions:

- Columns instead of rows and the usual trace.
- The space `L²_W` is realized in `L²` by `W^{1/2}`.
- The limiting process for `∫ log det W = −∞` is carried out once, for the infimum of Theorem 8 (in
  Theorem 2, for the inequality itself).
- In the proof of Lemma 2, which Lemma 5 repeats, the one of the truncations `min (u, n)`,
  `min (v, n)` with the larger integral is scaled, since for these the source's "there is an `m`"
  fails when the positive part is bounded and the negative part is not.
- Fejér means along a subsequence that converges almost everywhere.
- Of Theorem 1 only (23), with bounded instead of continuous analytic functions.
- `B` is determined up to a constant unitary factor, so `det Q̂ (0) = 1` by a constant of modulus
  `1`.

[HL2], departures and completions:

- Columns instead of rows, transposition instead of `Ã (e^{ix}) = A (e^{−ix})*`.
- That `B` has full rank by the argument of p. 207, whose last step (a factor of `W` with `r`
  columns makes the rank of the process at most `r`) is proved here because the source does not.
- In Theorem 8 the infimum (44) is computed from the limit `A₀`, not from the element of smallest
  norm.
- Theorem 12 with isometries (partial isometries in the statement); in its proof, range `V` = range
  `B` because `D` is invertible; `U` with `rank U` columns.
- In the necessity of Theorem 13, `V` is an isometry, not shown to be left-outer (the source says
  this is true but not easy to prove, p. 208), and the integrability is that of [HL1, Thm 9], not
  Theorem 8.
- (131) lacks two logarithms.

[S], departures and completions:

- Finite dimension (Lemmas 10.2 and 10.5 are not included); there, and for `Â (0)` non-singular, the
  factorization `A = A₁ A₂` is [HL1, Thm 10].
- Lemma 10.3, quoted from Helson's book in the source, from [HL2, §§9–10]; "conjugate analytic",
  not defined there, is defined.
- The partial isometry `J` by an explicit formula, which makes it measurable, and `Jᴴ J A₂ᴴ = A₂ᴴ`
  by computation.
- Szegő's theorem and the quotient by an outer function, quoted from Hoffman's book in the source,
  from [HL1, Thm 9] and the argument of Theorem 4.
- The norm of `A (z)` in the weight is the sum of the `|a_{ij}|`.

[LPP], departures and completions:

- (III.3) by [MC, Thm 1.3], the second reference of the source, in place of Bourgain's version of
  the Marcinkiewicz theorem, the values `ε_ℓ + ε_{ℓ+1}` at `2^ℓ` by a combination of multipliers
  with blocks closed on one side.
- Only the sequence `2^k`.
- [LPP] recall that `C_{2p}` is UMD, with Cotlar's trick as a known argument: the fact is proved in
  BanachProbability by Randrianantoanina's theorem.
- `H²` is defined by the vanishing of the Fourier coefficients.
- `p = 1` by the proof of Theorem III.1.
- The maximum of the two norms in place of the norm of `C_q (ℓ²_S)`.
- Real matrices in the final theorem.

[B83], used for:

- Lemmas 2–4, (33), (2)
- (9) for `ℝ`, which p. 275 asserts without proof, by the argument of Lemma 1 (pp. 277–278) for
  `B = ℝ` and Khintchine's inequality
- Lemma 1 from BanachProbability, by the source's argument

[B83], departures and completions:

- UMD constants in place of ζ-convexity ((8) and its constant; Theorem 1 only for `ℝ`, in (9), and
  replaced, see below).
- Explicit constants, by Minkowski's inequality where the source integrates `p`-th powers in the
  rotation `α`.
- In (9), `‖S (f)‖_p ≤ κ_{2,p} (p* − 1) ‖f‖_p` and `‖f‖_p ≤ κ_{p,2} (p* − 1) ‖S (f)‖_p`, with the
  Kahane–Khintchine constants `κ`, and (20), stated with `2 (p* − 1)`, is derived for `p < 2` from
  `p = 2`.
- The signs as coordinates of a cube and of an infinite product.
- Lemma 4 by [R, §18], see below.
- In place of Theorem 2 (`H f = lim H_ε f` in `L^p` and almost everywhere) the limit on the
  functions `𝓕⁻ G ∈ L^p`, `G ∈ L¹`, from [HNVW, Lemma 5.2.1].
- `β = ∞` is treated apart.
- Corrections: `≤` in the Taylor estimate (p. 279), `N² δ² w_k` for `k² δ²` (p. 280).

[MC], departures and completions:

- The facts on Brownian motion, (2.1), (3.4) and the Hilbert transform as below.
- Poisson integrals by their Fourier transforms, (2.7) on the Fourier side.
- Lemma 3.1 without its two cases.
- `f = 𝓕⁻ G`, `G ∈ L¹`, in place of test functions with finite-dimensional values.
- `m` complex and `C²` on `ℝ ∖ {0}`, without mollification.
- The estimate (3.6) after the integration in `s`.
- Finite parts of the sums `m_i`, `M`, with one function `ρ`, `ρ = 1` on `[3/4, 2]`.
- Corrections:
  - the limit of `g_N` (pp. 747–748)
  - the starting height on p. 751
  - (3.19)
  - `φ = 1` near `3/2`

[R], departures and completions:

- The truncated conjugate functions and (33) in place of the conjugate functions and Theorem II.
- (38) for `|x| + ε < nπ`.
- "`lim f̃_n (x) = f̃ (x)`", which the source leaves out, by dominated convergence.
- Fatou's lemma also as `m → ∞`.

Facts that [B83] and [MC] recall, or state without proof, and the arguments used for them:

| Step | Fact | Cited work | Read | Argument here |
| --- | --- | --- | --- | --- |
| [B83] (9), p. 275 | "(8) implies (9)" where Khintchine's inequality is valid | none | — | the argument of Lemma 1 (pp. 277–278) for `B = ℝ`, with Khintchine's inequality at each point |
| [B83] (9), p. 275 | (8) for `B = ℝ`: "By Theorem 1, inequality (8) does hold" | Theorem 1; Burkholder, Ann. Probab. 9 (1981) (below) | read for BanachProbability; not followed | BanachProbability's `p* − 1` inequality, `dyadicUMDConst_le_of_innerProductSpace` (Burkholder's inequality, by the proof of Theorem 3.5 of Osękowski's book) |
| [B83] (9), p. 275 | Khintchine's inequality for real Rademacher sums | none | — | BanachProbability's Kahane–Khintchine inequality between `p` and `2` ([HNVW II, Thm 6.2.4], by hypercontractivity), and the orthonormality of the signs |
| [B83] p. 279 | the Taylor estimate, the third derivatives of `Re z^k`, `Im z^k` bounded by `k³ 2^{k−3}` | Taylor's theorem | — | the remainder of the Taylor polynomial of `z^k`, by induction on `k` |
| [B83] (29), pp. 281–282 | two transformations of the signs have the same distribution | none | — | the average over the cube is invariant under their composition |
| [B83] Lemma 3, p. 283 | "Just as in the real-valued case, `u − u (0)` and `v` are the uniform limits on the circle `\|z\| = r` of functions of the form (18) and (19)" | none | — | the geometric series: the kernels are `1 + 2 Re (z / (1 − z))` and `2 Im (z / (1 − z))`, and `z / (1 − z)` is the uniform limit on `\|z\| = r` of `Σ_{k=1}^N z^k` |
| [B83] (33), p. 283 | "there is a nonnegative function `K_r`" with two properties | none | — | `K_r` is the modulus of the difference of the two kernels, and its integral is computed |
| [B83] Lemma 4, p. 283 | "This follows from (33) just as it does in the real case" | [R] and Zygmund's *Trigonometric series* ([B83, refs 14, 18]) | [R]; Zygmund not consulted | [R, §18], for the truncations (below) |
| [MC] (2.1), p. 743 | Burkholder's inequality for transforms by predictable coefficients bounded by one | Burkholder, Ann. Probab. 9 (1981) ([MC, ref. 5]) | read for BanachProbability; not followed | from the definition of a UMD constant, for deterministic coefficients, which are convex combinations of signs (BanachProbability, after [HNVW, Thm 4.2.25]); complex ones by real and imaginary parts |
| [MC] §2, pp. 743–745 | the place `X (y)` where Brownian motion first hits the height `y` (below) | Itô–McKean, Neveu, Doob (1957) ([MC, refs 12, 18, 7]); for Lemma 2.3, Sharpe (1980) ([MC, ref. 21]) | not consulted | chains with independent Cauchy increments (below) |
| [MC] (3.4), p. 746 | the semigroup property of the Poisson integral | none | — | on the Fourier side |
| [MC] pp. 741, 754 | the Hilbert transform is bounded on `L^p (ℝ; B)` for ζ-convex `B` | [B83] ([MC, ref. 6]) | read | [B83], Lemmas 2–4, and not [MC, Remark 3.1] |

The cited work for [B83] (9), p. 275, (8) for `B = ℝ`:

- Theorem 1, which combines Theorems 2.1 (p. 1001) and 3.1 (p. 1003) of Burkholder, Ann. Probab. 9
  (1981), [B83, ref. 3]; (8) from ζ-convexity is Theorem 3.1, since (8) is UMD.
- [B83] gives no reference for the proof of Theorem 1; it says the theorem extends results of [4]
  and points to [3] for "other such extensions" (p. 275), and to "[3 and 5]" for "other properties
  and all the proofs" of the ζ-condition (p. 272); it cites `ℝ ∈ UMD` to [4], Burkholder (1966)
  (p. 271).

The argument here for [B83] Lemma 4, p. 283:

- [R, §18], for the truncations: (38), the limit `n → ∞`, Theorem II (here (33)) with the dilation,
  Fatou's lemma as `n → ∞` for fixed `m`, then `m → ∞`, for which [R] gives no reason (here Fatou's
  lemma again)
- "`lim f̃_n (x) = f̃ (x)`", which [R] leaves out ("Nous ne nous y arrêtons pas"), by dominated
  convergence, with `|cot u| ≤ |u|⁻¹` for `|u| ≤ 2` and Hölder's inequality

The fact of [MC] §2, pp. 743–745, on the place `X (y)` where Brownian motion first hits the height
`y`:

- the Cauchy laws (2.2)
- independent increments
- Lemma 2.3 (proved there, with Sharpe [21])
- Doob's conditioned processes
- (2.3)
- (2.4)

The argument here for [MC] §2, pp. 743–745:

- The finite-dimensional distributions as the definition: chains with independent Cauchy
  increments.
- (2.3) with (2.6) by the reversal of the chains.
- (2.4) is not needed.

Not consulted:

- Hoffman's *Banach spaces of analytic functions* and Helson's *Lectures on invariant subspaces*
  (cited in [S])
- Wiener (1955)
- Wiener and Masani (1957, 1958)
- Lust-Piquard (1986)
- Bourgain (1986)

For [B83] and [MC], see the table above.

## Planned extensions

- Dragičević's bound `‖𝓑^n‖_p ≥ κ_n(p)` for every `n`; here for `n = 1` (`‖𝓑‖_p ≥ p − 1`, half of
  Lehto's `‖𝓑‖_p ≥ p* − 1`) and `n = 2`.
- General dimension: `EuclideanSpace ℝ (Fin d)` and `UnitAddTorus (Fin d)`; also for the vector-valued part.
- The other inequalities of [HNVW, Cor. 5.7.6]: `‖T_m‖_{L^p_0(𝕋²)} ≤ ‖T_m‖_{L^p(𝕋²)} ≤ ‖T_m‖_{L^p(ℝ²)}`.
- From [HNVW], vector-valued:
  - the dyadic shifts for all generations and all admissible kernels, and their convergence
  - the Hilbert transform as a limit in `L^p`
  - the extension of the inequalities on the line from `𝓕⁻ L¹ ∩ L^p` to `L^p (ℝ; X)`, and from
    finite to infinite Littlewood–Paley sums
  - the left-hand Littlewood–Paley inequalities and the operator-valued statement of Theorem
    5.7.10 (1)
  - Mihlin's theorem with first derivatives (5.3.18) and the Marcinkiewicz theorem
  - complex Rademacher variables
- From [B83]:
  - Theorem 2 (singular integrals, the limit of `H_ε f` almost everywhere and in `L^p`, the maximal
    function)
  - ζ-convexity (Theorem 1)
  - Bourgain's converse
- From [MC]:
  - dimension `n > 1`
  - Theorem 1.2
  - the converse of Theorem 1.3
  - predictable coefficients in (2.1)
- From [HL1], [HL2] and [S]:
  - the singular part of a matrix-valued measure in [HL1, Thm 8]
  - [HL2, corollary of Thm 10, Thms 11, 14–17]
  - Lemmas 10.2 and 10.5 of [S] (infinite dimension)
- From [LPP]:
  - the easy inequality (I.14) in Corollary III.4
  - the constant `1 + √2` and the other parts of Theorem II.1
  - Corollaries 0.2 and 0.4
  - general `H¹–ℓ²` multipliers
  - Theorem III.1 (ii)–(iii), III.5–III.7
  - the appendix
  - general `C_E`
  - infinite dimension
  - complex and rectangular matrices in the Khintchine inequality

## Shorter proofs

Shorter arguments than the sources' are in [docs/SHORTER_PROOFS.md](docs/SHORTER_PROOFS.md), with their
scope and status. The main ones:

| Result | Shorter proof | Status |
| --- | --- | --- |
| transference `𝕋² → ℝ²` [HNVW, Cor. 5.7.6] | Riemann sums and Fatou's lemma (Igari) | Lean, in the history at `bf215c5` |
| Littlewood–Paley on `𝕋` [HNVW, Thm 5.7.10], transference | a cut-off with compactly supported Fourier transform (the argument of [HNVW, Prop. 5.2.5]), exact for multipliers locally constant at the frequencies | Lean, in the history at `d0d081b` |
| the factorization `f = g h` in Paley's inequality | [BX, Thms 3.1, 3.4] for analytic polynomials, with `‖h‖²_{S_{2p}} ≤ ‖f‖_{S_p} + δ`: 762 lines in place of about 5 600 | Lean, in the history at `3ecee00` |
| [HL1, Thms 8, 9] | Jensen's inequality for the determinants of the Fejér means, without Lemmas 4–5 and (68) | on paper |
| [LPP, (III.3)], on average over the signs, which is all that (III.2) uses | the Littlewood–Paley inequality [HNVW, Thm 5.7.10] and the randomised boundedness of single frequencies | Lean, in the history at `ec00cb2` |
| [LPP, (III.3)] | the UMD inequality itself, on `𝕋ⁿ` with independent unimodular variables in place of `e^{i 2^k t}` | on paper |
| noncommutative Khintchine, upper bound | exchangeable pairs (Mackey–Jordan–Chen–Farrell–Tropp), constant `√(2 (q − 1))` | Lean, `BanachProbability.ncKhintchine_upper` |
| the Hilbert transform on UMD spaces [B83] | the dyadic shifts of [HNVW, Section 5.1], with a larger constant: about 1 840 lines in place of about 3 800; for the multiplier `sgn`, with a large constant, Theorem 1.1 of [MC] | Lean, the first in the library, the second compiled |
| Paley and the lower Khintchine inequality for `p = 1` | any factorization in `L² (S_2)` and nested orthogonal projections (Fournier) | on paper |

## Literature

As of 22 November 2026; preprints are reported as claimed. Keys in brackets are in
[docs/REFERENCES.md](docs/REFERENCES.md), as are the full references of the articles linked in the table
of the vector-valued part.

### Fourier multipliers and the Beurling–Ahlfors transform

- **Transference.** Restriction from `ℝ` to `𝕋` is de Leeuw's [dL, Prop. 3.3]. The converse used
  here, `‖m‖_{M_p(ℝ)} ≤ lim_{λ→0} ‖(m(λn))_n‖_{M_p(ℤ)}`, is Igari's ([I, Thm 2], for `1 ≤ p ≤ 2`, by
  Riemann sums and Fatou's lemma; from Igari's lectures of 1968), and Jodeit [J, p. 215] states that a
  symbol continuous off `0` and homogeneous of degree `0` is a multiplier on `ℝ^N` iff its
  restriction to `ℤ^N` is one. Equality of the norms, mean-zero functions included, is in
  [GMS, Lemma 2.2] (smooth symbols, vector-valued) and [HNVW, Cor. 5.7.6] (operator-valued symbols,
  continuous off `0`).
- **`‖𝓑‖_p`.** `≥ p* − 1` is Lehto's [Le]; Iwaniec [Iw] conjectured equality. Uniform upper bounds:
  - `4(p* − 1)` [BW]
  - `2(p* − 1)` [NV]
  - `1.575(p* − 1)` [BJ]
  - `1.523958(p* − 1)`, claimed in a manuscript of
    [Tencent-Hunyuan/Hyra-results](https://github.com/Tencent-Hunyuan/Hyra-results) (2026)
  - the conjecture, claimed in the preprint [arXiv:2609.28311](https://arxiv.org/abs/2609.28311)
    (v2, October 2026)
- **`‖𝓑^n‖_p`.**
  - Of order `n^{1−2/p*}(p* − 1)` ([DPV]; the lower bound completed in [D]).
  - `≥ κ_n(p)` for `p > 2` [D]; the same for all powers of the complex Riesz transform [CDK].
  - The conjecture `‖𝓑^n‖_p = κ_n(p)`, `p ≥ 2` ([D, Conj. 1.2]), is open for `n ≥ 2` as far as we
    found; [arXiv:2609.28311](https://arxiv.org/abs/2609.28311) concerns `n = 1`.
- **Other formalizations of `𝓑`** (all Lean 4).
  - Bounded on `L^p`, `1 < p < ∞`:
    [will1491/no-wandering-domains](https://github.com/will1491/no-wandering-domains)
    ([arXiv:2609.16027](https://arxiv.org/abs/2609.16027); the singular integral, through the
    Carleson project's Calderón–Zygmund theory) and
    [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) (the multiplier, through
    Mihlin–Hörmander; it also has `𝓑∂̄ = ∂` and the Fourier symbols of `∂`, `∂̄` on Schwartz
    functions).
  - `L²` isometry: [openai/math](https://github.com/openai/math),
    [Tencent-Hunyuan/Hyra-results](https://github.com/Tencent-Hunyuan/Hyra-results) (which also has
    certificates for parts of its manuscript).
  - Lehto's bound, the bound `1.575(p* − 1)` and Iwaniec's conjecture are stated, not proved, in
    [facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean).
- **Other overlaps.**
  - Poisson summation on lattices of `ℝ^n` for Schwartz functions: at least five Lean projects of
    2026, among them [CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB),
    [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem) and
    TauCeti (Mathlib: only on `ℝ`).
  - Fourier series and `∂̄` of smooth functions on tori, and `L²` multipliers: TauCeti.
  - Mathlib has Fourier multipliers with smooth symbols of temperate growth, on Schwartz functions
    and tempered distributions, and no `L^p` bounds for `p ≠ 2`.
  - The Isabelle AFP, MathComp-Analysis and HOL Light have no multiplier theory that we found.
- **Transference elsewhere in Lean.** Magyar–Stein–Wainger's transference from `ℝ` to `ℤ`, for
  variation norms, is in
  [PALOMAR-2026-11-17-000007](https://palomar-registry.org/entry?id=PALOMAR-2026-11-17-000007&version=1);
  `L^p` transference from `ℝ^d` to `𝕋^d` for scalar symbols, up to a constant (18 November 2026), in
  [matthewrosenzweigwork-max/Riesz-Gases](https://github.com/matthewrosenzweigwork-max/Riesz-Gases).
- **New here, as far as we found:**
  - `L^p` transference of Fourier multipliers from the torus to `ℝ²`
  - lower bounds for `‖𝓑²‖_p`
  - the isometric duality `‖T_m‖_p = ‖T_m‖_{p'}`
  - the `L^p` asymptotics of periodisations [HNVW, Lemma 5.7.5] and the density of the Schwartz
    functions with Fourier transform in `C_c^∞(ℝ^d∖{0})` [HNVW, Prop. 2.4.23 (ii)]
  - the corrections to HNVW listed under Method

### Vector-valued harmonic analysis

`β` is the UMD constant of `X` (real signs), `ħ` the norm of the Hilbert transform on `L^p (ℝ; X)`.

| Result | Origin | Later; state of the question |
| --- | --- | --- |
| Hilbert transform, UMD spaces | scalar: M. Riesz (1928), and others (below) | both quadratic bounds are sharp up to constants, according to [Lorist–van Neerven (2026)](https://arxiv.org/abs/2609.10444), preprint; linear comparison with a dyadic operator: Domelevo–Petermichl ([2022](https://arxiv.org/abs/2212.00090), [2023](https://arxiv.org/abs/2303.12480), [2026](https://arxiv.org/abs/2604.11273)), preprints |
| Littlewood–Paley and Mihlin multipliers, UMD spaces | scalar, on the circle: Littlewood–Paley ([1931](https://doi.org/10.1112/jlms/s1-6.3.230), [1936](https://doi.org/10.1112/plms/s2-42.1.52)); UMD: [McConnell (1984)](https://doi.org/10.1090/s0002-9947-1984-0752501-x), [Bourgain (1986)](https://zbmath.org/?q=an:0602.42015) | operator-valued symbols: Weis (2001), and others (below) |
| Transference `ℝ → 𝕋` | [de Leeuw (1965)](https://doi.org/10.2307/1970621) | operator-valued symbols: see [HNVW I (2016)](https://doi.org/10.1007/978-3-319-48520-1), Prop 5.7.1 |
| Szegő and Riesz factorization | scalar: Szegő (1921), F. Riesz (1923), and others (below) | subdiagonal algebras: Arveson (1967), Marsalli–West (1998), and others (below) |
| Paley's inequality | Paley (1933), and others (below) | `p = 1` without analytic factorization: [Fournier (2014)](https://arxiv.org/abs/1407.2578), preprint; discrete groups: [Chuah–Han–Liu–Mei (2022)](https://doi.org/10.1007/s00041-022-09971-1) |
| Noncommutative Khintchine | `1 < p < ∞`: Lust-Piquard (1986), and others (below) | best constants at even `q`: Buchholz (2001, 2005), and others (below) |
| Type 2 of `S_q`, K-convexity (from BanachProbability) | [Tomczak-Jaegermann (1974)](https://zbmath.org/?q=an:0282.46016); [Maurey–Pisier (1976)](https://doi.org/10.4064/sm-58-1-45-90) | optimal 2-uniform smoothness: [Ball–Carlen–Lieb (1994)](https://doi.org/10.1007/BF01231769); K-convex ⇔ non-trivial type: [Pisier (1982)](https://doi.org/10.2307/1971396) |

Hilbert transform, UMD spaces, origin:

- scalar: [M. Riesz (1928)](https://doi.org/10.1007/BF01171098) (read: §18 is followed for
  [B83, Lemma 4])
- UMD ⇒ bounded: [Burkholder (1983)](https://doi.org/10.1007/978-1-4419-7245-3_26) (`ħ ≤ β²`,
  according to [HNVW, p. 469])
- bounded ⇒ UMD, `β ≤ ħ²`: [Bourgain (1983)](https://doi.org/10.1007/BF02384306)
- by transformations of the Haar system:
  [Figiel (1991)](https://doi.org/10.1017/cbo9780511662317.010),
  [Petermichl (2000)](https://doi.org/10.1016/s0764-4442%2800%2900162-2),
  [Petermichl–Pott (2003)](https://doi.org/10.1090/s0002-9939-03-06925-9),
  [Hytönen (2008)](https://doi.org/10.1016/j.crma.2008.09.021)

Littlewood–Paley and Mihlin multipliers, UMD spaces, later:

- operator-valued symbols: [Weis (2001)](https://doi.org/10.1007/PL00004457)
- on the circle: [Arendt–Bu (2002)](https://doi.org/10.1007/s002090100384)
- monograph: [HNVW I (2016)](https://doi.org/10.1007/978-3-319-48520-1)

Szegő and Riesz factorization, origin:

- scalar: [Szegő (1921)](https://doi.org/10.1007/bf01459407),
  [F. Riesz (1923)](https://doi.org/10.1007/bf01192397)
- matrices: [Wiener (1955)](https://doi.org/10.1007/bf02564273),
  [Wiener–Masani (1957)](https://doi.org/10.1007/BF02404472), Helson–Lowdenslager
  ([1958](https://doi.org/10.1007/bf02392425), [1961](https://doi.org/10.1007/BF02545786))
- operators: [Devinatz (1961)](https://doi.org/10.2307/1970313),
  [Sarason (1967)](https://doi.org/10.1090/s0002-9947-1967-0208383-8)

Szegő and Riesz factorization, later:

- subdiagonal algebras: [Arveson (1967)](https://doi.org/10.2307/2373237),
  [Marsalli–West (1998)](https://zbmath.org/?q=an:1001.46041)
- outer factorization for `log |f|` integrable:
  [Blecher–Labuschagne (2008)](https://doi.org/10.1090/S0002-9947-08-04506-6)
- all `0 < p ≤ ∞`: [Bekjan–Xu (2009)](https://arxiv.org/abs/0705.1947)

Paley's inequality, origin:

- [Paley (1933)](https://doi.org/10.2307/1968183)
- vector-valued, including `S_1`:
  [Blasco–Pełczyński (1991)](https://doi.org/10.1090/s0002-9947-1991-0979957-5)
- with the row-plus-column norm in `S_p`: [LPP (1991)](https://doi.org/10.1007/BF02384340)

Noncommutative Khintchine, origin:

- `1 < p < ∞`: [Lust-Piquard (1986)](https://zbmath.org/?q=an:0592.47038)
- `p = 1`: [LPP (1991)](https://doi.org/10.1007/BF02384340)
- order `√q`: implicit in LPP, explicit in
  [Pisier (1998)](https://www.numdam.org/item/AST_1998__247__R1_0/) and, independently,
  [Junge (1996)](docs/REFERENCES.md)
- best possible: [Pisier–Xu (2003)](https://doi.org/10.1016/s1874-5849%2803%2980041-4)

Noncommutative Khintchine, later:

- best constants at even `q`: Buchholz ([2001](https://doi.org/10.1007/PL00004425),
  [2005](https://doi.org/10.4064/ba53-3-9))
- `√(q − 1)` for Hermitian matrices, `q = 2` or `q ≥ 3`:
  [Mackey et al. (2014)](https://doi.org/10.1214/13-AOP892)
- `p = 1`, best constant for `e^{i 2^n t}`:
  [Haagerup–Musat (2007)](https://doi.org/10.1016/j.jfa.2007.05.014), for signs claimed by
  [Chuah–Liu–Mei (2026)](https://arxiv.org/abs/2503.03187v4), preprint
- `p < 1`: [Pisier–Ricard (2017)](https://doi.org/10.1017/s1474748015000353)
- interpolation spaces: [Cadilhac (2019)](https://doi.org/10.1016/j.aim.2019.06.002)

### Related formalizations of the vector-valued part

Searched on 22 November 2026:

- GitHub repository and code search (Lean, Isabelle, Rocq, HOL Light, HOL4)
- the Mathlib source
- the Palomar registry
- the Archive of Formal Proofs
- the Lean Zulip archive
- arXiv

Third-party code was read as text (documentation and statements); none of it was built or audited.
The projects are in Lean 4 unless said otherwise.

| Project | Overlap | Not seen there |
| --- | --- | --- |
| [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | Mihlin–Hörmander for values in complex Hilbert spaces, and others (below) | UMD spaces, and others (below) |
| [elorist/UMD_Hilberttransform](https://github.com/elorist/UMD_Hilberttransform) | Hilbert and UMD constants of explicit spaces at `p = 2`, and others (below) | the Hilbert transform on a general UMD space; the comparison for `p ≠ 2` |
| [tchen-research/NLAlib](https://github.com/tchen-research/NLAlib) | Khintchine's upper bound in `S_{2p}`, `p ∈ ℕ`, with `√(2p − 1)`, for complex Hermitian matrices, signs or Gaussians; 2-uniform smoothness of `S_{2r}` | other exponents, and others (below) |
| [xf-shi/Tensor_Norm](https://github.com/xf-shi/Tensor_Norm), [BuxinSu/LearningTheoryFormalizations](https://github.com/BuxinSu/LearningTheoryFormalizations) | an `L¹` Khintchine inequality for Haar unitary coefficients, with the row-plus-column norm; matrix Khintchine in operator norm with `√log` of the dimension | signs (first); dimension-free constants (second) |
| [openai/math](https://github.com/openai/math) | type `p > 1` ⇒ K-convex (Pisier's theorem); scalar Littlewood–Paley estimates | the constant from type 2 |
| [SHW715/HardySpace_formalization](https://github.com/SHW715/HardySpace_formalization), [michael-haufschild-gib/hgt](https://github.com/michael-haufschild-gib/hgt), [bjbraams/lean-CA](https://github.com/bjbraams/lean-CA) | Hardy spaces of the disc; canonical, inner–outer and Riesz factorization of scalar functions | matrix-valued factorization |
| [matthewrosenzweigwork-max/Riesz-Gases](https://github.com/matthewrosenzweigwork-max/Riesz-Gases) | `L^p` transference from `ℝ^d` to `𝕋^d` for scalar symbols, up to a constant | operator-valued symbols, the same norm |
| [roos-j/lean-variationalsw](https://github.com/roos-j/lean-variationalsw), [LeanPool/lean-pool](https://github.com/LeanPool/lean-pool), [fpvandoorn/carleson](https://github.com/fpvandoorn/carleson), [janbernloehr/diss-lean](https://github.com/janbernloehr/diss-lean) | Littlewood–Paley, scalar and `ℓ²`-valued (lean-variationalsw), and others (below) | values in general Banach or UMD spaces, random signs, sharp cut-offs |
| Mathlib | Fourier multipliers on Schwartz functions and tempered distributions, singular values | Hilbert transforms, and others (below) |
| [Archive of Formal Proofs](https://www.isa-afp.org) (Isabelle), [MathComp-Analysis](https://github.com/math-comp/analysis) (Rocq), [HOL Light](https://github.com/jrh13/hol-light), [HOL4](https://github.com/HOL-Theorem-Prover/HOL) | Fourier series, martingales, the Hardy–Littlewood maximal function | all the results above |

TauCetiProject/TauCeti, overlap:

- for values in complex Hilbert spaces:
  - Mihlin–Hörmander (operator-valued symbols in finite dimension)
  - Riesz and Hilbert transforms on `L^p`
  - both Littlewood–Paley inequalities with smooth cut-offs
- `H²` of `ℂ^r`-valued functions, block Toeplitz operators
- type and cotype of Hilbert spaces
- `p* − 1` for signed scalar Haar sums

TauCetiProject/TauCeti, not seen there:

- UMD spaces
- sharp cut-offs
- transference
- factorization
- Khintchine in `S_q` (a target with `sorry` in
  [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap))

elorist/UMD_Hilberttransform, overlap:

- Hilbert and UMD constants of explicit `2^n`-dimensional spaces, `p = 2`
- dyadic reduction of the UMD constant at `p = 2`
- scalar Hilbert transform on `L^{3/2}`, `L³`, `L⁴`

tchen-research/NLAlib, not seen there:

- other exponents
- non-Hermitian matrices
- the lower bound
- `p < 2`

roos-j/lean-variationalsw, LeanPool/lean-pool, fpvandoorn/carleson, janbernloehr/diss-lean, overlap:

- Littlewood–Paley, scalar and `ℓ²`-valued (lean-variationalsw)
- scalar Hilbert transform (`L²`, weak type `(1, 1)`)
- discrete Hilbert transform on `ℓ^p`

Mathlib, not seen there:

- Hilbert transforms
- UMD spaces
- Hardy spaces
- Schatten norms
- Khintchine's inequality
- Littlewood–Paley theory

Not found elsewhere in these searches:

- the Hilbert transform, Mihlin's multiplier theorem and Littlewood–Paley inequalities for general
  UMD spaces
- dyadic shifts on UMD spaces
- transference of operator-valued multipliers with the same norm
- Szegő's theorem and the Szegő and Riesz factorization of matrix-valued functions
- Paley's inequality, scalar or in the Schatten classes
- the lower Khintchine inequality in `S_p` for signs and `1 ≤ p ≤ 2`
- the two-sided inequality for all real `q ≥ 2` and real matrices that need not be symmetric (also
  in BanachProbability, with another proof of the upper bound)

## Using it from another Lake project

```toml
[[require]]
name = "HarmonicAnalysis"
git = "https://github.com/vltanh/lean4-harmonic-analysis"
rev = "<commit>"
```

Then import the modules you need, for instance `public import HarmonicAnalysis.BeurlingAhlfors.LowerBound`,
or `import HarmonicAnalysis` for everything. The package requires Lean and Mathlib `v4.36.0-rc2`
(your project should use the same Mathlib version) and
[BanachProbability](https://github.com/vltanh/lean4-banach-probability), at the commit in the
[lakefile](lakefile.toml), which only the vector-valued modules import.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build                         # the library and the Palomar entries (whose Challenges have `sorry`s)
lake env lean scripts/Audit.lean   # axioms: fails on any `sorry` or non-standard axiom
# Comparator (needs bubblewrap): the Solution of an entry proves its Challenge's statements
lake env lake comparator --config=palomar/FourierMultipliers/comparator.json   # and the other entries
```

## Layout

| Path | Content |
| --- | --- |
| [`HarmonicAnalysis/Defs.lean`](HarmonicAnalysis/Defs.lean) | the definitions that the headline theorems of the scalar part use |
| [`HarmonicAnalysis/Complex/`](HarmonicAnalysis/Complex) | Wirtinger derivatives, radial integrals, the Cauchy transform, Liouville (below) |
| [`HarmonicAnalysis/FourierMultiplier/`](HarmonicAnalysis/FourierMultiplier) | multipliers, density, norming, duality, extension (below) |
| [`HarmonicAnalysis/Torus/`](HarmonicAnalysis/Torus) | periodic functions, trigonometric polynomials, Poisson summation, smooth periodic functions (below) |
| [`HarmonicAnalysis/Transference/`](HarmonicAnalysis/Transference) | `RiemannSum`, `ContinuousSymbol` (symbols continuous off `0`), `Homogeneous` (symbols homogeneous of degree `0`) |
| [`HarmonicAnalysis/VectorValued/`](HarmonicAnalysis/VectorValued) | the vector-valued part (below) |
| [`HarmonicAnalysis/Hardy/`](HarmonicAnalysis/Hardy) | matrix-valued Hardy functions (below) |
| [`HarmonicAnalysis/Paley/`](HarmonicAnalysis/Paley), [`HarmonicAnalysis/NoncommutativeKhintchine.lean`](HarmonicAnalysis/NoncommutativeKhintchine.lean) | Paley's inequality in the Schatten classes, its form for signs, the noncommutative Khintchine inequality |
| [`HarmonicAnalysis/BeurlingAhlfors/`](HarmonicAnalysis/BeurlingAhlfors) | the Beurling–Ahlfors transform (below) |
| [`palomar/`](palomar) | the four Palomar entries |
| [`docs/`](docs) | references, shorter proofs |
| [`scripts/`](scripts) | the axiom audit and other tools (below) |
| [`.github/workflows/`](.github/workflows) | CI and Palomar's preflight (below) |

[`HarmonicAnalysis/Complex/`](HarmonicAnalysis/Complex):

- `Wirtinger` (`∂`, `∂̄` on functions and on `𝓢(ℂ, F)`, symbols, conjugation)
- `WirtingerRadial` (`∂`, `∂̄` of `z^a z̄^b K(|z|²)`)
- `RadialIntegral` (radial integrals)
- `CauchyTransform` (the Cauchy transform `(1/π) ∫ g(w)/(z − w) dw`: smoothness, derivatives, decay)
- `CauchyPompeiu` (`C(∂̄g) = g`)
- `Liouville` (`∂̄u = 0` and `u → 0` at infinity imply `u = 0`)

[`HarmonicAnalysis/FourierMultiplier/`](HarmonicAnalysis/FourierMultiplier):

- `Basic` ([`fourierMultiplier`](HarmonicAnalysis/Defs.lean#L56),
  [`multiplierNorm`](HarmonicAnalysis/Defs.lean#L61), density)
- `Density` (mollifiers, the Schwartz functions with Fourier transform supported off `0`)
- `Norming` (`L^p` norms by Schwartz test functions)
- `Duality`
- `Extension` (`T_m` as an operator on `L^p`)
- `CompactSupport` (cut-offs of Schwartz functions, with `L¹` convergence of the Fourier transforms)

[`HarmonicAnalysis/Torus/`](HarmonicAnalysis/Torus):

- `Cube` (periodic functions, the unit cube, `𝕋² ↔ ℂ`)
- `Lattice` (the lattice `ℤ + iℤ`, the tiling of `ℂ` by cells, periodic functions on `𝕋²`)
- `TrigPoly` (trigonometric polynomials, [`torusMultiplierNorm`](HarmonicAnalysis/Defs.lean#L88),
  orthogonality)
- `Poisson` (periodisation, Poisson summation on `ℤ²`, the `L^p` norms of the periodisations)
- `Lipschitz` (Fourier coefficients over the unit cube, Parseval, derivatives of Lipschitz periodic
  functions)
- `Smooth` (smooth periodic functions: rapid decay, Fourier series, multipliers `T_m`, Wirtinger
  derivatives, `∂̄⁻¹`)

[`HarmonicAnalysis/VectorValued/`](HarmonicAnalysis/VectorValued):

- `Defs` (the definitions that the headline theorems use)
- `CircPoly` (trigonometric polynomials on the circle)
- `RademacherNorm`
- `Common` (lemmas shared by the route of [HNVW] and that of [B83] and [MC], so that the second does
  not import the first)
- `Dyadic/` (martingales, shifts, averages)
- `HilbertTransform/` (truncations, the symbol, the bound by dyadic shifts)
- `Burkholder/` (conjugate functions, the Hilbert transform)
- [`Transference`](HarmonicAnalysis/VectorValued/Transference.lean) (`ℝ → 𝕋`)
- `LittlewoodPaley/` (line, circle; `Signs`, `CircleSigns`: every choice of the signs)
- `McConnell/` (Poisson kernel, chains, Mihlin multipliers)

[`HarmonicAnalysis/Hardy/`](HarmonicAnalysis/Hardy):

- `Defs` (the definitions that the headline theorems use)
- `Basic` (`H²`, Fourier coefficients)
- `Approximation` (`H¹`, Fejér means, products)
- `FunctionalCalculus` (functions of Hermitian functions)
- `GeometricMean`
- `Jensen`
- `Outer`
- `Szego`
- `RangeFunction`
- `RieszFactorization`

[`HarmonicAnalysis/BeurlingAhlfors/`](HarmonicAnalysis/BeurlingAhlfors):

- `Basic` (symbol, `𝓑^k`, `𝓑^k ∂̄^k = ∂^k`, density)
- `Duality`
- `TestFunctions` (Dragičević's `f_{2,α}`; with `TestFunctions/Profile`, one-variable calculus, and
  `TestFunctions/Approx`, its Schwartz approximations)
- `TestFunctions/One` (Dragičević's `f_{1,α}`, with the cutoff `g₂`, and its Schwartz
  approximations)
- `LowerBound` (Dragičević, `n = 1` and `n = 2`)
- [`Transference`](HarmonicAnalysis/BeurlingAhlfors/Transference.lean) (`𝓑^k` on `𝕋²`)
- `Periodic` (`𝓑` on smooth periodic functions)
- `Regularity` (`𝓑g` differentiable, `∂̄(𝓑g) = ∂g`, `𝓑g → 0` at infinity)
- `CauchyTransform` (`∂̄(C g) = g`, `∂(C g) = 𝓑g` for `g ∈ C_c^∞`)
- `CompactSupport` (cut-offs; `‖𝓑‖_p` as the best constant of `‖∂u‖_p ≤ C ‖∂̄u‖_p` on `C_c^∞`)

[`scripts/`](scripts):

- [`Audit.lean`](scripts/Audit.lean) (the axiom audit)
- [`sync_challenge_defs.py`](scripts/sync_challenge_defs.py) (the Challenges' copies of the
  definitions)
- [`check_md_tables.py`](scripts/check_md_tables.py)
- tools for checking files and statements

[`.github/workflows/`](.github/workflows):

- CI:
  - build
  - audit
  - import lists of the audit and of the root module
  - the Challenges' copies of the definitions
  - the links of the documents
  - Markdown tables
  - line lengths
- Palomar's preflight, run by hand

## References

In [docs/REFERENCES.md](docs/REFERENCES.md).

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
