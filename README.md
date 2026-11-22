# VectorValuedHarmonicAnalysis

A Lean 4 library of harmonic analysis for functions with values in Banach spaces:

- the Hilbert transform and the Littlewood–Paley inequality for UMD spaces, on the line and on the
  circle, with the transference of Fourier multipliers from the line to the circle;
- matrix-valued Hardy functions on the circle: Szegő and Riesz factorization;
- Paley's inequality in the Schatten classes and the noncommutative Khintchine inequality, along the
  route of Lust-Piquard and Pisier, with constants `1` and `C √q`.

**Status.** Every result below is proved, and no theorem takes an unproved result as a hypothesis. The
library builds with no `sorry` and no axiom beyond Lean's standard [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and
[`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound); [`scripts/Audit.lean`](scripts/Audit.lean) checks this for every declaration and fails otherwise.

**Not formalized, planned extensions.** From HNVW I: the dyadic shifts for all generations and all
admissible kernels, and their convergence; the Hilbert transform as a limit in `L^p`; the extension of the
inequalities on the line from `𝓕⁻ L¹ ∩ L^p` to `L^p (ℝ; X)`, and from finite to infinite Littlewood–Paley
sums (with the intervals inside `(−1, 1)`); the left-hand Littlewood–Paley inequalities and the
operator-valued statement of Theorem 5.7.10 (1); Mihlin's theorem (5.3.18) and the Marcinkiewicz theorem;
several variables; complex Rademacher variables. From Lust-Piquard and Pisier: the easy inequality (I.14)
in Corollary III.4, the constant `1 + √2` and the other parts of Theorem II.1, Corollaries 0.2 and 0.4,
general `H¹–ℓ²` multipliers, Theorem III.1 (ii)–(iii), III.5–III.7, the appendix, general `C_E`, `H^p (X)`
beyond what the factorization needs, infinite dimension; complex and rectangular matrices in the final
theorem.

## Results

`X` is a complex Banach space and `β` a `UMD_p` constant of `X`
(`BanachProbability.IsUMDBound X p β`, real signs), `1 < p < ∞`, `ε_k` are independent fair signs,
`𝕋 = ℝ / ℤ` with its normalised Haar measure, `e_n (t) = e^{2πi n t}`; [`eLpNormRad`](VectorValuedHarmonicAnalysis/RademacherNorm.lean#L47) is the norm of a
Rademacher sum `Σ_k ε_k f_k` in `L^p` of the product with the signs; `C_p = S_p` are the Schatten
classes of complex matrices, of every size. All declarations are in the namespace
[`VectorValuedHarmonicAnalysis`](VectorValuedHarmonicAnalysis); modules are relative to [`VectorValuedHarmonicAnalysis/`](VectorValuedHarmonicAnalysis). HNVW is
Hytönen–van Neerven–Veraar–Weis, *Analysis in Banach Spaces*, LPP is Lust-Piquard–Pisier (1991); the
full references are in [docs/REFERENCES.md](docs/REFERENCES.md).

| Theorem | Lean | Source | Module |
| --- | --- | --- | --- |
| Dyadic averages on the line form a martingale on each unit interval; the parts `S_j`, `0 ≤ j < n`, of the dyadic shift with the kernel `h` or (5.19): `‖Σ_j ε_j S_j f‖_p ≤ 2β ‖f‖_p`, and `‖Σ_j S_j f‖_p ≤ 2β² ‖f‖_p` for (5.19) | [`martingale_dyadicAvg`](VectorValuedHarmonicAnalysis/Dyadic/Martingale.lean#L185), [`eLpNormRad_dyadicShift_le`](VectorValuedHarmonicAnalysis/Dyadic/Shift.lean#L176), [`eLpNorm_sum_dyadicShift_le`](VectorValuedHarmonicAnalysis/Dyadic/Shift.lean#L258) | HNVW I, Props 5.1.4, 5.1.5 | `Dyadic/Martingale`, `Dyadic/Shift` |
| Averaging over translates gives a convolution: `∫_0^1 S_j (f (· + u)) (· − u) du = φ_{2^{−j}} * f`, `φ (x) = ∫ k (x + u) h (u) du` for a kernel `k`; hence `‖Σ_j ε_j φ_{2^{−j}} * f‖_p ≤ 2β ‖f‖_p` for `k = h`, and `‖Σ_j φ_{t 2^{−j}} * f‖_p ≤ 2β² ‖f‖_p` for `k` of (5.19) and `t > 0` | [`intervalIntegral_dyadicShift_translate`](VectorValuedHarmonicAnalysis/Dyadic/Average.lean#L339), [`eLpNormRad_dilateConv_le`](VectorValuedHarmonicAnalysis/Dyadic/Average.lean#L402), [`eLpNorm_sum_dilateConv_le`](VectorValuedHarmonicAnalysis/Dyadic/Average.lean#L472) | HNVW I, Lemma 5.1.9, Prop 5.1.10 | `Dyadic/Average` |
| Hilbert transform: the truncations `H_{ε, 2^n ε}` are bounded on `L^p (ℝ; X)` by `4β² + 11`; their symbols are `−i sgn (ξ) m_{ε,R} (ξ)` with `\|m_{ε,R}\| ≤ 2`, `m_{ε,R} → 1`; hence `‖𝓕⁻ (sgn · G)‖_p ≤ (4β² + 11) ‖𝓕⁻ G‖_p` for `G ∈ L¹` | [`eLpNorm_truncatedHilbert_le`](VectorValuedHarmonicAnalysis/HilbertTransform/Truncated.lean#L600), [`truncatedHilbert_fourierInv`](VectorValuedHarmonicAnalysis/HilbertTransform/Fourier.lean#L410), [`abs_hilbertSymbol_le`](VectorValuedHarmonicAnalysis/HilbertTransform/Fourier.lean#L209), [`tendsto_hilbertSymbol`](VectorValuedHarmonicAnalysis/HilbertTransform/Fourier.lean#L237), [`eLpNorm_fourierInv_sign_le`](VectorValuedHarmonicAnalysis/HilbertTransform/Fourier.lean#L555) | HNVW I, Thm 5.1.13, Lemma 5.2.1, Prop 5.2.2 | `HilbertTransform/Truncated`, `HilbertTransform/Fourier` |
| Littlewood–Paley on the line, for the intervals `(2^{k−1}, 2^k)`, `−(2^{k−1}, 2^k)`, `(−1, 1)`, `0 < k ≤ K`, and `f = 𝓕⁻ G`, `G ∈ L¹`: `‖Σ ε_k Δ_k f‖_p ≤ C_β ‖f‖_p` | [`eLpNormRad_fourierInv_indicator_le`](VectorValuedHarmonicAnalysis/LittlewoodPaley/Line.lean#L822), [`eLpNormRad_lineBlock_le`](VectorValuedHarmonicAnalysis/LittlewoodPaley/Line.lean#L1096) | HNVW I, Thm 5.3.24 and Cor 5.3.25, right-hand inequalities | `LittlewoodPaley/Line` |
| Transference: if `T_m`, with a bounded operator-valued symbol `m` such that each `m (·) x` is strongly measurable, and continuous at the integers, is bounded from `L^p (ℝ; X)` to `L^p (ℝ; Y)` with norm `C`, then so is its restriction to `ℤ`, from `L^p (𝕋; X)` to `L^p (𝕋; Y)` | [`eLpNorm_trigPoly_multiplier_le`](VectorValuedHarmonicAnalysis/Transference.lean#L1064); Lemmas 5.7.2, 5.7.3: [`tendsto_integral_dilate_multiplier`](VectorValuedHarmonicAnalysis/Transference.lean#L558), [`tendsto_eLpNorm_dilate_smul`](VectorValuedHarmonicAnalysis/Transference.lean#L320) | HNVW I, Prop 5.7.1 (`d = 1`) | `Transference` |
| Littlewood–Paley on the circle, for the dyadic blocks `Ĩ_k ⊂ ℤ`, `\|k\| ≤ K`, and trigonometric polynomials: `‖Σ ε_k Δ̃_k f‖_{L^p (Ω × 𝕋; X)} ≤ C_β ‖f‖_{L^p (𝕋; X)}` | [`eLpNormRad_dyadicBlock_le`](VectorValuedHarmonicAnalysis/LittlewoodPaley/Circle.lean#L383), [`eLpNormRad_dyadicBlock_succ_le`](VectorValuedHarmonicAnalysis/LittlewoodPaley/Circle.lean#L371) | HNVW I, Thm 5.7.10 (2), right-hand inequality | `LittlewoodPaley/Circle` |
| Szegő factorization: a continuous invertible `a : 𝕋 → M_n (ℂ)` is `Ψ h` a.e., `Ψ` unitary-valued, `h, h⁻¹ ∈ H²` | [`exists_szego_factorization`](VectorValuedHarmonicAnalysis/Hardy/Factorization.lean#L475) | Bekjan–Xu (2009), Thm 3.1 | `Hardy/Factorization` |
| Riesz factorization: an analytic matrix polynomial is `f = g h` a.e., `g, h ∈ H²`, with `‖g (t)‖²_{S_{2p}} ≤ ‖f (t)‖_{S_p}` and `‖h (t)‖²_{S_{2p}} ≤ ‖f (t)‖_{S_p} + δ` for a.e. `t` and all `p ≥ 1` | [`exists_riesz_factorization`](VectorValuedHarmonicAnalysis/Hardy/Factorization.lean#L732) | Sarason (1967); Bekjan–Xu (2009), Thm 3.4 | `Hardy/Factorization` |
| Paley's inequality: for `1 ≤ p ≤ 2` and every analytic polynomial `f = Σ c_k e_k` with `c_k ∈ M_n (ℂ)`, `c_{2^k} = a_k + b_k` with `‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M ∫ ‖f‖_{S_p}`, `M` absolute | [`paley_schatten`](VectorValuedHarmonicAnalysis/Paley/Schatten.lean#L828) | LPP, Thm III.1 (i) for the Paley projection, and Thm II.1 without its constant | `Paley/Schatten` |
| The lower Khintchine inequality, `1 ≤ p ≤ 2`: `A_k = a_k + b_k` with `‖(Σ a_k a_kᴴ)^{1/2}‖_{S_p} + ‖(Σ b_kᴴ b_k)^{1/2}‖_{S_p} ≤ M E ‖Σ ε_k A_k‖_{S_p}`, `M` absolute | [`rademacher_schatten_le`](VectorValuedHarmonicAnalysis/Paley/Rademacher.lean#L96) | LPP, Cor III.4 (`1 < p < 2`) and Thm 0.1 (`p = 1`), with signs; Pisier (1998), (8.4.4) | `Paley/Rademacher` |
| **Noncommutative Khintchine inequality**: an absolute `C` such that for all `2 ≤ q < ∞` and real matrices `x_k` of any size, with `m = max (‖(Σ x_kᵀ x_k)^{1/2}‖_{S_q}, ‖(Σ x_k x_kᵀ)^{1/2}‖_{S_q})`, `m ≤ ‖Σ ε_k x_k‖_{L_q (Ω; S_q)} ≤ C √q m`; for normal `x_k` with the one square function | [`ncKhintchine`](VectorValuedHarmonicAnalysis/NoncommutativeKhintchine.lean#L249), [`ncKhintchine_of_normal`](VectorValuedHarmonicAnalysis/NoncommutativeKhintchine.lean#L279) | Lust-Piquard (1986); LPP; Pisier (1998), Thm 8.4.1 (i), (8.4.5) | `NoncommutativeKhintchine` |

The library uses [BanachProbability](https://github.com/vltanh/lean4-banach-probability) (UMD
constants; Schatten norms of real and complex matrices, Hölder's inequality; Kahane's contraction
principle; type 2 of `S_q` and K-convexity; norming elements) and
[HarmonicAnalysis](https://github.com/vltanh/lean4-harmonic-analysis) (a weighted form of
Jensen's inequality).

## Method

The proofs follow the sources; the module docstrings say where they depart. In order:

1. *Dyadic shifts and the Hilbert transform* (HNVW I, Section 5.1). The UMD property bounds the Haar
   projections with random signs, hence the dyadic shifts; averages over translates and dilates of the
   dyadic system are convolutions, and `∫_ε^R φ_t * f dt/t` is a truncated Hilbert transform up to two
   error terms; its Fourier symbol is computed by Cauchy's theorem (Lemma 5.2.1).
2. *Littlewood–Paley on the line and on the circle* (HNVW I, Sections 5.3, 5.7). Intervals from the
   Hilbert transform, a randomised multiplier bound for `1_I / φ̂_I` (Lemmas 5.3.21–5.3.23), the bounds of
   step 1; transference by duality, with the book's dilation that moves the dyadic points off the integers.
3. *Factorization* (Bekjan–Xu, Section 3, after Arveson). Project `a` onto the closure of `a A_0` in
   `L²`; the difference `y` has `yᴴ y` constant; `Ψ` is its unitary part, `h = Ψᴴ a`.
4. *Paley* (LPP, pp. 249–253). `f = g h`; the coefficient of order `2^k` is split at `2^{k−1}`; Jensen's
   inequality in `C_p (ℓ²_R)` and `C_p (ℓ²_L)`, Hölder's inequality, (I.7) and step 2 for the UMD space
   `C_{2p}`.
5. *Khintchine* (LPP, pp. 243, 254–255; Pisier 1998, p. 106). Averaging over signs; duality; the Rademacher
   projection on `L_q (S_q)` is bounded by a multiple of `√q`, because `S_q` has type 2 with constant at
   most `√(q + 1)` (BanachProbability).

### Sources

| Source | Read | Used for | Departures and completions |
| --- | --- | --- | --- |
| HNVW I (2016), II (2017) | the books | I, Sections 5.1–5.3, 5.7; Props 1.2.22, 1.3.1, 3.2.10, Lemma 2.4.8; II, Thm 6.1.13 | finitely many generations; the bounds are uniform in the truncation and the limit is taken on the Fourier side by Fatou's lemma, instead of the convergence of the averaged shifts in `L^p` (Lemmas 5.1.8, 5.1.12); the random dyadic systems are translates of the standard one; the randomised UMD property is used directly on unit intervals instead of Theorem 4.2.13; for the left half of Prop 5.1.5, the martingale of the shifts; real signs, so the contraction principle costs a factor; Lemma 5.3.21 only for scalar weights equal up to dilation, with the `L¹` norm of the derivative; in Cor 5.3.25 the signs `±` are split first, by reflection; continuity at the integers instead of Lebesgue points in Prop 5.7.1; Minkowski's inequality by a weighted Jensen inequality |
| Bekjan–Xu (2009) | arXiv:0705.1947 | Theorems 3.1, 3.4 | matrix case, `p = q = 2`, continuous `a`; `Φ (h) Φ (h⁻¹) = 1` is replaced by an explicit inverse, and (3.2), (3.3) and Proposition 3.3 are not needed; pointwise bounds, which give the mixed norms that LPP need; `f` an analytic polynomial |
| LPP (1991) | Ark. Mat. 29 | Theorem III.1 (i), Corollary III.4, pp. 254–255, (I.1)–(I.7) | (III.3) on average over the signs, from HNVW I, Theorem 5.7.10, instead of Bourgain's theorem for every choice of signs; the UMD property of `C_{2p}` from noncommutative martingale transforms (Randrianantoanina), instead of Cotlar's identity; a factorization up to a factor `2` instead of the equality (β), p. 252; `H²` is defined by the vanishing of the Fourier coefficients; `p = 1` by the proof of Theorem III.1; symmetric matrices and the Hermitian dilation in the duality step |
| Pisier (1998) | Numdam, `AST_1998__247__R1_0` | pp. 105–106, `√q` | the type 2 constant for all `q ≥ 2` (the source has even `q`) |

Not consulted: Lust-Piquard (1986), Sarason (1967), Helson–Lowdenslager (1958), Arveson (1967),
Bourgain (1986).

## Literature

*(Placeholder: a dated literature search for this package has not been made; the items below are the
references whose bibliographic data were checked on Crossref, zbMATH or arXiv on 2026-11-22.)*

| Result | Origin |
| --- | --- |
| Hilbert transform for UMD spaces; dyadic shifts | Burkholder (1983), Bourgain (1983); Petermichl (2000), Hytönen (2008); HNVW (2016) |
| Vector-valued multipliers and Littlewood–Paley | McConnell (1984), Bourgain (1986); HNVW (2016) |
| Factorization | Helson–Lowdenslager (1958), Sarason (1967), Arveson (1967); Bekjan–Xu (2009) |
| Paley's inequality | Paley (1933); vector-valued: Blasco–Pełczyński (1991); in the Schatten classes: LPP |
| Noncommutative Khintchine | Lust-Piquard (1986); LPP (`p = 1`); Pisier (1998), Pisier–Xu (2003); best constants for even `q`: Buchholz (2001, 2005); by exchangeable pairs: Mackey et al. (2014) |

**Related formalizations.** *(Placeholder: only those found in searches made on 2026-11-22 for the
noncommutative Khintchine inequality and UMD constants; not searched for the other topics.)*
[elorist/UMD_Hilberttransform](https://github.com/elorist/UMD_Hilberttransform) (Hilbert and UMD constants
of explicit spaces, `p = 2`);
[BuxinSu/LearningTheoryFormalizations](https://github.com/BuxinSu/LearningTheoryFormalizations) and
[xf-shi/Tensor_Norm](https://github.com/xf-shi/Tensor_Norm) (matrix Khintchine with a logarithm of the
dimension; an `L¹` inequality with Haar unitary coefficients). Mathlib has no Hilbert transform, UMD
space, Hardy space or Schatten norm.

## Shorter proofs

Shorter arguments than the sources' were noticed; they are in
[docs/SHORTER_PROOFS.md](docs/SHORTER_PROOFS.md), with their scope and status. The main ones:

| Result | Shorter proof | Status |
| --- | --- | --- |
| noncommutative Khintchine, upper bound | exchangeable pairs (Mackey–Jordan–Chen–Farrell–Tropp), constant `√(2 (q − 1))` | Lean, `BanachProbability.ncKhintchine_upper` |
| HNVW I, Theorem 5.7.10, transference | a cut-off with compactly supported Fourier transform (the argument of HNVW I, Prop 5.2.5), exact for multipliers locally constant at the frequencies | Lean, in the history at `d0d081b` |
| LPP, (III.3) | the UMD inequality itself, on `𝕋ⁿ` with independent unimodular variables in place of `e^{i 2^k t}` | on paper |

## Using the library

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`, the module system. In a [`lakefile.toml`](lakefile.toml), with `<commit>`
replaced by the full hash of the commit to use *(placeholder: not published yet)*:

```toml
[[require]]
name = "VectorValuedHarmonicAnalysis"
git = "https://github.com/vltanh/lean4-vector-valued-harmonic-analysis"
rev = "<commit>"
```

Build with `lake build`; audit the axioms with `lake env lean scripts/Audit.lean`.

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## Licence

Apache 2.0 ([`LICENSE`](LICENSE)).
