# Shorter proofs

Arguments shorter than those of the sources, noticed while following them. The library follows the
sources up to the departures stated in the module docstrings (and, for the vector-valued part, in the
table of sources of the [README](../README.md), "Method"); the items with the status "in the library" are
among them. Status:

- "in the library"
- "history" (proved in this repository at the commit named, replaced since by the source's proof;
  the paths there are those of the commit)
- "compiled" (checked by Lean, not kept)
- "Lean elsewhere"
- "on paper" (written out or sketched, not compiled)

References are in [REFERENCES.md](REFERENCES.md).

## Fourier multipliers and transference

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 1 | [HNVW, Cor. 5.7.6], `I ≤ II` | the torus series with coefficients `R⁻² m(n) 𝓕f(n/R)`, `n ≠ 0`, at `x/R` are, up to the term `n = 0`, Riemann sums of `T_m f(x)`, and Fatou's lemma concludes, with no second test function, duality or density on `ℝ²`; the torus bound is extended to absolutely summable coefficients instead. This is Igari's proof of his Theorem 2 [I], there for `f ∈ C_c^∞(ℝ)` and the full norm on `𝕋`; here for Schwartz `f` and mean-zero polynomials | history (`bf215c5`) |
| 2 | [HNVW, Prop. 5.7.4] | `g` can be any Schwartz function, since `m 𝓕f 𝓕⁻¹g` is already continuous with compact support and the mean of the (then infinite, absolutely convergent) sum `Σ_n 𝓕g(n/R) e_n` plays no role; this removes the density step for `g` and the correction on norming | on paper |
| 3 | [HNVW, Prop. 2.4.23 (ii)] | `‖h‖_p ≤ ‖h‖_1^{1/p} ‖h‖_∞^{1−1/p}` gives the `L^p` limits from `‖𝓕f_j − 𝓕f‖_1 → 0` and `‖ϕ_t ∗ f‖_1 ≤ ‖ϕ‖_1 ‖f‖_1` | on paper |

## The Hilbert transform and Littlewood–Paley theory

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 4 | [HNVW, Thm 5.7.10 (2)], transference of Littlewood–Paley inequalities | `θ` a Schwartz function whose Fourier transform has compact support; `1_{I_k}` acts on `θ (ε·) f (ρ·)` exactly for small `ε`, and Lemma 5.7.3 on both sides gives the inequality without duality. This is the book's own argument for the Hilbert transform (Proposition 5.2.5, Lemma 5.2.6). Scope: multipliers locally constant at the points of `ρ · supp f̂` | history (`d0d081b`) |
| 5 | [HNVW, Thm 5.1.13], the symbol of `∫_0^∞ φ_t * f dt/t` | `φ̂ (ξ) = 2i sin³ θ sin² (θ/2) / θ²`, `θ = πξ/2`, so the symbol of `∫_ε^R φ_t * f dt/t` is `2i ∫_{εθ}^{Rθ} sin³ s sin² (s/2) s⁻³ ds`, absolutely convergent, with limit `i (π/8) sgn ξ`; that the constant is not `0` follows from `s⁻³ = ½ ∫_0^∞ u² e^{−su} du`. No kernel identity (5.23), no Cauchy integral | on paper |
| 6 | [HNVW, Lemma 5.2.1] | on the half circle only `cos ≤ 0` is needed for the bound `π`, and the limit at `∞` is dominated convergence: no inequality of Jordan | on paper (about 45 lines less) |
| 7 | [HNVW, Lemma 5.3.23] | `\|(1/φ̂)'\| ≤ π²` on `[1/2, 1]` from `sin² t ≥ 2t/π` and `t ≤ tan t`, and integrate it, instead of the bound `2π` "by elementary calculus" | in the library |
| 8 | [HNVW, Lemma 5.7.3], `w` integrable and `f` continuous | Riemann–Lebesgue for `e_n`, then uniform approximation by trigonometric polynomials; more general in `w` (the book: `w = \|φ\|^p`, `φ` Schwartz), less general in `f` (the book: `f ∈ L^p`), and no shorter | history (`d0d081b`) |
| 9 | Minkowski's integral inequality | weighted Jensen inequality with the weight `a (y) = ‖h (·, y)‖_p` and the function `h / a` | in the library |
| 10 | [HNVW, Props 5.1.4, 5.1.5], finitely many generations | the randomised UMD property applied directly to the dyadic martingale on each unit interval, instead of Theorem 4.2.13 and the equality of laws; for the left half of 5.1.5, to the martingale of the shifts | in the library |
| 11 | [HNVW, Thm 5.1.13], for the Fourier multiplier `sgn` | bound the truncations `H_{ε, 2^n ε}` uniformly, with the error terms by Young's inequality, and pass to the limit on the Fourier side with Fatou's lemma; no maximal function, no convergence in `L^p` | in the library |

## Matrix-valued Hardy functions

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 12 | the factorization `f = g h` that Paley's inequality needs, (α) and (β) of [LPP], p. 252 | [BX, Thms 3.1, 3.4] for `L^∞ (𝕋; M_n)`: for `a = (fᴴ f + η²)^{1/4}`, let `x` be the projection of `a` on the closure of `a A_0` in `L²` and `y = a − x`; `yᴴ y` is constant; `Ψ` is the unitary part of `y`, `h = Ψᴴ a`, `g = f h⁻¹`. 762 lines in place of the theory of outer functions, Szegő's theorem and range functions (about 5 600 lines). Scope: `f` an analytic polynomial, and `‖h‖²_{S_{2p}} ≤ ‖f‖_{S_p} + δ` in place of the equality, which is enough for Paley's inequality | history (`3ecee00`, `VectorValuedHarmonicAnalysis/Hardy/Factorization.lean`) |
| 13 | [BX, Thm 3.1], matrix case | any `B` with `D = Bᴴ B` may replace the positive square root of `D = yᴴ y`; and `Φ (h⁻¹) = D^{−1/2}` is explicit, so `Φ (h) Φ (h⁻¹) = 1`, (3.2) and (3.3) are not needed | the second in the history (`3ecee00`), the first on paper |
| 14 | [HL1, Thm 2], polynomials | Jensen's formula (the Mahler measure) instead of Theorem 1 of the source, which names it on p. 192 as the alternative; the general case needs only polynomials | history (`1fecd57`) |
| 15 | [HL1, Lemma 5] | cut `log W` at `±N` and add the constant `λ_N` that makes `∫ tr` zero: `Ψ_N = λ_N − clamp (log W)`; no normalization, no splitting into positive and negative parts, and no gap in the source's choice of the truncations | on paper (about 100 lines less) |
| 16 | [HL1, Lemma 6], the function `B` is outer ((77) and p. 194) | the argument of [HL2, p. 203], by density in `H²`, uses only that the entries of `A` are in `L²`, not that `A` is analytic: it can be applied to `A = W^{1/2}`, and the argument of p. 194 ([`isOuter_conjTranspose_mul`](../HarmonicAnalysis/Hardy/Outer.lean#L747)), used also for the extremal problem of [HL2, Thm 8], is not needed | on paper |
| 17 | [HL1, Thms 8, 9] without Lemmas 4–5 and (68) | for `B ∈ H²` with `det B̂ (0) ≠ 0`, apply Jensen's inequality for polynomials (Jensen's formula, item 14, which does not use Lemma 5) to `det (σ_N B)`, `σ_N B` the Fejér means, and pass to the limit (`log \|det M\| ≤ ½ tr Mᴴ M`, reverse Fatou): this is the necessity of Theorem 9 with (76). "≥" in Theorem 8 makes the infimum positive, Lemma 6 gives an outer `B`, and (76) gives "≤" | on paper |
| 18 | [HL2, §§9–10], the function `B` with `Bᴴ B = Aᴴ A` is outer, and `B̂ (0)` is surjective | `A (1 + P_N) → X B̂ (0)` multiplied by `Xᴴ` (p. 194 of the first paper), instead of the density of the functions `Q A` (p. 203); and the rank of `B̂ (0)` directly, instead of the contradiction of p. 207, also if `A` is not analytic: the components of the columns of `A` orthogonal to the future span the innovation; or, from the density of p. 203, `B d_N → 1` for analytic polynomials `d_N`, hence `B̂ (0) d̂_N (0) → 1` | history (`1fecd57`; the last argument `72d9c71`) |
| 19 | [HL2, Thm 12] | for `A ∈ H²` the innovation `X` is already an analytic isometry with the range of `A`: the functions `B`, `D̃` and `V = B D̃⁻¹` of (136)–(138) are not needed | compiled (12 lines) |
| 20 | [HL2, Thm 8] | from `A = X B` (`X` is square because `det Â (0) ≠ 0`), `\|det X\| = 1`: the equality says `\|det X̂ (0)\| = 1`, so `X̂ (0)` is unitary and `X` is constant | on paper |
| 21 | [S, Thm 4] | `A₁ = A A₂ᴴ (A₂ A₂ᴴ)⁻¹` directly: `A₁ᴴ A₁ = A₂ A₂ᴴ` in one line, and `A₁ A₂ = A` because `A` vanishes on the kernel of `A₂`; no partial isometry | compiled |
| 22 | [S, Lemma 10.4], unbounded `A` | apply Lemma 10.1 to `(Aᴴ A)^{1/2}` with the range function of `(h² A)ᴴ` and `log Δ` up to the rank times `log \|h\|²`; no division by `h` | on paper |

## Paley's and Khintchine's inequalities

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 23 | noncommutative Khintchine, upper bound, real matrices, `q ≥ 2` | exchangeable pairs (Mackey–Jordan–Chen–Farrell–Tropp 2014), then the Hermitian dilation: constant `√(2 (q − 1))`, about 500 lines in place of the route of [LPP] and [Pi] | Lean elsewhere (`BanachProbability.ncKhintchine_upper`) |
| 24 | `p = 1`: [LPP, Thm II.1 a) (i)] and the lower Khintchine inequality in `S_1` | Fournier (2014, preprint): `f = h* g` with `g, h ∈ L² (S_2)` (any factorization), and the orthogonal projections of `g` and of `h` onto nested closed spaces spanned by functions `w h b`, `w` in a block of Walsh functions (or frequencies) and `b` a bounded operator; the coefficient of `w_{2^j}` splits into two terms by the orthogonality of the projections, with the constant `2`. No analytic factorization, no Littlewood–Paley theory. Scope: `p = 1` only (the orthogonality is that of `L² (S_2)`), signs, or frequencies with `k_{j+1} > 2 k_j` (so `2^k` only after a splitting into two sequences); not compared in detail with the proofs here | on paper |
| 25 | [LPP, Thm III.1 (i)] for the Paley projection, (III.3) | independent unimodular variables on `𝕋ⁿ` (below) | on paper (identity checked numerically, `n = 2, 3`) |
| 26 | [LPP, Thm III.1 (i)] for a lacunary sequence | `n_k = 2^{k+1} − 1` in place of `2^k` (the source allows any lacunary sequence, p. 242): both blocks are exactly `[2^k, 2^{k+1})`, so no single frequencies occur. Serves the Khintchine inequality | on paper |
| 27 | [LPP, (III.1)–(III.3)] | only the average of (III.3) over the signs is needed: the Littlewood–Paley inequality [HNVW, Thm 5.7.10] with random signs for the dyadic blocks, and the randomised boundedness of single frequencies (the blocks of the source differ from the dyadic ones by one or two frequencies): about 280 lines on top of [HNVW, Thm 5.7.10], in place of [MC, Thms 1.1, 1.3] and their transference (about 4 740 lines), and of [B83] for the Hilbert transform (about 3 490 lines). Scope: the average, not each choice of the signs | history (`ec00cb2`) |
| 28 | the duality step of the Khintchine inequality | the bilinear pairing `tr (A B)` instead of `tr (A Bᴴ)`: (I.3) is then the only inequality needed, twice, with no transposes | compiled |
| 29 | [LPP, (I.9)] for signs, `(E ‖Σ ε_k A_k‖²_{S_p})^{1/2} ≤ ‖(Σ A_kᴴ A_k)^{1/2}‖_{S_p}`, `1 ≤ p < 2`, and hence (I.14), with adjoints for the other square function and the triangle inequality (not in the library; `p = 2` is an equality) | with `D = (Σ A_kᴴ A_k)^{1/2}`, `S = Σ ε_k A_k`, `1/p = 1/2 + 1/r` and `α = 1 − p/2`: Hölder's inequality for `S = (S D^{−α}) D^α`, where `D^{−α}` is the inverse on the range of `D` (`S` vanishes on the kernel), `E ‖S D^{−α}‖²_{S_2} = tr D^p` and `‖D^α‖_{S_r} = ‖D‖_{S_p}^{p/r}`; no duality, and not (I.6), (I.8). Scope: `S_p`, any orthonormal system in place of the signs | on paper |

Item 25:

- Replace `e^{i 2^k t}` by independent unimodular variables `z_1, …, z_n` on `𝕋ⁿ`, with `ℤⁿ`
  ordered lexicographically from the last coordinate (`α > 0` if its last non-zero coordinate is
  `> 0`):
  - The factorization works for an ordered dual.
  - The coefficient of `z_k` in `g h` is `∫ z̄_k g d_k h + ∫ z̄_k d_k g h`, `d_k` the martingale
    differences of the filtration `σ (z_1, …, z_k)`.
  - (III.3) becomes the UMD inequality for `C_{2p}`.
- No Littlewood–Paley theory.

## McConnell's theorems

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 30 | [MC, Thm 1.1], from (3.7) to (3.2) | partitions of growing intervals `[0, A_N]` with mesh `→ 0`: `−16 g_N → T_m f` directly, without `T_m^A` and with one use of Fatou's lemma (the error must be bounded uniformly in `A`, by the exponential decay of `w`) | on paper (about 100 lines less) |
| 31 | [MC, (3.3)] | the primitive `−(w − y w_y + ½ y² w_yy)` of `−½ y² w_yyy` does both integrations by parts at once; or, on the Fourier side, `∫_0^∞ y² t³ e^{−4ty} dy = 1/32` | the first on paper, the second in the history (`beab475`) |
| 32 | [MC, (3.5)–(3.6)], equal parts | on the Fourier side the sum is a difference quotient times a Riemann sum of a continuous function; no error estimate | compiled |
| 33 | [MC, Lemma 3.1] for `n = 1` | the two cases `\|s\| < y`, `\|s\| ≥ y` are added instead of separated: the constant `17` | in the library |
| 34 | [MC, (2.1)], complex coefficients | the factor `π/2` instead of `2`, from the complex UMD constant of BanachProbability | on paper |
| 35 | [MC, Thm 1.3], the two uses of (2.1) for Rademacher sums | Kahane's contraction principle, which holds in every Banach space: `C β⁶ ħ²` in place of `C β⁸ ħ²` | history (`beab475`) |
| 36 | [MC, Thm 1.3], the two last uses of Theorem 1.1 | `T_M T_{m_1}` is itself the multiplier `Σ ξ_j φ (2^{2j} \|·\|)`, which satisfies (3.1): one use | compiled |
| 37 | [MC, Thm 1.3], the reduction to `f̂ = 0` on `λ < 0` | one-sided bumps `φ (2^{2j} ·)`: no reduction, one factor `ħ` less | on paper |
| 38 | [MC, Thm 1.3] | from both inequalities of [HNVW, Thm 5.3.24]: the random signs absorb the `ε_j`, without Theorem 1.1 (only the right-hand inequality is in the library) | on paper |
| 39 | [MC, p. 751], the last step | let the sum in (3.11) run to `j = 2N − 1` and start at `z_{2N} = 2A`, so that the chain need not be cut at `z_{2N−1}`; take the `x`-integral first: translation invariance and `‖u (·, y)‖_p ≤ ‖f‖_p` | history (`beab475`) |

## Burkholder's theorem

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 40 | [B83, Lemmas 2–4], the Hilbert transform on UMD spaces | the dyadic shifts of [HNVW, Section 5.1]: about 1 840 lines ([`VectorValued/Dyadic/`](../HarmonicAnalysis/VectorValued/Dyadic), `VectorValued/HilbertTransform/Truncated`, `ec00cb2`) in place of about 3 800 ([`VectorValued/Burkholder/`](../HarmonicAnalysis/VectorValued/Burkholder), with (9) and Lemma 4 after [B83, Lemma 1] and [R, §18]; about 3 490 at `c8182f9`); for the multiplier `sgn` both need [HNVW, Lemma 5.2.1] (`VectorValued/HilbertTransform/Fourier`, 600 lines). The constant is `4 β² + 11` in place of `2 β² + 1` | in the library (the first for the Littlewood–Paley inequalities of [HNVW], the second for [MC]) |
| 41 | [B83, Lemmas 3, 4] and the multiplier `sgn` | no truncations (below) | on paper |
| 42 | [B83, Lemma 4], the constant | `‖v‖_p ≤ β² ‖u − u (0)‖_p` in (33), and the mean of the dilated function tends to `0` (in `L^p`, with the dilation): `β² + 1` in (34) | on paper |
| 43 | [B83, (21)–(23)], `τ < ∞` | orthogonality, `2 δ² E (τ ∧ n) = E \|Z_{τ ∧ n}\|² ≤ 4`, or a run of about `2 / δ` equal signs, instead of (20); (27) still needs (20) | on paper |
| 44 | [B83, Lemma 2], the limits `n → ∞`, `δ → 0` | for each `δ` an `n` with `P (τ > n) ≤ δ`, on the cube `{±1}^{2n}`: `1 ≤ \|Z_{τ ∧ n}\| ≤ 1 + 2δ` off a set of probability `δ`, and `\|Z_{τ ∧ n}\| ≤ 2`; no infinite sequence of signs, no `Z_τ` | on paper (about 250 lines less) |
| 45 | the Hilbert transform in [MC, Thm 1.3] | Theorem 1.1 of [MC] in the library's form allows `m` of class `C²` on `ℝ ∖ {0}`, hence `m = sgn` with `c = 1`: `‖𝓕⁻ (sgn · G)‖_p ≤ C β² ‖𝓕⁻ G‖_p`, about 20 lines, without [B83] and [HNVW]. Scope: the multiplier, with a large absolute `C`; no truncations, no conjugate functions. Compare [MC, Remark 3.1], a direct proof by the same method | compiled |
| 46 | [B83, (9)] for real martingales | Osękowski's Theorem 8.6, in BanachProbability (`BanachProbability.Burkholder.squareFunction_of_martingale`), gives (9) directly, with the constant `p* − 1` on both sides: no average over the signs and no Khintchine inequality. The proof here needs both: p. 275 asserts without proof that (8) implies (9) where Khintchine's inequality holds, and the proof is that of Lemma 1 (pp. 277–278) for `ℝ`, followed by Khintchine's inequality at each point, with the constants `κ_{2,p} (p* − 1)` and `κ_{p,2} (p* − 1)`. It stays in BanachProbability as the other proof | history (`11e9e12`); Lean elsewhere (BanachProbability) |
| 47 | [B83, Lemma 4] | first for `f` that vanishes off `[−A, A]`: then `g_R ((x − s) / R) = f (x − s)` for `\|s\| < πR` and large `R`, so (38) holds with the kernel `(2R)⁻¹ cot (s / (2R))` for `\|s\| < πR` only, where `\|cot u\| ≤ \|u\|⁻¹` for `\|u\| < π/2` is enough, and Fatou's lemma as `R → ∞`; then `1_{[−A, A]} f → f` and Fatou's lemma again. Shorter in Lean, about 400 lines against 570 (non-blank lines of the module up to the limit `ε → 0`, docstrings included), because it needs no analysis of the kernel past `π/2` and no wrap-around (`perCot`, `abs_cot_le` up to `\|u\| ≤ 2`). Replaced by M. Riesz's argument (§18), which [B83] cites | history (`11e9e12`); not used |

Item 41, no truncations:

1. On the circle of length `2πR`, Lemma 2 in the limit (`u (0) = 0`, so the constant is `β²`) for
   `f − f̂ (0)` and `r = 1 − y / R`.
2. As `R → ∞` the mean tends to `0` and `‖v (·, y)‖_p ≤ β² ‖f‖_p` for the conjugate Poisson integral
   `v (x, y) = π⁻¹ ∫ t (t² + y²)⁻¹ f (x − t) dt` on the line, whose symbol is
   `−i sgn (ξ) e^{−2π|ξ|y}` (by Fubini for `f ψ (η ·) ∈ L¹`, a cut-off, `η → 0`).
3. `y → 0` with Fatou's lemma: `ħ ≤ β²`, without `K_r`, (33), `H_ε` and [HNVW, Lemma 5.2.1].

## The Beurling–Ahlfors transform

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 48 | `‖𝓑‖_p ≤ C` if `‖∂u‖_p ≤ C ‖∂̄u‖_p` on `C_c^∞` [BMS, §1 (b)], by the proof of [Gu, Cor. 1.4] | the dense class of [HNVW, Prop. 2.4.23 (ii)] (Fourier transform in `C_c^∞(ℂ∖{0})`) in place of `C_c^∞`: the Cauchy transform `𝓕⁻¹((πiξ)⁻¹ 𝓕g)` is then a Schwartz function, so no Cauchy kernel and no decay estimate of the potential are needed, and the cut-offs work for every Schwartz function. Guerra's own class would also work here: for `g ∈ C_c^∞` the Cauchy transform `f` is `O(1/\|z\|)` and `∂f = 𝓑g = O(1/\|z\|²)`, so `‖f ∇η_R‖_p = O(R^{2/p − 2}) → 0` for every `p > 1`. The change of class is for economy, not forced | in the library |
