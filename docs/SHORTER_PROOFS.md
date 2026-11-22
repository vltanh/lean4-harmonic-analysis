# Shorter proofs

Arguments shorter than those of the sources, noticed while following them. The library follows the
sources up to the departures stated in the module docstrings (and in the README, "Sources"); the items
with the status "in the library" are among them. Status: "in the library"; "history" (proved in this
repository at the commit named, replaced since by the source's proof); "Lean elsewhere"; "on paper"
(written out or sketched, not compiled). References are in [REFERENCES.md](REFERENCES.md).

| # | Result | Shorter proof | Status |
| --- | --- | --- | --- |
| 1 | noncommutative Khintchine, upper bound, real matrices, `q ≥ 2` | exchangeable pairs (Mackey–Jordan–Chen–Farrell–Tropp 2014), then the Hermitian dilation: constant `√(2 (q − 1))`, about 500 lines in place of the route of Lust-Piquard–Pisier and Pisier | Lean elsewhere (`BanachProbability.ncKhintchine_upper`) |
| 2 | HNVW I, Theorem 5.7.10 (2), transference of Littlewood–Paley inequalities | `θ` a Schwartz function whose Fourier transform has compact support; `1_{I_k}` acts on `θ (ε·) f (ρ·)` exactly for small `ε`, and Lemma 5.7.3 on both sides gives the inequality without duality. This is the book's own argument for the Hilbert transform (Proposition 5.2.5, Lemma 5.2.6). Scope: multipliers locally constant at the points of `ρ · supp f̂` | history (`d0d081b`) |
| 3 | LPP, Theorem III.1 (i) for the Paley projection, (III.3) | replace `e^{i 2^k t}` by independent unimodular variables `z_1, …, z_n` on `𝕋ⁿ`, with `ℤⁿ` ordered lexicographically from the last coordinate (`α > 0` if its last non-zero coordinate is `> 0`): the factorization works for an ordered dual, the coefficient of `z_k` in `g h` is `∫ z̄_k g d_k h + ∫ z̄_k d_k g h`, `d_k` the martingale differences of the filtration `σ (z_1, …, z_k)`, and (III.3) becomes the UMD inequality for `C_{2p}`. No Littlewood–Paley theory | on paper (identity checked numerically, `n = 2, 3`) |
| 4 | LPP, Theorem III.1 (i) for a lacunary sequence | `n_k = 2^{k+1} − 1` in place of `2^k` (the source allows any lacunary sequence, p. 242): both blocks are exactly `[2^k, 2^{k+1})`, so no single frequencies occur. Serves the Khintchine inequality | on paper |
| 5 | HNVW I, Theorem 5.1.13, the symbol of `∫_0^∞ φ_t * f dt/t` | `φ̂ (ξ) = 2i sin³ θ sin² (θ/2) / θ²`, `θ = πξ/2`, so the symbol of `∫_ε^R φ_t * f dt/t` is `2i ∫_{εθ}^{Rθ} sin³ s sin² (s/2) s⁻³ ds`, absolutely convergent, with limit `i (π/8) sgn ξ`; that the constant is not `0` follows from `s⁻³ = ½ ∫_0^∞ u² e^{−su} du`. No kernel identity (5.23), no Cauchy integral | on paper |
| 6 | HNVW I, Lemma 5.2.1 | on the half circle only `cos ≤ 0` is needed for the bound `π`, and the limit at `∞` is dominated convergence: no inequality of Jordan | on paper (about 45 lines less) |
| 7 | HNVW I, Lemma 5.3.23 | `\|(1/φ̂)'\| ≤ π²` on `[1/2, 1]` from `sin² t ≥ 2t/π` and `t ≤ tan t`, and integrate it, instead of the bound `2π` "by elementary calculus" | in the library |
| 8 | HNVW I, Lemma 5.7.3, `w` integrable and `f` continuous | Riemann–Lebesgue for `e_n`, then uniform approximation by trigonometric polynomials; more general in `w` (the book: `w = \|φ\|^p`, `φ` Schwartz), less general in `f` (the book: `f ∈ L^p`), and no shorter | history (`d0d081b`) |
| 9 | Minkowski's integral inequality | weighted Jensen inequality with the weight `a (y) = ‖h (·, y)‖_p` and the function `h / a` | in the library |
| 10 | Bekjan–Xu, Theorem 3.1, matrix case | any `B` with `D = Bᴴ B` may replace the positive square root of `D` | on paper |
| 11 | LPP, (III.1)–(III.3) | only the average of (III.3) over the signs is needed | in the library |
| 12 | HNVW I, Propositions 5.1.4, 5.1.5, finitely many generations | the randomised UMD property applied directly to the dyadic martingale on each unit interval, instead of Theorem 4.2.13 and the equality of laws; for the left half of 5.1.5, to the martingale of the shifts | in the library |
| 13 | HNVW I, Theorem 5.1.13, for the Fourier multiplier `sgn` | bound the truncations `H_{ε, 2^n ε}` uniformly, with the error terms by Young's inequality, and pass to the limit on the Fourier side with Fatou's lemma; no maximal function, no convergence in `L^p` | in the library |
| 14 | Bekjan–Xu, Theorem 3.1, matrix case | `Φ (h⁻¹) = D^{−1/2}` is explicit, so `Φ (h) Φ (h⁻¹) = 1`, (3.2) and (3.3) are not needed | in the library |
