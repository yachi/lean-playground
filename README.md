# LeanPlayground

A playground for doing mathematics in Lean 4 with Mathlib.

API docs: <https://yachi.github.io/lean-playground/docs/> (rebuilt by CI on every push to `main`).

## Setup

The toolchain comes from [mise](https://mise.jdx.dev) and [elan](https://github.com/leanprover/elan).
`mise.toml` pins elan and puts `~/.elan/bin` on `PATH` inside this directory.
`lean-toolchain` pins the Lean version, and elan installs it on first use.

```fish
mise install
elan-init -y --default-toolchain none --no-modify-path  # once per machine
lake exe cache get   # download prebuilt Mathlib (~9k files); never build Mathlib from source
lake build
```

## Layout

- `LeanPlayground/` — playground files. Each file starts with `module`, then `public import` of only
  the Mathlib modules it uses (not all of `Mathlib`), so checks and the CI docs build stay small.
  To find them, put `#min_imports in` before a declaration. It can miss tactic extensions
  (for example `positivity`) and lemmas that are used only through dot notation. It can also
  suggest too many. To check that a list is minimal, remove each import in turn and compile.
- `LeanPlayground.lean` — the library root. Import every new file here so `lake build` checks it.

## Formalizations

### Sums of element orders — `LeanPlayground/SumElementOrders/`

For a finite group `G`, `ψ(G)` is the sum of the orders of its elements, and `ψ(n) = ψ(Cₙ)`.
This proves the theorem of Amiri, Jafarian Amiri and Isaacs (*Sums of element orders in finite
groups*, Comm. Algebra 37 (2009)) and Lemmas 1–3 of Péter P. Pálfy and Alex D. Simonyi, [*Finite
groups with large sum of element orders compared to cyclic
groups*](https://arxiv.org/abs/2610.27846) (arXiv, 2026-10). The paper's classification of groups
with `ψ(G) ≥ ψ(Cₙ)/3` is not formalized.

| Statement | Lean |
|---|---|
| `ψ(Cₙ) = ∑_{d ∣ n} d φ(d)` | `SumElementOrders.psi_eq_psiNat` |
| `ψ` is multiplicative; `(p + 1) ψ(pᵉ) = p^{2e+1} + 1` | `psiNat_mul`, `succ_mul_psiNat_prime_pow` |
| Lemma 1 (both identities) | `lemma1_one`, `lemma1_two` |
| Estimate (1): `ψ(n) > n² ∏_{p ∣ n} p/(p + 1)` | `sq_mul_prod_lt` |
| Amiri–Jafarian Amiri–Isaacs: `ψ(G) ≤ ψ(\|G\|)` | `psi_le` |
| … with equality only for cyclic `G` | `psi_lt`, `psi_eq_iff` |
| Lemma 2: `ψ(C_{p^{k-1}} × C_p) / ψ(pᵏ)` | `psi_prod`, `lemma2` |
| Lemma 3: if `ψ'(G) ≥ 1/3`, then `c < p` or one of ten exceptions | `lemma3` |

The main theorem is proved by strong induction on `|G|`. Let `q` be the largest prime divisor of
`n`. If every element has `q · o(g) ≤ n`, then `q ψ(G) ≤ n² < q ψ(n)`. Otherwise some `⟨g⟩` has
index `c < q`, and the Sylow `q`-subgroup `Q` of `⟨g⟩` is normal in `G`: the number of Sylow
`q`-subgroups is `≡ 1 mod q` and divides `c`. For a cyclic normal `Q` of order coprime to its index,
each coset has a representative `b` with `b^{o(bQ)} = 1`. Then `(bz)^{o(bQ)} ∈ ⟨z⟩` for `z ∈ Q`,
so `ψ(G) ≤ ψ(Q) ψ(G/Q)` (`psi_le_mul`), and induction on `G/Q` finishes the proof.

### The strong Erdős–Frankl–Füredi cover-free conjecture — `LeanPlayground/CoverFree/`

Yanan Hu and Leilei Zhang, [*A proof of the strong Erdős–Frankl–Füredi cover-free
conjecture*](https://arxiv.org/abs/2610.24442) (arXiv, 2026-10). A family is `r`-cover-free if no
member lies in the union of at most `r` others, and `T(r)` is the least `n` with an `r`-cover-free
family of more than `n` subsets of `[n]`. Everything is unconditional: Stehlík's theorem, which the
paper uses as a black box, is proved too.

| Paper | Lean |
|---|---|
| Lemma 2.1 (Stehlík 2006, dual form): critical, connected `⇒ \|U\| ≥ 2κ − 1` | `CoverFree.stehlikBound` |
| Lemma 2.2: `κ² ≤ ∑_{x ∈ U} 1 / p_x` for a probability weighting | `CoverFree.weighted'` |
| Theorem 1.1: more than `n` members on `n` points `⇒ n ≥ (r + 1)²` | `CoverFree.sq_le_card_of_card_lt` |
| Theorem 1.1 for `T`: `T(r) ≥ (r + 1)²` | `CoverFree.sq_le_T` |
| Affine planes: `T(r) ≤ q²` for prime powers `q > r` | `CoverFree.T_le` |
| Corollary 1.2: `T(r) = (r + 1)²` when `r + 1` is a prime power | `CoverFree.T_eq` |

`coverNum H W` counts members of `H` that need not lie inside `W`, so restricting to a subset keeps
the same family and weights, and Lemma 2.2 needs no down-closure. Stehlík's theorem
(*Minimal connected τ-critical hypergraphs*, Graphs Combin. 22 (2006)) is proved in the dual
setting of good partitions (`CoverFree.IsPart`), following his Lemmas 2–5. Lemma 4 (two singleton
blocks never share a component) is proved by induction on the distance between them, moving the
singleton one step along a shortest walk, instead of Stehlík's cut of a shortest path.

### The center of a Clifford algebra — `LeanPlayground/CliffordCenter/`

Both propositions of Chris Peters and Hans Sterk, [*On the center of the Clifford
Algebra*](https://arxiv.org/abs/2610.23323) (arXiv, 2026-10), for Mathlib's `CliffordAlgebra Q`
over a field `k`. Here `C₀(q)` is Mathlib's `CliffordAlgebra.even Q`.

| Paper | Lean |
|---|---|
| Prop 1.1 (char ≠ 2, orthogonal basis `eᵢ` with `q(eᵢ) ≠ 0`, `e = e₁ ⋯ eₙ`): centralizer of `C₀(q)` is `k + ke` | `CliffordCenter.centralizer_even` |
| Prop 1.1 a): center of `C(q)` is `k` (`n` even), `k + ke` (`n` odd) | `center_eq_bot`, `center_eq_span` |
| Prop 1.1 b): center of `C₀(q)` is `k` (`n` odd), `k + ke` (`n` even) | `center_even_eq_bot`, `mem_center_even_iff`, `vol_mem_even` |
| Prop 1.2 (char 2, symplectic basis `eᵢ, fᵢ`, `z = ∑ eᵢfᵢ`): centralizer of `C₀(q)` is `k + kz` | `CliffordCenter.CharTwo.centralizer_even` |
| Prop 1.2 a): center of `C(q)` is `k` | `CharTwo.center_eq_bot` |
| Prop 1.2 b): center of `C₀(q)` is `k + kz` | `CharTwo.mem_center_even_iff`, `z_mem_even` |
| Prop 1.2 c): `z² + z = ∑ q(eᵢ) q(fᵢ)` (the Arf invariant) | `CharTwo.z_mul_z_add_z` |

The proofs differ from the paper's in one respect: they never use that the monomials `e_J` are
linearly independent, only that they span `C(q)`. For Prop 1.1, averaging over conjugation by
`eᵢeⱼ` gives a linear map that fixes the centralizer and kills every `e_J` other than `1` and `e`.
For Prop 1.2, whose degree-by-degree argument the paper only sketches from degree 6 on, the
proof inducts on the number of blocks `eᵢ, fᵢ`. The coordinates of an element over one block are
read off with an operator built from a separability idempotent of that block
(`CliffordCenter.Block.coord_eq_zero`).

### What a complex derivative means — `LeanPlayground/ComplexDerivative/`

Claims from Zundamon's Theorem, [*What Does a Complex Derivative Actually
Mean?*](https://youtu.be/2-95hN4fgmE) (YouTube, 2026-10-26): near `a`, the derivative acts as the
multiplier in `Δw ≈ f'(a) Δz`, and multiplying by `r e^{iθ}` scales the plane by `r` and rotates
it by `θ`. So a complex derivative is a local rotation and scaling.

| Lean | Claim |
|---|---|
| `hasDerivAt_iff_tendsto_slope'`, `deriv_rules` | `df/dz = lim Δf/Δz`; `(z²)' = 2z`, `(sin z)' = cos z`, `(e^z)' = e^z` |
| `hasDerivAt_iff_sub_mul_isLittleO` | `Δw ≈ f'(a) Δz`, i.e. `f(a+h) − f(a) = f'(a) h + o(h)` (and the real version) |
| `exp_mul_I_eq`, `polar_form`, `polar_mul`, `sqrt_three_add_I` | Euler's formula, polar form, "length → multiply, angle → add", `√3 + i = 2e^{iπ/6}` |
| `mul_eq_smul_rotation`, `isConformalMap_mul`, `dist_mul_mul` | Multiplying by `α` is a rotation by `arg α` then a scaling by `‖α‖`, keeps angles, and scales distances by `‖α‖` |
| `sub_rotation_isLittleO_of_hasDerivAt`, `conformalAt_of_hasDerivAt` | Near `a`, `f` is that rotation and scaling up to `o(h)`; conformal when `f'(a) ≠ 0` |
| `hasDerivAt_exp_I_mul`, `exp_I_mul_z₀`, `deriv_z₀`, `exp_I_mul_local_scale_rotate` | The worked example: `f(z) = e^{iz}` at `z₀ = −π/4 − i ln 2` has `f(z₀) = 2e^{−iπ/4}`, `f'(z₀) = 2e^{iπ/4}`, so near `z₀` it scales by 2 and rotates by 45° |

### The friendship paradox — `LeanPlayground/FriendshipParadox/`

Scott L. Feld, *Why your friends have more friends than you do*, Amer. J. Sociology 96 (1991).
For a finite simple graph with degrees `d v` on `n` vertices, and `friendDegreeSum v = ∑_{u ~ v} d u`:

| Statement | Lean |
|---|---|
| A random friend has on average `∑ d² / ∑ d ≥ ∑ d / n` friends | `SimpleGraph.friendship_paradox` |
| … with equality iff all degrees are equal | `SimpleGraph.friendship_paradox_eq_iff` |
| Per person: `∑_v d v ≤ ∑_v friendDegreeSum v / d v` | `SimpleGraph.friendship_paradox_local` |
| … with equality iff `d` is constant on each connected component | `SimpleGraph.friendship_paradox_local_eq_iff_reachable` |

Mathlib has the degree-sum formula but not the friendship paradox (nor should it be confused with
the friendship *theorem* of Erdős–Rényi–Sós). Both inequalities are sums of squares:
`∑_u ∑_v (d u − d v)² = 2 (n ∑ d² − (∑ d)²)`, and pairing each friendship with its reverse,
`2 (∑_v friendDegreeSum v / d v − ∑ d) = ∑_{u ~ v} (d u − d v)² / (d u d v)`.

### The productegral — `LeanPlayground/Productegral/`

Claims from Sohil Rathi, [*The Missing Calculus Operation*](https://youtu.be/QN680Is4euw)
(YouTube, 2026-10-12), proved with Mathlib. The productegral `∏ f(x)^dx` is defined as
`exp (∫ log f)`. Each theorem's doc comment quotes the claim and its video timestamp.

| File | Claims |
|---|---|
| `Finite.lean` | Bar sums and products: 15, 120, 3543.75, about 59.5, about 45, 4^0.01 ≈ 1.014 |
| `Integrals.lean` | ∫x = 12.5, ∫log x = 5 log 5 − 5, the value (5/e)^5 ≈ 21.06, the line length (t/e)^t |
| `Limits.lean` | The bar products converge to (5/e)^5; the n! ≈ (n/e)^n approximation |
| `Decrease.lean` | The bar products strictly decrease for every bar count N ≥ 1 |
| `MulCalculus.lean` | The multiplying slope of 2^x is 2; multiplicative FTC: ∏ (f*)^dx = f(b)/f(a) |

Two claims are false as stated, so the files prove the corrected forms:

- **2:03, "exactly 45":** the third-width product is 45.0015, and `riemannProduct_id_fifteen_ne_45` proves it is not 45.
- **6:17, "n! is about (n/e)^n":** this is true only for n-th roots. `tendsto_factorial_div_pow_atTop` proves that the ratio `n! / (n/e)^n` tends to infinity.

### −1/12 in physics — `LeanPlayground/MinusTwelfth/`

Claims from PBS Space Time, [*Why Does -1/12 Keep Appearing Everywhere In
Physics?*](https://www.youtube.com/watch?v=w6229Ivy_Lo) (YouTube, 2026-10-08). Lean cannot prove
physics, so these files prove the mathematical steps that the video states. Each doc comment
names the physical modelling assumption that a theorem stands in for.

| File | Claims |
|---|---|
| `Series.lean` | ½+¼+… = 1. 1+2+3+… diverges (and Lean's `∑'` gives 0, not −1/12). No linear, shift-stable summation method can sum 1, 2, 3, …. Cesàro and Abel sums of the viral argument's series |
| `Zeta.lean` | ζ(s) = Σ 1/nˢ only for s > 1. The analytic continuation to ℂ \ {1} is unique. ζ(−1) = −1/12, ζ(−3) = 1/120, and the pole at 1 |
| `Cutoff.lean` | With the cutoff e^(−nε): Σ n·e^(−nε) − 1/ε² → −1/12. The 1D Casimir energy minus its divergent part → −πħc/(24d) |
| `Physics.lean` | The 1D Casimir energy is negative and the force is attractive. −(D−2)/24 = −1 gives D = 26. With ζ(−1, ½) = 1/24, the superstring gives D = 10. The 3D Casimir energy uses ζ(−3) |

One step uses a formula from the literature and does not derive it: the 3D Casimir prefactor
−π²ħc/(6d³) (Casimir 1948). `Physics.lean` says so.

### Restricted vs. full division over PA⁻ — `LeanPlayground/RestrictedDivision/`

The whole of Naoya Kato, [*Equivalence of Restricted and Full Division*](https://arxiv.org/abs/2610.24976)
(arXiv, 2026-10), which answers Visser's Open Question 8.29: over PA⁻, Euclidean division for
co-prime pairs implies full Euclidean division. `PAMinus` is the paper's exact axiom list
(pa1–pa13, pa15), and `PAMinus.pa17Minus_iff_pa17` proves the equivalence in every model, which
is the paper's `PA⁻ ⊢` claim by the completeness theorem.

| Paper | Lean |
|---|---|
| Lemma 1 | `le_antisymm'`, `le_of_add_le_add_right`, `mul_zero'`, `zero_le'`, `lt_iff_add_one_le` |
| Theorem 2 | `euc_iff_euc_affine` |
| Corollary 3 | `cop_sq`, `euc_iff_euc_sq` |
| Corollary 4 | `pa17Minus_iff_pa17` |

Theorem 2 holds without the paper's hypothesis `x ≠ 0`, so the Lean statement drops it.

### The 2023 Simon Marais open problem — `LeanPlayground/SimonMarais/`

The main theorem of Anthony Pisani, [*On the Open Problem in the 2023 Simon Marais Mathematics
Competition*](https://arxiv.org/abs/2610.30658) (arXiv, 2026-10). For `n` not a perfect square,
some real `r` makes both `r^a + √n` and `r^b + √n` rational exactly when `a = b`, or
`{a, b} = {g, 2g}` with `g` odd. This is `SimonMarais.main`.

| File | Paper |
|---|---|
| `Lucas.lean` | Lucas sequences: the cases of Theorem 3 and Corollary 5 that are used (cited from Ballot–Williams there, proved here), and Lemma 6 |
| `OddSum.lean` | The `p`-adic valuation of the odd binomial sum, used twice in Theorem 13 |
| `Quad.lean` | Arithmetic in `ℚ(√n)` and the reduction to `r ∈ ℚ(√n)` (Lemma 7) |
| `Core.lean` | Lemma 8, Theorem 9, Lemmas 10–12, Theorem 13 |
| `Main.lean` | Theorem 2, both directions |

The paper cites two results on Lucas sequences from Ballot and Williams' book. The files prove
the special cases that are needed instead of assuming them. Theorem 9 is proved by comparing the
ratios `(|x| + √n)/(|x| - √n)` instead of with Rolle's theorem.

### The perfect cuboid problem — `LeanPlayground/PerfectCuboid/`

A perfect cuboid has integer edges, face diagonals and space diagonal. Whether one exists is
open. `Basic.lean` proves the classical partial results, not the problem itself.

#### Summary of results

The files below were added over many pull requests. This table lists every file in
`LeanPlayground/PerfectCuboid/` with its main statement; the sections after it give the Lean
names. **Status**: *theorem* = an unconditional main result; *partial* = a reduction, or some cases
only; *example* = examples or sharpness checks; *data* = kernel-checked certificates;
*infrastructure* = definitions or tools used elsewhere. **Attribution** says where the statement
comes from; "new" means we found no earlier source, not a claim of priority.

Highlights proved here with no earlier source we know of: no face diagonal of a perfect cuboid is
a prime power, and every edge has at least three distinct prime factors (Korec's side conditions
removed); a perfect cuboid exists if and only if some congruent-number curve `E_N` has a positive
configuration, with no extra square condition (twist rigidity); every polynomial cuboid
specializes to a perfect cuboid, and a polynomial cuboid with a monomial or single-root edge is
proportional; prime-power results for face cuboids and edge cuboids; and 91 Peschmann fibers ruled
out by descent. Round 15 adds: rational-edged cuboids over `ℤ√d` are exactly the twisted near-miss
objects, and are perfect cuboids when `d < 0` or some `p ≡ 3 (mod 4)` divides `d`; a Pythagorean
triple plus a number adjacent to all three sides is a perfect cuboid or one of two face-cuboid
types that are never perfect; a polynomial family of Eisenstein bricks; and the Frobenius cuboid,
a nondegenerate non-proportional polynomial cuboid over `𝔽_p[X]` for every `p ≡ 1 (mod 4)`.
Round 16 adds a 2-descent on `E_N`: in Asiryan's rank-one pattern the third point lies in
`U + 2E_N(ℚ)`, so a rank-one configuration forces a rational perfect cuboid whose derived
triangle `(cg, ab, ef)` is a *quarter triangle* (generators `m`, `m ± n` all squares); this
replaces Ingram's primitive-divisor theorem by the explicit square condition `QuarterFree N`
(`KummerDescent.lean`), which remains unproved (open problem 14). Along the way: the Kummer
relations of the pattern (`KummerAddition.lean`), the integer theory of quarter triangles
(`QuarterTriangle.lean`), and a new square class for every box with integral `d, e, g`:
`gcd(ag, bc)·(e+a)(g+e)(d+a)(g+d)` is a square or twice a square (`QuarterCharacters.lean`).

<details>
<summary>Every file, by topic (click to expand)</summary>

**Perfect cuboids: divisibility, primes, lengths**

| File | Object | Headline statement(s) | Status | Attribution | PR |
|---|---|---|---|---|---|
| [`Basic.lean`](LeanPlayground/PerfectCuboid/Basic.lean) | perfect cuboid / brick | `IsEulerBrick`, `IsPerfectCuboid`; (44,117,240); Saunderson's parametrization; 3, 4, 9, 16, 5, 11 divide brick edges; 7, 19 divide an edge, and 13, 17, 29, 37 divide some length, of a perfect cuboid | theorem + infrastructure | Halcke 1719, Saunderson 1740; classical divisibility (Leech 1977 / Guy D18) | [#3](https://github.com/yachi/lean-playground/pull/3) |
| [`Leech.lean`](LeanPlayground/PerfectCuboid/Leech.lean) | perfect cuboid | 2⁸·3⁴·5³·7·11·13·17·19·29·37 ∣ abcdefg | theorem | Leech (Guy, UPINT D18) | [#19](https://github.com/yachi/lean-playground/pull/19) |
| [`SpaceDiagonal.lean`](LeanPlayground/PerfectCuboid/SpaceDiagonal.lean) | perfect cuboid | every prime factor of g is ≡ 1 (mod 4); g ≡ 1 (mod 4); `prime_dvd_both_of_dvd_sq_add_sq` | theorem | classical | [#5](https://github.com/yachi/lean-playground/pull/5) |
| [`Korec.lean`](LeanPlayground/PerfectCuboid/Korec.lean) | perfect cuboid | g is neither a prime power nor a product of two primes | theorem | Korec 1992 (Math. Slovaca 42), Thm 5.1 | [#18](https://github.com/yachi/lean-playground/pull/18) |
| [`EdgePrimePower.lean`](LeanPlayground/PerfectCuboid/EdgePrimePower.lean) | perfect cuboid | no edge is a prime power (every p, every edge, no primitivity) | theorem | Korec 1984 | [#43](https://github.com/yachi/lean-playground/pull/43) |
| [`EdgeTwoPrimes.lean`](LeanPlayground/PerfectCuboid/EdgeTwoPrimes.lean) | perfect cuboid | no edge is p^k q^l; every edge has ≥ 3 distinct prime factors | theorem | Korec 1984 (with side conditions); side conditions removed: new | [#44](https://github.com/yachi/lean-playground/pull/44) |
| [`DiagonalPrimePower.lean`](LeanPlayground/PerfectCuboid/DiagonalPrimePower.lean) | perfect cuboid | no face diagonal is a prime power | theorem | new | [#43](https://github.com/yachi/lean-playground/pull/43) |
| [`DiagonalTwoPrimes.lean`](LeanPlayground/PerfectCuboid/DiagonalTwoPrimes.lean) | perfect cuboid | even face diagonal 2^s p^k: the family F1 is empty | partial | new | [#44](https://github.com/yachi/lean-playground/pull/44) |
| [`FaceDiagonalF2.lean`](LeanPlayground/PerfectCuboid/FaceDiagonalF2.lean) | perfect cuboid | face diagonal 2^s p^k: the family F2 reduced to types II/III, and its structure | partial | new | [#45](https://github.com/yachi/lean-playground/pull/45) |
| [`PrimeSupport.lean`](LeanPlayground/PerfectCuboid/PrimeSupport.lean) | perfect / face cuboid / brick | prime support: 17 shapes for every p, 7 for p ≡ 3 (mod 4), 3 for p = 2; 14 face-cuboid shapes (7 for p ≡ 3 mod 4); 17 brick shapes | theorem | new | [#46](https://github.com/yachi/lean-playground/pull/46) |
| [`SquareLengths.lean`](LeanPlayground/PerfectCuboid/SquareLengths.lean) | perfect cuboid | xy, xz, 2xy are never squares in a right triangle; at most 3 of a..g are squares; abcg ≠ □, 2□ | theorem | Fermat quartics; packaging new | [#46](https://github.com/yachi/lean-playground/pull/46) |
| [`SquareLengthsHyp.lean`](LeanPlayground/PerfectCuboid/SquareLengthsHyp.lean) | perfect cuboid | 2·leg·hyp is never a square (y⁴ + (2xz)² = (x²+z²)²); all 12 products for a perfect cuboid | theorem | new | [#47](https://github.com/yachi/lean-playground/pull/47) |
| [`Adjacency.lean`](LeanPlayground/PerfectCuboid/Adjacency.lean) | perfect cuboid / face cuboid | Pythagorean adjacency: a triple u²+v²=w² plus z adjacent to u, v, w is a perfect cuboid (z > w), a type-A face cuboid (x²+y²+2c² = □) or a type-B face cuboid (u²−r² = □) (`classification`, with converses); types A, B are never perfect (Fermat); in a perfect cuboid d²+e², d²+f², e²+f² are not squares; signed cuboids (+,−,−), (+,+,−) | theorem | new (Leech's square-difference graph is the analogue) | [#49](https://github.com/yachi/lean-playground/pull/49) |
| [`DivisorForm.lean`](LeanPlayground/PerfectCuboid/DivisorForm.lean) | perfect cuboid | a perfect cuboid exists ⟺ there are rationals r₁, r₂, r₃ > 1 with r₁² + r₁⁻² + r₂² + r₂⁻² − r₃² − r₃⁻² = 2 | theorem | Korec 1983 divisor framework (reformulation) | [#43](https://github.com/yachi/lean-playground/pull/43) |
| [`Bridges.lean`](LeanPlayground/PerfectCuboid/Bridges.lean) | perfect cuboid | four explicit iffs for the existence of a perfect cuboid: Gaussian pairs u, v ∈ ℤ[i] with N(uv), N(u²−v²), N(u²+v²) squares; de Gua/Heron: derived brick perfect ⟺ σ₂ = □ ⟺ face-diagonal triangle Heronian; three Pythagorean direction cosines on S²; three representations of g² | theorem | reformulations (Stoll–Testa ξ; de Gua; Korec); the iffs new | [#49](https://github.com/yachi/lean-playground/pull/49) |
| [`Contradiction.lean`](LeanPlayground/PerfectCuboid/Contradiction.lean) | perfect cuboid | normal form (primitive, one odd edge, 12640320 ∣ abc, longest edge ≥ 233); `no_congruence_obstruction` | theorem | new (meta-result on congruences) | [#4](https://github.com/yachi/lean-playground/pull/4) |
| [`BeauvilleLambda.lean`](LeanPlayground/PerfectCuboid/BeauvilleLambda.lean) | perfect cuboid | the Beauville invariant is never trivial (twist of y² = x⁵ − x) | theorem | Stoll–Testa setup; statement new | [#28](https://github.com/yachi/lean-playground/pull/28) |
| [`BeauvilleCharacters.lean`](LeanPlayground/PerfectCuboid/BeauvilleCharacters.lean) | perfect cuboid | three more square classes (2ξ, ξ²∓1) are never trivial | theorem | Stoll–Testa (arXiv:1009.0388) setup; new | [#32](https://github.com/yachi/lean-playground/pull/32) |
| [`QuarterCharacters.lean`](LeanPlayground/PerfectCuboid/QuarterCharacters.lean) | body cuboid / perfect cuboid | Gaussian identities (p²−q²)(p²+q̄²) = 4p²(ag+ιbc), (ag+ιbc)(bg+ιac)(cg+ιab) = ι(def)², and the key identity (ag+ιbc)·W·(2p)² = (β₂β̄₃)² with W = (e+a)(g+e)(d+a)(g+d); **gcd(ag, bc)·W is a square (ag/gcd odd) or twice a square (ag/gcd even)** for every box with integral d, e, g, hence for all three derived triangles of a perfect cuboid; the quarter condition as a factorisation β₂β̄₃ = ±(1+ι)·w·p·(σ² − ιδ²) in ℤ[i] (a restatement, not a kill: it holds for the degenerate box) | theorem | new | (round 16) |
| [`OctahedralJ.lean`](LeanPlayground/PerfectCuboid/OctahedralJ.lean) | perfect cuboid | the Legendre curve E_ξ of a cuboid has non-real j-invariant | theorem | Stoll–Testa §4 coordinates; new | [#33](https://github.com/yachi/lean-playground/pull/33) |

**Perfect cuboids: congruent-number / configuration framework**

| File | Object | Headline statement(s) | Status | Attribution | PR |
|---|---|---|---|---|---|
| [`CongruentNumber.lean`](LeanPlayground/PerfectCuboid/CongruentNumber.lean) | E_N configuration | N congruent ⟺ E_N has a point with Y ≠ 0; 1 is not congruent; abcg/2 is congruent | theorem | Koblitz Ch. I; Conrad | [#22](https://github.com/yachi/lean-playground/pull/22) |
| [`CongruentCharacters.lean`](LeanPlayground/PerfectCuboid/CongruentCharacters.lean) | perfect cuboid / body cuboid | three congruent numbers of a perfect cuboid (from body-cuboid identities) | theorem | new | [#34](https://github.com/yachi/lean-playground/pull/34) |
| [`CongruentRank.lean`](LeanPlayground/PerfectCuboid/CongruentRank.lean) | E_N configuration | cuboid ⇒ positive configuration on E_N; rank ≥ 2 modulo `RankOneReduction` | theorem (with reduction) | Paulsen–West 2022; Asiryan (arXiv:2610.10643) | [#15](https://github.com/yachi/lean-playground/pull/15) |
| [`RankOneReduction.lean`](LeanPlayground/PerfectCuboid/RankOneReduction.lean) | E_N configuration | Asiryan Lemmas 2–3: reduction of a rank-one configuration | theorem | Asiryan §5 | [#20](https://github.com/yachi/lean-playground/pull/20) |
| [`DivPolyScale.lean`](LeanPlayground/PerfectCuboid/DivPolyScale.lean) | E_N configuration | weighted homogeneity of division polynomials of E_N (P_k, Q_k independent of N) | infrastructure | Asiryan §5 | [#20](https://github.com/yachi/lean-playground/pull/20) |
| [`DivPolyFormula.lean`](LeanPlayground/PerfectCuboid/DivPolyFormula.lean) | tool | affine n•P formula from Tau Ceti's `zsmul_point_eq_smulEval` | infrastructure | Tau Ceti / AINTLIB (Xu, Angdinata) | [#20](https://github.com/yachi/lean-playground/pull/20) |
| [`Torsion.lean`](LeanPlayground/PerfectCuboid/Torsion.lean) | E_N configuration | E_N(ℚ)_tors = {0, S, T, U} | theorem | Koblitz Ch. I §9 | [#23](https://github.com/yachi/lean-playground/pull/23) |
| [`KummerDescent.lean`](LeanPlayground/PerfectCuboid/KummerDescent.lean) | E_N configuration | 2-descent on E_N: Kummer classes (x, x−N, x+N) of the four cosets of 2E_N; in Asiryan's rank-one pattern the third point lies in U + 2E, so its abscissa is a *quarter point* (−Nx, −2N(x−N) ∈ ℚ²); `not_inRankOne_of_quarterFree` replaces Ingram's primitive-divisor step by the Diophantine hypothesis `QuarterFree N`, which `quarterFree_iff` shows is the same as: no rational perfect cuboid with abcg = 2Ns² has cg(ef+ab) and 2(ef+ab)(ef+ab+cg) both square (round trip configuration → cuboid → configuration) | theorem (reduction; `QuarterFree` itself unproved) | new (Asiryan arXiv:2610.10643 uses Ingram instead) | (round 16) |
| [`KummerAddition.lean`](LeanPlayground/PerfectCuboid/KummerAddition.lean) | E_N configuration | the Kummer addition and doubling identities on E_N as polynomial identities; κ(P + 2R) = κ(P); in the rank-one pattern κ(Q₁)κ(Q₂) = κ(T), κ(Q₃) = κ(U), κ(Q₁)κ(Q₂)κ(Q₃) = κ(S); general dichotomy for a rank-one configuration (a point in E[2] + 2E or Q₁ − Q₂ ∈ E[2] + 2E) in explicit square form; the full rank-one square system (eq. 24 + Kummer) in Asiryan's variables t_a, t_b (a surface, not a curve); the pair relation in cuboid coordinates | theorem + infrastructure | Kummer map standard (Silverman AEC X.1.4); the pattern relations are new | (round 16) |
| [`QuarterTriangle.lean`](LeanPlayground/PerfectCuboid/QuarterTriangle.lean) | Pythagorean triangles / E_N | the quarter condition (m, m−n, m+n squares) ⟺ the Kummer condition −Nx, −2N(x−N) ∈ ℚ² for x = −N·U/(H+V) (odd reduced leg), never for the even reduced leg, never for the odd-leg S-translate (mn = □ and 2m(m+n) = □ are incompatible; 2m(m+n) = □ alone occurs, (8, 1)); parametrisation σ² + δ² = 2τ², m odd, 4 ∣ n; x⁴ + y⁴ = 2z² ⇒ x² = y²; a quarter triangle has no square (reduced) hypotenuse; for a box with integral d, e, g and ag odd: the condition on x₁ ⟺ (ag, bc, de) is a quarter triangle, explicit system ag = k(σδ)², de ± bc = kσ⁴, kδ⁴; (49, 1200, 1201) is a quarter triangle | theorem | classical ingredients (Fermat: three squares in arithmetic progression, x⁴ + y⁴ = 2z²); the dictionary is new | (round 16) |
| [`ConfigCuboid.lean`](LeanPlayground/PerfectCuboid/ConfigCuboid.lean) | E_N configuration | positive configuration → rational box; `exists_isPerfectCuboid_iff` | theorem | Paulsen–West Prop. 3.1; Asiryan Prop. 1 | [#19](https://github.com/yachi/lean-playground/pull/19) |
| [`TwistedCuboid.lean`](LeanPlayground/PerfectCuboid/TwistedCuboid.lean) | E_N configuration | configurations are k-twisted perfect cuboids (`IsTwistedCuboid`) | theorem + infrastructure | new | [#21](https://github.com/yachi/lean-playground/pull/21) |
| [`TwistClass.lean`](LeanPlayground/PerfectCuboid/TwistClass.lean) | E_N configuration | twist k ≡ −X₁X₂X₃ (mod ℚ*²) | theorem | new | [#26](https://github.com/yachi/lean-playground/pull/26) |
| [`TwistRigidity.lean`](LeanPlayground/PerfectCuboid/TwistRigidity.lean) | twist framework | three of four sums in class k, fourth in 1 or k ⇒ k = 1; a cuboid exists ⟺ some E_N has a positive configuration | theorem | new | [#46](https://github.com/yachi/lean-playground/pull/46) |
| [`TwistTwo.lean`](LeanPlayground/PerfectCuboid/TwistTwo.lean) | twist framework | three face twists equal ⇒ s ∈ {1, 2} (both occur: (1,1,1), (23,289,527)); n-dimensional rigidity | theorem | new | [#47](https://github.com/yachi/lean-playground/pull/47) |
| [`ConjugateBox.lean`](LeanPlayground/PerfectCuboid/ConjugateBox.lean) | twist framework | conjugate boxes: prime factors of k are ≡ 1 (mod 8); half-twisted boxes: k ∣ c, odd primes ≡ 1 (mod 4) | partial | new | [#46](https://github.com/yachi/lean-playground/pull/46) |
| [`NearMissTwist.lean`](LeanPlayground/PerfectCuboid/NearMissTwist.lean) | brick / face cuboid | brick space twist ≡ 1 (mod 24); face-cuboid twist ≡ 1, 2, 5 (mod 8); 313921 prime example | theorem + example | new | [#46](https://github.com/yachi/lean-playground/pull/46) |
| [`QuadraticCuboid.lean`](LeanPlayground/PerfectCuboid/QuadraticCuboid.lean) | cuboids over ℤ√d | `IsQuadCuboid`; classification of rational-edged ℤ√d-cuboids (perfect / face with twist d / brick with space twist d / d-conjugate / d-half-twisted; at most two twists equal d); d < 0 or a prime p ≡ 3 (mod 4) dividing d ⇒ perfect cuboid over ℤ; d = 2 ⇒ perfect, face cuboid with twist 2, or half-twisted k = 2 | theorem | new (packaging of twist rigidity; descent for p ≡ 3 mod 4 classical) | [#49](https://github.com/yachi/lean-playground/pull/49) |
| [`Genocchi.lean`](LeanPlayground/PerfectCuboid/Genocchi.lean) | tool (congruent numbers) | p ≡ 3 (mod 8) and 2p (p ≡ 5 mod 8) are not congruent | theorem | Genocchi 1855 | [#34](https://github.com/yachi/lean-playground/pull/34) |
| [`TwoPrimeCongruent.lean`](LeanPlayground/PerfectCuboid/TwoPrimeCongruent.lean) | tool (congruent numbers) | the seven two-prime non-congruent classes C1–C7 | theorem | Lagrange 1974/75 | [#43](https://github.com/yachi/lean-playground/pull/43) |
| [`FermatTriangle.lean`](LeanPlayground/PerfectCuboid/FermatTriangle.lean) | tool | Fermat's right triangle theorem (1 is not congruent) | theorem | Fermat c. 1640 | [#5](https://github.com/yachi/lean-playground/pull/5) |
| [`GaussianQuartic.lean`](LeanPlayground/PerfectCuboid/GaussianQuartic.lean) | tool | x⁴ ± y⁴ = z² over ℤ[i] (Hilbert Satz 169); y² = x⁵ − x over ℤ[i] | theorem | Hilbert Zahlbericht; Najman; Szabó | [#28](https://github.com/yachi/lean-playground/pull/28) |
| [`SqrtTwoJacobi.lean`](LeanPlayground/PerfectCuboid/SqrtTwoJacobi.lean) | tool | Jacobi symbol (c₀/ℓ) for ℓ = c₀² − 2c₁² | theorem | Leonard–Williams background | [#35](https://github.com/yachi/lean-playground/pull/35) |
| [`LeonardWilliams.lean`](LeanPlayground/PerfectCuboid/LeonardWilliams.lean) | tool | unit-step invariance of the Leonard–Williams symbol | theorem | Leonard–Williams | [#37](https://github.com/yachi/lean-playground/pull/37) |

**Perfect cuboids: fibers and descent**

| File | Object | Headline statement(s) | Status | Attribution | PR |
|---|---|---|---|---|---|
| [`MasterTuple.lean`](LeanPlayground/PerfectCuboid/MasterTuple.lean) | brick | every primitive Euler brick comes from a master tuple (a, b, m, n) | theorem | Peschmann (arXiv:2604.28072); Cipollini (arXiv:2609.14526) | [#5](https://github.com/yachi/lean-playground/pull/5) |
| [`MasterTupleGcd.lean`](LeanPlayground/PerfectCuboid/MasterTupleGcd.lean) | brick | arithmetic of a master tuple (Peschmann §2) | theorem | Peschmann §2 | [#6](https://github.com/yachi/lean-playground/pull/6) |
| [`Fiber.lean`](LeanPlayground/PerfectCuboid/Fiber.lean) | perfect cuboid | every perfect cuboid lies on a fiber (m, n); reduction on a fiber | theorem | Peschmann §§3–4 | [#6](https://github.com/yachi/lean-playground/pull/6) |
| [`FiberPairs.lean`](LeanPlayground/PerfectCuboid/FiberPairs.lean) | perfect cuboid | three Pythagorean pair curves per fiber | infrastructure | Peschmann | [#24](https://github.com/yachi/lean-playground/pull/24) |
| [`FiberTwoOne.lean`](LeanPlayground/PerfectCuboid/FiberTwoOne.lean) | perfect cuboid | no perfect cuboid has two edges in ratio 3 : 4 (hand descent) | theorem | new (Fermat-style descent) | [#6](https://github.com/yachi/lean-playground/pull/6) |
| [`Descent.lean`](LeanPlayground/PerfectCuboid/Descent.lean) | perfect cuboid | generic descent for two right triangles with a common leg, given a finite check | theorem (conditional on a check) | new | [#7](https://github.com/yachi/lean-playground/pull/7) |
| [`DescentCheck.lean`](LeanPlayground/PerfectCuboid/DescentCheck.lean) | tool | residue checker `check` + `check_sound` | infrastructure | new | [#7](https://github.com/yachi/lean-playground/pull/7) |
| [`DescentClass.lean`](LeanPlayground/PerfectCuboid/DescentClass.lean) | tool | descent with the 2-Selmer class lemma | infrastructure | new | [#30](https://github.com/yachi/lean-playground/pull/30) |
| [`DescentTR.lean`](LeanPlayground/PerfectCuboid/DescentTR.lean) | tool | descent with the ±T₄ exception (family TR) | infrastructure | new | [#31](https://github.com/yachi/lean-playground/pull/31) |
| [`FiberDescent.lean`](LeanPlayground/PerfectCuboid/FiberDescent.lean) | perfect cuboid | no cuboid with edge ratio 5:12, 8:15, 7:24, …, 13:84, 28:45 | theorem | new | [#7](https://github.com/yachi/lean-playground/pull/7) |
| [`FiberDescentCert.lean`](LeanPlayground/PerfectCuboid/FiberDescentCert.lean) | perfect cuboid | certificates for the fiber descent | data | generated (`scripts/cuboid_cert.py`) | [#11](https://github.com/yachi/lean-playground/pull/11) |
| [`Fibers/F_p_q.lean`](LeanPlayground/PerfectCuboid/Fibers/) (98 files) | perfect cuboid | one fiber each | data + theorem | generated | #7–#12, #24, #25, #30, #31 |
| [`FiberList.lean`](LeanPlayground/PerfectCuboid/FiberList.lean) | perfect cuboid | 91 fibers ruled out; every cuboid lies on a fiber outside the list | theorem | new; fibers after Peschmann | [#12](https://github.com/yachi/lean-playground/pull/12) |
| [`Kubert.lean`](LeanPlayground/PerfectCuboid/Kubert.lean) | perfect cuboid | the curve E″ of a fiber (Kubert's ℤ/2×ℤ/8 curve); uniform facts | partial | Cipollini; Kubert | [#27](https://github.com/yachi/lean-playground/pull/27) |

**Euler bricks and parametric families (never perfect)**

| File | Object | Headline statement(s) | Status | Attribution | PR |
|---|---|---|---|---|---|
| [`Saunderson.lean`](LeanPlayground/PerfectCuboid/Saunderson.lean) | family | Saunderson bricks are never perfect (x⁴ + 18x²y² + y⁴ ≠ □) | theorem | Pocklington 1912, Spohn 1972 | [#35](https://github.com/yachi/lean-playground/pull/35) |
| [`DerivedCuboid.lean`](LeanPlayground/PerfectCuboid/DerivedCuboid.lean) | family | the derived brick (bc, ca, ab) of a Saunderson brick is never perfect | theorem | Chein 1977, Lagrange 1979, Leech 1981, Collins 1858 | [#39](https://github.com/yachi/lean-playground/pull/39) |
| [`EulerSecondFamily.lean`](LeanPlayground/PerfectCuboid/EulerSecondFamily.lean) | family | Euler's two-parameter family is never perfect (Pocklington's quartic) | theorem | Euler; Knill's notes | [#38](https://github.com/yachi/lean-playground/pull/38) |
| [`ColmanBrick.lean`](LeanPlayground/PerfectCuboid/ColmanBrick.lean) | family | Colman's degree-14 family is never perfect | theorem | Colman 1988 (Fib. Quart. 26) | [#43](https://github.com/yachi/lean-playground/pull/43) |
| [`BrickPrimePower.lean`](LeanPlayground/PerfectCuboid/BrickPrimePower.lean) | brick | prime-power edge of a brick: reduction to one equation, and an exponent gap | partial | new; question = Conjecture E (open) | [#44](https://github.com/yachi/lean-playground/pull/44) |
| [`BrickSupport.lean`](LeanPlayground/PerfectCuboid/BrickSupport.lean) | brick | prime support for p ≡ 3 (mod 4): 7 shapes; all 7 occur at (44,117,240) | theorem + example | new | [#47](https://github.com/yachi/lean-playground/pull/47) |
| [`LatticeBox.lean`](LeanPlayground/PerfectCuboid/LatticeBox.lean) | lattice box (A₃, hexagonal prism) | Eisenstein bricks (a²+ab+b² squares): derived-brick closure, the 7 bricks with edges ≤ 1500, primes ≡ 2 (mod 3) divide both a and b, a two-parameter polynomial family (`eisensteinBrick_family`, degree 14, proved by `ring`); no A₃ box or perfect hexagonal-prism box with edges ≤ 10⁵ | theorem + example | new (Eisenstein triples: OEIS A357274; perfect parallelepipeds: Sawyer–Reiter 2011) | [#49](https://github.com/yachi/lean-playground/pull/49) |

**Face cuboids**

| File | Object | Headline statement(s) | Status | Attribution | PR |
|---|---|---|---|---|---|
| [`FaceCuboid.lean`](LeanPlayground/PerfectCuboid/FaceCuboid.lean) | face cuboid | `IsFaceCuboid`; Theorem P′; edges a, b next to the irrational face are not prime powers; (153, 672, 104) | theorem | new | [#44](https://github.com/yachi/lean-playground/pull/44) |
| [`FaceCuboidThirdEdge.lean`](LeanPlayground/PerfectCuboid/FaceCuboidThirdEdge.lean) | face cuboid | third edge c is not a prime power (Theorem Q: (p^{2A}+1)(p^{2B}+1) ≠ □) | theorem | new | [#45](https://github.com/yachi/lean-playground/pull/45) |
| [`FaceCuboidLeech.lean`](LeanPlayground/PerfectCuboid/FaceCuboidLeech.lean) | face cuboid | 2⁴·3²·5²·7·13·17 ∣ abcefg (sharp); 2-adic shape | theorem | new (Leech-type table) | [#45](https://github.com/yachi/lean-playground/pull/45) |
| [`FaceCuboidDiagonal.lean`](LeanPlayground/PerfectCuboid/FaceCuboidDiagonal.lean) | face cuboid | prime-power space diagonal: structure (p ≡ 1 mod 4, p divides exactly one of a, b) | partial | new; uses Korec's uniqueness | [#45](https://github.com/yachi/lean-playground/pull/45) |
| [`AdjacencyNearMiss.lean`](LeanPlayground/PerfectCuboid/AdjacencyNearMiss.lean) | face cuboid (types A, B) | type-A (g²+c² = □) and type-B (u²−r² = □) face cuboids: odd twist primes not dividing c (resp. u) are ≡ 1 (mod 8); 2-adic shape (A: 4 ∣ c, g, h odd, twist ≡ 1 mod 8; B: r even); 3 ∣ c, 11 ∣ xyc (A), 3 ∣ r (B); Leech tables 2⁴·3²·5²·7·11·13·17·29·37 (A), 2⁴·3²·5²·7·13·17·29·37 (B); none with common edge ≤ 10⁷ | theorem | new | [#49](https://github.com/yachi/lean-playground/pull/49) |
| [`PellLeg.lean`](LeanPlayground/PerfectCuboid/PellLeg.lean) | tool | (x^{2m} − 1)(x^{2n} − 1) is never a square (Theorem P) | theorem | new | [#44](https://github.com/yachi/lean-playground/pull/44) |

**Edge cuboids**

| File | Object | Headline statement(s) | Status | Attribution | PR |
|---|---|---|---|---|---|
| [`EdgeCuboid.lean`](LeanPlayground/PerfectCuboid/EdgeCuboid.lean) | edge cuboid | `IsEdgeCuboid`; N is not a prime power; a Leech table; (520, 576, 618849) | theorem | Leech 1977 (example); new | [#44](https://github.com/yachi/lean-playground/pull/44) |
| [`EdgeCuboidTwoPrimes.lean`](LeanPlayground/PerfectCuboid/EdgeCuboidTwoPrimes.lean) | edge cuboid | N ≠ p^K q^L; N has ≥ 3 prime factors | theorem | new | [#45](https://github.com/yachi/lean-playground/pull/45) |
| [`LeechEdge.lean`](LeanPlayground/PerfectCuboid/LeechEdge.lean) | family | Leech's edge cuboids never have an integral third edge; `fermat_sub` | theorem | Leech 1977 (Amer. Math. Monthly 84) | [#43](https://github.com/yachi/lean-playground/pull/43) |
| [`ColmanEdge.lean`](LeanPlayground/PerfectCuboid/ColmanEdge.lean) | family | Bromhead–Colman edge cuboids: c is never a square (2-adic proof) | theorem | Bromhead 1960, Colman 1988 | [#43](https://github.com/yachi/lean-playground/pull/43) |

**Polynomial cuboids and bricks**

| File | Object | Headline statement(s) | Status | Attribution | PR |
|---|---|---|---|---|---|
| [`PolynomialCuboid.lean`](LeanPlayground/PerfectCuboid/PolynomialCuboid.lean) | polynomial | `IsPolyCuboid`; no constant edge; Mason–Stothers bound; coprime monomial edge impossible; linear edge ⇒ proportional | partial | new; Stoll–Testa context | [#46](https://github.com/yachi/lean-playground/pull/46) |
| [`PolyMonomialEdge.lean`](LeanPlayground/PerfectCuboid/PolyMonomialEdge.lean) | polynomial | monomial edge αX^k of any degree (no coprimality) ⇒ proportional; same for α(X − r)^k, so such a polynomial cuboid exists ⟺ an integer perfect cuboid exists | theorem | new | [#47](https://github.com/yachi/lean-playground/pull/47) |
| [`PolyBrick.lean`](LeanPlayground/PerfectCuboid/PolyBrick.lean) | polynomial | `IsPolyBrick`; Saunderson polynomial brick (6, 5, 5) is not proportional; linear edge αX and edge αX² ⇒ proportional; Mason–Stothers radical bound; every polynomial brick specializes to an integer Euler brick | partial | new | [#47](https://github.com/yachi/lean-playground/pull/47) |
| [`PolySpecialize.lean`](LeanPlayground/PerfectCuboid/PolySpecialize.lean) | polynomial | any polynomial cuboid specializes to an integer perfect cuboid, so polynomial cuboids exist ⟺ perfect cuboids exist | theorem | new | [#47](https://github.com/yachi/lean-playground/pull/47) |
| [`PolyCharP.lean`](LeanPlayground/PerfectCuboid/PolyCharP.lean) | polynomial (char p) | cuboids over K[X] for any field: char 2 trivial; with i² = −1, a²+b²+c² = 0 gives degenerate non-proportional cuboids; −1 not a square ⇒ every cuboid nondegenerate; **Frobenius cuboid** (X − X^p, i(X + X^p), X^(p+1) + 1): nondegenerate non-proportional cuboids over 𝔽_p[X] for every p ≡ 1 (mod 4); `natDegree_hyp` fails in char 5 | theorem + example | new | [#49](https://github.com/yachi/lean-playground/pull/49) |

</details>

#### What is still open


1. **Two-twist rigidity**: conjugate boxes (k d² = a²+b², k e² = a²+c², f, g integral) and half-twisted boxes (k d² = a²+b², k g² = a²+b²+c², e, f integral). Do nontrivial k occur? None with f ≤ 10⁷, resp. c ≤ 3·10⁶. The fibers have genus 3, so this is Faltings-level.
2. **Half-twisted k = 2** (pattern (2,1,1,2)): even the single value k = 2 is open. The degenerate box (a, a, 0) blocks congruence arguments.
3. **Non-proportional polynomial cuboids over ℚ**: is every polynomial cuboid over `ℚ[X]` proportional? Monomial and single-root edges are done (`PolyMonomialEdge.lean`). The general case is open, and so is whether Stoll–Testa's conics in G are degenerate. Over `𝔽_p[X]`, `p ≡ 1 (mod 4)`, the answer is no (the Frobenius cuboid, `PolyCharP.lean`); for `p ≡ 3 (mod 4)` no cuboid over `𝔽_p[X]` is known (none for p = 3 up to degree 7).
4. **d·e = □** (the product of two face diagonals): there is no one-triangle method, since (de)² = (ag)² + (bc)² mixes triangles.
5. **Face-cuboid g = p^k leftovers**: `FaceCuboidDiagonal.lean` gives the structure only. The case where p divides exactly one of a, b is not excluded.
6. **Face-diagonal 2^s p^k, family F2 types II/III** (`FaceDiagonalF2.lean`): partial.
7. **Conjecture E** (an Euler brick with a prime-power edge does not exist): only the reduction and the exponent gap are proved; likely out of reach of these methods.
8. **T3.3** (g = p^k q^l for a perfect cuboid): open; likely out of reach of these methods.
9. **Rank ≥ 2 beyond Asiryan**: no route from "E_N has rank ≥ 2" to a contradiction is known. The rank-one case itself no longer needs Ingram if `QuarterFree N` holds (`KummerDescent.lean`, `not_inRankOne_of_quarterFree`): `QuarterFree N` is equivalent to "no rational perfect cuboid with abcg = 2Ns² has cg(ef+ab) and 2(ef+ab)(ef+ab+cg) both square" (`quarterFree_iff`), and it cannot be proved by congruences, because the degenerate box satisfies the two square conditions (see 14).
10. **The fibers**: 91 fibers are ruled out, and every perfect cuboid lies on one of the infinitely many fibers that remain.
11. **Type-A and type-B face cuboids** (`Adjacency.lean`, `AdjacencyNearMiss.lean`): do any exist? None has common edge ≤ 10⁷, and none is among the 126 known primitive face cuboids. Equivalently: is there a Pythagorean triple with a fourth number adjacent to all three sides, other than a perfect cuboid?
12. **Cuboids over ℤ√d with irrational edges** (`QuadraticCuboid.lean`): rational-edged ones are classified; none with irrational edges was found for |d| ≤ 13, |x|, |y| ≤ 120, and none is excluded. For d = 2 the face cuboid with twist 2 and the half-twisted k = 2 box remain.
13. **A₃ boxes and the Eisenstein family** (`LatticeBox.lean`): no perfect box in the 60° lattice with edges ≤ 10⁵; whether the family point has infinite order on the genus-one curve a²+ab+b² = □, a²+ac+c² = □ is open.
14. **Theorem K / `QuarterFree`** (`KummerDescent.lean`, `QuarterTriangle.lean`, `QuarterCharacters.lean`): is a derived triangle of a box with integral d, e, g (relabelled: `(ag, bc, de)` with ag odd) ever a *quarter triangle*, i.e. `ag = k(σδ)²`, `de + bc = kσ⁴`, `de − bc = kδ⁴`, `σ² + δ² = 2τ²`, k = gcd(ag, bc)? Equivalently (Kummer): is the triangle point ever divisible by 4 on E_N? "Never" would make Asiryan's rank ≥ 2 unconditional in Lean (`not_inRankOne_of_quarterFree`), but only that: rank ≥ 2 does not exclude a cuboid. Known: none among the 126 face cuboids, none with de ≤ 10¹¹; the condition is satisfiable by Pythagorean triangles alone ((49, 1200, 1201)) and by the degenerate box, so a proof must use c > 0 globally. The rank-one system in Asiryan's variables is a surface (fibres of genus 49 over the u-line), so no curve-level descent applies.

#### Details by file

| Result | Lean |
|---|---|
| (44, 117, 240) is an Euler brick, but its space diagonal √73225 is not an integer | `eulerBrick_44_117_240`, `not_perfectCuboid_44_117_240` |
| Saunderson's formula: a Pythagorean triple gives an Euler brick; there are infinitely many | `saunderson`, `infinite_eulerBricks` |
| Every Euler brick: two edges divisible by 3, two by 4; some edge by 5, 9, 11 and 16 | `IsEulerBrick.two_dvd_three`, `two_dvd_four`, `five_dvd`, `nine_dvd`, `eleven_dvd`, `sixteen_dvd` |
| Every perfect cuboid: some edge divisible by 7 and by 19 | `IsPerfectCuboid.seven_dvd`, `nineteen_dvd` |
| An edge or the space diagonal divisible by 13; an edge or a diagonal by 17, 29, 37 | `thirteen_dvd`, `seventeen_dvd`, `twentynine_dvd`, `thirtyseven_dvd` |

Most proofs check every triple of residues modulo `m` with `decide +kernel`. Divisibility by 16
is not decided by residues modulo any small power of 2, so it is proved by descent.

`Contradiction.lean` assumes a perfect cuboid exists and pushes the assumption as far as these
methods go. `IsPerfectCuboid.exists_normalForm` gives a primitive one with exactly one odd edge,
an odd space diagonal, `12640320 = 2⁶·3³·5·7·11·19` dividing `abc`, and longest edge at least 233.
`no_congruence_obstruction` shows where the argument stops: for every `m`, the triple `(m, 3, 4)`
satisfies all four equations modulo `m`, because it is congruent to the flat cuboid `(0, 3, 4)`.
So congruences alone can never give a contradiction.

Three further files formalize the ingredients of the recent fiber-by-fiber attacks on the problem
(Peschmann, [arXiv:2604.28072](https://arxiv.org/abs/2604.28072); Cipollini,
[arXiv:2609.14526](https://arxiv.org/abs/2609.14526)):

| File | Result | Lean |
|---|---|---|
| `FermatTriangle.lean` | Fermat's right triangle theorem: no Pythagorean triangle has square area; `m n (m² − n²)` is never a square; `a² ± b²` are not both squares; 1 is not a congruent number | `FermatTriangle.not_isSqAreaTriangle`, `not_isSquare_mul_mul_sq_sub_sq`, `not_isSquare_sq_add_sq_and_sq_sub_sq`, `not_congruent_one` |
| `MasterTuple.lean` | Every primitive Euler brick comes from two Pythagorean pairs `(a, b)`, `(m, n)` sharing an edge (the *master tuple*), and conversely | `IsEulerBrick.exists_masterTuple`, `isEulerBrick_of_euclidLegs`, `exists_euclidLegs` |
| `SpaceDiagonal.lean` | In a primitive perfect cuboid every prime factor of the space diagonal is `≡ 1 (mod 4)`, so the diagonal is `≡ 1 (mod 4)` | `IsPerfectCuboid.prime_dvd_space_diagonal`, `space_diagonal_mod_four` |
| `Korec.lean` | Korec (Math. Slovaca 42, 1992), Theorem 5.1: the space diagonal of a perfect cuboid is neither a prime power nor a product of two primes. The prime-power case is Euler's uniqueness of the representation of `p^m` as a sum of two squares; for `pq` we replace Korec's parametrization and Pocklington's theorem on `x⁴ + 18x²y² + y⁴` by a twelve-case polynomial argument that uses that `q` is prime | `IsPerfectCuboid.ne_prime_pow`, `IsPerfectCuboid.ne_prime_mul_prime`, `Korec.sq_add_sq_unique`, `Korec.sq_add_sq_factor` |
| `Leech.lean` | Leech (Guy, D18): `2⁸ · 3⁴ · 5³ · 7 · 11 · 13 · 17 · 19 · 29 · 37` divides the product `abcdefg` of the edges and all four diagonals. Each prime power is a congruence check modulo `128, 27, 5` or `p`, on the squares of a unit edge and the profiles `(x² mod pʲ, min(v_p(x), j))` of the other two, after dividing out common factors | `Leech.leech_dvd`, `IsPerfectCuboid.leech_dvd` |

Fermat's theorem is proved by his infinite descent on primitive triangles (Mathlib has the
related `not_fermat_42`, but neither statement follows from the other directly). It is the one
step in the fiber papers that is uniform in `(m, n)`.

Two more files formalize the rest of Peschmann's argument. The *fiber* `(m, n)` turns out to
have a plain meaning: a brick lies on it when two of its edges are in the ratio
`(m² − n²) : 2mn` (for `(2, 1)` that is `3 : 4`), and every perfect cuboid lies on some fiber.

| File | Result | Lean |
|---|---|---|
| `MasterTupleGcd.lean` | §2: `f₁ = L · R` with `L, R` sums of two squares; `g₊ · g₋ = gcd(U₁, U₂)` with `g₊, g₋` coprime; `g₊² ∣ R`, `g₋² ∣ L`; scaling | `MasterTupleGcd.f₁_eq`, `gcd_mul_gcd`, `coprime_gPlus_gMinus`, `gPlus_sq_dvd`, `gMinus_sq_dvd`, `IsPerfectCuboid.mul`, `of_mul` |
| `Fiber.lean` | §§3–4: the genus-3 curve `H_{m,n}`, its quotients `E₃` and `E_uV`, the trivial points, and Theorem 4.5: if `E₃` has no rational point with `w ≠ 0` (or `E_uV` has no nontrivial lift), no perfect cuboid lies on the fiber | `Fiber.onH_iff_onE3`, `OnH.toEuV`, `IsPerfectCuboid.onH`, `eq_trivial_of_e3Trivial`, `IsPerfectCuboid.not_onFiber_of_e3Trivial`, `IsEulerBrick.exists_fiber`, `not_isPerfectCuboid_of_forall` |
| `FiberTwoOne.lean` | The fiber `(2, 1)`, unconditionally: no perfect cuboid has two edges in ratio `3 : 4`, because `p² + 16q²` and `p² + 25q²` are never both squares for `p, q ≠ 0` (an elementary descent on the rank-0 curve `y² = x(x + 16)(x + 25)`) | `not_isPerfectCuboid_three_four`, `not_sq_add_sixteen_sq_and_sq_add_twentyfive_sq`, `not_isSquare_sq_add_sixteen_and_sq_add_twentyfive` |
| `DescentCheck.lean`, `Descent.lean` | The descent of `FiberTwoOne.lean` for any pair `(p, q)` with `gcd(p, q) = 1` and `p < q`, with `D = q² − p²` a square `a²` or not, `p` even or odd (only one size bound changes: `4 (k₁k₂)² ≤ p² e²` for even `p`, `(k₁k₂)² ≤ p² e²` for odd `p`, see `boundK`). After a sign argument, a case gives a smaller solution exactly when it is the image of a torsion point; the two possible torsion classes give three families of formulas (one linear, two quadratic representations of the translate by a `4`-torsion point), proved once for all `(p, q)` and recognized by `torsionOK`. For the second quadratic family the size comparison may instead go through a finite search over a box of small `(β, γ)` (`smallCheck`). Every other case is ruled out by a congruence, checked by the kernel (`decide +kernel`, proved sound by `check_sound`): either by trying every modulus (`fiberCheck`), or, much faster, by replaying a certificate that names the one torsion family or modulus for each case (`fiberCheckCert`). Certificates are generated by `scripts/cuboid_cert.py`, which mirrors the case list and the checks in Python. Only family L (the trivial class, `qλ`, `Dλσ`, `Dqσ` squares) and the range `σ ∣ λ'² D` see `D`; for `D` not a square the cases are listed by `fiberCasesD` and the certificate gives `CoveredD p q D` (`fiberCheckCertD`). This works when the curve has rank 0 and `Ш[2] = 0` | `Descent.not_isSol`, `Descent.not_isSolD`, `Descent.not_isSquare_sq_add_sq_and_sq_add_sq`, `Descent.torsionOK_sound`, `Descent.check_sound`, `Descent.coveredOn_of_fiberCheckCert`, `Descent.covered_of_fiberCheck` |
| `FiberDescentCert.lean`, `FiberDescent.lean` | The fibers `(3, 2)`, `(4, 1)`, `(4, 3)`, `(6, 1)`, `(8, 1)`, `(7, 6)` and `(7, 2)`, unconditionally: no perfect cuboid has two edges in ratio `5 : 12`, `8 : 15`, `7 : 24`, `12 : 35`, `16 : 63`, `13 : 84` or `28 : 45` (pairs `(12, 13)`, `(8, 17)`, `(24, 25)`, `(12, 37)`, `(16, 65)`, `(84, 85)` and `(28, 53)`, on the rank-0 curves `y² = x(x + p²)(x + q²)`). The generic descent also re-proves `3 : 4`. The certificates (`FiberDescentCert.lean`) are generated by `python3 scripts/cuboid_cert.py --certs-only 2,1 3,2 4,1 4,3 6,1 8,1 7,6 7,2 -o LeanPlayground/PerfectCuboid/FiberDescentCert.lean` | `not_isPerfectCuboid_five_twelve`, `not_isPerfectCuboid_eight_fifteen`, `not_isPerfectCuboid_seven_twentyfour`, `not_isPerfectCuboid_twelve_thirtyfive`, `not_isPerfectCuboid_sixteen_sixtythree`, `not_isPerfectCuboid_twentyeight_fortyfive`, `not_isPerfectCuboid_thirteen_eightyfour`, `not_isSquare_sq_add_144_and_sq_add_169`, `not_isSquare_sq_add_64_and_sq_add_289`, `not_isSquare_sq_add_576_and_sq_add_625`, `not_isSquare_sq_add_144_and_sq_add_1369`, `not_isSquare_sq_add_256_and_sq_add_4225`, `not_isSquare_sq_add_7056_and_sq_add_7225`, `not_isSquare_sq_add_784_and_sq_add_2809`, `Descent.not_isSol_four_five` |
| `Fibers/F_<p>_<q>.lean` | 33 more fibers, one generated module each (so that each build stays within a few GB), unconditionally: no perfect cuboid has two edges in ratio `36 : 77`, `65 : 72`, `44 : 117`, `24 : 143`, `17 : 144`, `85 : 132`, `119 : 120`, `52 : 165`, `60 : 221`, `68 : 285`, `136 : 273`, `152 : 345`, `135 : 352`, `228 : 325`, `87 : 416`, `203 : 396`, `132 : 475`, `155 : 468`, `100 : 621`, `429 : 460`, `52 : 675`, `156 : 667`, `37 : 684`, `333 : 644`, `56 : 783`, `273 : 736`, `432 : 665`, `96 : 247`, `336 : 377`, `396 : 403`, `336 : 527`, `400 : 561` or `684 : 1363`. These are all the fibers with `q ≤ 829` whose curve has rank 0 and `Ш[2] = 0` (PARI/GP), except `(748, 773)`, `(468, 757)` and `(540, 829)`: their certificates exist, but the prime `q` is needed as a modulus, and one residue check modulo a prime that size takes minutes and several GB of kernel memory. Each file is `python3 scripts/cuboid_cert.py m,n -o …` (pair `(V, W)`) | `not_isPerfectCuboid_thirtysix_seventyseven`, …, `not_isPerfectCuboid_684_1363`, and `not_isSquare_sq_add_<p²>_and_sq_add_<q²>`, `Descent.not_isSol_<p>_<q>` for each pair (numbers below 100 are spelled as words, e.g. `Descent.not_isSol_seventytwo_ninetyseven`, `not_isPerfectCuboid_sixtyfive_seventytwo`) |
| `FiberPairs.lean` | On the fiber `(m, n)`, with `U = m² − n²`, `V = 2mn`, `W = m² + n²`, a perfect cuboid with edges `X = Vk`, `Y`, `Z = Uk` makes `Y² + U²k²`, `Y² + V²k²` and `Y² + W²k²` all squares, so it gives a solution of the descent for each of the three pairs `(V, W)`, `(U, W)`, `(U, V)`, and the descent for any one of them rules the fiber out. The three curves `y² = x(x + p²)(x + q²)` have different ranks | `IsPerfectCuboid.isSol_three_pairs`, `IsPerfectCuboid.not_onFiber_of_pair` |
| `Fibers/F_<U>_<W>.lean` (odd `p`) | 21 more fibers through the pair `(U, W)`, i.e. the curve `y² = x(x + U²)(x + W²)`, where the pair `(V, W)` has rank ≥ 1 or `Ш[2] ≠ 0`: no perfect cuboid has two edges in ratio `21 : 20`, `33 : 56`, `99 : 20`, `91 : 60`, `51 : 140`, `57 : 176`, `187 : 84`, `27 : 364`, `207 : 224`, `323 : 36`, `299 : 180`, `35 : 612`, `297 : 304`, `261 : 380`, `437 : 84`, `459 : 220`, `259 : 660`, `513 : 184`, `493 : 276`, `651 : 260` or `775 : 168`. These are all the fibers with `W ≤ 800` whose `(U, W)` curve has rank 0 and `Ш[2] = 0` and that the pair `(V, W)` does not already reach. Each file is `python3 scripts/cuboid_cert.py m,n,UW -o …` | `not_isPerfectCuboid_twenty_twentyone`, …, `not_isPerfectCuboid_168_775`, `Descent.not_isSol_twentyone_twentynine`, … |
| `Fibers/F_<min(U,V)>_<max(U,V)>.lean` (`D` not a square) | 24 more fibers through the pair `(U, V)`, i.e. the curve `y² = x(x + U²)(x + V²)`. Here `V² − U²` is not a square, so the descent runs with `D = q² − p²` (`Descent.not_isSolD`, certificates `fiberCheckCertD`): no perfect cuboid has two edges in ratio `9 : 40`, `105 : 88`, `15 : 112`, `133 : 156`, `19 : 180`, `21 : 220`, `115 : 252`, `255 : 32`, `175 : 288`, `75 : 308`, `319 : 360`, `399 : 40`, `435 : 308`, `279 : 440`, `465 : 368`, `231 : 520`, `455 : 528`, `165 : 532`, `385 : 552`, `589 : 300`, `595 : 468`, `627 : 364`, `629 : 540` or `533 : 756`. These are all the fibers with `max(U, V) ≤ 800` whose `(U, V)` curve has rank 0 and `Ш[2] = 0` and that the other two pairs do not already reach; they include `(26, 9)` and `(27, 10)`, which the other pairs could not reach in practice (their prime `W` was needed as a modulus). As far as we know no one had used this curve for a rank-0 argument before (Cipollini, arXiv:2609.14526, uses it only in rank-one sieves). Each file is `python3 scripts/cuboid_cert.py m,n,UV -o …` | `not_isPerfectCuboid_nine_forty`, …, `not_isPerfectCuboid_533_756`, `Descent.not_isSol_nine_forty`, … |
| `DescentClass.lean`, `Fibers/F_54264_133225.lean`, `Fibers/F_1215696_1221025*.lean` | The fibers `(19, 2)` and `(31, 12)` through `E″` (`Kubert.lean`), i.e. the pair `(2UV, W²)` = `(54264, 133225)` and `(1215696, 1221025)`: no perfect cuboid has two edges in ratio `357 : 76` or `817 : 744`. The plain case list has millions of cases, so `DescentClass.lean` groups them by `λ` and by the square class `σ₀` of `σ = σ₀t²` (divisors listed from factorizations, `facOf`, `divsF`, `sqGroups`) and kills a whole group when its `2`-descent class `(qλ, Dλσ₀)` is not in the `2`-Selmer group, as seen modulo one prime power (the class lemma `Descent.classKill_sound`, keys stored in a binary tree `KTree`). Of `6400` and `80000` groups only `32` and `48` survive; their `19852` and `233240` cases go to the torsion families. Family QK searches its small cases only under the hyperbolas `|γδ| ≤ X`, `|αβ| ≤ Y` (`hypCheck`) when that is cheaper than the box. Each file is `python3 scripts/cuboid_class_cert.py [--parts K] m,n`; `(31, 12)` is split over five modules | `Descent.casesOn_of_classCert`, `Descent.CasesOn.casesOK`, `Descent.classKill_sound`, `Descent.hypCheck_sound`, `not_isPerfectCuboid_seventysix_357`, `not_isPerfectCuboid_744_817` |
| `DescentTR.lean`, `Fibers/F_<U²>_<V²>_sq*.lean` | The fibers `(14, 5)`, `(30, 7)` and `(39, 38)` through `E″` itself, i.e. the pair `(U², V²)` (sorted) = `(19600, 29241)`, `(176400, 724201)` and `(5929, 8785296)`: no perfect cuboid has two edges in ratio `171 : 140`, `851 : 420` or `77 : 2964`. A cuboid gives a solution with `M² ≠ pq e²` (`IsPerfectCuboid.not_onFiber_of_sq`), but this pair also has the solutions `M² = pq e²` of the point `T₄` of order `4`, so the descent proves that every solution has `M² = pq e²`. The steps L, QD and QK of `Descent.lean` keep `M² ≠ pq e²` (`exists_case`); the cases in the class of a point of order `8` use the new family **TR**: the half-point `Q` of the solution minus a torsion point `T = (d₁, y_T)` of order `8`, with `x(Q − T) = (M′/e′)²` an explicit formula (`tr_sq`). If `Q − T` is `O`, `(0, 0)` or `±T₄`, then the solution is `±T₄`; each of these makes a binary form vanish, and a certificate `N G^k = R Z` with explicit coefficient lists shows that the `T₄` form `G` vanishes too (`trCert_sound`). The class tests modulo `N > 10⁵` (such as `593²` for `(39, 38)`) test squares by Euler's criterion (`classCheckE`, `sqTestE_of_sq`) instead of the bitmask of squares, which would take over 12 GB of kernel memory. Each file is `python3 scripts/cuboid_class_cert.py --sq [--parts K] m,n`; `(30, 7)` and `(39, 38)` are split over four and eight modules (so that each build stays under about 9 GB) | `Descent.trOK_sound`, `Descent.sq_eq_of_isSol_of_casesOKT`, `Descent.classCheckE_sound`, `Kubert.IsPerfectCuboid.not_onFiber_of_sq`, `not_isPerfectCuboid_140_171`, `not_isPerfectCuboid_420_851`, `not_isPerfectCuboid_seventyseven_2964` |
| `FiberList.lean` | The 91 fibers above in one statement: `provedFibers` lists the pairs `(m, n)`; no perfect cuboid has two edges `X, Z` with `(m² − n²) X = 2mn Z` for `(m, n)` in the list, so every perfect cuboid lies on a fiber outside it. The method only reaches fibers where one pair has rank 0 and `Ш[2] = 0`: of the 331 fibers with `m ≤ 40`, 70 for `(V, W)`, 88 for `(U, W)`, 98 for `(U, V)`, 179 for at least one | `provedFibers`, `IsPerfectCuboid.not_onFiber_of_mem`, `IsPerfectCuboid.exists_fiber_not_mem` |
| `Kubert.lean` | The fifth elliptic quotient `E″ : Y² = (X + V²W²)(X + U²W²)(X + U²V²)` of a fiber (Fable round 5, F3). A perfect cuboid gives a point of `2E″` with `X > 0`. Moving a root to `0` makes `E″` the pair curve of `(U², V²)`, which is `2`-isogenous to the pair curve `(2UV, W²)`, the pair `(V, W)` of the fiber `(U, V)`. `E″` is Kubert's curve with torsion `ℤ/2 × ℤ/8` at `τ = m(m + n)/(m² + 2mn − n²)` (checked as an explicit change of variables). **Uniform torsion lemma**: for `0 < n < m` no torsion point with `X > 0` is twice a rational point, since `X(P₈) + U²V² = (2m(m + n))² · mn(m² − n²)` and Fermat's right triangle theorem applies. So if `E″(ℚ)` is its torsion (rank `0`, a hypothesis here, true for 112 of the 331 fibers with `m ≤ 40` by PARI/GP, among them `(8, 3)` where `Ш(E″)[2] ≠ 0`), the fiber has no perfect cuboid | `onEpp_of_sq`, `IsPerfectCuboid.exists_onEpp`, `isSol_sq`, `isSol_isogeny`, `IsPerfectCuboid.not_onFiber_of_isogeny`, `kubertChange_smul`, `onEpp_of_mem_torsionPts`, `not_isSquare_of_mem_torsionPts`, `IsPerfectCuboid.not_onFiber_of_torsionOnly` |

Theorem 4.5 is formalized *conditionally*. Its hypotheses (`E3Trivial m n`, `EuVLiftTrivial m n`)
say that an elliptic curve has rank 0 and known torsion. Peschmann checks them for 1,072 fibers
with PARI and, via modularity and Kolyvagin's theorem, with modular symbols; Mathlib cannot do
that, so they stay as explicit hypotheses rather than `sorry`s.

`CongruentRank.lean` takes a different route that applies to every perfect cuboid at once.
Paulsen and West (Houston J. Math. 48, 2022) map a perfect cuboid to three points on the
congruent-number curve `E_N : Y² = X³ − N²X`, `N = sf(abcg/2)`, and claim that `E_N` then has
rank at least two. V. Asiryan, [*On the Rank Condition for Perfect
Cuboids*](https://arxiv.org/abs/2610.10643) (arXiv, 2026-10), finds a gap in their proof and
repairs it. The file proves the parts of that argument that Mathlib's group law can reach.

| Paper | Result | Lean |
|---|---|---|
| Prop 1 | A perfect cuboid gives three points of `E_N` with `−N < Xᵢ < 0` and `X₁X₂ + X₁X₃ + X₂X₃ = N²` (a positive cuboid configuration), for squarefree `N` with `abcg/2 = Ns²` | `IsPerfectCuboid.exists_config`, `CongruentRank.exists_config`, `cuboid_compat` |
| Lemma 1 | `±Q₁ ± Q₂ ± Q₃ ≠ S = (0, 0)`. Proved with Vieta's formulas instead of Riemann–Roch: the sum would force `(X₁² − N²)(X₂² − N²)(X₃² − N²) = 0` | `CongruentRank.add_add_ne_S`, `vieta_add` |
| Prop 2 (the gap) | Replacing `G` by `G + T` swaps the sequences `A_k(G) = kG + ε(k)S` and `B_k(G) = A_k(G) + T` only for odd `k`. For even `k` the swap claimed by Paulsen–West fails for every `G`, and `A_k`, `B_k` never share an `X`-coordinate | `A_add_T_of_odd`, `A_add_T_of_even`, `A_add_T_ne_B_of_even`, `HasX.ne_of_add_T` |
| §6.1, §6.4 | For the pattern `(aG, bG + T, cG + S + T)` the compatibility condition is `X_aX_b + X_aX_c − X_bX_c + N² = 0` (eq. 24), and `b = a + c` or `c = a + b` contradicts Lemma 1 | `eq24`, `eq24_ne`, `not_pattern` |
| Lemmas 2, 3 | A configuration inside `ℤG + E_N[2]` can be brought to the pattern `(aG, bG + T, cG + S + T)`, `a, b` odd, `c` even, now **unconditional** (the torsion hypothesis of Remark 1 is proved in `Torsion.lean`). Equation (18) `t(kG) = P_k(z)/Q_k(z)` with `N`-free integer polynomials comes from the division-polynomial formula for `n • P` and a weighted-homogeneity scaling (`DivPolyScale.lean`); Lemma 2 is the rational root theorem on `Z` (eq. 21); Lemma 3 is a descent on `k₁ + k₂ + k₃` through `G ↦ G + T` and `G ↦ 2G + S` (`RankOneReduction.lean`) | `rankOneReduction_of_pos`, `rankOneReduction_of_torsion`, `rankOneReduction`, `hasX_pt`, `not_excluded`, `pattern_of_pt`, `aeval_bigZ_ne_zero`, `sub_Φ`, `sub_ΨSq` |
| `n • P` | `n • (x, y) ≠ 0 ⇒ ΨSqₙ(x) ≠ 0` and `X(n • (x, y)) = Φₙ(x)/ΨSqₙ(x)` on any Weierstrass curve over a field, from the Tau Ceti project's `zsmul_point_eq_smulEval` (vendored, see below) | `WeierstrassCurve.exists_zsmul_some_eq`, `CongruentRank.divPolyX` |
| Remark 1 | `E_N(ℚ)_tors = {0, S, T, U}` for every rational `N ≠ 0` (Koblitz, Ch. I §9). No point of order `4`, by the doubling formula. No point of odd prime order `ℓ`: Dirichlet gives a prime `p ≡ 3 (mod 4)`, `p ≡ 1 (mod ℓ)` prime to the denominators of the point and of `N`; reducing through `ℤ_[p]` gives a nonzero point of `E_N(𝔽_p)` killed by `ℓ` (since `ΨSq_ℓ(x̄) = 0`), but `#E_N(𝔽_p) = p + 1 ≢ 0 (mod ℓ)`. So every point with `Y ≠ 0`, in particular every point of a configuration, has infinite order | `torsionTwo`, `add_self_eq_zero_of_four`, `eq_zero_of_prime_nsmul`, `exists_reduction`, `WeierstrassCurve.Affine.natCard_point`, `WeierstrassCurve.zsmul_eq_zero_iff`, `nonTors_of_hasX` |
| Thm 1 (rank one) | No positive configuration lies in `ℤG + E_N[2]`, **conditional** only on the primitive-divisor step (§6.2–6.3) | `not_rankOne_of_primitiveDivisorStep`, `not_rankOne_of_torsion`, `not_rankOne`, `PrimitiveDivisorStep` |

`ConfigCuboid.lean` goes back from a configuration to a cuboid. Each point gives a right triangle
of area `N` with leg `Uᵢ = 2NYᵢ/(N² − Xᵢ²)`; the box with edges `|U₁|, |U₂|, |U₃|` always has a
rational space diagonal, and if one face diagonal is rational then all three are. So the converse
of Prop 1 needs one extra condition, which the identities alone do not give.

| Result | Lean |
|---|---|
| `U₁² + U₂² + U₃² = (U₁U₂U₃/2N)²` and `(U₁² + U₃²)H₂² = (U₁² + U₂²)H₃²` for every configuration | `IsConfigPts.space`, `IsConfigPts.face₁₃`, `face_poly` |
| The box with edges `\|Uᵢ\|` is a rational perfect cuboid iff `U₁² + U₂²` is a square | `IsConfigPts.isRatCuboid_iff` |
| A perfect cuboid exists iff some `E_N` has a positive configuration with `U₁² + U₂² = □` | `exists_isPerfectCuboid_iff` |

`TwistedCuboid.lean` names what a configuration is without that extra condition. A
**`k`-twisted perfect cuboid** has rational edges `a, b, c` and space diagonal `g`, and face
diagonals rational up to the same factor `√k`: `a² + b² = kd²`, `a² + c² = ke²`, `b² + c² = kf²`.
Every configuration is one, with `k = U₁² + U₂²`, and `k = 1` is a perfect cuboid. So the square
condition is automatic only if no twisted perfect cuboid with `k ∉ ℚ*²` exists, which is as open as
the perfect cuboid problem. A search over all integer boxes with edges up to 6000 found none.
Asiryan (Definition 1, Corollary 1) and Paulsen–West (Proposition 3.1) state the
configuration-to-cuboid direction without this condition.

| Result | Lean |
|---|---|
| Prop 1 works for twisted cuboids, with `de, df, ef` replaced by `kde, kdf, kef` | `isConfigPts_of_twistedCuboid` |
| A configuration is a `k`-twisted perfect cuboid with `k = U₁² + U₂²` | `IsConfigPts.isTwistedCuboid` |
| For each `k`: a configuration with `U₁² + U₂² ∈ k·ℚ*²` exists iff a `k`-twisted perfect cuboid does | `exists_config_iff_exists_twistedCuboid` |
| A configuration exists iff a `k`-twisted perfect cuboid exists for some `k` | `exists_config_iff` |
| A perfect cuboid exists iff a `1`-twisted one does; only the class of `k` in `ℚ*/ℚ*²` matters | `exists_isPerfectCuboid_iff_twisted`, `isTwistedCuboid_one_iff`, `IsTwistedCuboid.of_mul_sq` |
| Every prime `q ≡ 3 (mod 4)` divides `k` to an even power (`k` is a sum of two squares) | `IsTwistedCuboid.even_padicValRat`, `even_padicValRat_sq_add_sq` |

`TwistClass.lean` computes the twist from the `X`-coordinates alone:
`U₁² + U₂² = −X₁X₂X₃·(2N(X₁ + X₂)/(Y₁Y₂))²`, so `k ≡ −X₁X₂X₃ (mod ℚ*²)`. Since `X mod ℚ*²` is the
`2`-isogeny descent map of `E_N`, a configuration is a perfect cuboid exactly when
`Q₁ + Q₂ + Q₃ + (0, 0)` lies in the image of the dual isogeny (this interpretation is not
formalized). It never excludes a configuration on its own.

| Result | Lean |
|---|---|
| `U₁² + U₂² = −X₁X₂X₃·(2N(X₁ + X₂)/(Y₁Y₂))²` for every configuration | `IsConfigPts.twist_class` |
| The box with edges `\|Uᵢ\|` is `k`-twisted iff `k > 0` and `k·(−X₁X₂X₃) = □`; perfect iff `−X₁X₂X₃ = □` | `IsConfigPts.isTwistedCuboid_iff_isSquare`, `IsConfigPts.isRatCuboid_iff_isSquare` |
| A perfect cuboid exists iff some `E_N` has a positive configuration with `−X₁X₂X₃ = □` (and the same for each `k`) | `exists_isPerfectCuboid_iff'`, `exists_config_iff_exists_twistedCuboid'` |
| In cuboid coordinates: `2(kde + bc)(kdf + ac)(kef + ab) = kg²(af + be + cd)²`, so Prop 1's configuration has `k·(−X₁X₂X₃) = (2N²s/(af + be + cd))²` | `IsTwistedCuboid.twist_identity`, `IsRatCuboid.twist_identity`, `twist_class_of_twistedCuboid` |

`GaussianQuartic.lean` and `BeauvilleLambda.lean` rule out one square class of perfect cuboids.
In `ℤ[i]` put `p = a + g` and `q = b − ic`. Then `pq(p⁴ − q⁴) · 8(a+g)(f+b)(e+a)(g+e)(d+a)(g+d)`
is a square, so `p/q` is a point on a quadratic twist of the genus-two curve `y² = x⁵ − x`. When
that twist is trivial (up to `2`), an elementary `ℤ[i]` descent (Hilbert, *Zahlbericht*, Satz 169:
`x⁴ ± y⁴ = z²` has only trivial solutions in `ℤ[i]`) shows `p/q` would have to be a Weierstrass
point, which is impossible for a cuboid.

| Result | Lean |
|---|---|
| `x⁴ ± y⁴ = z²`, `x⁴ − y⁴ = iz²` have only trivial solutions in `ℤ[i]` | `GaussianQuartic.quartic_one`, `GaussianQuartic.quartic_i`, `GaussianQuartic.quartic` |
| `pq(p⁴ − q⁴) = uV²` (`u` a unit) forces `p = 0`, `q = 0` or `p⁴ = q⁴` | `GaussianQuartic.genus_two` |
| `pq(p⁴ − q⁴) · 8(a+g)(f+b)(e+a)(g+e)(d+a)(g+d) = W²` | `cuboid_identity` |
| For a perfect cuboid, `(a+g)(f+b)(e+a)(g+e)(d+a)(g+d)` is never `2^k m²` | `IsPerfectCuboid.diag_prod_ne_two_pow_mul_sq` |
| No perfect cuboid has Beauville invariant `λ = 1`: the product of the six triple gcds `(a,b)(a,c)(b,c)(a,f)(b,e)(c,d)` is never `2^k m²` | `IsPerfectCuboid.gcd_prod_ne_two_pow_mul_sq` |

`BeauvilleCharacters.lean` rules out three more square classes. The same identities give the
square classes of `2ξ`, `ξ² − 1`, `ξ² + 1` (`ξ = p/q`), which twist the three `j = 1728` factors of
the curve `X(8)` the cuboid lies on (Stoll–Testa §4). When one of those twists is trivial, the
point lies on `y² = x³ − x` or `y² = x³ + x` over `ℚ(i)`, which have only torsion points. With
`μ₁, μ₂, μ₃` the odd squarefree parts of the gcd products of the two triples through `f`, `e`, `d`,
this says `μ₁, μ₂, μ₃` are pairwise distinct. The first is the global, fiber-free form of
Cipollini's "infinity class" (arXiv:2609.14526 §2).

| Result | Lean |
|---|---|
| `X⁴ + Y⁴ = uw²` (`u` a unit) forces `X = 0`, `Y = 0`, `w = 0` or `X⁴ = Y⁴` (`1 + 1 = i(1 − i)²`) | `GaussianQuartic.quartic_plus` |
| `pq(p² − q²) = uV²` (`u` a unit) forces `p = 0`, `q = 0` or `p⁴ = q⁴` | `GaussianQuartic.cn_gauss` |
| `μ₂ ≠ μ₃`: `(a,c)(b,e)(a,b)(c,d)` is never `2^k m²` | `IsPerfectCuboid.gcd_prod_ed_ne_two_pow_mul_sq` |
| `μ₁ ≠ μ₂`: `(a,f)(b,c)(a,c)(b,e)` is never `2^k m²` | `IsPerfectCuboid.gcd_prod_fe_ne_two_pow_mul_sq` |
| `μ₁ ≠ μ₃`: `(a,f)(b,c)(a,b)(c,d)` is never `2^k m²` | `IsPerfectCuboid.gcd_prod_fd_ne_two_pow_mul_sq` |

`OctahedralJ.lean` looks at the same point `ξ = (a+g)/(b − ic)` as a point of `X(4) = ℙ¹`, which
carries a Legendre curve `E_ξ` with `j(ξ) = 16(ξ⁸ + 14ξ⁴ + 1)³/(ξ⁴(ξ⁴ − 1)⁴)`. Since `j(u) − j(v)`
factors through the 24 octahedral Möbius maps, `j(ξ)` is real only on the hyperplanes `c = 0`,
`b = 0`, `a = 0`, `a = b`, `b = c`, `a = c`, which carry only degenerate cuboids.

| Result | Lean |
|---|---|
| `N(u)D(v) − N(v)D(u) = (u − v)·S(u + v, uv)`, `S` a product of 12 explicit factors | `octJ_identity`, `octS` |
| For a perfect cuboid, `j((a+g)/(b − ic))` is not real (so `E_ξ` is not defined over `ℚ`) | `IsPerfectCuboid.octJ_im_ne_zero` |

`CongruentNumber.lean` states the correspondence in the language of congruent numbers: `N` is
*congruent* if it is the area of a right triangle with rational sides.

| Result | Lean |
|---|---|
| For `N > 0`: `N` is congruent iff `E_N` has a rational point with `Y ≠ 0`, iff `E_N(ℚ)` has a point with `2P ≠ 0` | `isCongruent_iff`, `isCongruent_iff_exists_add_self_ne_zero` |
| `N` is congruent iff `E_N(ℚ)` has a point of infinite order (using `torsionTwo`) | `isCongruent_iff_exists_nonTors`, `IsCongruent.of_nonTors` |
| Being congruent depends only on the square class of `N` | `isCongruent_mul_sq_iff` |
| Fermat: `1` (and every `q²`) is not congruent, so every rational point of `E_1` (and `E_{q²}`) is `2`-torsion; `E_1(ℚ)` has no point of infinite order | `add_self_eq_zero_one`, `add_self_eq_zero_of_sq`, `not_nonTors_one` |
| A perfect cuboid makes `abcg/2` and its squarefree part `N` congruent, and `E_N` has a point outside `E_N[2]`, hence of infinite order | `IsPerfectCuboid.isCongruent`, `IsPerfectCuboid.exists_nonTors` |

`Genocchi.lean` proves Genocchi's theorems (1855) by Fermat's descent: a prime `p ≡ 3 (mod 8)` is
not congruent, and neither is `2p` for a prime `p ≡ 5 (mod 8)`. A primitive triangle of area
`p w²` gives `rs(r − s)(r + s) = p w²` with four pairwise coprime factors; `p` sits in one of them,
three placements die because `−1`, `2` or `−2` is not a square mod `p` (or mod `8`), and the
fourth halves to a smaller triangle. `CongruentCharacters.lean` turns every *body cuboid* (edge
`x`, face diagonals `u, v` through `x`, space diagonal `g`) into a congruent number through the
identity `(s − t)(g + v)(x + u) = y²(s + t)`, `s = g + u`, `t = x + v`. A perfect cuboid is a body
cuboid in three ways, which gives three congruent numbers over `ℚ` (the `j = 1728` classes of
`BeauvilleCharacters.lean`), and Genocchi excludes square classes of each.

| Result | Lean |
|---|---|
| Genocchi: a prime `p ≡ 3 (mod 8)` is not congruent; `2p` is not congruent for a prime `p ≡ 5 (mod 8)` | `FermatTriangle.not_isCongruent_prime_three_mod_eight`, `FermatTriangle.not_isCongruent_two_mul_prime_five_mod_eight` |
| A body cuboid makes `(x+u)(x+v)(g+u)(g+v)` congruent | `isCongruent_body` |
| A perfect cuboid makes `(a+d)(a+e)(g+d)(g+e)`, `(b+d)(b+f)(g+d)(g+f)`, `(c+e)(c+f)(g+e)(g+f)` congruent | `IsPerfectCuboid.isCongruent_ed`, `_fd`, `_fe` |
| None of these is `p m²` (`p ≡ 3 mod 8`) or `2p m²` (`p ≡ 5 mod 8`) | `IsPerfectCuboid.diag_prod_ed_ne_prime_mul_sq`, `…_ne_two_mul_prime_mul_sq` (and `fd`, `fe`) |
| If `a` is odd, `(a,c)(b,e)(a,b)(c,d)` is never `p m²` with `p ≡ 3 (mod 8)` | `IsPerfectCuboid.gcd_prod_ed_ne_prime_mul_sq` |
| The squarefree part `N` of `abcg/2` is neither such a `p` nor such a `2p` | `IsPerfectCuboid.squarefree_part_ne` |

The one hypothesis left in `not_rankOne_of_primitiveDivisorStep` is Ingram's primitive-divisor
theorem, which needs canonical heights; Mathlib does not have them yet. `KummerDescent.lean`
gives an alternative to it: `not_inRankOne_of_quarterFree` derives the same conclusion from the
purely Diophantine hypothesis `QuarterFree N` (no positive configuration has a point with `−N·x`
and `−2N·(x − N)` both rational squares), which is equivalent to a square condition on rational
perfect cuboids (`quarterFree_iff`); `KummerAddition.lean` records all Kummer relations the
pattern forces. Neither hypothesis is proved.

`Saunderson.lean` formalizes **Spohn's theorem** (1972): no Saunderson brick is a perfect
cuboid. Saunderson's brick `(u|4v² − w²|, v|4u² − w²|, 4uvw)` from `u² + v² = w²` has space
diagonal squared `w²(u⁴ + 18u²v² + v⁴)`, and Pocklington (1912) showed `x⁴ + 18x²y² + y⁴` is
never a nonzero square. The descent here handles every even `y` at once (the congruence-only
argument in some expositions misses `4 ∣ y`). `SqrtTwoJacobi.lean` is the symbol lemma in the
2-descent over `ℚ(√2)`: for `ℓ = c₀² − 2c₁²` prime, `(c₀/ℓ) = (2/c₀)` if `ℓ ≡ 7 (mod 8)` and
`(−2/c₀)` if `ℓ ≡ 1 (mod 8)`. `LeonardWilliams.lean` shows that the Leonard–Williams symbol
`(2u/v)` is the same for every positive representation `ℓ = u² − 2v²`: it is unchanged when
`u + v√2` is multiplied by `(1 + √2)²` and when it is replaced by `(1 + √2)²(u − v√2)`. For
`ℓ ≡ 15 (mod 16)` this sign decides the Cassels–Tate pairing on `Sel₂(E₁^{(ℓ)}/ℚ(√2))`
(theorem T1‴(a), proved on paper in the project notes: the pairing is the Frobenius of the prime
over `ℓ` in the 8-class field of `ℚ(√−2ℓ)`).

| Result | Lean |
|---|---|
| Pocklington: `x⁴ + 18x²y² + y⁴ = z²` forces `x = 0` or `y = 0` | `pocklington_quartic` |
| Spohn: no Saunderson brick is perfect | `not_isPerfectCuboid_saunderson`, `not_isPerfectCuboid_saunderson_int` |
| The six gcds of a primitive Saunderson brick multiply to `2mn(m⁴ − n⁴)`, the value of the degenerate cuboid `(u, v, 0)` | `saunderson_gcd`, `saunderson_gcd_prod_mn` |
| `ℓ = c₀² − 2c₁²` prime, `ℓ ≡ 7 (mod 8)`: `(c₀/ℓ) = (2/c₀)`, so `(c₀/ℓ) = 1 ↔ ℓ ≡ 15 (mod 16)` | `SqrtTwoJacobi.jacobiSym_c0_of_sq_sub_two_sq` |
| Same, `ℓ ≡ 1 (mod 8)`: `(c₀/ℓ) = (−2/c₀)` | `SqrtTwoJacobi.jacobiSym_c0_of_sq_sub_two_sq_one_mod_eight` |
| `u, v` odd: `(2(3u + 4v) / (2u + 3v)) = (2u/v)` (unit step of the Leonard–Williams symbol) | `LeonardWilliams.jacobiSym_LW_unit_step` |
| `u, v` odd, `2u > 3v`: `(2(3u − 4v) / (2u − 3v)) = (2u/v)` (conjugate step) | `LeonardWilliams.jacobiSym_LW_conj_step` |
| Iterated unit step `(1 + √2)^{2n}` | `LeonardWilliams.jacobiSym_LW_unit_step_iterate` |
| Both steps keep `u² − 2v²` | `LeonardWilliams.norm_LW_unit_step`, `norm_LW_conj_step` |

`DerivedCuboid.lean` formalizes the **Chein–Lagrange theorem** (1977/1979): the derived brick
`(bc, ca, ab)` of a Saunderson brick `(a, b, c)` is an Euler brick but never perfect. Its space
diagonal squared is `u²v²(t⁴ − 6s²t² + 25s⁴)` with `s = w²`, `t = 4uv`. No new descent is
needed: the curve of that quartic maps to Pocklington's curve by a 4-isogeny, and in coordinates
`x = r(5s² − t²)`, `y = 2st(t² + 5s²)` solves `x⁴ + 18x²y² + y⁴ = z²` whenever
`t⁴ − 6s²t² + 25s⁴ = r²`. The middle curve of the isogeny carries Collins' theorem (1858), which
Leech used for the same result; it falls out the same way with `x = mp`, `y = nq`.

| Result | Lean |
|---|---|
| The derived brick `(bc, ca, ab)` of an Euler brick is an Euler brick | `IsEulerBrick.derived` |
| `t⁴ − 6s²t² + 25s⁴ = r²` forces `st = 0` | `quartic_six_twentyfive` |
| Collins: `m² + n² = p²` and `m² + 5n² = q²` force `mn = 0` | `collins` |
| Chein–Lagrange: the derived brick of a Saunderson brick is never perfect | `not_isPerfectCuboid_derived_saunderson`, `not_isPerfectCuboid_derived_saunderson_int` |

`EulerSecondFamily.lean` covers Euler's family `a = 2mn(3m² − n²)(3n² − m²)`, `b = 8mn(m⁴ − n⁴)`,
`c = (m² − n²)(m² − 4mn + n²)(m² + 4mn + n²)` (as listed in Knill's 2009 notes). Its space
diagonal squared is `(m² + n²)²(m⁸ + 68m⁶n² − 122m⁴n⁴ + 68m²n⁶ + n⁸)`, and the octic is
Pocklington's quartic at `(x, y) = (m² − n², 2mn)`. Indeed the family is Saunderson's brick for
Euclid's triple, up to signs and edge order, so it is never perfect.

| Result | Lean |
|---|---|
| The family is Saunderson's for `(m² − n², 2mn, m² + n²)`; `(2, 1)` gives `(44, 240, 117)` | `euler_eq_saunderson`, `euler_two_one` |
| For `mn(m² − n²) ≠ 0` it is an Euler brick | `euler_isEulerBrick` |
| The octic is a square only if `mn(m² − n²) = 0` | `euler_octic_ne_sq` |
| No brick of the family is perfect | `not_isPerfectCuboid_euler` |

Round 10 looks at the prime factorizations of the seven lengths. An edge `x` is a leg of three
right triangles, so `x² = (d − b)(d + b) = (e − c)(e + c) = (g − f)(g + f)`.
`DivisorForm.lean` turns this into one equation in three rationals `rᵢ = (hypotenuse + leg)/x`.
`EdgePrimePower.lean` proves Korec's 1984 theorem that no edge is a prime power. It covers
every edge and `p = 2`, and does not assume primitivity. `DiagonalPrimePower.lean` proves the
same for the face diagonals; we found no earlier statement of that. Its proof rests on two
inequalities, `(g − x)² > 2(g + x)` and `p^m ∣ x², p ∤ 2y ⇒ p^m < x + 2y`.

| Result | Lean |
|---|---|
| A perfect cuboid exists iff `r₁² + r₁⁻² + r₂² + r₂⁻² − r₃² − r₃⁻² = 2` has a rational solution with all `rᵢ > 1` | `exists_isPerfectCuboid_iff_divisor_form` |
| No edge is a prime power `p^k` | `IsPerfectCuboid.edge_ne_prime_pow`, `edge_ne_prime_pow_b`, `edge_ne_prime_pow_c` |
| Divisor inequality `t₁²t₂² < t₃²(t₁² + t₂²)` | `inv_sq_add_inv_sq_gt` |
| No face diagonal is a prime power `p^k` | `IsPerfectCuboid.face_diagonal_ne_prime_pow` |

`TwoPrimeCongruent.lean` proves seven classes of numbers `pq` and `2pq` non-congruent. They are
exactly the two-prime classes in which every member has 2-Selmer rank 0. The descents are by
Genocchi (1855) and Lagrange (1974/75); for the class `2pq` with `p ≡ q ≡ 3 (mod 8)` we found no
source. Each case of the descent fails mod 8, or because `−1`, `2` or `−2` is not a square
mod `p`, or because `p` is not a square mod `q`. Consequently the three congruent numbers
`(a + d)(a + e)(g + d)(g + e)`, … of a perfect cuboid avoid all seven classes.

| Result | Lean |
|---|---|
| `pq` is not congruent: `p ≡ q ≡ 3`; `p ≡ 1, q ≡ 3`; `p ≡ 5, q ≡ 7` (mod 8), the last two with `(p/q) = −1` | `not_isCongruent_pq_three_three`, `not_isCongruent_pq_one_three`, `not_isCongruent_pq_five_seven` |
| `2pq` is not congruent: `p ≡ q ≡ 5`; `p ≡ q ≡ 3`; `p ≡ 1, q ≡ 5`; `p ≡ 3, q ≡ 7` (mod 8), the last two with `(p/q) = −1` | `not_isCongruent_two_pq_five_five`, `…_three_three`, `…_one_five`, `…_three_seven` |
| The diagonal products and `sf(abcg/2)` avoid all seven classes | `IsPerfectCuboid.diag_prod_{ed,fd,fe}_twoPrimeAvoid`, `squarefree_part_twoPrimeAvoid` |

Three published parametric families of almost-perfect boxes are never perfect:

| Family | Why it is never perfect | Lean |
|---|---|---|
| Colman's degree-14 Euler bricks (Fibonacci Quart. 1988, (4.8)); we found no earlier proof | `g² = (m² + n²)²·O·P` with `O` Euler's octic and `P = O² + (16mnR)²`. `O` and `P` share only the prime 2, so `O` must be a square, which Pocklington rules out | `not_isPerfectCuboid_colman` |
| Bromhead–Colman edge cuboids (Colman 1988, (4.12)) | `c = 2E·(4pq(p⁴ − q⁴))²`, and `2E ≡ 2 (mod 4)` or `≡ 32 (mod 64)` | `not_isPerfectCuboid_colmanEdge` |
| Leech's edge cuboids (1977), with no Pythagorean hypothesis needed | `T(ζ⁴ + ξ²η²)² = (ζ⁴ − ξ²η²)⁴ − (2ξηζ²)⁴`, and Fermat: `x⁴ − y⁴ ≠ z²` | `not_isPerfectCuboid_leechEdge`, `quartic_neg_six` |

Round 11 pushes the prime-factor line further. `EdgeTwoPrimes.lean` proves that no edge of a
perfect cuboid is `p^k q^l`, so **every edge has at least three distinct prime factors**. Korec
(1984) had the two-prime case only under side conditions. The proof needs no primitivity: at each
of the two primes the smallest exponent among the three legs must occur twice, and together with
the divisor inequality this leaves eight shapes, all reducing to one equation
`(XVY − U)² + (UV − XY)² = (UVY − X)²` in prime powers. That equation is ruled out by reducing it
modulo `X` and `U` and then using it as an inequality.

| Result | Lean |
|---|---|
| No edge is `p^k q^l` (`p ≠ q` prime) | `IsPerfectCuboid.edge_ne_two_prime_pow` (`_b`, `_c`) |
| Every edge has `≥ 3` prime factors; `≥ 2` odd ones; an odd edge has `≥ 3` odd ones | `IsPerfectCuboid.three_le_primeFactors_card`, `two_le_oddPrimeFactors_card`, `three_le_oddPrimeFactors_card_of_odd` |
| The residual equation has no solution in prime powers | `res_no_solution` |

The same divisor method applies to boxes that are almost perfect.

| Result | Lean |
|---|---|
| `(x^{2m} − 1)(x^{2n} − 1)` is never a square for `m ≠ n` (known: Hajdu–Szalay 2000, Cohn 2002); here an elementary proof via the Pell equation and lifting the exponent | `PellLeg.pow_sub_one_mul_pow_sub_one_not_square` (`PellLeg.lean`) |
| Face cuboid (all integral except one face diagonal): neither edge next to the irrational diagonal is a prime power; `(153, 672, 104)` shows two primes can occur | `IsFaceCuboid.edge_ne_prime_pow_a`, `_b` (`FaceCuboid.lean`) |
| Edge cuboid (all integral except one edge `√N`): `N` is not a prime power | `IsEdgeCuboid.N_ne_prime_pow` (`EdgeCuboid.lean`) |
| Edge cuboid: `2⁸·3⁴·5⁴·7·11·13 ∣ a·b·N·d·e·f·g`, attained, and no prime `≥ 17` is forced; 2-adic shape | `IsEdgeCuboid.leech_dvd`, `edge_two_adic` |
| Euler brick with an edge `p^k`: reduced to `(PQ − 1)² + P(Q − 1)² = F²` with `P, Q` even powers of `p`, which forces `k ≥ 4` (`k ≥ 5` for `p = 2`) | `exists_isEulerBrick_prime_pow_iff`, `IsEulerBrick.prime_pow_exponent_ge` (`BrickPrimePower.lean`) |
| If no odd prime divides all edges, `g − x` is not `p^i` or `2p^i` dividing the opposite face diagonal; so a face diagonal `2^s p^k` cannot have `g − a = 2p^i` | `DiagonalTwoPrimes.g_sub_ne_prime_pow`, `face_diagonal_ne_two_pow_mul_prime_pow_of_F1` |

#### Vendored: the division-polynomial formula — `TauCeti/`

Mathlib's division polynomials are not yet linked to the group law (its pull request #13782 was
closed unmerged). The [Tau Ceti project](https://github.com/TauCetiProject/TauCeti) proves the
link, `WeierstrassCurve.zsmul_point_eq_smulEval`: `n • (x, y) = (φₙ : ωₙ : ψₙ)` in Jacobian
coordinates. `TauCeti/` holds the files it needs, copied unchanged from Tau Ceti commit
`6ff9009` (Apache-2.0, `TauCeti/LICENSE`; ported there from the AINTLIB work of J. Xu and
D. K. Angdinata) except for one added import each. They need about 200 lines of newer Mathlib
(J. Xu's `IsEllipticNet.normEDS` and `normEDS_mul_complEDS`), backported verbatim in
`TauCeti/MathlibCompat/EllipticDivisibilitySequence.lean`; delete that file when the Mathlib pin
moves past them.

## Update Mathlib

```fish
lake update
```

The `update.yml` workflow also opens a pull request when a new Mathlib release is out.
