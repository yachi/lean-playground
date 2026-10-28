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
| `FiberList.lean` | The 86 fibers above in one statement: `provedFibers` lists the pairs `(m, n)`; no perfect cuboid has two edges `X, Z` with `(m² − n²) X = 2mn Z` for `(m, n)` in the list, so every perfect cuboid lies on a fiber outside it. The method only reaches fibers where one pair has rank 0 and `Ш[2] = 0`: of the 331 fibers with `m ≤ 40`, 70 for `(V, W)`, 88 for `(U, W)`, 98 for `(U, V)`, 179 for at least one | `provedFibers`, `IsPerfectCuboid.not_onFiber_of_mem`, `IsPerfectCuboid.exists_fiber_not_mem` |
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

`CongruentNumber.lean` states the correspondence in the language of congruent numbers: `N` is
*congruent* if it is the area of a right triangle with rational sides.

| Result | Lean |
|---|---|
| For `N > 0`: `N` is congruent iff `E_N` has a rational point with `Y ≠ 0`, iff `E_N(ℚ)` has a point with `2P ≠ 0` | `isCongruent_iff`, `isCongruent_iff_exists_add_self_ne_zero` |
| `N` is congruent iff `E_N(ℚ)` has a point of infinite order (using `torsionTwo`) | `isCongruent_iff_exists_nonTors`, `IsCongruent.of_nonTors` |
| Being congruent depends only on the square class of `N` | `isCongruent_mul_sq_iff` |
| Fermat: `1` (and every `q²`) is not congruent, so every rational point of `E_1` (and `E_{q²}`) is `2`-torsion; `E_1(ℚ)` has no point of infinite order | `add_self_eq_zero_one`, `add_self_eq_zero_of_sq`, `not_nonTors_one` |
| A perfect cuboid makes `abcg/2` and its squarefree part `N` congruent, and `E_N` has a point outside `E_N[2]`, hence of infinite order | `IsPerfectCuboid.isCongruent`, `IsPerfectCuboid.exists_nonTors` |

The one hypothesis left in `not_rankOne_of_primitiveDivisorStep` is Ingram's primitive-divisor
theorem, which needs canonical heights; Mathlib does not have them yet.

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
