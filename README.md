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

### What a complex derivative means — `LeanPlayground/ComplexDerivative/`

Claims from Zundamon's Theorem, [*What Does a Complex Derivative Actually
Mean?*](https://youtu.be/2-95hN4fgmE) (YouTube, 2026-10-26): near `a`, the derivative acts as the
multiplier in `Δw ≈ f'(a) Δz`, and multiplying by `r e^{iθ}` scales the plane by `r` and rotates
it by `θ`. So a complex derivative is a local rotation and scaling.

| Lean | Claim |
|---|---|
| `hasDerivAt_iff_sub_mul_isLittleO` | `f(a+h) − f(a) = f'(a) h + o(h)` (and the real version) |
| `polar_form`, `exp_mul_I_eq`, `polar_mul` | Euler's formula, `α = ‖α‖ e^{i arg α}`, lengths multiply and angles add |
| `mul_eq_smul_rotation`, `isConformalMap_mul`, `dist_mul_mul` | Multiplying by `α` is a rotation by `arg α` then a scaling by `‖α‖`, keeps angles, and scales distances by `‖α‖` |
| `sub_rotation_isLittleO_of_hasDerivAt`, `conformalAt_of_hasDerivAt` | Near `a`, `f` is that rotation and scaling up to `o(h)`; conformal when `f'(a) ≠ 0` |
| `exp_deriv_at_log_add`, `exp_local_scale_rotate`, `exp_deriv_ln_two` | The worked example: `e^z` at `ln r + iθ` scales by `r` and rotates by `θ`; at `ln 2 + iπ/2` the derivative is `2i` |

The transcript does not show the example's formulas on screen, so the file reads it as `e^z` at a
point built from `ln 2` and proves the general case for every `r > 0` and `θ`.

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
| `DescentCheck.lean`, `Descent.lean` | The descent of `FiberTwoOne.lean` for any pair `(p, q)` with `p` even, `gcd(p, q) = 1` and `q² − p² = a²`. After a sign argument, a case gives a smaller solution exactly when it is the image of a torsion point; the two possible torsion classes give three families of formulas (one linear, two quadratic representations of the translate by a `4`-torsion point), proved once for all `(p, q)` and recognized by `torsionOK`. Every other case is ruled out by a congruence, checked by the kernel (`decide +kernel`, proved sound by `check_sound`): either by trying every modulus (`fiberCheck`), or, much faster, by replaying a certificate that names the one torsion family or modulus for each case (`fiberCheckCert`). Certificates are generated by `scripts/cuboid_cert.py`, which mirrors the case list and the checks in Python. This works when the curve has rank 0 and `Ш[2] = 0` | `Descent.not_isSol`, `Descent.not_isSquare_sq_add_sq_and_sq_add_sq`, `Descent.torsionOK_sound`, `Descent.check_sound`, `Descent.coveredOn_of_fiberCheckCert`, `Descent.covered_of_fiberCheck` |
| `FiberDescentCert.lean`, `FiberDescent.lean` | The fibers `(3, 2)`, `(4, 1)`, `(4, 3)`, `(6, 1)`, `(8, 1)`, `(7, 6)` and `(7, 2)`, unconditionally: no perfect cuboid has two edges in ratio `5 : 12`, `8 : 15`, `7 : 24`, `12 : 35`, `16 : 63`, `13 : 84` or `28 : 45` (pairs `(12, 13)`, `(8, 17)`, `(24, 25)`, `(12, 37)`, `(16, 65)`, `(84, 85)` and `(28, 53)`, on the rank-0 curves `y² = x(x + p²)(x + q²)`). The generic descent also re-proves `3 : 4`. The certificates (`FiberDescentCert.lean`) are generated by `python3 scripts/cuboid_cert.py --certs-only 2,1 3,2 4,1 4,3 6,1 8,1 7,6 7,2 -o LeanPlayground/PerfectCuboid/FiberDescentCert.lean` | `not_isPerfectCuboid_five_twelve`, `not_isPerfectCuboid_eight_fifteen`, `not_isPerfectCuboid_seven_twentyfour`, `not_isPerfectCuboid_twelve_thirtyfive`, `not_isPerfectCuboid_sixteen_sixtythree`, `not_isPerfectCuboid_twentyeight_fortyfive`, `not_isPerfectCuboid_thirteen_eightyfour`, `not_isSquare_sq_add_144_and_sq_add_169`, `not_isSquare_sq_add_64_and_sq_add_289`, `not_isSquare_sq_add_576_and_sq_add_625`, `not_isSquare_sq_add_144_and_sq_add_1369`, `not_isSquare_sq_add_256_and_sq_add_4225`, `not_isSquare_sq_add_7056_and_sq_add_7225`, `not_isSquare_sq_add_784_and_sq_add_2809`, `Descent.not_isSol_four_five` |
| `Fibers/F_<p>_<q>.lean` | 27 more fibers, one generated module each (so that each build stays within a few GB), unconditionally: no perfect cuboid has two edges in ratio `36 : 77`, `65 : 72`, `44 : 117`, `24 : 143`, `17 : 144`, `85 : 132`, `119 : 120`, `52 : 165`, `60 : 221`, `68 : 285`, `136 : 273`, `152 : 345`, `135 : 352`, `228 : 325`, `87 : 416`, `203 : 396`, `132 : 475`, `155 : 468`, `100 : 621`, `429 : 460`, `52 : 675`, `156 : 667`, `37 : 684`, `333 : 644`, `56 : 783`, `273 : 736` or `432 : 665`. These are all the remaining fibers with `q ≤ 793` whose curve has rank 0 and `Ш[2] = 0` (PARI/GP), except `(96, 265)`, `(336, 505)`, `(396, 565)`, `(336, 625)`, `(400, 689)` and `(468, 757)`, where a few cases are neither torsion translates of the three families nor ruled out by a modulus, and `(748, 773)`, whose build takes over 10 minutes. Each file is `python3 scripts/cuboid_cert.py m,n -o …` | `not_isPerfectCuboid_thirtysix_seventyseven`, …, `not_isPerfectCuboid_432_665`, and `not_isSquare_sq_add_<p²>_and_sq_add_<q²>`, `Descent.not_isSol_<p>_<q>` for each pair (numbers below 100 are spelled as words, e.g. `Descent.not_isSol_seventytwo_ninetyseven`, `not_isPerfectCuboid_sixtyfive_seventytwo`) |

Theorem 4.5 is formalized *conditionally*. Its hypotheses (`E3Trivial m n`, `EuVLiftTrivial m n`)
say that an elliptic curve has rank 0 and known torsion. Peschmann checks them for 1,072 fibers
with PARI and, via modularity and Kolyvagin's theorem, with modular symbols; Mathlib cannot do
that, so they stay as explicit hypotheses rather than `sorry`s.

## Update Mathlib

```fish
lake update
```

The `update.yml` workflow also opens a pull request when a new Mathlib release is out.
