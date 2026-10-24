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

## Update Mathlib

```fish
lake update
```

The `update.yml` workflow also opens a pull request when a new Mathlib release is out.
