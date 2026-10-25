module

public import LeanPlayground.PerfectCuboid.Descent

/-!
# No perfect cuboid has two edges in ratio `5 : 12` or `8 : 15`

These are the fibers `(m, n) = (3, 2)` and `(4, 1)` of Peschmann's master-tuple parametrization
(arXiv:2604.28072), handled by the generic descent of `LeanPlayground.PerfectCuboid.Descent`.

* `5 : 12`. With `X = 5k`, `Z = 12k` the face diagonal `√(Y² + 144k²)` and the space diagonal
  `√(Y² + 169k²)` would be integers. We use the pair `(p, q) = (12, 13)`, `a = 5`; the curve
  `y² = x (x + 144)(x + 169)` has conductor `195` and rank `0`.
* `8 : 15`. With `X = 8k`, `Z = 15k` the face diagonal `√(Y² + 64k²)` and the space diagonal
  `√(Y² + 289k²)` would be integers. We use `(p, q) = (8, 17)`, `a = 15`; the curve
  `y² = x (x + 64)(x + 289)` has conductor `510` and rank `0`.

The same machinery also reproves the `3 : 4` fiber of `LeanPlayground.PerfectCuboid.FiberTwoOne`
with `(p, q) = (4, 5)` (`not_isSol_four_five`).

In each case the kernel runs `fiberCheck` (`decide +kernel`) over all a few hundred descent
cases; every case is either one of the two shapes that give a smaller solution or is impossible
modulo one of the numbers in `mods`.

The rank computations (PARI/GP `ellrank`) are only the reason to expect the descent to work; the
proofs do not depend on them. Not every fiber can be done this way: for `48 : 55` (`(m, n) =
(8, 3)`) all three elliptic curves `y² = x (x + u²)(x + v²)` with `{u, v} ⊂ {48, 55, 73}` have
rank `1`, so no descent on one of them can succeed.

## Main results

* `not_isPerfectCuboid_five_twelve` — no perfect cuboid has `12 X = 5 Z`.
* `not_isPerfectCuboid_eight_fifteen` — no perfect cuboid has `15 X = 8 Z`.
* `not_isSquare_sq_add_144_and_sq_add_169`, `not_isSquare_sq_add_64_and_sq_add_289` — the
  underlying statements over `ℚ`.
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

/-- The moduli tried by the residue check, in order. -/
def mods : List (ℕ × ℕ) :=
  [(8, 2), (16, 2), (3, 3), (5, 5), (9, 3), (13, 13), (17, 17), (7, 7), (25, 5), (32, 2)]

theorem fiberCheck_four_five : fiberCheck 4 5 3 mods = true := by decide +kernel

theorem fiberCheck_twelve_thirteen : fiberCheck 12 13 5 mods = true := by decide +kernel

theorem fiberCheck_eight_seventeen : fiberCheck 8 17 15 mods = true := by decide +kernel

/-- The `3 : 4` fiber again, now through the generic descent. -/
theorem not_isSol_four_five (M e r s : ℤ) : ¬ IsSol 4 5 M e r s := by
  simpa using not_isSol (p := 4) (q := 5) (a := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) fiberCheck_four_five M e r s

theorem not_isSol_twelve_thirteen (M e r s : ℤ) : ¬ IsSol 12 13 M e r s := by
  simpa using not_isSol (p := 12) (q := 13) (a := 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) fiberCheck_twelve_thirteen M e r s

theorem not_isSol_eight_seventeen (M e r s : ℤ) : ¬ IsSol 8 17 M e r s := by
  simpa using not_isSol (p := 8) (q := 17) (a := 15) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (by decide) fiberCheck_eight_seventeen M e r s

end Descent

/-- For rational `t ≠ 0`, `t² + 144` and `t² + 169` are not both squares. -/
theorem not_isSquare_sq_add_144_and_sq_add_169 {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 144) ∧ IsSquare (t ^ 2 + 169)) := by
  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := 12) (q := 13) (a := 5) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)
    Descent.fiberCheck_twelve_thirteen ht
  norm_num at this
  exact fun h ↦ this h.1 h.2

/-- For rational `t ≠ 0`, `t² + 64` and `t² + 289` are not both squares. -/
theorem not_isSquare_sq_add_64_and_sq_add_289 {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 64) ∧ IsSquare (t ^ 2 + 289)) := by
  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := 8) (q := 17) (a := 15) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)
    Descent.fiberCheck_eight_seventeen ht
  norm_num at this
  exact fun h ↦ this h.1 h.2

/-- **No perfect cuboid has two edges in ratio `5 : 12`.** This is the fiber `(m, n) = (3, 2)`:
with `X = 5k`, `Z = 12k`, the face diagonal `√(Y² + 144k²)` and the space diagonal
`√(Y² + 169k²)` cannot both be integers. -/
theorem not_isPerfectCuboid_five_twelve {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    12 * X ≠ 5 * Z := by
  intro hXZ
  obtain ⟨k, rfl⟩ : 5 ∣ X := by omega
  obtain rfl : Z = 12 * k := by omega
  obtain ⟨r, hr⟩ := h.sq_bc
  obtain ⟨s, hs⟩ := h.sq_abc
  have hY := h.pos_b
  have hk : 0 < k := by have := h.pos_a; omega
  apply Descent.not_isSol_twelve_thirteen (Y : ℤ) k r s
  refine ⟨by exact_mod_cast hY.ne', by exact_mod_cast hk.ne', ?_, ?_⟩
  · have : ((Y ^ 2 + (12 * k) ^ 2 : ℕ) : ℤ) = ((r * r : ℕ) : ℤ) := by rw [hr]
    push_cast at this
    linear_combination this
  · have : (((5 * k) ^ 2 + Y ^ 2 + (12 * k) ^ 2 : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    linear_combination this

/-- **No perfect cuboid has two edges in ratio `8 : 15`.** This is the fiber `(m, n) = (4, 1)`:
with `X = 8k`, `Z = 15k`, the face diagonal `√(Y² + 64k²)` and the space diagonal
`√(Y² + 289k²)` cannot both be integers. -/
theorem not_isPerfectCuboid_eight_fifteen {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    15 * X ≠ 8 * Z := by
  intro hXZ
  obtain ⟨k, rfl⟩ : 8 ∣ X := by omega
  obtain rfl : Z = 15 * k := by omega
  obtain ⟨r, hr⟩ := h.sq_ab
  obtain ⟨s, hs⟩ := h.sq_abc
  have hY := h.pos_b
  have hk : 0 < k := by have := h.pos_a; omega
  apply Descent.not_isSol_eight_seventeen (Y : ℤ) k r s
  refine ⟨by exact_mod_cast hY.ne', by exact_mod_cast hk.ne', ?_, ?_⟩
  · have : (((8 * k) ^ 2 + Y ^ 2 : ℕ) : ℤ) = ((r * r : ℕ) : ℤ) := by rw [hr]
    push_cast at this
    linear_combination this
  · have : (((8 * k) ^ 2 + Y ^ 2 + (15 * k) ^ 2 : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    linear_combination this

end PerfectCuboid
