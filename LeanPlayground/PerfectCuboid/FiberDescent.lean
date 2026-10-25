module

public import LeanPlayground.PerfectCuboid.Descent

/-!
# No perfect cuboid has two edges in ratio `5 : 12`, `8 : 15`, …, `16 : 63` or `13 : 84`

These are fibers `(m, n)` of Peschmann's master-tuple parametrization (arXiv:2604.28072),
handled by the generic descent of `LeanPlayground.PerfectCuboid.Descent`.

* `5 : 12`. With `X = 5k`, `Z = 12k` the face diagonal `√(Y² + 144k²)` and the space diagonal
  `√(Y² + 169k²)` would be integers. We use the pair `(p, q) = (12, 13)`, `a = 5`; the curve
  `y² = x (x + 144)(x + 169)` has conductor `195` and rank `0`.
* `8 : 15`. With `X = 8k`, `Z = 15k` the face diagonal `√(Y² + 64k²)` and the space diagonal
  `√(Y² + 289k²)` would be integers. We use `(p, q) = (8, 17)`, `a = 15`; the curve
  `y² = x (x + 64)(x + 289)` has conductor `510` and rank `0`.
* `7 : 24`, the fiber `(m, n) = (4, 3)`. With `X = 7k`, `Z = 24k` the face diagonal
  `√(Y² + 576k²)` and the space diagonal `√(Y² + 625k²)` would be integers. We use
  `(p, q) = (24, 25)`, `a = 7`; the curve `y² = x (x + 576)(x + 625)` has conductor `210` and
  rank `0`. Here `q = 5²` and `q − p = 1²`, and the cases `λ = 1` and `λ = pq` are torsion
  translates that only exist because of this.
* `12 : 35`, the fiber `(m, n) = (6, 1)`. With `X = 12k`, `Z = 35k` the face diagonal
  `√(Y² + 144k²)` and the space diagonal `√(Y² + 1369k²)` would be integers. We use
  `(p, q) = (12, 37)`, `a = 35`; the curve `y² = x (x + 144)(x + 1369)` has conductor `3885`
  and rank `0`. The modulus `37` is needed.
* `16 : 63`, the fiber `(m, n) = (8, 1)`. With `X = 16k`, `Z = 63k` the face diagonal
  `√(Y² + 256k²)` and the space diagonal `√(Y² + 4225k²)` would be integers. We use
  `(p, q) = (16, 65)`, `a = 63`; the curve `y² = x (x + 256)(x + 4225)` has rank `0` and
  `Ш[2] = 0`. Here `p = 4²` and `q − p = 7²`, so the case `λ = 1`, `c₃ = c₄ = 1`, `σ = 49` is a
  `4`-torsion translate; it needs family QD with the divisor `F = 49`.
* `13 : 84`, the fiber `(m, n) = (7, 6)`. With `X = 13k`, `Z = 84k` the face diagonal
  `√(Y² + 7056k²)` and the space diagonal `√(Y² + 7225k²)` would be integers. We use
  `(p, q) = (84, 85)`, `a = 13`; the curve `y² = x (x + 7056)(x + 7225)` has rank `0` and
  `Ш[2] = 0`. The `64` surviving cases with `λ = 85` are all handled by family L.

The same machinery also reproves the `3 : 4` fiber of `LeanPlayground.PerfectCuboid.FiberTwoOne`
with `(p, q) = (4, 5)` (`not_isSol_four_five`).

In each case the kernel runs `fiberCheck` (`decide +kernel`) over all a few hundred descent
cases (a few thousand for `16 : 63` and `13 : 84`); every case is either a torsion translate that
gives a smaller solution or is impossible modulo one of the numbers in `mods`.

The rank computations (PARI/GP `ellrank`) are only the reason to expect the descent to work; the
proofs do not depend on them. Not every fiber can be done this way: for `48 : 55` (`(m, n) =
(8, 3)`) all three elliptic curves `y² = x (x + u²)(x + v²)` with `{u, v} ⊂ {48, 55, 73}` have
rank `1`, so no descent on one of them can succeed.

## Main results

* `not_isPerfectCuboid_five_twelve` — no perfect cuboid has `12 X = 5 Z`.
* `not_isPerfectCuboid_eight_fifteen` — no perfect cuboid has `15 X = 8 Z`.
* `not_isPerfectCuboid_seven_twentyfour` — no perfect cuboid has `24 X = 7 Z`.
* `not_isPerfectCuboid_twelve_thirtyfive` — no perfect cuboid has `35 X = 12 Z`.
* `not_isPerfectCuboid_sixteen_sixtythree` — no perfect cuboid has `63 X = 16 Z`.
* `not_isPerfectCuboid_thirteen_eightyfour` — no perfect cuboid has `84 X = 13 Z`.
* `not_isSquare_sq_add_144_and_sq_add_169`, `not_isSquare_sq_add_64_and_sq_add_289`,
  `not_isSquare_sq_add_576_and_sq_add_625`, `not_isSquare_sq_add_144_and_sq_add_1369`,
  `not_isSquare_sq_add_256_and_sq_add_4225`, `not_isSquare_sq_add_7056_and_sq_add_7225` — the
  underlying statements over `ℚ`.
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

/-- The moduli tried by the residue check, in order. -/
def mods : List (ℕ × ℕ) :=
  [(8, 2), (16, 2), (3, 3), (5, 5), (9, 3), (13, 13), (17, 17), (7, 7), (25, 5), (32, 2),
    (37, 37)]

theorem fiberCheck_four_five : fiberCheck 4 5 3 mods = true := by decide +kernel

theorem fiberCheck_twelve_thirteen : fiberCheck 12 13 5 mods = true := by decide +kernel

theorem fiberCheck_eight_seventeen : fiberCheck 8 17 15 mods = true := by decide +kernel

theorem fiberCheck_twentyfour_twentyfive : fiberCheck 24 25 7 mods = true := by decide +kernel

theorem fiberCheck_twelve_thirtyseven : fiberCheck 12 37 35 mods = true := by decide +kernel

/-- The `16 : 63` fiber has a few thousand cases; the kernel checks them in eight ranges of `λ`,
so that each run stays small. -/
theorem fiberCheckOn_sixteen_sixtyfive_1 : fiberCheckOn 16 65 63 mods 0 20 = true := by
  decide +kernel

theorem fiberCheckOn_sixteen_sixtyfive_2 : fiberCheckOn 16 65 63 mods 20 65 = true := by
  decide +kernel

theorem fiberCheckOn_sixteen_sixtyfive_3 : fiberCheckOn 16 65 63 mods 65 80 = true := by
  decide +kernel

theorem fiberCheckOn_sixteen_sixtyfive_4 : fiberCheckOn 16 65 63 mods 80 130 = true := by
  decide +kernel

theorem fiberCheckOn_sixteen_sixtyfive_5 : fiberCheckOn 16 65 63 mods 130 208 = true := by
  decide +kernel

theorem fiberCheckOn_sixteen_sixtyfive_6 : fiberCheckOn 16 65 63 mods 208 520 = true := by
  decide +kernel

theorem fiberCheckOn_sixteen_sixtyfive_7 : fiberCheckOn 16 65 63 mods 520 1040 = true := by
  decide +kernel

theorem fiberCheckOn_sixteen_sixtyfive_8 : fiberCheckOn 16 65 63 mods 1040 1041 = true := by
  decide +kernel

theorem fiberCheck_sixteen_sixtyfive : fiberCheck 16 65 63 mods = true :=
  fiberCheck_of_on (by decide) <|
    fiberCheckOn_trans fiberCheckOn_sixteen_sixtyfive_1 <|
    fiberCheckOn_trans fiberCheckOn_sixteen_sixtyfive_2 <|
    fiberCheckOn_trans fiberCheckOn_sixteen_sixtyfive_3 <|
    fiberCheckOn_trans fiberCheckOn_sixteen_sixtyfive_4 <|
    fiberCheckOn_trans fiberCheckOn_sixteen_sixtyfive_5 <|
    fiberCheckOn_trans fiberCheckOn_sixteen_sixtyfive_6 <|
    fiberCheckOn_trans fiberCheckOn_sixteen_sixtyfive_7 <|
    fiberCheckOn_sixteen_sixtyfive_8

/-- The `13 : 84` fiber has a few thousand cases; the kernel checks them in twelve ranges of `λ`,
so that each run stays small. -/
theorem fiberCheckOn_eightyfour_eightyfive_1 : fiberCheckOn 84 85 13 mods 0 17 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_2 : fiberCheckOn 84 85 13 mods 17 60 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_3 : fiberCheckOn 84 85 13 mods 60 85 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_4 : fiberCheckOn 84 85 13 mods 85 102 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_5 : fiberCheckOn 84 85 13 mods 102 204 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_6 : fiberCheckOn 84 85 13 mods 204 340 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_7 : fiberCheckOn 84 85 13 mods 340 476 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_8 : fiberCheckOn 84 85 13 mods 476 595 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_9 : fiberCheckOn 84 85 13 mods 595 1020 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_10 : fiberCheckOn 84 85 13 mods 1020 1785 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_11 : fiberCheckOn 84 85 13 mods 1785 3570 = true := by
  decide +kernel

theorem fiberCheckOn_eightyfour_eightyfive_12 : fiberCheckOn 84 85 13 mods 3570 7141 = true := by
  decide +kernel

theorem fiberCheck_eightyfour_eightyfive : fiberCheck 84 85 13 mods = true :=
  fiberCheck_of_on (by decide) <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_1 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_2 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_3 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_4 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_5 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_6 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_7 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_8 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_9 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_10 <|
    fiberCheckOn_trans fiberCheckOn_eightyfour_eightyfive_11 <|
    fiberCheckOn_eightyfour_eightyfive_12

/-- The `3 : 4` fiber again, now through the generic descent. -/
theorem not_isSol_four_five (M e r s : ℤ) : ¬ IsSol 4 5 M e r s := by
  simpa using not_isSol (p := 4) (q := 5) (a := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) fiberCheck_four_five M e r s

theorem not_isSol_twelve_thirteen (M e r s : ℤ) : ¬ IsSol 12 13 M e r s := by
  simpa using not_isSol (p := 12) (q := 13) (a := 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) fiberCheck_twelve_thirteen M e r s

theorem not_isSol_eight_seventeen (M e r s : ℤ) : ¬ IsSol 8 17 M e r s := by
  simpa using not_isSol (p := 8) (q := 17) (a := 15) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) fiberCheck_eight_seventeen M e r s

theorem not_isSol_twentyfour_twentyfive (M e r s : ℤ) : ¬ IsSol 24 25 M e r s := by
  simpa using not_isSol (p := 24) (q := 25) (a := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) fiberCheck_twentyfour_twentyfive M e r s

theorem not_isSol_twelve_thirtyseven (M e r s : ℤ) : ¬ IsSol 12 37 M e r s := by
  simpa using not_isSol (p := 12) (q := 37) (a := 35) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) fiberCheck_twelve_thirtyseven M e r s

theorem not_isSol_sixteen_sixtyfive (M e r s : ℤ) : ¬ IsSol 16 65 M e r s := by
  simpa using not_isSol (p := 16) (q := 65) (a := 63) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) fiberCheck_sixteen_sixtyfive M e r s

theorem not_isSol_eightyfour_eightyfive (M e r s : ℤ) : ¬ IsSol 84 85 M e r s := by
  simpa using not_isSol (p := 84) (q := 85) (a := 13) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide) fiberCheck_eightyfour_eightyfive M e r s

end Descent

/-- For rational `t ≠ 0`, `t² + 144` and `t² + 169` are not both squares. -/
theorem not_isSquare_sq_add_144_and_sq_add_169 {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 144) ∧ IsSquare (t ^ 2 + 169)) := by
  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := 12) (q := 13) (a := 5) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    Descent.fiberCheck_twelve_thirteen ht
  norm_num at this
  exact fun h ↦ this h.1 h.2

/-- For rational `t ≠ 0`, `t² + 64` and `t² + 289` are not both squares. -/
theorem not_isSquare_sq_add_64_and_sq_add_289 {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 64) ∧ IsSquare (t ^ 2 + 289)) := by
  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := 8) (q := 17) (a := 15) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    Descent.fiberCheck_eight_seventeen ht
  norm_num at this
  exact fun h ↦ this h.1 h.2

/-- For rational `t ≠ 0`, `t² + 576` and `t² + 625` are not both squares. -/
theorem not_isSquare_sq_add_576_and_sq_add_625 {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 576) ∧ IsSquare (t ^ 2 + 625)) := by
  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := 24) (q := 25) (a := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    Descent.fiberCheck_twentyfour_twentyfive ht
  norm_num at this
  exact fun h ↦ this h.1 h.2

/-- For rational `t ≠ 0`, `t² + 144` and `t² + 1369` are not both squares. -/
theorem not_isSquare_sq_add_144_and_sq_add_1369 {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 144) ∧ IsSquare (t ^ 2 + 1369)) := by
  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := 12) (q := 37) (a := 35) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    Descent.fiberCheck_twelve_thirtyseven ht
  norm_num at this
  exact fun h ↦ this h.1 h.2

/-- For rational `t ≠ 0`, `t² + 256` and `t² + 4225` are not both squares. -/
theorem not_isSquare_sq_add_256_and_sq_add_4225 {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 256) ∧ IsSquare (t ^ 2 + 4225)) := by
  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := 16) (q := 65) (a := 63) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    Descent.fiberCheck_sixteen_sixtyfive ht
  norm_num at this
  exact fun h ↦ this h.1 h.2

/-- For rational `t ≠ 0`, `t² + 7056` and `t² + 7225` are not both squares. -/
theorem not_isSquare_sq_add_7056_and_sq_add_7225 {t : ℚ} (ht : t ≠ 0) :
    ¬ (IsSquare (t ^ 2 + 7056) ∧ IsSquare (t ^ 2 + 7225)) := by
  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := 84) (q := 85) (a := 13) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    Descent.fiberCheck_eightyfour_eightyfive ht
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

/-- **No perfect cuboid has two edges in ratio `7 : 24`.** This is the fiber `(m, n) = (4, 3)`:
with `X = 7k`, `Z = 24k`, the face diagonal `√(Y² + 576k²)` and the space diagonal
`√(Y² + 625k²)` cannot both be integers. -/
theorem not_isPerfectCuboid_seven_twentyfour {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    24 * X ≠ 7 * Z := by
  intro hXZ
  obtain ⟨k, rfl⟩ : 7 ∣ X := by omega
  obtain rfl : Z = 24 * k := by omega
  obtain ⟨r, hr⟩ := h.sq_bc
  obtain ⟨s, hs⟩ := h.sq_abc
  have hY := h.pos_b
  have hk : 0 < k := by have := h.pos_a; omega
  apply Descent.not_isSol_twentyfour_twentyfive (Y : ℤ) k r s
  refine ⟨by exact_mod_cast hY.ne', by exact_mod_cast hk.ne', ?_, ?_⟩
  · have : ((Y ^ 2 + (24 * k) ^ 2 : ℕ) : ℤ) = ((r * r : ℕ) : ℤ) := by rw [hr]
    push_cast at this
    linear_combination this
  · have : (((7 * k) ^ 2 + Y ^ 2 + (24 * k) ^ 2 : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    linear_combination this

/-- **No perfect cuboid has two edges in ratio `12 : 35`.** This is the fiber `(m, n) = (6, 1)`:
with `X = 12k`, `Z = 35k`, the face diagonal `√(Y² + 144k²)` and the space diagonal
`√(Y² + 1369k²)` cannot both be integers. -/
theorem not_isPerfectCuboid_twelve_thirtyfive {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    35 * X ≠ 12 * Z := by
  intro hXZ
  obtain ⟨k, rfl⟩ : 12 ∣ X := by omega
  obtain rfl : Z = 35 * k := by omega
  obtain ⟨r, hr⟩ := h.sq_ab
  obtain ⟨s, hs⟩ := h.sq_abc
  have hY := h.pos_b
  have hk : 0 < k := by have := h.pos_a; omega
  apply Descent.not_isSol_twelve_thirtyseven (Y : ℤ) k r s
  refine ⟨by exact_mod_cast hY.ne', by exact_mod_cast hk.ne', ?_, ?_⟩
  · have : (((12 * k) ^ 2 + Y ^ 2 : ℕ) : ℤ) = ((r * r : ℕ) : ℤ) := by rw [hr]
    push_cast at this
    linear_combination this
  · have : (((12 * k) ^ 2 + Y ^ 2 + (35 * k) ^ 2 : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    linear_combination this

/-- **No perfect cuboid has two edges in ratio `16 : 63`.** This is the fiber `(m, n) = (8, 1)`:
with `X = 16k`, `Z = 63k`, the face diagonal `√(Y² + 256k²)` and the space diagonal
`√(Y² + 4225k²)` cannot both be integers. -/
theorem not_isPerfectCuboid_sixteen_sixtythree {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    63 * X ≠ 16 * Z := by
  intro hXZ
  obtain ⟨k, rfl⟩ : 16 ∣ X := by omega
  obtain rfl : Z = 63 * k := by omega
  obtain ⟨r, hr⟩ := h.sq_ab
  obtain ⟨s, hs⟩ := h.sq_abc
  have hY := h.pos_b
  have hk : 0 < k := by have := h.pos_a; omega
  apply Descent.not_isSol_sixteen_sixtyfive (Y : ℤ) k r s
  refine ⟨by exact_mod_cast hY.ne', by exact_mod_cast hk.ne', ?_, ?_⟩
  · have : (((16 * k) ^ 2 + Y ^ 2 : ℕ) : ℤ) = ((r * r : ℕ) : ℤ) := by rw [hr]
    push_cast at this
    linear_combination this
  · have : (((16 * k) ^ 2 + Y ^ 2 + (63 * k) ^ 2 : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    linear_combination this

/-- **No perfect cuboid has two edges in ratio `13 : 84`.** This is the fiber `(m, n) = (7, 6)`:
with `X = 13k`, `Z = 84k`, the face diagonal `√(Y² + 7056k²)` and the space diagonal
`√(Y² + 7225k²)` cannot both be integers. -/
theorem not_isPerfectCuboid_thirteen_eightyfour {X Y Z : ℕ} (h : IsPerfectCuboid X Y Z) :
    84 * X ≠ 13 * Z := by
  intro hXZ
  obtain ⟨k, rfl⟩ : 13 ∣ X := by omega
  obtain rfl : Z = 84 * k := by omega
  obtain ⟨r, hr⟩ := h.sq_bc
  obtain ⟨s, hs⟩ := h.sq_abc
  have hY := h.pos_b
  have hk : 0 < k := by have := h.pos_a; omega
  apply Descent.not_isSol_eightyfour_eightyfive (Y : ℤ) k r s
  refine ⟨by exact_mod_cast hY.ne', by exact_mod_cast hk.ne', ?_, ?_⟩
  · have : ((Y ^ 2 + (84 * k) ^ 2 : ℕ) : ℤ) = ((r * r : ℕ) : ℤ) := by rw [hr]
    push_cast at this
    linear_combination this
  · have : (((13 * k) ^ 2 + Y ^ 2 + (84 * k) ^ 2 : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) := by rw [hs]
    push_cast at this
    linear_combination this

end PerfectCuboid
