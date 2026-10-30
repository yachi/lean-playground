module

public import LeanPlayground.PerfectCuboid.Saunderson
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Euler's two-parameter family of Euler bricks is never perfect

Euler's family of Euler bricks (as listed in Knill's notes "Treasure hunting perfect Euler
bricks", Harvard 2009) is
`a = 2mn(3m² − n²)(3n² − m²)`, `b = 8mn(m⁴ − n⁴)`,
`c = (m² − n²)(m² − 4mn + n²)(m² + 4mn + n²)`, with face diagonals
`a² + b² = (2mn(5m⁴ − 6m²n² + 5n⁴))²`, `a² + c² = ((m² + n²)³)²` and
`b² + c² = ((m² − n²)(m⁴ + 18m²n² + n⁴))²`. Its space diagonal is
`a² + b² + c² = (m² + n²)² (m⁸ + 68m⁶n² − 122m⁴n⁴ + 68m²n⁶ + n⁸)`.

The octic is Pocklington's quartic in disguise:
`m⁸ + 68m⁶n² − 122m⁴n⁴ + 68m²n⁶ + n⁸ = x⁴ + 18x²y² + y⁴` with `x = m² − n²`, `y = 2mn`
(`euler_octic_eq_pocklington`). In fact the whole family is Saunderson's brick for Euclid's
triple `(u, v, w) = (m² − n², 2mn, m² + n²)`, up to signs and the order of the edges
(`euler_eq_saunderson`). So Pocklington's theorem (`pocklington_quartic`) gives the result
at once: no brick of the family is perfect.

## Main results

* `euler_isEulerBrick` — for `m, n ≠ 0` and `m² ≠ n²` the edges are nonzero and the face
  diagonals are integers.
* `euler_eq_saunderson` — the family is Saunderson's for Euclid's triple.
* `euler_space_diag_sq` — the space-diagonal identity.
* `euler_octic_ne_sq` — `m⁸ + 68m⁶n² − 122m⁴n⁴ + 68m²n⁶ + n⁸` is a square only when
  `m n (m² − n²) = 0`.
* `not_isPerfectCuboid_euler` — no brick of the family is a perfect cuboid.
-/

@[expose] public section

namespace PerfectCuboid

namespace EulerFamily

/-- The first edge `2mn(3m² − n²)(3n² − m²)`. -/
def a (m n : ℤ) : ℤ := 2 * m * n * (3 * m ^ 2 - n ^ 2) * (3 * n ^ 2 - m ^ 2)

/-- The second edge `8mn(m⁴ − n⁴)`. -/
def b (m n : ℤ) : ℤ := 8 * m * n * (m ^ 4 - n ^ 4)

/-- The third edge `(m² − n²)(m² − 4mn + n²)(m² + 4mn + n²)`. -/
def c (m n : ℤ) : ℤ :=
  (m ^ 2 - n ^ 2) * (m ^ 2 - 4 * m * n + n ^ 2) * (m ^ 2 + 4 * m * n + n ^ 2)

/-- The octic `m⁸ + 68m⁶n² − 122m⁴n⁴ + 68m²n⁶ + n⁸`. -/
def octic (m n : ℤ) : ℤ :=
  m ^ 8 + 68 * m ^ 6 * n ^ 2 - 122 * m ^ 4 * n ^ 4 + 68 * m ^ 2 * n ^ 6 + n ^ 8

end EulerFamily

open EulerFamily

/-! ### The identities -/

/-- The family is Saunderson's brick `(u (4v² − w²), v (4u² − w²), 4uvw)` for Euclid's triple
`(u, v, w) = (m² − n², 2mn, m² + n²)`: its edges are `-c`, `-a` and `b`. -/
theorem euler_eq_saunderson (m n : ℤ) :
    (m ^ 2 - n ^ 2) * (4 * (2 * m * n) ^ 2 - (m ^ 2 + n ^ 2) ^ 2) = -c m n ∧
      2 * m * n * (4 * (m ^ 2 - n ^ 2) ^ 2 - (m ^ 2 + n ^ 2) ^ 2) = -a m n ∧
      4 * (m ^ 2 - n ^ 2) * (2 * m * n) * (m ^ 2 + n ^ 2) = b m n := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [a, b, c] <;> ring

theorem euler_sq_ab (m n : ℤ) :
    a m n ^ 2 + b m n ^ 2 = (2 * m * n * (5 * m ^ 4 - 6 * m ^ 2 * n ^ 2 + 5 * n ^ 4)) ^ 2 := by
  simp only [a, b]; ring

theorem euler_sq_ac (m n : ℤ) : a m n ^ 2 + c m n ^ 2 = ((m ^ 2 + n ^ 2) ^ 3) ^ 2 := by
  simp only [a, c]; ring

theorem euler_sq_bc (m n : ℤ) :
    b m n ^ 2 + c m n ^ 2 = ((m ^ 2 - n ^ 2) * (m ^ 4 + 18 * m ^ 2 * n ^ 2 + n ^ 4)) ^ 2 := by
  simp only [b, c]; ring

/-- The space diagonal: `a² + b² + c² = (m² + n²)² · octic`. -/
theorem euler_space_diag_sq (m n : ℤ) :
    a m n ^ 2 + b m n ^ 2 + c m n ^ 2 = (m ^ 2 + n ^ 2) ^ 2 * octic m n := by
  simp only [a, b, c, octic]; ring

/-- The octic is Pocklington's quartic `x⁴ + 18x²y² + y⁴` at `x = m² − n²`, `y = 2mn`. -/
theorem euler_octic_eq_pocklington (m n : ℤ) :
    octic m n = (m ^ 2 - n ^ 2) ^ 4 + 18 * (m ^ 2 - n ^ 2) ^ 2 * (2 * m * n) ^ 2 +
      (2 * m * n) ^ 4 := by
  simp only [octic]; ring

/-! ### Pocklington's theorem for the octic -/

/-- **Euler's octic is never a square** except on the degenerate lines `m n (m² − n²) = 0`. -/
theorem euler_octic_ne_sq {m n z : ℤ} (h : octic m n = z ^ 2) :
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2 := by
  rw [euler_octic_eq_pocklington] at h
  rcases pocklington_quartic h with h0 | h0
  · exact Or.inr (Or.inr (sub_eq_zero.mp h0))
  · rcases mul_eq_zero.mp h0 with h0 | h0
    · exact Or.inl (by simpa using h0)
    · exact Or.inr (Or.inl h0)

/-! ### The bricks are genuine Euler bricks -/

/-- `3x² = y²` forces `x = 0`, because `3` is not a rational square. -/
theorem eq_zero_of_three_mul_sq_eq_sq {x y : ℤ} (h : 3 * x ^ 2 = y ^ 2) : x = 0 := by
  by_contra hx
  have hq : IsSquare ((3 : ℕ) : ℚ) := by
    refine ⟨(y : ℚ) / x, ?_⟩
    have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast hx
    have h' : (3 : ℚ) * x ^ 2 = y ^ 2 := by exact_mod_cast h
    field_simp
    push_cast
    linear_combination h'
  rw [Rat.isSquare_natCast_iff] at hq
  exact absurd hq (by decide +kernel)

theorem a_ne_zero {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) : a m n ≠ 0 := by
  simp only [a]
  have h1 : 3 * m ^ 2 - n ^ 2 ≠ 0 := fun h ↦
    hm (eq_zero_of_three_mul_sq_eq_sq (y := n) (by linear_combination h))
  have h2 : 3 * n ^ 2 - m ^ 2 ≠ 0 := fun h ↦
    hn (eq_zero_of_three_mul_sq_eq_sq (y := m) (by linear_combination h))
  positivity

theorem b_ne_zero {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ^ 2 ≠ n ^ 2) : b m n ≠ 0 := by
  simp only [b]
  have h1 : m ^ 4 - n ^ 4 ≠ 0 := by
    intro h
    have : (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact hmn (sub_eq_zero.mp h)
    · have : 0 < m ^ 2 + n ^ 2 := by positivity
      omega
  positivity

theorem c_ne_zero {m n : ℤ} (hn : n ≠ 0) (hmn : m ^ 2 ≠ n ^ 2) : c m n ≠ 0 := by
  simp only [c]
  have h1 : m ^ 2 - n ^ 2 ≠ 0 := sub_ne_zero.mpr hmn
  have h2 : m ^ 2 - 4 * m * n + n ^ 2 ≠ 0 := fun h ↦
    hn (eq_zero_of_three_mul_sq_eq_sq (y := m - 2 * n) (by linear_combination -h))
  have h3 : m ^ 2 + 4 * m * n + n ^ 2 ≠ 0 := fun h ↦
    hn (eq_zero_of_three_mul_sq_eq_sq (y := m + 2 * n) (by linear_combination -h))
  positivity

theorem isSquare_natAbs_sq_add_sq {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    IsSquare (x.natAbs ^ 2 + y.natAbs ^ 2) :=
  ⟨z.natAbs, by
    rw [← sq]
    zify
    simp only [sq_abs]
    exact h⟩

/-- **Euler's family consists of Euler bricks**: for `m, n ≠ 0` and `m² ≠ n²` the three
edges are nonzero and all three face diagonals are integers. -/
theorem euler_isEulerBrick {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ^ 2 ≠ n ^ 2) :
    IsEulerBrick (a m n).natAbs (b m n).natAbs (c m n).natAbs where
  pos_a := Int.natAbs_pos.mpr (a_ne_zero hm hn)
  pos_b := Int.natAbs_pos.mpr (b_ne_zero hm hn hmn)
  pos_c := Int.natAbs_pos.mpr (c_ne_zero hn hmn)
  sq_ab := isSquare_natAbs_sq_add_sq (euler_sq_ab m n)
  sq_bc := isSquare_natAbs_sq_add_sq (euler_sq_bc m n)
  sq_ca := isSquare_natAbs_sq_add_sq (by rw [add_comm]; exact euler_sq_ac m n)

/-- `(m, n) = (2, 1)` gives Halcke's brick `(44, 240, 117)`. -/
theorem euler_two_one : ((a 2 1).natAbs, (b 2 1).natAbs, (c 2 1).natAbs) = (44, 240, 117) := by
  decide

/-! ### No brick of the family is perfect -/

/-- The space diagonal of a nondegenerate brick of the family is never an integer. -/
theorem euler_space_diag_ne_sq {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ^ 2 ≠ n ^ 2)
    (r : ℤ) : a m n ^ 2 + b m n ^ 2 + c m n ^ 2 ≠ r ^ 2 := by
  intro hr
  rw [euler_space_diag_sq] at hr
  have hw : (m ^ 2 + n ^ 2) ^ 2 ≠ 0 := by positivity
  obtain ⟨r', rfl⟩ : m ^ 2 + n ^ 2 ∣ r := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨_, hr.symm⟩
  have hq : octic m n = r' ^ 2 :=
    mul_left_cancel₀ hw (by rw [hr]; ring)
  rcases euler_octic_ne_sq hq with h0 | h0 | h0
  · exact hm h0
  · exact hn h0
  · exact hmn h0

/-- **No brick of Euler's family is a perfect cuboid.** -/
theorem not_isPerfectCuboid_euler {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ^ 2 ≠ n ^ 2) :
    ¬ IsPerfectCuboid (a m n).natAbs (b m n).natAbs (c m n).natAbs := by
  rintro ⟨-, r, hr⟩
  have hr' : ((a m n).natAbs : ℤ) ^ 2 + ((b m n).natAbs : ℤ) ^ 2 + ((c m n).natAbs : ℤ) ^ 2 =
      (r : ℤ) ^ 2 := by
    rw [sq (r : ℤ)]; exact_mod_cast hr
  simp only [Int.natCast_natAbs, sq_abs] at hr'
  exact euler_space_diag_ne_sq hm hn hmn r hr'

end PerfectCuboid
