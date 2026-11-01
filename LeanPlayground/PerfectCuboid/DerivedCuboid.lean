module

public import LeanPlayground.PerfectCuboid.Saunderson

/-!
# The derived cuboid of a Saunderson brick is never perfect (Chein 1977, Lagrange 1979)

If `(a, b, c)` is an Euler brick with face diagonals `d, e, f`, then so is its *derived* brick
`(bc, ca, ab)`, with face diagonals `ad`, `be`, `cf` (`IsEulerBrick.derived`). Spohn (1972)
proved that no Saunderson brick is perfect (`not_isPerfectCuboid_saunderson`). Chein (1977) and
Lagrange (1979) proved the same for the derived brick of a Saunderson brick. Leech (1981)
reduced it to a result of Collins (1858): `m² + n²` and `m² + 5n²` are never both nonzero
squares.

## Main results

* `IsEulerBrick.derived` — the derived brick `(bc, ca, ab)` of an Euler brick is an Euler brick.
* `derived_saunderson_space_diag_sq` — for `u² + v² = w²` the derived Saunderson brick has
  `(bc)² + (ca)² + (ab)² = u² v² (t⁴ − 6 s² t² + 25 s⁴)` with `s = w²`, `t = 4uv`.
* `quartic_six_twentyfive` — `t⁴ − 6 s² t² + 25 s⁴ = r²` forces `s = 0` or `t = 0`.
* `not_isPerfectCuboid_derived_saunderson`, `not_isPerfectCuboid_derived_saunderson_int` —
  **Chein–Lagrange**: the derived brick of a Saunderson brick is never perfect.
* `collins` — **Collins (1858)**: `m² + n²` and `m² + 5n²` are both squares only when
  `m n = 0`.

## Proof

Both quartics reduce to Pocklington's `x⁴ + 18 x² y² + y⁴ = z²` (`pocklington_quartic`) by a
polynomial identity, with no new descent. The curve `y² = X (X² − 6X + 25)`, which carries the
quartic in `s, t`, maps to Pocklington's curve `y² = X (X² + 18X + 1)` by a cyclic 4-isogeny
through `y² = X (X + 1)(X + 5)`; that middle curve carries Collins' pair of squares. Written out
in coordinates:

* if `t⁴ − 6 s² t² + 25 s⁴ = r²`, then `x = r (5s² − t²)`, `y = 2st (t² + 5s²)` satisfy
  `x⁴ + 18 x² y² + y⁴ = (625 s⁸ + 500 s⁶ t² − 170 s⁴ t⁴ + 20 s² t⁶ + t⁸)²`;
* if `m² + n² = p²` and `m² + 5n² = q²`, then `x = mp`, `y = nq` satisfy
  `x⁴ + 18 x² y² + y⁴ = (m⁴ + 10 m² n² + 5 n⁴)²`.

Pocklington's theorem then gives `x y = 0`, and in both cases that forces the trivial solution.

For a general Euler brick, the derived brick is perfect iff `σ₂ = a²b² + b²c² + c²a²` is a square,
iff the face-diagonal triangle `(d, e, f)` is Heronian (`Bridges.isSquare_sigma2_iff_derived`,
`Bridges.heron_iff_derived`).
-/

@[expose] public section

namespace PerfectCuboid

/-! ### The derived brick -/

/-- The derived brick `(bc, ca, ab)` of an Euler brick `(a, b, c)` is an Euler brick: if
`b² + c² = d²` then `(ca)² + (ab)² = (ad)²`, and similarly for the other two faces. -/
theorem IsEulerBrick.derived {a b c : ℕ} (h : IsEulerBrick a b c) :
    IsEulerBrick (b * c) (c * a) (a * b) where
  pos_a := Nat.mul_pos h.pos_b h.pos_c
  pos_b := Nat.mul_pos h.pos_c h.pos_a
  pos_c := Nat.mul_pos h.pos_a h.pos_b
  sq_ab := by
    obtain ⟨f, hf⟩ := h.sq_ab
    exact ⟨c * f, by
      rw [show (b * c) ^ 2 + (c * a) ^ 2 = c ^ 2 * (a ^ 2 + b ^ 2) by ring, hf]; ring⟩
  sq_bc := by
    obtain ⟨d, hd⟩ := h.sq_bc
    exact ⟨a * d, by
      rw [show (c * a) ^ 2 + (a * b) ^ 2 = a ^ 2 * (b ^ 2 + c ^ 2) by ring, hd]; ring⟩
  sq_ca := by
    obtain ⟨e, he⟩ := h.sq_ca
    exact ⟨b * e, by
      rw [show (a * b) ^ 2 + (b * c) ^ 2 = b ^ 2 * (c ^ 2 + a ^ 2) by ring, he]; ring⟩

/-! ### The two quartics -/

theorem sq_ne_five_mul_sq {x y : ℕ} (hy : 0 < y) : x ^ 2 ≠ 5 * y ^ 2 := by
  intro h
  have hirr : Irrational √((5 : ℕ) : ℝ) := Nat.Prime.irrational_sqrt (by norm_num)
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have e : ((5 : ℕ) : ℝ) = ((x : ℝ) / y) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    exact_mod_cast h.symm
  exact hirr ⟨(x : ℚ) / y, by rw [e, Real.sqrt_sq (by positivity)]; push_cast; rfl⟩

/-- `t⁴ − 6 s² t² + 25 s⁴ = r²` forces `s = 0` or `t = 0`. The point
`x = r (5s² − t²)`, `y = 2st (t² + 5s²)` lies on Pocklington's quartic. -/
theorem quartic_six_twentyfive {s t r : ℤ}
    (h : t ^ 4 - 6 * s ^ 2 * t ^ 2 + 25 * s ^ 4 = r ^ 2) : s = 0 ∨ t = 0 := by
  have hP : (r * (5 * s ^ 2 - t ^ 2)) ^ 4 +
      18 * (r * (5 * s ^ 2 - t ^ 2)) ^ 2 * (2 * s * t * (t ^ 2 + 5 * s ^ 2)) ^ 2 +
      (2 * s * t * (t ^ 2 + 5 * s ^ 2)) ^ 4 =
      (625 * s ^ 8 + 500 * s ^ 6 * t ^ 2 - 170 * s ^ 4 * t ^ 4 + 20 * s ^ 2 * t ^ 6 +
        t ^ 8) ^ 2 := by
    linear_combination (-(5 * s ^ 2 - t ^ 2) ^ 2 * (25 * r ^ 2 * s ^ 4 -
      10 * r ^ 2 * s ^ 2 * t ^ 2 + r ^ 2 * t ^ 4 +
      625 * s ^ 8 + 1400 * s ^ 6 * t ^ 2 + 830 * s ^ 4 * t ^ 4 +
      56 * s ^ 2 * t ^ 6 + t ^ 8)) * h
  by_contra hst
  rw [not_or] at hst
  obtain ⟨hs, ht⟩ := hst
  have hs2 : 0 < s ^ 2 := by positivity
  have ht2 : 0 < t ^ 2 := by positivity
  rcases pocklington_quartic hP with h0 | h0
  · rcases mul_eq_zero.mp h0 with hr | h5
    · -- `r = 0`, but `t⁴ − 6s²t² + 25s⁴ = (t² − 3s²)² + 16 s⁴ > 0`.
      subst hr
      nlinarith [sq_nonneg (t ^ 2 - 3 * s ^ 2)]
    · -- `t² = 5 s²` is impossible since `5` is not a square.
      have h5' : t ^ 2 = 5 * s ^ 2 := by linear_combination -h5
      refine sq_ne_five_mul_sq (x := t.natAbs) (Int.natAbs_pos.mpr hs) ?_
      zify
      simpa only [sq_abs] using h5'
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact hs h3
      · exact ht h2
    · nlinarith

/-- **Collins (1858).** `m² + n²` and `m² + 5n²` are both squares only when `m = 0` or `n = 0`.
The point `x = mp`, `y = nq` lies on Pocklington's quartic. -/
theorem collins {m n p q : ℤ} (hp : m ^ 2 + n ^ 2 = p ^ 2) (hq : m ^ 2 + 5 * n ^ 2 = q ^ 2) :
    m = 0 ∨ n = 0 := by
  have hP : (m * p) ^ 4 + 18 * (m * p) ^ 2 * (n * q) ^ 2 + (n * q) ^ 4 =
      (m ^ 4 + 10 * m ^ 2 * n ^ 2 + 5 * n ^ 4) ^ 2 := by
    linear_combination (-(m ^ 4) * (p ^ 2 + m ^ 2 + n ^ 2) - 18 * m ^ 2 * n ^ 2 * q ^ 2) * hp +
      (-(n ^ 4) * (q ^ 2 + m ^ 2 + 5 * n ^ 2) - 18 * m ^ 2 * n ^ 2 * (m ^ 2 + n ^ 2)) * hq
  rcases pocklington_quartic hP with h0 | h0
  · rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · subst h
      by_contra hmn
      obtain ⟨hm, -⟩ := not_or.mp hmn
      have : 0 < m ^ 2 := by positivity
      nlinarith [sq_nonneg n]
  · rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inr h
    · subst h
      by_contra hmn
      obtain ⟨hm, -⟩ := not_or.mp hmn
      have : 0 < m ^ 2 := by positivity
      nlinarith [sq_nonneg n]

/-! ### The derived Saunderson brick -/

/-- The space diagonal of the derived Saunderson brick: with `a = u (4v² − w²)`,
`b = v (4u² − w²)`, `c = 4uvw` and `u² + v² = w²`,
`(bc)² + (ca)² + (ab)² = u² v² (t⁴ − 6 s² t² + 25 s⁴)` where `s = w²`, `t = 4uv`. -/
theorem derived_saunderson_space_diag_sq {u v w : ℤ} (h : u ^ 2 + v ^ 2 = w ^ 2) :
    (v * (4 * u ^ 2 - w ^ 2) * (4 * u * v * w)) ^ 2 +
        (4 * u * v * w * (u * (4 * v ^ 2 - w ^ 2))) ^ 2 +
        (u * (4 * v ^ 2 - w ^ 2) * (v * (4 * u ^ 2 - w ^ 2))) ^ 2 =
      u ^ 2 * v ^ 2 * ((4 * u * v) ^ 4 - 6 * (w ^ 2) ^ 2 * (4 * u * v) ^ 2 + 25 * (w ^ 2) ^ 4) := by
  linear_combination (8 * u ^ 2 * v ^ 2 * w ^ 2 *
    (16 * u ^ 2 * v ^ 2 + 2 * u ^ 2 * w ^ 2 + 2 * v ^ 2 * w ^ 2 + 3 * w ^ 4)) * h

/-- The space diagonal of the derived brick of a Saunderson brick with `u v ≠ 0` is never an
integer. -/
theorem derived_saunderson_space_diag_ne_sq {u v w : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : u ^ 2 + v ^ 2 = w ^ 2) (r : ℤ) :
    (v * (4 * u ^ 2 - w ^ 2) * (4 * u * v * w)) ^ 2 +
        (4 * u * v * w * (u * (4 * v ^ 2 - w ^ 2))) ^ 2 +
        (u * (4 * v ^ 2 - w ^ 2) * (v * (4 * u ^ 2 - w ^ 2))) ^ 2 ≠ r ^ 2 := by
  intro hr
  rw [derived_saunderson_space_diag_sq h] at hr
  have huv : (u * v) ^ 2 ≠ 0 := by positivity
  obtain ⟨r', rfl⟩ : u * v ∣ r := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero]
    exact ⟨(4 * u * v) ^ 4 - 6 * (w ^ 2) ^ 2 * (4 * u * v) ^ 2 + 25 * (w ^ 2) ^ 4,
      by rw [← hr]; ring⟩
  have hq : (4 * u * v) ^ 4 - 6 * (w ^ 2) ^ 2 * (4 * u * v) ^ 2 + 25 * (w ^ 2) ^ 4 = r' ^ 2 := by
    have : (u * v) ^ 2 * ((4 * u * v) ^ 4 - 6 * (w ^ 2) ^ 2 * (4 * u * v) ^ 2 +
        25 * (w ^ 2) ^ 4) = (u * v) ^ 2 * r' ^ 2 := by
      rw [mul_pow] at hr ⊢; linear_combination hr
    exact mul_left_cancel₀ huv this
  rcases quartic_six_twentyfive hq with h0 | h0
  · -- `w = 0` would force `u = v = 0`.
    have hw : w = 0 := pow_eq_zero_iff two_ne_zero |>.mp h0
    subst hw
    have : 0 < u ^ 2 := by positivity
    nlinarith [sq_nonneg v]
  · simp [hu, hv] at h0

/-- **Chein (1977), Lagrange (1979)** (integer form): the derived brick `(bc, ca, ab)` of the
Saunderson brick `a = |u (4v² − w²)|`, `b = |v (4u² − w²)|`, `c = |4uvw|` is never perfect. -/
theorem not_isPerfectCuboid_derived_saunderson_int {u v w : ℤ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : u ^ 2 + v ^ 2 = w ^ 2) :
    ¬ IsPerfectCuboid ((v * (4 * u ^ 2 - w ^ 2)).natAbs * (4 * u * v * w).natAbs)
      ((4 * u * v * w).natAbs * (u * (4 * v ^ 2 - w ^ 2)).natAbs)
      ((u * (4 * v ^ 2 - w ^ 2)).natAbs * (v * (4 * u ^ 2 - w ^ 2)).natAbs) := by
  rintro ⟨-, r, hr⟩
  have hr' := congrArg (Nat.cast : ℕ → ℤ) hr
  push_cast at hr'
  simp only [mul_pow, sq_abs] at hr'
  refine derived_saunderson_space_diag_ne_sq hu hv h r ?_
  simp only [mul_pow]
  linear_combination hr'

/-- **Chein (1977), Lagrange (1979).** The derived brick `(bc, ca, ab)` of the Saunderson brick
`(a, b, c)` built from a Pythagorean triple `u² + v² = w²` with `u, v > 0`
(`PerfectCuboid.saunderson`) is an Euler brick (`IsEulerBrick.derived`) but never a perfect
cuboid. -/
theorem not_isPerfectCuboid_derived_saunderson {u v w : ℕ} (hu : 0 < u) (hv : 0 < v)
    (h : u ^ 2 + v ^ 2 = w ^ 2) :
    ¬ IsPerfectCuboid (v * ((4 * u ^ 2 : ℤ) - w ^ 2).natAbs * (4 * u * v * w))
      (4 * u * v * w * (u * ((4 * v ^ 2 : ℤ) - w ^ 2).natAbs))
      (u * ((4 * v ^ 2 : ℤ) - w ^ 2).natAbs * (v * ((4 * u ^ 2 : ℤ) - w ^ 2).natAbs)) := by
  rintro ⟨-, r, hr⟩
  have hz : (u : ℤ) ^ 2 + v ^ 2 = w ^ 2 := by exact_mod_cast h
  have hr' := congrArg (Nat.cast : ℕ → ℤ) hr
  push_cast at hr'
  simp only [mul_pow, sq_abs] at hr'
  refine derived_saunderson_space_diag_ne_sq (by exact_mod_cast hu.ne') (by exact_mod_cast hv.ne')
    hz r ?_
  simp only [mul_pow]
  linear_combination hr'

/-- The derived brick of a Saunderson brick is an Euler brick. -/
theorem derived_saunderson_isEulerBrick {u v w : ℕ} (hu : 0 < u) (hv : 0 < v)
    (h : u ^ 2 + v ^ 2 = w ^ 2) :
    IsEulerBrick (v * ((4 * u ^ 2 : ℤ) - w ^ 2).natAbs * (4 * u * v * w))
      (4 * u * v * w * (u * ((4 * v ^ 2 : ℤ) - w ^ 2).natAbs))
      (u * ((4 * v ^ 2 : ℤ) - w ^ 2).natAbs * (v * ((4 * u ^ 2 : ℤ) - w ^ 2).natAbs)) :=
  (saunderson hu hv h).derived

end PerfectCuboid
