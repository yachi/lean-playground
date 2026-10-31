module

public import LeanPlayground.PerfectCuboid.Basic
public import LeanPlayground.PerfectCuboid.FermatTriangle

/-!
# Leech's edge cuboids never have an integral third edge

Leech (*The rational cuboid revisited*, Amer. Math. Monthly 84 (1977) 518–533; see van Luijk,
*On Perfect Cuboids*, 2000, §2, formula (6)): for a Pythagorean triple `ξ² + η² = ζ²` put
`τ = (ζ⁸ − 6ξ²η²ζ⁴ + ξ⁴η⁴) / (2ξηζ)²`. Then `τ + ξ²`, `τ + η²` and `τ + ζ²` are squares, so
after scaling by `2ξηζ` the box with edges `2ξ²ηζ`, `2ξη²ζ`, `√T`,
`T = ζ⁸ − 6ξ²η²ζ⁴ + ξ⁴η⁴`, is an edge cuboid. Leech showed `T` is never a square, from
`T (ζ⁴ + ξ²η²)² = (ζ⁴ − ξ²η²)⁴ − (2ξηζ²)⁴` and Fermat's `x⁴ − y⁴ ≠ z²`.

We prove the slightly stronger `T ≠ □` for **all** integers with `ξηζ ≠ 0` (the Pythagorean
relation is not needed), via `a⁴ − 6a²b² + b⁴ = □ ⇒ ab = 0` (`quartic_neg_six`).
-/

@[expose] public section

namespace PerfectCuboid

namespace LeechEdge

/-- `ζ⁸ − 6ξ²η²ζ⁴ + ξ⁴η⁴`, the square of the missing edge (after scaling). -/
def T (x y z : ℤ) : ℤ := z ^ 8 - 6 * x ^ 2 * y ^ 2 * z ^ 4 + x ^ 4 * y ^ 4

end LeechEdge

open LeechEdge

/-! ### The edge cuboid -/

theorem leechEdge_sq_ab {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    (2 * x ^ 2 * y * z) ^ 2 + (2 * x * y ^ 2 * z) ^ 2 = (2 * x * y * z ^ 2) ^ 2 := by
  linear_combination (2 * x * y * z) ^ 2 * h

theorem leechEdge_sq_ac {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    (2 * x ^ 2 * y * z) ^ 2 + T x y z = (x ^ 2 * z ^ 2 - y ^ 4) ^ 2 := by
  simp only [T]
  linear_combination (-(y ^ 6 - y ^ 4 * x ^ 2 + y ^ 4 * z ^ 2 - 4 * y ^ 2 * x ^ 2 * z ^ 2 +
    y ^ 2 * z ^ 4 + x ^ 2 * z ^ 4 + z ^ 6)) * h

theorem leechEdge_sq_bc {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    (2 * x * y ^ 2 * z) ^ 2 + T x y z = (x ^ 4 - y ^ 2 * z ^ 2) ^ 2 := by
  simp only [T]
  linear_combination (-(-y ^ 2 * x ^ 4 - 4 * y ^ 2 * x ^ 2 * z ^ 2 + y ^ 2 * z ^ 4 + x ^ 6 +
    x ^ 4 * z ^ 2 + x ^ 2 * z ^ 4 + z ^ 6)) * h

theorem leechEdge_sq_abc {x y z : ℤ} (h : x ^ 2 + y ^ 2 = z ^ 2) :
    (2 * x ^ 2 * y * z) ^ 2 + (2 * x * y ^ 2 * z) ^ 2 + T x y z = (z ^ 4 - x ^ 2 * y ^ 2) ^ 2 := by
  simp only [T]
  linear_combination (2 * x * y * z) ^ 2 * h

/-- Leech's identity (no relation needed). -/
theorem leech_identity (x y z : ℤ) :
    T x y z * (z ^ 4 + x ^ 2 * y ^ 2) ^ 2 =
      (z ^ 4 - x ^ 2 * y ^ 2) ^ 4 - (2 * x * y * z ^ 2) ^ 4 := by
  simp only [T]; ring

/-! ### The quartics -/

/-- **Fermat.** `x⁴ − y⁴ = z²` forces `x y z = 0`. -/
theorem fermat_sub {x y z : ℤ} (h : x ^ 4 - y ^ 4 = z ^ 2) : x = 0 ∨ y = 0 ∨ z = 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨hx, hy, hz⟩ := hc
  apply FermatTriangle.not_isSqAreaTriangle (x ^ 4 - y ^ 4) (2 * x ^ 2 * y ^ 2) (x ^ 4 + y ^ 4)
    (|x * y * z|)
  refine ⟨?_, by positivity, abs_pos.mpr (by positivity), by ring, ?_⟩
  · rw [h]; positivity
  · rw [sq_abs]; linear_combination 2 * x ^ 2 * y ^ 2 * h

theorem sq_ne_two_mul_sq {x y : ℕ} (hy : 0 < y) : x ^ 2 ≠ 2 * y ^ 2 := by
  intro h
  have hirr : Irrational √((2 : ℕ) : ℝ) := Nat.Prime.irrational_sqrt (by norm_num)
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have e : ((2 : ℕ) : ℝ) = ((x : ℝ) / y) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    exact_mod_cast h.symm
  exact hirr ⟨(x : ℚ) / y, by rw [e, Real.sqrt_sq (by positivity)]; push_cast; rfl⟩

/-- `a⁴ − 6a²b² + b⁴` is a square only when `a b = 0`: multiply by `(a² + b²)²` to get
`(a² − b²)⁴ − (2ab)⁴`. -/
theorem quartic_neg_six {a b t : ℤ} (h : a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4 = t ^ 2) :
    a = 0 ∨ b = 0 := by
  have key : (a ^ 2 - b ^ 2) ^ 4 - (2 * a * b) ^ 4 = (t * (a ^ 2 + b ^ 2)) ^ 2 := by
    linear_combination (a ^ 2 + b ^ 2) ^ 2 * h
  rcases fermat_sub key with h0 | h0 | h0
  · -- `a² = b²`: then `−4a⁴ = t²`.
    have hb : b ^ 2 = a ^ 2 := by linear_combination -h0
    have h4 : -4 * a ^ 4 = t ^ 2 := by linear_combination h - (b ^ 2 - 5 * a ^ 2) * hb
    left
    have : a ^ 4 = 0 := by nlinarith [sq_nonneg t, sq_nonneg (a ^ 2)]
    exact (pow_eq_zero_iff (by norm_num)).mp this
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact Or.inl h2
    · exact Or.inr h1
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · -- `t = 0`: `(a² − 3b²)² = 2 (2b²)²`, impossible unless `b = 0`.
      subst h1
      by_contra hab
      push Not at hab
      obtain ⟨-, hb⟩ := hab
      have e : (a ^ 2 - 3 * b ^ 2) ^ 2 = 2 * (2 * b ^ 2) ^ 2 := by linear_combination h
      refine sq_ne_two_mul_sq (x := (a ^ 2 - 3 * b ^ 2).natAbs) (y := (2 * b ^ 2).natAbs)
        (Int.natAbs_pos.mpr (by positivity)) ?_
      zify
      simpa only [sq_abs] using e
    · left
      have : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      exact (pow_eq_zero_iff two_ne_zero).mp this

/-- **Leech (1977), strengthened.** `ζ⁸ − 6ξ²η²ζ⁴ + ξ⁴η⁴` is a square only if `ξηζ = 0`. -/
theorem leechEdge_T_ne_sq {x y z t : ℤ} (h : T x y z = t ^ 2) : x * y * z = 0 := by
  have h' : (z ^ 2) ^ 4 - 6 * (z ^ 2) ^ 2 * (x * y) ^ 2 + (x * y) ^ 4 = t ^ 2 := by
    rw [← h]; simp only [T]; ring
  rcases quartic_neg_six h' with h0 | h0
  · rw [(pow_eq_zero_iff two_ne_zero).mp h0, mul_zero]
  · rw [h0, zero_mul]

/-- **No member of Leech's edge-cuboid family is a perfect cuboid.** -/
theorem not_isPerfectCuboid_leechEdge {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (e : ℕ) (he : (e : ℤ) ^ 2 = T x y z) :
    ¬ IsPerfectCuboid (2 * x ^ 2 * y * z).natAbs (2 * x * y ^ 2 * z).natAbs e := fun _ ↦ by
  have := leechEdge_T_ne_sq he.symm
  simp [hx, hy, hz] at this

end PerfectCuboid
