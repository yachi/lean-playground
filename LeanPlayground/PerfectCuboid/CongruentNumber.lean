module

public import LeanPlayground.PerfectCuboid.ConfigCuboid
public import LeanPlayground.PerfectCuboid.FermatTriangle
public import LeanPlayground.PerfectCuboid.Torsion

/-!
# Congruent numbers and the curve `E_N`

A rational number `N` is *congruent* if it is the area of a right triangle with rational sides.
This file proves the classical criterion (Koblitz, *Introduction to Elliptic Curves and Modular
Forms*, Ch. I §§1–2; Conrad, *The congruent number problem*) and applies it to perfect cuboids.

## Main results

* `isCongruent_iff`: for `N > 0`, `N` is congruent if and only if `E_N : Y² = X³ − N²X` has a
  rational point with `Y ≠ 0`. The triangle `(a, b, c)` gives `X = (c/2)²`,
  `Y = c(a² − b²)/8`; the point `(x, y)` gives the triangle with sides
  `|(x² − N²)/y|`, `|2Nx/y|`, `|(x² + N²)/y|`.
* `isCongruent_iff_exists_add_self_ne_zero`: the same with points of the group `E_N(ℚ)`: `N` is
  congruent if and only if `E_N(ℚ)` has a point of order other than `1` and `2`.
* `isCongruent_iff_exists_nonTors`: `N > 0` is congruent if and only if `E_N(ℚ)` has a point of
  infinite order, since every torsion point has order at most `2` (`torsionTwo`, Asiryan's
  Remark 1, proved in `Torsion.lean`).
* `isCongruent_mul_sq_iff`: being congruent depends only on the square class of `N`.
* `add_self_eq_zero_of_sq` (Fermat): for `N = q²`, in particular `N = 1`, every rational point of
  `E_N` is a `2`-torsion point, so `E_N(ℚ) = {0, (0, 0), (±N, 0)}`. This is "`E_1` has rank `0`"
  without Mordell–Weil, because the conclusion is about every point.
* `IsPerfectCuboid.isCongruent`: a perfect cuboid with edges `a, b, c` and space diagonal `g`
  makes both `abcg/2` and its squarefree part `N` congruent numbers, and gives a point of `E_N`
  outside the `2`-torsion, which has infinite order (`IsPerfectCuboid.exists_nonTors`).
-/

@[expose] public section

namespace PerfectCuboid.CongruentRank

open WeierstrassCurve WeierstrassCurve.Affine

/-- `N` is a *congruent number*: the area of a right triangle with rational sides `a, b, c`. -/
def IsCongruent (N : ℚ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 * N

variable {N : ℚ}

theorem IsCongruent.pos (h : IsCongruent N) : 0 < N := by
  obtain ⟨a, b, c, ha, hb, -, hab⟩ := h
  nlinarith [mul_pos ha hb]

/-! ### Square classes -/

theorem IsCongruent.mul_sq (h : IsCongruent N) {q : ℚ} (hq : q ≠ 0) :
    IsCongruent (q ^ 2 * N) := by
  obtain ⟨a, b, c, ha, hb, h1, h2⟩ := h
  have : 0 < |q| := abs_pos.mpr hq
  refine ⟨|q| * a, |q| * b, |q| * c, by positivity, by positivity, ?_, ?_⟩
  · linear_combination |q| ^ 2 * h1
  · linear_combination |q| ^ 2 * h2 + 2 * N * sq_abs q

/-- Being congruent depends only on the class of `N` in `ℚ*/ℚ*²`. -/
theorem isCongruent_mul_sq_iff {q : ℚ} (hq : q ≠ 0) :
    IsCongruent (q ^ 2 * N) ↔ IsCongruent N := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mul_sq hq⟩
  have := h.mul_sq (inv_ne_zero hq)
  rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hq, one_pow, one_mul] at this

/-! ### Triangles and points -/

/-- The point `((c/2)², c(a² − b²)/8)` of a right triangle of area `N` lies on `E_N`. -/
theorem triangle_point_eq {a b c : ℚ} (h1 : a ^ 2 + b ^ 2 = c ^ 2) (h2 : a * b = 2 * N) :
    (c * (a ^ 2 - b ^ 2) / 8) ^ 2 = (c ^ 2 / 4) ^ 3 - N ^ 2 * (c ^ 2 / 4) := by
  linear_combination (c ^ 2 / 64) * ((a ^ 2 + b ^ 2 + c ^ 2) * h1 - 4 * (a * b + 2 * N) * h2)

/-- The legs of a right triangle with rational sides are never equal, since `√2 ∉ ℚ`. -/
theorem sq_ne_sq_of_triangle {a b c : ℚ} (ha : 0 < a) (h1 : a ^ 2 + b ^ 2 = c ^ 2) :
    a ^ 2 ≠ b ^ 2 := by
  intro hab
  apply sq_ne_two (c / a)
  rw [div_pow, ← h1, hab, ← hab]
  field_simp
  ring

/-- The triangle of a point `(x, y)` of `E_N` with `y ≠ 0`. -/
theorem point_triangle {x y : ℚ} (hN : 0 < N) (hy : y ^ 2 = x ^ 3 - N ^ 2 * x) (hy0 : y ≠ 0) :
    0 < |(x ^ 2 - N ^ 2) / y| ∧ 0 < |2 * N * x / y| ∧
      |(x ^ 2 - N ^ 2) / y| ^ 2 + |2 * N * x / y| ^ 2 = ((x ^ 2 + N ^ 2) / y) ^ 2 ∧
      |(x ^ 2 - N ^ 2) / y| * |2 * N * x / y| = 2 * N := by
  have hxy : x * (x ^ 2 - N ^ 2) ≠ 0 := by
    intro h
    exact hy0 (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination hy + h))
  have hx : x ≠ 0 := left_ne_zero_of_mul hxy
  have hx2 : x ^ 2 - N ^ 2 ≠ 0 := right_ne_zero_of_mul hxy
  refine ⟨abs_pos.mpr (div_ne_zero hx2 hy0),
    abs_pos.mpr (div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hN.ne') hx) hy0), ?_, ?_⟩
  · rw [sq_abs, sq_abs]
    field_simp
    ring
  · have : (x ^ 2 - N ^ 2) / y * (2 * N * x / y) = 2 * N := by
      field_simp
      linear_combination -hy
    rw [← abs_mul, this, abs_of_pos (by positivity)]

/-- **The congruent number criterion.** For `N > 0`, `N` is a congruent number if and only if
`E_N : Y² = X³ − N²X` has a rational point with `Y ≠ 0`. -/
theorem isCongruent_iff (hN : 0 < N) :
    IsCongruent N ↔ ∃ x y : ℚ, (curve N).Equation x y ∧ y ≠ 0 := by
  constructor
  · rintro ⟨a, b, c, ha, hb, h1, h2⟩
    refine ⟨c ^ 2 / 4, c * (a ^ 2 - b ^ 2) / 8, equation_iff.mpr (triangle_point_eq h1 h2), ?_⟩
    have hc : c ≠ 0 := by
      rintro rfl
      nlinarith
    exact div_ne_zero (mul_ne_zero hc (sub_ne_zero.mpr (sq_ne_sq_of_triangle ha h1)))
      (by norm_num)
  · rintro ⟨x, y, h, hy0⟩
    obtain ⟨ha, hb, h1, h2⟩ := point_triangle hN (equation_iff.mp h) hy0
    exact ⟨_, _, _, ha, hb, h1, h2⟩

/-! ### Points of the group `E_N(ℚ)` -/

theorem negY_eq (x y : ℚ) : (curve N).negY x y = -y := by
  simp [curve, negY]

/-- An affine point of `E_N` is `2`-torsion exactly when its `Y`-coordinate is `0`. -/
theorem some_add_self_eq_zero_iff {x y : ℚ} (h : (curve N).Nonsingular x y) :
    Point.some x y h + Point.some x y h = 0 ↔ y = 0 := by
  constructor
  · intro hP
    by_contra hy
    rw [Point.add_self_of_Y_ne (by rw [negY_eq]; intro h'; exact hy (by linarith))] at hP
    exact Point.some_ne_zero _ hP
  · rintro rfl
    exact Point.add_self_of_Y_eq (by rw [negY_eq, neg_zero])

/-- `N > 0` is congruent if and only if `E_N(ℚ)` has a point that is not `2`-torsion. -/
theorem isCongruent_iff_exists_add_self_ne_zero (hN : 0 < N) :
    IsCongruent N ↔ ∃ P : (curve N).Point, P + P ≠ 0 := by
  rw [isCongruent_iff hN]
  constructor
  · rintro ⟨x, y, h, hy0⟩
    have hns := (nonsingular_iff hN.ne').mpr (equation_iff.mp h)
    exact ⟨.some x y hns, (some_add_self_eq_zero_iff hns).not.mpr hy0⟩
  · rintro ⟨P, hP⟩
    cases P with
    | zero => exact absurd (zero_add 0) hP
    | some x y h => exact ⟨x, y, h.1, (some_add_self_eq_zero_iff h).not.mp hP⟩

/-- A point of infinite order makes `N` congruent. -/
theorem IsCongruent.of_nonTors (hN : 0 < N) {G : (curve N).Point} (hG : NonTors G) :
    IsCongruent N := by
  refine (isCongruent_iff_exists_add_self_ne_zero hN).mpr ⟨G, ?_⟩
  rw [← two_nsmul]
  exact hG 2 two_pos

/-- If every torsion point has order at most `2` (Asiryan, Remark 1), a point outside the
`2`-torsion has infinite order. -/
theorem nonTors_of_add_self_ne_zero (htor : TorsionTwo N) {P : (curve N).Point} (hP : P + P ≠ 0) :
    NonTors P :=
  fun n hn h ↦ hP (htor P n hn h)

/-- **Congruent numbers and rank.** `N > 0` is congruent if and only if `E_N(ℚ)` has a point of
infinite order. -/
theorem isCongruent_iff_exists_nonTors (hN : 0 < N) :
    IsCongruent N ↔ ∃ G : (curve N).Point, NonTors G := by
  refine ⟨fun h ↦ ?_, fun ⟨G, hG⟩ ↦ IsCongruent.of_nonTors hN hG⟩
  obtain ⟨P, hP⟩ := (isCongruent_iff_exists_add_self_ne_zero hN).mp h
  exact ⟨P, nonTors_of_add_self_ne_zero (torsionTwo hN.ne') hP⟩

/-! ### Fermat: `E_1(ℚ)` is the `2`-torsion -/

/-- **Fermat.** `1` is not a congruent number. -/
theorem not_isCongruent_one : ¬ IsCongruent 1 := by
  rintro ⟨a, b, c, ha, hb, h1, h2⟩
  exact FermatTriangle.not_congruent_one ⟨a, b, c, ha, hb, h1, by rw [h2, mul_one]⟩

/-- If `N > 0` is not congruent, every rational point of `E_N` is a `2`-torsion point. -/
theorem add_self_eq_zero_of_not_isCongruent (hN : 0 < N) (h : ¬ IsCongruent N)
    (P : (curve N).Point) : P + P = 0 := by
  by_contra hP
  exact h ((isCongruent_iff_exists_add_self_ne_zero hN).mpr ⟨P, hP⟩)

/-- No nonzero rational square is a congruent number. -/
theorem not_isCongruent_sq {q : ℚ} (hq : q ≠ 0) : ¬ IsCongruent (q ^ 2) := by
  rw [← mul_one (q ^ 2), isCongruent_mul_sq_iff hq]
  exact not_isCongruent_one

/-- **`E_{q²}(ℚ)` is its `2`-torsion.** For `N = q² ≠ 0` every rational point of
`E_N : Y² = X³ − N²X` satisfies `2P = 0`, so `E_N(ℚ) = {0, (0, 0), (N, 0), (−N, 0)}`. -/
theorem add_self_eq_zero_of_sq {q : ℚ} (hq : q ≠ 0) (P : (curve (q ^ 2)).Point) : P + P = 0 :=
  add_self_eq_zero_of_not_isCongruent (by positivity) (not_isCongruent_sq hq) P

/-- **Fermat, as a statement about `E_1`.** Every rational point of `Y² = X³ − X` is a
`2`-torsion point. -/
theorem add_self_eq_zero_one (P : (curve 1).Point) : P + P = 0 :=
  add_self_eq_zero_of_not_isCongruent one_pos not_isCongruent_one P

/-- `E_1(ℚ)` has no point of infinite order (rank `0`, unconditionally). -/
theorem not_nonTors_one (G : (curve 1).Point) : ¬ NonTors G := fun hG ↦
  not_isCongruent_one (IsCongruent.of_nonTors one_pos hG)

/-! ### Perfect cuboids -/

/-- **A perfect cuboid gives congruent numbers.** If `a, b, c` are the edges of a perfect cuboid
with space diagonal `g`, then `abcg/2` and its squarefree part `N` (`abcg/2 = Ns²`) are congruent
numbers, and `E_N` has a rational point outside its `2`-torsion. -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.isCongruent {a b c : ℕ}
    (h : IsPerfectCuboid a b c) :
    ∃ N : ℕ, Squarefree N ∧ ∃ (g : ℕ) (s : ℚ), g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      (a * b * c * g : ℚ) / 2 = N * s ^ 2 ∧ IsCongruent N ∧
      IsCongruent ((a * b * c * g : ℚ) / 2) ∧ ∃ P : (curve N).Point, P + P ≠ 0 := by
  obtain ⟨N, hsq, g, s, hg, hs, x₁, _, _, P₁, _, _, ⟨y₁, h₁, rfl⟩, -, -, hc⟩ :=
    h.exists_config
  have hy := y_ne_zero hc.pos hc.neg₁ hc.lt₁ ((nonsingular_iff hc.pos.ne').mp h₁)
  have hP : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ ≠ 0 :=
    (some_add_self_eq_zero_iff h₁).not.mpr hy
  have hN : IsCongruent N := (isCongruent_iff_exists_add_self_ne_zero hc.pos).mpr ⟨_, hP⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := h.pos_a; have := h.pos_b; have := h.pos_c
    have hg0 : 0 < g := by
      have : 0 < g ^ 2 := by rw [hg]; positivity
      exact Nat.pos_of_ne_zero (by rintro rfl; simp at this)
    have : (0 : ℚ) < a * b * c * g / 2 := by positivity
    rw [hs] at this
    simp at this
  refine ⟨N, hsq, g, s, hg, hs, hN, ?_, _, hP⟩
  rw [hs, mul_comm]
  exact hN.mul_sq hs0

/-- The curve `E_N`, `N = sf(abcg/2)`, of a perfect cuboid has a rational point of infinite
order. -/
theorem _root_.PerfectCuboid.IsPerfectCuboid.exists_nonTors {a b c : ℕ}
    (h : IsPerfectCuboid a b c) :
    ∃ N : ℕ, Squarefree N ∧ ∃ (g : ℕ) (s : ℚ), g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 ∧
      (a * b * c * g : ℚ) / 2 = N * s ^ 2 ∧
      ∃ G : (curve N).Point, NonTors G := by
  obtain ⟨N, hsq, g, s, hg, hs, hN, -, P, hP⟩ := h.isCongruent
  have hN0 : (N : ℚ) ≠ 0 := by
    rintro h0
    obtain ⟨a, b, c, ha, hb, -, hab⟩ := hN
    rw [h0, mul_zero] at hab
    exact (mul_pos ha hb).ne' hab
  exact ⟨N, hsq, g, s, hg, hs, P, nonTors_of_add_self_ne_zero (torsionTwo hN0) hP⟩

end PerfectCuboid.CongruentRank
