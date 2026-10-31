module

public import Mathlib
public import LeanPlayground.PerfectCuboid.Basic
public import LeanPlayground.PerfectCuboid.EdgePrimePower
public import LeanPlayground.PerfectCuboid.PellLeg

/-!
# Face cuboids: the two edges next to the irrational face diagonal are not prime powers

A *face cuboid* (of type `d`) is a box `(a, b, c)` with positive integer edges such that
`a² + c²`, `b² + c²` and `a² + b² + c²` are squares, while the face diagonal `√(a² + b²)` need not
be an integer. Every perfect cuboid is one (`IsPerfectCuboid.toIsFaceCuboid`), and face cuboids
exist: `(153, 672, 104)` with `e = 185`, `f = 680`, `g = 697` (`isFaceCuboid_153_672_104`).

## Main results

* `two_triangles_prime_pow_leg` (**Theorem P′**): if `p` is prime and `(p^k, y₁, z₁)`,
  `(p^k, y₂, z₂)` are integer right triangles, then `y₂² − y₁²` is not a positive square, i.e.
  there is no `w > 0` with `y₁² + w² = y₂²` (`y₁ > 0`).
* `IsFaceCuboid.edge_ne_prime_pow_a`, `IsFaceCuboid.edge_ne_prime_pow_b` (**C1**): in a face
  cuboid, neither `a` nor `b` is a prime power.
* `IsPerfectCuboid.edge_ne_prime_pow_of_faceCuboid` (**C2**): Korec's theorem (no edge of a
  perfect cuboid is a prime power) re-derived from C1,
  using only two of the three right triangles through the edge.

## Proof of Theorem P′

`(p^k)² + y² = z²` forces `2y = p^i (p^(2(k−i)) − 1)` with `i < k` (`leg_of_prime_pow`). For two
such legs with exponents `i > j` (the larger leg has the smaller exponent) put `δ = i − j ≥ 1`,
`v = k − i ≥ 1`. Then
`(2y₂)² − (2y₁)² = p^(2j) (p^(2δ) − 1)(p^(2(2v+δ)) − 1)`,
so if `y₂² − y₁² = w²` then `p^j ∣ 2w` and `(p^(2δ) − 1)(p^(2(2v+δ)) − 1)` is a square, which
contradicts Theorem P (`PellLeg.pow_sub_one_mul_pow_sub_one_not_square`) as `δ ≠ 2v + δ`.

For C1, `a` is the common leg of `(a, c, e)` and `(a, f, g)`, and `f² − c² = b²`.

## Sharpness

The face cuboid `(153, 672, 104)` has `a = 153 = 3²·17`: the bound "not a prime power" cannot be
improved to "not a product of two prime powers" for face cuboids.
-/

@[expose] public section

namespace PerfectCuboid

/-- A *face cuboid* (of type `d`): positive integer edges with `a² + c²`, `b² + c²` and
`a² + b² + c²` squares; the face diagonal `√(a² + b²)` may be irrational. -/
structure IsFaceCuboid (a b c : ℕ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sq_ac : IsSquare (a ^ 2 + c ^ 2)
  sq_bc : IsSquare (b ^ 2 + c ^ 2)
  sq_abc : IsSquare (a ^ 2 + b ^ 2 + c ^ 2)

/-- Every perfect cuboid is a face cuboid. -/
theorem IsPerfectCuboid.toIsFaceCuboid {a b c : ℕ} (h : IsPerfectCuboid a b c) :
    IsFaceCuboid a b c where
  pos_a := h.pos_a
  pos_b := h.pos_b
  pos_c := h.pos_c
  sq_ac := by have := h.sq_ca; rwa [add_comm] at this
  sq_bc := h.sq_bc
  sq_abc := h.sq_abc

/-- The roles of `a` and `b` in a face cuboid are symmetric. -/
theorem IsFaceCuboid.swap {a b c : ℕ} (h : IsFaceCuboid a b c) : IsFaceCuboid b a c where
  pos_a := h.pos_b
  pos_b := h.pos_a
  pos_c := h.pos_c
  sq_ac := h.sq_bc
  sq_bc := h.sq_ac
  sq_abc := by have := h.sq_abc; rwa [show a ^ 2 + b ^ 2 + c ^ 2 = b ^ 2 + a ^ 2 + c ^ 2 by ring]
    at this

/-- A face cuboid that is not a perfect cuboid: `153² + 104² = 185²`, `672² + 104² = 680²`,
`153² + 672² + 104² = 697²`, but `153² + 672² = 474993` is not a square. -/
theorem isFaceCuboid_153_672_104 : IsFaceCuboid 153 672 104 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ac := ⟨185, by norm_num⟩
  sq_bc := ⟨680, by norm_num⟩
  sq_abc := ⟨697, by norm_num⟩

theorem not_isSquare_153_672 : ¬ IsSquare (153 ^ 2 + 672 ^ 2) := by
  rintro ⟨r, hr⟩
  have h1 : r < 690 := by nlinarith
  interval_cases r <;> omega

/-- The leg formula in integer form: `2y = p^i (p^(2(k−i)) − 1)` with `i < k`. -/
theorem leg_formula_int {p k y z : ℕ} (hp : p.Prime) (hy : 0 < y)
    (h : (p ^ k) ^ 2 + y ^ 2 = z ^ 2) :
    ∃ i < k, (2 * y : ℤ) = (p : ℤ) ^ i * ((p : ℤ) ^ (2 * (k - i)) - 1) := by
  obtain ⟨i, hi, B, hB, hB1⟩ := leg_of_prime_pow hp hy h
  refine ⟨i, hi, ?_⟩
  have e1 : (B : ℤ) = (p : ℤ) ^ (2 * (k - i)) - 1 := by
    have := congrArg (Nat.cast (R := ℤ)) hB1; push_cast at this; linarith
  have e2 := congrArg (Nat.cast (R := ℤ)) hB
  push_cast at e2
  rw [e2, e1]

/-- **Theorem P′.** Two integer right triangles with the same prime-power leg `p^k`: the
difference of the squares of their other legs is never a positive square. -/
theorem two_triangles_prime_pow_leg {p k y₁ z₁ y₂ z₂ w : ℕ} (hp : p.Prime)
    (h₁ : (p ^ k) ^ 2 + y₁ ^ 2 = z₁ ^ 2) (h₂ : (p ^ k) ^ 2 + y₂ ^ 2 = z₂ ^ 2)
    (hy₁ : 0 < y₁) (hw : 0 < w) (h : y₁ ^ 2 + w ^ 2 = y₂ ^ 2) : False := by
  have hy12 : y₁ < y₂ := by
    have : y₁ ^ 2 < y₂ ^ 2 := by rw [← h]; have := pow_pos hw 2; omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hy₂ : 0 < y₂ := by omega
  obtain ⟨i, hik, e1⟩ := leg_formula_int hp hy₁ h₁
  obtain ⟨j, hjk, e2⟩ := leg_formula_int hp hy₂ h₂
  have hP : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  set P : ℤ := (p : ℤ) with hPdef
  rcases lt_trichotomy i j with hij | rfl | hij
  · -- `i < j` would give `y₁ ≥ y₂`
    obtain ⟨δ, rfl⟩ : ∃ δ, j = i + δ := ⟨j - i, by omega⟩
    have hk : k - i = (k - (i + δ)) + δ := by omega
    rw [hk] at e1
    set v := k - (i + δ)
    have hD : 1 ≤ P ^ δ := one_le_pow₀ (by linarith)
    have hA : 1 ≤ P ^ i := one_le_pow₀ (by linarith)
    have hV : 0 ≤ P ^ (2 * v) := by positivity
    have key : (2 * y₁ : ℤ) - 2 * y₂ = P ^ i * (P ^ δ - 1) * (P ^ δ * P ^ (2 * v) + 1) := by
      rw [e1, e2]; ring
    have : (0 : ℤ) ≤ P ^ i * (P ^ δ - 1) * (P ^ δ * P ^ (2 * v) + 1) := by
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith)); positivity
    have : (y₂ : ℤ) < y₁ + 1 := by linarith
    omega
  · have : (y₁ : ℤ) = y₂ := by linarith
    omega
  · -- `j < i`: reduce to Theorem P
    obtain ⟨δ, rfl⟩ : ∃ δ, i = j + δ := ⟨i - j, by omega⟩
    have hδ : 0 < δ := by omega
    set v := k - (j + δ) with hv
    have hv0 : 0 < v := by omega
    have hk : k - j = v + δ := by omega
    rw [hk] at e2
    have hwz : ((2 * w : ℕ) : ℤ) ^ 2 =
        P ^ (2 * j) * ((P ^ (2 * δ) - 1) * (P ^ (2 * (2 * v + δ)) - 1)) := by
      have : (2 * w : ℤ) ^ 2 = (2 * y₂ : ℤ) ^ 2 - (2 * y₁ : ℤ) ^ 2 := by
        have := congrArg (Nat.cast (R := ℤ)) h; push_cast at this; linarith
      push_cast; rw [this, e1, e2]; ring
    set X : ℕ := (p ^ (2 * δ) - 1) * (p ^ (2 * (2 * v + δ)) - 1) with hX
    have hXz : (X : ℤ) = (P ^ (2 * δ) - 1) * (P ^ (2 * (2 * v + δ)) - 1) := by
      have h1 : 1 ≤ p ^ (2 * δ) := Nat.one_le_pow _ _ hp.pos
      have h2 : 1 ≤ p ^ (2 * (2 * v + δ)) := Nat.one_le_pow _ _ hp.pos
      rw [hX]; push_cast [h1, h2]; ring
    have hwN : (2 * w) ^ 2 = p ^ (2 * j) * X := by
      have : (((2 * w) ^ 2 : ℕ) : ℤ) = ((p ^ (2 * j) * X : ℕ) : ℤ) := by
        push_cast; rw [hXz]; push_cast at hwz; exact hwz
      exact_mod_cast this
    have hdvd : p ^ j ∣ 2 * w := by
      have : (p ^ j) ^ 2 ∣ (2 * w) ^ 2 := ⟨X, by rw [hwN, ← pow_mul, mul_comm j]⟩
      exact (Nat.pow_dvd_pow_iff two_ne_zero).1 this
    obtain ⟨z, hz⟩ := hdvd
    have hXsq : X = z ^ 2 := by
      rw [hz, mul_pow, ← pow_mul, mul_comm j] at hwN
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) hwN).symm
    exact PellLeg.pow_sub_one_mul_pow_sub_one_not_square hp.two_le hδ (by omega)
      (by omega : δ ≠ 2 * v + δ) ⟨z, by rw [← hX, hXsq, sq]⟩

/-- **C1.** In a face cuboid the edge `a` (adjacent to the possibly irrational face diagonal) is
not a prime power. -/
theorem IsFaceCuboid.edge_ne_prime_pow_a {a b c : ℕ} (h : IsFaceCuboid a b c) {p k : ℕ}
    (hp : p.Prime) : a ≠ p ^ k := by
  rintro rfl
  obtain ⟨e, he⟩ := h.sq_ac
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  exact two_triangles_prime_pow_leg (y₁ := c) (z₁ := e) (y₂ := f) (z₂ := g) (w := b) hp
    (by rw [he]; ring) (by rw [sq f, ← hf, sq g, ← hg]; ring) h.pos_c h.pos_b
    (by rw [sq f, ← hf]; ring)

/-- **C1.** In a face cuboid the edge `b` is not a prime power. -/
theorem IsFaceCuboid.edge_ne_prime_pow_b {a b c : ℕ} (h : IsFaceCuboid a b c) {p k : ℕ}
    (hp : p.Prime) : b ≠ p ^ k :=
  h.swap.edge_ne_prime_pow_a hp

/-- **C2.** Korec's theorem for perfect cuboids, re-derived from C1: no edge is a prime power.
Each edge is adjacent to two faces; declaring either face diagonal "irrational" makes it an edge
`a` of a face cuboid. -/
theorem IsPerfectCuboid.edge_ne_prime_pow_of_faceCuboid {a b c : ℕ}
    (h : IsPerfectCuboid a b c) {p k : ℕ} (hp : p.Prime) : a ≠ p ^ k ∧ b ≠ p ^ k ∧ c ≠ p ^ k := by
  have hc : IsFaceCuboid c a b :=
    { pos_a := h.pos_c, pos_b := h.pos_a, pos_c := h.pos_b
      sq_ac := by have := h.sq_bc; rwa [add_comm] at this
      sq_bc := h.sq_ab
      sq_abc := by
        have := h.sq_abc; rwa [show a ^ 2 + b ^ 2 + c ^ 2 = c ^ 2 + a ^ 2 + b ^ 2 by ring]
          at this }
  exact ⟨h.toIsFaceCuboid.edge_ne_prime_pow_a hp, h.toIsFaceCuboid.edge_ne_prime_pow_b hp,
    hc.edge_ne_prime_pow_a hp⟩

end PerfectCuboid
