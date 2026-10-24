module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Prime

/-!
# Euler bricks and the perfect cuboid problem

A *perfect cuboid* is a box whose three edges, three face diagonals and space diagonal all have
integer length. Whether one exists is a famous open problem: none is known, and nobody has
proved that none exists. This file does not settle the problem. It proves the classical partial
results about what a perfect cuboid would have to look like.

An *Euler brick* only asks for integer edges and face diagonals. Euler bricks exist, and
infinitely many of them come from Saunderson's formula (1740).

## Main results

* `eulerBrick_44_117_240`, `not_perfectCuboid_44_117_240` — the smallest Euler brick,
  found by Halcke in 1719. Its space diagonal is `√73225 ≈ 270.6`, which is not an integer.
* `saunderson` — Saunderson's parametrization: every Pythagorean triple `u² + v² = w²` gives
  the Euler brick `u·|4v² − w²|, v·|4u² − w²|, 4uvw`.
* Divisibility of the edges of every Euler brick:
  `IsEulerBrick.two_dvd_three`, `IsEulerBrick.two_dvd_four` (two edges are divisible by 3, and
  two by 4), `IsEulerBrick.nine_dvd`, `IsEulerBrick.sixteen_dvd`, `IsEulerBrick.five_dvd`,
  `IsEulerBrick.eleven_dvd` (some edge is divisible by 9, by 16, by 5 and by 11).
* Extra divisibility for a perfect cuboid: some edge is divisible by 7 and by 19
  (`IsPerfectCuboid.seven_dvd`, `IsPerfectCuboid.nineteen_dvd`); an edge or the space diagonal
  is divisible by 13 (`IsPerfectCuboid.thirteen_dvd`); and an edge or a diagonal is divisible
  by 17, 29 and 37 (`IsPerfectCuboid.seventeen_dvd`, `IsPerfectCuboid.twentynine_dvd`,
  `IsPerfectCuboid.thirtyseven_dvd`).

## How the divisibility results are proved

Most of them are congruence arguments. If `a² + b²` is a square then so is
`(a mod m)² + (b mod m)²` modulo `m`, so it is enough to check every triple of residues modulo
`m`. The check `allRes` is a `Bool` computation that the kernel runs (`decide +kernel`).
The moduli are `m = 3, 5, 7, 11, 13, 16, 17, 19, 27, 29, 37`.

Divisibility by 16 is not a congruence condition modulo any small power of 2, so
`IsEulerBrick.sixteen_dvd` is proved by descent: halve a brick with only even edges, and
otherwise use that an odd leg of a Pythagorean triple forces the other leg to be divisible by 4.
-/

@[expose] public section

namespace PerfectCuboid

/-! ### Definitions -/

/-- An Euler brick: positive integer edges `a, b, c` whose three face diagonals
`√(a² + b²)`, `√(b² + c²)`, `√(c² + a²)` are integers. -/
structure IsEulerBrick (a b c : ℕ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sq_ab : IsSquare (a ^ 2 + b ^ 2)
  sq_bc : IsSquare (b ^ 2 + c ^ 2)
  sq_ca : IsSquare (c ^ 2 + a ^ 2)

/-- A perfect cuboid: an Euler brick whose space diagonal `√(a² + b² + c²)` is an integer too.
No example is known. -/
structure IsPerfectCuboid (a b c : ℕ) : Prop extends IsEulerBrick a b c where
  sq_abc : IsSquare (a ^ 2 + b ^ 2 + c ^ 2)

/-- Halcke's brick `(44, 117, 240)`, the smallest Euler brick. Its face diagonals are
`125`, `267` and `244`. -/
theorem eulerBrick_44_117_240 : IsEulerBrick 44 117 240 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ab := ⟨125, by norm_num⟩
  sq_bc := ⟨267, by norm_num⟩
  sq_ca := ⟨244, by norm_num⟩

/-- Halcke's brick is not perfect: its space diagonal is `√73225`, and
`270² = 72900 < 73225 < 73441 = 271²`. -/
theorem not_perfectCuboid_44_117_240 : ¬ IsPerfectCuboid 44 117 240 := by
  rintro ⟨-, r, hr⟩
  have h1 : r * r < 271 * 271 := by omega
  have h2 : 270 * 270 < r * r := by omega
  have h3 : r < 271 := Nat.mul_self_lt_mul_self_iff.mp h1
  have h4 : 270 < r := Nat.mul_self_lt_mul_self_iff.mp h2
  omega

namespace IsEulerBrick

variable {a b c : ℕ}

/-- The edges of an Euler brick can be rotated. -/
theorem rotate (h : IsEulerBrick a b c) : IsEulerBrick b c a :=
  ⟨h.pos_b, h.pos_c, h.pos_a, h.sq_bc, h.sq_ca, h.sq_ab⟩

/-- Scaling an Euler brick gives an Euler brick. -/
theorem mul (h : IsEulerBrick a b c) {k : ℕ} (hk : 0 < k) :
    IsEulerBrick (k * a) (k * b) (k * c) := by
  have sq {x y : ℕ} (hxy : IsSquare (x ^ 2 + y ^ 2)) : IsSquare ((k * x) ^ 2 + (k * y) ^ 2) := by
    obtain ⟨r, hr⟩ := hxy
    exact ⟨k * r, by rw [mul_pow, mul_pow, ← mul_add, hr]; ring⟩
  exact ⟨Nat.mul_pos hk h.pos_a, Nat.mul_pos hk h.pos_b, Nat.mul_pos hk h.pos_c, sq h.sq_ab,
    sq h.sq_bc, sq h.sq_ca⟩

end IsEulerBrick

/-- There are infinitely many Euler bricks, for example the multiples of Halcke's brick. -/
theorem infinite_eulerBricks : {p : ℕ × ℕ × ℕ | IsEulerBrick p.1 p.2.1 p.2.2}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ ((k + 1) * 44, (k + 1) * 117,
    (k + 1) * 240)) (fun i j hij ↦ by simp_all) fun k ↦ ?_
  exact eulerBrick_44_117_240.mul k.succ_pos

/-! ### Saunderson's parametrization -/

/-- `x² = 3y²` has no solution in positive integers, since `√3` is irrational. -/
theorem sq_ne_three_mul_sq {x y : ℕ} (hy : 0 < y) : x ^ 2 ≠ 3 * y ^ 2 := by
  intro h
  have hirr : Irrational √((3 : ℕ) : ℝ) := Nat.Prime.irrational_sqrt (by norm_num)
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have e : ((3 : ℕ) : ℝ) = ((x : ℝ) / y) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity)]
    exact_mod_cast h.symm
  exact hirr ⟨(x : ℚ) / y, by rw [e, Real.sqrt_sq (by positivity)]; push_cast; rfl⟩

/-- **Saunderson (1740).** A Pythagorean triple `u² + v² = w²` with `u, v > 0` gives the
Euler brick with edges `u·|4v² − w²|`, `v·|4u² − w²|` and `4uvw`. Its face diagonals are `w³`,
`v·(4u² + w²)` and `u·(4v² + w²)`. For `(3, 4, 5)` it is Halcke's brick `(117, 44, 240)`. -/
theorem saunderson {u v w : ℕ} (hu : 0 < u) (hv : 0 < v) (h : u ^ 2 + v ^ 2 = w ^ 2) :
    IsEulerBrick (u * ((4 * v ^ 2 : ℤ) - w ^ 2).natAbs) (v * ((4 * u ^ 2 : ℤ) - w ^ 2).natAbs)
      (4 * u * v * w) := by
  have hz : (u : ℤ) ^ 2 + v ^ 2 = w ^ 2 := by exact_mod_cast h
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · have : 0 < u ^ 2 + v ^ 2 := by positivity
      omega
    · exact hw
  -- `4v² = w²` would mean `u² = 3v²`, and `4u² = w²` would mean `v² = 3u²`.
  have h1 : (4 * v ^ 2 : ℤ) - w ^ 2 ≠ 0 := fun h0 ↦
    sq_ne_three_mul_sq hv (x := u) (by zify; linear_combination hz - h0)
  have h2 : (4 * u ^ 2 : ℤ) - w ^ 2 ≠ 0 := fun h0 ↦
    sq_ne_three_mul_sq hu (x := v) (by zify; linear_combination hz - h0)
  -- Every identity only involves `w²`, so we may substitute `t = w² = u² + v²`.
  have key : ∀ t : ℤ, t = u ^ 2 + v ^ 2 →
      (u ^ 2 * (4 * v ^ 2 - t) ^ 2 + v ^ 2 * (4 * u ^ 2 - t) ^ 2 = t ^ 3) ∧
      (v ^ 2 * (4 * u ^ 2 - t) ^ 2 + (4 * u * v) ^ 2 * t = (v * (4 * u ^ 2 + t)) ^ 2) ∧
      ((4 * u * v) ^ 2 * t + u ^ 2 * (4 * v ^ 2 - t) ^ 2 = (u * (4 * v ^ 2 + t)) ^ 2) := by
    rintro t rfl
    refine ⟨by ring, by ring, by ring⟩
  obtain ⟨k1, k2, k3⟩ := key _ hz.symm
  refine ⟨by positivity, by positivity, by positivity, ⟨w ^ 3, ?_⟩,
    ⟨v * (4 * u ^ 2 + w ^ 2), ?_⟩, ⟨u * (4 * v ^ 2 + w ^ 2), ?_⟩⟩
  all_goals zify; simp only [mul_pow, sq_abs]
  · linear_combination k1
  · linear_combination k2
  · linear_combination k3

/-! ### Checking residues -/

/-- `n` is a square modulo `m`. -/
def IsSqMod (m n : ℕ) : Bool := (List.range m).any fun r ↦ r * r % m == n % m

/-- `P x y z` holds for all residues `x, y, z < m`. -/
def allRes (m : ℕ) (P : ℕ → ℕ → ℕ → Bool) : Bool :=
  (List.range m).all fun x ↦ (List.range m).all fun y ↦ (List.range m).all fun z ↦ P x y z

theorem isSqMod_of_isSquare {m n : ℕ} (hm : 0 < m) (h : IsSquare n) : IsSqMod m n = true := by
  obtain ⟨r, rfl⟩ := h
  simp only [IsSqMod, List.any_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨r % m, Nat.mod_lt _ hm, (Nat.mul_mod r r m).symm⟩

theorem isSqMod_mod (m n : ℕ) : IsSqMod m (n % m) = IsSqMod m n := by
  simp [IsSqMod]

theorem allRes_spec {m : ℕ} {P : ℕ → ℕ → ℕ → Bool} (h : allRes m P = true) {x y z : ℕ}
    (hx : x < m) (hy : y < m) (hz : z < m) : P x y z = true := by
  simp only [allRes, List.all_eq_true, List.mem_range] at h
  exact h x hx y hy z hz

theorem mod_sq_add_sq (m a b : ℕ) : ((a % m) ^ 2 + (b % m) ^ 2) % m = (a ^ 2 + b ^ 2) % m := by
  simp [Nat.add_mod, Nat.pow_mod]

theorem mod_sq_add_sq_add_sq (m a b c : ℕ) :
    ((a % m) ^ 2 + (b % m) ^ 2 + (c % m) ^ 2) % m = (a ^ 2 + b ^ 2 + c ^ 2) % m := by
  simp [Nat.add_mod, Nat.pow_mod]

theorem isSqMod_res {m a b : ℕ} (hm : 0 < m) (h : IsSquare (a ^ 2 + b ^ 2)) :
    IsSqMod m ((a % m) ^ 2 + (b % m) ^ 2) = true := by
  rw [← isSqMod_mod, mod_sq_add_sq, isSqMod_mod]
  exact isSqMod_of_isSquare hm h

/-- The residues of an Euler brick's edges modulo `m` pass the face-diagonal test. So a property
of residues that holds whenever the test passes holds for every Euler brick. -/
theorem IsEulerBrick.residues {a b c m : ℕ} (h : IsEulerBrick a b c) (hm : 0 < m)
    {P : ℕ → ℕ → ℕ → Bool}
    (hP : allRes m (fun x y z ↦ !(IsSqMod m (x ^ 2 + y ^ 2) && IsSqMod m (y ^ 2 + z ^ 2) &&
      IsSqMod m (z ^ 2 + x ^ 2)) || P x y z) = true) :
    P (a % m) (b % m) (c % m) = true := by
  have := allRes_spec hP (Nat.mod_lt a hm) (Nat.mod_lt b hm) (Nat.mod_lt c hm)
  simpa [isSqMod_res hm h.sq_ab, isSqMod_res hm h.sq_bc, isSqMod_res hm h.sq_ca]
    using this

/-- The same as `IsEulerBrick.residues`, with the space-diagonal test added. -/
theorem IsPerfectCuboid.residues {a b c m : ℕ} (h : IsPerfectCuboid a b c) (hm : 0 < m)
    {P : ℕ → ℕ → ℕ → Bool}
    (hP : allRes m (fun x y z ↦ !(IsSqMod m (x ^ 2 + y ^ 2) && IsSqMod m (y ^ 2 + z ^ 2) &&
      IsSqMod m (z ^ 2 + x ^ 2) && IsSqMod m (x ^ 2 + y ^ 2 + z ^ 2)) || P x y z) = true) :
    P (a % m) (b % m) (c % m) = true := by
  have := allRes_spec hP (Nat.mod_lt a hm) (Nat.mod_lt b hm) (Nat.mod_lt c hm)
  have h4 : IsSqMod m ((a % m) ^ 2 + (b % m) ^ 2 + (c % m) ^ 2) = true := by
    rw [← isSqMod_mod, mod_sq_add_sq_add_sq, isSqMod_mod]
    exact isSqMod_of_isSquare hm h.sq_abc
  simpa [isSqMod_res hm h.sq_ab, isSqMod_res hm h.sq_bc, isSqMod_res hm h.sq_ca, h4]
    using this

/-- For `q ∣ m`, divisibility by `q` can be read off the residue modulo `m`. -/
theorem mod_mod_eq_zero_iff {a m q : ℕ} (hq : q ∣ m) : a % m % q = 0 ↔ q ∣ a := by
  rw [Nat.mod_mod_of_dvd a hq, Nat.dvd_iff_mod_eq_zero]

/-! ### Divisibility of the edges of an Euler brick -/

namespace IsEulerBrick

variable {a b c : ℕ}

/-- At least two edges of an Euler brick are divisible by 3. -/
theorem two_dvd_three (h : IsEulerBrick a b c) :
    (3 ∣ a ∧ 3 ∣ b) ∨ (3 ∣ b ∧ 3 ∣ c) ∨ (3 ∣ c ∧ 3 ∣ a) := by
  have := h.residues (m := 3) (by norm_num)
    (P := fun x y z ↦ (x % 3 == 0 && y % 3 == 0) || (y % 3 == 0 && z % 3 == 0) ||
      (z % 3 == 0 && x % 3 == 0)) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (dvd_refl 3), or_assoc, Nat.dvd_iff_mod_eq_zero]
    using this

/-- At least two edges of an Euler brick are divisible by 4. -/
theorem two_dvd_four (h : IsEulerBrick a b c) :
    (4 ∣ a ∧ 4 ∣ b) ∨ (4 ∣ b ∧ 4 ∣ c) ∨ (4 ∣ c ∧ 4 ∣ a) := by
  have := h.residues (m := 16) (by norm_num)
    (P := fun x y z ↦ (x % 4 == 0 && y % 4 == 0) || (y % 4 == 0 && z % 4 == 0) ||
      (z % 4 == 0 && x % 4 == 0)) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (show 4 ∣ 16 by norm_num), or_assoc, Nat.dvd_iff_mod_eq_zero]
    using this

/-- Some edge of an Euler brick is divisible by 9. -/
theorem nine_dvd (h : IsEulerBrick a b c) : 9 ∣ a ∨ 9 ∣ b ∨ 9 ∣ c := by
  have := h.residues (m := 27) (by norm_num)
    (P := fun x y z ↦ x % 9 == 0 || y % 9 == 0 || z % 9 == 0) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (show 9 ∣ 27 by norm_num), or_assoc, Nat.dvd_iff_mod_eq_zero]
    using this

/-- Some edge of an Euler brick is divisible by 5. -/
theorem five_dvd (h : IsEulerBrick a b c) : 5 ∣ a ∨ 5 ∣ b ∨ 5 ∣ c := by
  have := h.residues (m := 5) (by norm_num)
    (P := fun x y z ↦ x % 5 == 0 || y % 5 == 0 || z % 5 == 0) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (dvd_refl 5), or_assoc, Nat.dvd_iff_mod_eq_zero]
    using this

/-- Some edge of an Euler brick is divisible by 11. -/
theorem eleven_dvd (h : IsEulerBrick a b c) : 11 ∣ a ∨ 11 ∣ b ∨ 11 ∣ c := by
  have := h.residues (m := 11) (by norm_num)
    (P := fun x y z ↦ x % 11 == 0 || y % 11 == 0 || z % 11 == 0) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (dvd_refl 11), or_assoc, Nat.dvd_iff_mod_eq_zero]
    using this

end IsEulerBrick

/-! ### Divisibility by 16 -/

/-- If `x² + y²` is a square and `x` is odd, then `4 ∣ y`. -/
theorem four_dvd_of_odd {x y : ℕ} (h : IsSquare (x ^ 2 + y ^ 2)) (hx : ¬ 2 ∣ x) : 4 ∣ y := by
  have hres := isSqMod_res (m := 8) (by norm_num) h
  have := allRes_spec (m := 8)
    (P := fun x y _ ↦ !IsSqMod 8 (x ^ 2 + y ^ 2) || x % 2 == 0 || y % 4 == 0)
    (by decide +kernel) (Nat.mod_lt x (by norm_num)) (Nat.mod_lt y (by norm_num))
    (z := 0) (by norm_num)
  simp only [hres, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
    mod_mod_eq_zero_iff (show 2 ∣ 8 by norm_num), mod_mod_eq_zero_iff (show 4 ∣ 8 by norm_num)]
    at this
  tauto

/-- Halving both legs: if `(2x)² + (2y)²` is a square then so is `x² + y²`. -/
theorem isSquare_half {x y : ℕ} (h : IsSquare ((2 * x) ^ 2 + (2 * y) ^ 2)) :
    IsSquare (x ^ 2 + y ^ 2) := by
  obtain ⟨r, hr⟩ := h
  have h2 : 2 ∣ r * r := ⟨2 * (x ^ 2 + y ^ 2), by rw [← hr]; ring⟩
  obtain ⟨s, rfl⟩ := (Nat.prime_two.dvd_mul.mp h2).elim id id
  exact ⟨s, by nlinarith⟩

/-- If `x² + y²` is a square and `4 ∣ x`, `4 ∣ y`, then `16 ∣ x` or `16 ∣ y`. -/
theorem sixteen_dvd_of_four_dvd {x y : ℕ} (h : IsSquare (x ^ 2 + y ^ 2)) (hx : 4 ∣ x)
    (hy : 4 ∣ y) : 16 ∣ x ∨ 16 ∣ y := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  have h1 : IsSquare (x ^ 2 + y ^ 2) := isSquare_half (isSquare_half (by ring_nf at h ⊢; exact h))
  by_cases ex : 2 ∣ x
  · by_cases ey : 2 ∣ y
    · obtain ⟨x, rfl⟩ := ex
      obtain ⟨y, rfl⟩ := ey
      have h2 := isSquare_half h1
      by_cases ex' : 2 ∣ x
      · left
        obtain ⟨x, rfl⟩ := ex'
        exact ⟨x, by ring⟩
      · right
        obtain ⟨y, rfl⟩ := four_dvd_of_odd h2 ex'
        exact ⟨2 * y, by ring⟩
    · left
      obtain ⟨x, rfl⟩ := four_dvd_of_odd (by rwa [add_comm]) ey
      exact ⟨x, by ring⟩
  · right
    obtain ⟨y, rfl⟩ := four_dvd_of_odd h1 ex
    exact ⟨y, by ring⟩

/-- Some edge of an Euler brick is divisible by 16. -/
theorem IsEulerBrick.sixteen_dvd {a b c : ℕ} (h : IsEulerBrick a b c) :
    16 ∣ a ∨ 16 ∣ b ∨ 16 ∣ c := by
  induction a using Nat.strong_induction_on generalizing b c with
  | _ a ih =>
  by_cases ha : 2 ∣ a
  · by_cases hb : 2 ∣ b
    · by_cases hc : 2 ∣ c
      · -- All edges are even: halve the brick.
        obtain ⟨a, rfl⟩ := ha
        obtain ⟨b, rfl⟩ := hb
        obtain ⟨c, rfl⟩ := hc
        have h' : IsEulerBrick a b c :=
          ⟨by have := h.pos_a; omega, by have := h.pos_b; omega, by have := h.pos_c; omega,
            isSquare_half h.sq_ab, isSquare_half h.sq_bc, isSquare_half h.sq_ca⟩
        have := ih a (by have := h'.pos_a; omega) h'
        rcases this with h1 | h1 | h1
        · exact Or.inl (dvd_mul_of_dvd_right h1 2)
        · exact Or.inr (Or.inl (dvd_mul_of_dvd_right h1 2))
        · exact Or.inr (Or.inr (dvd_mul_of_dvd_right h1 2))
      · -- `c` is odd, so `4 ∣ a` and `4 ∣ b`.
        have := sixteen_dvd_of_four_dvd h.sq_ab (four_dvd_of_odd h.sq_ca hc)
          (four_dvd_of_odd (by rw [add_comm]; exact h.sq_bc) hc)
        tauto
    · -- `b` is odd, so `4 ∣ c` and `4 ∣ a`.
      have := sixteen_dvd_of_four_dvd h.sq_ca (four_dvd_of_odd h.sq_bc hb)
        (four_dvd_of_odd (by rw [add_comm]; exact h.sq_ab) hb)
      tauto
  · -- `a` is odd, so `4 ∣ b` and `4 ∣ c`.
    have := sixteen_dvd_of_four_dvd h.sq_bc (four_dvd_of_odd h.sq_ab ha)
      (four_dvd_of_odd (by rw [add_comm]; exact h.sq_ca) ha)
    tauto

/-! ### Extra divisibility for a perfect cuboid -/

namespace IsPerfectCuboid

variable {a b c : ℕ}

/-- Some edge of a perfect cuboid is divisible by 7. (This fails for Euler bricks:
Halcke's brick `(44, 117, 240)` has none.) -/
theorem seven_dvd (h : IsPerfectCuboid a b c) : 7 ∣ a ∨ 7 ∣ b ∨ 7 ∣ c := by
  have := h.residues (m := 7) (by norm_num)
    (P := fun x y z ↦ x % 7 == 0 || y % 7 == 0 || z % 7 == 0) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (dvd_refl 7), or_assoc, Nat.dvd_iff_mod_eq_zero]
    using this

/-- Some edge of a perfect cuboid is divisible by 19. -/
theorem nineteen_dvd (h : IsPerfectCuboid a b c) : 19 ∣ a ∨ 19 ∣ b ∨ 19 ∣ c := by
  have := h.residues (m := 19) (by norm_num)
    (P := fun x y z ↦ x % 19 == 0 || y % 19 == 0 || z % 19 == 0) (by decide +kernel)
  simpa [mod_mod_eq_zero_iff (dvd_refl 19), or_assoc, Nat.dvd_iff_mod_eq_zero]
    using this

/-- For a prime `p`, `p` divides a diagonal `d` with `d² = s` as soon as `p ∣ s`. -/
theorem dvd_of_sq_eq {p s d : ℕ} (hp : p.Prime) (hd : s = d ^ 2) (h : s % p = 0) : p ∣ d :=
  hp.dvd_of_dvd_pow (n := 2) (hd ▸ Nat.dvd_of_mod_eq_zero h)

/-- An edge or the space diagonal `g` of a perfect cuboid is divisible by 13. -/
theorem thirteen_dvd (h : IsPerfectCuboid a b c) {g : ℕ} (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    13 ∣ a ∨ 13 ∣ b ∨ 13 ∣ c ∨ 13 ∣ g := by
  have := h.residues (m := 13) (by norm_num)
    (P := fun x y z ↦ x % 13 == 0 || y % 13 == 0 || z % 13 == 0 ||
      (x ^ 2 + y ^ 2 + z ^ 2) % 13 == 0) (by decide +kernel)
  simp only [Bool.or_eq_true, beq_iff_eq, mod_mod_eq_zero_iff (dvd_refl 13),
    mod_sq_add_sq_add_sq] at this
  rcases this with ((h1 | h1) | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (dvd_of_sq_eq (by norm_num) hg h1)))

/-- The common shape of the results for 17, 29 and 37: `p` divides an edge, a face diagonal
`d, e, f` or the space diagonal `g`. -/
theorem dvd_of_residues {p : ℕ} (hp : p.Prime) (h : IsPerfectCuboid a b c) {d e f g : ℕ}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : b ^ 2 + c ^ 2 = e ^ 2) (hf : c ^ 2 + a ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2)
    (hP : allRes p (fun x y z ↦ !(IsSqMod p (x ^ 2 + y ^ 2) && IsSqMod p (y ^ 2 + z ^ 2) &&
      IsSqMod p (z ^ 2 + x ^ 2) && IsSqMod p (x ^ 2 + y ^ 2 + z ^ 2)) ||
      (x % p == 0 || y % p == 0 || z % p == 0 || (x ^ 2 + y ^ 2) % p == 0 ||
        (y ^ 2 + z ^ 2) % p == 0 || (z ^ 2 + x ^ 2) % p == 0 || (x ^ 2 + y ^ 2 + z ^ 2) % p == 0))
        = true) :
    p ∣ a ∨ p ∣ b ∨ p ∣ c ∨ p ∣ d ∨ p ∣ e ∨ p ∣ f ∨ p ∣ g := by
  have := h.residues hp.pos hP
  simp only [Bool.or_eq_true, beq_iff_eq, mod_mod_eq_zero_iff (dvd_refl p), mod_sq_add_sq,
    mod_sq_add_sq_add_sq] at this
  rcases this with ((((((h1 | h1) | h1) | h1) | h1) | h1) | h1)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (dvd_of_sq_eq hp hd h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (dvd_of_sq_eq hp he h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (dvd_of_sq_eq hp hf h1))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (dvd_of_sq_eq hp hg h1))))))

/-- An edge or a diagonal of a perfect cuboid is divisible by 17. -/
theorem seventeen_dvd (h : IsPerfectCuboid a b c) {d e f g : ℕ}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : b ^ 2 + c ^ 2 = e ^ 2) (hf : c ^ 2 + a ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    17 ∣ a ∨ 17 ∣ b ∨ 17 ∣ c ∨ 17 ∣ d ∨ 17 ∣ e ∨ 17 ∣ f ∨ 17 ∣ g :=
  dvd_of_residues (by norm_num) h hd he hf hg (by decide +kernel)

/-- An edge or a diagonal of a perfect cuboid is divisible by 29. -/
theorem twentynine_dvd (h : IsPerfectCuboid a b c) {d e f g : ℕ}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : b ^ 2 + c ^ 2 = e ^ 2) (hf : c ^ 2 + a ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    29 ∣ a ∨ 29 ∣ b ∨ 29 ∣ c ∨ 29 ∣ d ∨ 29 ∣ e ∨ 29 ∣ f ∨ 29 ∣ g :=
  dvd_of_residues (by norm_num) h hd he hf hg (by decide +kernel)

/-- An edge or a diagonal of a perfect cuboid is divisible by 37. -/
theorem thirtyseven_dvd (h : IsPerfectCuboid a b c) {d e f g : ℕ}
    (hd : a ^ 2 + b ^ 2 = d ^ 2) (he : b ^ 2 + c ^ 2 = e ^ 2) (hf : c ^ 2 + a ^ 2 = f ^ 2)
    (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) :
    37 ∣ a ∨ 37 ∣ b ∨ 37 ∣ c ∨ 37 ∣ d ∨ 37 ∣ e ∨ 37 ∣ f ∨ 37 ∣ g :=
  dvd_of_residues (by norm_num) h hd he hf hg (by decide +kernel)

end IsPerfectCuboid

end PerfectCuboid
