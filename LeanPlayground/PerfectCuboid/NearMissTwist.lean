module

public import LeanPlayground.PerfectCuboid.FaceCuboidLeech

/-!
# Twists of near-miss cuboids

For positive integers `a, b, c` the *twist* of one of the four sums `a² + b²`, `a² + c²`,
`b² + c²`, `a² + b² + c²` is its class modulo squares, i.e. its squarefree part `s`
(`s · r² = sum`, `s` squarefree). A perfect cuboid has all four twists trivial; an Euler brick
has trivial face twists and a possibly nontrivial space twist; a face cuboid
(`IsFaceCuboid a b c`) has a possibly nontrivial twist of the face sum `a² + b²`.

## Main results

* `isEulerBrick_495_4888_8160`, `prime_313921`, `sum_sq_495_4888_8160`: the space twist of a
  primitive Euler brick can be a prime: `495² + 4888² + 8160² = 313921 · 17²` with `313921`
  prime.
* `isEulerBrick_429_880_2340`, `face_diagonal_429_880_2340`: a face diagonal of an Euler brick
  can be a perfect square, `880² + 2340² = 2500² = (50²)²`.
* `IsEulerBrick.sum_sq_mod_twentyfour`, `IsEulerBrick.space_twist_mod_24`: for a primitive
  Euler brick `a² + b² + c² ≡ 1 (mod 24)`, hence its space twist is `≡ 1 (mod 24)`.
  (Numerically, the space twists of the 87 primitive bricks with edges `≤ 2·10⁵` are all
  `≡ 1 (mod 24)`; this file proves it in general.)
* `IsFaceCuboid.sq_add_sq_mod_eight`, `IsFaceCuboid.twist_mod_eight`: for a primitive face
  cuboid either `a² + b² ≡ 1 (mod 8)` (so its twist is `≡ 1 (mod 8)`), or `c` is the odd edge
  and `4 ∣ a`, `4 ∣ b`. (In the second case the twist can be `≡ 2, 5 (mod 8)`, as the face
  cuboid data with common leg `c < 30000` show.)
* `NearMissTwist.derived_identity`, `NearMissTwist.isSquare_derived_iff`:
  `(def)² + (abc)² = (a² + b² + c²)((bc)² + (ca)² + (ab)²)`, so the space twist of the derived
  brick `(bc, ca, ab)` is the twist of `(def)² + (abc)²` times the space twist of `(a, b, c)`.

Data (round 13): the space twists of the 87 primitive bricks with edges `≤ 2·10⁵` are pairwise
distinct, all `≡ 1 (mod 24)`, and four of them are prime: `313921` for `(495, 4888, 8160)`,
`86161` for `(828, 2035, 3120)`, `842209` for `(10296, 11753, 16800)`, `20815441` for
`(117469, 161040, 194220)`.
-/

@[expose] public section

namespace PerfectCuboid

namespace NearMissTwist

/-- `x² mod 8` for `4 ∣ x`. -/
theorem sq_mod_eight_of_four_dvd {x : ℕ} (h : 4 ∣ x) : x ^ 2 % 8 = 0 := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.mul_pow, Nat.mul_mod]
  norm_num

/-- `x² mod 8` for odd `x`. -/
theorem sq_mod_eight_of_odd {x : ℕ} (h : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  rw [Nat.pow_mod]
  have : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h8 : x % 8 % 2 = 1 := by rw [Nat.mod_mod_of_dvd x (by norm_num : 2 ∣ 8)]; exact h
  interval_cases hx : x % 8 <;> simp_all

/-- `x² mod 3` for `3 ∣ x`. -/
theorem sq_mod_three_of_dvd {x : ℕ} (h : 3 ∣ x) : x ^ 2 % 3 = 0 :=
  Nat.mod_eq_zero_of_dvd (dvd_pow h two_ne_zero)

/-- `x² mod 3` for `3 ∤ x`. -/
theorem sq_mod_three_of_not_dvd {x : ℕ} (h : ¬ 3 ∣ x) : x ^ 2 % 3 = 1 := by
  rw [Nat.pow_mod]
  have : x % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h3 : x % 3 ≠ 0 := fun h' ↦ h (Nat.dvd_of_mod_eq_zero h')
  interval_cases hx : x % 3 <;> simp_all

/-- A number with `x ≡ 1 (mod 2)` and `3 ∤ x` has `x² ≡ 1 (mod 24)`. -/
theorem sq_mod_twentyfour {x : ℕ} (h2 : x % 2 = 1) (h3 : x % 3 ≠ 0) : x ^ 2 % 24 = 1 := by
  rw [Nat.pow_mod]
  have : x % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have h2' : x % 24 % 2 = 1 := by rw [Nat.mod_mod_of_dvd x (by norm_num : 2 ∣ 24)]; exact h2
  have h3' : x % 24 % 3 ≠ 0 := by rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 24)]; exact h3
  interval_cases hx : x % 24 <;> simp_all

/-- If `s · r² = N` with `N ≡ 1` and `r² ≡ 1 (mod m)`, then `s ≡ 1 (mod m)`. -/
theorem twist_of_mod {s r N m : ℕ} (hr : s * r ^ 2 = N) (hN : N % m = 1)
    (hr2 : r ^ 2 % m = 1) : s % m = 1 := by
  have h := congrArg (· % m) hr
  rw [Nat.mul_mod, hr2, mul_one, Nat.mod_mod, hN] at h
  exact h

end NearMissTwist

open NearMissTwist

/-! ### Examples -/

/-- `(495, 4888, 8160)` is an Euler brick whose space-diagonal sum is `313921 · 17²` with
`313921` prime: the squarefree twist of a brick can be prime. Face diagonals:
`4913 = 17³`, `9512`, `8175`. -/
theorem isEulerBrick_495_4888_8160 : IsEulerBrick 495 4888 8160 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ab := ⟨4913, by norm_num⟩
  sq_bc := ⟨9512, by norm_num⟩
  sq_ca := ⟨8175, by norm_num⟩

/-- The space twist `313921` of the brick `(495, 4888, 8160)` is prime. -/
theorem prime_313921 : Nat.Prime 313921 := by norm_num

theorem sum_sq_495_4888_8160 : 495 ^ 2 + 4888 ^ 2 + 8160 ^ 2 = 313921 * 17 ^ 2 := by norm_num

/-- `(429, 880, 2340)` is an Euler brick with the square face diagonal
`880² + 2340² = 2500² = 50⁴`. Face diagonals: `979`, `2500`, `2379`. -/
theorem isEulerBrick_429_880_2340 : IsEulerBrick 429 880 2340 where
  pos_a := by norm_num
  pos_b := by norm_num
  pos_c := by norm_num
  sq_ab := ⟨979, by norm_num⟩
  sq_bc := ⟨2500, by norm_num⟩
  sq_ca := ⟨2379, by norm_num⟩

theorem face_diagonal_429_880_2340 : 880 ^ 2 + 2340 ^ 2 = (50 ^ 2) ^ 2 := by norm_num

/-! ### The space twist of a primitive Euler brick -/

/-- Space-diagonal sum of a primitive Euler brick is `≡ 1 (mod 24)`: one odd edge, two edges
divisible by `4`, and exactly two edges divisible by `3`. -/
theorem IsEulerBrick.sum_sq_mod_twentyfour {a b c : ℕ} (h : IsEulerBrick a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) : (a ^ 2 + b ^ 2 + c ^ 2) % 24 = 1 := by
  have h8 : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = 1 := by
    rcases h.two_dvd_four with ⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨hc, ha⟩
    · have hc : c % 2 = 1 := by
        by_contra hc
        have := Nat.dvd_gcd (dvd_trans (by norm_num : 2 ∣ 4) ha)
          (Nat.dvd_gcd (dvd_trans (by norm_num : 2 ∣ 4) hb)
            (Nat.dvd_of_mod_eq_zero (by omega : c % 2 = 0)))
        rw [hp] at this; omega
      have := sq_mod_eight_of_four_dvd ha; have := sq_mod_eight_of_four_dvd hb
      have := sq_mod_eight_of_odd hc; omega
    · have ha : a % 2 = 1 := by
        by_contra ha
        have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero (by omega : a % 2 = 0))
          (Nat.dvd_gcd (dvd_trans (by norm_num : 2 ∣ 4) hb) (dvd_trans (by norm_num : 2 ∣ 4) hc))
        rw [hp] at this; omega
      have := sq_mod_eight_of_four_dvd hc; have := sq_mod_eight_of_four_dvd hb
      have := sq_mod_eight_of_odd ha; omega
    · have hb : b % 2 = 1 := by
        by_contra hb
        have := Nat.dvd_gcd (dvd_trans (by norm_num : 2 ∣ 4) ha)
          (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero (by omega : b % 2 = 0))
            (dvd_trans (by norm_num : 2 ∣ 4) hc))
        rw [hp] at this; omega
      have := sq_mod_eight_of_four_dvd ha; have := sq_mod_eight_of_four_dvd hc
      have := sq_mod_eight_of_odd hb; omega
  have h3 : (a ^ 2 + b ^ 2 + c ^ 2) % 3 = 1 := by
    rcases h.two_dvd_three with ⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨hc, ha⟩
    · have hc : ¬ 3 ∣ c := fun hc ↦ by
        have := Nat.dvd_gcd ha (Nat.dvd_gcd hb hc); rw [hp] at this; omega
      have := sq_mod_three_of_dvd ha; have := sq_mod_three_of_dvd hb
      have := sq_mod_three_of_not_dvd hc; omega
    · have ha : ¬ 3 ∣ a := fun ha ↦ by
        have := Nat.dvd_gcd ha (Nat.dvd_gcd hb hc); rw [hp] at this; omega
      have := sq_mod_three_of_dvd hc; have := sq_mod_three_of_dvd hb
      have := sq_mod_three_of_not_dvd ha; omega
    · have hb : ¬ 3 ∣ b := fun hb ↦ by
        have := Nat.dvd_gcd ha (Nat.dvd_gcd hb hc); rw [hp] at this; omega
      have := sq_mod_three_of_dvd ha; have := sq_mod_three_of_dvd hc
      have := sq_mod_three_of_not_dvd hb; omega
  omega

/-- The squarefree twist of a primitive brick is `≡ 1 (mod 24)`. (Squarefreeness of `s` is not
even needed: every `s` with `s · r² = a² + b² + c²` is `≡ 1 (mod 24)`.) -/
theorem IsEulerBrick.space_twist_mod_24 {a b c s r : ℕ} (h : IsEulerBrick a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) (_hs : Squarefree s)
    (hr : s * r ^ 2 = a ^ 2 + b ^ 2 + c ^ 2) : s % 24 = 1 := by
  have hN := h.sum_sq_mod_twentyfour hp
  have hr2 : r % 2 = 1 := by
    by_contra h2
    have : 2 ∣ s * r ^ 2 := Dvd.dvd.mul_left
      (Dvd.dvd.pow (Nat.dvd_of_mod_eq_zero (by omega) : 2 ∣ _) two_ne_zero) s
    rw [hr] at this; omega
  have hr3 : r % 3 ≠ 0 := by
    intro h3
    have : 3 ∣ s * r ^ 2 := Dvd.dvd.mul_left
      (Dvd.dvd.pow (Nat.dvd_of_mod_eq_zero h3) two_ne_zero) s
    rw [hr] at this; omega
  exact twist_of_mod hr hN (sq_mod_twentyfour hr2 hr3)

/-! ### The face twist of a primitive face cuboid -/

/-- Face-cuboid twist: for a primitive face cuboid either the missing sum `a² + b²` is
`≡ 1 (mod 8)` (hence so is its squarefree part), or `c` is odd and `4 ∣ a`, `4 ∣ b`. -/
theorem IsFaceCuboid.sq_add_sq_mod_eight {a b c : ℕ} (h : IsFaceCuboid a b c)
    (hp : Nat.gcd (Nat.gcd a b) c = 1) :
    (a ^ 2 + b ^ 2) % 8 = 1 ∨ (c % 2 = 1 ∧ 4 ∣ a ∧ 4 ∣ b) := by
  have hn : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c) := by
    rintro ⟨ha, hb, hc⟩
    have := Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc
    rw [hp] at this
    omega
  rcases h.two_adic hn with ⟨h1, h2, -, -⟩ | ⟨h1, h2, -, -⟩ | h3
  · left
    have := sq_mod_eight_of_odd h1; have := sq_mod_eight_of_four_dvd h2; omega
  · left
    have := sq_mod_eight_of_odd h1; have := sq_mod_eight_of_four_dvd h2; omega
  · exact Or.inr h3

/-- The squarefree twist `s` of the missing face sum of a primitive face cuboid is `≡ 1 (mod 8)`
unless `c` is the odd edge (and then `4 ∣ a`, `4 ∣ b`). -/
theorem IsFaceCuboid.twist_mod_eight {a b c s r : ℕ} (h : IsFaceCuboid a b c)
    (hp : Nat.gcd (Nat.gcd a b) c = 1) (_hs : Squarefree s) (hr : s * r ^ 2 = a ^ 2 + b ^ 2) :
    s % 8 = 1 ∨ (c % 2 = 1 ∧ 4 ∣ a ∧ 4 ∣ b) := by
  rcases h.sq_add_sq_mod_eight hp with hN | h3
  · left
    have hr2 : r % 2 = 1 := by
      by_contra h2
      have : 2 ∣ s * r ^ 2 := Dvd.dvd.mul_left
        (Dvd.dvd.pow (Nat.dvd_of_mod_eq_zero (by omega) : 2 ∣ _) two_ne_zero) s
      rw [hr] at this; omega
    exact twist_of_mod hr hN (sq_mod_eight_of_odd hr2)
  · exact Or.inr h3

/-! ### The derived-brick twist swap -/

/-- For a box with face diagonals `d, e, f`: `(def)² + (abc)² = σ₁ · σ₂` where
`σ₁ = a² + b² + c²` and `σ₂ = (bc)² + (ca)² + (ab)²` is the space-diagonal sum of the derived
box `(bc, ca, ab)`. (This is `(x + y)(y + z)(z + x) + xyz = σ₁(x,y,z) σ₂(x,y,z)` for
`x, y, z = a², b², c²`.) -/
theorem NearMissTwist.derived_identity {a b c d e f : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2) :
    (d * e * f) ^ 2 + (a * b * c) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2) * ((b * c) ^ 2 + (c * a) ^ 2 + (a * b) ^ 2) := by
  rw [mul_pow, mul_pow, hd, he, hf]
  ring

/-- The twist of the derived brick's space sum `σ₂` equals the twist of `(def)² + (abc)²`
up to the twist of the brick's space sum `σ₁`: `σ₂ σ₁` is a square iff `(def)² + (abc)²` is. -/
theorem NearMissTwist.isSquare_derived_iff {a b c d e f : ℕ} (hd : d ^ 2 = a ^ 2 + b ^ 2)
    (he : e ^ 2 = a ^ 2 + c ^ 2) (hf : f ^ 2 = b ^ 2 + c ^ 2) :
    IsSquare (((b * c) ^ 2 + (c * a) ^ 2 + (a * b) ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2)) ↔
      IsSquare ((d * e * f) ^ 2 + (a * b * c) ^ 2) := by
  rw [NearMissTwist.derived_identity hd he hf, mul_comm]

end PerfectCuboid
