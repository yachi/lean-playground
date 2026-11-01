module

public import Mathlib

/-!
# Perfect boxes in lattices: Eisenstein bricks, `A₃` boxes and hexagonal prisms

A *perfect box in a lattice* `L ⊂ ℝ³` with basis `e₁, e₂, e₃` is a triple `(a, b, c)` of positive
integers such that every nonzero `0/1`-combination of `a e₁, b e₂, c e₃` has square norm.
For `L = ℤ³` this is the perfect cuboid. Two new instances:

* the `60°` lattice `A₃` (`⟨eᵢ, eⱼ⟩ = 1/2` for `i ≠ j`): the faces have the *Eisenstein* norms
  `a² + ab + b²`, and the space vector has norm `a² + b² + c² + ab + bc + ca`;
* the hexagonal prism (`e₁, e₂` at `60°`, `e₃` orthogonal): faces `a² + ab + b²`, `a² + c²`,
  `b² + c²`, space `a² + ab + b² + c²`.

## Main results

* `IsEisensteinBrick`, `IsA3Box`, `IsHexPrismBox`: the definitions.
* `IsEisensteinBrick.derived`: as for Euler bricks, the derived box `(bc, ca, ab)` of an
  Eisenstein brick is again an Eisenstein brick (`(bc)² + (bc)(ca) + (ca)² = c²(a² + ab + b²)`);
  `IsHexPrismBox.derived_faces`: for a hexagonal-prism box only the three *face* conditions pass
  to the derived box (the space condition does not).
  The two smallest primitive Eisenstein bricks `(195, 264, 325)` and `(264, 325, 440)` are
  derived from each other: `(264·325, 325·195, 195·264) = 195 · (440, 325, 264)`.
* `eisensteinBrick_195_264_325`, …: the seven Eisenstein bricks with edges `≤ 1500` (two of them
  primitive), and `not_isA3Box_195_264_325`, `not_isA3Box_264_325_440`.
* `eisensteinBrick_family` (**Saunderson-type family**): for every Eisenstein pair `(b, c)`,
  `0 < c < b`, the box `(A, bD, cD)` with `A = 8bc(b + c)(3b² + 6bc + 7c²)(7b² + 6bc + 3c²)`,
  `D = (b − c)²(b + 3c)(3b + c)(9b² + 14bc + 9c²)` is an Eisenstein brick. The underlying
  identity (`family_identity`) holds for all `b ≥ c` (`famD` uses truncated subtraction `b − c`;
  over `ℤ` it is an identity in `b, c`): the genus-one curve
  `a² + ab + b² = □, a² + ac + c² = □` over `ℚ(b, c)` has the point `a = A/D`, found as the
  fourth intersection of planes through trivial points (`a = 0`, `a = −(b + c)`, `a = ∞`).
  With `b = m² − n²`, `c = 2mn + n²` this is a two-parameter polynomial family of degree 14 in
  `(m, n)`; the smallest member (from `(5, 3)`) is `576 · (110960, 4515, 2709)`, whose primitive
  part is the brick `(110960, 4515, 2709)` (`eisensteinBrick_110960_4515_2709`). Whether the
  family point has infinite order on the curve is open. None of the 473 members with `m < 40` is
  an `A₃` box.
* `prime_dvd_both_of_dvd_eisenstein`: if `p` is a prime with `p % 3 = 2` and
  `p ∣ a² + ab + b²` then `p ∣ a` and `p ∣ b`. *Proof*: if `p ∤ b`, then `t = a/b` in `ZMod p`
  satisfies `t² + t + 1 = 0`, so `t³ = 1`; as `p − 1 ≡ 1 (mod 3)`, Fermat gives
  `1 = t^(p−1) = t`, and then `3 = 0` in `ZMod p`, impossible. No quadratic reciprocity is
  needed, and `p = 2` is covered by the same argument.
* `three_dvd_both_of_nine_dvd_eisenstein`: if `9 ∣ a² + ab + b²` then `3 ∣ a` and `3 ∣ b`.
* `prime_mod_three_of_eisensteinTriple`: in an Eisenstein triple `a² + ab + b² = c²` with
  `gcd(a, b) = 1`, every prime factor of `c` is `≡ 1 (mod 3)` — the `A₃` analogue of
  `SpaceDiagonal.lean`. Corollary `IsEisensteinBrick.prime_dvd_diag`: in a primitive Eisenstein
  brick a prime `q ≡ 2 (mod 3)` dividing the `(a, b)` face diagonal divides `a` and `b` but not
  `c`. (Primitive Eisenstein bricks need not have pairwise coprime edges:
  `gcd(195, 325) = 65`, and the face diagonal `399 = 3·7·19` of `(195, 264)` contains `3`.)

Searches (edges `≤ 10⁵`, `round15/code/b3/latsearch.c`): 896 Eisenstein bricks (69 primitive),
no `A₃` box; 25293 hexagonal-prism bricks (665 primitive), none perfect.
-/

@[expose] public section

namespace PerfectCuboid.Lattice

/-- An Eisenstein triple: `a² + ab + b² = c²` (a triangle with a `120°` angle between `a`, `b`). -/
def IsEisensteinTriple (a b c : ℕ) : Prop := a ^ 2 + a * b + b ^ 2 = c ^ 2

/-- An Eisenstein brick: a box in the `60°` lattice `A₃` with all three face diagonals integral. -/
structure IsEisensteinBrick (a b c : ℕ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sq_ab : IsSquare (a ^ 2 + a * b + b ^ 2)
  sq_ac : IsSquare (a ^ 2 + a * c + c ^ 2)
  sq_bc : IsSquare (b ^ 2 + b * c + c ^ 2)

/-- A perfect box in the lattice `A₃`: an Eisenstein brick whose space vector
`a e₁ + b e₂ + c e₃` has square norm `a² + b² + c² + ab + bc + ca`. -/
structure IsA3Box (a b c : ℕ) : Prop extends IsEisensteinBrick a b c where
  sq_abc : IsSquare (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)

/-- A perfect box in the hexagonal prism lattice (`e₁, e₂` at `60°`, `e₃` orthogonal). -/
structure IsHexPrismBox (a b c : ℕ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sq_ab : IsSquare (a ^ 2 + a * b + b ^ 2)
  sq_ac : IsSquare (a ^ 2 + c ^ 2)
  sq_bc : IsSquare (b ^ 2 + c ^ 2)
  sq_abc : IsSquare (a ^ 2 + a * b + b ^ 2 + c ^ 2)

/-! ### Derived boxes -/

theorem isSquare_mul_sq {x n : ℕ} (h : IsSquare n) : IsSquare (x ^ 2 * n) := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨x * r, by ring⟩

/-- The derived box `(bc, ca, ab)` of an Eisenstein brick is an Eisenstein brick. -/
theorem IsEisensteinBrick.derived {a b c : ℕ} (h : IsEisensteinBrick a b c) :
    IsEisensteinBrick (b * c) (c * a) (a * b) where
  pos_a := Nat.mul_pos h.pos_b h.pos_c
  pos_b := Nat.mul_pos h.pos_c h.pos_a
  pos_c := Nat.mul_pos h.pos_a h.pos_b
  sq_ab := by
    have := isSquare_mul_sq (x := c) h.sq_ab
    convert this using 1; ring
  sq_ac := by
    have := isSquare_mul_sq (x := b) h.sq_ac
    convert this using 1; ring
  sq_bc := by
    have := isSquare_mul_sq (x := a) h.sq_bc
    convert this using 1; ring

/-- The derived box `(bc, ca, ab)` of a hexagonal-prism box has the three face conditions and
the `60°` face of the original; its space vector need not be square, so we state the brick part. -/
theorem IsHexPrismBox.derived_faces {a b c : ℕ} (h : IsHexPrismBox a b c) :
    IsSquare ((b * c) ^ 2 + (b * c) * (c * a) + (c * a) ^ 2) ∧
      IsSquare ((b * c) ^ 2 + (a * b) ^ 2) ∧ IsSquare ((c * a) ^ 2 + (a * b) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have := isSquare_mul_sq (x := c) h.sq_ab
    convert this using 1; ring
  · have := isSquare_mul_sq (x := b) h.sq_ac
    convert this using 1; ring
  · have := isSquare_mul_sq (x := a) h.sq_bc
    convert this using 1; ring

/-! ### The seven Eisenstein bricks with edges `≤ 1500` -/

theorem eisensteinBrick_195_264_325 : IsEisensteinBrick 195 264 325 :=
  ⟨by norm_num, by norm_num, by norm_num, ⟨399, by norm_num⟩, ⟨455, by norm_num⟩,
    ⟨511, by norm_num⟩⟩

theorem eisensteinBrick_264_325_440 : IsEisensteinBrick 264 325 440 :=
  ⟨by norm_num, by norm_num, by norm_num, ⟨511, by norm_num⟩, ⟨616, by norm_num⟩,
    ⟨665, by norm_num⟩⟩

theorem eisensteinBrick_390_528_650 : IsEisensteinBrick 390 528 650 :=
  ⟨by norm_num, by norm_num, by norm_num, ⟨798, by norm_num⟩, ⟨910, by norm_num⟩,
    ⟨1022, by norm_num⟩⟩

theorem eisensteinBrick_528_650_880 : IsEisensteinBrick 528 650 880 :=
  ⟨by norm_num, by norm_num, by norm_num, ⟨1022, by norm_num⟩, ⟨1232, by norm_num⟩,
    ⟨1330, by norm_num⟩⟩

theorem eisensteinBrick_585_792_975 : IsEisensteinBrick 585 792 975 :=
  ⟨by norm_num, by norm_num, by norm_num, ⟨1197, by norm_num⟩, ⟨1365, by norm_num⟩,
    ⟨1533, by norm_num⟩⟩

theorem eisensteinBrick_780_1056_1300 : IsEisensteinBrick 780 1056 1300 :=
  ⟨by norm_num, by norm_num, by norm_num, ⟨1596, by norm_num⟩, ⟨1820, by norm_num⟩,
    ⟨2044, by norm_num⟩⟩

theorem eisensteinBrick_792_975_1320 : IsEisensteinBrick 792 975 1320 :=
  ⟨by norm_num, by norm_num, by norm_num, ⟨1533, by norm_num⟩, ⟨1848, by norm_num⟩,
    ⟨1995, by norm_num⟩⟩

/-- `n` lies strictly between two consecutive squares, so it is not a square. -/
theorem not_isSquare_of_between {n k : ℕ} (h1 : k * k < n) (h2 : n < (k + 1) * (k + 1)) :
    ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  rcases le_or_gt r k with h | h
  · have := Nat.mul_le_mul h h; omega
  · have h' : k + 1 ≤ r := h
    have := Nat.mul_le_mul h' h'; omega

/-- `(195, 264, 325)` is not an `A₃` box: `195² + 264² + 325² + 195·264 + 264·325 + 325·195 =
414001` lies strictly between `643²` and `644²`. -/
theorem not_isA3Box_195_264_325 : ¬ IsA3Box 195 264 325 := fun h =>
  not_isSquare_of_between (k := 643) (by norm_num) (by norm_num) h.sq_abc

theorem not_isA3Box_264_325_440 : ¬ IsA3Box 264 325 440 := fun h =>
  not_isSquare_of_between (k := 844) (by norm_num) (by norm_num) h.sq_abc

/-! ### Primes `≡ 2 (mod 3)` and the Eisenstein form -/

/-- If `p ≡ 2 (mod 3)` is prime and `p ∣ a² + ab + b²`, then `p ∣ a` and `p ∣ b`. -/
theorem prime_dvd_both_of_dvd_eisenstein {p a b : ℕ} (hp : p.Prime) (h3 : p % 3 = 2)
    (h : p ∣ a ^ 2 + a * b + b ^ 2) : p ∣ a ∧ p ∣ b := by
  have := Fact.mk hp
  have hz : ((a : ZMod p)) ^ 2 + a * b + b ^ 2 = 0 := by
    rw [← ZMod.natCast_eq_zero_iff] at h; push_cast at h; exact h
  by_cases hb : (b : ZMod p) = 0
  · have ha : (a : ZMod p) = 0 := by
      rw [hb] at hz; simpa using hz
    exact ⟨(ZMod.natCast_eq_zero_iff _ _).mp ha, (ZMod.natCast_eq_zero_iff _ _).mp hb⟩
  · exfalso
    set t : ZMod p := (a : ZMod p) * (b : ZMod p)⁻¹ with ht
    have hq : t ^ 2 + t + 1 = 0 := by
      have : t ^ 2 + t + 1 = ((a : ZMod p) ^ 2 + a * b + b ^ 2) * ((b : ZMod p)⁻¹) ^ 2 := by
        rw [ht]; field_simp
      rw [this, hz, zero_mul]
    have hcube : t ^ 3 = 1 := by
      linear_combination (t - 1) * hq
    have ht0 : t ≠ 0 := by
      rintro h0; rw [h0] at hq; simp at hq
    obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 2 := ⟨p / 3, by omega⟩
    have hferm := ZMod.pow_card_sub_one_eq_one ht0
    have hpk : p - 1 = 3 * k + 1 := by omega
    rw [hpk, pow_succ, pow_mul, hcube, one_pow, one_mul] at hferm
    rw [hferm] at hq
    have h3z : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hq
    rw [ZMod.natCast_eq_zero_iff] at h3z
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3z
    omega

/-- If `9 ∣ a² + ab + b²` then `3 ∣ a` and `3 ∣ b`. -/
theorem three_dvd_both_of_nine_dvd_eisenstein {a b : ℕ} (h : 9 ∣ a ^ 2 + a * b + b ^ 2) :
    3 ∣ a ∧ 3 ∣ b := by
  have key : (a ^ 2 + a * b + b ^ 2) % 9 =
      ((a % 9) ^ 2 + (a % 9) * (b % 9) + (b % 9) ^ 2) % 9 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have ha := Nat.mod_lt a (show 0 < 9 by norm_num)
  have hb := Nat.mod_lt b (show 0 < 9 by norm_num)
  have h0 : (a ^ 2 + a * b + b ^ 2) % 9 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [key] at h0
  have e1 : a % 3 = a % 9 % 3 := (Nat.mod_mod_of_dvd a (by norm_num)).symm
  have e2 : b % 3 = b % 9 % 3 := (Nat.mod_mod_of_dvd b (by norm_num)).symm
  refine ⟨Nat.dvd_of_mod_eq_zero ?_, Nat.dvd_of_mod_eq_zero ?_⟩ <;>
  · rw [e1] at *; rw [e2] at *
    interval_cases (a % 9) <;> interval_cases (b % 9) <;> simp_all

/-- In an Eisenstein triple `a² + ab + b² = c²` with `gcd(a, b) = 1`, every prime factor of `c`
is `≡ 1 (mod 3)`. -/
theorem prime_mod_three_of_eisensteinTriple {a b c q : ℕ} (h : IsEisensteinTriple a b c)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hqc : q ∣ c) : q % 3 = 1 := by
  have hqs : q ∣ a ^ 2 + a * b + b ^ 2 := by
    rw [h]; exact Dvd.dvd.mul_left hqc c |>.trans (by rw [sq])
  have hnot : ¬ (q ∣ a ∧ q ∣ b) := by
    rintro ⟨h1, h2⟩
    have := Nat.dvd_gcd h1 h2
    rw [hab] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hlt := Nat.mod_lt q (show 0 < 3 by norm_num)
  rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h0 | h1 | h2
  · have hq3 : q = 3 := by
      have : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp this).symm
    subst hq3
    have h9 : 9 ∣ a ^ 2 + a * b + b ^ 2 := by
      rw [h]; obtain ⟨k, rfl⟩ := hqc; exact ⟨k ^ 2, by ring⟩
    exact absurd (three_dvd_both_of_nine_dvd_eisenstein h9) hnot
  · exact h1
  · exact absurd (prime_dvd_both_of_dvd_eisenstein hq h2 hqs) hnot

/-- In an Eisenstein brick with `gcd(a, gcd(b, c)) = 1`, a prime `q ≡ 2 (mod 3)` dividing the
`(a, b)` face diagonal divides `a` and `b` but not `c`. -/
theorem IsEisensteinBrick.prime_dvd_diag {a b c x q : ℕ} (_h : IsEisensteinBrick a b c)
    (hp : Nat.gcd a (Nat.gcd b c) = 1) (hx : a ^ 2 + a * b + b ^ 2 = x ^ 2) (hq : q.Prime)
    (h2 : q % 3 = 2) (hqx : q ∣ x) : q ∣ a ∧ q ∣ b ∧ ¬ q ∣ c := by
  have hqs : q ∣ a ^ 2 + a * b + b ^ 2 := by
    rw [hx]; exact Dvd.dvd.mul_left hqx x |>.trans (by rw [sq])
  obtain ⟨ha, hb⟩ := prime_dvd_both_of_dvd_eisenstein hq h2 hqs
  refine ⟨ha, hb, fun hc => ?_⟩
  have := Nat.dvd_gcd ha (Nat.dvd_gcd hb hc)
  rw [hp] at this
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

/-! ### A two-parameter polynomial family of Eisenstein bricks -/

/-- `A(b, c) = 8bc(b + c)(3b² + 6bc + 7c²)(7b² + 6bc + 3c²)`. -/
def famA (b c : ℕ) : ℕ :=
  8 * b * c * (b + c) * (3 * b ^ 2 + 6 * b * c + 7 * c ^ 2) * (7 * b ^ 2 + 6 * b * c + 3 * c ^ 2)

/-- `D(b, c) = (b − c)²(b + 3c)(3b + c)(9b² + 14bc + 9c²)`. -/
def famD (b c : ℕ) : ℕ :=
  (b - c) ^ 2 * (b + 3 * c) * (3 * b + c) * (9 * b ^ 2 + 14 * b * c + 9 * c ^ 2)

/-- The polynomial identities behind `eisensteinBrick_family`. For all `b, c`, with
`A = 8bc(b + c)(3b² + 6bc + 7c²)(7b² + 6bc + 3c²)` and
`D = (b − c)²(b + 3c)(3b + c)(9b² + 14bc + 9c²)`, both `A² + A(bD) + (bD)²` and
`A² + A(cD) + (cD)²` are squares. -/
theorem family_identity (b c k : ℕ) (hb : b = c + k) :
    famA b c ^ 2 + famA b c * (b * famD b c) + (b * famD b c) ^ 2 =
      (b * (27 * b ^ 6 + 162 * b ^ 5 * c + 673 * b ^ 4 * c ^ 2 + 1164 * b ^ 3 * c ^ 3 +
        1197 * b ^ 2 * c ^ 4 + 690 * b * c ^ 5 + 183 * c ^ 6)) ^ 2 ∧
    famA b c ^ 2 + famA b c * (c * famD b c) + (c * famD b c) ^ 2 =
      (c * (183 * b ^ 6 + 690 * b ^ 5 * c + 1197 * b ^ 4 * c ^ 2 + 1164 * b ^ 3 * c ^ 3 +
        673 * b ^ 2 * c ^ 4 + 162 * b * c ^ 5 + 27 * c ^ 6)) ^ 2 := by
  subst hb
  simp only [famA, famD, Nat.add_sub_cancel_left]
  constructor <;> ring

/-- **A Saunderson-type family of Eisenstein bricks.** If `0 < c < b` and `b² + bc + c²` is a
square (e.g. `b = m² − n²`, `c = 2mn + n²` or swapped), then `(A, bD, cD)` is an Eisenstein brick,
where `A = 8bc(b + c)(3b² + 6bc + 7c²)(7b² + 6bc + 3c²)` and
`D = (b − c)²(b + 3c)(3b + c)(9b² + 14bc + 9c²)`. The face diagonals are
`b(27b⁶ + 162b⁵c + 673b⁴c² + 1164b³c³ + 1197b²c⁴ + 690bc⁵ + 183c⁶)`,
`c(183b⁶ + 690b⁵c + 1197b⁴c² + 1164b³c³ + 673b²c⁴ + 162bc⁵ + 27c⁶)` and `D·√(b² + bc + c²)`. -/
theorem eisensteinBrick_family {b c : ℕ} (hc : 0 < c) (hcb : c < b)
    (h : IsSquare (b ^ 2 + b * c + c ^ 2)) :
    IsEisensteinBrick (famA b c) (b * famD b c) (c * famD b c) := by
  obtain ⟨k, hk⟩ : ∃ k, b = c + k := ⟨b - c, by omega⟩
  obtain ⟨i₁, i₂⟩ := family_identity b c k hk
  have hb : 0 < b := by omega
  have hbc : 0 < b - c := by omega
  have hA : 0 < famA b c := by unfold famA; positivity
  have hD : 0 < famD b c := by unfold famD; positivity
  refine ⟨hA, Nat.mul_pos hb hD, Nat.mul_pos hc hD, ⟨_, i₁.trans (sq _)⟩,
    ⟨_, i₂.trans (sq _)⟩, ?_⟩
  obtain ⟨r, hr⟩ := h
  refine ⟨famD b c * r, ?_⟩
  have e : ∀ D : ℕ, (b * D) ^ 2 + (b * D) * (c * D) + (c * D) ^ 2 =
      D ^ 2 * (b ^ 2 + b * c + c ^ 2) := fun D => by ring
  rw [e, hr]; ring

/-- The first member of the family, from the Eisenstein pair `(5, 3)` (`25 + 15 + 9 = 7²`),
reduced by the common factor: the primitive Eisenstein brick `(110960, 4515, 2709)`. -/
theorem eisensteinBrick_110960_4515_2709 : IsEisensteinBrick 110960 4515 2709 :=
  ⟨by norm_num, by norm_num, by norm_num, ⟨113285, by norm_num⟩, ⟨112339, by norm_num⟩,
    ⟨6321, by norm_num⟩⟩

end PerfectCuboid.Lattice
