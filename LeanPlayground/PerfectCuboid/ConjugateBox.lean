module

public import Mathlib
public import LeanPlayground.PerfectCuboid.SpaceDiagonal

/-!
# Two-twisted boxes: conjugate boxes and half-twisted boxes

For positive integers `a, b, c` consider the four sums `S₁ = a² + b²`, `S₂ = a² + c²`,
`S₃ = b² + c²`, `S₄ = a² + b² + c²` and their *twists* (classes modulo squares). A perfect
cuboid has all four twists trivial. If three of the four twists are equal to `k`, then `k = 1`
(twist rigidity). This file studies the patterns with **two** equal twists `k` and two squares.
Up to permuting the edges there are two of them:

* a **conjugate box** (`IsConjugateBox k a b c d e f g`): `k d² = a² + b²`, `k e² = a² + c²`,
  `f² = b² + c²`, `g² = a² + b² + c²`. Equivalently `(a g)² + (b c)² = (k d e)²` together with
  the two squares: the two face diagonals `d √k`, `e √k` through the edge `a` are "conjugate".
* a **half-twisted box** (`IsHalfTwistedBox k a b c d e f g`): `k d² = a² + b²`,
  `e² = a² + c²`, `f² = b² + c²`, `k g² = a² + b² + c²`.

For `k = 1` both are exactly perfect cuboids (`isConjugateBox_one_iff`,
`isHalfTwistedBox_one_iff`). No example with `k ≠ 1` is known (see the enumeration bounds in the
round-13 report); whether two equal twists and two squares already force `k = 1` is open.

## Main results

* `IsConjugateBox.ag_bc`, `IsConjugateBox.afg`: the identities `(ag)² + (bc)² = (kde)²` and
  `a² + f² = g²` (a conjugate box is a pair of nested Pythagorean triples `(b, c, f)`,
  `(a, f, g)` with `(a² + b²)(a² + c²)` a square).
* `IsConjugateBox.prime_dvd_all_or_none`: a prime of `k` dividing one edge divides all three.
* `IsConjugateBox.twist_odd`: the twist of a primitive conjugate box is odd.
* `IsConjugateBox.prime_mod_four`, `IsConjugateBox.prime_mod_eight`: **every prime of the twist
  of a primitive conjugate box is `≡ 1 (mod 8)`.** (From `a² + b² ≡ a² + c² ≡ 0 (mod p)` one gets
  `b² ≡ c²`, hence `f² ≡ 2 b² (mod p)` with `p ∤ b`, so `2` is a square mod `p`.)
* `IsHalfTwistedBox.dvd_c`: the twist of a half-twisted box divides `c`;
  `IsHalfTwistedBox.prime_dvd_all_or_none`, `IsHalfTwistedBox.prime_mod_four`: every odd prime
  of the twist of a primitive half-twisted box is `≡ 1 (mod 4)`. The twist `k = 2` cannot be
  excluded by a congruence argument: the degenerate box `(a, a, 0)` is a half-twisted box with
  `k = 2` (`isHalfTwistedBox_degenerate`), so the conditions `c > 0` must be used globally.
-/

@[expose] public section

namespace PerfectCuboid

namespace ConjugateBox

/-- Two twisted face diagonals `k d² = a² + b²`, `k e² = a² + c²`, square third face and space
diagonal. -/
structure IsConjugateBox (k a b c d e f g : ℕ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sqfree : Squarefree k
  hd : k * d ^ 2 = a ^ 2 + b ^ 2
  he : k * e ^ 2 = a ^ 2 + c ^ 2
  hf : f ^ 2 = b ^ 2 + c ^ 2
  hg : g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2

/-- Twisted face `a² + b²` and twisted space diagonal, square faces `a² + c²`, `b² + c²`. -/
structure IsHalfTwistedBox (k a b c d e f g : ℕ) : Prop where
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sqfree : Squarefree k
  hd : k * d ^ 2 = a ^ 2 + b ^ 2
  he : e ^ 2 = a ^ 2 + c ^ 2
  hf : f ^ 2 = b ^ 2 + c ^ 2
  hg : k * g ^ 2 = a ^ 2 + b ^ 2 + c ^ 2

variable {k a b c d e f g : ℕ}

/-! ### Elementary helpers -/

theorem sq_mod_two (x : ℕ) : x ^ 2 % 2 = x % 2 := by
  rw [Nat.pow_mod]
  have : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases x % 2 <;> rfl

theorem sq_mod_eight (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  have : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases x % 8 <;> simp

theorem sq_mod_eight_of_odd {x : ℕ} (h : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  rw [Nat.pow_mod]
  have : x % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h8 : x % 8 % 2 = 1 := by rw [Nat.mod_mod_of_dvd x (by norm_num : 2 ∣ 8)]; exact h
  interval_cases hx : x % 8 <;> simp_all

/-- If `p ∣ x` and `p ∣ x² + y²` for a prime `p`, then `p ∣ y`. -/
theorem dvd_of_dvd_sq_add_sq {p x y : ℕ} (hp : p.Prime) (hx : p ∣ x) (h : p ∣ x ^ 2 + y ^ 2) :
    p ∣ y :=
  hp.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow hx two_ne_zero)).mp h)

/-- A prime dividing all of `a, b, c` contradicts primitivity. -/
theorem not_dvd_all {p : ℕ} (hp : p.Prime) (hprim : Nat.gcd a (Nat.gcd b c) = 1)
    (ha : p ∣ a) (hb : p ∣ b) (hc : p ∣ c) : False := by
  have := Nat.dvd_gcd ha (Nat.dvd_gcd hb hc)
  rw [hprim] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-! ### Conjugate boxes -/

/-- `k = 1` is exactly a perfect cuboid. -/
theorem isConjugateBox_one_iff {a b c : ℕ} :
    (∃ d e f g, IsConjugateBox 1 a b c d e f g) ↔ IsPerfectCuboid a b c := by
  constructor
  · rintro ⟨d, e, f, g, h⟩
    exact ⟨⟨h.pos_a, h.pos_b, h.pos_c, ⟨d, by rw [← h.hd]; ring⟩, ⟨f, by rw [← h.hf]; ring⟩,
      ⟨e, by rw [add_comm, ← h.he]; ring⟩⟩, ⟨g, by rw [← h.hg]; ring⟩⟩
  · rintro ⟨⟨ha, hb, hc, ⟨d, hd⟩, ⟨f, hf⟩, ⟨e, he⟩⟩, ⟨g, hg⟩⟩
    exact ⟨d, e, f, g, ha, hb, hc, squarefree_one, by rw [hd]; ring,
      by rw [add_comm, he]; ring, by rw [hf]; ring, by rw [hg]; ring⟩

namespace IsConjugateBox

/-- The identity `(de)² k² = (ag)² + (bc)²` behind the name "conjugate face diagonals". -/
theorem ag_bc (h : IsConjugateBox k a b c d e f g) :
    (a * g) ^ 2 + (b * c) ^ 2 = (k * d * e) ^ 2 := by
  calc (a * g) ^ 2 + (b * c) ^ 2 = a ^ 2 * g ^ 2 + (b * c) ^ 2 := by ring
    _ = a ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) + (b * c) ^ 2 := by rw [h.hg]
    _ = (a ^ 2 + b ^ 2) * (a ^ 2 + c ^ 2) := by ring
    _ = (k * d ^ 2) * (k * e ^ 2) := by rw [h.hd, h.he]
    _ = (k * d * e) ^ 2 := by ring

/-- The space diagonal and `f` form a Pythagorean triple with `a`. -/
theorem afg (h : IsConjugateBox k a b c d e f g) : a ^ 2 + f ^ 2 = g ^ 2 := by
  rw [h.hf, h.hg]; ring

/-- No prime `p ≡ 3 (mod 4)` divides the twist of a primitive conjugate box (any prime of `k`
dividing one edge divides all three). -/
theorem prime_dvd_all_or_none (h : IsConjugateBox k a b c d e f g) {p : ℕ}
    (hp : p.Prime) (hpk : p ∣ k) (hpa : p ∣ a ∨ p ∣ b ∨ p ∣ c) : p ∣ a ∧ p ∣ b ∧ p ∣ c := by
  have hab : p ∣ a ^ 2 + b ^ 2 := h.hd ▸ dvd_mul_of_dvd_left hpk _
  have hac : p ∣ a ^ 2 + c ^ 2 := h.he ▸ dvd_mul_of_dvd_left hpk _
  have hba : p ∣ b ^ 2 + a ^ 2 := by rwa [add_comm]
  have hca : p ∣ c ^ 2 + a ^ 2 := by rwa [add_comm]
  rcases hpa with ha | hb | hc
  · exact ⟨ha, dvd_of_dvd_sq_add_sq hp ha hab, dvd_of_dvd_sq_add_sq hp ha hac⟩
  · have ha := dvd_of_dvd_sq_add_sq hp hb hba
    exact ⟨ha, hb, dvd_of_dvd_sq_add_sq hp ha hac⟩
  · have ha := dvd_of_dvd_sq_add_sq hp hc hca
    exact ⟨ha, dvd_of_dvd_sq_add_sq hp ha hab, hc⟩

/-- The twist of a primitive conjugate box is odd. -/
theorem twist_odd (h : IsConjugateBox k a b c d e f g)
    (hprim : Nat.gcd a (Nat.gcd b c) = 1) : k % 2 = 1 := by
  by_contra hk
  have h2 : 2 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
  have hab : 2 ∣ a ^ 2 + b ^ 2 := h.hd ▸ dvd_mul_of_dvd_left h2 _
  have hac : 2 ∣ a ^ 2 + c ^ 2 := h.he ▸ dvd_mul_of_dvd_left h2 _
  have := sq_mod_two a; have := sq_mod_two b; have := sq_mod_two c
  rcases Nat.even_or_odd a with ha | ha
  · have ha' : 2 ∣ a := ha.two_dvd
    exact not_dvd_all Nat.prime_two hprim ha' (dvd_of_dvd_sq_add_sq Nat.prime_two ha' hab)
      (dvd_of_dvd_sq_add_sq Nat.prime_two ha' hac)
  · have ha' : a % 2 = 1 := Nat.odd_iff.mp ha
    have hb : b % 2 = 1 := by omega
    have hc : c % 2 = 1 := by omega
    have h1 := sq_mod_eight_of_odd hb
    have h2 := sq_mod_eight_of_odd hc
    have h3 := sq_mod_eight f
    rw [h.hf] at h3
    omega

/-- Every prime of the twist of a primitive conjugate box is `≡ 1 (mod 4)`. -/
theorem prime_mod_four (h : IsConjugateBox k a b c d e f g)
    (hprim : Nat.gcd a (Nat.gcd b c) = 1) {p : ℕ} (hp : p.Prime) (hpk : p ∣ k) : p % 4 = 1 := by
  have hodd := h.twist_odd hprim
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h2
    · omega
    · exact h2
  have hp3 : p % 4 ≠ 3 := by
    intro h3
    have hab : p ∣ a ^ 2 + b ^ 2 := h.hd ▸ dvd_mul_of_dvd_left hpk _
    obtain ⟨ha, -⟩ := prime_dvd_both_of_dvd_sq_add_sq hp h3 hab
    obtain ⟨ha, hb, hc⟩ := h.prime_dvd_all_or_none hp hpk (Or.inl ha)
    exact not_dvd_all hp hprim ha hb hc
  omega

/-- **Every prime of the twist of a primitive conjugate box is `≡ 1 (mod 8)`.**
From `a² + b² ≡ a² + c² ≡ 0 (mod p)` we get `b² ≡ c²`, so `f² = b² + c² ≡ 2 b²`; since `p ∤ b`,
`2` is a square modulo `p`, i.e. `p ≡ ±1 (mod 8)`; together with `p ≡ 1 (mod 4)` this gives
`p ≡ 1 (mod 8)`. -/
theorem prime_mod_eight (h : IsConjugateBox k a b c d e f g)
    (hprim : Nat.gcd a (Nat.gcd b c) = 1) {p : ℕ} (hp : p.Prime) (hpk : p ∣ k) : p % 8 = 1 := by
  have h4 := h.prime_mod_four hprim hp hpk
  have : Fact p.Prime := ⟨hp⟩
  have hb : ¬ p ∣ b := fun hb ↦ by
    obtain ⟨ha, hb, hc⟩ := h.prime_dvd_all_or_none hp hpk (Or.inr (Or.inl hb))
    exact not_dvd_all hp hprim ha hb hc
  have hb' : (b : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hab : ((a ^ 2 + b ^ 2 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (h.hd ▸ dvd_mul_of_dvd_left hpk _)
  have hac : ((a ^ 2 + c ^ 2 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (h.he ▸ dvd_mul_of_dvd_left hpk _)
  have hf : ((f ^ 2 : ℕ) : ZMod p) = ((b ^ 2 + c ^ 2 : ℕ) : ZMod p) := by rw [h.hf]
  push_cast at hab hac hf
  have hf2 : (f : ZMod p) ^ 2 = 2 * (b : ZMod p) ^ 2 := by linear_combination hf - hab + hac
  have hsq : IsSquare (2 : ZMod p) := ⟨(f : ZMod p) * (b : ZMod p)⁻¹, by
    rw [show (f : ZMod p) * (b : ZMod p)⁻¹ * ((f : ZMod p) * (b : ZMod p)⁻¹) =
      (f : ZMod p) ^ 2 * ((b : ZMod p)⁻¹) ^ 2 by ring, hf2, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hb', one_pow, mul_one]⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  rcases (ZMod.exists_sq_eq_two_iff hp2).mp hsq with h8 | h8 <;> omega

end IsConjugateBox

/-! ### Half-twisted boxes -/

/-- `k = 1` is exactly a perfect cuboid. -/
theorem isHalfTwistedBox_one_iff {a b c : ℕ} :
    (∃ d e f g, IsHalfTwistedBox 1 a b c d e f g) ↔ IsPerfectCuboid a b c := by
  constructor
  · rintro ⟨d, e, f, g, h⟩
    exact ⟨⟨h.pos_a, h.pos_b, h.pos_c, ⟨d, by rw [← h.hd]; ring⟩, ⟨f, by rw [← h.hf]; ring⟩,
      ⟨e, by rw [add_comm, ← h.he]; ring⟩⟩, ⟨g, by rw [← h.hg]; ring⟩⟩
  · rintro ⟨⟨ha, hb, hc, ⟨d, hd⟩, ⟨f, hf⟩, ⟨e, he⟩⟩, ⟨g, hg⟩⟩
    exact ⟨d, e, f, g, ha, hb, hc, squarefree_one, by rw [hd]; ring,
      by rw [add_comm, he]; ring, by rw [hf]; ring, by rw [hg]; ring⟩

/-- The degenerate box `(a, a, 0)` satisfies all equations of a half-twisted box with `k = 2`
(only `0 < c` fails): no congruence argument can show that the twist of a half-twisted box is
odd. -/
theorem isHalfTwistedBox_degenerate (a : ℕ) :
    Squarefree 2 ∧ 2 * a ^ 2 = a ^ 2 + a ^ 2 ∧ a ^ 2 = a ^ 2 + 0 ^ 2 ∧
      2 * a ^ 2 = a ^ 2 + a ^ 2 + 0 ^ 2 :=
  ⟨Nat.prime_two.squarefree, by ring, by ring, by ring⟩

namespace IsHalfTwistedBox

/-- The twist of a half-twisted box divides `c`. -/
theorem dvd_c (h : IsHalfTwistedBox k a b c d e f g) : k ∣ c := by
  have h1 : k * g ^ 2 = k * d ^ 2 + c ^ 2 := by rw [h.hg, h.hd]
  have h2 : k ∣ k * d ^ 2 + c ^ 2 := h1 ▸ dvd_mul_right k _
  exact (h.sqfree.dvd_pow_iff_dvd two_ne_zero).mp ((Nat.dvd_add_right (dvd_mul_right k _)).mp h2)

/-- A prime of the twist of a half-twisted box divides `c`, and if it divides `a` or `b` it
divides all three edges. -/
theorem prime_dvd_all_or_none (h : IsHalfTwistedBox k a b c d e f g) {p : ℕ}
    (hp : p.Prime) (hpk : p ∣ k) (hpa : p ∣ a ∨ p ∣ b) : p ∣ a ∧ p ∣ b ∧ p ∣ c := by
  have hc := dvd_trans hpk h.dvd_c
  have hab : p ∣ a ^ 2 + b ^ 2 := h.hd ▸ dvd_mul_of_dvd_left hpk _
  have hba : p ∣ b ^ 2 + a ^ 2 := by rwa [add_comm]
  rcases hpa with ha | hb
  · exact ⟨ha, dvd_of_dvd_sq_add_sq hp ha hab, hc⟩
  · exact ⟨dvd_of_dvd_sq_add_sq hp hb hba, hb, hc⟩

/-- Every odd prime of the twist of a primitive half-twisted box is `≡ 1 (mod 4)`. -/
theorem prime_mod_four (h : IsHalfTwistedBox k a b c d e f g)
    (hprim : Nat.gcd a (Nat.gcd b c) = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ k) :
    p % 4 = 1 := by
  have hp2' : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · exact absurd h2 hp2
    · exact h2
  have hp3 : p % 4 ≠ 3 := by
    intro h3
    have hab : p ∣ a ^ 2 + b ^ 2 := h.hd ▸ dvd_mul_of_dvd_left hpk _
    obtain ⟨ha, -⟩ := prime_dvd_both_of_dvd_sq_add_sq hp h3 hab
    obtain ⟨ha, hb, hc⟩ := h.prime_dvd_all_or_none hp hpk (Or.inl ha)
    exact not_dvd_all hp hprim ha hb hc
  omega

end IsHalfTwistedBox

end ConjugateBox

end PerfectCuboid
