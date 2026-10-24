module

public import LeanPlayground.PerfectCuboid.Basic

/-!
# Towards a proof by contradiction

Suppose a perfect cuboid exists. This file pushes that assumption as far as the known
elementary methods go, and then proves that the congruence method cannot finish the job.

## What a counterexample must look like

`IsPerfectCuboid.exists_normalForm`: if a perfect cuboid exists, then there is one with

* `gcd(a, b, c) = 1` (dividing out a common factor, the first step of an infinite descent),
* exactly one odd edge, and an odd space diagonal,
* `12640320 = 2⁶ · 3³ · 5 · 7 · 11 · 19` dividing `a · b · c`,
* longest edge at least `233`.

## Where the argument gets stuck

A proof by contradiction needs a step that the conditions above cannot satisfy. The natural
candidates fail:

* **Congruences.** `no_congruence_obstruction`: for every modulus `m`, the positive triple
  `(m, 3, 4)` satisfies all four perfect-cuboid equations modulo `m`, because it is congruent to
  the flat "cuboid" `(0, 3, 4)`, whose diagonals `3, 5, 4, 5` are integers. So no argument modulo
  `m` alone can reach a contradiction: the best it can conclude is that some edge is `≡ 0`, which
  is exactly the shape of every result in `Basic.lean`.
* **Descent.** Dividing by `gcd(a, b, c)` only reaches a primitive cuboid. To finish an infinite
  descent one would have to build a *smaller* perfect cuboid from a primitive one, and no such
  construction is known.
-/

@[expose] public section

namespace PerfectCuboid

/-! ### Dividing out a common factor -/

/-- If `g² · n` is a square and `g > 0`, then `n` is a square. -/
theorem isSquare_of_sq_mul {g n : ℕ} (hg : 0 < g) (h : IsSquare (g ^ 2 * n)) : IsSquare n := by
  obtain ⟨r, hr⟩ := h
  have hd : g ^ 2 ∣ r ^ 2 := ⟨n, by rw [sq r, ← hr]⟩
  obtain ⟨s, rfl⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).mp hd
  refine ⟨s, Nat.eq_of_mul_eq_mul_left (pow_pos hg 2) ?_⟩
  rw [hr]
  ring

namespace IsPerfectCuboid

variable {a b c : ℕ}

/-- Dividing a perfect cuboid by `gcd(a, b, c)` gives a primitive perfect cuboid. -/
theorem exists_primitive (h : IsPerfectCuboid a b c) :
    ∃ a' b' c', IsPerfectCuboid a' b' c' ∧ Nat.gcd a' (Nat.gcd b' c') = 1 := by
  set g := Nat.gcd a (Nat.gcd b c) with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ h.pos_a
  have ha : g ∣ a := Nat.gcd_dvd_left _ _
  have hbc : g ∣ Nat.gcd b c := Nat.gcd_dvd_right _ _
  have hb : g ∣ b := hbc.trans (Nat.gcd_dvd_left _ _)
  have hc : g ∣ c := hbc.trans (Nat.gcd_dvd_right _ _)
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  obtain ⟨z, hz⟩ := hc
  have pos {u v : ℕ} (huv : u = g * v) (hu : 0 < u) : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · omega
    · exact hv
  have sq2 {u v : ℕ} (huv : IsSquare ((g * u) ^ 2 + (g * v) ^ 2)) : IsSquare (u ^ 2 + v ^ 2) :=
    isSquare_of_sq_mul hg0 (by rw [mul_add, ← mul_pow, ← mul_pow]; exact huv)
  refine ⟨x, y, z, ⟨⟨pos hx h.pos_a, pos hy h.pos_b, pos hz h.pos_c, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact sq2 (hx ▸ hy ▸ h.sq_ab)
  · exact sq2 (hy ▸ hz ▸ h.sq_bc)
  · exact sq2 (hz ▸ hx ▸ h.sq_ca)
  · refine isSquare_of_sq_mul hg0 ?_
    have := h.sq_abc
    rw [hx, hy, hz, mul_pow, mul_pow, mul_pow] at this
    rwa [mul_add, mul_add]
  · have e : Nat.gcd (g * x) (Nat.gcd (g * y) (g * z)) = g * Nat.gcd x (Nat.gcd y z) := by
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left]
    rw [← hx, ← hy, ← hz, ← hg] at e
    exact (Nat.mul_eq_left hg0.ne').mp e.symm

/-- In a primitive perfect cuboid exactly one edge is odd. -/
theorem one_odd (h : IsPerfectCuboid a b c) (hp : Nat.gcd a (Nat.gcd b c) = 1) :
    (¬ 2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c) ∨ (2 ∣ a ∧ ¬ 2 ∣ b ∧ 2 ∣ c) ∨ (2 ∣ a ∧ 2 ∣ b ∧ ¬ 2 ∣ c) := by
  have h4 := h.toIsEulerBrick.two_dvd_four
  have even {x : ℕ} (hx : 4 ∣ x) : 2 ∣ x := (show 2 ∣ 4 by norm_num).trans hx
  have hall : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c) := fun ⟨ha, hb, hc⟩ ↦ by
    have := Nat.dvd_gcd ha (Nat.dvd_gcd hb hc)
    rw [hp] at this
    norm_num at this
  rcases h4 with ⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨hc, ha⟩
  · have := even ha; have := even hb; tauto
  · have := even hb; have := even hc; tauto
  · have := even hc; have := even ha; tauto

/-- In a primitive perfect cuboid the space diagonal is odd. -/
theorem odd_space_diagonal (h : IsPerfectCuboid a b c) (hp : Nat.gcd a (Nat.gcd b c) = 1) :
    ¬ 2 ∣ a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.add_mod (a ^ 2), Nat.pow_mod, Nat.pow_mod b,
    Nat.pow_mod c]
  rcases h.one_odd hp with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;>
  · rw [Nat.dvd_iff_mod_eq_zero] at ha hb hc
    simp [Nat.mod_two_ne_zero.mp, *]

/-! ### The product of the edges -/

theorem dvd_mul_of_one {p : ℕ} (h : p ∣ a ∨ p ∣ b ∨ p ∣ c) : p ∣ a * b * c := by
  rcases h with h | h | h
  · exact (h.mul_right b).mul_right c
  · exact (h.mul_left a).mul_right c
  · exact h.mul_left _

theorem dvd_mul_of_two {m n : ℕ}
    (h : (m ∣ a ∧ n ∣ b) ∨ (m ∣ b ∧ n ∣ a) ∨ (m ∣ b ∧ n ∣ c) ∨ (m ∣ c ∧ n ∣ b) ∨
      (m ∣ a ∧ n ∣ c) ∨ (m ∣ c ∧ n ∣ a)) : m * n ∣ a * b * c := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨c, rfl⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨c, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨a, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨a, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨b, by ring⟩
  · exact (mul_dvd_mul h1 h2).trans ⟨b, by ring⟩

/-- The product of the edges of a perfect cuboid is divisible by
`12640320 = 2⁶ · 3³ · 5 · 7 · 11 · 19`. -/
theorem dvd_mul_edges (h : IsPerfectCuboid a b c) : 12640320 ∣ a * b * c := by
  have e := h.toIsEulerBrick
  have h64 : 16 * 4 ∣ a * b * c := by
    have := e.two_dvd_four
    rcases e.sixteen_dvd with h16 | h16 | h16 <;> exact dvd_mul_of_two (by tauto)
  have h27 : 9 * 3 ∣ a * b * c := by
    have := e.two_dvd_three
    rcases e.nine_dvd with h9 | h9 | h9 <;> exact dvd_mul_of_two (by tauto)
  have h5 := dvd_mul_of_one e.five_dvd
  have h7 := dvd_mul_of_one h.seven_dvd
  have h11 := dvd_mul_of_one e.eleven_dvd
  have h19 := dvd_mul_of_one h.nineteen_dvd
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h64 h27
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) this h5
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) this h7
  have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) this h11
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) this h19

/-- The longest edge of a perfect cuboid is at least 233, since `232³ < 12640320`. -/
theorem le_max_edge (h : IsPerfectCuboid a b c) : 233 ≤ max a (max b c) := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have ha : a ≤ 232 := by omega
  have hb : b ≤ 232 := by omega
  have hc : c ≤ 232 := by omega
  have hpos : 0 < a * b * c := Nat.mul_pos (Nat.mul_pos h.pos_a h.pos_b) h.pos_c
  have := Nat.le_of_dvd hpos h.dvd_mul_edges
  have : a * b * c ≤ 232 * 232 * 232 := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
  omega

/-- **What a counterexample must look like.** If a perfect cuboid exists, there is a primitive
one with exactly one odd edge, an odd space diagonal, `12640320 ∣ a · b · c` and longest edge at
least 233. -/
theorem exists_normalForm (h : IsPerfectCuboid a b c) :
    ∃ a' b' c', IsPerfectCuboid a' b' c' ∧ Nat.gcd a' (Nat.gcd b' c') = 1 ∧
      ((¬ 2 ∣ a' ∧ 2 ∣ b' ∧ 2 ∣ c') ∨ (2 ∣ a' ∧ ¬ 2 ∣ b' ∧ 2 ∣ c') ∨
        (2 ∣ a' ∧ 2 ∣ b' ∧ ¬ 2 ∣ c')) ∧
      ¬ 2 ∣ a' ^ 2 + b' ^ 2 + c' ^ 2 ∧ 12640320 ∣ a' * b' * c' ∧ 233 ≤ max a' (max b' c') := by
  obtain ⟨a', b', c', h', hp⟩ := h.exists_primitive
  exact ⟨a', b', c', h', hp, h'.one_odd hp, h'.odd_space_diagonal hp, h'.dvd_mul_edges,
    h'.le_max_edge⟩

end IsPerfectCuboid

/-! ### Why congruences cannot finish the proof -/

/-- **No congruence obstruction.** For every modulus `m > 0` there are positive integers
`a, b, c` (namely `m, 3, 4`) that satisfy all four perfect-cuboid equations modulo `m`. So an
argument modulo `m` alone can never prove that perfect cuboids do not exist. -/
theorem no_congruence_obstruction (m : ℕ) (hm : 0 < m) :
    ∃ a b c d e f g : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a ^ 2 + b ^ 2 ≡ d ^ 2 [MOD m] ∧ b ^ 2 + c ^ 2 ≡ e ^ 2 [MOD m] ∧
      c ^ 2 + a ^ 2 ≡ f ^ 2 [MOD m] ∧ a ^ 2 + b ^ 2 + c ^ 2 ≡ g ^ 2 [MOD m] := by
  refine ⟨m, 3, 4, 3, 5, 4, 5, hm, by norm_num, by norm_num, ?_, rfl, ?_, ?_⟩
  all_goals
    unfold Nat.ModEq
    norm_num [add_assoc, Nat.add_mod (m ^ 2), Nat.add_mod 16 (m ^ 2), Nat.pow_mod]

/-- The flat "cuboid" `(0, 3, 4)` behind `no_congruence_obstruction`: all its diagonals are
integers, so every congruence a perfect cuboid satisfies, it satisfies too. -/
theorem flat_cuboid : IsSquare (0 ^ 2 + 3 ^ 2) ∧ IsSquare (3 ^ 2 + 4 ^ 2) ∧
    IsSquare (4 ^ 2 + 0 ^ 2) ∧ IsSquare (0 ^ 2 + 3 ^ 2 + 4 ^ 2) :=
  ⟨⟨3, rfl⟩, ⟨5, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩⟩

end PerfectCuboid
