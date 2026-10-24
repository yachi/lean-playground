module

public import LeanPlayground.PerfectCuboid.Contradiction
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The space diagonal of a primitive perfect cuboid

A primitive perfect cuboid (edges with `gcd(a, b, c) = 1`) has an odd space diagonal `g`
(`IsPerfectCuboid.odd_space_diagonal`). This file proves the classical sharpening:

* `IsPerfectCuboid.prime_dvd_space_diagonal`: every prime factor of `g` is `≡ 1 (mod 4)`;
* `IsPerfectCuboid.space_diagonal_mod_four`: hence `g ≡ 1 (mod 4)`.

The proof is the only place in this development where a *structural* fact about all primes is
used, rather than a check of residues modulo one fixed number: a prime `p ≡ 3 (mod 4)` that
divides `x² + y²` divides both `x` and `y` (because `-1` is not a square modulo `p`). Applied to
`g² = (a² + b²) + c²` and then to `a² + b² = d²`, such a `p` would divide `a`, `b` and `c`.
-/

@[expose] public section

namespace PerfectCuboid

/-- A prime `p ≡ 3 (mod 4)` dividing a sum of two squares divides both of them. -/
theorem prime_dvd_both_of_dvd_sq_add_sq {p x y : ℕ} (hp : p.Prime) (h3 : p % 4 = 3)
    (h : p ∣ x ^ 2 + y ^ 2) : p ∣ x ∧ p ∣ y := by
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ {x y : ℕ}, p ∣ x ^ 2 + y ^ 2 → p ∣ y := by
    intro x y h
    by_contra hy
    have hy' : (y : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hxy : (x : ZMod p) ^ 2 = -(y : ZMod p) ^ 2 := by
      have : ((x ^ 2 + y ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      push_cast at this
      linear_combination this
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy' hxy h3
  exact ⟨key (by rwa [add_comm] at h), key h⟩

/-- A positive number all of whose prime factors are `≡ 1 (mod 4)` is itself `≡ 1 (mod 4)`. -/
theorem mod_four_eq_one_of_forall_prime_dvd {n : ℕ} (hn : 0 < n)
    (h : ∀ p, p.Prime → p ∣ n → p % 4 = 1) : n % 4 = 1 := by
  induction n using Nat.recOnMul with
  | zero => omega
  | one => rfl
  | prime p hp => exact h p hp dvd_rfl
  | mul a b iha ihb =>
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have ha4 := iha ha fun p hp hpa ↦ h p hp (hpa.mul_right b)
    have hb4 := ihb hb fun p hp hpb ↦ h p hp (hpb.mul_left a)
    rw [Nat.mul_mod, ha4, hb4]

namespace IsPerfectCuboid

variable {a b c : ℕ}

/-- **Prime factors of the space diagonal.** In a primitive perfect cuboid every prime factor
of the space diagonal `g` is `≡ 1 (mod 4)`. -/
theorem prime_dvd_space_diagonal (h : IsPerfectCuboid a b c) (hp : Nat.gcd a (Nat.gcd b c) = 1)
    {g : ℕ} (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) {p : ℕ} (pp : p.Prime) (hpg : p ∣ g) :
    p % 4 = 1 := by
  have hodd := h.odd_space_diagonal hp
  rcases pp.eq_two_or_odd with rfl | hp2
  · exact absurd (hg ▸ dvd_pow hpg two_ne_zero) hodd
  by_contra h1
  have h3 : p % 4 = 3 := by omega
  obtain ⟨d, hd⟩ := h.sq_ab
  have hpg2 : p ∣ d ^ 2 + c ^ 2 := by
    rw [sq d, ← hd, hg]
    exact dvd_pow hpg two_ne_zero
  obtain ⟨hpd, hpc⟩ := prime_dvd_both_of_dvd_sq_add_sq pp h3 hpg2
  have hpab : p ∣ a ^ 2 + b ^ 2 := by
    rw [hd]
    exact hpd.mul_right d
  obtain ⟨hpa, hpb⟩ := prime_dvd_both_of_dvd_sq_add_sq pp h3 hpab
  have := Nat.dvd_gcd hpa (Nat.dvd_gcd hpb hpc)
  rw [hp] at this
  exact pp.one_lt.ne' (Nat.dvd_one.mp this)

/-- The space diagonal of a primitive perfect cuboid is `≡ 1 (mod 4)`. -/
theorem space_diagonal_mod_four (h : IsPerfectCuboid a b c) (hp : Nat.gcd a (Nat.gcd b c) = 1)
    {g : ℕ} (hg : a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2) : g % 4 = 1 := by
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · have := h.pos_a
      nlinarith
    · exact hg0
  exact mod_four_eq_one_of_forall_prime_dvd hg0 fun p pp hpg ↦
    h.prime_dvd_space_diagonal hp hg pp hpg

end IsPerfectCuboid

end PerfectCuboid
