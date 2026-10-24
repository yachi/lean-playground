module

public import LeanPlayground.SimonMarais.Core
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The open problem from the 2023 Simon Marais Mathematics Competition

Formalization of the main result of

  Anthony Pisani, "On the Open Problem in the 2023 Simon Marais Mathematics Competition",
  <https://arxiv.org/abs/2610.30658> (October 2026).

**Question (SMMC 2023, B4(b)).** Let `n` be a positive integer that is not a perfect square.
Find all pairs `(a, b)` of positive integers for which there is a real `r` such that
`r^a + √n` and `r^b + √n` are both rational.

**Answer (Theorem 2 of the paper, `SimonMarais.main`).** Exactly the pairs with `a = b`, and the
pairs `{a, b} = {g, 2g}` with `g` odd.

## How the proof is organized

* `LeanPlayground/SimonMarais/Lucas.lean` — Lucas sequences, with elementary proofs of the cases
  of Ballot–Williams' Theorems 6 and 46 that the paper cites, and the growth bound (Lemma 6).
* `LeanPlayground/SimonMarais/OddSum.lean` — the `p`-adic valuation of the odd part of a binomial
  expansion, used twice in Theorem 13.
* `LeanPlayground/SimonMarais/Quad.lean` — arithmetic in `ℚ(√n)` and the reduction to
  `r ∈ ℚ(√n)` (Lemma 7).
* `LeanPlayground/SimonMarais/Core.lean` — Lemma 8, Theorem 9, Lemmas 10–12 and Theorem 13.

Two places differ from the paper. Theorem 9 is proved by comparing the ratios
`(|x| + √n)/(|x| - √n)` instead of by Rolle's theorem. Lemma 11's maximal `λ` is produced by
dividing out primes `p` with `p ∣ P` and `p² ∣ Q` until none is left.
-/

@[expose] public section

namespace SimonMarais

open Real

variable {n : ℕ}

/-- The forward direction for `a < b`: then `a = g` and `b = 2g` with `g` odd. -/
theorem forward_lt (hn : ¬ IsSquare n) {a b : ℕ} (ha : 0 < a) (hab : a < b) {r : ℝ} {qa qb : ℚ}
    (hra : r ^ a + √(n : ℝ) = qa) (hrb : r ^ b + √(n : ℝ) = qb) :
    ∃ g, Odd g ∧ a = g ∧ b = 2 * g := by
  set g := Nat.gcd a b with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨α, hα⟩ : g ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨β, hβ⟩ : g ∣ b := Nat.gcd_dvd_right a b
  have hcop : α.Coprime β := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg0
    rwa [← hg, hα, hβ, Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  have hα1 : 1 ≤ α := by
    rcases Nat.eq_zero_or_pos α with h | h
    · rw [h, mul_zero] at hα; omega
    · exact h
  have hαβ : α < β := by
    by_contra h
    push Not at h
    have : g * β ≤ g * α := Nat.mul_le_mul_left g h
    omega
  set t := r ^ g
  have hta : t ^ α = qa - √(n : ℝ) := by rw [← pow_mul, ← hα]; linarith
  have htb : t ^ β = qb - √(n : ℝ) := by rw [← pow_mul, ← hβ]; linarith
  obtain ⟨u, v, htuv⟩ := inQS_of_pow hn hα1 hαβ hcop hta htb
  have hB : ∀ c (q : ℚ), t ^ c = q - √(n : ℝ) → coeffB n u v c = -1 := by
    intro c q h
    rw [htuv, pow_eq_coeff] at h
    have := coeff_unique hn (x' := q) (y' := -1) (by rw [h]; push_cast; ring)
    exact this.2
  obtain ⟨rfl, rfl, hN⟩ := core hn hα1 hαβ hcop (hB α qa hta) (hB β qb htb)
  refine ⟨g, ?_, by omega, by omega⟩
  -- `g` is odd: otherwise `t = r^g ≥ 0` would force `N(t) ≥ 0`.
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have ht0 : 0 ≤ t := hev.pow_nonneg r
  have h1 : t = qa - √(n : ℝ) := by simpa using hta
  rw [htuv] at h1
  obtain ⟨rfl, rfl⟩ := coeff_unique hn (x' := qa) (y' := -1) (by rw [h1]; push_cast; ring)
  have hs : √(n : ℝ) ≤ u := by
    have : (0 : ℝ) ≤ u + (-1 : ℚ) * √(n : ℝ) := htuv ▸ ht0
    push_cast at this; linarith
  have : (n : ℝ) ≤ (u : ℝ) ^ 2 := by
    rw [← sq_sqrt_nat n]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  have : (n : ℚ) ≤ u ^ 2 := by exact_mod_cast this
  linarith

/-- **Theorem 2 of the paper** (answer to SMMC 2023 B4(b)). For `n` not a perfect square,
there is a real `r` with `r^a + √n` and `r^b + √n` both rational if and only if `a = b`, or
`{a, b} = {g, 2g}` for some odd `g`. -/
theorem main (hn : ¬ IsSquare n) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (∃ r : ℝ, (∃ q : ℚ, r ^ a + √(n : ℝ) = q) ∧ (∃ q : ℚ, r ^ b + √(n : ℝ) = q)) ↔
      a = b ∨ ∃ g, Odd g ∧ ((a = g ∧ b = 2 * g) ∨ (a = 2 * g ∧ b = g)) := by
  have hs1 := one_lt_sqrt hn
  have hsq := sq_sqrt_nat n
  constructor
  · rintro ⟨r, ⟨qa, hra⟩, ⟨qb, hrb⟩⟩
    rcases lt_trichotomy a b with hab | rfl | hab
    · obtain ⟨g, hg, h1, h2⟩ := forward_lt hn ha hab hra hrb
      exact Or.inr ⟨g, hg, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inl rfl
    · obtain ⟨g, hg, h1, h2⟩ := forward_lt hn hb hab hrb hra
      exact Or.inr ⟨g, hg, Or.inr ⟨h2, h1⟩⟩
  · rintro (rfl | ⟨g, hg, hab⟩)
    · -- `r = (n - √n)^(1/a)`
      have hpos : 0 ≤ (n : ℝ) - √(n : ℝ) := by nlinarith
      refine ⟨((n : ℝ) - √(n : ℝ)) ^ ((a : ℝ)⁻¹), ⟨n, ?_⟩, ⟨n, ?_⟩⟩ <;>
      · rw [Real.rpow_inv_natCast_pow hpos (by omega)]; push_cast; ring
    · -- `r = -(√n - 1/2)^(1/g)`, so `r^g = 1/2 - √n` and `r^(2g) = n + 1/4 - √n`
      have hpos : 0 ≤ √(n : ℝ) - 1 / 2 := by linarith
      have hg0 : g ≠ 0 := by rintro rfl; simp at hg
      set r := -((√(n : ℝ) - 1 / 2) ^ ((g : ℝ)⁻¹))
      have hrg : r ^ g = 1 / 2 - √(n : ℝ) := by
        rw [hg.neg_pow, Real.rpow_inv_natCast_pow hpos hg0]; ring
      have hr2g : r ^ (2 * g) = n + 1 / 4 - √(n : ℝ) := by
        rw [mul_comm, pow_mul, hrg]; linear_combination hsq
      have h1 : ∃ q : ℚ, r ^ g + √(n : ℝ) = q := ⟨1 / 2, by rw [hrg]; push_cast; ring⟩
      have h2 : ∃ q : ℚ, r ^ (2 * g) + √(n : ℝ) = q :=
        ⟨n + 1 / 4, by rw [hr2g]; push_cast; ring⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨r, h1, h2⟩
      · exact ⟨r, h2, h1⟩

end SimonMarais
