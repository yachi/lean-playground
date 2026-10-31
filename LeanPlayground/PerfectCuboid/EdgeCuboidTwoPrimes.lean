module

public import LeanPlayground.PerfectCuboid.EdgeTwoPrimes
public import LeanPlayground.PerfectCuboid.EdgeCuboid

/-!
# The irrational edge of an edge cuboid has at least three distinct prime factors

## Main results

* `three_factorizations_ne_two_prime_pow`: let `N > 0` have three "factorizations through
  squares" `N + x² = X²`, `N + y² = Y²`, `N + z² = Z²` with `x, y > 0` and `x² + y² = z²`. Then
  `N ≠ p^K q^L` for primes `p ≠ q` and **any** `K, L ≥ 0` (odd exponents allowed, `N` may or may
  not be a square; `p = 2` allowed).
* `IsEdgeCuboid.N_ne_two_prime_pow`: the square `N` of the irrational edge of an edge cuboid is
  not `p^K q^L`; in particular not `2^s p^k` and not a prime power (re-proving
  `IsEdgeCuboid.N_ne_prime_pow`).
* `IsEdgeCuboid.three_le_primeFactors_card`: `N` has at least three distinct prime factors.
* `IsPerfectCuboid.edge_ne_two_prime_pow_of_three_factorizations`: the special case `N = a²`
  (`K = 2k`, `L = 2l`) re-derives the round-11 theorem `IsPerfectCuboid.edge_ne_two_prime_pow`
  of `EdgeTwoPrimes.lean` (Korec's two-prime case without side conditions).

The edge-cuboid statement is, as far as we know, new: the literature on edge cuboids (Leech 1977,
van Luijk 2000 §2) gives examples and parametrizations but nothing on the prime structure of `N`.
It is consistent with the examples: Leech's `N = 618849 = 3²·7·11·19·47` (five primes) and the
smallest `N = 461776 = 2⁴·7²·19·31` (four primes, `(a, b) = (1443, 1800)`), and with all 173
edge cuboids with `N ≤ 10⁹`.

## The proof

This is the case tree of `EdgeTwoPrimes.config_false` with `2k, 2l` replaced by arbitrary
`K, L`. Writing `N = tₘuₘ` with `tₘ = X − x = p^iₘ q^jₘ`, `uₘ = X + x = p^aₘ q^bₘ`
(`iₘ + aₘ = K`, `jₘ + bₘ = L`, `leg_two_gen`), the legs `2x = uₘ − tₘ` satisfy the
Pythagorean relation. The only places where evenness of the exponent entered `EdgeTwoPrimes`
are `two_min` (now `two_min_gen`: either all `iₘ = aₘ`, which forces `K` even, or the minimum of
the `min(iₘ, aₘ)` is attained twice and is `< K/2`) and the linear hypotheses of the eleven case
lemmas, all still closed by `omega`. The residual equation (`res_shape`, `res_no_solution`) never
needed even exponents and is reused verbatim.

## Near-miss remarks

Positivity of `x, y` is used only through `tₘ < uₘ` and `t₃ < t₁, t₂` (and to get `z > 0`);
degenerate configurations (`x = 0`, i.e. `t = u`, possible only for a square `N`) fail exactly
there. Neither parity of `tₘ, uₘ` nor `N` non-square is used. Face cuboids and Euler bricks have
a different structure (no common `N` with three factorizations) and are not covered.
-/

@[expose] public section

namespace PerfectCuboid.EdgeCuboidTwoPrimes

/-- "The minimum is attained twice", for a general exponent `K = iₘ + aₘ`: either all
`iₘ = aₘ` (only possible for `K` even), or the minimum of the `min(iₘ, aₘ)` is attained at two
indices and is `< K/2`. -/
theorem two_min_gen {K i1 i2 i3 a1 a2 a3 : ℕ}
    (e1 : i1 + a1 = K) (e2 : i2 + a2 = K) (e3 : i3 + a3 = K)
    (v1 : ¬ (i1 ≠ a1 ∧ min i1 a1 < min i2 a2 ∧ min i1 a1 < min i3 a3))
    (v2 : ¬ (i2 ≠ a2 ∧ min i2 a2 < min i1 a1 ∧ min i2 a2 < min i3 a3))
    (v3 : ¬ (i3 ≠ a3 ∧ min i3 a3 < min i1 a1 ∧ min i3 a3 < min i2 a2)) :
    (i1 = a1 ∧ i2 = a2 ∧ i3 = a3) ∨
    (min i1 a1 = min i2 a2 ∧ min i1 a1 ≤ min i3 a3 ∧ 2 * min i1 a1 < K) ∨
    (min i1 a1 = min i3 a3 ∧ min i1 a1 ≤ min i2 a2 ∧ 2 * min i1 a1 < K) ∨
    (min i2 a2 = min i3 a3 ∧ min i2 a2 ≤ min i1 a1 ∧ 2 * min i2 a2 < K) := by
  omega

section CaseTree

variable {K L i1 i2 i3 j1 j2 j3 a1 a2 a3 b1 b2 b3 : ℕ}
    (e1 : i1 + a1 = K) (e2 : i2 + a2 = K) (e3 : i3 + a3 = K)
    (f1 : j1 + b1 = L) (f2 : j2 + b2 = L) (f3 : j3 + b3 = L)
    (h11 : ¬ (a1 ≤ i1 ∧ b1 ≤ j1)) (h12 : ¬ (a2 ≤ i1 ∧ b2 ≤ j1)) (h13 : ¬ (a3 ≤ i1 ∧ b3 ≤ j1))
    (h21 : ¬ (a1 ≤ i2 ∧ b1 ≤ j2)) (h22 : ¬ (a2 ≤ i2 ∧ b2 ≤ j2)) (h23 : ¬ (a3 ≤ i2 ∧ b3 ≤ j2))
    (h31 : ¬ (a1 ≤ i3 ∧ b1 ≤ j3)) (h32 : ¬ (a2 ≤ i3 ∧ b2 ≤ j3)) (h33 : ¬ (a3 ≤ i3 ∧ b3 ≤ j3))
    (g1 : ¬ (i1 ≤ i3 ∧ j1 ≤ j3)) (g2 : ¬ (i2 ≤ i3 ∧ j2 ≤ j3)) (g12 : ¬ (i1 = i2 ∧ j1 = j2))
    (hineq : ¬ (i3 ≤ i1 ∧ j3 ≤ j1 ∧ i3 ≤ i2 ∧ j3 ≤ j2))
include e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq

set_option linter.unusedSectionVars false

/-- No `p`-adic jump at all (`iₘ = aₘ`, so `K` is even): then two legs coincide. -/
theorem caseA0_gen (hA : i1 = a1 ∧ i2 = a2 ∧ i3 = a3)
    (w1 : ¬ (j1 ≠ b1 ∧ min j1 b1 < min j2 b2 ∧ min j1 b1 < min j3 b3))
    (w2 : ¬ (j2 ≠ b2 ∧ min j2 b2 < min j1 b1 ∧ min j2 b2 < min j3 b3))
    (w3 : ¬ (j3 ≠ b3 ∧ min j3 b3 < min j1 b1 ∧ min j3 b3 < min j2 b2)) : False := by
  omega

theorem caseB0_gen (hB : j1 = b1 ∧ j2 = b2 ∧ j3 = b3)
    (v1 : ¬ (i1 ≠ a1 ∧ min i1 a1 < min i2 a2 ∧ min i1 a1 < min i3 a3))
    (v2 : ¬ (i2 ≠ a2 ∧ min i2 a2 < min i1 a1 ∧ min i2 a2 < min i3 a3))
    (v3 : ¬ (i3 ≠ a3 ∧ min i3 a3 < min i1 a1 ∧ min i3 a3 < min i2 a2)) : False := by
  omega

theorem case12_12_gen (hA : min i1 a1 = min i2 a2 ∧ min i1 a1 ≤ min i3 a3 ∧ 2 * min i1 a1 < K)
    (hB : min j1 b1 = min j2 b2 ∧ min j1 b1 ≤ min j3 b3 ∧ 2 * min j1 b1 < L) : False := by
  omega

theorem case13_13_gen (hA : min i1 a1 = min i3 a3 ∧ min i1 a1 ≤ min i2 a2 ∧ 2 * min i1 a1 < K)
    (hB : min j1 b1 = min j3 b3 ∧ min j1 b1 ≤ min j2 b2 ∧ 2 * min j1 b1 < L) : False := by
  omega

theorem case23_23_gen (hA : min i2 a2 = min i3 a3 ∧ min i2 a2 ≤ min i1 a1 ∧ 2 * min i2 a2 < K)
    (hB : min j2 b2 = min j3 b3 ∧ min j2 b2 ≤ min j1 b1 ∧ 2 * min j2 b2 < L) : False := by
  omega

theorem case13_23_gen (hA : min i1 a1 = min i3 a3 ∧ min i1 a1 ≤ min i2 a2 ∧ 2 * min i1 a1 < K)
    (hB : min j2 b2 = min j3 b3 ∧ min j2 b2 ≤ min j1 b1 ∧ 2 * min j2 b2 < L) : False := by
  omega

theorem case23_13_gen (hA : min i2 a2 = min i3 a3 ∧ min i2 a2 ≤ min i1 a1 ∧ 2 * min i2 a2 < K)
    (hB : min j1 b1 = min j3 b3 ∧ min j1 b1 ≤ min j2 b2 ∧ 2 * min j1 b1 < L) : False := by
  omega

set_option maxHeartbeats 1000000 in
-- `omega` with the general exponents `K, L` needs more than the default budget here.
theorem case12_13_gen (hA : min i1 a1 = min i2 a2 ∧ min i1 a1 ≤ min i3 a3 ∧ 2 * min i1 a1 < K)
    (hB : min j1 b1 = min j3 b3 ∧ min j1 b1 ≤ min j2 b2 ∧ 2 * min j1 b1 < L) :
    (j3 = j1 ∧ i2 = a1 ∧ j1 < j2 ∧ j2 < b1 ∧ a1 < i3 ∧ i3 < i1) ∨
    (i2 = i1 ∧ j3 = b1 ∧ b1 < j2 ∧ j2 < j1 ∧ i1 < i3 ∧ i3 < a1) := by
  rcases le_total i1 a1 with hi | hi <;> rcases le_total j1 b1 with hj | hj
  · exfalso; omega
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · left; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exfalso; omega

set_option maxHeartbeats 1000000 in
-- `omega` with the general exponents `K, L` needs more than the default budget here.
theorem case12_23_gen (hA : min i1 a1 = min i2 a2 ∧ min i1 a1 ≤ min i3 a3 ∧ 2 * min i1 a1 < K)
    (hB : min j2 b2 = min j3 b3 ∧ min j2 b2 ≤ min j1 b1 ∧ 2 * min j2 b2 < L) :
    (i1 = i2 ∧ j3 = b2 ∧ b2 < j1 ∧ j1 < j2 ∧ i2 < i3 ∧ i3 < a2) ∨
    (j3 = j2 ∧ i1 = a2 ∧ j2 < j1 ∧ j1 < b2 ∧ a2 < i3 ∧ i3 < i2) := by
  rcases le_total i2 a2 with hi | hi <;> rcases le_total j2 b2 with hj | hj
  · exfalso; omega
  · left; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exfalso; omega

set_option maxHeartbeats 1000000 in
-- `omega` with the general exponents `K, L` needs more than the default budget here.
theorem case13_12_gen (hA : min i1 a1 = min i3 a3 ∧ min i1 a1 ≤ min i2 a2 ∧ 2 * min i1 a1 < K)
    (hB : min j1 b1 = min j2 b2 ∧ min j1 b1 ≤ min j3 b3 ∧ 2 * min j1 b1 < L) :
    (i3 = i1 ∧ j2 = b1 ∧ i1 < i2 ∧ i2 < a1 ∧ b1 < j3 ∧ j3 < j1) ∨
    (j2 = j1 ∧ i3 = a1 ∧ a1 < i2 ∧ i2 < i1 ∧ j1 < j3 ∧ j3 < b1) := by
  rcases le_total i1 a1 with hi | hi <;> rcases le_total j1 b1 with hj | hj
  · exfalso; omega
  · left; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exfalso; omega

set_option maxHeartbeats 1000000 in
-- `omega` with the general exponents `K, L` needs more than the default budget here.
theorem case23_12_gen (hA : min i2 a2 = min i3 a3 ∧ min i2 a2 ≤ min i1 a1 ∧ 2 * min i2 a2 < K)
    (hB : min j1 b1 = min j2 b2 ∧ min j1 b1 ≤ min j3 b3 ∧ 2 * min j1 b1 < L) :
    (i3 = i2 ∧ j1 = b2 ∧ i2 < i1 ∧ i1 < a2 ∧ b2 < j3 ∧ j3 < j2) ∨
    (j1 = j2 ∧ i3 = a2 ∧ a2 < i1 ∧ i1 < i2 ∧ j2 < j3 ∧ j3 < b2) := by
  rcases le_total i2 a2 with hi | hi <;> rcases le_total j2 b2 with hj | hj
  · exfalso; omega
  · left; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exfalso; omega

end CaseTree


/-- **Main lemma (exponent form, general `N`).** Let `p ≠ q` be primes, `N = p^K q^L`, and let
`tₘ = p^iₘ q^jₘ < uₘ = p^aₘ q^bₘ` (`iₘ + aₘ = K`, `jₘ + bₘ = L`, so `tₘ uₘ = N`) for
`m = 1, 2, 3`. Then `(u₁ − t₁)² + (u₂ − t₂)² ≠ (u₃ − t₃)²`. -/
theorem config_false_gen {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {K L i1 i2 i3 j1 j2 j3 a1 a2 a3 b1 b2 b3 : ℕ}
    (e1 : i1 + a1 = K) (e2 : i2 + a2 = K) (e3 : i3 + a3 = K)
    (f1 : j1 + b1 = L) (f2 : j2 + b2 = L) (f3 : j3 + b3 = L)
    (lt1 : mn p q i1 j1 < mn p q a1 b1) (lt2 : mn p q i2 j2 < mn p q a2 b2)
    (lt3 : mn p q i3 j3 < mn p q a3 b3)
    (key : (mn p q a1 b1 - mn p q i1 j1) ^ 2 + (mn p q a2 b2 - mn p q i2 j2) ^ 2 =
      (mn p q a3 b3 - mn p q i3 j3) ^ 2) : False := by
  have pos := mn_pos hp hq
  have prod : ∀ {i a j b : ℕ}, i + a = K → j + b = L →
      mn p q i j * mn p q a b = mn p q (K) (L) := by
    intro i a j b h1 h2; unfold mn; rw [← h1, ← h2]; ring
  have P1 := prod e1 f1
  have P2 := prod e2 f2
  have P3 := prod e3 f3
  -- order facts: `t₃ < t₁, t₂` and `tₘ < uₘ'`
  have hY1 : 0 < mn p q a1 b1 - mn p q i1 j1 := by linarith
  have hY2 : 0 < mn p q a2 b2 - mn p q i2 j2 := by linarith
  have t31 : mn p q i3 j3 < mn p q i1 j1 :=
    t_lt_of_sq_lt (pos _ _) (pos _ _) (P1.trans P3.symm) lt1 lt3 (by nlinarith [pow_pos hY2 2])
  have t32 : mn p q i3 j3 < mn p q i2 j2 :=
    t_lt_of_sq_lt (pos _ _) (pos _ _) (P2.trans P3.symm) lt2 lt3 (by nlinarith [pow_pos hY1 2])
  have cr : ∀ {i a j b i' a' j' b' : ℕ}, mn p q i j * mn p q a b = mn p q i' j' * mn p q a' b' →
      mn p q i j < mn p q a b → mn p q i' j' < mn p q a' b' → ¬ (a' ≤ i ∧ b' ≤ j) :=
    fun h h1 h2 ↦ not_le_le_of_mn_lt hp hq (t_lt_u (pos _ _) (pos _ _) h h1 h2)
  have h11 := cr (P1.trans P1.symm) lt1 lt1
  have h12 := cr (P1.trans P2.symm) lt1 lt2
  have h13 := cr (P1.trans P3.symm) lt1 lt3
  have h21 := cr (P2.trans P1.symm) lt2 lt1
  have h22 := cr (P2.trans P2.symm) lt2 lt2
  have h23 := cr (P2.trans P3.symm) lt2 lt3
  have h31 := cr (P3.trans P1.symm) lt3 lt1
  have h32 := cr (P3.trans P2.symm) lt3 lt2
  have h33 := cr (P3.trans P3.symm) lt3 lt3
  have g1 := not_le_le_of_mn_lt hp hq t31
  have g2 := not_le_le_of_mn_lt hp hq t32
  -- `t₁ ≠ t₂` (else `f² = 2b²`)
  have g12 : ¬ (i1 = i2 ∧ j1 = j2) := by
    rintro ⟨rfl, rfl⟩
    obtain rfl : a1 = a2 := by omega
    obtain rfl : b1 = b2 := by omega
    exact sq_ne_two_mul_sq_int (x := mn p q a3 b3 - mn p q i3 j3) hY1.ne'
      (by linear_combination -key)
  -- the divisor inequality
  have hineq : ¬ (i3 ≤ i1 ∧ j3 ≤ j1 ∧ i3 ≤ i2 ∧ j3 ≤ j2) := by
    rintro ⟨h1, h2, h3, h4⟩
    exact not_dvd_both (inv_sq_add_inv_sq_gt P1 P2 P3 (pos _ _) (pos _ _) (pos _ _) lt1 lt2 key).2
      (pos _ _) t31 t32 (mn_dvd h1 h2) (mn_dvd h3 h4)
  -- valuations
  have dv3 : ∀ P : ℤ, P ∣ mn p q a1 b1 - mn p q i1 j1 → P ∣ mn p q a2 b2 - mn p q i2 j2 →
      P ∣ mn p q a3 b3 - mn p q i3 j3 := fun P h1 h2 ↦
    (Int.pow_dvd_pow_iff two_ne_zero).1 (key ▸ dvd_add (pow_dvd_pow_of_dvd h1 2)
      (pow_dvd_pow_of_dvd h2 2))
  have dv1 : ∀ P : ℤ, P ∣ mn p q a2 b2 - mn p q i2 j2 → P ∣ mn p q a3 b3 - mn p q i3 j3 →
      P ∣ mn p q a1 b1 - mn p q i1 j1 := fun P h2 h3 ↦ by
    refine (Int.pow_dvd_pow_iff two_ne_zero).1 ?_
    rw [show (mn p q a1 b1 - mn p q i1 j1) ^ 2 = (mn p q a3 b3 - mn p q i3 j3) ^ 2 -
      (mn p q a2 b2 - mn p q i2 j2) ^ 2 by linear_combination key]
    exact dvd_sub (pow_dvd_pow_of_dvd h3 2) (pow_dvd_pow_of_dvd h2 2)
  have dv2 : ∀ P : ℤ, P ∣ mn p q a1 b1 - mn p q i1 j1 → P ∣ mn p q a3 b3 - mn p q i3 j3 →
      P ∣ mn p q a2 b2 - mn p q i2 j2 := fun P h1 h3 ↦ by
    refine (Int.pow_dvd_pow_iff two_ne_zero).1 ?_
    rw [show (mn p q a2 b2 - mn p q i2 j2) ^ 2 = (mn p q a3 b3 - mn p q i3 j3) ^ 2 -
      (mn p q a1 b1 - mn p q i1 j1) ^ 2 by linear_combination key]
    exact dvd_sub (pow_dvd_pow_of_dvd h3 2) (pow_dvd_pow_of_dvd h1 2)
  have np := int_not_dvd_pow hp hq hpq
  have nq := int_not_dvd_pow hq hp hpq.symm
  have v1 := val_fact hp (np b1) (np j1) rfl rfl rfl dv1
  have v2 := val_fact hp (np b2) (np j2) rfl rfl rfl dv2
  have v3 := val_fact hp (np b3) (np j3) rfl rfl rfl dv3
  have w1 := val_fact hq (nq a1) (nq i1) (mn_sub_swap ..) (mn_sub_swap ..) (mn_sub_swap ..) dv1
  have w2 := val_fact hq (nq a2) (nq i2) (mn_sub_swap ..) (mn_sub_swap ..) (mn_sub_swap ..) dv2
  have w3 := val_fact hq (nq a3) (nq i3) (mn_sub_swap ..) (mn_sub_swap ..) (mn_sub_swap ..) dv3
  -- the eight residual shapes are all RES
  have S1 : (i3 = i2 ∧ j1 = b2 ∧ i2 < i1 ∧ i1 < a2 ∧ b2 < j3 ∧ j3 < j2) → False := fun h ↦
    res_shape hp hq hpq (I1 := i1) (J1 := j1) (A1 := a1) (B1 := b1) (I2 := i2) (J2 := j2)
        (A2 := a2) (B2 := b2) (I3 := i3) (J3 := j3) (A3 := a3) (B3 := b3)
      (s := i2) (σ := b2) (a := (i1-i2)) (b := (a1-i2)) (c := (j3-b2)) (d := (b3-b2))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S2 : (i1 = i2 ∧ j3 = b2 ∧ b2 < j1 ∧ j1 < j2 ∧ i2 < i3 ∧ i3 < a2) → False := fun h ↦
    res_shape hq hp hpq.symm (I1 := j1) (J1 := i1) (A1 := b1) (B1 := a1) (I2 := b2) (J2 := a2)
        (A2 := j2) (B2 := i2) (I3 := j3) (J3 := i3) (A3 := b3) (B3 := a3)
      (s := b2) (σ := i2) (a := (j1-b2)) (b := (b1-b2)) (c := (i3-i2)) (d := (a3-i2))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S3 : (i3 = i1 ∧ j2 = b1 ∧ i1 < i2 ∧ i2 < a1 ∧ b1 < j3 ∧ j3 < j1) → False := fun h ↦
    res_shape hp hq hpq (I1 := i2) (J1 := j2) (A1 := a2) (B1 := b2) (I2 := i1) (J2 := j1)
        (A2 := a1) (B2 := b1) (I3 := i3) (J3 := j3) (A3 := a3) (B3 := b3)
      (s := i1) (σ := b1) (a := (i2-i1)) (b := (a2-i1)) (c := (j3-b1)) (d := (b3-b1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S4 : (i2 = i1 ∧ j3 = b1 ∧ b1 < j2 ∧ j2 < j1 ∧ i1 < i3 ∧ i3 < a1) → False := fun h ↦
    res_shape hq hp hpq.symm (I1 := j2) (J1 := i2) (A1 := b2) (B1 := a2) (I2 := b1) (J2 := a1)
        (A2 := j1) (B2 := i1) (I3 := j3) (J3 := i3) (A3 := b3) (B3 := a3)
      (s := b1) (σ := i1) (a := (j2-b1)) (b := (b2-b1)) (c := (i3-i1)) (d := (a3-i1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S5 : (j3 = j2 ∧ i1 = a2 ∧ j2 < j1 ∧ j1 < b2 ∧ a2 < i3 ∧ i3 < i2) → False := fun h ↦
    res_shape hq hp hpq.symm (I1 := j1) (J1 := i1) (A1 := b1) (B1 := a1) (I2 := j2) (J2 := i2)
        (A2 := b2) (B2 := a2) (I3 := j3) (J3 := i3) (A3 := b3) (B3 := a3)
      (s := j2) (σ := a2) (a := (j1-j2)) (b := (b1-j2)) (c := (i3-a2)) (d := (a3-a2))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S6 : (j1 = j2 ∧ i3 = a2 ∧ a2 < i1 ∧ i1 < i2 ∧ j2 < j3 ∧ j3 < b2) → False := fun h ↦
    res_shape hp hq hpq (I1 := i1) (J1 := j1) (A1 := a1) (B1 := b1) (I2 := a2) (J2 := b2)
        (A2 := i2) (B2 := j2) (I3 := i3) (J3 := j3) (A3 := a3) (B3 := b3)
      (s := a2) (σ := j2) (a := (i1-a2)) (b := (a1-a2)) (c := (j3-j2)) (d := (b3-j2))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S7 : (j3 = j1 ∧ i2 = a1 ∧ j1 < j2 ∧ j2 < b1 ∧ a1 < i3 ∧ i3 < i1) → False := fun h ↦
    res_shape hq hp hpq.symm (I1 := j2) (J1 := i2) (A1 := b2) (B1 := a2) (I2 := j1) (J2 := i1)
        (A2 := b1) (B2 := a1) (I3 := j3) (J3 := i3) (A3 := b3) (B3 := a3)
      (s := j1) (σ := a1) (a := (j2-j1)) (b := (b2-j1)) (c := (i3-a1)) (d := (a3-a1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  have S8 : (j2 = j1 ∧ i3 = a1 ∧ a1 < i2 ∧ i2 < i1 ∧ j1 < j3 ∧ j3 < b1) → False := fun h ↦
    res_shape hp hq hpq (I1 := i2) (J1 := j2) (A1 := a2) (B1 := b2) (I2 := a1) (J2 := b1)
        (A2 := i1) (B2 := j1) (I3 := i3) (J3 := j3) (A3 := a3) (B3 := b3)
      (s := a1) (σ := j1) (a := (i2-a1)) (b := (a2-a1)) (c := (j3-j1)) (d := (b3-j1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold mn at key ⊢; linear_combination key)
  rcases two_min_gen e1 e2 e3 v1 v2 v3 with hA | hA | hA | hA
  · exact caseA0_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq
      hA w1 w2 w3
  all_goals rcases two_min_gen f1 f2 f3 w1 w2 w3 with hB | hB | hB | hB
  all_goals first
    | exact caseB0_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq
        hB v1 v2 v3
    | exact case12_12_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq
        hA hB
    | exact case13_13_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq
        hA hB
    | exact case23_23_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq
        hA hB
    | exact case13_23_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq
        hA hB
    | exact case23_13_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq
        hA hB
    | exact
        (case12_13_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA
        hB).elim S7 S4
    | exact
        (case12_23_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA
        hB).elim S2 S5
    | exact
        (case13_12_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA
        hB).elim S3 S8
    | exact
        (case23_12_gen e1 e2 e3 f1 f2 f3 h11 h12 h13 h21 h22 h23 h31 h32 h33 g1 g2 g12 hineq hA
        hB).elim S1 S6

/-- **Shape of a leg, general `N`.** If `N = p^K q^L` and `N + x² = X²` with `x > 0`, then
`X − x = p^i q^j` and `X + x = p^a q^b` with `i + a = K`, `j + b = L`, so
`2x = p^a q^b − p^i q^j`. -/
theorem leg_two_gen {p q K L N x X : ℕ} (hp : p.Prime) (hq : q.Prime) (hx : 0 < x)
    (h : N + x ^ 2 = X ^ 2) (hN : N = p ^ K * q ^ L) :
    ∃ i a j b, i + a = K ∧ j + b = L ∧ mn p q i j < mn p q a b ∧
      (2 * x : ℤ) = mn p q a b - mn p q i j := by
  subst hN
  have hN0 : 0 < p ^ K * q ^ L := by have := hp.pos; have := hq.pos; positivity
  have hxX : x < X := by
    have : x ^ 2 < X ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hmul : (X - x) * (X + x) = p ^ K * q ^ L := by
    have h1 := Nat.sq_sub_sq X x
    have h2 : X ^ 2 - x ^ 2 = p ^ K * q ^ L := by omega
    rw [mul_comm, ← h1, h2]
  obtain ⟨t1, t2, ht1, ht2, ht⟩ := dvd_mul.1 (Dvd.intro _ hmul)
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 ht1
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hq).1 ht2
  have hu : X + x = p ^ (K - i) * q ^ (L - j) := by
    have hpos : 0 < p ^ i * q ^ j := by have := hp.pos; have := hq.pos; positivity
    have e : p ^ i * q ^ j * (p ^ (K - i) * q ^ (L - j)) = p ^ K * q ^ L := by
      rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_cancel' hi, Nat.add_sub_cancel' hj]
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [e, ← hmul, ht]
  have hT : mn p q i j = (X : ℤ) - x := by
    unfold mn; rw [← Nat.cast_sub hxX.le, ht]; push_cast; ring
  have hU : mn p q (K - i) (L - j) = (X : ℤ) + x := by
    unfold mn; rw [show ((X : ℤ) + x) = ((X + x : ℕ) : ℤ) by push_cast; ring, hu]; push_cast; ring
  refine ⟨i, K - i, j, L - j, by omega, by omega, ?_, ?_⟩
  · rw [hT, hU]; have : (0 : ℤ) < x := by exact_mod_cast hx
    linarith
  · rw [hT, hU]; ring

end PerfectCuboid.EdgeCuboidTwoPrimes

namespace PerfectCuboid

open EdgeCuboidTwoPrimes

/-- **Three factorizations of a two-prime number.** If `N` has three representations
`N + x² = X²`, `N + y² = Y²`, `N + z² = Z²` whose legs satisfy `x² + y² = z²` with `x, y > 0`,
then `N` is not of the form `p^K q^L` (`p ≠ q` primes, any `K, L ≥ 0`). No parity, primitivity
or non-square assumption is needed. -/
theorem three_factorizations_ne_two_prime_pow {N x y z X Y Z : ℕ} (hx0 : 0 < x) (hy0 : 0 < y)
    (hxyz : x ^ 2 + y ^ 2 = z ^ 2) (hX : N + x ^ 2 = X ^ 2) (hY : N + y ^ 2 = Y ^ 2)
    (hZ : N + z ^ 2 = Z ^ 2) {p q K L : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    N ≠ p ^ K * q ^ L := by
  intro hN
  have hz0 : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h0 | h0
    · subst h0; nlinarith
    · exact h0
  obtain ⟨i1, a1, j1, b1, e1, f1, lt1, Y1⟩ := leg_two_gen hp hq hx0 hX hN
  obtain ⟨i2, a2, j2, b2, e2, f2, lt2, Y2⟩ := leg_two_gen hp hq hy0 hY hN
  obtain ⟨i3, a3, j3, b3, e3, f3, lt3, Y3⟩ := leg_two_gen hp hq hz0 hZ hN
  refine config_false_gen hp hq hpq e1 e2 e3 f1 f2 f3 lt1 lt2 lt3 ?_
  rw [← Y1, ← Y2, ← Y3]
  have : ((x : ℤ) ^ 2 + y ^ 2) = z ^ 2 := by exact_mod_cast hxyz
  linear_combination 4 * this

/-- **The irrational edge of an edge cuboid is not `√(p^K q^L)`.** -/
theorem IsEdgeCuboid.N_ne_two_prime_pow {a b N : ℕ} (h : IsEdgeCuboid a b N)
    {p q K L : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : N ≠ p ^ K * q ^ L := by
  obtain ⟨d, e, f, g, hd, he, hf, hg⟩ := h.diagonals
  exact three_factorizations_ne_two_prime_pow h.pos_a h.pos_b hd (by rw [← he]; ring)
    (by rw [← hf]; ring) (by rw [← hg, ← hd]; ring) hp hq hpq

/-- **The square of the irrational edge of an edge cuboid has at least three distinct prime
factors.** -/
theorem IsEdgeCuboid.three_le_primeFactors_card {a b N : ℕ} (h : IsEdgeCuboid a b N) :
    3 ≤ N.primeFactors.card :=
  three_le_card_primeFactors_of h.pos_N.ne' fun _ _ _ _ hp hq hpq ↦
    h.N_ne_two_prime_pow hp hq hpq

/-- **Round 11 as a special case.** Taking `N = a²` (`K = 2k`, `L = 2l`) and the legs `b, c, f`
in `three_factorizations_ne_two_prime_pow` shows again that the first edge of a perfect cuboid is
not of the form `p^k q^l`. -/
theorem IsPerfectCuboid.edge_ne_two_prime_pow_of_three_factorizations {a b c : ℕ}
    (h : IsPerfectCuboid a b c) {p q k l : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    a ≠ p ^ k * q ^ l := by
  rintro rfl
  obtain ⟨d, hd⟩ := h.sq_ab
  obtain ⟨e, he⟩ := h.sq_ca
  obtain ⟨f, hf⟩ := h.sq_bc
  obtain ⟨g, hg⟩ := h.sq_abc
  rw [← sq] at hd he hf hg
  refine three_factorizations_ne_two_prime_pow (N := (p ^ k * q ^ l) ^ 2) (K := 2 * k)
    (L := 2 * l) h.pos_b h.pos_c hf hd (by rw [← he]; ring) (by rw [← hg, ← hf]; ring)
    hp hq hpq ?_
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l]

end PerfectCuboid
