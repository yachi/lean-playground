module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Unit-step invariance of the Leonard–Williams symbol

Leonard and Williams decide whether `16` divides the class number `h(−8ℓ)` for primes
`ℓ ≡ 15 (mod 16)` by writing `2u² = N(2v + √−2ℓ)` and evaluating the Jacobi symbol `(2u/v)`.
The pair `(u, v)` with `u + v√2` is only determined up to multiplication by units of `ℤ[√2]`.
Multiplying by the totally positive unit `(1 + √2)² = 3 + 2√2` sends

  `u + v√2 ↦ (3u + 4v) + (2u + 3v)√2`.

This file shows that the symbol `(2u/v)` does not change under this step:

* `jacobiSym_LW_unit_step`: for odd `u, v`,
  `(2(3u + 4v) / (2u + 3v)) = (2u / v)`.

## Why it matters for perfect cuboids

In the round-8 data for the twists `E₁^{(±ℓ)}` with `ℓ ≡ 15 (mod 16)`, the 2-Selmer classes that
survive are exactly the primes with `(−1)^{(ℓ+1)/16} (2u/v) = +1`, and the proposed formula for the
Cassels–Tate pairing on the two non-torsion Selmer classes is this sign. The lemma here is the
check that the sign is well defined: it does not depend on which representative `(u, v)` of the
unit class is used. The Cassels–Tate identification itself is not formalized.

## Proof

Put `w = 2u + 3v`. Then `2(3u + 4v) = 3w − v ≡ −v (mod w)`, so the left side is
`(−1/w)(v/w)`. Quadratic reciprocity turns `(v/w)` into `±(w/v)`, and `w ≡ 2u (mod v)`.
Since `u` is odd, `w ≡ 2 − v (mod 4)`, so `w ≡ v (mod 4)`: for `v ≡ 1` both signs are `+1`, and
for `v ≡ 3` both are `−1` and cancel.
-/

@[expose] public section

namespace LeonardWilliams

open ZMod

/-- **Unit-step invariance of the Leonard–Williams symbol.** The step
`(u, v) ↦ (3u + 4v, 2u + 3v)` (multiplication of `u + v√2` by `(1 + √2)²`) leaves the Jacobi
symbol `(2u / v)` unchanged, for odd `u` and `v`. -/
theorem jacobiSym_LW_unit_step (u v : ℕ) (hu : u % 2 = 1) (hv : v % 2 = 1) :
    jacobiSym (2 * (3 * u + 4 * v) : ℤ) (2 * u + 3 * v) = jacobiSym (2 * u : ℤ) v := by
  set w := 2 * u + 3 * v with hw
  have hvo : Odd v := Nat.odd_iff.mpr hv
  have hwo : Odd w := Nat.odd_iff.mpr (by omega)
  -- `2(3u + 4v) ≡ −v (mod w)`
  have h1 : jacobiSym (2 * (3 * u + 4 * v) : ℤ) w = jacobiSym (-1) w * jacobiSym (v : ℤ) w := by
    rw [← jacobiSym.mul_left]
    apply jacobiSym.mod_left'
    have : (2 * (3 * u + 4 * v) : ℤ) = -1 * v + 3 * (w : ℤ) := by rw [hw]; push_cast; ring
    rw [this, Int.add_mul_emod_self_right]
  -- `w ≡ 2u (mod v)`
  have h2 : jacobiSym (w : ℤ) v = jacobiSym (2 * u : ℤ) v := by
    apply jacobiSym.mod_left'
    have : (w : ℤ) = 2 * u + 3 * (v : ℤ) := by rw [hw]; push_cast; ring
    rw [this, Int.add_mul_emod_self_right]
  rw [h1, jacobiSym.at_neg_one hwo, ← h2, ZMod.χ₄_nat_eq_if_mod_four]
  rcases Nat.odd_mod_four_iff.mp hv with hv1 | hv3
  · -- `v ≡ w ≡ 1 (mod 4)`: both signs are `+1`
    have hw1 : w % 4 = 1 := by omega
    rw [jacobiSym.quadratic_reciprocity_one_mod_four hv1 hwo]
    simp [hw1, Nat.odd_iff.mp hwo]
  · -- `v ≡ w ≡ 3 (mod 4)`: both signs are `−1`
    have hw3 : w % 4 = 3 := by omega
    rw [jacobiSym.quadratic_reciprocity_three_mod_four hv3 hw3]
    simp [hw3, Nat.odd_iff.mp hwo]

end LeonardWilliams
