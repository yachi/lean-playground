module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Unit-step invariance of the Leonard–Williams symbol

Leonard and Williams decide whether `16` divides the class number `h(−8ℓ)` for primes
`ℓ ≡ 15 (mod 16)` by writing `2u² = N(2v + √−2ℓ)` and evaluating the Jacobi symbol `(2u/v)`.
The pair `(u, v)` with `u + v√2` is only determined up to multiplication by units of `ℤ[√2]`.
Multiplying by the totally positive unit `(1 + √2)² = 3 + 2√2` sends

  `u + v√2 ↦ (3u + 4v) + (2u + 3v)√2`.

This file shows that the symbol `(2u/v)` does not change under this step, nor under the step
that also swaps `π` and its conjugate:

* `jacobiSym_LW_unit_step`: for odd `u, v`,
  `(2(3u + 4v) / (2u + 3v)) = (2u / v)`; `jacobiSym_LW_unit_step_iterate` is the version for
  `(1 + √2)^{2n}`.
* `jacobiSym_LW_conj_step`: for odd `u, v` with `2u > 3v`,
  `(2(3u − 4v) / (2u − 3v)) = (2u / v)`. This is `u − v√2 ↦ (1 + √2)²(u − v√2)`, which takes a
  positive representation of `π'` to one of `π`, e.g. `31 = 7² − 2·3² = 9² − 2·5²`.

Both steps keep `u² − 2v²` (`norm_LW_unit_step`, `norm_LW_conj_step`).

## Why it matters for perfect cuboids

In the round-8 data for the twists `E₁^{(±ℓ)}` with `ℓ ≡ 15 (mod 16)`, the 2-Selmer classes that
survive are exactly the primes with `(−1)^{(ℓ+1)/16} (2u/v) = +1`, and the proposed formula for the
Cassels–Tate pairing on the two non-torsion Selmer classes is this sign. The lemma here is the
check that the sign is well defined: it does not depend on which representative `(u, v)` of the
unit class is used. The Cassels–Tate identification is now proved on paper (project notes,
`perfect-cuboid/round9/t1-triple-prime-a.md`): for `ℓ ≡ 15 (mod 16)` the pairing on
`Sel₂(E₁^{(ℓ)}/ℚ(√2))` is the Frobenius of the prime over `ℓ` in the 8-class field of
`ℚ(√−2ℓ)`, so it is non-degenerate exactly when `8 ∥ h(−8ℓ)`, which by Leonard–Williams is the
sign above. Only this symbol computation is formalized.

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

/-- **Conjugate-step invariance.** The step `(u, v) ↦ (3u − 4v, 2u − 3v)` (conjugate `u + v√2`,
then multiply by `(1 + √2)²`) leaves `(2u / v)` unchanged, for odd `u, v` with `2u > 3v`. -/
theorem jacobiSym_LW_conj_step (u v : ℕ) (hu : u % 2 = 1) (hv : v % 2 = 1) (huv : 3 * v < 2 * u) :
    jacobiSym (2 * (3 * u - 4 * v) : ℤ) (2 * u - 3 * v) = jacobiSym (2 * u : ℤ) v := by
  set w := 2 * u - 3 * v with hw
  have hvo : Odd v := Nat.odd_iff.mpr hv
  have hwo : Odd w := Nat.odd_iff.mpr (by omega)
  have hwz : (w : ℤ) = 2 * u - 3 * v := by rw [hw]; push_cast [huv.le]; ring
  -- `2(3u − 4v) ≡ v (mod w)`
  have h1 : jacobiSym (2 * (3 * u - 4 * v) : ℤ) w = jacobiSym (v : ℤ) w := by
    apply jacobiSym.mod_left'
    have : (2 * (3 * u - 4 * v) : ℤ) = v + 3 * (w : ℤ) := by rw [hwz]; ring
    rw [this, Int.add_mul_emod_self_right]
  -- `w ≡ 2u (mod v)`
  have h2 : jacobiSym (w : ℤ) v = jacobiSym (2 * u : ℤ) v := by
    apply jacobiSym.mod_left'
    have : (w : ℤ) = 2 * u + (-3) * (v : ℤ) := by rw [hwz]; ring
    rw [this, Int.add_mul_emod_self_right]
  rw [h1, ← h2]
  -- `w ≡ v + 2 (mod 4)`, so one of `v, w` is `1 (mod 4)` and both signs are `+1`
  rcases Nat.odd_mod_four_iff.mp hv with hv1 | hv3
  · exact jacobiSym.quadratic_reciprocity_one_mod_four hv1 hwo
  · exact jacobiSym.quadratic_reciprocity_one_mod_four' hvo (by omega)

/-- The unit step `(u, v) ↦ (3u + 4v, 2u + 3v)`. -/
def unitStep (p : ℕ × ℕ) : ℕ × ℕ := (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)

/-- The unit step keeps `u` and `v` odd. -/
theorem unitStep_odd {p : ℕ × ℕ} (hu : p.1 % 2 = 1) (hv : p.2 % 2 = 1) :
    (unitStep p).1 % 2 = 1 ∧ (unitStep p).2 % 2 = 1 := by
  simp only [unitStep]; omega

/-- **Iterated unit step** (multiplication by `(1 + √2)^{2n}`): `(2u / v)` is unchanged. -/
theorem jacobiSym_LW_unit_step_iterate (n : ℕ) {p : ℕ × ℕ} (hu : p.1 % 2 = 1)
    (hv : p.2 % 2 = 1) :
    jacobiSym (2 * (unitStep^[n] p).1 : ℤ) (unitStep^[n] p).2 = jacobiSym (2 * p.1 : ℤ) p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    obtain ⟨hu', hv'⟩ := unitStep_odd hu hv
    rw [Function.iterate_succ_apply, ih hu' hv']
    simpa [unitStep] using jacobiSym_LW_unit_step p.1 p.2 hu hv

/-- `(1 + √2)² = 3 + 2√2` has norm `1`. -/
theorem norm_LW_unit_step (u v : ℤ) :
    (3 * u + 4 * v) ^ 2 - 2 * (2 * u + 3 * v) ^ 2 = u ^ 2 - 2 * v ^ 2 := by ring

/-- The conjugate step keeps the norm. -/
theorem norm_LW_conj_step (u v : ℤ) :
    (3 * u - 4 * v) ^ 2 - 2 * (2 * u - 3 * v) ^ 2 = u ^ 2 - 2 * v ^ 2 := by ring

/-- `31 = 7² − 2·3² = 9² − 2·5²`, the second the conjugate step of the first:
`(14 / 3) = (18 / 5) = −1`. -/
example : jacobiSym 14 3 = -1 ∧ jacobiSym 18 5 = -1 := by
  constructor <;> norm_num

end LeonardWilliams
